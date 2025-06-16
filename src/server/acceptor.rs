use rustix::fs;
use std::{
    borrow::Cow,
    env, io,
    os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd, RawFd},
    path::{Path, PathBuf},
};
use thiserror::Error;
use tokio::net::{UnixListener, UnixStream};

/// Errors returned by [`Acceptor`].
#[derive(Debug, Error)]
pub enum AcceptorError {
    #[error("no available socket candidates")]
    NoAvailableSocket,
    #[error("XDG_RUNTIME_DIR is not set or invalid")]
    RuntimeDirInvalid,
    #[error("could not open or create lock file: {0}")]
    LockOpen(#[source] io::Error),
    #[error("could not acquire file lock: {0}")]
    LockAcquire(#[source] io::Error),
    #[error("could not bind to socket: {0}")]
    Bind(#[source] io::Error),
    #[error("could not accept incoming connection: {0}")]
    Accept(#[source] io::Error),
}

/// Connection acceptor.
#[derive(Debug)]
pub struct Acceptor {
    /// The underlying listener.
    listener: UnixListener,

    /// Name of the bound socket.
    socket_name: String,
    /// Path to the bound socket.
    bind_path: PathBuf,
    /// Path to the lock file.
    lock_path: PathBuf,

    /// Lock fd, held as guard.
    _lock: OwnedFd,
}

impl Acceptor {
    /// Automatically binds to an available socket.
    ///
    /// The socket will be created under the `XDG_RUNTIME_DIR`.
    pub fn auto() -> Result<Self, AcceptorError> {
        // Try from "wayland-0" to "wayland-32"
        Self::with_candidates((0..33).map(|i| format!("wayland-{i}")))
    }

    /// Attempts to bind to a socket from a set of names.
    ///
    /// The socket will be created under the `XDG_RUNTIME_DIR`.
    pub fn with_candidates<'a, I, S>(candidates: I) -> Result<Self, AcceptorError>
    where
        I: IntoIterator<Item = S>,
        S: Into<Cow<'a, str>>,
    {
        Self::with_candidates_in_dir(xdg_runtime_dir()?, candidates)
    }

    /// Binds to a socket with the given name.
    ///
    /// The socket will be created under the `XDG_RUNTIME_DIR`.
    pub fn with_name<'a, S>(socket_name: S) -> Result<Self, AcceptorError>
    where
        S: Into<Cow<'a, str>>,
    {
        Self::with_name_in_dir(xdg_runtime_dir()?, socket_name)
    }

    /// Attempts to bind to a socket from a set of names in the given directory.
    pub fn with_candidates_in_dir<'a, P, I, S>(
        directory: P,
        candidates: I,
    ) -> Result<Self, AcceptorError>
    where
        P: AsRef<Path>,
        I: IntoIterator<Item = S>,
        S: Into<Cow<'a, str>>,
    {
        for socket_name in candidates {
            match Self::with_name_in_dir(directory.as_ref(), socket_name) {
                // Successfully bound to a socket, return.
                Ok(acceptor) => return Ok(acceptor),

                // Failed to acquire lock, try the next one.
                Err(AcceptorError::LockAcquire(_)) => continue,

                // Other errors, abort.
                Err(err) => return Err(err),
            }
        }

        Err(AcceptorError::NoAvailableSocket)
    }

    /// Binds to a socket in the given directory with the given name.
    pub fn with_name_in_dir<'a, P, S>(directory: P, socket_name: S) -> Result<Self, AcceptorError>
    where
        P: AsRef<Path>,
        S: Into<Cow<'a, str>>,
    {
        // Into Cow
        let socket_name = socket_name.into();

        // Build paths
        let (bind_path, lock_path) = build_paths(directory.as_ref(), socket_name.as_ref());

        // Try to lock
        let _lock = lock_file(&lock_path)?;

        // Remove leftover socket file if it exists
        let _ = fs::unlink(&bind_path);

        // Bind and listen
        let listener = UnixListener::bind(&bind_path).map_err(AcceptorError::Bind)?;

        Ok(Acceptor {
            listener,
            socket_name: socket_name.into_owned(),
            bind_path,
            lock_path,
            _lock,
        })
    }

    /// Returns the name of the bound socket.
    pub fn socket_name(&self) -> &str {
        &self.socket_name
    }

    /// Accepts a new connection.
    pub async fn accept(&self) -> Result<UnixStream, AcceptorError> {
        let (stream, _) = self
            .listener
            .accept()
            .await
            .map_err(AcceptorError::Accept)?;

        Ok(stream)
    }
}

impl AsRawFd for Acceptor {
    fn as_raw_fd(&self) -> RawFd {
        self.listener.as_raw_fd()
    }
}

impl AsFd for Acceptor {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.listener.as_fd()
    }
}

impl Drop for Acceptor {
    fn drop(&mut self) {
        let _ = fs::unlink(&self.bind_path);
        let _ = fs::unlink(&self.lock_path);
    }
}

/// Builds (bind_path, lock_path) from the given directory and socket name.
fn build_paths(directory: &Path, socket_name: &str) -> (PathBuf, PathBuf) {
    (
        directory.join(socket_name),
        directory.join(format!("{socket_name}.lock")),
    )
}

/// Attempts to lock the file at the given path.
///
/// If the file does not exist, it will be created.
fn lock_file(path: &Path) -> Result<OwnedFd, AcceptorError> {
    // Open or create file
    let fd = fs::openat(
        fs::CWD,
        path,
        fs::OFlags::CREATE | fs::OFlags::WRONLY,
        fs::Mode::RUSR | fs::Mode::WUSR,
    )
    .map_err(|err| AcceptorError::LockOpen(err.into()))?;

    // Lock file
    fs::flock(&fd, fs::FlockOperation::NonBlockingLockExclusive)
        .map_err(|err| AcceptorError::LockAcquire(err.into()))?;

    Ok(fd)
}

/// Returns the `XDG_RUNTIME_DIR` directory.
fn xdg_runtime_dir() -> Result<PathBuf, AcceptorError> {
    let dir = env::var("XDG_RUNTIME_DIR")
        .map(PathBuf::from)
        .map_err(|_| AcceptorError::RuntimeDirInvalid)?;

    if !dir.is_absolute() {
        return Err(AcceptorError::RuntimeDirInvalid);
    }

    Ok(dir)
}
