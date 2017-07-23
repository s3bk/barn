use libc;

thread_local! {
    static ERRNO: *const i32 = unsafe { libc::__errno_location() };
}

#[inline(always)]
pub fn syscall_result(ret: isize) -> Result<isize, isize> {
    if ret >= 0 {
        Ok(ret)
    } else if ret == -1 {
        Err(ERRNO.with(|&e| unsafe { *e }) as isize)
    } else {
        Err(-ret)
    }
}


pub mod futex {
    use std::sync::atomic::AtomicU32;
    use std::time::Duration;
    use util::*;
    use libc;
    use syscall_alt::syscalls::Syscall;
    use syscall_alt::constants::linux_like::SyscallResult::*;
    use super::syscall_result;

    #[derive(Debug)]
    pub enum FutexError {
        OsError(i32)
    }
    use self::FutexError::*;

    enum FutexOp {
        Wait = 0,
        Wake = 1
    }
    
    #[inline]
    pub fn wait(atomic: &AtomicU32, val: u32, timeout: Option<Duration>) -> Result<(), FutexError> {
        let timeout = timeout.map(timespec);

        let r = unsafe {
            Syscall::futex.syscall6(
                atomic as *const AtomicU32 as isize, // int *uaddr
                FutexOp::Wait as isize,              // int futex_op
                val as isize,                        // int val
                ptr_opt(timeout.as_ref()) as isize,  // const struct timespec *timeout
                0,                                   // int *uaddr2
                0                                    // int val3
            )
        };
        match syscall_result(r) {
            Ok(_)      => Ok(()),
            Err(EAGAIN) => Ok(()),
            Err(e)     => Err(OsError(e as i32))
        }
    }

    #[inline]
    pub fn wake_n(atomic: &AtomicU32, n: i32) -> Result<(), FutexError> {
        let r = unsafe {
            Syscall::futex.syscall6(
                atomic as *const AtomicU32 as isize, // int *uaddr
                FutexOp::Wake as isize,              // int futex_op
                n as isize,                          // int val
                0,                                   // const struct timespec *timeout
                0,                                   // int *uaddr2
                0                                    // int val3
            )
        };
        match syscall_result(r) {
            Ok(_) => Ok(()),
            Err(e) => Err(OsError(e as i32))
        }
    }
    #[inline(always)]
    pub fn wake_all(atomic: &AtomicU32) -> Result<(), FutexError> {
        wake_n(atomic, libc::c_int::max_value())
    }
    #[inline(always)]
    pub fn wake_one(atomic: &AtomicU32) -> Result<(), FutexError> {
        wake_n(atomic, 1)
    }
}
