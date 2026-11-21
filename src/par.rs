//! Work-stealing parallel loop over an index range, and a portable prefetch.

use std::sync::atomic::{AtomicUsize, Ordering};

/// Runs `f(&mut state, i)` for every i in 0..n on `threads` threads, each with its own
/// state from `init`. Returns the results in index order and the per-thread states.
pub fn run<S: Send, R: Send>(
    n: usize,
    threads: usize,
    init: impl Fn() -> S + Sync,
    f: impl Fn(&mut S, usize) -> R + Sync,
) -> (Vec<R>, Vec<S>) {
    let next = AtomicUsize::new(0);
    let per: Vec<(Vec<(usize, R)>, S)> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..threads.max(1))
            .map(|_| {
                s.spawn(|| {
                    let mut st = init();
                    let mut out = Vec::new();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= n {
                            break;
                        }
                        out.push((i, f(&mut st, i)));
                    }
                    (out, st)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut results: Vec<Option<R>> = (0..n).map(|_| None).collect();
    let mut states = Vec::with_capacity(per.len());
    for (out, st) in per {
        for (i, r) in out {
            results[i] = Some(r);
        }
        states.push(st);
    }
    (results.into_iter().map(Option::unwrap).collect(), states)
}

/// Like `run` without per-thread state.
pub fn map<R: Send>(n: usize, threads: usize, f: impl Fn(usize) -> R + Sync) -> Vec<R> {
    run(n, threads, || (), |_, i| f(i)).0
}

#[inline(always)]
pub fn prefetch<T>(p: &T) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        std::arch::x86_64::_mm_prefetch(p as *const T as *const i8, std::arch::x86_64::_MM_HINT_T0);
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        std::arch::asm!("prfm pldl1keep, [{0}]", in(reg) p as *const T, options(nostack, readonly, preserves_flags));
    }
}
