# Version 1.0.1

- Xcode needs `_Atomic(...)` instead of `volatile *` first arguments in `atomic_exchange` etc.
- added `./configure --pedantic` to test for C11 conformance (removes `popen` and thus compressed reading)
