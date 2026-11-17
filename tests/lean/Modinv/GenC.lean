import Aeneas.Deep.CDriver
import Modinv.Modinv

/-! The C of the modular inversion example (from `tests/lean`: `lake env lean Modinv/GenC.lean`
writes `modinv.c` in the current directory; `Modinv/C/run.sh` compiles and runs it). -/
#deep_c "modinv.c" modinv
