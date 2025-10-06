import Mathlib.Data.Nat.Basic
import Library.Basic

math2001_init

/-- If 3 ∤ n, then 13 ∣ (3^(2*n) + 3^n + 1) -/

theorem div_by_thirteen (n : ℕ) (h : ¬ 3 ∣ n) :
  13 ∣ (3^(2*n) + 3^n + 1) :=
sorry
