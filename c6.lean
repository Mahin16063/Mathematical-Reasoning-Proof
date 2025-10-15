import Mathlib.Data.Nat.Basic
import Library.Basic

math2001_init

-- If c | a - b and c | b then c | a.
lemma dvd_multiple_minus_multiple {a b c : ℤ} (h1 : c ∣ a - b) (h2 : c ∣ b) : c ∣ a := by
  obtain⟨x,hx⟩ := h1
  obtain⟨y,hy⟩ := h2
  use x + y
  calc
    a = a - b + b := by ring
    _ = c * x + c * y := by rw[hx,hy]
    _ = c * (x + y) := by ring

/-- If 3 ∤ n, then 13 ∣ (3^(2*n) + 3^n + 1) -/

theorem div_by_thirteen (n : ℕ) (h : ¬ (3 : ℤ) ∣ n) :
  13 ∣ (3^(2*n) + 3^n + 1) :=
sorry
