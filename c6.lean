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
  13 ∣ (3^(2*n) + 3^n + 1) := by
  have h1 : ∀b, 3 ^ (3 * b) ≡ 1 [ZMOD 13] := by
    sorry
  have h2 : ∃k : ℕ, n = 3 * k + 1 ∨ n = 3 * k + 2 := by
    sorry
  obtain⟨k,hk⟩ := h2
  obtain h3 | h3 := hk
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      sorry
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      sorry
    sorry
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      sorry
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      sorry
    sorry
