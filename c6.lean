/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq
import Library.Basic

math2001_init

-- If c | a - b and c | b then c | a.
lemma dvd_multiple_minus_multiple {a b c : ℤ} (h1 : c ∣ a - b) (h2 : c ∣ b) : c ∣ a := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a = a - b + b := by ring
    _ = c * x + c * y := by rw [hx, hy]
    _ = c * (x + y) := by ring

/-- If 3 ∤ n, then 13 ∣ (3 ^ (2 * n) + 3 ^ n + 1) -/

theorem div_by_thirteen (n : ℕ) (h : ¬ (3 : ℤ) ∣ n) :
    13 ∣ (3 ^ (2 * n) + 3 ^ n + 1) := by

  have h1 : ∀ (b : ℕ), 3 ^ (3 * b) ≡ 1 [ZMOD 13] := by
    intro b
    have base : 3 ^ 3 ≡ 1 [ZMOD 13] := by exact rfl
    calc
      3 ^ (3 * b) = (3 ^ 3) ^ b := by exact pow_mul 3 3 b
      _ ≡ 1 ^ b [ZMOD 13] := by exact Int.ModEq.pow b base
      _ ≡ 1 [ZMOD 13] := by norm_num

  have h2 : ∃k : ℕ, n = 3 * k + 1 ∨ n = 3 * k + 2 := by
    sorry
  obtain ⟨k, hk⟩ := h2
  obtain h3 | h3 := hk
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      calc
        3 ^ (2 * (3 * k)) * 3 ^ 2 ≡ (3 ^ (3 * k)) ^ 2 * 3 ^ 2 [ZMOD 13] := by sorry
        _ ≡ 1 ^ 2 * 3 ^ 2 [ZMOD 13] := by rw [h1, k]
        _ ≡ 3 ^ 2 [ZMOD 13] := by norm_num
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      calc
        3 ^ (3 * k) * 3 ≡ 1 * 3 [ZMOD 13] := by exact Int.ModEq.mul (h1 k) rfl
        _ ≡ 3 [ZMOD 13] := by norm_num
    calc
      3 ^ (2 * (3 * k + 1)) + 3 ^ (3 * k + 1) + 1
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 2 + 3 ^ (3 * k) * 3 + 1 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 2 + 3 + 1 [ZMOD 13] := by sorry
        _ ≡ 0 [ZMOD 13] := by exact rfl
    exact Int.ModEq.dvd (by norm_num)
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      calc
        3 ^ (2 * 3 * k) * 3 ^ 4 ≡ (3 ^ (3 * k)) ^ 2 * 3 ^ 4 [ZMOD 13] := by sorry 
        _ ≡ 1 ^ 2 * 3 ^ 4 [ZMOD 13] := by rw [h1, k]
        _ ≡ 3 ^ 4 [ZMOD 13] := by norm_num
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      calc
      3 ^ (3 * k) * 3 ^ 2 ≡ 1 * 3 ^ 2 [ZMOD 13] := by rw [h1, k]
        _ ≡ 3 ^ 2 [ZMOD 13] := by norm_num
    calc
      3 ^ (2 * (3 * k + 2)) + 3 ^ (3 * k + 2) + 1
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 4 + 3 ^ (3 * k) * 3 ^ 2 + 1 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 4 + 3 ^ 2 + 1 [ZMOD 13] := by sorry
        _ ≡ 0 [ZMOD 13] := by exact rfl
    exact Int.ModEq.dvd (by norm_num)
