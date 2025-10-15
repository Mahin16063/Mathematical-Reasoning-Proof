/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Nat.Basic
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
  have h1 : ∀ b, 3 ^ (3 * b) ≡ 1 [ZMOD 13] := by
    intro b
    have base : 3 ^ 3 ≡ 1 [ZMOD 13] := by -- not sure if it should be like this Teo --
      calc
        3 ^ 3 = 27 := by ring
        _ = 26 + 1 := by ring
        _ ≡ 1 [ZMOD 13] := by use 2
      calc
        3 ^ (3 * b) = (3 ^ 3) ^ b := by sorry
        _ ≡ 1 ^ b [ZMOD 13] := by sorry
        _ ≡ 1 [ZMOD 13] := by ring
  have h2 : ∃k : ℕ, n = 3 * k + 1 ∨ n = 3 * k + 2 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 := by
      exact nat.exists_eq_add_of_lt (Nat.mod_lt n (by norm_num : 0 < 3))
    sorry -- I think there has to be something else here, don't know how to continue Teo --
  obtain ⟨k, hk⟩ := h2
  obtain h3 | h3 := hk
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      calc
        3 ^ (2 * 3 * k) * 3 ^ 2
          ≡ (3 ^ (3 * k)) ^ 2 * 3 ^ 2 [ZMOD 13] := by sorry
        _ ≡ 1 ^ 2 * 3 ^ 2 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 2 [ZMOD 13] := by numbers
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      calc
        3 ^ (3 * k) * 3 ≡ 1 * 3 [ZMOD 13] := by sorry
        _ ≡ 3 [ZMOD 13] := by numbers
    calc
      3 ^ (2 * (3 * k + 1)) + 3 ^ (3 * k + 1) + 1 
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 2 + 3 ^ (3 * k) * 3 + 1 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 2 + 3 + 1 [ZMOD 13] := by rw [h4, h5]
        _ ≡ 0 [ZMOD 13] := by numbers
    exact Int.ModEq.dvd 
  . have h4 : 3 ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      calc
        3 ^ (3 * k) * 3 ^ 2 ≡ (3 ^ (3 * k)) ^ 2 * 3 ^ 4 [ZMOD 13] := by sorry
        _ ≡ 1 ^ 2 * 3 ^ 4 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 4 [ZMOD 13] := by numbers
    have h5 : 3 ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      calc
        3 ^ (3 * k) * 3 ^ 2 ≡ 1 * 3 ^ 2 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 2 [ZMOD 13] := by numbers
    calc
      3 ^ (2 * (3 * k + 2)) + 3 ^ (3 * k + 2) + 1
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 4 + 3 ^ (3 * k) * 3 ^ 2 + 1 [ZMOD 13] := by sorry
        _ ≡ 3 ^ 4 + 3 ^ 2 + 1 [ZMOD 13] := by rw [h4, h5]
        _ ≡ 0 [ZMOD 13] := by numbers
    exact Int. ModEq.dvd 
