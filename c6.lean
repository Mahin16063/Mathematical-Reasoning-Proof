/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Nat.Basic
import Library.Basic
import Library.Tactic.ModEq   -- for `by rel [...]` on [ZMOD _]

math2001_init

-- If c | a - b and c | b then c | a.
lemma dvd_multiple_minus_multiple {a b c : ℤ}
    (h1 : c ∣ a - b) (h2 : c ∣ b) : c ∣ a := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a = a - b + b := by ring
    _ = c * x + c * y := by rw [hx, hy]
    _ = c * (x + y) := by ring

/-- If `3 ∤ n`, then `13 ∣ (3^(2*n) + 3^n + 1)`. -/
theorem div_by_thirteen (n : ℕ) (h : ¬ (3 : ℤ) ∣ n) :
  13 ∣ ((3 : ℤ) ^ (2 * n) + (3 : ℤ) ^ n + 1) := by

  -- Period 3 modulo 13: (3^3) ≡ 1, hence 3^(3*b) ≡ 1 for all b.
  have h1 : ∀ b : ℕ, (3 : ℤ) ^ (3 * b) ≡ 1 [ZMOD 13] := by
    intro b
    -- show 3^3 ≡ 1 [ZMOD 13] by proving 13 ∣ (3^3 - 1) = 26
    have base : (3 : ℤ) ^ 3 ≡ 1 [ZMOD 13] := by
      change (13 : ℤ) ∣ ((3 : ℤ) ^ 3 - 1)
      have : (3 : ℤ) ^ 3 - 1 = 26 := by norm_num
      simpa [this] using (show (13 : ℤ) ∣ 26 from ⟨2, by norm_num⟩)
    calc
      (3 : ℤ) ^ (3 * b) = ((3 : ℤ) ^ 3) ^ b := by
        simpa [pow_mul]
      _ ≡ 1 ^ b [ZMOD 13] := by simpa using base.pow b
      _ ≡ 1 [ZMOD 13] := by norm_num

  -- Since 3 ∤ n, n % 3 is 1 or 2, so n = 3k + 1 or n = 3k + 2.
  have h2 : ∃ k : ℕ, n = 3 * k + 1 ∨ n = 3 * k + 2 := by
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
    interval_cases r : n % 3 using hlt.
    · -- r = 0 ⇒ 3 ∣ n (contradiction)
      have h2 : ∃ k : ℕ, n = 3 * k + 1 ∨ n = 3 * k + 2 := by
        have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
        interval_cases r : n % 3 using hlt
        case zero =>
          have : (3 : ℤ) ∣ n := by
            have eq := Nat.mod_add_div n 3
            have : n = 3 * (n / 3) := by simpa [r] using eq
            exact ⟨(n / 3 : ℕ), by simpa [this, Int.ofNat_mul]⟩
          exact (h this).elim
        case one =>
          exact ⟨n / 3, Or.inl (by simpa [r, Nat.mod_add_div])⟩
        case two =>
          exact ⟨n / 3, Or.inr (by simpa [r, Nat.mod_add_div])⟩

    · -- r = 1
      refine ⟨n / 3, ?_⟩
      left
      have := Nat.mod_add_div n 3
      simpa [r, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
    · -- r = 2
      refine ⟨n / 3, ?_⟩
      right
      have := Nat.mod_add_div n 3
      simpa [r, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm

  obtain ⟨k, hk⟩ := h2
  obtain h3 | h3 := hk

  -- Case 1: n = 3k + 1
  ·
    -- 3^(2*(3k)) ≡ 1 ⇒ 3^(2*(3k)) * 3^2 ≡ 3^2
    have h4 : (3 : ℤ) ^ (2 * 3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      have : (3 : ℤ) ^ (3 * k) ≡ 1 [ZMOD 13] := h1 k
      simpa using (by rel [this] :
        (3 : ℤ) ^ (2 * 3 * k) * 3 ^ 2 ≡ 1 ^ 2 * 3 ^ 2 [ZMOD 13])
    -- 3^(3k) ≡ 1 ⇒ 3^(3k) * 3 ≡ 3
    have h5 : (3 : ℤ) ^ (3 * k) * 3 ≡ 3 [ZMOD 13] := by
      simpa using (by rel [h1 k] :
        (3 : ℤ) ^ (3 * k) * 3 ≡ 1 * 3 [ZMOD 13])
    -- Expand 3^(2*(3k+1)) and 3^(3k+1)
    have hsum :
      (3 : ℤ) ^ (2 * (3 * k + 1)) + 3 ^ (3 * k + 1) + 1
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 2 + 3 ^ (3 * k) * 3 + 1 [ZMOD 13] := by
      simpa [pow_add, two_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
             Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    -- Sum ≡ 13 ≡ 0
    have hzero :
        (3 : ℤ) ^ (2 * n) + 3 ^ n + 1 ≡ 0 [ZMOD 13] := by
      simpa [h3] using
        (calc
          (3 : ℤ) ^ (2 * (3 * k + 1)) + 3 ^ (3 * k + 1) + 1
              ≡ 3 ^ (2 * 3 * k) * 3 ^ 2 + 3 ^ (3 * k) * 3 + 1 [ZMOD 13] := hsum
          _ ≡ 3 ^ 2 + 3 + 1 [ZMOD 13] := by rw [h4, h5]
          _ = 13 := by norm_num
          _ ≡ 0 [ZMOD 13] := by
            change (13 : ℤ) ≡ 0 [ZMOD 13]
            simpa using Int.ModEq.zero_of_dvd (show (13 : ℤ) ∣ 13 from ⟨1, by norm_num⟩)))
    simpa using hzero

  -- Case 2: n = 3k + 2
  ·
    -- 3^(2*(3k)) ≡ 1 ⇒ 3^(2*(3k)) * 3^4 ≡ 3^4
    have h4 : (3 : ℤ) ^ (2 * 3 * k) * 3 ^ 4 ≡ 3 ^ 4 [ZMOD 13] := by
      have : (3 : ℤ) ^ (3 * k) ≡ 1 [ZMOD 13] := h1 k
      simpa using (by rel [this] :
        (3 : ℤ) ^ (2 * 3 * k) * 3 ^ 4 ≡ 1 ^ 2 * 3 ^ 4 [ZMOD 13])
    -- 3^(3k) ≡ 1 ⇒ 3^(3k) * 3^2 ≡ 3^2
    have h5 : (3 : ℤ) ^ (3 * k) * 3 ^ 2 ≡ 3 ^ 2 [ZMOD 13] := by
      simpa using (by rel [h1 k] :
        (3 : ℤ) ^ (3 * k) * 3 ^ 2 ≡ 1 * 3 ^ 2 [ZMOD 13])
    -- Expand 3^(2*(3k+2)) and 3^(3k+2)
    have hsum :
      (3 : ℤ) ^ (2 * (3 * k + 2)) + 3 ^ (3 * k + 2) + 1
        ≡ 3 ^ (2 * 3 * k) * 3 ^ 4 + 3 ^ (3 * k) * 3 ^ 2 + 1 [ZMOD 13] := by
      simpa [pow_add, two_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
             Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    -- Sum ≡ 91 ≡ 0
    have hzero :
        (3 : ℤ) ^ (2 * n) + 3 ^ n + 1 ≡ 0 [ZMOD 13] := by
      simpa [h3] using
        (calc
          (3 : ℤ) ^ (2 * (3 * k + 2)) + 3 ^ (3 * k + 2) + 1
              ≡ 3 ^ (2 * 3 * k) * 3 ^ 4 + 3 ^ (3 * k) * 3 ^ 2 + 1 [ZMOD 13] := hsum
          _ ≡ 3 ^ 4 + 3 ^ 2 + 1 [ZMOD 13] := by rw [h4, h5]
          _ = 81 + 9 + 1 := by norm_num
          _ = 91 := by norm_num
          _ ≡ 0 [ZMOD 13] := by
            change (91 : ℤ) ≡ 0 [ZMOD 13]
            simpa using Int.ModEq.zero_of_dvd (show (13 : ℤ) ∣ 91 from ⟨7, by norm_num⟩)))
    simpa using hzero
