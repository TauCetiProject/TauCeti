/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.KummerContiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.KummerLimit

/-!
# The recurrence of the continued fraction for Tricomi's function

DLMF 8.9.1 expands `Γ(a + 1) e^z γ*(a, z)`, for `a ∉ {−1, −2, …}` and every `z`, as the continued
fraction `a₁/(b₁ + a₂/(b₂ + ⋯))` with

* `b₁ = 1` and `b_n = a + n − 1` for `n ≥ 2`;
* `a₁ = 1`, `a₂ = −z`, `a_{2k} = −(a + k − 1) z` for `k ≥ 2` and `a_{2k+1} = k z` for `k ≥ 1`.

This file defines these partial numerators and denominators and an explicit solution `f` of the
three-term recurrence `f(n + 1) = b_n f(n) + a_n f(n − 1)` (`n ≥ 1`) attached to the fraction,
namely `f(0) = 1` and, for `n ≥ 1`,

  `f(n) = (−1)^{⌈n/2⌉} Γ(a + 1) z^{n−1} d_n 𝐌(⌈n/2⌉, a + n, z)`,

where `𝐌` is the regularized Kummer function, `d₁ = 1`, `d_{2k} = (a + 1)_{k−1} (k − 1)!` and
`d_{2k+1} = (a + 1)_{k−1} k!`. Its first two values give `−f(1)/f(0) = Γ(a + 1) e^z γ*(a, z)`,
the value that DLMF 8.9.1 assigns to the fraction. By Pincherle's theorem the fraction converges
to this value once `f` is shown to be the minimal solution of the recurrence, which uses the
large-parameter limit `Complex.tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two` of the Kummer
function.

## Main definitions

* `Complex.tricomiIncompleteGammaPartNum a z n` — the partial numerators `a_n` of DLMF 8.9.1;
* `Complex.tricomiIncompleteGammaPartDen a n` — the partial denominators `b_n`;
* `Complex.tricomiIncompleteGammaContFracSol a z n` — the solution `f(n)` above.

## Main results

* `Complex.tricomiIncompleteGammaContFracSol_succ_succ` — `f` solves the recurrence of the
  fraction, for `a ∉ {−1, −2, …}`;
* `Complex.tricomiIncompleteGammaContFracSol_zero`, `tricomiIncompleteGammaContFracSol_one` —
  `f(0) = 1` and `f(1) = −Γ(a + 1) e^z γ*(a, z)`;
* `Complex.tricomiIncompleteGammaContFracSol_two_mul_add_one`,
  `tricomiIncompleteGammaContFracSol_two_mul_add_two` — `f` at odd and at positive even indices;
* `Complex.eventually_tricomiIncompleteGammaContFracSol_ne_zero` — for `z ≠ 0`, `f(n) ≠ 0` for all
  large `n`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82.
-/

public section

noncomputable section

open Filter Polynomial
open scoped Nat

namespace Complex

/-- The partial numerators of the continued fraction DLMF 8.9.1 for `Γ(a + 1) e^z γ*(a, z)`:
`a₁ = 1`, `a₂ = −z`, `a_{2k} = −(a + k − 1) z` for `k ≥ 2` and `a_{2k+1} = k z` for `k ≥ 1`.
The fraction has no partial numerator of index `0`, where the value is `0`. -/
def tricomiIncompleteGammaPartNum (a z : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => -z
  | n + 3 => if Even n then ((n + 3) / 2 : ℕ) * z else -(a + ((n + 3) / 2 : ℕ) - 1) * z

/-- The partial denominators of the continued fraction DLMF 8.9.1 for `Γ(a + 1) e^z γ*(a, z)`:
`b₁ = 1` and `b_n = a + n − 1` for `n ≥ 2`. The fraction has head `0` and no partial denominator
of index `0`, where the value is `0`. -/
def tricomiIncompleteGammaPartDen (a : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => a + (n + 1)

@[simp]
theorem tricomiIncompleteGammaPartNum_zero (a z : ℂ) : tricomiIncompleteGammaPartNum a z 0 = 0 :=
  (rfl)

@[simp]
theorem tricomiIncompleteGammaPartNum_one (a z : ℂ) : tricomiIncompleteGammaPartNum a z 1 = 1 :=
  (rfl)

@[simp]
theorem tricomiIncompleteGammaPartNum_two (a z : ℂ) : tricomiIncompleteGammaPartNum a z 2 = -z :=
  (rfl)

/-- The odd partial numerators `a_{2k+3} = (k + 1) z` of DLMF 8.9.1. -/
@[simp]
theorem tricomiIncompleteGammaPartNum_two_mul_add_three (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaPartNum a z (2 * k + 3) = (k + 1) * z := by
  simp only [tricomiIncompleteGammaPartNum, even_two_mul, ite_true]
  rw [show (2 * k + 3) / 2 = k + 1 by omega]
  push_cast
  ring

/-- The even partial numerators `a_{2k+4} = −(a + k + 1) z` of DLMF 8.9.1. -/
@[simp]
theorem tricomiIncompleteGammaPartNum_two_mul_add_four (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaPartNum a z (2 * k + 4) = -(a + k + 1) * z := by
  rw [show 2 * k + 4 = (2 * k + 1) + 3 by omega]
  simp only [tricomiIncompleteGammaPartNum, Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k),
    ite_false]
  rw [show (2 * k + 1 + 3) / 2 = k + 2 by omega]
  push_cast
  ring

@[simp]
theorem tricomiIncompleteGammaPartDen_zero (a : ℂ) : tricomiIncompleteGammaPartDen a 0 = 0 :=
  (rfl)

@[simp]
theorem tricomiIncompleteGammaPartDen_one (a : ℂ) : tricomiIncompleteGammaPartDen a 1 = 1 :=
  (rfl)

/-- The partial denominators `b_{n+2} = a + n + 1` of DLMF 8.9.1. -/
@[simp]
theorem tricomiIncompleteGammaPartDen_add_two (a : ℂ) (n : ℕ) :
    tricomiIncompleteGammaPartDen a (n + 2) = a + (n + 1) :=
  (rfl)

/-- The explicit solution of the three-term recurrence of the continued fraction DLMF 8.9.1:
`f(0) = 1` and, for `n ≥ 1`, `f(n) = (−1)^{⌈n/2⌉} Γ(a + 1) z^{n−1} d_n 𝐌(⌈n/2⌉, a + n, z)`, with
`d_n = (a + 1)_{⌊n/2⌋−1} ⌊(n − 1)/2⌋!` (so `d₁ = 1`, `d_{2k} = (a + 1)_{k−1} (k − 1)!` and
`d_{2k+1} = (a + 1)_{k−1} k!`). It solves the recurrence by
`tricomiIncompleteGammaContFracSol_succ_succ`, and `−f(1)/f(0) = Γ(a + 1) e^z γ*(a, z)` is the
value that DLMF 8.9.1 assigns to the fraction. -/
def tricomiIncompleteGammaContFracSol (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else
    (-1) ^ ((n + 1) / 2) * Gamma (a + 1) * z ^ (n - 1) *
      ((ascPochhammer ℂ (n / 2 - 1)).eval (a + 1) * ((n - 1) / 2)!) *
        regularizedHGFun {(((n + 1) / 2 : ℕ) : ℂ)} {a + n} z

@[simp]
theorem tricomiIncompleteGammaContFracSol_zero (a z : ℂ) :
    tricomiIncompleteGammaContFracSol a z 0 = 1 := by
  simp [tricomiIncompleteGammaContFracSol]

/-- The solution of DLMF 8.9.1 at odd indices:
`f(2k + 1) = (−1)^{k+1} Γ(a + 1) z^{2k} (a + 1)_{k−1} k! 𝐌(k + 1, a + 2k + 1, z)`, where at `k = 0`
the truncated index `k − 1 = 0` gives `d₁ = 1`. -/
theorem tricomiIncompleteGammaContFracSol_two_mul_add_one (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaContFracSol a z (2 * k + 1) =
      (-1) ^ (k + 1) * Gamma (a + 1) * z ^ (2 * k) *
        ((ascPochhammer ℂ (k - 1)).eval (a + 1) * k !) *
          regularizedHGFun {(k : ℂ) + 1} {a + (2 * k + 1)} z := by
  rw [tricomiIncompleteGammaContFracSol, ite_eq_right (by omega),
    show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 - 1 = k - 1 by omega,
    show (2 * k + 1 - 1) / 2 = k by omega, Nat.add_sub_cancel]
  push_cast
  ring

/-- The solution of DLMF 8.9.1 at positive even indices:
`f(2k + 2) = (−1)^{k+1} Γ(a + 1) z^{2k+1} (a + 1)_k k! 𝐌(k + 1, a + 2k + 2, z)`. -/
theorem tricomiIncompleteGammaContFracSol_two_mul_add_two (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaContFracSol a z (2 * k + 2) =
      (-1) ^ (k + 1) * Gamma (a + 1) * z ^ (2 * k + 1) *
        ((ascPochhammer ℂ k).eval (a + 1) * k !) *
          regularizedHGFun {(k : ℂ) + 1} {a + (2 * k + 2)} z := by
  rw [tricomiIncompleteGammaContFracSol, ite_eq_right (by omega),
    show (2 * k + 2 + 1) / 2 = k + 1 by omega, show (2 * k + 2) / 2 - 1 = k by omega,
    show (2 * k + 2 - 1) / 2 = k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega]
  push_cast
  ring

/-- The first value of the solution of DLMF 8.9.1, `f(1) = −Γ(a + 1) e^z γ*(a, z)`, so that
`−f(1)/f(0) = Γ(a + 1) e^z γ*(a, z)` is the value that DLMF 8.9.1 assigns to the fraction. -/
theorem tricomiIncompleteGammaContFracSol_one (a z : ℂ) :
    tricomiIncompleteGammaContFracSol a z 1 =
      -(Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z) := by
  have h := tricomiIncompleteGammaContFracSol_two_mul_add_one a z 0
  simp only [mul_zero, zero_add, pow_one, pow_zero, Nat.zero_sub, ascPochhammer_zero, eval_one,
    Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, mul_one] at h
  rw [h, tricomiIncompleteGamma_def, ← mul_assoc, mul_assoc (Gamma (a + 1)), ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero]
  ring

/-- The recurrence of DLMF 8.9.1 at `n = 1`: `f(2) = f(1) + f(0)`. -/
private theorem tricomiIncompleteGammaContFracSol_two {a : ℂ} (ha : Gamma (a + 1) ≠ 0) (z : ℂ) :
    tricomiIncompleteGammaContFracSol a z 2 = tricomiIncompleteGammaContFracSol a z 1 + 1 := by
  have h := tricomiIncompleteGammaContFracSol_two_mul_add_two a z 0
  have hM := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z
  rw [tricomiIncompleteGamma_def, tricomiIncompleteGamma_def] at hM
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, ascPochhammer_zero, eval_one,
    Nat.factorial_zero, Nat.cast_one, mul_one] at h
  rw [h, tricomiIncompleteGammaContFracSol_one, tricomiIncompleteGamma_def, hM,
    show a + 1 + 1 = a + 2 by ring]
  field_simp
  rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  ring

/-- The recurrence of DLMF 8.9.1 at `n = 2`: `f(3) = (a + 1) f(2) − z f(1)`. -/
private theorem tricomiIncompleteGammaContFracSol_three (a z : ℂ) :
    tricomiIncompleteGammaContFracSol a z 3 =
      (a + 1) * tricomiIncompleteGammaContFracSol a z 2 -
        z * tricomiIncompleteGammaContFracSol a z 1 := by
  have h₃ := tricomiIncompleteGammaContFracSol_two_mul_add_one a z 1
  have h₂ := tricomiIncompleteGammaContFracSol_two_mul_add_two a z 0
  have h₁ := tricomiIncompleteGammaContFracSol_two_mul_add_one a z 0
  have hM := regularizedHGFun_singleton_singleton_eq_mul_add_mul 1 (a + 1) z
  norm_num at h₃ h₂ h₁ hM
  rw [h₃, h₂, h₁]
  rw [show a + 1 + 1 = a + 2 by ring, show a + 1 + 2 = a + 3 by ring] at hM
  linear_combination (-(Gamma (a + 1) * z)) * hM

/-- The recurrence of DLMF 8.9.1 at the odd indices `n = 2k + 3`:
`f(2k + 4) = (a + 2k + 2) f(2k + 3) + (k + 1) z f(2k + 2)`. -/
private theorem tricomiIncompleteGammaContFracSol_two_mul_add_four (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaContFracSol a z (2 * k + 4) =
      (a + (2 * k + 2)) * tricomiIncompleteGammaContFracSol a z (2 * k + 3) +
        (k + 1) * z * tricomiIncompleteGammaContFracSol a z (2 * k + 2) := by
  have h₄ := tricomiIncompleteGammaContFracSol_two_mul_add_two a z (k + 1)
  have h₃ := tricomiIncompleteGammaContFracSol_two_mul_add_one a z (k + 1)
  have h₂ := tricomiIncompleteGammaContFracSol_two_mul_add_two a z k
  have hM := regularizedHGFun_singleton_singleton_eq_mul_sub_mul (k + 1) (a + (2 * k + 2)) z
  rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring] at h₄
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at h₃
  rw [h₄, h₃, h₂, ascPochhammer_succ_eval, Nat.add_sub_cancel, Nat.factorial_succ]
  rw [show a + (2 * k + 2) + 1 = a + (2 * (k + 1) + 1) by ring,
    show a + (2 * k + 2) + 2 = a + (2 * (k + 1) + 2) by ring] at hM
  push_cast
  linear_combination ((-1) ^ k * Gamma (a + 1) * z ^ (2 * k + 2) *
    (ascPochhammer ℂ k).eval (a + 1) * (k + 1) * k !) * hM

/-- The recurrence of DLMF 8.9.1 at the even indices `n = 2k + 4`:
`f(2k + 5) = (a + 2k + 3) f(2k + 4) − (a + k + 1) z f(2k + 3)`. -/
private theorem tricomiIncompleteGammaContFracSol_two_mul_add_five (a z : ℂ) (k : ℕ) :
    tricomiIncompleteGammaContFracSol a z (2 * k + 5) =
      (a + (2 * k + 3)) * tricomiIncompleteGammaContFracSol a z (2 * k + 4) -
        (a + k + 1) * z * tricomiIncompleteGammaContFracSol a z (2 * k + 3) := by
  have h₅ := tricomiIncompleteGammaContFracSol_two_mul_add_one a z (k + 2)
  have h₄ := tricomiIncompleteGammaContFracSol_two_mul_add_two a z (k + 1)
  have h₃ := tricomiIncompleteGammaContFracSol_two_mul_add_one a z (k + 1)
  have hM := regularizedHGFun_singleton_singleton_eq_mul_add_mul (k + 2) (a + (2 * k + 3)) z
  rw [show 2 * (k + 2) + 1 = 2 * k + 5 by ring] at h₅
  rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring] at h₄
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at h₃
  rw [h₅, h₄, h₃, show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, ascPochhammer_succ_eval,
    Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  rw [show (k : ℂ) + 2 = k + 1 + 1 by ring, show (k : ℂ) + 1 + 1 + 1 = k + 2 + 1 by ring,
    show a + (2 * k + 3) + 1 = a + (2 * (k + 1) + 2) by ring,
    show a + (2 * k + 3) + 2 = a + (2 * (k + 2) + 1) by ring,
    show a + (2 * k + 3) = a + (2 * (k + 1) + 1) by ring] at hM
  push_cast
  linear_combination ((-1) ^ k * Gamma (a + 1) * z ^ (2 * k + 3) *
    (ascPochhammer ℂ k).eval (a + 1) * (a + k + 1) * (k + 1) * k !) * hM

/-- The explicit solution solves the three-term recurrence of the continued fraction DLMF 8.9.1:
for `a ∉ {−1, −2, …}`, every `z` and every `n ≥ 1`, `f(n + 1) = b_n f(n) + a_n f(n − 1)`. -/
theorem tricomiIncompleteGammaContFracSol_succ_succ {a : ℂ} (ha : ∀ m : ℕ, a + 1 ≠ -m) (z : ℂ)
    (n : ℕ) :
    tricomiIncompleteGammaContFracSol a z (n + 2) =
      tricomiIncompleteGammaPartDen a (n + 1) * tricomiIncompleteGammaContFracSol a z (n + 1) +
        tricomiIncompleteGammaPartNum a z (n + 1) * tricomiIncompleteGammaContFracSol a z n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases k with _ | k
    · simpa using tricomiIncompleteGammaContFracSol_two (Gamma_ne_zero ha) z
    · rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring,
        tricomiIncompleteGammaContFracSol_two_mul_add_four,
        tricomiIncompleteGammaPartNum_two_mul_add_three,
        show 2 * k + 3 = (2 * k + 1) + 2 by ring, tricomiIncompleteGammaPartDen_add_two,
        show 2 * (k + 1) = 2 * k + 2 by ring]
      push_cast
      ring
  · rcases k with _ | k
    · simpa [sub_eq_add_neg] using tricomiIncompleteGammaContFracSol_three a z
    · rw [show 2 * (k + 1) + 1 + 2 = 2 * k + 5 by ring,
        show 2 * (k + 1) + 1 + 1 = 2 * k + 4 by ring,
        tricomiIncompleteGammaContFracSol_two_mul_add_five,
        tricomiIncompleteGammaPartNum_two_mul_add_four,
        show 2 * k + 4 = (2 * k + 2) + 2 by ring, tricomiIncompleteGammaPartDen_add_two,
        show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
      push_cast
      ring

/-- For `a ∉ {−1, −2, …}` and `z ≠ 0`, the solution of the recurrence of DLMF 8.9.1 is nonzero at
every sufficiently large index. -/
theorem eventually_tricomiIncompleteGammaContFracSol_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a + 1 ≠ -m)
    {z : ℂ} (hz : z ≠ 0) : ∀ᶠ n in atTop, tricomiIncompleteGammaContFracSol a z n ≠ 0 := by
  have hM (c : ℂ) : ∀ᶠ k : ℕ in atTop, regularizedHGFun {(k : ℂ)} {2 * k + c} z ≠ 0 := by
    filter_upwards [(tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two c z).eventually_ne
      (exp_ne_zero _)] with k hk
    exact right_ne_zero_of_mul hk
  have hP (j : ℕ) : (ascPochhammer ℂ j).eval (a + 1) ≠ 0 := by
    simp only [ne_eq, ascPochhammer_eval_eq_zero_iff, not_exists, not_and]
    intro i _ hi
    exact ha i (by rw [hi, neg_neg])
  obtain ⟨N₁, h₁⟩ := eventually_atTop.1 (hM a)
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (hM (a - 1))
  refine eventually_atTop.2 ⟨2 * (N₁ + N₂) + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := h₁ (j + 1) (by omega)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, tricomiIncompleteGammaContFracSol_two_mul_add_two]
    push_cast at h
    rw [show 2 * ((j : ℂ) + 1) + a = a + (2 * j + 2) by ring] at h
    simp [h, hz, hP, Gamma_ne_zero ha, Nat.factorial_ne_zero]
  · have h := h₂ (k + 1) (by omega)
    rw [tricomiIncompleteGammaContFracSol_two_mul_add_one]
    push_cast at h
    rw [show 2 * ((k : ℂ) + 1) + (a - 1) = a + (2 * k + 1) by ring] at h
    simp [h, hz, hP, Gamma_ne_zero ha, Nat.factorial_ne_zero]

end Complex
