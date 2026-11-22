/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Selberg's weighted Gram inequality and Gram-row bounds

For an arbitrary finite family of vectors `y : ι → E` indexed by a finite set `s : Finset ι` in a
real or complex inner-product space `E` (without completeness, finite dimensionality, linear
independence, or nonvanishing assumptions), write `r i = ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖` for the `i`-th
absolute Gram row sum.

This file proves:

* `TauCeti.sum_norm_inner_eq_zero_iff_norm_eq_zero` and `TauCeti.sum_norm_inner_eq_zero_iff`:
  a Gram row sum `r i` vanishes if and only if `‖y i‖ = 0` (respectively `y i = 0` in a normed
  inner-product space).
* `Finset.norm_sum_smul_sq_le_sum_mul_sum_norm_inner`: for any scalars `c : ι → 𝕜`,
  `‖∑ i ∈ s, c i • y i‖ ^ 2 ≤ ∑ i ∈ s, ‖c i‖ ^ 2 * r i`.
* `Finset.norm_sub_sum_smul_sq_le`: Selberg's normalized projection defect bound,
  `‖x - ∑ i ∈ s, (⟪y i, x⟫_𝕜 / r i) • y i‖ ^ 2 ≤ ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i`.
* `Finset.sum_norm_inner_sq_div_le`: **Selberg's weighted Gram inequality**,
  `∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i ≤ ‖x‖ ^ 2`, with zero rows contributing zero under totalized
  real division.
* `Finset.sum_norm_inner_sq_le_of_sum_norm_inner_le`: the uniform Gram-row inequality,
  `∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ C * ‖x‖ ^ 2` whenever `0 ≤ C` and `r i ≤ C` for all `i ∈ s`.
* `TauCeti.sum_norm_inner_sq_le_sup'_sum_norm_inner_mul_norm_sq`: the maximum-row Gram inequality
  for nonempty `s`.
* `Finset.sum_norm_inner_sq_le_of_diag_offDiag`: the diagonal/off-diagonal Gram inequality when
  `‖y i‖ ^ 2 ≤ D` and `∑ j ∈ s.erase i, ‖⟪y i, y j⟫_𝕜‖ ≤ O` with `0 ≤ D + O`.

## References

* E. Bombieri, *A note on the large sieve*, Acta Arithmetica **18** (1971), 401–404,
  Proposition 1 (attributed there to A. Selberg).
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Annals of Mathematics **191** (2020), 355–392, Theorem 7.
-/

public section

open scoped InnerProductSpace

section Seminormed

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem norm_inner_self_eq_norm_sq (x : E) : ‖⟪x, x⟫_𝕜‖ = ‖x‖ ^ 2 := by
  simp [inner_self_eq_norm_sq_to_K]

namespace TauCeti

/-- A Gram row sum `∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖` vanishes if and only if `‖y i‖ = 0`. -/
theorem sum_norm_inner_eq_zero_iff_norm_eq_zero {s : Finset ι} {y : ι → E} {i : ι} (hi : i ∈ s) :
    (∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) = 0 ↔ ‖y i‖ = 0 := by
  constructor
  · intro h
    have hdiag : ‖⟪y i, y i⟫_𝕜‖ ≤ ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖⟪y i, y j⟫_𝕜‖) (fun j _ ↦ norm_nonneg _) hi
    rw [h, norm_inner_self_eq_norm_sq] at hdiag
    nlinarith [norm_nonneg (y i)]
  · intro h
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hle : ‖⟪y i, y j⟫_𝕜‖ ≤ ‖y i‖ * ‖y j‖ := norm_inner_le_norm (y i) (y j)
    rw [h, zero_mul] at hle
    exact le_antisymm hle (norm_nonneg _)

end TauCeti

namespace Finset

/-- **Gram-row quadratic bound for a finite linear combination** (Bombieri, eq. (4)):
`‖∑ i ∈ s, c i • y i‖ ^ 2 ≤ ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖`. -/
theorem norm_sum_smul_sq_le_sum_mul_sum_norm_inner (s : Finset ι) (y : ι → E) (c : ι → 𝕜) :
    ‖∑ i ∈ s, c i • y i‖ ^ 2 ≤
      ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ := by
  have hexp :
      ‖∑ i ∈ s, c i • y i‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, RCLike.re (starRingEnd 𝕜 (c i) * c j * ⟪y i, y j⟫_𝕜) := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), sum_inner, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_smul_left, inner_smul_right, mul_assoc]
  have h1 :
      ∑ i ∈ s, ∑ j ∈ s, RCLike.re (starRingEnd 𝕜 (c i) * c j * ⟪y i, y j⟫_𝕜) ≤
        ∑ i ∈ s, ∑ j ∈ s,
          (‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖ + ‖c j‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) / 2 := by
    refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    calc
      RCLike.re (starRingEnd 𝕜 (c i) * c j * ⟪y i, y j⟫_𝕜)
          ≤ ‖starRingEnd 𝕜 (c i) * c j * ⟪y i, y j⟫_𝕜‖ := RCLike.re_le_norm _
      _ = ‖c i‖ * ‖c j‖ * ‖⟪y i, y j⟫_𝕜‖ := by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
      _ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖⟪y i, y j⟫_𝕜‖ := by
        gcongr
        nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
      _ = (‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖ + ‖c j‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) / 2 := by ring
  have hsymm :
      (∑ i ∈ s, ∑ j ∈ s, ‖c j‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) =
        ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [norm_inner_symm]
  calc
    ‖∑ i ∈ s, c i • y i‖ ^ 2
        ≤ ∑ i ∈ s, ∑ j ∈ s,
            (‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖ + ‖c j‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) / 2 := hexp.trans_le h1
    _ = ((∑ i ∈ s, ∑ j ∈ s, ‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) +
          ∑ i ∈ s, ∑ j ∈ s, ‖c j‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖) / 2 := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ ^ 2 * ‖⟪y i, y j⟫_𝕜‖ := by rw [hsymm]; ring
    _ = ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ := by
      refine Finset.sum_congr rfl fun i _ ↦ (Finset.mul_sum _ _ _).symm

/-- **Selberg's normalized projection defect bound** (Bombieri, eqs. (3)–(4)):
setting `c i = ⟪y i, x⟫_𝕜 / r i` where `r i = ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖`, we have
`‖x - ∑ i ∈ s, c i • y i‖ ^ 2 ≤ ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i`. -/
theorem norm_sub_sum_smul_sq_le (s : Finset ι) (y : ι → E) (x : E) :
    ‖x - ∑ i ∈ s, (⟪y i, x⟫_𝕜 / ((∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ : ℝ) : 𝕜)) • y i‖ ^ 2 ≤
      ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ := by
  let r : ι → ℝ := fun i ↦ ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖
  let c : ι → 𝕜 := fun i ↦ ⟪y i, x⟫_𝕜 / (r i : 𝕜)
  have hr_nonneg : ∀ i, 0 ≤ r i := fun i ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hcross :
      RCLike.re ⟪x, ∑ i ∈ s, c i • y i⟫_𝕜 = ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i := by
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only [c]
    rw [inner_smul_right, div_mul_eq_mul_div, ← inner_conj_symm x (y i), RCLike.mul_conj,
      RCLike.norm_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, RCLike.ofReal_re]
  have hquad :
      ∑ i ∈ s, ‖c i‖ ^ 2 * r i = ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hri : r i = 0
    · simp [c, hri]
    · have hnorm : ‖(r i : 𝕜)‖ = r i := by
        rw [RCLike.norm_ofReal, abs_of_nonneg (hr_nonneg i)]
      dsimp only [c]
      rw [norm_div, hnorm, norm_inner_symm]
      field_simp [hri]
  have hsub :
      ‖x - ∑ i ∈ s, c i • y i‖ ^ 2 =
        ‖x‖ ^ 2 - 2 * RCLike.re ⟪x, ∑ i ∈ s, c i • y i⟫_𝕜 + ‖∑ i ∈ s, c i • y i‖ ^ 2 :=
    norm_sub_sq (𝕜 := 𝕜) x (∑ i ∈ s, c i • y i)
  have hbound : ‖∑ i ∈ s, c i • y i‖ ^ 2 ≤ ∑ i ∈ s, ‖c i‖ ^ 2 * r i :=
    s.norm_sum_smul_sq_le_sum_mul_sum_norm_inner y c
  linarith

/-- **Selberg's weighted Gram inequality** (Bombieri 1971, Proposition 1): for every finite family
`y : ι → E` on `s : Finset ι` and every `x : E`,
`∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / (∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) ≤ ‖x‖ ^ 2`.
Zero rows contribute zero under totalized real division; no completeness, independence, or
nonvanishing assumption is needed. -/
theorem sum_norm_inner_sq_div_le (s : Finset ι) (y : ι → E) (x : E) :
    ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / (∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) ≤ ‖x‖ ^ 2 := by
  have hdef := s.norm_sub_sum_smul_sq_le (𝕜 := 𝕜) y x
  linarith [sq_nonneg ‖x - ∑ i ∈ s,
    (⟪y i, x⟫_𝕜 / ((∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ : ℝ) : 𝕜)) • y i‖]

/-- **Uniform Gram-row inequality**: if `0 ≤ C` and every Gram row sum `∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖`
for `i ∈ s` is at most `C`, then `∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ C * ‖x‖ ^ 2`. -/
theorem sum_norm_inner_sq_le_of_sum_norm_inner_le (s : Finset ι) (y : ι → E) (x : E)
    {C : ℝ} (hC : 0 ≤ C) (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ ≤ C) :
    ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  have hterm : ∀ i ∈ s,
      ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ C * (‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) := by
    intro i hi
    set r : ℝ := ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖
    by_cases hr : r = 0
    · have hy0 : ‖y i‖ = 0 := (TauCeti.sum_norm_inner_eq_zero_iff_norm_eq_zero (𝕜 := 𝕜) hi).mp hr
      have hinner0 : ‖⟪x, y i⟫_𝕜‖ = 0 := by
        have hle := norm_inner_le_norm (𝕜 := 𝕜) x (y i)
        rw [hy0, mul_zero] at hle
        exact le_antisymm hle (norm_nonneg _)
      simp [hinner0]
    · have hr0 : 0 ≤ r := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
      calc
        ‖⟪x, y i⟫_𝕜‖ ^ 2 = r * (‖⟪x, y i⟫_𝕜‖ ^ 2 / r) := by field_simp [hr]
        _ ≤ C * (‖⟪x, y i⟫_𝕜‖ ^ 2 / r) :=
          mul_le_mul_of_nonneg_right (hrow i hi) (div_nonneg (sq_nonneg _) hr0)
  calc
    ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2
        ≤ ∑ i ∈ s, C * (‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) :=
      Finset.sum_le_sum hterm
    _ = C * ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (s.sum_norm_inner_sq_div_le y x) hC

end Finset

namespace TauCeti

/-- **Maximum-row Gram inequality** (Bennett–Siksek 2020, Theorem 7): for a nonempty finite family
`y : ι → E` on `s : Finset ι`, the sum of squared inner products with `x` is at most `‖x‖ ^ 2`
times the maximum Gram row sum. -/
theorem sum_norm_inner_sq_le_sup'_sum_norm_inner_mul_norm_sq {s : Finset ι} (hs : s.Nonempty)
    (y : ι → E) (x : E) :
    ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤
      s.sup' hs (fun i ↦ ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) * ‖x‖ ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := hs
  refine s.sum_norm_inner_sq_le_of_sum_norm_inner_le y x ?_
    (fun i hi ↦ Finset.le_sup' (f := fun i ↦ ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) hi)
  exact le_trans (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)
    (Finset.le_sup' (f := fun i ↦ ∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) hi₀)

end TauCeti

namespace Finset

/-- **Diagonal/off-diagonal Gram inequality**: if `0 ≤ D + O`, `‖y i‖ ^ 2 ≤ D`, and
`∑ j ∈ s.erase i, ‖⟪y i, y j⟫_𝕜‖ ≤ O` for all `i ∈ s`, then
`∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ (D + O) * ‖x‖ ^ 2`. -/
theorem sum_norm_inner_sq_le_of_diag_offDiag [DecidableEq ι] (s : Finset ι) (y : ι → E) (x : E)
    {D O : ℝ} (hDO : 0 ≤ D + O) (hdiag : ∀ i ∈ s, ‖y i‖ ^ 2 ≤ D)
    (hoff : ∀ i ∈ s, ∑ j ∈ s.erase i, ‖⟪y i, y j⟫_𝕜‖ ≤ O) :
    ∑ i ∈ s, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ (D + O) * ‖x‖ ^ 2 := by
  refine s.sum_norm_inner_sq_le_of_sum_norm_inner_le y x hDO fun i hi ↦ ?_
  rw [← Finset.add_sum_erase _ _ hi, norm_inner_self_eq_norm_sq]
  exact add_le_add (hdiag i hi) (hoff i hi)

end Finset

end Seminormed

section Normed

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TauCeti

/-- In a normed inner-product space, a Gram row sum `∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖` vanishes if and only
if `y i = 0`. -/
theorem sum_norm_inner_eq_zero_iff {s : Finset ι} {y : ι → E} {i : ι} (hi : i ∈ s) :
    (∑ j ∈ s, ‖⟪y i, y j⟫_𝕜‖) = 0 ↔ y i = 0 := by
  rw [sum_norm_inner_eq_zero_iff_norm_eq_zero (𝕜 := 𝕜) hi, norm_eq_zero]

end TauCeti

end Normed
