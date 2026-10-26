/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

import TauCeti.Analysis.MeanInequalities

/-!
# Hilbert–Schmidt energy and the Hilbert–Schmidt norm

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces and a Hilbert basis `(bᵢ)` of the
source, the **Hilbert–Schmidt energy** is the unconditional sum `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²` in
`ℝ≥0∞`. Working in `ℝ≥0∞` means that no summability hypothesis is ever needed: an operator that is
not Hilbert–Schmidt simply has energy `∞`, and iterated sums may be exchanged freely.

Expanding each column `T bᵢ` in a Hilbert basis `(cⱼ)` of the target by Parseval writes the energy
as the double sum `∑' i, ∑' j, ‖⟪cⱼ, T bᵢ⟫‖ₑ²`. Exchanging the two sums identifies it with the
energy of the adjoint, `E_b(T) = E_c(T†)`, and applying this twice shows that `E_b(T)` does not
depend on the basis `b`. Its square root therefore defines a basis-free **Hilbert–Schmidt norm**
`‖T‖_HS`, which is invariant under taking adjoints and homogeneous under scalar multiplication. For
operators of finite energy it dominates the operator norm and satisfies the two-sided ideal
inequality `‖A T B‖_HS ≤ ‖A‖ ‖T‖_HS ‖B‖`; an operator of infinite energy has `‖T‖_HS = 0`. The
square root of the energy satisfies the triangle inequality, by Minkowski's inequality for
unconditional sums in `ℝ≥0∞`, so the Hilbert–Schmidt norm is subadditive on operators of finite
energy. On a finite-dimensional source the energy is the square of the Frobenius seminorm
`TauCeti.UnitarilyInvariantSeminorm.frobenius`.

These are the norm estimates behind the Hilbert–Schmidt class of operators: its identification with
`ℓ²` families of columns, and the compactness of Hilbert–Schmidt operators.

## Main definitions

* `ContinuousLinearMap.hilbertSchmidtEnergy T b`: the energy `∑' i, ‖T bᵢ‖ₑ²` in `ℝ≥0∞`.
* `ContinuousLinearMap.hilbertSchmidtNorm T`: the Hilbert–Schmidt norm `√(E_b(T)).toReal`,
  computed in any Hilbert basis `b` of the source.

## Main results

* `ContinuousLinearMap.hilbertSchmidtEnergy_eq_tsum_tsum`: the Parseval expansion
  `E_b(T) = ∑' i, ∑' j, ‖⟪cⱼ, T bᵢ⟫‖ₑ²`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_adjoint`: `E_c(T†) = E_b(T)`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_indep`: the energy is independent of the basis.
* `ContinuousLinearMap.enorm_sq_le_hilbertSchmidtEnergy`: `‖T‖ₑ² ≤ E_b(T)`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_comp_le_left` and
  `ContinuousLinearMap.hilbertSchmidtEnergy_comp_le_right`: one-sided ideal bounds for the energy.
* `ContinuousLinearMap.hilbertSchmidtEnergy_comp_comp_le`: `E(A T B) ≤ ‖A‖ₑ² E(T) ‖B‖ₑ²`.
* `ContinuousLinearMap.rpow_hilbertSchmidtEnergy_add_le`: the triangle inequality
  `E_b(S + T)^(1/2) ≤ E_b(S)^(1/2) + E_b(T)^(1/2)`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_smul` and `ContinuousLinearMap.hilbertSchmidtNorm_smul`:
  homogeneity, `E_b(c • T) = ‖c‖ₑ² E_b(T)` and `‖c • T‖_HS = ‖c‖ ‖T‖_HS`.
* `ContinuousLinearMap.hilbertSchmidtNorm_adjoint`: `‖T†‖_HS = ‖T‖_HS`, for every operator.
* `ContinuousLinearMap.hilbertSchmidtNorm_add_le`: `‖S + T‖_HS ≤ ‖S‖_HS + ‖T‖_HS` for operators of
  finite energy.
* `ContinuousLinearMap.norm_le_hilbertSchmidtNorm` and
  `ContinuousLinearMap.hilbertSchmidtNorm_comp_comp_le`: domination of the operator norm and the
  two-sided ideal inequality for the Hilbert–Schmidt norm of a finite-energy operator.
* `ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius`: on a finite-dimensional
  source, `E_b(T) = ‖T‖_F²`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, Mathematical Surveys and
  Monographs 120, American Mathematical Society, 2005, Section 2.
-/

public section

open scoped InnerProductSpace ENNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H ι ι' κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **Hilbert–Schmidt energy** `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²` of a bounded operator `T` relative to
a Hilbert basis `(bᵢ)` of its source. It takes values in `ℝ≥0∞`, and is finite exactly for the
Hilbert–Schmidt operators. It does not depend on `b`, see `hilbertSchmidtEnergy_indep`. -/
noncomputable def hilbertSchmidtEnergy (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

theorem hilbertSchmidtEnergy_def (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b = ∑' i, ‖T (b i)‖ₑ ^ 2 :=
  (rfl)

/-- **Parseval expansion of the Hilbert–Schmidt energy.** Expanding each column `T bᵢ` in a
Hilbert basis `(cⱼ)` of the target gives `E_b(T) = ∑' i, ∑' j, ‖⟪cⱼ, T bᵢ⟫‖ₑ²`. -/
theorem hilbertSchmidtEnergy_eq_tsum_tsum (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    T.hilbertSchmidtEnergy b = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
  simp only [hilbertSchmidtEnergy_def, c.tsum_enorm_sq_inner]

@[simp]
theorem hilbertSchmidtEnergy_zero (b : HilbertBasis ι 𝕜 E) :
    (0 : E →L[𝕜] F).hilbertSchmidtEnergy b = 0 := by
  simp [hilbertSchmidtEnergy_def]

/-- The energy is homogeneous of degree two: `E_b(c • T) = ‖c‖ₑ² E_b(T)`. -/
@[simp]
theorem hilbertSchmidtEnergy_smul (c : 𝕜) (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (c • T).hilbertSchmidtEnergy b = ‖c‖ₑ ^ 2 * T.hilbertSchmidtEnergy b := by
  simp [hilbertSchmidtEnergy_def, enorm_smul, mul_pow, ENNReal.tsum_mul_left]

/-- Composition on the left with a bounded operator scales the energy by at most `‖A‖ₑ²`. -/
theorem hilbertSchmidtEnergy_comp_le_left (A : F →L[𝕜] G) (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    (A ∘L T).hilbertSchmidtEnergy b ≤ ‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b := by
  rw [hilbertSchmidtEnergy_def, hilbertSchmidtEnergy_def, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i ↦ ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ zero_le (A.le_opENorm _) 2

/-- **Triangle inequality for the Hilbert–Schmidt energy.** The square root of the energy is
subadditive: `E_b(S + T)^(1/2) ≤ E_b(S)^(1/2) + E_b(T)^(1/2)`, with no finiteness assumption. -/
theorem rpow_hilbertSchmidtEnergy_add_le (S T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (S + T).hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) ≤
      S.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) + T.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) := by
  have h := ENNReal.Lp_add_le_tsum (fun i ↦ ‖S (b i)‖ₑ) (fun i ↦ ‖T (b i)‖ₑ) one_le_two
  simp only [ENNReal.rpow_two] at h
  refine le_trans ?_ h
  gcongr
  exact ENNReal.tsum_le_tsum fun i ↦ by gcongr; exact enorm_add_le _ _

section Complete

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- **Adjoint energy swap.** For Hilbert bases `(bᵢ)` of the source and `(cⱼ)` of the target, the
energy of `T†` relative to `c` equals the energy of `T` relative to `b`: both are the double sum
`∑ ‖⟪cⱼ, T bᵢ⟫‖ₑ²`, summed in the two possible orders. -/
theorem hilbertSchmidtEnergy_adjoint (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    (adjoint T).hilbertSchmidtEnergy c = T.hilbertSchmidtEnergy b := by
  rw [hilbertSchmidtEnergy_eq_tsum_tsum _ c b, hilbertSchmidtEnergy_eq_tsum_tsum _ b c,
    ENNReal.tsum_comm]
  simp_rw [adjoint_inner_right, ← ofReal_norm, norm_inner_symm]

/-- **Basis independence of the Hilbert–Schmidt energy.** Any two Hilbert bases of the source give
the same energy. -/
theorem hilbertSchmidtEnergy_indep (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis ι' 𝕜 E) :
    T.hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b' := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [← hilbertSchmidtEnergy_adjoint T b c, hilbertSchmidtEnergy_adjoint T b' c]

/-- Composition on the right with a bounded operator scales the energy by at most `‖B‖ₑ²`. The
two energies may be computed in Hilbert bases of different spaces. -/
theorem hilbertSchmidtEnergy_comp_le_right (T : F →L[𝕜] G) (B : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) :
    (T ∘L B).hilbertSchmidtEnergy b ≤ T.hilbertSchmidtEnergy c * ‖B‖ₑ ^ 2 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis 𝕜 G
  rw [← hilbertSchmidtEnergy_adjoint _ b d, ← hilbertSchmidtEnergy_adjoint T c d, adjoint_comp,
    mul_comm, ← LinearIsometryEquiv.enorm_map adjoint B]
  exact hilbertSchmidtEnergy_comp_le_left _ _ d

/-- **Two-sided ideal inequality for the energy.** `E_b(A T B) ≤ ‖A‖ₑ² E_c(T) ‖B‖ₑ²`, where `b`
and `c` are Hilbert bases of the sources of `B` and `T`. -/
theorem hilbertSchmidtEnergy_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) :
    (A ∘L T ∘L B).hilbertSchmidtEnergy b ≤
      ‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy c * ‖B‖ₑ ^ 2 := by
  rw [mul_assoc]
  grw [hilbertSchmidtEnergy_comp_le_left A _ b, hilbertSchmidtEnergy_comp_le_right T B b c]

/-- **Hilbert–Schmidt domination of the operator norm**, in energy form: `‖T‖ₑ² ≤ E_b(T)`. -/
theorem enorm_sq_le_hilbertSchmidtEnergy (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    ‖T‖ₑ ^ 2 ≤ T.hilbertSchmidtEnergy b := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  -- `‖T x‖ₑ² = ∑' j, ‖⟪T† cⱼ, x⟫‖ₑ² ≤ (∑' j, ‖T† cⱼ‖ₑ²) ‖x‖ₑ² = E_c(T†) ‖x‖ₑ²`.
  have key (x : E) : ‖T x‖ₑ ^ 2 ≤ T.hilbertSchmidtEnergy b * ‖x‖ₑ ^ 2 := by
    rw [← hilbertSchmidtEnergy_adjoint T b c, hilbertSchmidtEnergy_def, ← ENNReal.tsum_mul_right,
      ← c.tsum_enorm_sq_inner]
    refine ENNReal.tsum_le_tsum fun j ↦ ?_
    rw [← adjoint_inner_left, ← mul_pow]
    exact pow_le_pow_left₀ zero_le (enorm_inner_le_enorm _ _) 2
  set M := T.hilbertSchmidtEnergy b ^ (2⁻¹ : ℝ)
  have hM : M ^ 2 = T.hilbertSchmidtEnergy b := ENNReal.rpow_inv_natCast_pow two_ne_zero _
  rw [← hM]
  refine pow_le_pow_left₀ zero_le (T.opENorm_le_bound fun x ↦ ?_) 2
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hM]
  exact key x

omit [CompleteSpace E] in
/-- On a finite-dimensional source, the Hilbert–Schmidt energy is the square of the Frobenius
seminorm `TauCeti.UnitarilyInvariantSeminorm.frobenius`. -/
theorem hilbertSchmidtEnergy_eq_ofReal_sq_frobenius [FiniteDimensional 𝕜 E] (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b =
      ENNReal.ofReal (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E F T.toLinearMap ^ 2) := by
  have := FiniteDimensional.complete 𝕜 E
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtEnergy_indep T b e.toHilbertBasis, hilbertSchmidtEnergy_def,
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply e,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity, tsum_fintype]
  simp [e.coe_toHilbertBasis, ENNReal.ofReal_pow]

omit [CompleteSpace F] in
/-- The **Hilbert–Schmidt norm** `‖T‖_HS = √(E_b(T)).toReal` of a bounded operator, computed in a
Hilbert basis `b` of the source chosen once and for all; by `hilbertSchmidtNorm_eq_sqrt` any Hilbert
basis gives the same value. It is meaningful for operators of finite energy: an operator of
infinite energy has Hilbert–Schmidt norm `0`. -/
noncomputable def hilbertSchmidtNorm (T : E →L[𝕜] F) : ℝ :=
  √(T.hilbertSchmidtEnergy (exists_hilbertBasis 𝕜 E).choose_spec.choose).toReal

/-- The Hilbert–Schmidt norm may be computed in any Hilbert basis of the source. -/
theorem hilbertSchmidtNorm_eq_sqrt (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtNorm = √(T.hilbertSchmidtEnergy b).toReal := by
  rw [hilbertSchmidtNorm, hilbertSchmidtEnergy_indep T _ b]

/-- The Hilbert–Schmidt norm is the real value of the square root `E_b(T)^(1/2)` of the energy,
computed in any Hilbert basis of the source. -/
theorem hilbertSchmidtNorm_eq_toReal_rpow (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtNorm = (T.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ)).toReal := by
  rw [T.hilbertSchmidtNorm_eq_sqrt b, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]

omit [CompleteSpace F] in
theorem hilbertSchmidtNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ T.hilbertSchmidtNorm :=
  Real.sqrt_nonneg _

/-- The square of the Hilbert–Schmidt norm is the real value of the energy. -/
theorem sq_hilbertSchmidtNorm (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtNorm ^ 2 = (T.hilbertSchmidtEnergy b).toReal := by
  rw [T.hilbertSchmidtNorm_eq_sqrt b, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- For an operator of finite energy, the square of the Hilbert–Schmidt norm recovers the energy
without loss. -/
theorem ofReal_sq_hilbertSchmidtNorm (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (h : T.hilbertSchmidtEnergy b ≠ ∞) :
    ENNReal.ofReal (T.hilbertSchmidtNorm ^ 2) = T.hilbertSchmidtEnergy b := by
  rw [T.sq_hilbertSchmidtNorm b, ENNReal.ofReal_toReal h]

omit [CompleteSpace F] in
@[simp]
theorem hilbertSchmidtNorm_zero : (0 : E →L[𝕜] F).hilbertSchmidtNorm = 0 := by
  simp [hilbertSchmidtNorm]

omit [CompleteSpace F] in
/-- **Homogeneity of the Hilbert–Schmidt norm.** `‖c • T‖_HS = ‖c‖ ‖T‖_HS`, for every operator. -/
@[simp]
theorem hilbertSchmidtNorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).hilbertSchmidtNorm = ‖c‖ * T.hilbertSchmidtNorm := by
  simp [hilbertSchmidtNorm, ENNReal.toReal_mul, ENNReal.toReal_pow]

/-- **Triangle inequality for the Hilbert–Schmidt norm.** If `S` and `T` have finite energy, then
`‖S + T‖_HS ≤ ‖S‖_HS + ‖T‖_HS`. -/
theorem hilbertSchmidtNorm_add_le (S T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (hS : S.hilbertSchmidtEnergy b ≠ ∞) (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    (S + T).hilbertSchmidtNorm ≤ S.hilbertSchmidtNorm + T.hilbertSchmidtNorm := by
  have hfin (U : E →L[𝕜] F) (hU : U.hilbertSchmidtEnergy b ≠ ∞) :
      U.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hU
  simp only [hilbertSchmidtNorm_eq_toReal_rpow _ b]
  rw [← ENNReal.toReal_add (hfin S hS) (hfin T hT)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin S hS, hfin T hT⟩)
    (rpow_hilbertSchmidtEnergy_add_le S T b)

/-- **Hilbert–Schmidt domination of the operator norm.** An operator of finite energy satisfies
`‖T‖ ≤ ‖T‖_HS`. -/
theorem norm_le_hilbertSchmidtNorm (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (h : T.hilbertSchmidtEnergy b ≠ ∞) : ‖T‖ ≤ T.hilbertSchmidtNorm := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg T) T.hilbertSchmidtNorm_nonneg two_ne_zero,
    T.sq_hilbertSchmidtNorm b, ← toReal_enorm, ← ENNReal.toReal_pow]
  exact ENNReal.toReal_mono h (T.enorm_sq_le_hilbertSchmidtEnergy b)

/-- **Adjoint invariance of the Hilbert–Schmidt norm.** `‖T†‖_HS = ‖T‖_HS`. -/
@[simp]
theorem hilbertSchmidtNorm_adjoint (T : E →L[𝕜] F) :
    (adjoint T).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [hilbertSchmidtNorm_eq_sqrt _ c, hilbertSchmidtNorm_eq_sqrt _ b,
    hilbertSchmidtEnergy_adjoint T b c]

/-- **Two-sided ideal inequality for the Hilbert–Schmidt norm.** If `T` has finite energy, then
`‖A T B‖_HS ≤ ‖A‖ ‖T‖_HS ‖B‖`. -/
theorem hilbertSchmidtNorm_comp_comp_le [CompleteSpace H] (A : G →L[𝕜] H) (T : F →L[𝕜] G)
    (B : E →L[𝕜] F) (c : HilbertBasis ι' 𝕜 F) (h : T.hilbertSchmidtEnergy c ≠ ∞) :
    (A ∘L T ∘L B).hilbertSchmidtNorm ≤ ‖A‖ * T.hilbertSchmidtNorm * ‖B‖ := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hle := hilbertSchmidtEnergy_comp_comp_le A T B b c
  have hfin : ‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy c * ‖B‖ₑ ^ 2 ≠ ∞ := by
    simp [ENNReal.mul_eq_top, h]
  rw [← pow_le_pow_iff_left₀ (hilbertSchmidtNorm_nonneg _)
    (by have := T.hilbertSchmidtNorm_nonneg; positivity) two_ne_zero,
    sq_hilbertSchmidtNorm _ b, mul_pow, mul_pow, T.sq_hilbertSchmidtNorm c]
  convert ENNReal.toReal_mono hfin hle using 1
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

end Complete

end ContinuousLinearMap
