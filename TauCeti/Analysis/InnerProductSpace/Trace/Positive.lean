/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.RealAlgebra

/-!
# The extended trace of positive operators

`ContinuousLinearMap.positiveTrace` is the canonical trace, with values in `ℝ≥0∞`,
on the positive cone of bounded operators on a real or complex Hilbert space. It is
computed in any Hilbert basis by summing the nonnegative diagonal coefficients.
There is no separability or finite-trace assumption.

The construction uses the Hilbert–Schmidt energy of the positive square root; basis
independence follows from basis independence of that energy. The diagonal formula gives
additivity, positive homogeneity and monotonicity. The rectangular identity
`positiveTrace (T† T) = positiveTrace (T T†)` relates this trace to Hilbert–Schmidt
operators, and the finite-dimensional formula agrees with the usual algebraic trace.

Only values on positive operators are intended for use; the definition is zero off the
positive cone. In particular it is not a linear trace on all bounded operators.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  revised edition, Academic Press, 1980, Section VI.6.
-/

public section

open scoped InnerProductSpace InnerProduct ComplexOrder NNReal ENNReal
open InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section RealAlgebra

-- Restriction of scalars supplies the real functional calculus over any `RCLike` field.
attribute [local instance] realAlgebra realIsScalarTower

/-- The extended trace on the positive cone, defined as the Hilbert–Schmidt energy of the
positive square root. It is zero on operators outside the positive cone. -/
noncomputable def positiveTrace (T : E →L[𝕜] E) : ℝ≥0∞ :=
  (CFC.sqrt T).hilbertSchmidtEnergy (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- The extended trace is zero outside the positive cone. -/
theorem positiveTrace_of_not_nonneg {T : E →L[𝕜] E} (hT : ¬ 0 ≤ T) :
    T.positiveTrace = 0 := by
  simp [positiveTrace, CFC.sqrt_of_not_nonneg hT]

private theorem positiveTrace_exists_sq_eq {T : E →L[𝕜] E} (hT : 0 ≤ T)
    (b : HilbertBasis ι 𝕜 E) :
    ∃ S : E →L[𝕜] E, 0 ≤ S ∧ S * S = T ∧ T.positiveTrace = S.hilbertSchmidtEnergy b :=
  ⟨CFC.sqrt T, CFC.sqrt_nonneg T, CFC.sqrt_mul_sqrt_self T hT,
    (CFC.sqrt T).hilbertSchmidtEnergy_indep _ b⟩

end RealAlgebra

/-- The extended positive trace is the energy of the square root in any Hilbert basis,
for any real algebra structure on the operators compatible with the `𝕜`-action. -/
theorem positiveTrace_eq_hilbertSchmidtEnergy_sqrt
    [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    (T : E →L[𝕜] E) (b : HilbertBasis ι 𝕜 E) :
    T.positiveTrace = (CFC.sqrt T).hilbertSchmidtEnergy b := by
  by_cases hT : 0 ≤ T
  · obtain ⟨S, hS, hSq, hTrace⟩ := positiveTrace_exists_sq_eq hT b
    rwa [CFC.sqrt_unique hSq hS]
  · simp [positiveTrace_of_not_nonneg hT, CFC.sqrt_of_not_nonneg hT]

attribute [local instance] realAlgebra realIsScalarTower in
/-- **The diagonal formula for the positive trace.** Any Hilbert basis, including an
uncountable or empty one, computes the trace by its nonnegative diagonal coefficients. -/
theorem positiveTrace_eq_tsum (T : E →L[𝕜] E) (hT : 0 ≤ T)
    (b : HilbertBasis ι 𝕜 E) :
    T.positiveTrace = ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, T (b i)⟫_𝕜) := by
  rw [T.positiveTrace_eq_hilbertSchmidtEnergy_sqrt b, hilbertSchmidtEnergy_def]
  refine tsum_congr fun i => ?_
  have hs := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint.adjoint_eq
  have hsq : (CFC.sqrt T)† ∘L CFC.sqrt T = T := by
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self T hT
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    @norm_sq_eq_re_inner 𝕜, ← adjoint_inner_right, ← comp_apply, hsq]

/-- The zero operator has zero positive trace. -/
@[simp]
theorem positiveTrace_zero : (0 : E →L[𝕜] E).positiveTrace = 0 := by
  simp [positiveTrace]

/-- The extended positive trace is additive on positive operators, even at infinite trace. -/
theorem positiveTrace_add {S T : E →L[𝕜] E} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (S + T).positiveTrace = S.positiveTrace + T.positiveTrace := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [positiveTrace_eq_tsum _ (add_nonneg hS hT) b,
    positiveTrace_eq_tsum _ hS b, positiveTrace_eq_tsum _ hT b, ← tsum_add]
  refine tsum_congr fun i => ?_
  simp only [add_apply, inner_add_right, map_add]
  exact ENNReal.ofReal_add (nonneg_iff_isPositive.mp hS |>.re_inner_nonneg_right _)
    (nonneg_iff_isPositive.mp hT |>.re_inner_nonneg_right _)

/-- The extended positive trace distributes over finite sums of positive operators. -/
theorem positiveTrace_sum {s : Finset ι} {f : ι → E →L[𝕜] E} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i).positiveTrace = ∑ i ∈ s, (f i).positiveTrace := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [positiveTrace_add (hf i (Finset.mem_insert_self i s)) (Finset.sum_nonneg hs), ih hs]

/-- Scaling by a nonnegative scalar scales the trace by its extended norm, including the
convention `0 * ∞ = 0` and the zero extension off the positive cone. -/
theorem positiveTrace_smul_of_nonneg (T : E →L[𝕜] E) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).positiveTrace = ‖c‖ₑ * T.positiveTrace := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases hT : 0 ≤ T
  swap
  · have hscaled : ¬ 0 ≤ c • T := by
      intro h
      have hback := (nonneg_iff_isPositive.mp h).smul_of_nonneg (inv_nonneg.mpr hc)
      apply hT
      simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using
        (nonneg_iff_isPositive.mpr hback)
    rw [positiveTrace_of_not_nonneg hscaled, positiveTrace_of_not_nonneg hT, mul_zero]
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [positiveTrace_eq_tsum _ (nonneg_iff_isPositive.mpr
      ((nonneg_iff_isPositive.mp hT).smul_of_nonneg hc)) b,
    positiveTrace_eq_tsum _ hT b, ← ENNReal.tsum_mul_left]
  obtain ⟨r, hr, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp hc
  refine tsum_congr fun i => ?_
  rw [smul_apply, inner_smul_right, RCLike.re_ofReal_mul, ENNReal.ofReal_mul hr,
    ← ofReal_norm, RCLike.norm_of_nonneg hr]

/-- Scaling by a nonnegative real scales the extended trace by that real. -/
@[simp]
theorem positiveTrace_smul [SMul ℝ≥0 (E →L[𝕜] E)] [IsScalarTower ℝ≥0 𝕜 (E →L[𝕜] E)]
    (T : E →L[𝕜] E) (r : ℝ≥0) : (r • T).positiveTrace = r * T.positiveTrace := by
  have h : r • (1 : 𝕜) = ((r : ℝ) : 𝕜) := by
    simp [NNReal.smul_def, RCLike.real_smul_eq_coe_mul]
  rw [← smul_one_smul 𝕜 r T, h,
    T.positiveTrace_smul_of_nonneg (RCLike.ofReal_nonneg.2 r.coe_nonneg),
    ← ofReal_norm, RCLike.norm_of_nonneg r.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- The positive trace, extended by zero off the positive cone, is monotone. -/
theorem positiveTrace_mono {S T : E →L[𝕜] E} (hST : S ≤ T) :
    S.positiveTrace ≤ T.positiveTrace := by
  by_cases hS : 0 ≤ S
  swap
  · rw [positiveTrace_of_not_nonneg hS]
    exact zero_le
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [positiveTrace_eq_tsum _ hS b, positiveTrace_eq_tsum _ (hS.trans hST) b]
  refine tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
  have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hST)).re_inner_nonneg_right (b i)
  simpa only [sub_apply, inner_sub_right, map_sub, sub_nonneg] using h

/-- Taking the adjoint preserves the extended trace, including its zero extension. -/
@[simp]
theorem positiveTrace_adjoint (T : E →L[𝕜] E) : (T†).positiveTrace = T.positiveTrace := by
  by_cases hT : 0 ≤ T
  · rw [(nonneg_iff_isPositive.mp hT).isSelfAdjoint.adjoint_eq]
  · have hAdj : ¬ 0 ≤ T† := by
      intro h
      have hEq := (nonneg_iff_isPositive.mp h).isSelfAdjoint.adjoint_eq
      rw [adjoint_adjoint] at hEq
      exact hT (hEq.symm ▸ h)
    rw [positiveTrace_of_not_nonneg hAdj, positiveTrace_of_not_nonneg hT]

/-- Taking the star of an operator preserves its extended positive trace. -/
@[simp]
theorem positiveTrace_star (T : E →L[𝕜] E) : (star T).positiveTrace = T.positiveTrace :=
  T.positiveTrace_adjoint

/-- The trace of the source Gram operator is the Hilbert–Schmidt energy of the operator. -/
theorem positiveTrace_adjoint_comp_self (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (T† ∘L T).positiveTrace = T.hilbertSchmidtEnergy b := by
  rw [positiveTrace_eq_tsum _ (nonneg_iff_isPositive.mpr T.isPositive_adjoint_comp_self) b,
    hilbertSchmidtEnergy_def]
  refine tsum_congr fun i => ?_
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **The rectangular trace identity.** Source and target may have different dimensions and
cardinalities; the two traces are equal even when infinite. -/
theorem positiveTrace_adjoint_comp_self_eq_positiveTrace_self_comp_adjoint (T : E →L[𝕜] F) :
    (T† ∘L T).positiveTrace = (T ∘L T†).positiveTrace := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨κ, c, -⟩ := exists_hilbertBasis 𝕜 F
  calc
    (T† ∘L T).positiveTrace = T.hilbertSchmidtEnergy b :=
      positiveTrace_adjoint_comp_self T b
    _ = (T†).hilbertSchmidtEnergy c := (T.hilbertSchmidtEnergy_adjoint b c).symm
    _ = (T ∘L T†).positiveTrace := by
      simpa only [adjoint_adjoint] using (positiveTrace_adjoint_comp_self (T†) c).symm

attribute [local instance] realAlgebra realIsScalarTower in
/-- Unitary transport preserves the positive trace. -/
@[simp]
theorem positiveTrace_conjStarAlgEquiv (T : E →L[𝕜] E) (U : E ≃ₗᵢ[𝕜] F) :
    (U.conjStarAlgEquiv T).positiveTrace = T.positiveTrace := by
  by_cases hT : 0 ≤ T
  swap
  · have hconj : ¬ 0 ≤ U.conjStarAlgEquiv T := by
      intro h
      apply hT
      simpa only [StarAlgEquiv.symm_apply_apply] using map_nonneg U.conjStarAlgEquiv.symm h
    rw [positiveTrace_of_not_nonneg hT, positiveTrace_of_not_nonneg hconj]
  let A := (U : E →L[𝕜] F) ∘L CFC.sqrt T
  have hs := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint.adjoint_eq
  have hsource : A† ∘L A = T := by
    ext x
    simp only [A, adjoint_comp, U.adjoint_eq_symm, comp_apply,
      LinearIsometryEquiv.coe_coe'', U.symm_apply_apply, hs]
    exact congr($(CFC.sqrt_mul_sqrt_self T hT) x)
  have htarget : A ∘L A† = U.conjStarAlgEquiv T := by
    ext x
    simp only [A, adjoint_comp, U.adjoint_eq_symm, comp_apply,
      LinearIsometryEquiv.coe_coe'', hs,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    exact congr(U ($(CFC.sqrt_mul_sqrt_self T hT) (U.symm x)))
  rw [← htarget, ← positiveTrace_adjoint_comp_self_eq_positiveTrace_self_comp_adjoint A, hsource]

attribute [local instance] realAlgebra realIsScalarTower in
/-- The positive trace dominates the operator norm. -/
theorem enorm_le_positiveTrace {T : E →L[𝕜] E} (hT : 0 ≤ T) :
    ‖T‖ₑ ≤ T.positiveTrace := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hn : ‖CFC.sqrt T‖ₑ ^ 2 = ‖T‖ₑ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint.norm_mul_self,
      CFC.sqrt_mul_sqrt_self T hT, ofReal_norm]
  rw [← hn, T.positiveTrace_eq_hilbertSchmidtEnergy_sqrt b]
  exact enorm_sq_le_hilbertSchmidtEnergy _ b

/-- A positive operator has zero trace exactly when it is zero. -/
@[simp]
theorem positiveTrace_eq_zero_iff {T : E →L[𝕜] E} (hT : 0 ≤ T) :
    T.positiveTrace = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have he : ‖T‖ₑ = 0 := le_antisymm ((enorm_le_positiveTrace hT).trans_eq h) zero_le
  simpa only [← ofReal_norm, ENNReal.ofReal_eq_zero, norm_le_zero_iff] using he

/-- In finite dimension the positive trace agrees with the usual, unnormalized trace. -/
theorem positiveTrace_eq_ofReal_trace [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E}
    (hT : 0 ≤ T) :
    T.positiveTrace = ENNReal.ofReal (RCLike.re (T.toLinearMap.trace 𝕜 E)) := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [positiveTrace_eq_tsum T hT b.toHilbertBasis, LinearMap.trace_eq_sum_inner _ b,
    map_sum, ENNReal.ofReal_sum_of_nonneg]
  · simp [tsum_fintype]
  · intro i _
    exact (nonneg_iff_isPositive.mp hT).re_inner_nonneg_right _

/-- The positive rank-one operator `x ↦ ⟪v,x⟫ v` has trace `‖v‖²` in every dimension. -/
@[simp]
theorem positiveTrace_rankOne_self (v : E) :
    (rankOne 𝕜 v v).positiveTrace = ‖v‖ₑ ^ 2 := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [positiveTrace_eq_tsum _ (nonneg_iff_isPositive.mpr (isPositive_rankOne_self v)) b,
    ← b.tsum_enorm_sq_inner v]
  refine tsum_congr fun i => ?_
  rw [inner_right_rankOne_apply, ← inner_conj_symm (b i) v, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]
  simp only [← ofReal_norm, RCLike.norm_conj, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The identity has trace equal to the cardinality of any Hilbert basis, interpreted in
`ℝ≥0∞`. Thus infinite-dimensional spaces have infinite identity trace. -/
theorem _root_.HilbertBasis.positiveTrace_one (b : HilbertBasis ι 𝕜 E) :
    (1 : E →L[𝕜] E).positiveTrace = ENat.card ι := by
  rw [positiveTrace_eq_tsum _ (nonneg_iff_isPositive.mpr isPositive_one) b]
  simp [b.orthonormal.norm_eq_one, ENNReal.tsum_one]

/-- The trace of the identity in finite dimension is the dimension, without normalization. -/
@[simp]
theorem positiveTrace_one_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    (1 : E →L[𝕜] E).positiveTrace = Module.finrank 𝕜 E := by
  rw [(stdOrthonormalBasis 𝕜 E).toHilbertBasis.positiveTrace_one]
  simp

/-- In infinite dimension the identity has infinite positive trace, even for nonseparable
Hilbert spaces. -/
theorem positiveTrace_one_of_not_finiteDimensional (hE : ¬ FiniteDimensional 𝕜 E) :
    (1 : E →L[𝕜] E).positiveTrace = ∞ := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Infinite ι := by
    by_contra! hι
    have := Fintype.ofFinite ι
    exact hE (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  rw [b.positiveTrace_one]
  simp

end ContinuousLinearMap
