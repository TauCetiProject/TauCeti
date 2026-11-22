/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Henkel
public import TauCeti.Topology.Algebra.Group.FirstCountable
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Analysis.Normed.Ring.ZeroSequenceOfUnits

/-!
# Closed range criteria from the open mapping theorem

This file proves closed-range criteria for continuous linear maps by applying
`TauCeti.HasZeroSequenceOfUnits.isQuotientMap` to the coproduct `Φ(x, y) = f x + y` from
`E × G` onto `F`, where `G` is an algebraic complement of `f.range`: the preimage of `f.range`
under `Φ` is `{p : E × G | p.2 = 0}`, which is closed in `E × G`.

## Main results

* `ContinuousLinearMap.isClosed_range_of_isCompl_of_completeSpace_right`: if `f : E →L[R] F` is a
  continuous linear map from a complete first-countable uniform module `E` into a `T₀` Baire
  uniform module `F` over a topological ring with a zero sequence of units, and `G` is a complete
  first-countable algebraic complement of `f.range`, with scalar orbits continuous at zero on both
  `E` and `G`, then `f.range` is closed.
* `ContinuousLinearMap.isClosed_range_of_isCompl_of_isClosed_right_of_complete`: specialization
  where `F` is itself complete and first countable and `G` is a closed algebraic complement.
* `ContinuousLinearMap.isClosed_range_of_finite_coker`: over a complete nontrivially normed field,
  a continuous linear map from a complete first-countable uniform vector space into a `T₀` Baire
  topological vector space with finite-dimensional cokernel has closed range.

## Attribution & References

The coproduct argument generalizes the former Banach-space proof of
`ContinuousLinearMap.isClosed_range_of_finite_coker` in
`TauCeti/Analysis/Fredholm/ClosedRange.lean`.

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1 (for the
  Banach-space closed-range criterion from a finite-dimensional cokernel).
-/

public section

open Filter Function Topology
open scoped Uniformity

namespace ContinuousLinearMap

section Complement

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F] [BaireSpace F]
  [Module R F] [ContinuousConstSMul R F]

/-- **Closed range from a complete first-countable algebraic complement.** If `f : E →L[R] F` is a
continuous linear map from a complete first-countable uniform module `E` into a `T₀` Baire uniform
module `F` over a topological ring with a zero sequence of units, and `G` is a complete
first-countable algebraic complement of `f.range` with scalar orbits continuous at zero on both `E`
and `G`, then `f.range` is closed.

No injectivity assumption (`f.ker = ⊥`) and no completeness or first-countability on the ambient
codomain `F` is required: the coproduct `Φ(x, y) = f x + y` from `E × G` onto `F` is a quotient
map by `TauCeti.HasZeroSequenceOfUnits.isQuotientMap`, and the preimage
`Φ ⁻¹' f.range = {p | p.2 = 0}` is closed. -/
theorem isClosed_range_of_isCompl_of_completeSpace_right (f : E →L[R] F) (G : Submodule R F)
    (hG : IsCompl f.range G) [CompleteSpace G] [(𝓝 (0 : G)).IsCountablyGenerated]
    (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcG : ∀ y : G, ContinuousAt (fun a : R ↦ a • y) 0) :
    IsClosed (f.range : Set F) := by
  let Φ : (E × G) →L[R] F := f.coprod G.subtypeL
  have hsurj : Surjective Φ := LinearMap.range_eq_top.mp <| by
    dsimp only [Φ]
    rw [ContinuousLinearMap.range_coprod, Submodule.toLinearMap_subtypeL, Submodule.range_subtype,
      hG.sup_eq_top]
  have hpre : Φ ⁻¹' (f.range : Set F) = {p : E × G | p.snd = 0} := by
    ext p
    simp only [Φ, Set.mem_preimage, SetLike.mem_coe, Set.mem_ofPred_eq,
      ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply]
    exact (f.range.add_mem_iff_right (f.mem_range_self p.fst)).trans
      (Submodule.mem_left_iff_eq_zero_of_disjoint hG.disjoint)
  have hclosed : IsClosed (Φ ⁻¹' (f.range : Set F)) := by
    rw [hpre]
    exact isClosed_eq continuous_snd continuous_const
  have hc : ∀ p : E × G, ContinuousAt (fun a : R ↦ a • p) 0 := fun p ↦
    (hcE p.1).prodMk (hcG p.2)
  have hq : IsQuotientMap Φ :=
    TauCeti.HasZeroSequenceOfUnits.isQuotientMap Φ hsurj Φ.continuous.continuousAt hc
  exact hq.isClosed_preimage.mp hclosed

end Complement

section ClosedComplement

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousSMul R F]

/-- **Closed range from a closed algebraic complement.** If `f : E →L[R] F` is a continuous linear
map between complete first-countable uniform modules (with `T₀` target) over a topological ring
with a zero sequence of units, and `G` is a closed algebraic complement of `f.range`, then `f.range`
is closed. -/
theorem isClosed_range_of_isCompl_of_isClosed_right_of_complete
    (f : E →L[R] F) (G : Submodule R F) (hG : IsCompl f.range G)
    (hG_closed : IsClosed (G : Set F)) :
    IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG_closed.completeSpace_coe
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact f.isClosed_range_of_isCompl_of_completeSpace_right G hG
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)

end ClosedComplement

section FiniteCoker

/-- **Closed range from a finite-dimensional cokernel.** Let `f : E →L[𝕜] F` be a continuous
linear map from a complete first-countable uniform vector space `E` into a `T₀` Baire
topological vector space `F` over a complete nontrivially normed field `𝕜`. If the cokernel
`F ⧸ f.range` is finite dimensional, then `f.range` is closed.

This applies to all Fréchet spaces, F-spaces, and Banach spaces over `ℝ`, `ℂ`, or `ℚ_[p]`, with
no local convexity, normability, or injectivity hypothesis, and requires neither completeness nor
first-countability on the ambient codomain `F`. -/
theorem isClosed_range_of_finite_coker {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (f : E →L[𝕜] F) [FiniteDimensional 𝕜 (F ⧸ f.range)] :
    IsClosed (f.range : Set F) := by
  obtain ⟨G, hG⟩ := f.range.exists_isCompl
  have : FiniteDimensional 𝕜 G := (f.range.quotientEquivOfIsCompl G hG).finiteDimensional
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕜 G
  have : FirstCountableTopology G := (Module.finBasis 𝕜 G).equivFun
    |>.toContinuousLinearEquiv.toHomeomorph.isInducing.firstCountableTopology
  exact f.isClosed_range_of_isCompl_of_completeSpace_right G hG
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)

end FiniteCoker

end ContinuousLinearMap

end
