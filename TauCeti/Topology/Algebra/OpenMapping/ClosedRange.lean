/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Henkel
public import TauCeti.Topology.Algebra.Group.FirstCountable
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Closed range criteria from the open mapping theorem

This file proves closed-range criteria for continuous linear maps by applying
`TauCeti.HasZeroSequenceOfUnits.isQuotientMap` to the coproduct `Φ(x, y) = f x + y` from
`E × G` onto `F`, where `G` is an algebraic complement of `f.range`: the preimage of `f.range`
under `Φ` is `{p : E × G | p.2 = 0}`, which is closed in `E × G`.

## Main results

* `ContinuousLinearMap.isClosed_range_of_isCompl_of_completeSpace_right`: if `f : E →L[R] F` is a
  continuous linear map from a complete first-countable uniform module `E` into a `T₀` Baire
  topological additive module `F` with continuous fixed scalar actions (`ContinuousConstSMul R F`)
  over a topological ring with a zero sequence of units, and `G` is a first-countable algebraic
  complement of `f.range` complete for its canonical additive uniformity, with scalar orbits
  continuous at zero on both `E` and `G`, then `f.range` is closed.
* `ContinuousLinearMap.isClosed_range_of_isCompl_of_isClosed_right_of_complete`: specialization
  where `F` is itself a complete first-countable uniform module, scalar multiplication is jointly
  continuous (`ContinuousSMul`) on both `E` and `F`, and `G` is a closed algebraic complement.

The finite-dimensional cokernel specialization over complete nontrivially normed fields lives in
`TauCeti.Topology.Algebra.OpenMapping.FiniteCokernel`.
-/

public section

open Filter Function Topology
open scoped Uniformity

namespace ContinuousLinearMap

section Complement

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
  [Module R F] [ContinuousConstSMul R F]

/-- **Closed range from a complete first-countable algebraic complement.** If `f : E →L[R] F` is a
continuous linear map from a complete first-countable uniform module `E` into a `T₀` Baire
topological additive module `F` with continuous fixed scalar actions (`ContinuousConstSMul R F`)
over a topological ring with a zero sequence of units, and `G` is a first-countable algebraic
complement of `f.range` that is complete for its canonical additive uniformity, with scalar orbits
continuous at zero on both `E` and `G`, then `f.range` is closed.

No injectivity assumption (`f.ker = ⊥`) and no uniform structure, completeness, or
first-countability on the ambient codomain `F` is required: the coproduct `Φ(x, y) = f x + y` from
`E × G` onto `F` is a quotient map by `TauCeti.HasZeroSequenceOfUnits.isQuotientMap`, and the
preimage `Φ ⁻¹' f.range = {p | p.2 = 0}` is closed. -/
theorem isClosed_range_of_isCompl_of_completeSpace_right (f : E →L[R] F) (G : Submodule R F)
    (hG : IsCompl f.range G) [@CompleteSpace G (IsTopologicalAddGroup.rightUniformSpace G)]
    [(𝓝 (0 : G)).IsCountablyGenerated]
    (hcE : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hcG : ∀ y : G, ContinuousAt (fun a : R ↦ a • y) 0) :
    IsClosed (f.range : Set F) := by
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
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
map between complete first-countable uniform modules (with `T₀` target) with jointly continuous
scalar multiplication (`ContinuousSMul`) on both `E` and `F` over a topological ring with a zero
sequence of units, and `G` is a closed algebraic complement of `f.range`, then `f.range` is
closed. -/
theorem isClosed_range_of_isCompl_of_isClosed_right_of_complete
    (f : E →L[R] F) (G : Submodule R F) (hG : IsCompl f.range G)
    (hG_closed : IsClosed (G : Set F)) :
    IsClosed (f.range : Set F) := by
  have : @CompleteSpace G (IsTopologicalAddGroup.rightUniformSpace G) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq (G := G)]
    exact hG_closed.completeSpace_coe
  have : (𝓤 F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact f.isClosed_range_of_isCompl_of_completeSpace_right G hG
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)

end ClosedComplement

end ContinuousLinearMap

end
