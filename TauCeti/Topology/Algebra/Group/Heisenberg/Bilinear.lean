/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Bilinear
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup

/-!
# Joint continuity of the isometry action on a Heisenberg extension

The native isometry action of a bilinear form fixes the coefficient coordinate and evaluates the
isometry on the vector coordinate. For the native factor-set topology, its joint continuity is
therefore equivalent to joint continuity of evaluation on the vector space. The converse uses the
native continuous canonical section, so the equivalence needs no continuity of the bilinear form.

For a finite module with its module topology, the isometry subgroup inherits the topology on
linear automorphisms from `TauCeti.Topology.Algebra.Module.GeneralLinearGroup`. Evaluation, and
hence the native action, is jointly continuous. In particular this applies to finite-dimensional
spaces over nondiscrete local fields, including the half-alternating convention for the
oscillator action. The result applies to arbitrary bilinear forms.

The fixed-coefficient and composition laws are already provided by
`LinearMap.BilinForm.isometryGroupToMulAut_inl` and
`LinearMap.BilinForm.IsometryEquiv.extensionCongr_trans`. Group multiplication applies the right
factor first, while `IsometryEquiv.trans` applies its left argument first.

## References

* S. Kudla, *Notes on the local theta correspondence* (1996), I.1, pp. 3–4, and I.2, p. 6.
-/

public section

namespace LinearMap.BilinForm

open Multiplicative TauCeti

attribute [local instance] TauCeti.trivialMulDistribMulAction

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [TopologicalSpace R] [TopologicalSpace W] (B : LinearMap.BilinForm R W)

/-- Joint continuity of the native isometry action on the extension is equivalent to joint
continuity of evaluation on the vector space. The isometry group may carry any topology. -/
theorem continuous_isometryGroupToMulAut_apply_iff
    [TopologicalSpace (LinearMap.isometryGroup B)] :
    (Continuous fun p : LinearMap.isometryGroup B × B.bilinearFactorSet.Extension ↦
      isometryGroupToMulAut B p.1 p.2) ↔
    Continuous (fun p : LinearMap.isometryGroup B × W ↦ (p.1 : W ≃ₗ[R] W) p.2) := by
  constructor
  · intro h
    have hs : Continuous fun p : LinearMap.isometryGroup B × W ↦
        (p.1, B.bilinearFactorSet.canonicalSection (ofAdd p.2)) :=
      continuous_fst.prodMk ((FactorSet.continuous_canonicalSection _).comp
        (continuous_ofAdd.comp continuous_snd))
    simpa only [Function.comp_def, isometryGroupToMulAut_apply,
      FactorSet.canonicalSection_apply, toAdd_ofAdd] using
      continuous_toAdd.comp (FactorSet.Extension.continuous_right.comp (h.comp hs))
  · intro h
    refine FactorSet.Extension.isInducing_leftRight.continuous_iff.mpr ?_
    simp only [Function.comp_def, isometryGroupToMulAut_apply]
    exact (FactorSet.Extension.continuous_left.comp continuous_snd).prodMk
      (continuous_ofAdd.comp (h.comp (continuous_fst.prodMk
        (continuous_toAdd.comp (FactorSet.Extension.continuous_right.comp continuous_snd)))))

/-- Over a commutative ring with continuous addition and multiplication, the native isometry
action on the Heisenberg extension of a finite module is jointly continuous for the isometry
subgroup topology inside linear automorphisms. -/
@[fun_prop]
theorem continuous_isometryGroupToMulAut_apply [IsTopologicalSemiring R] [IsModuleTopology R W]
    [Module.Finite R W] :
    Continuous (fun p : LinearMap.isometryGroup B × B.bilinearFactorSet.Extension ↦
      isometryGroupToMulAut B p.1 p.2) := by
  apply (continuous_isometryGroupToMulAut_apply_iff B).mpr
  exact continuous_linearEquiv_apply.comp
    ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)

end LinearMap.BilinForm
