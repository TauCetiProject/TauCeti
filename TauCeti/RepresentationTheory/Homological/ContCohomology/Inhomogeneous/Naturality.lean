/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Comparison
import TauCeti.Algebra.Category.ModuleCat.Topology.Iso
import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Naturality of dehomogenization in continuous cochains

`TopRep.continuousInhomogeneousCochainsMap` acts by postcomposition with a continuous
equivariant linear map. Over a locally compact group,
`TopRep.continuousInhomogeneousCochainsIso_inv_naturality` identifies it with Mathlib's
`ContinuousCohomology.cochainsMap` via dehomogenization. The pointwise comparison uses
`TopRep.resolutionEval_resolutionMap_apply`.

See Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §2,
for the homogeneous and inhomogeneous cochain conventions.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X Y : TopRep.{max v w} k G}
  {hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2}
  {hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2}

/-- Over a locally compact group, dehomogenization commutes with maps of coefficients whose
actions are jointly continuous. -/
@[reassoc]
theorem continuousInhomogeneousCochainsIso_inv_naturality [LocallyCompactSpace G] (f : X ⟶ Y) :
    ((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).map
        (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f) ≫
      (continuousInhomogeneousCochainsIso Y hY).inv =
    (continuousInhomogeneousCochainsIso X hX).inv ≫ continuousInhomogeneousCochainsMap f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply ContinuousMap.ext
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [continuousInhomogeneousCochainsMap_f_apply,
    continuousInhomogeneousCochainsIso_inv_f_apply, continuousInhomogeneousCochainsIso_inv_f_apply,
    homogeneousCochainsLinearEquiv_apply, homogeneousCochainsLinearEquiv_apply]
  rw [Functor.mapHomologicalComplex_map_f, TopModuleCat.hom_forget₂_ModuleCat_map]
  have hval :
      Subtype.val (((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f).f n).hom a) =
        (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom a.val :=
    TauCeti.ContinuousCohomology.coe_cochainsMap_f_apply (ContinuousMonoidHom.id G) f n a
  exact (congrArg (fun b ↦ resolutionEval Y (n + 1) b (Fin.partialProd x)) hval).trans
    (resolutionEval_resolutionMap_apply X (ContinuousMonoidHom.id G) f (n + 1)
      a.val (Fin.partialProd x))

end TopRep
