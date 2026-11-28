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
  [IsTopologicalGroup G] {X Y Z : TopRep.{max v w} k G}
  {hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2}
  {hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2}
  {hZ : Continuous fun p : G × Z.V ↦ Z.ρ p.1 p.2}

-- The bundled cochain map exposes this square via `HomologicalComplex.Hom.comm`.
private theorem compLeftContinuous_comm_continuousInhomogeneousCochains_d (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom (f.hom.toContinuousLinearMap.compLeftContinuous k (Fin n → G)).toLinearMap ≫
        (continuousInhomogeneousCochains Y hY).d n (n + 1) =
      (continuousInhomogeneousCochains X hX).d n (n + 1) ≫
        ModuleCat.ofHom
          (f.hom.toContinuousLinearMap.compLeftContinuous k (Fin (n + 1) → G)).toLinearMap := by
  ext a x : 3
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CochainComplex.of_d, ModuleCat.hom_ofHom]
  -- Read postcomposition at each evaluation point.
  have happly (i : ℕ) (b : C(Fin i → G, X.V)) (y : Fin i → G) :
      ((f.hom.toContinuousLinearMap.compLeftContinuous k (Fin i → G)).toLinearMap b) y =
        f.hom (b y) := by
    let l := f.hom.toContinuousLinearMap
    have h₁ := ContinuousLinearMap.compLeftContinuous_apply k (Fin i → G) l b
    have h₂ := AddMonoidHom.compLeftContinuous_apply (Fin i → G) l.toLinearMap.toAddMonoidHom
      l.continuous b
    have h₃ := congrArg (fun c : C(Fin i → G, Y.V) ↦ c y) (h₁.trans h₂)
    exact h₃.trans (ContIntertwiningMap.toContinuousLinearMap_apply _ _)
  simp only [happly, continuousInhomogeneousCochainsD_apply, map_add, map_sum, map_zsmul,
    hom_comm_apply]

/-- The map on continuous inhomogeneous cochains induced by a continuous equivariant linear map
between representations with jointly continuous actions. It postcomposes each cochain with
the coefficient map. -/
noncomputable def continuousInhomogeneousCochainsMap (f : X ⟶ Y) :
    continuousInhomogeneousCochains X hX ⟶ continuousInhomogeneousCochains Y hY where
  f n := ModuleCat.ofHom
    (f.hom.toContinuousLinearMap.compLeftContinuous k (Fin n → G)).toLinearMap
  comm' n _ h := h ▸ compLeftContinuous_comm_continuousInhomogeneousCochains_d f n

/-- Evaluating the induced cochain map applies the coefficient map to the cochain value. -/
@[simp]
theorem continuousInhomogeneousCochainsMap_f_apply (f : X ⟶ Y) (n : ℕ)
    (a : C(Fin n → G, X.V)) (x : Fin n → G) :
    ((continuousInhomogeneousCochainsMap (hX := hX) (hY := hY) f).f n).hom a x =
      f.hom (a x) := (rfl)

/-- The identity on coefficients induces the identity on continuous inhomogeneous cochains. -/
@[simp]
theorem continuousInhomogeneousCochainsMap_id :
    continuousInhomogeneousCochainsMap (hX := hX) (hY := hX) (𝟙 X) = 𝟙 _ := by
  ext n a : 3
  apply ContinuousMap.ext
  intro x
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rw [continuousInhomogeneousCochainsMap_f_apply, hom_id, ContIntertwiningMap.id_apply]

/-- Continuous inhomogeneous cochain maps respect composition of coefficient maps. -/
@[reassoc]
theorem continuousInhomogeneousCochainsMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    continuousInhomogeneousCochainsMap (hX := hX) (hY := hZ) (f ≫ g) =
      continuousInhomogeneousCochainsMap (hY := hY) f ≫ continuousInhomogeneousCochainsMap g := by
  ext n a : 3
  apply ContinuousMap.ext
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [continuousInhomogeneousCochainsMap_f_apply, continuousInhomogeneousCochainsMap_f_apply,
    continuousInhomogeneousCochainsMap_f_apply]
  exact TopRep.comp_apply f g (a x)

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
