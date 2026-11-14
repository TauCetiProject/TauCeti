/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains. Naturality of the cellular differential assembles these into a complex in `Rep`.
The forgetful isomorphism identifies it with the original cellular chain complex. Naturality of the
cellular augmentation promotes it to a chain map into the trivial representation placed in degree
`0` (`TauCeti.cellularActionComplexAugmentation`), which is a quasi-isomorphism whenever the CW
complex is contractible (`TauCeti.quasiIso_cellularActionComplexAugmentation`).

The maps act on the CW subset itself; no extension to its ambient space or compatibility with
chosen characteristic maps is required.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {G : Type u} [Monoid G] (ρ : G → (TopCat.of C ⟶ TopCat.of C))
  (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  (R : Type u) [Ring R]

/-- The representation induced on cellular chains by a cellular action. -/
def cellularActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) where
  toFun g := (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom
  map_one' := by
    simp only [hone, cellularChainGroupMap_id, ModuleCat.hom_id]
    rfl
  map_mul' g h := by
    simpa only [hmul, ModuleCat.hom_comp, Module.End.mul_eq_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp C C (hcell h) C (hcell g) (ModuleCat.of R R) n)

/-- The action is induced by the given cellular self-map. -/
@[simp]
theorem cellularActionRepresentation_apply (n : ℕ) (g : G) :
    cellularActionRepresentation C ρ hcell hone hmul R n g =
      (cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n).hom := (rfl)

/-- The cellular differential as a morphism of representations. -/
def cellularActionDifferential (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R (n + 1)) ⟶
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) :=
  Rep.ofHom
    { toLinearMap := (cellularDifferential C (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        simpa only [cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom
            (cellularChainGroupMap_comp_cellularDifferential C C (hcell g)
              (ModuleCat.of R R) n) }

/-- The underlying linear map is the cellular differential. -/
@[simp]
theorem cellularActionDifferential_hom_toLinearMap (n : ℕ) :
    (cellularActionDifferential C ρ hcell hone hmul R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := (rfl)

/-- Cellular chains retaining a cellular monoid action. -/
def cellularActionComplex : ChainComplex (Rep R G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n))
    (cellularActionDifferential C ρ hcell hone hmul R) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom
        (cellularDifferential_comp_cellularDifferential C (ModuleCat.of R R) n) x

/-- The terms of the equivariant cellular complex. -/
@[simp]
theorem cellularActionComplex_X (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).X n =
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) := (rfl)

/-- Its differential is the equivariant cellular differential. -/
@[simp]
theorem cellularActionComplex_d (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul R).d (n + 1) n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R (n + 1)) ≫
        cellularActionDifferential C ρ hcell hone hmul R n ≫
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n).symm := by
  -- Proof irrelevance normalizes the reflexive transports without exposing the complex API.
  have h : ∀ m, cellularActionComplex_X C ρ hcell hone hmul R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

/-- Forgetting the action recovers the geometric cellular chain complex. -/
def cellularActionComplexForget₂Iso :
    cellularChainComplex C (ModuleCat.of R R) ≅
      ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).obj
        (cellularActionComplex C ρ hcell hone hmul R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
        cellularChainComplex_X]
      rfl))
    fun i j hij ↦ by
      subst i
      simp only [cellularChainComplex_d, Functor.mapHomologicalComplex_obj_d,
        cellularActionComplex_d, eqToIso.hom, Functor.map_comp, eqToHom_map,
        Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
      unfold cellularActionComplex
      simp only [eqToHom_refl, Category.comp_id,
        Rep.forget₂_moduleCat_map, cellularActionDifferential_hom_toLinearMap,
        ModuleCat.ofHom_hom]

/-- Components of the forgetful identification are the canonical cellular-term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_hom_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- Inverse components of the forgetful identification are the reverse term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_inv_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- The augmentation of cellular chains in degree `0`, as a morphism of representations to the
trivial representation: cellular maps preserve the augmentation. -/
def cellularActionAugmentation :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellularActionRepresentation_apply]
        exact ConcreteCategory.congr_hom
          (cellularChainGroupMap_comp_cellularAugmentation C C (hcell g) (ModuleCat.of R R)) x }

/-- The underlying linear map of `TauCeti.cellularActionAugmentation` is the cellular
augmentation. -/
@[simp]
theorem cellularActionAugmentation_hom_toLinearMap :
    (cellularActionAugmentation C ρ hcell hone hmul R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom := (rfl)

/-- The equivariant augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellularActionDifferential_comp_cellularActionAugmentation :
    cellularActionDifferential C ρ hcell hone hmul R 0 ≫
      cellularActionAugmentation C ρ hcell hone hmul R = 0 := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R))) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  simpa [Rep.hom_comp] using h

/-- The augmentation of the equivariant cellular chain complex, as a chain map to the trivial
representation placed in degree `0`. -/
def cellularActionComplexAugmentation :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      (ChainComplex.single₀ (Rep.{u} R G)).obj (Rep.trivial R G R) :=
  ((cellularActionComplex C ρ hcell hone hmul R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
      cellularActionAugmentation C ρ hcell hone hmul R, by
        simp [cellularActionComplex_d]⟩

/-- In degree `0`, `TauCeti.cellularActionComplexAugmentation` is
`TauCeti.cellularActionAugmentation`. -/
@[simp]
theorem cellularActionComplexAugmentation_f_zero :
    (cellularActionComplexAugmentation C ρ hcell hone hmul R).f 0 =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R 0) ≫
        cellularActionAugmentation C ρ hcell hone hmul R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **For a contractible CW complex, the equivariant cellular augmentation is a
quasi-isomorphism.** Forgetting the `G`-action recovers the geometric cellular chain complex
augmentation, which is a quasi-isomorphism on a contractible CW complex. -/
theorem quasiIso_cellularActionComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellularActionComplexAugmentation C ρ hcell hone hmul R) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _
      (cellularChainComplexAugmentation C (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation _ _
  · refine Arrow.isoMk' _ _ (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).symm
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    have h : (forget₂ (Rep R G) (ModuleCat R)).map
        (cellularActionAugmentation C ρ hcell hone hmul R) =
          cellularAugmentation C (ModuleCat.of R R) := by
      rw [Rep.forget₂_moduleCat_map, cellularActionAugmentation_hom_toLinearMap,
        ModuleCat.ofHom_hom]
    ext : 1
    simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end TauCeti
