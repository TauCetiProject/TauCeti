/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.RepresentationTheory.Rep.HomologicalComplex

/-!
# Cellular chains with a monoid action

A family of cellular self-maps satisfying the action laws induces representations on cellular
chains. Naturality of the cellular differential assembles these into a complex in `Rep`.
The forgetful isomorphism identifies it with the original cellular chain complex.

Along a monoid homomorphism `φ : G →* H`, a cellular map intertwining the two actions induces
morphisms of cellular chain representations to the restricted target representations, and these
assemble into a chain map `TauCeti.cellularActionComplexMap` respecting identities, composition,
and the forgetful isomorphism `TauCeti.cellularActionComplexForget₂Iso`.

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

section Map

variable {Y Z : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  (D : Set Y) [CWComplex D] (E : Set Z) [CWComplex E]
  {H K : Type u} [Monoid H] [Monoid K]
  (ρH : H → (TopCat.of D ⟶ TopCat.of D)) (hcellH : ∀ h, IsCellular D D (ρH h))
  (honeH : ρH 1 = 𝟙 _) (hmulH : ∀ h₁ h₂, ρH (h₁ * h₂) = ρH h₂ ≫ ρH h₁)
  (ρK : K → (TopCat.of E ⟶ TopCat.of E)) (hcellK : ∀ k, IsCellular E E (ρK k))
  (honeK : ρK 1 = 𝟙 _) (hmulK : ∀ k₁ k₂, ρK (k₁ * k₂) = ρK k₂ ≫ ρK k₁)

/-- A cellular map intertwining two cellular monoid actions along `φ : G →* H` induces a morphism
of cellular chain representations to the restricted target representation. -/
def cellularActionGroupMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation D ρH hcellH honeH hmulH R n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        have hcomp :
            cellularChainGroupMap C C (hcell g) (ModuleCat.of R R) n ≫
                cellularChainGroupMap C D hf (ModuleCat.of R R) n =
              cellularChainGroupMap C D hf (ModuleCat.of R R) n ≫
                cellularChainGroupMap D D (hcellH (φ g)) (ModuleCat.of R R) n := by
          rw [← cellularChainGroupMap_comp C C (hcell g) D hf,
            ← cellularChainGroupMap_comp C D hf D (hcellH (φ g))]
          have heq := hequiv g
          congr! 1
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply, Rep.of_ρ,
          cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom hcomp }

/-- The underlying linear map of `cellularActionGroupMap` is `cellularChainGroupMap`. -/
@[simp]
theorem cellularActionGroupMap_hom_toLinearMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D}
    (hf : IsCellular C D f) (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) (n : ℕ) :
    (cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv
      n).hom.toLinearMap = (cellularChainGroupMap C D hf (ModuleCat.of R R) n).hom :=
  (rfl)

/-- Equal equivariant cellular maps induce equal morphisms of cellular chain representations. -/
theorem cellularActionGroupMap_congr (φ : G →* H) {f f' : TopCat.of C ⟶ TopCat.of D}
    (h : f = f') (hf : IsCellular C D f) (hf' : IsCellular C D f')
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) (hequiv' : ∀ g, ρ g ≫ f' = f' ≫ ρH (φ g))
    (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv n =
      cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf' hequiv' n := by
  subst h
  rfl

/-- The identity cellular map induces the identity morphism of cellular chain representations. -/
@[simp]
theorem cellularActionGroupMap_id (hf : IsCellular C C (𝟙 (TopCat.of C)))
    (hequiv : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g))
    (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R C ρ hcell hone hmul (MonoidHom.id G) hf hequiv
        n =
      𝟙 (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  have h : hf = isCellular_id C := Subsingleton.elim _ _
  subst h
  simp

/-- Morphisms of cellular chain representations respect composition of equivariant cellular maps. -/
theorem cellularActionGroupMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} {g : TopCat.of D ⟶ TopCat.of E}
    (hf : IsCellular C D f) (hg : IsCellular D E g) (hfg : IsCellular C E (f ≫ g))
    (hequivf : ∀ x, ρ x ≫ f = f ≫ ρH (φ x))
    (hequivg : ∀ y, ρH y ≫ g = g ≫ ρK (ψ y))
    (hequivfg : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρK ((ψ.comp φ) x))
    (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul R E ρK hcellK honeK hmulK (ψ.comp φ) hfg hequivfg
        n =
      cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequivf n ≫
        (Rep.resFunctor φ).map
          (cellularActionGroupMap D ρH hcellH honeH hmulH R E ρK hcellK honeK hmulK ψ hg hequivg
            n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  have h : hfg = IsCellular.comp C D hf hg := Subsingleton.elim _ _
  subst h
  simpa only [cellularActionGroupMap_hom_toLinearMap, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
    ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom
      (cellularChainGroupMap_comp C D hf E hg (ModuleCat.of R R) n)

/-- A cellular map intertwining two cellular monoid actions along `φ : G →* H` induces a chain map
from the source equivariant cellular complex to the restricted target complex. -/
def cellularActionComplexMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex D ρH hcellH honeH hmulH R) where
  f n :=
    eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
      cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv n ≫
      (Rep.resFunctor φ).map (eqToHom (cellularActionComplex_X D ρH hcellH honeH hmulH R n).symm)
  comm' i j hij := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, cellularActionComplex_d, cellularActionComplex_d,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc ((Rep.resFunctor φ).map (eqToHom _)),
      ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.id_comp]
    refine congrArg (eqToHom (cellularActionComplex_X C ρ hcell hone hmul R (j + 1)) ≫ ·) ?_
    simp only [← Category.assoc]
    refine congrArg (· ≫ (Rep.resFunctor φ).map
      (eqToHom (cellularActionComplex_X D ρH hcellH honeH hmulH R j).symm)) ?_
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      Rep.resMap_hom_toLinearMap, cellularActionGroupMap_hom_toLinearMap,
      cellularActionDifferential_hom_toLinearMap, ModuleCat.hom_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp_cellularDifferential C D hf (ModuleCat.of R R) j)

/-- The degree-`n` component of `cellularActionComplexMap` is `cellularActionGroupMap`, transported
across `cellularActionComplex_X`. -/
@[simp]
theorem cellularActionComplexMap_f (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of D}
    (hf : IsCellular C D f) (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) (n : ℕ) :
    (cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv).f n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
        cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv n ≫
        (Rep.resFunctor φ).map
          (eqToHom (cellularActionComplex_X D ρH hcellH honeH hmulH R n).symm) :=
  (rfl)

/-- Equal equivariant cellular maps induce equal maps of equivariant cellular complexes. -/
theorem cellularActionComplexMap_congr (φ : G →* H) {f f' : TopCat.of C ⟶ TopCat.of D}
    (h : f = f') (hf : IsCellular C D f) (hf' : IsCellular C D f')
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) (hequiv' : ∀ g, ρ g ≫ f' = f' ≫ ρH (φ g)) :
    cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv =
      cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf' hequiv' := by
  subst h
  rfl

/-- The identity cellular map induces the identity chain map on `cellularActionComplex`. -/
@[simp]
theorem cellularActionComplexMap_id (hf : IsCellular C C (𝟙 (TopCat.of C)))
    (hequiv : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g)) :
    cellularActionComplexMap C ρ hcell hone hmul R C ρ hcell hone hmul (MonoidHom.id G) hf
        hequiv =
      𝟙 (cellularActionComplex C ρ hcell hone hmul R) := by
  ext n : 1
  simp only [cellularActionComplexMap_f, cellularActionGroupMap_id, Category.id_comp,
    HomologicalComplex.id_f]
  dsimp only [Rep.resFunctor]
  rw [Rep.resMap_id, eqToHom_trans, eqToHom_refl]

/-- Maps of equivariant cellular complexes respect composition of equivariant cellular maps. -/
theorem cellularActionComplexMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} {g : TopCat.of D ⟶ TopCat.of E}
    (hf : IsCellular C D f) (hg : IsCellular D E g) (hfg : IsCellular C E (f ≫ g))
    (hequivf : ∀ x, ρ x ≫ f = f ≫ ρH (φ x))
    (hequivg : ∀ y, ρH y ≫ g = g ≫ ρK (ψ y))
    (hequivfg : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρK ((ψ.comp φ) x)) :
    cellularActionComplexMap C ρ hcell hone hmul R E ρK hcellK honeK hmulK (ψ.comp φ) hfg
        hequivfg =
      cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequivf ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap D ρH hcellH honeH hmulH R E ρK hcellK honeK hmulK ψ hg
            hequivg) := by
  ext n : 1
  simp only [cellularActionComplexMap_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    cellularActionGroupMap_comp C ρ hcell hone hmul R D E ρH hcellH honeH hmulH
      ρK hcellK honeK hmulK ψ φ hf hg hfg hequivf hequivg hequivfg n,
    Category.assoc]
  congr 2

/-- Forgetting the action intertwines `cellularActionComplexMap` with `cellularChainComplexMap`. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) :
    cellularChainComplexMap C D hf (ModuleCat.of R R) ≫
        (cellularActionComplexForget₂Iso D ρH hcellH honeH hmulH R).hom =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom ≫
        ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv) ≫
        ((cellularActionComplex D ρH hcellH honeH hmulH R).repResForget₂Iso φ).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f, Category.comp_id,
    CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans]
  apply (cancel_epi (eqToHom (cellularChainComplex_X C (ModuleCat.of R R) n))).mpr
  have hg :
      (forget₂ (Rep R G) (ModuleCat R)).map
          (cellularActionGroupMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv n) =
        cellularChainGroupMap C D hf (ModuleCat.of R R) n := by
    rw [Rep.forget₂_moduleCat_map, cellularActionGroupMap_hom_toLinearMap, ModuleCat.ofHom_hom]
  have he :
      (forget₂ (Rep R G) (ModuleCat R)).map
          ((Rep.resFunctor φ).map
            (eqToHom (cellularActionComplex_X D ρH hcellH honeH hmulH R n).symm)) =
        eqToHom (by rw [cellularActionComplex_X]) :=
    eqToHom_map (Rep.resFunctor φ ⋙ forget₂ (Rep R G) (ModuleCat R))
      (cellularActionComplex_X D ρH hcellH honeH hmulH R n).symm
  rw [hg, he]

/-- Inverse form of `cellularActionComplexForget₂Iso_hom_naturality`. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_inv_naturality (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of D} (hf : IsCellular C D f)
    (hequiv : ∀ g, ρ g ≫ f = f ≫ ρH (φ g)) :
    ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
        (cellularActionComplexMap C ρ hcell hone hmul R D ρH hcellH honeH hmulH φ hf hequiv) ≫
      ((cellularActionComplex D ρH hcellH honeH hmulH R).repResForget₂Iso φ).hom ≫
      (cellularActionComplexForget₂Iso D ρH hcellH honeH hmulH R).inv =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).inv ≫
        cellularChainComplexMap C D hf (ModuleCat.of R R) := by
  simp only [← Category.assoc]
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    cellularActionComplexForget₂Iso_hom_naturality C ρ hcell hone hmul R D ρH hcellH honeH hmulH
      φ hf hequiv]

end Map

end TauCeti
