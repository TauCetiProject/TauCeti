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

A cellular map intertwining two cellular actions along a monoid homomorphism `φ : G →* H` induces
a chain map from the source complex to the restriction of the target complex along `φ`
(`TauCeti.cellularActionComplexMap`), compatible with the forgetful identifications and with
identity and composition of cellular maps.

The maps act on the CW subsets themselves; no extension to their ambient spaces or compatibility
with chosen characteristic maps is required.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe u

section Complex

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

end Complex

section Map

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  (C : Set X) [CWComplex C] {G : Type u} [Monoid G]
  (ρ : G → (TopCat.of C ⟶ TopCat.of C)) (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  (C' : Set Y) [CWComplex C'] {H : Type u} [Monoid H]
  (ρ' : H → (TopCat.of C' ⟶ TopCat.of C')) (hcell' : ∀ h, IsCellular C' C' (ρ' h))
  (hone' : ρ' 1 = 𝟙 _) (hmul' : ∀ h₁ h₂, ρ' (h₁ * h₂) = ρ' h₂ ≫ ρ' h₁)

/-- A cellular map intertwining two cellular actions along `φ : G →* H` induces a morphism of
representations on cellular chains in each degree, with the target restricted along `φ`. -/
def cellularActionGroupMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    (R : Type u) [Ring R] (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation C' ρ' hcell' hone' hmul' R n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C C' hf (ModuleCat.of R R) n).hom
      isIntertwining' g := by
        have hcongr : ∀ {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'}
            (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂), f₁ = f₂ →
            cellularChainGroupMap C C' hf₁ (ModuleCat.of R R) n =
              cellularChainGroupMap C C' hf₂ (ModuleCat.of R R) n := by
          rintro _ _ _ _ rfl
          rfl
        have h₁ := cellularChainGroupMap_comp C C (hcell g) C' hf (ModuleCat.of R R) n
        have h₂ := cellularChainGroupMap_comp C C' hf C' (hcell' (φ g)) (ModuleCat.of R R) n
        have h₃ := hcongr (IsCellular.comp C C (hcell g) hf)
          (IsCellular.comp C C' hf (hcell' (φ g))) (hcomm g)
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply, cellularActionRepresentation_apply,
          ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom (h₁.symm.trans (h₃.trans h₂)) }

/-- Forgetting equivariance recovers the underlying cellular chain-group map. -/
@[simp]
theorem cellularActionGroupMap_hom_toLinearMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    (R : Type u) [Ring R] (n : ℕ) :
    (cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R n
      ).hom.toLinearMap =
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n).hom :=
  (rfl)

/-- Equal cellular maps induce equal morphisms of cellular chain representations. -/
theorem cellularActionGroupMap_congr (φ : G →* H) {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'}
    (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂)
    (hcomm₁ : ∀ g, ρ g ≫ f₁ = f₁ ≫ ρ' (φ g)) (hcomm₂ : ∀ g, ρ g ≫ f₂ = f₂ ≫ ρ' (φ g))
    (hf : f₁ = f₂) (R : Type u) [Ring R] (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₁ hcomm₁ R n =
      cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₂ hcomm₂ R n := by
  subst hf
  rfl

/-- The equivariant cellular chain-group maps commute with the equivariant cellular differentials.
-/
@[reassoc]
theorem cellularActionGroupMap_comp_cellularActionDifferential (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
    (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g)) (R : Type u) [Ring R] (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R (n + 1) ≫
        (Rep.resFunctor φ).map (cellularActionDifferential C' ρ' hcell' hone' hmul' R n) =
      cellularActionDifferential C ρ hcell hone hmul R n ≫
        cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, cellularActionGroupMap_hom_toLinearMap,
    cellularActionDifferential_hom_toLinearMap, ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom
      (cellularChainGroupMap_comp_cellularDifferential C C' hf (ModuleCat.of R R) n)

/-- **Equivariant cellular chain map along a monoid homomorphism.** A cellular map intertwining
two cellular actions along `φ : G →* H` induces a chain map from the source equivariant cellular
complex to the restriction of the target complex along `φ`. -/
def cellularActionComplexMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    (R : Type u) [Ring R] :
    cellularActionComplex C ρ hcell hone hmul R ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex C' ρ' hcell' hone' hmul' R) where
  f n :=
    eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
      cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R n ≫
      eqToHom (congrArg (Rep.resFunctor φ).obj
        (cellularActionComplex_X C' ρ' hcell' hone' hmul' R n).symm)
  comm' i j hij := by
    subst i
    have hX : ∀ m, cellularActionComplex_X C ρ hcell hone hmul R m = rfl :=
      fun _ ↦ Subsingleton.elim _ _
    have hX' : ∀ m, cellularActionComplex_X C' ρ' hcell' hone' hmul' R m = rfl :=
      fun _ ↦ Subsingleton.elim _ _
    simp only [cellularActionComplex_d, Functor.mapHomologicalComplex_obj_d]
    rw [hX (j + 1), hX j, hX' (j + 1), hX' j]
    unfold cellularActionComplex
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact cellularActionGroupMap_comp_cellularActionDifferential
      C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R j

/-- The degree-`n` component of `cellularActionComplexMap` is `cellularActionGroupMap`, up to the
canonical cellular-term transports. -/
@[simp]
theorem cellularActionComplexMap_f (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    (R : Type u) [Ring R] (n : ℕ) :
    (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R).f n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul R n) ≫
        cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R n ≫
        eqToHom (congrArg (Rep.resFunctor φ).obj
          (cellularActionComplex_X C' ρ' hcell' hone' hmul' R n).symm) :=
  (rfl)

/-- Equal cellular maps induce equal equivariant cellular chain maps. -/
theorem cellularActionComplexMap_congr (φ : G →* H) {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'}
    (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂)
    (hcomm₁ : ∀ g, ρ g ≫ f₁ = f₁ ≫ ρ' (φ g)) (hcomm₂ : ∀ g, ρ g ≫ f₂ = f₂ ≫ ρ' (φ g))
    (hf : f₁ = f₂) (R : Type u) [Ring R] :
    cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₁ hcomm₁ R =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₂ hcomm₂ R := by
  subst hf
  rfl

/-- Forgetting the actions identifies `cellularActionComplexMap` with the underlying cellular chain
map `cellularChainComplexMap`. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
    (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g)) (R : Type u) [Ring R] :
    cellularChainComplexMap C C' hf (ModuleCat.of R R) ≫
        (cellularActionComplexForget₂Iso C' ρ' hcell' hone' hmul' R).hom =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul R).hom ≫
        ((forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm R) ≫
        ((cellularActionComplex C' ρ' hcell' hone' hmul' R).repResForget₂Iso φ).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f, Category.comp_id,
    CategoryTheory.Functor.map_comp, eqToHom_map]
  simp only [Rep.forget₂_moduleCat_map, cellularActionGroupMap_hom_toLinearMap,
    ModuleCat.ofHom_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- The identity cellular map and identity monoid homomorphism induce the identity morphism of
cellular chain representations. -/
@[simp]
theorem cellularActionGroupMap_id
    (hcomm : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g))
    (R : Type u) [Ring R] (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul C ρ hcell hone hmul
      (MonoidHom.id G) (isCellular_id C) hcomm R n = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simp

/-- The identity cellular map and identity monoid homomorphism induce the identity equivariant
cellular chain map. -/
@[simp]
theorem cellularActionComplexMap_id
    (hcomm : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g))
    (R : Type u) [Ring R] :
    cellularActionComplexMap C ρ hcell hone hmul C ρ hcell hone hmul
      (MonoidHom.id G) (isCellular_id C) hcomm R = 𝟙 _ := by
  ext n : 1
  simp

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z]
  (C'' : Set Z) [CWComplex C''] {K : Type u} [Monoid K]
  (ρ'' : K → (TopCat.of C'' ⟶ TopCat.of C'')) (hcell'' : ∀ k, IsCellular C'' C'' (ρ'' k))
  (hone'' : ρ'' 1 = 𝟙 _) (hmul'' : ∀ k₁ k₂, ρ'' (k₁ * k₂) = ρ'' k₂ ≫ ρ'' k₁)

/-- Equivariant cellular chain-group maps respect composition of cellular maps and monoid
homomorphisms. -/
theorem cellularActionGroupMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g)
    (hcommf : ∀ x, ρ x ≫ f = f ≫ ρ' (φ x))
    (hcommg : ∀ y, ρ' y ≫ g = g ≫ ρ'' (ψ y))
    (hcommgf : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    (R : Type u) [Ring R] (n : ℕ) :
    cellularActionGroupMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
        (ψ.comp φ) (IsCellular.comp C C' hf hg) hcommgf R n =
      cellularActionGroupMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcommf R n ≫
        (Rep.resFunctor φ).map
          (cellularActionGroupMap C' ρ' hcell' hone' hmul' C'' ρ'' hcell'' hone'' hmul''
            ψ hg hcommg R n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, cellularActionGroupMap_hom_toLinearMap, ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom (cellularChainGroupMap_comp C C' hf C'' hg (ModuleCat.of R R) n)

/-- Equivariant cellular chain maps respect composition of cellular maps and monoid homomorphisms.
-/
theorem cellularActionComplexMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g)
    (hcommf : ∀ x, ρ x ≫ f = f ≫ ρ' (φ x))
    (hcommg : ∀ y, ρ' y ≫ g = g ≫ ρ'' (ψ y))
    (hcommgf : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    (R : Type u) [Ring R] :
    cellularActionComplexMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
        (ψ.comp φ) (IsCellular.comp C C' hf hg) hcommgf R =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcommf R ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap C' ρ' hcell' hone' hmul' C'' ρ'' hcell'' hone'' hmul''
            ψ hg hcommg R) := by
  ext n : 1
  have hX : ∀ m, cellularActionComplex_X C ρ hcell hone hmul R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  have hX' : ∀ m, cellularActionComplex_X C' ρ' hcell' hone' hmul' R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  have hX'' : ∀ m, cellularActionComplex_X C'' ρ'' hcell'' hone'' hmul'' R m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  simp only [cellularActionComplexMap_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  rw [hX n, hX' n, hX'' n]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact cellularActionGroupMap_comp C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
    C'' ρ'' hcell'' hone'' hmul'' ψ φ hf hg hcommf hcommg hcommgf R n

end Map

end TauCeti
