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

The maps act on the relative CW subsets themselves; no extension to their ambient spaces or
compatibility with chosen characteristic maps is required.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

universe w r v₁ v₂ v₃

section Complex

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {G : Type v₁} [Monoid G] (ρ : G → (TopCat.of C ⟶ TopCat.of C))
  (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  {R : Type r} [Ring R] (M : ModuleCat.{w} R)

/-- The representation induced on cellular chains by a cellular action. -/
def cellularActionRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C M n : ModuleCat.{w} R) where
  toFun g := (cellularChainGroupMap C C (hcell g) M n).hom
  map_one' := by
    simp only [hone, cellularChainGroupMap_id, ModuleCat.hom_id]
    rfl
  map_mul' g h := by
    simpa only [hmul, ModuleCat.hom_comp, Module.End.mul_eq_comp] using
      congrArg ModuleCat.Hom.hom
        (cellularChainGroupMap_comp C C (hcell h) C (hcell g) M n)

/-- The action is induced by the given cellular self-map. -/
@[simp]
theorem cellularActionRepresentation_apply (n : ℕ) (g : G) :
    cellularActionRepresentation C ρ hcell hone hmul M n g =
      (cellularChainGroupMap C C (hcell g) M n).hom := (rfl)

/-- The cellular differential as a morphism of representations. -/
def cellularActionDifferential (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul M (n + 1)) ⟶
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul M n) :=
  Rep.ofHom
    { toLinearMap := (cellularDifferential C M n).hom
      isIntertwining' g := by
        simpa only [cellularActionRepresentation_apply, ModuleCat.hom_comp] using
          congrArg ModuleCat.Hom.hom
            (cellularChainGroupMap_comp_cellularDifferential C C (hcell g) M n) }

/-- The underlying linear map is the cellular differential. -/
@[simp]
theorem cellularActionDifferential_hom_toLinearMap (n : ℕ) :
    (cellularActionDifferential C ρ hcell hone hmul M n).hom.toLinearMap =
      (cellularDifferential C M n).hom := (rfl)

/-- Cellular chains retaining a cellular monoid action. -/
def cellularActionComplex : ChainComplex (Rep.{w} R G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (cellularActionRepresentation C ρ hcell hone hmul M n))
    (cellularActionDifferential C ρ hcell hone hmul M) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom
        (cellularDifferential_comp_cellularDifferential C M n) x

/-- The terms of the equivariant cellular complex. -/
@[simp]
theorem cellularActionComplex_X (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul M).X n =
      Rep.of (cellularActionRepresentation C ρ hcell hone hmul M n) := (rfl)

/-- Its differential is the equivariant cellular differential. -/
@[simp]
theorem cellularActionComplex_d (n : ℕ) :
    (cellularActionComplex C ρ hcell hone hmul M).d (n + 1) n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul M (n + 1)) ≫
        cellularActionDifferential C ρ hcell hone hmul M n ≫
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul M n).symm := by
  -- Proof irrelevance normalizes the reflexive transports without exposing the complex API.
  have h : ∀ m, cellularActionComplex_X C ρ hcell hone hmul M m = rfl :=
    fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularActionComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

/-- Forgetting the action recovers the geometric cellular chain complex. -/
def cellularActionComplexForget₂Iso :
    cellularChainComplex C M ≅
      ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellularActionComplex C ρ hcell hone hmul M) :=
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
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul M).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

/-- Inverse components of the forgetful identification are the reverse term transports. -/
@[simp]
theorem cellularActionComplexForget₂Iso_inv_f (n : ℕ) :
    (cellularActionComplexForget₂Iso C ρ hcell hone hmul M).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X,
          cellularChainComplex_X]
        rfl) := (rfl)

end Complex

section Map

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} (C : Set X) [RelCWComplex C D] {G : Type v₁} [Monoid G]
  (ρ : G → (TopCat.of C ⟶ TopCat.of C)) (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  {E : Set Y} (C' : Set Y) [RelCWComplex C' E] {H : Type v₂} [Monoid H]
  (ρ' : H → (TopCat.of C' ⟶ TopCat.of C')) (hcell' : ∀ h, IsCellular C' C' (ρ' h))
  (hone' : ρ' 1 = 𝟙 _) (hmul' : ∀ h₁ h₂, ρ' (h₁ * h₂) = ρ' h₂ ≫ ρ' h₁)

/-- A cellular map intertwining two cellular actions along `φ : G →* H` induces a morphism of
representations on cellular chains in each degree, with the target restricted along `φ`. -/
def cellularActionRepMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    Rep.of (cellularActionRepresentation C ρ hcell hone hmul M n) ⟶
      Rep.res φ (Rep.of (cellularActionRepresentation C' ρ' hcell' hone' hmul' M n)) :=
  Rep.ofHom
    { toLinearMap := (cellularChainGroupMap C C' hf M n).hom
      isIntertwining' g := by
        have h₁ := cellularChainGroupMap_comp C C (hcell g) C' hf M n
        have h₂ := cellularChainGroupMap_comp C C' hf C' (hcell' (φ g)) M n
        have h₃ := cellularChainGroupMap_congr C C' (IsCellular.comp C C (hcell g) hf)
          (IsCellular.comp C C' hf (hcell' (φ g))) (hcomm g) M n
        simpa only [Rep.res_obj_ρ, MonoidHom.comp_apply, cellularActionRepresentation_apply,
          ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom (h₁.symm.trans (h₃.trans h₂)) }

/-- Forgetting equivariance recovers the underlying cellular chain-group map. -/
@[simp]
theorem cellularActionRepMap_hom_toLinearMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    (cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M n
      ).hom.toLinearMap =
      (cellularChainGroupMap C C' hf M n).hom :=
  (rfl)

/-- Equal cellular maps induce equal morphisms of cellular chain representations. -/
theorem cellularActionRepMap_congr (φ : G →* H) {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'}
    (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂)
    (hcomm₁ : ∀ g, ρ g ≫ f₁ = f₁ ≫ ρ' (φ g)) (hcomm₂ : ∀ g, ρ g ≫ f₂ = f₂ ≫ ρ' (φ g))
    (hf : f₁ = f₂) {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₁ hcomm₁ M n =
      cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₂ hcomm₂ M n := by
  subst hf
  rfl

/-- The equivariant cellular chain-group maps commute with the equivariant cellular differentials.
-/
@[reassoc]
theorem cellularActionRepMap_comp_cellularActionDifferential (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
    (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g)) {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M (n + 1) ≫
        (Rep.resFunctor φ).map (cellularActionDifferential C' ρ' hcell' hone' hmul' M n) =
      cellularActionDifferential C ρ hcell hone hmul M n ≫
        cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, cellularActionRepMap_hom_toLinearMap,
    cellularActionDifferential_hom_toLinearMap, ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom
      (cellularChainGroupMap_comp_cellularDifferential C C' hf M n)

/-- **Equivariant cellular chain map along a monoid homomorphism.** A cellular map intertwining
two cellular actions along `φ : G →* H` induces a chain map from the source equivariant cellular
complex to the restriction of the target complex along `φ`. -/
def cellularActionComplexMap (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) :
    cellularActionComplex C ρ hcell hone hmul M ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj
        (cellularActionComplex C' ρ' hcell' hone' hmul' M) where
  f n :=
    eqToHom (cellularActionComplex_X C ρ hcell hone hmul M n) ≫
      cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M n ≫
      eqToHom (congrArg (Rep.resFunctor φ).obj
        (cellularActionComplex_X C' ρ' hcell' hone' hmul' M n).symm)
  comm' i j hij := by
    subst i
    -- `-proj` keeps the `abbrev` `(Rep.resFunctor φ).map` unreduced so `Functor.map_comp` and
    -- `eqToHom_map` apply before reducing to `Rep.resMap`.
    simp -proj [eqToHom_map,
      cellularActionRepMap_comp_cellularActionDifferential_assoc C ρ hcell hone hmul
        C' ρ' hcell' hone' hmul' φ hf hcomm M j]

/-- The degree-`n` component of `cellularActionComplexMap` is `cellularActionRepMap`, up to the
canonical cellular-term transports. -/
@[simp]
theorem cellularActionComplexMap_f (φ : G →* H) {f : TopCat.of C ⟶ TopCat.of C'}
    (hf : IsCellular C C' f) (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M).f n =
      eqToHom (cellularActionComplex_X C ρ hcell hone hmul M n) ≫
        cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M n ≫
        eqToHom (congrArg (Rep.resFunctor φ).obj
          (cellularActionComplex_X C' ρ' hcell' hone' hmul' M n).symm) :=
  (rfl)

/-- Equal cellular maps induce equal equivariant cellular chain maps. -/
theorem cellularActionComplexMap_congr (φ : G →* H) {f₁ f₂ : TopCat.of C ⟶ TopCat.of C'}
    (hf₁ : IsCellular C C' f₁) (hf₂ : IsCellular C C' f₂)
    (hcomm₁ : ∀ g, ρ g ≫ f₁ = f₁ ≫ ρ' (φ g)) (hcomm₂ : ∀ g, ρ g ≫ f₂ = f₂ ≫ ρ' (φ g))
    (hf : f₁ = f₂) {R : Type r} [Ring R] (M : ModuleCat.{w} R) :
    cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₁ hcomm₁ M =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf₂ hcomm₂ M := by
  subst hf
  rfl

/-- Forgetting the actions identifies `cellularActionComplexMap` with the underlying cellular chain
map `cellularChainComplexMap`. -/
@[reassoc]
theorem cellularActionComplexForget₂Iso_hom_naturality (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
    (hcomm : ∀ g, ρ g ≫ f = f ≫ ρ' (φ g)) {R : Type r} [Ring R] (M : ModuleCat.{w} R) :
    cellularChainComplexMap C C' hf M ≫
        (cellularActionComplexForget₂Iso C' ρ' hcell' hone' hmul' M).hom =
      (cellularActionComplexForget₂Iso C ρ hcell hone hmul M).hom ≫
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).map
          (cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcomm M) ≫
        ((cellularActionComplex C' ρ' hcell' hone' hmul' M).repResForget₂Iso φ).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularActionComplexForget₂Iso_hom_f, Functor.mapHomologicalComplex_map_f,
    cellularActionComplexMap_f, HomologicalComplex.repResForget₂Iso_hom_f, Category.comp_id,
    CategoryTheory.Functor.map_comp, eqToHom_map]
  simp only [Rep.forget₂_moduleCat_map, cellularActionRepMap_hom_toLinearMap,
    ModuleCat.ofHom_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- The identity cellular map and identity monoid homomorphism induce the identity morphism of
cellular chain representations. -/
@[simp]
theorem cellularActionRepMap_id
    (hcomm : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    cellularActionRepMap C ρ hcell hone hmul C ρ hcell hone hmul
      (MonoidHom.id G) (isCellular_id C) hcomm M n = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simp

/-- The identity cellular map and identity monoid homomorphism induce the identity equivariant
cellular chain map. -/
@[simp]
theorem cellularActionComplexMap_id
    (hcomm : ∀ g, ρ g ≫ 𝟙 (TopCat.of C) = 𝟙 (TopCat.of C) ≫ ρ ((MonoidHom.id G) g))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) :
    cellularActionComplexMap C ρ hcell hone hmul C ρ hcell hone hmul
      (MonoidHom.id G) (isCellular_id C) hcomm M = 𝟙 _ := by
  ext n : 1
  simp

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z]
  {F : Set Z} (C'' : Set Z) [RelCWComplex C'' F] {K : Type v₃} [Monoid K]
  (ρ'' : K → (TopCat.of C'' ⟶ TopCat.of C'')) (hcell'' : ∀ k, IsCellular C'' C'' (ρ'' k))
  (hone'' : ρ'' 1 = 𝟙 _) (hmul'' : ∀ k₁ k₂, ρ'' (k₁ * k₂) = ρ'' k₂ ≫ ρ'' k₁)

/-- Equivariant cellular chain-group maps respect composition of cellular maps and monoid
homomorphisms. -/
theorem cellularActionRepMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g)
    (hcommf : ∀ x, ρ x ≫ f = f ≫ ρ' (φ x))
    (hcommg : ∀ y, ρ' y ≫ g = g ≫ ρ'' (ψ y))
    (hcommgf : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) (n : ℕ) :
    cellularActionRepMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
        (ψ.comp φ) (IsCellular.comp C C' hf hg) hcommgf M n =
      cellularActionRepMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcommf M n ≫
        (Rep.resFunctor φ).map
          (cellularActionRepMap C' ρ' hcell' hone' hmul' C'' ρ'' hcell'' hone'' hmul''
            ψ hg hcommg M n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  simpa only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, cellularActionRepMap_hom_toLinearMap, ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom (cellularChainGroupMap_comp C C' hf C'' hg M n)

/-- Equivariant cellular chain maps respect composition of cellular maps and monoid homomorphisms.
-/
theorem cellularActionComplexMap_comp (ψ : H →* K) (φ : G →* H)
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g)
    (hcommf : ∀ x, ρ x ≫ f = f ≫ ρ' (φ x))
    (hcommg : ∀ y, ρ' y ≫ g = g ≫ ρ'' (ψ y))
    (hcommgf : ∀ x, ρ x ≫ (f ≫ g) = (f ≫ g) ≫ ρ'' ((ψ.comp φ) x))
    {R : Type r} [Ring R] (M : ModuleCat.{w} R) :
    cellularActionComplexMap C ρ hcell hone hmul C'' ρ'' hcell'' hone'' hmul''
        (ψ.comp φ) (IsCellular.comp C C' hf hg) hcommgf M =
      cellularActionComplexMap C ρ hcell hone hmul C' ρ' hcell' hone' hmul' φ hf hcommf M ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (cellularActionComplexMap C' ρ' hcell' hone' hmul' C'' ρ'' hcell'' hone'' hmul''
            ψ hg hcommg M) := by
  ext n : 1
  -- `-proj` keeps `(Rep.resFunctor _).map` unreduced so `Functor.map_comp` and `eqToHom_map`
  -- fire; `Rep.resFunctor` is an `abbrev`, so restriction along `ψ.comp φ` agrees with sequential
  -- restriction along `ψ` then `φ` on objects.
  simp -proj [eqToHom_map,
    cellularActionRepMap_comp C ρ hcell hone hmul C' ρ' hcell' hone' hmul'
      C'' ρ'' hcell'' hone'' hmul'' ψ φ hf hg hcommf hcommg hcommgf M n]

end Map

end TauCeti
