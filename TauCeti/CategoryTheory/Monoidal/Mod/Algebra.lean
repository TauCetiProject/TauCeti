/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mod.Symmetric
public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Commutative monoids under a commutative monoid as monoids of modules, and their modules

Let `A` be a commutative monoid object of a braided monoidal category `C`, and `f : A ⟶ B` a
morphism of monoids into a commutative monoid `B`. Restricting the regular `B`-module along `f`
makes `B` an `A`-module (`Mod.comapRegular f`), acting by `f ▷ B ≫ μ`. Its multiplication
`μ : B ⊗ B ⟶ B` identifies the two actions of `A` on `B ⊗ B`, so it descends to the balanced
tensor product `B ⊗_A B`. With unit `f : A ⟶ B` this makes `B` a monoid object of `Mod C A`
(`Mod.monObjComapRegular`), which is commutative when `C` is symmetric
(`Mod.isCommMonObjComapRegular`). On representatives the multiplication is that of `B`
(`Mod.tensorπ_comapRegular_mul_hom`), and the unit is `f` (`Mod.comapRegular_one_hom`). A morphism
of monoids `φ : B ⟶ B'` under `A` becomes a morphism of monoid objects `comapRegular f ⟶
comapRegular f'` in `Mod C A` (`Mod.comapRegularMap`, `Mod.isMonHom_comapRegularMap`).

Modules over `comapRegular f` in `Mod C A` are the same thing as `B`-modules in `C`
(`Mod.comapRegularModEquivalence`):

* For a `B`-module `M`, the action `γ[B, M.X] : B ⊗ M.X ⟶ M.X` equalizes the two actions of `A` on
  `B ⊗ M.X` and descends to `(comapRegular f) ⊗_A (comap f).obj M ⟶ (comap f).obj M`, upgrading
  restriction of scalars along `f` to `Mod.comapRegularMod f : Mod C B ⥤ Mod (Mod C A)
  (comapRegular f)`.
* Conversely, precomposing the action of `comapRegular f` on `N : Mod (Mod C A) (comapRegular f)`
  with the quotient map `B ⊗ N.X.X ⟶ (comapRegular f ⊗_A N.X).X` defines a `B`-module structure on
  `N.X.X` (`Mod.ofComapRegularMod f`) whose restriction along `f` recovers `N.X`.

The unit and counit of the equivalence are identities on the underlying objects in `C`. The regular
`B`-module corresponds to the regular `comapRegular f`-module (`Mod.comapRegularModRegularIso`),
and restriction of scalars along a morphism of monoids under `A` corresponds to restriction along
`comapRegularMap` (`Mod.comapRegularModComapIso`). For symmetric spectra, `A` is the sphere: this
makes commutative monoids under `S` into commutative ring spectra and identifies modules over the
underlying monoid of symmetric sequences with module spectra over the ring spectrum.

## Main definitions

* `Mod.comapRegular f`: a monoid `B` under `A` as an `A`-module, and `Mod.comapRegularMap`:
  morphisms of monoids under `A` as `A`-module morphisms.
* `Mod.monObjComapRegular`, `Mod.isCommMonObjComapRegular`: the monoid and commutative monoid
  structures on `comapRegular f` in `Mod C A`, and `Mod.isMonHom_comapRegularMap`.
* `Mod.comapRegularMod f` and `Mod.ofComapRegularMod f`: the functors upgrading `B`-modules in `C`
  to `comapRegular f`-modules in `Mod C A` and descending them back.
* `Mod.comapRegularModEquivalence f`: the equivalence `Mod C B ≌ Mod (Mod C A) (comapRegular f)`.
* `Mod.comapRegularModRegularIso f` and `Mod.comapRegularModComapIso`: compatibility of
  `comapRegularMod` with regular modules and scalar restriction along monoid morphisms under `A`.

## Main statements

* `Mod.tensorπ_comapRegular_mul_hom`, `Mod.comapRegular_one_hom`: multiplication and unit of
  `comapRegular f` on representatives.
* `Mod.tensorπ_comapRegularMod_obj_smul_hom`, `Mod.whiskerRight_tensorπ_smul_hom`: characterization
  of the `comapRegular f`-action on representatives and recovery of the `A`-action along `f`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalLeftAction MonObj BraidedCategory Limits

namespace Mod

section comapRegular

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A B : C} [MonObj A] [MonObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- The monoid `B` as an `A`-module through `f : A ⟶ B`: the restriction along `f` of the regular
`B`-module. -/
-- Written as a structure with an explicit underlying object, exposed and implicitly reducible, so
-- that its underlying object is `B` and morphisms of `B` may be used as morphisms of this module.
@[expose, implicit_reducible]
def comapRegular : Mod C A :=
  letI := ModObj.regular B
  letI := scalarRestriction f B
  ⟨B⟩

/-- `comapRegular f` is the restriction along `f` of the regular `B`-module. -/
lemma comapRegular_eq : comapRegular f = (comap f).obj (regular B) :=
  (rfl)

@[simp]
lemma comapRegular_X : (comapRegular f).X = B :=
  (rfl)

/-- `A` acts on `B` through `f`, followed by the multiplication of `B`. -/
lemma comapRegular_smul : γ[A, (comapRegular f).X] = f ▷ B ≫ μ :=
  (rfl)

/-- A morphism of monoids `φ : B ⟶ B'` under `A` (`f ≫ φ = f'`) is a morphism of the corresponding
`A`-modules `comapRegular f ⟶ comapRegular f'`. -/
def comapRegularMap {B' : C} [MonObj B'] (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ]
    (w : f ≫ φ = f' := by cat_disch) : comapRegular f ⟶ comapRegular f' :=
  Hom.mk' φ (by
    change (f ▷ B ≫ μ) ≫ φ = A ◁ φ ≫ f' ▷ B' ≫ μ
    rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def_assoc, ← comp_whiskerRight_assoc, w,
      ← tensorHom_def_assoc, ← tensorHom_def'_assoc])

@[simp]
lemma comapRegularMap_hom {B' : C} [MonObj B'] (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B')
    [IsMonHom φ] (w : f ≫ φ = f') : (comapRegularMap f f' φ w).hom = φ :=
  (rfl)

@[simp]
lemma comapRegularMap_id : comapRegularMap f f (𝟙 B) (Category.comp_id f) = 𝟙 (comapRegular f) :=
  hom_ext _ _ rfl

@[reassoc]
lemma comapRegularMap_comp {B' B'' : C} [MonObj B'] [MonObj B''] (f' : A ⟶ B') (f'' : A ⟶ B'')
    [IsMonHom f'] [IsMonHom f''] (φ : B ⟶ B') (ψ : B' ⟶ B'') [IsMonHom φ] [IsMonHom ψ]
    (w₁ : f ≫ φ = f') (w₂ : f' ≫ ψ = f'') :
    comapRegularMap f f'' (φ ≫ ψ) (by rw [← Category.assoc, w₁, w₂]) =
      comapRegularMap f f' φ w₁ ≫ comapRegularMap f' f'' ψ w₂ :=
  hom_ext _ _ rfl

end comapRegular

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A] {B : C} [MonObj B] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [IsCommMonObj A] in
/- The multiplication of `B` identifies the two actions of `A` on `B ⊗ B`. -/
private lemma mul_tensorπ_condition :
    ((β_ A (comapRegular f).X).inv ≫ γ[A, (comapRegular f).X]) ▷ (comapRegular f).X ≫
        (μ : B ⊗ B ⟶ B) =
      (α_ (comapRegular f).X A (comapRegular f).X).hom ≫
        (comapRegular f).X ◁ γ[A, (comapRegular f).X] ≫ (μ : B ⊗ B ⟶ B) := by
  -- The action on `comapRegular f` is `f ▷ B ≫ μ` only after unfolding, so the statement is
  -- restated in `C` before rewriting.
  change ((β_ A B).inv ≫ f ▷ B ≫ μ) ▷ B ≫ μ = (α_ B A B).hom ≫ B ◁ (f ▷ B ≫ μ) ≫ μ
  rw [braiding_inv_whiskerRight_mul, whiskerLeft_comp_assoc, mul_assoc_flip,
    associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc, comp_whiskerRight_assoc]

/-- The multiplication of `B`, descended to the balanced tensor product `B ⊗_A B`. -/
noncomputable def comapRegularMul : comapRegular f ⊗ comapRegular f ⟶ comapRegular f :=
  Hom.mk' (tensorDesc (μ : B ⊗ B ⟶ B) (mul_tensorπ_condition f)) (by
    rw [← cancel_epi (A ◁ tensorπ _ _), whiskerLeft_tensorπ_smul_assoc, tensorπ_tensorDesc,
      selfLeftAction_actionHomRight, whiskerLeft_tensorπ_tensorDesc_assoc]
    -- Rewriting with `comapRegular_smul` leaves `(comapRegular f).X` in the associators and
    -- whiskerings, where the naturality lemmas need `B` syntactically, and `comapRegular_X`
    -- cannot be rewritten there (the motive is not type correct). So the goal is restated in `C`.
    change (α_ A B B).inv ≫ (f ▷ B ≫ μ) ▷ B ≫ μ = A ◁ μ ≫ f ▷ B ≫ μ
    rw [comp_whiskerRight_assoc, MonObj.mul_assoc, ← associator_inv_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc])

/-- A commutative monoid `B` under a commutative monoid `A` is a monoid object of `A`-modules, with
multiplication that of `B` on representatives and unit `f : A ⟶ B`. -/
noncomputable instance monObjComapRegular : MonObj (comapRegular f) where
  one := Hom.mk' (M := 𝟙_ (Mod C A)) f (by
    rw [comapRegular_smul]
    exact (IsMonHom.mul_hom f).trans (by rw [tensorHom_def', Category.assoc]; rfl))
  mul := comapRegularMul f
  one_mul := by
    ext
    simp only [comapRegularMul, comp_hom', tensorπ_whiskerRight_hom_assoc, Hom.mk'_hom,
      tensorπ_tensorDesc, tensorπ_leftUnitor_hom_hom]
    rfl
  mul_one := by
    ext
    simp only [comapRegularMul, comp_hom', tensorπ_whiskerLeft_hom_assoc, Hom.mk'_hom,
      tensorπ_tensorDesc, tensorπ_rightUnitor_hom_hom]
    exact (braiding_inv_whiskerRight_mul f).symm
  mul_assoc := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _ ▷ _ ≫ tensorπ _ _)]
    simp [comapRegularMul, tensorπ_associator_hom_hom_assoc, MonObj.mul_assoc]

/-- On representatives, the multiplication `B ⊗_A B ⟶ B` is the multiplication of `B`. -/
@[reassoc (attr := simp)]
lemma tensorπ_comapRegular_mul_hom :
    tensorπ _ _ ≫ (μ : comapRegular f ⊗ comapRegular f ⟶ _).hom = (μ : B ⊗ B ⟶ B) :=
  tensorπ_tensorDesc _ _

/-- The unit of `B` as a monoid of `A`-modules is `f : A ⟶ B`. -/
@[simp]
lemma comapRegular_one_hom : (η : 𝟙_ (Mod C A) ⟶ comapRegular f).hom = f :=
  (rfl)

/-- A morphism of commutative monoids `φ : B ⟶ B'` under `A` induces a morphism of monoid objects
`comapRegular f ⟶ comapRegular f'` in `Mod C A`. -/
instance isMonHom_comapRegularMap {B' : C} [MonObj B'] [IsCommMonObj B'] (f' : A ⟶ B')
    [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') :
    IsMonHom (comapRegularMap f f' φ w) where
  one_hom := hom_ext _ _ w
  mul_hom := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _)]
    simp [IsMonHom.mul_hom φ]

section Module

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [IsCommMonObj A] in
/- The action of `B` on a `B`-module `M` identifies the two actions of `A` on `B ⊗ M.X`. -/
private lemma smul_tensorπ_condition (M : Mod C B) :
    ((β_ A (comapRegular f).X).inv ≫ γ[A, (comapRegular f).X]) ▷ ((comap f).obj M).X ≫
        γ[B, M.X] =
      (α_ (comapRegular f).X A ((comap f).obj M).X).hom ≫
        (comapRegular f).X ◁ γ[A, ((comap f).obj M).X] ≫ γ[B, M.X] := by
  -- Unfold the carriers and restricted actions to morphisms in `C` before applying naturality of
  -- the associator.
  change ((β_ A B).inv ≫ f ▷ B ≫ μ) ▷ M.X ≫ γ[B, M.X] =
    (α_ B A M.X).hom ≫ B ◁ (f ▷ M.X ≫ γ[B, M.X]) ≫ γ[B, M.X]
  rw [braiding_inv_whiskerRight_mul, whiskerLeft_comp_assoc, ModObj.mul_smul_self_flip,
    associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc, comp_whiskerRight_assoc]

/-- The action of `B` on `M : Mod C B`, descended to the balanced tensor product
`comapRegular f ⊗_A (comap f).obj M`. -/
noncomputable def comapRegularSmul (M : Mod C B) :
    comapRegular f ⊗ (comap f).obj M ⟶ (comap f).obj M := by
  let d : (comapRegular f ⊗ (comap f).obj M).X ⟶ ((comap f).obj M).X :=
    tensorDesc γ[B, M.X] (smul_tensorπ_condition f M)
  have hd : tensorπ (comapRegular f) ((comap f).obj M) ≫ d = γ[B, M.X] :=
    tensorπ_tensorDesc _ _
  refine Hom.mk' d ?_
  rw [← cancel_epi (A ◁ tensorπ _ _), whiskerLeft_tensorπ_smul_assoc,
    selfLeftAction_actionHomRight, ← whiskerLeft_comp_assoc, hd]
  -- Restate in `C` so that associator naturality applies to `A`, `B`, and `M.X`.
  change (α_ A B M.X).inv ≫ (f ▷ B ≫ μ) ▷ M.X ≫ γ[B, M.X] =
    A ◁ γ[B, M.X] ≫ f ▷ M.X ≫ γ[B, M.X]
  rw [comp_whiskerRight_assoc, ModObj.mul_smul_self, ← associator_inv_naturality_left_assoc,
    Iso.inv_hom_id_assoc, whisker_exchange_assoc]
  rfl

@[reassoc (attr := simp)]
lemma tensorπ_comapRegularSmul_hom (M : Mod C B) :
    tensorπ (comapRegular f) ((comap f).obj M) ≫ (comapRegularSmul f M).hom = γ[B, M.X] :=
  tensorπ_tensorDesc _ _

/-- Restricting a `B`-module `M` along `f : A ⟶ B` equips `(comap f).obj M` with an action of the
monoid `comapRegular f` in `Mod C A`. -/
@[instance_reducible]
noncomputable def comapRegularModObj (M : Mod C B) : ModObj (comapRegular f) ((comap f).obj M) where
  smul := comapRegularSmul f M
  one_smul := by
    change (η : 𝟙_ (Mod C A) ⟶ comapRegular f) ▷ (comap f).obj M ≫ comapRegularSmul f M =
      (λ_ ((comap f).obj M)).hom
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _), comp_hom', tensorπ_whiskerRight_hom_assoc,
      comapRegular_one_hom, tensorπ_comapRegularSmul_hom, tensorπ_leftUnitor_hom_hom]
    rfl
  mul_smul := by
    change (μ : comapRegular f ⊗ comapRegular f ⟶ comapRegular f) ▷ (comap f).obj M ≫
        comapRegularSmul f M =
      (α_ (comapRegular f) (comapRegular f) ((comap f).obj M)).hom ≫
        comapRegular f ◁ comapRegularSmul f M ≫ comapRegularSmul f M
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _ ▷ _ ≫ tensorπ _ _)]
    have hL : (tensorπ (comapRegular f) (comapRegular f) ▷ ((comap f).obj M).X ≫
        tensorπ (comapRegular f ⊗ comapRegular f) ((comap f).obj M)) ≫
          ((μ : comapRegular f ⊗ comapRegular f ⟶ comapRegular f) ▷ (comap f).obj M ≫
            comapRegularSmul f M).hom =
        (μ : B ⊗ B ⟶ B) ▷ M.X ≫ γ[B, M.X] := by
      rw [comp_hom', Category.assoc, tensorπ_whiskerRight_hom_assoc, ← comp_whiskerRight_assoc,
        tensorπ_comapRegular_mul_hom, tensorπ_comapRegularSmul_hom]
      rfl
    have hR : (tensorπ (comapRegular f) (comapRegular f) ▷ ((comap f).obj M).X ≫
        tensorπ (comapRegular f ⊗ comapRegular f) ((comap f).obj M)) ≫
          ((α_ (comapRegular f) (comapRegular f) ((comap f).obj M)).hom ≫
            comapRegular f ◁ comapRegularSmul f M ≫ comapRegularSmul f M).hom =
        (α_ B B M.X).hom ≫ B ◁ γ[B, M.X] ≫ γ[B, M.X] := by
      rw [comp_hom', comp_hom', Category.assoc, tensorπ_associator_hom_hom_assoc,
        tensorπ_whiskerLeft_hom_assoc, ← whiskerLeft_comp_assoc, tensorπ_comapRegularSmul_hom]
      rfl
    exact hL.trans ((ModObj.mul_smul_self B M.X).trans hR.symm)

/-- A morphism `g : M ⟶ N` of `B`-modules becomes a morphism of `comapRegular f`-modules in
`Mod C A` after restricting scalars along `f`. -/
lemma isModHom_comapRegular_comap_map {M N : Mod C B} (g : M ⟶ N) :
    letI := comapRegularModObj f M
    letI := comapRegularModObj f N
    IsModHom (comapRegular f) ((comap f).map g) := by
  let := comapRegularModObj f M
  let := comapRegularModObj f N
  refine ⟨hom_ext _ _ ?_⟩
  rw [← cancel_epi (tensorπ _ _)]
  change tensorπ (comapRegular f) ((comap f).obj M) ≫
      (comapRegularSmul f M).hom ≫ ((comap f).map g).hom =
    tensorπ (comapRegular f) ((comap f).obj M) ≫
      (comapRegular f ◁ (comap f).map g).hom ≫ (comapRegularSmul f N).hom
  rw [tensorπ_comapRegularSmul_hom_assoc, tensorπ_whiskerLeft_hom_assoc,
    tensorπ_comapRegularSmul_hom, comap_map_hom]
  exact IsModHom.smul_hom (A := B) (f := g.hom)

/-- Upgrading `B`-modules in `C` to modules over `comapRegular f` in `Mod C A`. -/
-- Exposed so that the underlying `A`-module of `(comapRegularMod f).obj M` is `(comap f).obj M`
-- across module boundaries, matching `Mod.comap` and `Mod.comapRegular`.
@[expose] noncomputable def comapRegularMod : Mod C B ⥤ Mod (Mod C A) (comapRegular f) where
  obj M :=
    letI := comapRegularModObj f M
    ⟨(comap f).obj M⟩
  map {M N} g :=
    letI := comapRegularModObj f M
    letI := comapRegularModObj f N
    letI := isModHom_comapRegular_comap_map f g
    ⟨(comap f).map g⟩

@[simp]
lemma comapRegularMod_obj_X (M : Mod C B) : ((comapRegularMod f).obj M).X = (comap f).obj M :=
  (rfl)

@[simp]
lemma comapRegularMod_map_hom {M N : Mod C B} (g : M ⟶ N) :
    ((comapRegularMod f).map g).hom = (comap f).map g :=
  (rfl)

/-- On representatives, the action of `comapRegular f` on `(comapRegularMod f).obj M` is the action
of `B` on `M`. -/
@[reassoc (attr := simp)]
lemma tensorπ_comapRegularMod_obj_smul_hom (M : Mod C B) :
    tensorπ (comapRegular f) ((comapRegularMod f).obj M).X ≫
        γ[comapRegular f, ((comapRegularMod f).obj M).X].hom =
      γ[B, M.X] :=
  tensorπ_comapRegularSmul_hom f M

/-- Restricting the descended `B`-action on `N : Mod (Mod C A) (comapRegular f)` along `f : A ⟶ B`
recovers the original `A`-action on `N.X`. -/
lemma whiskerRight_tensorπ_smul_hom (N : Mod (Mod C A) (comapRegular f)) :
    f ▷ N.X.X ≫ tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom = γ[A, N.X.X] := by
  have h₁ : (η : 𝟙_ (Mod C A) ⟶ comapRegular f) ▷ N.X ≫ γ[comapRegular f, N.X] = (λ_ N.X).hom :=
    ModObj.one_smul_self (comapRegular f) N.X
  have h₂ := tensorπ (𝟙_ (Mod C A)) N.X ≫= congrArg Hom.hom h₁
  simp only [comp_hom', tensorπ_whiskerRight_hom_assoc, comapRegular_one_hom,
    tensorπ_leftUnitor_hom_hom] at h₂
  exact h₂

/-- Precomposing the action of `comapRegular f` on `N : Mod (Mod C A) (comapRegular f)` with the
quotient map `B ⊗ N.X.X ⟶ (comapRegular f ⊗_A N.X).X` defines a `B`-module structure on `N.X.X`. -/
@[instance_reducible]
noncomputable def ofComapRegularModObj (N : Mod (Mod C A) (comapRegular f)) : ModObj B N.X.X where
  smul := tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom
  one_smul := by
    change (η : 𝟙_ C ⟶ B) ▷ N.X.X ≫ tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom =
      (λ_ N.X.X).hom
    rw [← IsMonHom.one_hom f, comp_whiskerRight_assoc, whiskerRight_tensorπ_smul_hom,
      ModObj.one_smul_self]
  mul_smul := by
    have h₁ : (μ : comapRegular f ⊗ comapRegular f ⟶ comapRegular f) ▷ N.X ≫
        γ[comapRegular f, N.X] =
      (α_ (comapRegular f) (comapRegular f) N.X).hom ≫
        comapRegular f ◁ γ[comapRegular f, N.X] ≫ γ[comapRegular f, N.X] :=
      ModObj.mul_smul_self (comapRegular f) N.X
    have h₂ := (tensorπ (comapRegular f) (comapRegular f) ▷ N.X.X ≫
      tensorπ (comapRegular f ⊗ comapRegular f) N.X) ≫= congrArg Hom.hom h₁
    simp only [comp_hom', Category.assoc, tensorπ_whiskerRight_hom_assoc,
      ← comp_whiskerRight_assoc, tensorπ_comapRegular_mul_hom,
      tensorπ_associator_hom_hom_assoc, tensorπ_whiskerLeft_hom_assoc,
      ← whiskerLeft_comp_assoc] at h₂
    exact h₂

/-- A morphism `g : N ⟶ N'` of `comapRegular f`-modules in `Mod C A` induces a morphism of the
underlying `B`-modules in `C`. -/
lemma isModHom_ofComapRegularMod {N N' : Mod (Mod C A) (comapRegular f)} (g : N ⟶ N') :
    letI := ofComapRegularModObj f N
    letI := ofComapRegularModObj f N'
    IsModHom B g.hom.hom := by
  let := ofComapRegularModObj f N
  let := ofComapRegularModObj f N'
  refine ⟨?_⟩
  have h := tensorπ (comapRegular f) N.X ≫=
    congrArg Hom.hom (IsModHom.smul_hom (A := comapRegular f) (f := g.hom))
  simp only [comp_hom', selfLeftAction_actionHomRight, tensorπ_whiskerLeft_hom_assoc] at h
  change (tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom) ≫ g.hom.hom =
    B ◁ g.hom.hom ≫ tensorπ (comapRegular f) N'.X ≫ γ[comapRegular f, N'.X].hom
  rw [Category.assoc]
  exact h

/-- Descending modules over `comapRegular f` in `Mod C A` to `B`-modules in `C`. -/
@[expose] noncomputable def ofComapRegularMod : Mod (Mod C A) (comapRegular f) ⥤ Mod C B where
  obj N :=
    letI := ofComapRegularModObj f N
    ⟨N.X.X⟩
  map {N N'} g :=
    letI := ofComapRegularModObj f N
    letI := ofComapRegularModObj f N'
    letI := isModHom_ofComapRegularMod f g
    ⟨g.hom.hom⟩

@[simp]
lemma ofComapRegularMod_obj_X (N : Mod (Mod C A) (comapRegular f)) :
    ((ofComapRegularMod f).obj N).X = N.X.X :=
  (rfl)

@[simp]
lemma ofComapRegularMod_map_hom {N N' : Mod (Mod C A) (comapRegular f)} (g : N ⟶ N') :
    ((ofComapRegularMod f).map g).hom = g.hom.hom :=
  (rfl)

@[simp]
lemma ofComapRegularMod_obj_smul (N : Mod (Mod C A) (comapRegular f)) :
    γ[B, ((ofComapRegularMod f).obj N).X] =
      tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom :=
  (rfl)

/-- A `B`-module `M` is isomorphic, by the identity of `M.X`, to the `B`-module underlying
`(comapRegularMod f).obj M`. -/
noncomputable def comapRegularModUnitIsoApp (M : Mod C B) :
    M ≅ (ofComapRegularMod f).obj ((comapRegularMod f).obj M) where
  hom := Hom.mk' (𝟙 M.X) <|
    (Category.comp_id _).trans <| (tensorπ_comapRegularMod_obj_smul_hom f M).symm.trans <|
      ((MonoidalLeftAction.actionHomRight_id B _ =≫ _).trans (Category.id_comp _)).symm
  inv := Hom.mk' (𝟙 M.X) <|
    (Category.comp_id _).trans <| (tensorπ_comapRegularMod_obj_smul_hom f M).trans <|
      ((MonoidalLeftAction.actionHomRight_id B _ =≫ _).trans (Category.id_comp _)).symm
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

@[simp]
lemma comapRegularModUnitIsoApp_hom_hom (M : Mod C B) :
    (comapRegularModUnitIsoApp f M).hom.hom = 𝟙 M.X :=
  (rfl)

@[simp]
lemma comapRegularModUnitIsoApp_inv_hom (M : Mod C B) :
    (comapRegularModUnitIsoApp f M).inv.hom = 𝟙 M.X :=
  (rfl)

private def mkModIso {R : Mod C A} [MonObj R] {N₁ N₂ : Mod (Mod C A) R}
    (e : N₁.X ≅ N₂.X) (h : IsModHom R e.hom) : N₁ ≅ N₂ :=
  letI : ModObj R N₁.X := N₁.mod
  letI : ModObj R N₂.X := N₂.mod
  letI : IsModHom R e.hom := h
  { hom := ⟨e.hom⟩
    inv := ⟨e.inv⟩
    hom_inv_id := Hom.ext e.hom_inv_id
    inv_hom_id := Hom.ext e.inv_hom_id }

/-- A `comapRegular f`-module `N` is isomorphic, by the identity of `N.X.X`, to the upgrade of its
underlying `B`-module. -/
noncomputable def comapRegularModCounitIsoApp (N : Mod (Mod C A) (comapRegular f)) :
    (comapRegularMod f).obj ((ofComapRegularMod f).obj N) ≅ N := by
  let M₀ := (ofComapRegularMod f).obj N
  let N₀ := (comapRegularMod f).obj M₀
  let e : N₀.X ≅ N.X :=
    { hom := Hom.mk' (𝟙 N.X.X) <|
        (Category.comp_id _).trans <| (whiskerRight_tensorπ_smul_hom f N).trans <|
          ((MonoidalLeftAction.actionHomRight_id A _ =≫ _).trans (Category.id_comp _)).symm
      inv := Hom.mk' (𝟙 N.X.X) <|
        (Category.comp_id _).trans <| (whiskerRight_tensorπ_smul_hom f N).symm.trans <|
          ((MonoidalLeftAction.actionHomRight_id A _ =≫ _).trans (Category.id_comp _)).symm
      hom_inv_id := Hom.ext (Category.id_comp _)
      inv_hom_id := Hom.ext (Category.id_comp _) }
  refine mkModIso e ⟨hom_ext _ _ ?_⟩
  rw [← cancel_epi (tensorπ _ _)]
  have hL : tensorπ (comapRegular f) N₀.X ≫ (γ[comapRegular f, N₀.X] ≫ e.hom).hom =
      tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom := by
    rw [comp_hom', tensorπ_comapRegularMod_obj_smul_hom_assoc]
    exact Category.comp_id _
  have hR : tensorπ (comapRegular f) N₀.X ≫
      (comapRegular f ⊴ₗ e.hom ≫ γ[comapRegular f, N.X]).hom =
      tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom := by
    rw [selfLeftAction_actionHomRight, comp_hom', tensorπ_whiskerLeft_hom_assoc]
    exact (whiskerLeft_id B N.X.X =≫ _).trans (Category.id_comp _)
  exact hL.trans hR.symm

@[simp]
lemma comapRegularModCounitIsoApp_hom_hom_hom (N : Mod (Mod C A) (comapRegular f)) :
    (comapRegularModCounitIsoApp f N).hom.hom.hom = 𝟙 N.X.X :=
  (rfl)

@[simp]
lemma comapRegularModCounitIsoApp_inv_hom_hom (N : Mod (Mod C A) (comapRegular f)) :
    (comapRegularModCounitIsoApp f N).inv.hom.hom = 𝟙 N.X.X :=
  (rfl)

/-- The equivalence of categories between `B`-modules in `C` and modules over `comapRegular f` in
`Mod C A`. Both functors preserve underlying objects in `C`, and the unit and counit are identities
on them. -/
@[expose] noncomputable def comapRegularModEquivalence :
    Mod C B ≌ Mod (Mod C A) (comapRegular f) where
  functor := comapRegularMod f
  inverse := ofComapRegularMod f
  unitIso := NatIso.ofComponents (comapRegularModUnitIsoApp f) fun _ ↦ by
    ext
    simp only [Functor.id_obj, Functor.comp_obj, comp_hom', comapRegularModUnitIsoApp_hom_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (comapRegularModCounitIsoApp f) fun _ ↦ by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, comp_hom',
      comapRegularModCounitIsoApp_hom_hom_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp _ := by
    ext
    simp only [Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app, comp_hom',
      comapRegularMod_map_hom, id_hom']
    exact Category.id_comp _

@[simp]
lemma comapRegularModEquivalence_functor :
    (comapRegularModEquivalence f).functor = comapRegularMod f :=
  (rfl)

@[simp]
lemma comapRegularModEquivalence_inverse :
    (comapRegularModEquivalence f).inverse = ofComapRegularMod f :=
  (rfl)

@[simp]
lemma comapRegularModEquivalence_unitIso_hom_app_hom (M : Mod C B) :
    ((comapRegularModEquivalence f).unitIso.hom.app M).hom = 𝟙 M.X :=
  (rfl)

@[simp]
lemma comapRegularModEquivalence_unitIso_inv_app_hom (M : Mod C B) :
    ((comapRegularModEquivalence f).unitIso.inv.app M).hom = 𝟙 M.X :=
  (rfl)

@[simp]
lemma comapRegularModEquivalence_counitIso_hom_app_hom_hom
    (N : Mod (Mod C A) (comapRegular f)) :
    (((comapRegularModEquivalence f).counitIso.hom.app N).hom).hom = 𝟙 N.X.X :=
  (rfl)

@[simp]
lemma comapRegularModEquivalence_counitIso_inv_app_hom_hom
    (N : Mod (Mod C A) (comapRegular f)) :
    (((comapRegularModEquivalence f).counitIso.inv.app N).hom).hom = 𝟙 N.X.X :=
  (rfl)

private lemma comapRegularMod_regular_smul_eq :
    γ[comapRegular f, ((comapRegularMod f).obj (regular B)).X] =
      γ[comapRegular f, (regular (comapRegular f)).X] := by
  apply hom_ext
  rw [← cancel_epi (tensorπ _ _), tensorπ_comapRegularMod_obj_smul_hom]
  exact (tensorπ_comapRegular_mul_hom f).symm

/-- Under `comapRegularMod f`, the regular `B`-module corresponds to the regular
`comapRegular f`-module, by the identity of `B`. -/
noncomputable def comapRegularModRegularIso :
    (comapRegularMod f).obj (regular B) ≅ regular (comapRegular f) where
  hom := Hom.mk' (𝟙 (comapRegular f)) <|
    (Category.comp_id _).trans <| (comapRegularMod_regular_smul_eq f).trans <|
      ((MonoidalLeftAction.actionHomRight_id (comapRegular f) _ =≫ _).trans
        (Category.id_comp _)).symm
  inv := Hom.mk' (𝟙 (comapRegular f)) <|
    (Category.comp_id _).trans <| (comapRegularMod_regular_smul_eq f).symm.trans <|
      ((MonoidalLeftAction.actionHomRight_id (comapRegular f) _ =≫ _).trans
        (Category.id_comp _)).symm
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

@[simp]
lemma comapRegularModRegularIso_hom_hom :
    (comapRegularModRegularIso f).hom.hom = 𝟙 (comapRegular f) :=
  (rfl)

@[simp]
lemma comapRegularModRegularIso_inv_hom :
    (comapRegularModRegularIso f).inv.hom = 𝟙 (comapRegular f) :=
  (rfl)

private lemma tensorπ_comap_smul_hom {R₁ R₂ : Mod C A} [MonObj R₁] [MonObj R₂]
    (ψ : R₁ ⟶ R₂) [IsMonHom ψ] (N : Mod (Mod C A) R₂) :
    tensorπ R₁ ((comap ψ).obj N).X ≫ γ[R₁, ((comap ψ).obj N).X].hom =
      ψ.hom ▷ N.X.X ≫ tensorπ R₂ N.X ≫ γ[R₂, N.X].hom :=
  tensorπ_whiskerRight_hom_assoc ψ N.X γ[R₂, N.X].hom

/-- Component isomorphism identifying restriction along `φ : B ⟶ B'` before `comapRegularMod f`
with `comapRegularMod f'` followed by restriction along `comapRegularMap f f' φ w`. -/
noncomputable def comapRegularModComapIsoApp {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularMod f).obj ((comap φ).obj M) ≅
      (comap (comapRegularMap f f' φ w)).obj ((comapRegularMod f').obj M) := by
  let N₁ := (comapRegularMod f).obj ((comap φ).obj M)
  let N₂ := (comapRegularMod f').obj M
  let N₂' := (comap (comapRegularMap f f' φ w)).obj N₂
  let e : N₁.X ≅ N₂'.X :=
    { hom := Hom.mk' (𝟙 M.X) (by
        change (f ▷ M.X ≫ φ ▷ M.X ≫ γ[B', M.X]) ≫ 𝟙 M.X =
          A ◁ 𝟙 M.X ≫ f' ▷ M.X ≫ γ[B', M.X]
        simp [← comp_whiskerRight_assoc, w])
      inv := Hom.mk' (𝟙 M.X) (by
        change (f' ▷ M.X ≫ γ[B', M.X]) ≫ 𝟙 M.X =
          A ◁ 𝟙 M.X ≫ f ▷ M.X ≫ φ ▷ M.X ≫ γ[B', M.X]
        simp [← comp_whiskerRight_assoc, w])
      hom_inv_id := Hom.ext (Category.id_comp _)
      inv_hom_id := Hom.ext (Category.id_comp _) }
  have hγ : tensorπ (comapRegular f) N₂'.X ≫ γ[comapRegular f, N₂'.X].hom =
      φ ▷ M.X ≫ γ[B', M.X] := by
    rw [tensorπ_comap_smul_hom, comapRegularMap_hom, tensorπ_comapRegularMod_obj_smul_hom]
    rfl
  refine mkModIso e ⟨hom_ext _ _ ?_⟩
  rw [← cancel_epi (tensorπ _ _)]
  have hL : tensorπ (comapRegular f) N₁.X ≫ (γ[comapRegular f, N₁.X] ≫ e.hom).hom =
      φ ▷ M.X ≫ γ[B', M.X] := by
    rw [comp_hom', tensorπ_comapRegularMod_obj_smul_hom_assoc]
    exact Category.comp_id _
  have hR : tensorπ (comapRegular f) N₁.X ≫
      (comapRegular f ⊴ₗ e.hom ≫ γ[comapRegular f, N₂'.X]).hom =
      φ ▷ M.X ≫ γ[B', M.X] := by
    rw [selfLeftAction_actionHomRight, comp_hom', tensorπ_whiskerLeft_hom_assoc, hγ]
    exact (whiskerLeft_id B M.X =≫ _).trans (Category.id_comp _)
  exact hL.trans hR.symm

@[simp]
lemma comapRegularModComapIsoApp_hom_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularModComapIsoApp f f' φ w M).hom.hom.hom = 𝟙 M.X :=
  (rfl)

@[simp]
lemma comapRegularModComapIsoApp_inv_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularModComapIsoApp f f' φ w M).inv.hom.hom = 𝟙 M.X :=
  (rfl)

/-- Restricting a `B'`-module along a morphism of commutative monoids `φ : B ⟶ B'` under `A`
corresponds under `comapRegularMod` to restricting along `comapRegularMap f f' φ w`. -/
noncomputable def comapRegularModComapIso {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') :
    comap φ ⋙ comapRegularMod f ≅
      comapRegularMod f' ⋙ comap (comapRegularMap f f' φ w) :=
  NatIso.ofComponents (comapRegularModComapIsoApp f f' φ w) fun _ ↦
    Hom.ext (Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

@[simp]
lemma comapRegularModComapIso_hom_app_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    ((comapRegularModComapIso f f' φ w).hom.app M).hom.hom = 𝟙 M.X :=
  (rfl)

@[simp]
lemma comapRegularModComapIso_inv_app_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    ((comapRegularModComapIso f f' φ w).inv.app M).hom.hom = 𝟙 M.X :=
  (rfl)

end Module

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A] {B : C} [MonObj B] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- A commutative monoid `B` under a commutative monoid `A` is a commutative monoid object of
`A`-modules. -/
instance isCommMonObjComapRegular : IsCommMonObj (comapRegular f) where
  mul_comm := by
    ext
    simp only [comp_hom', tensorπ_braiding_hom_hom_assoc, tensorπ_comapRegular_mul_hom]
    exact IsCommMonObj.mul_comm B

end Symmetric

end Mod

end CategoryTheory
