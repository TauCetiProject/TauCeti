/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mod.Basic
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
* `Mod.tensorπ_comapRegularMod_obj_smul_hom`, `Mod.whiskerRight_tensorπ_comapRegular_smul_hom`:
  characterization of the `comapRegular f`-action on representatives and recovery of the `A`-action
  along `f`.

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
-- Not `@[simp]`: `Mod.scalarRestriction_smul` and `ModObj.smul_eq_mul` already simplify the LHS.
@[reassoc]
lemma comapRegular_smul : γ[A, (comapRegular f).X] = f ▷ B ≫ μ :=
  (rfl)

/-- A morphism of monoids `φ : B ⟶ B'` under `A` (`f ≫ φ = f'`) is a morphism of the corresponding
`A`-modules `comapRegular f ⟶ comapRegular f'`. -/
def comapRegularMap {B' : C} [MonObj B'] (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ]
    (w : f ≫ φ = f' := by cat_disch) : comapRegular f ⟶ comapRegular f' :=
  Hom.mk' φ (by
    -- Unfold the carriers and restricted actions to morphisms in `C` so `IsMonHom.mul_hom` applies.
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
  simp only [selfLeftAction_actionObj]

@[reassoc (attr := simp)]
lemma tensorπ_comapRegularSmul_hom (M : Mod C B) :
    tensorπ (comapRegular f) ((comap f).obj M) ≫ (comapRegularSmul f M).hom = γ[B, M.X] :=
  tensorπ_tensorDesc _ _

/-- A commutative monoid `B` under a commutative monoid `A` is a monoid object of `A`-modules, with
multiplication that of `B` on representatives and unit `f : A ⟶ B`. -/
noncomputable instance monObjComapRegular : MonObj (comapRegular f) :=
  -- Bind `one` and `mul` at their `MonObj (comapRegular f)` morphism types so `simp` sees
  -- well-typed `comapRegular f` morphisms in the monoid laws rather than `A ⟶ B` or
  -- `(comap f).obj (regular B)`.
  let one : 𝟙_ (Mod C A) ⟶ comapRegular f := Hom.mk' (M := 𝟙_ (Mod C A)) f (by
    rw [comapRegular_smul]
    exact (IsMonHom.mul_hom f).trans (by
      rw [tensorHom_def', Category.assoc]
      exact (selfLeftAction_actionHomRight C A _ _ f =≫ _).symm))
  let mul : comapRegular f ⊗ comapRegular f ⟶ comapRegular f := comapRegularSmul f (regular B)
  have hone : one.hom = f := rfl
  have hmul : tensorπ (comapRegular f) (comapRegular f) ≫ mul.hom = (μ : B ⊗ B ⟶ B) :=
    (tensorπ_comapRegularSmul_hom f (regular B)).trans (ModObj.smul_eq_mul B)
  { one := one
    mul := mul
    one_mul := by
      ext
      simp -zeta only [comp_hom', tensorπ_whiskerRight_hom_assoc, hone, hmul,
        tensorπ_leftUnitor_hom_hom]
      exact (comapRegular_smul f).symm
    mul_one := by
      ext
      simp -zeta only [comp_hom', tensorπ_whiskerLeft_hom_assoc, hone, hmul,
        tensorπ_rightUnitor_hom_hom, comapRegular_smul]
      exact (braiding_inv_whiskerRight_mul f).symm
    mul_assoc := by
      apply hom_ext
      rw [← cancel_epi (tensorπ _ _ ▷ _ ≫ tensorπ _ _)]
      simp -zeta only [comp_hom', Category.assoc, tensorπ_whiskerRight_hom_assoc,
        ← comp_whiskerRight_assoc, hmul, tensorπ_associator_hom_hom_assoc,
        tensorπ_whiskerLeft_hom_assoc, ← whiskerLeft_comp_assoc]
      exact MonObj.mul_assoc B }

/-- On representatives, the multiplication `B ⊗_A B ⟶ B` is the multiplication of `B`. -/
@[reassoc (attr := simp)]
lemma tensorπ_comapRegular_mul_hom :
    tensorπ _ _ ≫ (μ : comapRegular f ⊗ comapRegular f ⟶ _).hom = (μ : B ⊗ B ⟶ B) := by
  exact (tensorπ_comapRegularSmul_hom f (regular B)).trans (ModObj.smul_eq_mul B)

/-- The unit of `B` as a monoid of `A`-modules is `f : A ⟶ B`. -/
@[simp]
lemma comapRegular_one_hom : (η : 𝟙_ (Mod C A) ⟶ comapRegular f).hom = f := by
  rfl

/-- A morphism of commutative monoids `φ : B ⟶ B'` under `A` induces a morphism of monoid objects
`comapRegular f ⟶ comapRegular f'` in `Mod C A`. -/
instance isMonHom_comapRegularMap {B' : C} [MonObj B'] [IsCommMonObj B'] (f' : A ⟶ B')
    [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') :
    IsMonHom (comapRegularMap f f' φ w) where
  one_hom := by
    ext
    simp only [comp_hom', comapRegular_one_hom, comapRegularMap_hom]
    exact w
  mul_hom := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _)]
    simp [IsMonHom.mul_hom φ]

section Module

/-- Restricting a `B`-module `M` along `f : A ⟶ B` equips `(comap f).obj M` with an action of the
monoid `comapRegular f` in `Mod C A`. -/
@[instance_reducible]
noncomputable def comapRegularModObj (M : Mod C B) : ModObj (comapRegular f) ((comap f).obj M) where
  smul := comapRegularSmul f M
  one_smul := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _)]
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso, comp_hom',
      tensorπ_whiskerRight_hom_assoc, comapRegular_one_hom, tensorπ_comapRegularSmul_hom,
      tensorπ_leftUnitor_hom_hom]
    exact (comap_obj_smul f M).symm
  mul_smul := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _ ▷ _ ≫ tensorπ _ _)]
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso, comp_hom', Category.assoc, tensorπ_whiskerRight_hom_assoc,
      ← comp_whiskerRight_assoc, tensorπ_comapRegular_mul_hom,
      tensorπ_associator_hom_hom_assoc, tensorπ_whiskerLeft_hom_assoc, ← whiskerLeft_comp_assoc]
    -- `tensorπ_comapRegularSmul_hom` has syntactic right-hand side in `B ⊗ M.X ⟶ M.X`, which
    -- cannot be rewritten directly under `(comapRegular f).X ◁ _` before unfolding the carriers
    -- `(comapRegular f).X = B` and `((comap f).obj M).X = M.X`. Bind `γ[B, M.X]` at the module
    -- carrier type first, then restate the resulting equation in `C`.
    let g : (comapRegular f).X ⊗ ((comap f).obj M).X ⟶ ((comap f).obj M).X := γ[B, M.X]
    have hg : tensorπ (comapRegular f) ((comap f).obj M) ≫ (comapRegularSmul f M).hom = g :=
      tensorπ_comapRegularSmul_hom f M
    rw [hg]
    change (μ : B ⊗ B ⟶ B) ▷ M.X ≫ γ[B, M.X] =
      (α_ B B M.X).hom ≫ B ◁ γ[B, M.X] ≫ γ[B, M.X]
    exact ModObj.mul_smul_self B M.X

/-- Restricting scalars along `f` equips `(comap f).obj M` with the descended action
`comapRegularSmul f M` of `comapRegular f`. -/
@[simp]
lemma comapRegularModObj_smul (M : Mod C B) :
    letI := comapRegularModObj f M
    γ[comapRegular f, (comap f).obj M] = comapRegularSmul f M :=
  (rfl)

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
  simp only [comapRegularModObj_smul, comp_hom', selfLeftAction_actionHomRight,
    tensorπ_whiskerLeft_hom_assoc, tensorπ_comapRegularSmul_hom_assoc, tensorπ_comapRegularSmul_hom]
  dsimp only [comap, comapRegular]
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
@[reassoc (attr := simp)]
lemma whiskerRight_tensorπ_comapRegular_smul_hom (N : Mod (Mod C A) (comapRegular f)) :
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
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    rw [← IsMonHom.one_hom f, comp_whiskerRight_assoc, whiskerRight_tensorπ_comapRegular_smul_hom,
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

/-- The descended `B`-module structure on `N.X.X` acts through `tensorπ (comapRegular f) N.X`
followed by the `comapRegular f`-action on `N.X`. -/
@[reassoc, simp]
lemma ofComapRegularModObj_smul (N : Mod (Mod C A) (comapRegular f)) :
    letI := ofComapRegularModObj f N
    γ[B, N.X.X] = tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom :=
  (rfl)

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
  dsimp only [comapRegular] at h
  simp only [ofComapRegularModObj_smul, selfLeftAction_actionHomRight, Category.assoc]
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

@[reassoc, simp]
lemma ofComapRegularMod_obj_smul (N : Mod (Mod C A) (comapRegular f)) :
    γ[B, ((ofComapRegularMod f).obj N).X] =
      tensorπ (comapRegular f) N.X ≫ γ[comapRegular f, N.X].hom :=
  (rfl)

/-- The equivalence of categories between `B`-modules in `C` and modules over `comapRegular f` in
`Mod C A`. Both functors preserve underlying objects in `C`, and the unit and counit are identities
on them. -/
-- Exposed so `.functor` and `.inverse` reduce in public signatures, giving the unit and counit
-- component projections codomain `M.X` and `N.X.X` without `eqToHom`.
@[expose] noncomputable def comapRegularModEquivalence :
    Mod C B ≌ Mod (Mod C A) (comapRegular f) :=
  let u (M : Mod C B) : M ≅ (ofComapRegularMod f).obj ((comapRegularMod f).obj M) :=
    isoOfSmulEq (X := M.X) M.mod (ofComapRegularModObj f ((comapRegularMod f).obj M))
      ((ofComapRegularModObj_smul f ((comapRegularMod f).obj M)).trans
        (tensorπ_comapRegularMod_obj_smul_hom f M)).symm
  have hu (M : Mod C B) : (u M).hom.hom = 𝟙 M.X := isoOfSmulEq_hom_hom _ _ _
  let c (N : Mod (Mod C A) (comapRegular f)) :
      (comapRegularMod f).obj ((ofComapRegularMod f).obj N) ≅ N :=
    let e : ((comapRegularMod f).obj ((ofComapRegularMod f).obj N)).X ≅ N.X :=
      isoOfSmulEq (X := N.X.X) (scalarRestriction f ((ofComapRegularMod f).obj N).X) N.X.mod
        ((scalarRestriction_smul f ((ofComapRegularMod f).obj N).X).trans
          ((f ▷ N.X.X ≫= ofComapRegularMod_obj_smul f N).trans
            (whiskerRight_tensorπ_comapRegular_smul_hom f N)))
    mkIso e <| hom_ext _ _ <| by
      have he : e.hom.hom = 𝟙 N.X.X := isoOfSmulEq_hom_hom _ _ _
      rw [← cancel_epi (tensorπ _ _)]
      simp only [selfLeftAction_actionHomRight, comp_hom', tensorπ_whiskerLeft_hom_assoc,
        tensorπ_comapRegularMod_obj_smul_hom_assoc, ofComapRegularMod_obj_smul]
      dsimp only [ofComapRegularMod, comapRegularMod, comap] at he ⊢
      simp [he]
  have hc (N : Mod (Mod C A) (comapRegular f)) : (c N).hom.hom.hom = 𝟙 N.X.X :=
    (congrArg Hom.hom (mkIso_hom_hom _ _)).trans (isoOfSmulEq_hom_hom _ _ _)
  { functor := comapRegularMod f
    inverse := ofComapRegularMod f
    unitIso := NatIso.ofComponents u fun _ ↦ by
      ext; dsimp -zeta only [ofComapRegularMod, comapRegularMod, comap]; simp -zeta [hu]
    counitIso := NatIso.ofComponents c fun _ ↦ by
      ext; dsimp -zeta only [ofComapRegularMod, comapRegularMod, comap]; simp -zeta [hc]
    functor_unitIso_comp _ := by
      ext
      simp -zeta only [Functor.id_obj, Functor.comp_obj, comp_hom', comapRegularMod_map_hom,
        NatIso.ofComponents_hom_app]
      dsimp -zeta only [ofComapRegularMod, comapRegularMod, comap]
      simp -zeta [hu, hc] }

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
    ((comapRegularModEquivalence f).unitIso.hom.app M).hom = 𝟙 M.X := by
  simp only [comapRegularModEquivalence]
  exact isoOfSmulEq_hom_hom _ _ _

@[simp]
lemma comapRegularModEquivalence_unitIso_inv_app_hom (M : Mod C B) :
    ((comapRegularModEquivalence f).unitIso.inv.app M).hom = 𝟙 M.X := by
  simp only [comapRegularModEquivalence]
  exact isoOfSmulEq_inv_hom _ _ _

@[simp]
lemma comapRegularModEquivalence_counitIso_hom_app_hom_hom
    (N : Mod (Mod C A) (comapRegular f)) :
    (((comapRegularModEquivalence f).counitIso.hom.app N).hom).hom = 𝟙 N.X.X := by
  simp only [comapRegularModEquivalence, NatIso.ofComponents_hom_app]
  exact (congrArg Hom.hom (mkIso_hom_hom _ _)).trans (isoOfSmulEq_hom_hom _ _ _)

@[simp]
lemma comapRegularModEquivalence_counitIso_inv_app_hom_hom
    (N : Mod (Mod C A) (comapRegular f)) :
    (((comapRegularModEquivalence f).counitIso.inv.app N).hom).hom = 𝟙 N.X.X := by
  simp only [comapRegularModEquivalence, NatIso.ofComponents_inv_app]
  exact (congrArg Hom.hom (mkIso_inv_hom _ _)).trans (isoOfSmulEq_inv_hom _ _ _)

/-- Under `comapRegularMod f`, the regular `B`-module corresponds to the regular
`comapRegular f`-module, by the identity of `B`. -/
noncomputable def comapRegularModRegularIso :
    (comapRegularMod f).obj (regular B) ≅ regular (comapRegular f) :=
  -- Both module structures have action map `comapRegularSmul f (regular B)` by definition.
  isoOfSmulEq (X := comapRegular f)
    (comapRegularModObj f (regular B)) (ModObj.regular (comapRegular f)) rfl

@[simp]
lemma comapRegularModRegularIso_hom_hom :
    (comapRegularModRegularIso f).hom.hom = 𝟙 (comapRegular f) := by
  unfold comapRegularModRegularIso
  exact isoOfSmulEq_hom_hom _ _ _

@[simp]
lemma comapRegularModRegularIso_inv_hom :
    (comapRegularModRegularIso f).inv.hom = 𝟙 (comapRegular f) := by
  unfold comapRegularModRegularIso
  exact isoOfSmulEq_inv_hom _ _ _

/- Component isomorphism identifying restriction along `φ : B ⟶ B'` before `comapRegularMod f`
with `comapRegularMod f'` followed by restriction along `comapRegularMap f f' φ w`. -/
private noncomputable def comapRegularModComapIsoApp {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularMod f).obj ((comap φ).obj M) ≅
      (comap (comapRegularMap f f' φ w)).obj ((comapRegularMod f').obj M) :=
  let e : ((comapRegularMod f).obj ((comap φ).obj M)).X ≅
      ((comap (comapRegularMap f f' φ w)).obj ((comapRegularMod f').obj M)).X :=
    isoOfSmulEq (X := M.X) (scalarRestriction f ((comap φ).obj M).X) (scalarRestriction f' M.X)
      (by dsimp only [ModObj.smul, scalarRestriction]
          rw [comap_obj_smul]
          dsimp only [comap, selfLeftAction_actionHomLeft]
          rw [← comp_whiskerRight_assoc, w])
  mkIso e <| hom_ext _ _ <| by
    have he : e.hom.hom = 𝟙 M.X := isoOfSmulEq_hom_hom _ _ _
    have hR := tensorπ_comapRegularMod_obj_smul_hom f' M
    rw [← cancel_epi (tensorπ _ _)]
    simp only [selfLeftAction_actionHomRight, comp_hom', tensorπ_whiskerLeft_hom_assoc,
      tensorπ_comapRegularMod_obj_smul_hom_assoc]
    simp only [comap_obj_smul, selfLeftAction_actionHomLeft, comp_hom']
    dsimp only [comap, comapRegularMod] at he hR ⊢
    simp [he, hR]

private lemma comapRegularModComapIsoApp_hom_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularModComapIsoApp f f' φ w M).hom.hom.hom = 𝟙 M.X := by
  unfold comapRegularModComapIsoApp
  dsimp only
  exact (congrArg Hom.hom (mkIso_hom_hom _ _)).trans (isoOfSmulEq_hom_hom _ _ _)

private lemma comapRegularModComapIsoApp_inv_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    (comapRegularModComapIsoApp f f' φ w M).inv.hom.hom = 𝟙 M.X := by
  unfold comapRegularModComapIsoApp
  dsimp only
  exact (congrArg Hom.hom (mkIso_inv_hom _ _)).trans (isoOfSmulEq_inv_hom _ _ _)

/-- Restricting a `B'`-module along a morphism of commutative monoids `φ : B ⟶ B'` under `A`
corresponds under `comapRegularMod` to restricting along `comapRegularMap f f' φ w`. -/
noncomputable def comapRegularModComapIso {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') :
    comap φ ⋙ comapRegularMod f ≅
      comapRegularMod f' ⋙ comap (comapRegularMap f f' φ w) :=
  NatIso.ofComponents (comapRegularModComapIsoApp f f' φ w) fun _ ↦ by
    ext
    simp [comapRegularMod, comap, comapRegularModComapIsoApp_hom_hom_hom]

@[simp]
lemma comapRegularModComapIso_hom_app_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    ((comapRegularModComapIso f f' φ w).hom.app M).hom.hom = 𝟙 M.X := by
  simpa only [comapRegularModComapIso, NatIso.ofComponents_hom_app] using
    comapRegularModComapIsoApp_hom_hom_hom f f' φ w M

@[simp]
lemma comapRegularModComapIso_inv_app_hom_hom {B' : C} [MonObj B'] [IsCommMonObj B']
    (f' : A ⟶ B') [IsMonHom f'] (φ : B ⟶ B') [IsMonHom φ] (w : f ≫ φ = f') (M : Mod C B') :
    ((comapRegularModComapIso f f' φ w).inv.app M).hom.hom = 𝟙 M.X := by
  simpa only [comapRegularModComapIso, NatIso.ofComponents_inv_app] using
    comapRegularModComapIsoApp_inv_hom_hom f f' φ w M

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
