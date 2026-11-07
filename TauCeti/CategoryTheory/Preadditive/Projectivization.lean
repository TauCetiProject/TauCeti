/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.Functor.MapBijective
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Projectivization

Let `C` be a preadditive category with finite biproducts, `M` an object of `C` and
`Γ = End M`. The **additive closure** `add M` (`TauCeti.additiveClosure M`) consists of the
direct summands of finite biproducts `Mⁿ`. The functor `Hom(M, -)` takes values in right
`Γ`-modules, that is in `Γᵐᵒᵖ`-modules (Mathlib's `CategoryTheory.preadditiveCoyonedaObj M`), and
**projectivization** says that it identifies `add M` with the finitely generated projective right
`Γ`-modules:

* `Hom(M, -)` is fully faithful on `add M`
  (`TauCeti.fullyFaithfulPreadditiveCoyonedaObj`): for `X` in `add M`, every `Γ`-linear map
  `Hom(M, X) → Hom(M, Y)` is composition with a unique morphism `X ⟶ Y`
  (`TauCeti.preadditiveCoyonedaObj_map_bijective`). For `X = M` this is the Yoneda argument
  `φ(f) = φ(f ≫ 𝟙) = f ≫ φ(𝟙)`, and the general case follows by passing to finite biproducts
  and retracts;
* `Hom(M, Mⁿ)` is the free module `Γᵐᵒᵖⁿ` (`TauCeti.preadditiveCoyonedaObjBiproductIso`), so
  `Hom(M, X)` is finitely generated and projective for `X` in `add M`;
* if idempotents split in `C`, every finitely generated projective right `Γ`-module is
  `Hom(M, X)` for some `X` in `add M`: it is a direct summand of some `Γᵐᵒᵖⁿ = Hom(M, Mⁿ)`, and
  the corresponding idempotent of `Mⁿ` splits.

Together these make `Hom(M, -)` an equivalence `TauCeti.projectivizationFunctor M` between
`add M` and the finitely generated projective `Γᵐᵒᵖ`-modules when idempotents split in `C`. For
the module category of a ring `A`, which is abelian and hence idempotent complete, and an
`A`-module `M`, this identifies the direct summands of the modules `Mⁿ` with the finitely
generated projective right modules over `End_A(M)`.

## Main definitions

* `TauCeti.additiveClosure M`: the direct summands of finite biproducts of copies of `M`.
* `TauCeti.fullyFaithfulPreadditiveCoyonedaObj M`: `Hom(M, -)` is fully faithful on `add M`.
* `TauCeti.preadditiveCoyonedaObjBiproductIso M n`: `Hom(M, Mⁿ) ≅ Γᵐᵒᵖⁿ`.
* `TauCeti.projectivizationFunctor M`: `Hom(M, -)` from `add M` to the finitely generated
  projective `Γᵐᵒᵖ`-modules; it is an equivalence in an idempotent-complete category.

## Main results

* `TauCeti.additiveClosure_le_iff`: `add M` is the smallest property holding for `M` that is
  stable under retracts and closed under finite products.
* `TauCeti.preadditiveCoyonedaObj_map_bijective`: for `X` in `add M`, composition identifies
  `X ⟶ Y` with the `Γᵐᵒᵖ`-linear maps `Hom(M, X) → Hom(M, Y)`.
* `TauCeti.finiteProjectiveModules_preadditiveCoyonedaObj_obj`: `Hom(M, X)` is finitely
  generated and projective for `X` in `add M`.
* `TauCeti.finiteProjectiveModules_le_essImage`: in an idempotent-complete category, every
  finitely generated projective `Γᵐᵒᵖ`-module is `Hom(M, X)` for some `X` in `add M`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition II.2.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-! ### The additive closure of an object -/

/-- The **additive closure** `add M` of an object `M`: the objects that are direct summands
(retracts) of a finite biproduct `Mⁿ` of copies of `M`. -/
def additiveClosure (M : C) : ObjectProperty C :=
  fun X ↦ ∃ n : ℕ, Nonempty (Retract X (⨁ fun _ : Fin n ↦ M))

variable {M : C}

theorem additiveClosure_iff {X : C} :
    additiveClosure M X ↔ ∃ n : ℕ, Nonempty (Retract X (⨁ fun _ : Fin n ↦ M)) :=
  Iff.rfl

theorem additiveClosure_biproduct (n : ℕ) : additiveClosure M (⨁ fun _ : Fin n ↦ M) :=
  ⟨n, ⟨Retract.refl _⟩⟩

variable (M) in
theorem additiveClosure_self : additiveClosure M M :=
  ⟨1, ⟨{ i := biproduct.ι (fun _ : Fin 1 ↦ M) 0, r := biproduct.π _ 0 }⟩⟩

instance : (additiveClosure M).IsStableUnderRetracts where
  of_retract h := fun ⟨n, ⟨e⟩⟩ ↦ ⟨n, ⟨h.trans e⟩⟩

instance : (additiveClosure M).Nonempty :=
  ⟨M, additiveClosure_self M⟩

section Biprod

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The biproduct of `Mⁿ` and `Mᵐ` is `Mⁿ⁺ᵐ`. -/
private noncomputable def biprodBiproductIso (n m : ℕ) :
    (⨁ fun _ : Fin n ↦ M) ⊞ (⨁ fun _ : Fin m ↦ M) ≅ ⨁ fun _ : Fin (n + m) ↦ M :=
  (biproductSumIso (fun _ : Fin n ↦ M) (fun _ : Fin m ↦ M)).symm ≪≫
    biproduct.whiskerEquiv (f := Sum.elim (fun _ : Fin n ↦ M) (fun _ : Fin m ↦ M))
      (g := fun _ : Fin (n + m) ↦ M) finSumFinEquiv fun j ↦ eqToIso (by cases j <;> rfl)

private theorem additiveClosure_biprod {X Y : C} (hX : additiveClosure M X)
    (hY : additiveClosure M Y) : additiveClosure M (X ⊞ Y) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  obtain ⟨m, ⟨e'⟩⟩ := hY
  exact ⟨n + m, ⟨Retract.trans { i := biprod.map e.i e'.i, r := biprod.map e.r e'.r }
    (biprodBiproductIso n m).retract⟩⟩

instance : (additiveClosure M).IsClosedUnderFiniteProducts :=
  have : (additiveClosure M).IsClosedUnderBinaryProducts :=
    ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ ↦ additiveClosure_biprod
  .mk'

end Biprod

/-- The additive closure of `M` is the smallest property of objects that holds for `M`, is stable
under retracts and is closed under finite products. -/
theorem additiveClosure_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts]
    [Q.IsClosedUnderFiniteProducts] : additiveClosure M ≤ Q ↔ Q M := by
  refine ⟨fun h ↦ h _ (additiveClosure_self M), fun hM X ⟨n, ⟨e⟩⟩ ↦ Q.prop_of_retract e ?_⟩
  exact Q.prop_of_isLimit (biproduct.isLimit _) fun _ ↦ hM

/-! ### `Hom(M, -)` is fully faithful on the additive closure -/

omit [HasFiniteBiproducts C] in
/-- For `X = M`, the Yoneda argument: a `Γᵐᵒᵖ`-linear map `φ : Hom(M, M) → Hom(M, Y)` is
composition with `φ (𝟙 M)`, since `φ f = φ (f • 𝟙 M) = f ≫ φ (𝟙 M)`. -/
private theorem preadditiveCoyonedaObj_map_bijective_self (Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj M).map : (M ⟶ Y) → _) := by
  -- The elements of `(preadditiveCoyonedaObj M).obj X` are the morphisms `M ⟶ X`, and
  -- `(preadditiveCoyonedaObj M).map g` acts on them by composition with `g`; both facts hold by
  -- definition, so the steps below are stated as equalities of morphisms of `C`.
  refine ⟨fun g g' h ↦ ?_, fun φ ↦ ⟨φ.hom (𝟙 M), ?_⟩⟩
  · exact (Category.id_comp g).symm.trans (congr(($h).hom (𝟙 M)).trans (Category.id_comp g'))
  · let ψ : (M ⟶ M) →ₗ[(End M)ᵐᵒᵖ] (M ⟶ Y) := φ.hom
    have key (f : M ⟶ M) : f ≫ ψ (𝟙 M) = ψ f :=
      calc f ≫ ψ (𝟙 M) = MulOpposite.op (End.of f) • ψ (𝟙 M) :=
            (End.smul_left (r := .op (.of f)) (f := ψ (𝟙 M))).symm
        _ = ψ (MulOpposite.op (End.of f) • 𝟙 M) := (ψ.map_smul _ _).symm
        _ = ψ f := congrArg ψ ((End.smul_left (r := .op (.of f)) (f := 𝟙 M)).trans
            (Category.comp_id f))
    ext f
    exact key f

/-- For `X` in the additive closure of `M`, composition identifies the morphisms `X ⟶ Y` with the
`Γᵐᵒᵖ`-linear maps `Hom(M, X) → Hom(M, Y)`, where `Γ = End M`. -/
theorem preadditiveCoyonedaObj_map_bijective {X : C} (hX : additiveClosure M X) (Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj M).map : (X ⟶ Y) → _) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  exact (preadditiveCoyonedaObj M).map_bijective_of_retract e
    ((preadditiveCoyonedaObj M).map_bijective_biproduct _ fun _ ↦
      preadditiveCoyonedaObj_map_bijective_self Y)

variable (M) in
/-- `Hom(M, -)` is fully faithful on the additive closure of `M`. -/
noncomputable def fullyFaithfulPreadditiveCoyonedaObj :
    ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).FullyFaithful where
  preimage {X Y} φ := ObjectProperty.homMk
    ((Equiv.ofBijective _ (preadditiveCoyonedaObj_map_bijective X.property Y.obj)).symm φ)
  map_preimage {X Y} φ :=
    (Equiv.ofBijective _ (preadditiveCoyonedaObj_map_bijective X.property Y.obj)).apply_symm_apply φ
  preimage_map {X Y} f := by
    ext1
    exact (Equiv.ofBijective _
      (preadditiveCoyonedaObj_map_bijective X.property Y.obj)).symm_apply_apply f.hom

instance : ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).Full :=
  (fullyFaithfulPreadditiveCoyonedaObj M).full

instance : ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).Faithful :=
  (fullyFaithfulPreadditiveCoyonedaObj M).faithful

/-! ### The image consists of the finitely generated projective modules -/

variable (M) in
/-- `Hom(M, Mⁿ)` is the free `Γᵐᵒᵖ`-module of rank `n`, where `Γ = End M`. -/
noncomputable def preadditiveCoyonedaObjBiproductIso (n : ℕ) :
    (preadditiveCoyonedaObj M).obj (⨁ fun _ : Fin n ↦ M) ≅
      ModuleCat.of (End M)ᵐᵒᵖ (Fin n → (End M)ᵐᵒᵖ) :=
  (preadditiveCoyonedaObj M).mapBiproduct _ ≪≫ ModuleCat.biproductIsoPi _ ≪≫
    (LinearEquiv.piCongrRight fun _ ↦
      Preadditive.homSelfLinearEquivEndMulOpposite M).toModuleIso

/-- For `X` in the additive closure of `M`, `Hom(M, X)` is a finitely generated projective
`Γᵐᵒᵖ`-module, where `Γ = End M`. -/
theorem finiteProjectiveModules_preadditiveCoyonedaObj_obj {X : C} (hX : additiveClosure M X) :
    finiteProjectiveModules (End M)ᵐᵒᵖ ((preadditiveCoyonedaObj M).obj X) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  refine (finiteProjectiveModules _).prop_of_retract (e.map _) ?_
  exact (finiteProjectiveModules _).prop_of_iso (preadditiveCoyonedaObjBiproductIso M n).symm
    (finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩)

/-- In an idempotent-complete category, every finitely generated projective `Γᵐᵒᵖ`-module is
isomorphic to `Hom(M, X)` for some `X` in the additive closure of `M`, where `Γ = End M`. -/
theorem finiteProjectiveModules_le_essImage [IsIdempotentComplete C] :
    finiteProjectiveModules (End M)ᵐᵒᵖ ≤
      ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).essImage := by
  intro P hP
  obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp hP
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (End M)ᵐᵒᵖ P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let r : Retract P (ModuleCat.of (End M)ᵐᵒᵖ (Fin n → (End M)ᵐᵒᵖ)) :=
    { i := ModuleCat.ofHom s
      r := ModuleCat.ofHom f
      retract := by ext x; exact congr($hs x) }
  exact ObjectProperty.prop_of_retract _
    (r.trans (preadditiveCoyonedaObjBiproductIso M n).symm.retract)
    ⟨⟨_, additiveClosure_biproduct n⟩, ⟨Iso.refl _⟩⟩

/-! ### Projectivization -/

variable (M) in
/-- `Hom(M, -)` on the additive closure of `M`, as a functor to the finitely generated projective
`Γᵐᵒᵖ`-modules, where `Γ = End M`. -/
noncomputable def projectivizationFunctor :
    (additiveClosure M).FullSubcategory ⥤ (finiteProjectiveModules (End M)ᵐᵒᵖ).FullSubcategory :=
  (finiteProjectiveModules (End M)ᵐᵒᵖ).lift ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M)
    fun X ↦ finiteProjectiveModules_preadditiveCoyonedaObj_obj X.property

@[simp]
theorem projectivizationFunctor_obj_obj (X : (additiveClosure M).FullSubcategory) :
    ((projectivizationFunctor M).obj X).obj = (preadditiveCoyonedaObj M).obj X.obj :=
  (rfl)

/-- `TauCeti.projectivizationFunctor M` followed by the inclusion of the finitely generated
projective modules is `Hom(M, -)` on the additive closure. -/
noncomputable def projectivizationFunctorCompιIso :
    projectivizationFunctor M ⋙ (finiteProjectiveModules (End M)ᵐᵒᵖ).ι ≅
      (additiveClosure M).ι ⋙ preadditiveCoyonedaObj M :=
  ObjectProperty.liftCompιIso _ _ _

instance : (projectivizationFunctor M).Full :=
  inferInstanceAs (ObjectProperty.lift _ _ _).Full

instance : (projectivizationFunctor M).Faithful :=
  inferInstanceAs (ObjectProperty.lift _ _ _).Faithful

/-- **Projectivization.** In an idempotent-complete preadditive category with finite biproducts,
`Hom(M, -)` is an equivalence between the additive closure `add M` and the finitely generated
projective `Γᵐᵒᵖ`-modules, that is the finitely generated projective right `Γ`-modules, where
`Γ = End M`. -/
instance [IsIdempotentComplete C] : (projectivizationFunctor M).IsEquivalence :=
  have : (projectivizationFunctor M).EssSurj :=
    (ObjectProperty.essSurj_lift_iff _ _ _).mpr finiteProjectiveModules_le_essImage
  { }

end TauCeti
