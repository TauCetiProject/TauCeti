/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.Functor.MapBijective
public import TauCeti.CategoryTheory.ObjectProperty.Retract
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure
public import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Projectivization

Let `C` be a preadditive category with finite biproducts, `M` an object of `C` and
`Γ = End M`. The **additive closure** `add M` (`TauCeti.additiveClosure M`, in
`TauCeti.CategoryTheory.Preadditive.AdditiveClosure`) consists of the direct summands of finite
biproducts `Mⁿ`. The functor `Hom(M, -)` takes values in right
`Γ`-modules, that is in `Γᵐᵒᵖ`-modules (Mathlib's `CategoryTheory.preadditiveCoyonedaObj M`), and
**projectivization** says that it identifies `add M` with the finitely generated projective right
`Γ`-modules:

* `Hom(M, -)` is fully faithful on `add M`
  (`TauCeti.fullyFaithfulPreadditiveCoyonedaObjAdditiveClosure`): for `X` in `add M`, every
  `Γ`-linear map `Hom(M, X) → Hom(M, Y)` is composition with a unique morphism `X ⟶ Y`
  (`TauCeti.preadditiveCoyonedaObj_map_bijective`). For `X = M` this is the Yoneda argument
  `φ(f) = φ(f ≫ 𝟙) = f ≫ φ(𝟙)` (`CategoryTheory.preadditiveCoyonedaObj_map_bijective_self`),
  and the general case follows by passing to finite biproducts
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

* `TauCeti.fullyFaithfulPreadditiveCoyonedaObjAdditiveClosure M`: `Hom(M, -)` is fully faithful
  on `add M`.
* `TauCeti.preadditiveCoyonedaObjBiproductIso M n`: `Hom(M, Mⁿ) ≅ Γᵐᵒᵖⁿ`.
* `TauCeti.projectivizationFunctor M`: `Hom(M, -)` from `add M` to the finitely generated
  projective `Γᵐᵒᵖ`-modules; it is an equivalence in an idempotent-complete category.

## Main results

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

variable {M : C}

/-! ### `Hom(M, -)` is fully faithful on the additive closure -/

/-- For `X` in the additive closure of `M`, composition identifies the morphisms `X ⟶ Y` with the
`Γᵐᵒᵖ`-linear maps `Hom(M, X) → Hom(M, Y)`, where `Γ = End M`. -/
theorem preadditiveCoyonedaObj_map_bijective {X : C} (hX : additiveClosure M X) (Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj M).map : (X ⟶ Y) → _) := by
  obtain ⟨n, ⟨e⟩⟩ := additiveClosure_iff.mp hX
  exact (preadditiveCoyonedaObj M).map_bijective_of_retract e
    ((preadditiveCoyonedaObj M).map_bijective_biproduct _ fun _ ↦
      preadditiveCoyonedaObj_map_bijective_self M Y)

instance : ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).Full where
  map_surjective {X Y} φ :=
    have ⟨g, hg⟩ := (preadditiveCoyonedaObj_map_bijective X.property Y.obj).2 φ
    ⟨ObjectProperty.homMk g, hg⟩

instance : ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).Faithful where
  map_injective {X Y} _ _ h :=
    ObjectProperty.hom_ext _ ((preadditiveCoyonedaObj_map_bijective X.property Y.obj).1 h)

variable (M) in
/-- `Hom(M, -)` is fully faithful on the additive closure of `M`. -/
noncomputable def fullyFaithfulPreadditiveCoyonedaObjAdditiveClosure :
    ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M).FullyFaithful :=
  .ofFullyFaithful _

/-! ### The image consists of the finitely generated projective modules -/

variable (M) in
/-- `Hom(M, Mⁿ)` is the free `Γᵐᵒᵖ`-module of rank `n`, where `Γ = End M`. -/
noncomputable def preadditiveCoyonedaObjBiproductIso (n : ℕ) :
    (preadditiveCoyonedaObj M).obj (⨁ fun _ : Fin n ↦ M) ≅
      ModuleCat.of (End M)ᵐᵒᵖ (Fin n → (End M)ᵐᵒᵖ) :=
  LinearEquiv.toModuleIso
    { toFun f j := Preadditive.homSelfLinearEquivEndMulOpposite M (f ≫ biproduct.π _ j)
      invFun v := biproduct.lift fun j ↦ (Preadditive.homSelfLinearEquivEndMulOpposite M).symm (v j)
      map_add' f g := funext fun j ↦ by
        simp only [Pi.add_apply, Preadditive.add_comp, map_add]
      map_smul' r f := funext fun j ↦ by
        have : (r • f) ≫ biproduct.π _ j = r • (f ≫ biproduct.π _ j) := by
          simp only [End.smul_left, Category.assoc]
        simp only [Pi.smul_apply, RingHom.id_apply, this, map_smul]
      left_inv f := by ext j; simp only [biproduct.lift_π, LinearEquiv.symm_apply_apply]
      right_inv v := funext fun j ↦ by simp only [biproduct.lift_π, LinearEquiv.apply_symm_apply] }

/- Mathlib's `@[simps]` lemmas for `Preadditive.homSelfLinearEquivEndMulOpposite` state it with
the raw `MulOpposite` constructor and a match on it, so `simp` cannot reach the `op`/`unop` forms
below. They hold by `rfl` because that equivalence is `f ↦ op (End.of f)` with inverse
`v ↦ v.unop.asHom` by definition. -/

/-- `TauCeti.preadditiveCoyonedaObjBiproductIso` sends `f : M ⟶ Mⁿ` to its components
`f ≫ biproduct.π _ j`, viewed in `Γᵐᵒᵖ`. -/
@[simp]
theorem preadditiveCoyonedaObjBiproductIso_hom_apply {n : ℕ} (f : M ⟶ ⨁ fun _ : Fin n ↦ M)
    (j : Fin n) :
    (preadditiveCoyonedaObjBiproductIso M n).hom.hom f j =
      MulOpposite.op (End.of (f ≫ biproduct.π _ j)) :=
  (rfl)

/-- The inverse of `TauCeti.preadditiveCoyonedaObjBiproductIso` sends a vector `v` of elements
of `Γᵐᵒᵖ` to the morphism `M ⟶ Mⁿ` with components `(v j).unop`. -/
@[simp]
theorem preadditiveCoyonedaObjBiproductIso_inv_apply {n : ℕ} (v : Fin n → (End M)ᵐᵒᵖ) :
    (preadditiveCoyonedaObjBiproductIso M n).inv.hom v =
      biproduct.lift fun j ↦ (v j).unop.asHom :=
  (rfl)

/-- For `X` in the additive closure of `M`, `Hom(M, X)` is a finitely generated projective
`Γᵐᵒᵖ`-module, where `Γ = End M`. -/
theorem finiteProjectiveModules_preadditiveCoyonedaObj_obj {X : C} (hX : additiveClosure M X) :
    finiteProjectiveModules (End M)ᵐᵒᵖ ((preadditiveCoyonedaObj M).obj X) := by
  obtain ⟨n, ⟨e⟩⟩ := additiveClosure_iff.mp hX
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
  obtain ⟨n, f, s, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective (End M)ᵐᵒᵖ P
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
@[expose] noncomputable def projectivizationFunctor :
    (additiveClosure M).FullSubcategory ⥤ (finiteProjectiveModules (End M)ᵐᵒᵖ).FullSubcategory :=
  (finiteProjectiveModules (End M)ᵐᵒᵖ).lift ((additiveClosure M).ι ⋙ preadditiveCoyonedaObj M)
    fun X ↦ finiteProjectiveModules_preadditiveCoyonedaObj_obj X.property

@[simp]
theorem projectivizationFunctor_obj_obj (X : (additiveClosure M).FullSubcategory) :
    ((projectivizationFunctor M).obj X).obj = (preadditiveCoyonedaObj M).obj X.obj :=
  (rfl)

@[simp]
theorem projectivizationFunctor_map_hom {X Y : (additiveClosure M).FullSubcategory} (f : X ⟶ Y) :
    ((projectivizationFunctor M).map f).hom = (preadditiveCoyonedaObj M).map f.hom :=
  (rfl)

/-- `TauCeti.projectivizationFunctor M` followed by the inclusion of the finitely generated
projective modules is `Hom(M, -)` on the additive closure. -/
noncomputable def projectivizationFunctorCompιIso :
    projectivizationFunctor M ⋙ (finiteProjectiveModules (End M)ᵐᵒᵖ).ι ≅
      (additiveClosure M).ι ⋙ preadditiveCoyonedaObj M :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem projectivizationFunctorCompιIso_hom_app (X : (additiveClosure M).FullSubcategory) :
    (projectivizationFunctorCompιIso (M := M)).hom.app X = 𝟙 _ :=
  (rfl)

@[simp]
theorem projectivizationFunctorCompιIso_inv_app (X : (additiveClosure M).FullSubcategory) :
    (projectivizationFunctorCompιIso (M := M)).inv.app X = 𝟙 _ :=
  (rfl)

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
