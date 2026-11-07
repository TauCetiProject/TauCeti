/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.RingTheory.Almost.Elements

/-!
# The symmetric monoidal structure on almost modules

For a basic setup `S = (V, m)`, almost isomorphisms of `V`-modules are stable under tensor
products: if `f` is an almost isomorphism, so are `X ⊗ f` and `f ⊗ X` for every `V`-module `X`
(Gabber–Ramero (2.2.5)). In the language of Mathlib, the morphism property
`S.almostZero.isoModSerre` of `ModuleCat V` is monoidal, so the category `Almost.Module S` of almost
`V`-modules inherits from `ModuleCat V` the localized symmetric monoidal structure, for which the
almostification functor `M ↦ M^a` is symmetric monoidal: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`, and the
tensor unit is `V^a`, which is isomorphic to `m^a` (Gabber–Ramero §2.2; Scholze, *Perfectoid
spaces*, §4). The tensor product of almost modules is additive, `V`-linear and right exact in each
variable.

The two adjoints of almostification interact with the tensor product as follows. The functor of
almost elements `M ↦ M_*`, right adjoint to the monoidal functor `M ↦ M^a`, is lax monoidal, with
comparison maps that are almost isomorphisms, and `M ⊗ N ≅ (M_* ⊗[V] N_*)^a`. The functor
`M ↦ M_!`, left adjoint to `M ↦ M^a`, is oplax monoidal, and its tensor comparison
`(M ⊗ N)_! → M_! ⊗[V] N_!` is an isomorphism, because `M_! ⊗[V] N_!` is firm. Its unit comparison
is `(V^a)_! ≅ m~ → V`, the multiplication map, which is an isomorphism only when `m = V`, so this
oplax monoidal structure is not strong unless the setup is classical.

## Main results

* `TauCeti.Almost.BasicSetup.isoModSerre_isMonoidal`: almost isomorphisms form a monoidal class of
  morphisms of `ModuleCat V`.
* `TauCeti.Almost.Module.instMonoidalCategory` and `TauCeti.Almost.Module.instSymmetricCategory`:
  the localized symmetric monoidal structure on `Almost.Module S`.
* `TauCeti.Almost.Module.toAlmostMonoidal` and `TauCeti.Almost.Module.toAlmostBraided`: the
  almostification functor is braided monoidal.
* `TauCeti.Almost.Module.instMonoidalPreadditive` and `TauCeti.Almost.Module.instMonoidalLinear`:
  the tensor product of almost modules is additive and `V`-linear in each variable.
* `TauCeti.Almost.Module.preservesFiniteColimits_tensorLeft` and
  `TauCeti.Almost.Module.preservesFiniteColimits_tensorRight`: the tensor product of almost modules
  is right exact in each variable.
* `TauCeti.Almost.Module.elementsLaxMonoidal`: almost elements form a lax monoidal functor, with
  comparison maps described by `TauCeti.Almost.Module.elements_ε_hom_apply_one` and
  `TauCeti.Almost.Module.elements_μ_hom_tmul`; they are almost isomorphisms
  (`TauCeti.Almost.Module.isAlmostIso_elements_ε`, `TauCeti.Almost.Module.isAlmostIso_elements_μ`).
* `TauCeti.Almost.Module.tensorIsoElements`: `M ⊗ N ≅ (M_* ⊗[V] N_*)^a`.
* `TauCeti.Almost.Module.shriekOplaxMonoidal` and `TauCeti.Almost.Module.shriekTensorIso`: the
  functor `M ↦ M_!` is oplax monoidal, and `(M ⊗ N)_! ≅ M_! ⊗[V] N_!`.
* `TauCeti.Almost.Module.shriek_η` and `TauCeti.Almost.Module.isIso_shriek_η_iff`: the unit
  comparison `(V^a)_! → V` is the multiplication `m~ → V`, an isomorphism exactly when `m = V`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.5)
  and (2.2.11).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Proposition 4.5.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

namespace BasicSetup

/-- **Almost isomorphisms are monoidal** (Gabber–Ramero (2.2.5)): they are stable under
composition and under tensoring with any `V`-module on either side. This is what equips the
category of almost modules with the localized monoidal structure. -/
instance isoModSerre_isMonoidal :
    (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.IsMonoidal where
  whiskerLeft X _ _ g hg := by
    rw [← isAlmostIso_iff_isoModSerre] at hg ⊢
    exact hg.lTensor X
  whiskerRight f hf Y := by
    rw [← isAlmostIso_iff_isoModSerre] at hf ⊢
    exact hf.rTensor Y

end BasicSetup

namespace Module

/-- The **monoidal structure on almost modules**, localized from the tensor product of
`V`-modules: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`, with unit `V^a`. -/
noncomputable instance instMonoidalCategory : MonoidalCategory (Module S) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)))

/-- The tensor product of almost modules is symmetric, with braiding localized from that of
`V`-modules. -/
noncomputable instance instSymmetricCategory : SymmetricCategory (Module S) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)))

/-- **Almostification is a monoidal functor**: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a` and `𝟙_ ≅ V^a`. -/
noncomputable instance toAlmostMonoidal : (toAlmost S).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)).Monoidal

/-- Almostification is a braided monoidal functor. -/
noncomputable instance toAlmostBraided : (toAlmost S).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)).Braided

variable {S} in
/-- Every almost module `X` is some `M^a`, and almostification intertwines tensoring on the left
with `M^a` and tensoring on the left with `M`. -/
private noncomputable def tensorLeftIso (X : Module S) :
    toAlmost S ⋙ tensorLeft X ≅ tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S :=
  Functor.isoWhiskerLeft _ ((tensoringLeft _).mapIso ((toAlmost S).objObjPreimageIso X)).symm ≪≫
    Functor.Monoidal.commTensorLeft (toAlmost S) _

/-- Tensoring on the left with an almost module is additive. -/
instance tensorLeft_additive (X : Module S) : (tensorLeft X).Additive :=
  (Localization.functor_additive_iff (toAlmost S) S.almostZero.isoModSerre _).mpr
    (Functor.additive_of_iso (tensorLeftIso X).symm)

/-- Tensoring on the left with an almost module is `V`-linear. -/
instance tensorLeft_linear (X : Module S) : (tensorLeft X).Linear V :=
  letI : Localization.Lifting (toAlmost S) S.almostZero.isoModSerre
      (tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S) (tensorLeft X) :=
    ⟨tensorLeftIso X⟩
  (Localization.functor_linear_iff (toAlmost S) S.almostZero.isoModSerre V
    (tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S) _).mp inferInstance

/-- **Tensoring on the left with an almost module is right exact.** -/
instance preservesFiniteColimits_tensorLeft (X : Module S) :
    PreservesFiniteColimits (tensorLeft X) :=
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff (toAlmost S)
    S.almostZero _).mp (preservesFiniteColimits_of_natIso (tensorLeftIso X).symm)

/-- Tensoring on the right with an almost module is additive. -/
instance tensorRight_additive (X : Module S) : (tensorRight X).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- Tensoring on the right with an almost module is `V`-linear. -/
instance tensorRight_linear (X : Module S) : (tensorRight X).Linear V :=
  Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight X)

/-- **Tensoring on the right with an almost module is right exact.** -/
instance preservesFiniteColimits_tensorRight (X : Module S) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The tensor product of almost modules is additive in each variable. -/
instance instMonoidalPreadditive : MonoidalPreadditive (Module S) where
  whiskerLeft_zero {X _ _} := (tensorLeft X).map_zero _ _
  zero_whiskerRight {X _ _} := (tensorRight X).map_zero _ _
  whiskerLeft_add {X _ _} f g := (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight {X _ _} f g := (tensorRight X).map_add (f := f) (g := g)

/-- The tensor product of almost modules is `V`-linear in each variable. -/
instance instMonoidalLinear : MonoidalLinear V (Module S) where
  whiskerLeft_smul X _ _ r f := (tensorLeft X).map_smul r f
  smul_whiskerRight r _ _ f X := (tensorRight X).map_smul r f

/-! ### Almost elements and the left adjoint `M ↦ M_!` -/

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- **Almost elements form a lax monoidal functor**: as the right adjoint of the monoidal functor
`M ↦ M^a`, the functor `M ↦ M_*` carries comparison maps `V → (𝟙_)_*` and
`M_* ⊗[V] N_* → (M ⊗ N)_*` (`elements_ε_hom_apply_one`, `elements_μ_hom_tmul`), which are almost
isomorphisms (`isAlmostIso_elements_ε`, `isAlmostIso_elements_μ`). -/
noncomputable instance elementsLaxMonoidal : (elements S).LaxMonoidal :=
  (adjElements S).rightAdjointLaxMonoidal

/-- The unit comparison `V → (𝟙_)_*` of almost elements sends `1` to the almost element
`V^a → 𝟙_` given by the monoidal structure of `M ↦ M^a`. -/
theorem elements_ε_hom_apply_one : (ε (elements S)).hom (1 : V) = η (toAlmost S) := by
  rw [elementsLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_ε,
    adjElements_homEquiv_apply_hom_apply]
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V V 1) = 𝟙 (ModuleCat.of V V) := by
    ext
    simp
  have h' : (toAlmost S).map (𝟙 (ModuleCat.of V V)) ≫ η (toAlmost S) = η (toAlmost S) := by
    rw [(toAlmost S).map_id, Category.id_comp]
  exact (congrArg (fun f ↦ (toAlmost S).map f ≫ η (toAlmost S)) h).trans h'

/-- The tensor comparison `M_* ⊗[V] N_* → (M ⊗ N)_*` of almost elements sends `x ⊗ y` to the
almost element `V^a ≅ V^a ⊗ V^a → M ⊗ N` given by `x ⊗ y`. -/
theorem elements_μ_hom_tmul (M N : Module S) (x : (toAlmost S).obj (ModuleCat.of V V) ⟶ M)
    (y : (toAlmost S).obj (ModuleCat.of V V) ⟶ N) :
    (μ (elements S) M N).hom (x ⊗ₜ[V] y) =
      (λ_ ((toAlmost S).obj (𝟙_ (ModuleCat.{u} V)))).inv ≫ ε (toAlmost S) ▷ _ ≫ (x ⊗ₘ y) := by
  rw [elementsLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_μ,
    adjElements_homEquiv_apply_hom_apply]
  -- `1 ↦ x ⊗ y` is `1 ↦ 1 ⊗ 1` followed by the tensor product of `1 ↦ x` and `1 ↦ y`.
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V
      ↑((elements S).obj M ⊗ (elements S).obj N) (x ⊗ₜ[V] y)) =
      (λ_ (𝟙_ (ModuleCat.{u} V))).inv ≫
        (ModuleCat.ofHom (LinearMap.toSpanSingleton V ((elements S).obj M) x) ⊗ₘ
          ModuleCat.ofHom (LinearMap.toSpanSingleton V ((elements S).obj N) y)) := by
    ext : 1
    refine LinearMap.ext_ring ?_
    -- Both sides evaluate at `1` to `1 • (x ⊗ y)` and `(1 • x) ⊗ (1 • y)` respectively.
    exact (by simp : (1 : V) • (x ⊗ₜ[V] y) = ((1 : V) • x) ⊗ₜ[V] ((1 : V) • y))
  -- The goal is an equation of elements of `(M ⊗ N)_*`; `key` states it as one of morphisms.
  have key : (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V
      ↑((elements S).obj M ⊗ (elements S).obj N) (x ⊗ₜ[V] y))) ≫
      δ (toAlmost S) _ _ ≫ ((adjElements S).counit.app M ⊗ₘ (adjElements S).counit.app N) =
      (λ_ ((toAlmost S).obj (𝟙_ (ModuleCat.{u} V)))).inv ≫ ε (toAlmost S) ▷ _ ≫ (x ⊗ₘ y) := by
    rw [h, Functor.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_assoc,
      tensorHom_comp_tensorHom]
    simp
  exact key

/-- **The tensor product through almost elements**: `M ⊗ N ≅ (M_* ⊗[V] N_*)^a` (Scholze,
*Perfectoid spaces*, Proposition 4.5). Its inverse is the almostification of the tensor comparison
`M_* ⊗[V] N_* → (M ⊗ N)_*` followed by the counit `((M ⊗ N)_*)^a ≅ M ⊗ N`
(`tensorIsoElements_inv`). -/
noncomputable def tensorIsoElements (M N : Module S) :
    M ⊗ N ≅ (toAlmost S).obj ((elements S).obj M ⊗ (elements S).obj N) :=
  (asIso ((adjElements S).counit.app M) ⊗ᵢ asIso ((adjElements S).counit.app N)).symm ≪≫
    Functor.Monoidal.μIso (toAlmost S) _ _

/-- The inverse of `M ⊗ N ≅ (M_* ⊗[V] N_*)^a` is the almostification of the tensor comparison of
almost elements followed by the counit. -/
theorem tensorIsoElements_inv (M N : Module S) :
    (tensorIsoElements S M N).inv =
      (toAlmost S).map (μ (elements S) M N) ≫ (adjElements S).counit.app (M ⊗ N) := by
  rw [Adjunction.map_μ_comp_counit_app_tensor]
  simp [tensorIsoElements]

/-- The unit comparison `V → (𝟙_)_*` of almost elements is an almost isomorphism. -/
theorem isAlmostIso_elements_ε : S.IsAlmostIso (ε (elements S)).hom := by
  have := (isIso_toAlmost_map_iff S _).mpr (isAlmostIso_adjElements_unit_app S (𝟙_ _))
  rw [← isIso_toAlmost_map_iff, ← Adjunction.unit_app_unit_comp_map_η (adjElements S),
    Functor.map_comp]
  infer_instance

/-- The tensor comparison `M_* ⊗[V] N_* → (M ⊗ N)_*` of almost elements is an almost
isomorphism. -/
theorem isAlmostIso_elements_μ (M N : Module S) : S.IsAlmostIso (μ (elements S) M N).hom := by
  rw [← isIso_toAlmost_map_iff]
  have : IsIso ((toAlmost S).map (μ (elements S) M N) ≫ (adjElements S).counit.app (M ⊗ N)) := by
    rw [← tensorIsoElements_inv]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adjElements S).counit.app (M ⊗ N))

/-- **`M ↦ M_!` is oplax monoidal**, as the left adjoint of the monoidal functor `M ↦ M^a`
(Gabber–Ramero, (2.2.20)–(2.2.24)). Its tensor comparison `(M ⊗ N)_! → M_! ⊗[V] N_!` is an
isomorphism (`shriekTensorIso`), but its unit comparison `(𝟙_)_! → V` is the multiplication map
`m~ → V` (`shriek_η`), an isomorphism only for the classical setup (`isIso_shriek_η_iff`). -/
noncomputable instance shriekOplaxMonoidal : (shriek S).OplaxMonoidal :=
  (adjShriek S).leftAdjointOplaxMonoidal

/-- The tensor comparison `(M ⊗ N)_! → M_! ⊗[V] N_!` is an isomorphism: it is the counit
`((M_! ⊗[V] N_!)^a)_! → M_! ⊗[V] N_!` up to isomorphism, and `M_! ⊗[V] N_!` is firm. -/
instance isIso_shriek_δ (M N : Module S) : IsIso (δ (shriek S) M N) := by
  have : IsIso ((adjShriek S).counit.app ((shriek S).obj M ⊗ (shriek S).obj N)) :=
    (isIso_adjShriek_counit_app_iff S _).mpr
      (((S.isFirm_iff _).mp (isFirm_shriek_obj S N)).tensorProduct _)
  rw [shriekOplaxMonoidal, Adjunction.leftAdjointOplaxMonoidal_δ, Adjunction.homEquiv_counit]
  infer_instance

/-- **`M ↦ M_!` preserves tensor products**: `(M ⊗ N)_! ≅ M_! ⊗[V] N_!`, through the tensor
comparison of its oplax monoidal structure (Gabber–Ramero, §2.2; Bhatt, Proposition 4.1.7). -/
noncomputable def shriekTensorIso (M N : Module S) :
    (shriek S).obj (M ⊗ N) ≅ (shriek S).obj M ⊗ (shriek S).obj N :=
  asIso (δ (shriek S) M N)

@[simp]
theorem shriekTensorIso_hom (M N : Module S) : (shriekTensorIso S M N).hom = δ (shriek S) M N :=
  (rfl)

/-- The unit comparison `(𝟙_)_! → V` of `M ↦ M_!` is, under the isomorphism
`(𝟙_)_! ≅ (V^a)_! ≅ m~ ⊗[V] V`, the action map `m~ ⊗[V] V → V`, `t ⊗ r ↦ tildeMul t * r`, that
is, the multiplication map `m~ → V` after `m~ ⊗[V] V ≅ m~`. -/
theorem shriek_η : η (shriek S) = (shriek S).map (ε (toAlmost S)) ≫
    (toAlmostCompShriekIso S).hom.app (𝟙_ _) ≫
      ModuleCat.ofHom (S.tildeAct (𝟙_ (ModuleCat.{u} V))) := by
  rw [shriekOplaxMonoidal, Adjunction.leftAdjointOplaxMonoidal_η, Adjunction.homEquiv_counit,
    adjShriek_counit_app]

/-- The unit comparison `(𝟙_)_! → V` of `M ↦ M_!` is an isomorphism exactly for the classical
setup `m = V`. -/
theorem isIso_shriek_η_iff : IsIso (η (shriek S)) ↔ S.ideal = ⊤ := by
  rw [shriekOplaxMonoidal, Adjunction.leftAdjointOplaxMonoidal_η, Adjunction.homEquiv_counit,
    isIso_comp_left_iff, isIso_adjShriek_counit_app_iff]
  exact S.isFirm_self_iff

end Module

end TauCeti.Almost
