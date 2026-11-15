/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.ProjectiveCover

/-!
# Right almost split morphisms and simple functors

Let `C` be a preadditive category and `Z` an object with a local endomorphism ring. In Auslander's
functorial picture, the maps into `Z` that are not split epimorphisms form the *radical functor*
`rad(-, Z)`, the unique maximal subfunctor of the representable functor `(-, Z)`, with simple
quotient `S_Z = (-, Z) / rad(-, Z)`. So a morphism `g : Y ⟶ Z` absorbs all these maps exactly when
`(-, g)` has image `rad(-, Z)`. This translates existence questions for almost-split maps into
finiteness questions for the functor `S_Z`.

* **Right almost split maps.** `g : Y ⟶ Z` is right almost split exactly when the image of `(-, g)`
  is `rad(-, Z)`, equivalently when `(-, Y) ⟶ (-, Z) ⟶ S_Z ⟶ 0` is exact, so that `g` is the start
  of a projective presentation of `S_Z`.
* **Minimality.** `g` is moreover right minimal exactly when `(-, Y) ⟶ rad(-, Z)` is a projective
  cover.
* **Finiteness.** `Z` ends a right almost split morphism exactly when `rad(-, Z)` is finitely
  generated, and exactly when `S_Z` is finitely presented. The functor `rad(-, Z)` need not itself
  be finitely presented, as `C` need not have weak kernels. In a Krull-Schmidt category such a `Z`
  also ends a right minimal right almost split morphism.
* **Simple functors.** A simple quotient of `(-, Z)` is isomorphic to `S_Z`. Hence in a
  Krull-Schmidt category the finitely generated simple functors are exactly the functors `S_Z`
  with `End Z` local, and the finitely presented ones are those with `S_Z` finitely presented.

In a Krull-Schmidt category the objects with local endomorphism ring are the indecomposable ones
(`TauCeti.IsKrullSchmidt.indecomposable_iff_isLocalRing_end`).

## Main definitions

* `TauCeti.radicalFunctor Z`: the subfunctor `rad(-, Z)` of `(-, Z)`, with its inclusion
  `TauCeti.radicalFunctorι Z`.
* `TauCeti.radicalFunctorLift g hg`: the map `(-, Y) ⟶ rad(-, Z)` induced by a radical morphism
  `g : Y ⟶ Z`.
* `TauCeti.simpleFunctor Z`: the quotient `S_Z = (-, Z) / rad(-, Z)`, with its projection
  `TauCeti.simpleFunctorπ Z`.

## Main results

* `TauCeti.shortExact_radicalFunctor`: the sequence `0 ⟶ rad(-, Z) ⟶ (-, Z) ⟶ S_Z ⟶ 0` is exact.
* `TauCeti.isRightAlmostSplit_iff_exists_epi_radicalFunctorLift` and
  `TauCeti.isRightAlmostSplit_iff_exists_exact_simpleFunctorπ`: right almost split morphisms in
  terms of `rad(-, Z)` and of `S_Z`.
* `TauCeti.isRepresentableProjectiveCover_radicalFunctorLift_iff`: right minimal right almost split
  morphisms are the projective covers of `rad(-, Z)`.
* `TauCeti.isFinitelyGeneratedFunctor_radicalFunctor_iff` and
  `TauCeti.isFinitelyPresentedFunctor_simpleFunctor_iff`: the two finiteness criteria.
* `TauCeti.IsKrullSchmidt.exists_isRightAlmostSplit_and_minimal`: existence of minimal right almost
  split morphisms in a Krull-Schmidt category.
* `TauCeti.exists_iso_simpleFunctor_of_epi`: a simple quotient of `(-, Z)` is `S_Z`, and
  `TauCeti.IsKrullSchmidt.simple_and_isFinitelyPresentedFunctor_iff` the classification of finitely
  presented simple functors.

## References

* Haruhisa Enomoto, *Classifications of exact structures and Cohen-Macaulay-finite algebras*,
  Adv. Math. 335 (2018), 838–877, Proposition A.2.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), Theorem IV.6.11.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### The radical functor and the simple functor -/

/-- The **radical functor** `rad(-, Z)`: the subfunctor of `(-, Z)` whose value at `W` is the
subgroup `jacobsonRadical W Z` of the morphisms `W ⟶ Z`. -/
@[expose] def radicalFunctor (Z : C) : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj W := .of (jacobsonRadical W.unop Z)
  map k := AddCommGrpCat.ofHom (((Preadditive.leftComp Z k.unop).comp
    (jacobsonRadical _ Z).subtype).codRestrict _ fun h ↦ comp_mem_jacobsonRadical_left k.unop h.2)
  map_id _ := AddCommGrpCat.ext fun h ↦ Subtype.ext (Category.id_comp h.1)
  map_comp _ _ := AddCommGrpCat.ext fun h ↦ Subtype.ext (Category.assoc _ _ h.1)

/-- The inclusion `rad(-, Z) ⟶ (-, Z)`. -/
def radicalFunctorι (Z : C) : radicalFunctor Z ⟶ preadditiveYoneda.obj Z where
  app W := AddCommGrpCat.ofHom (jacobsonRadical W.unop Z).subtype
  naturality _ _ _ := rfl

/-- The functor `rad(-, Z)` acts on morphisms by precomposition. -/
@[simp]
theorem radicalFunctor_map_apply (Z : C) {W W' : Cᵒᵖ} (k : W ⟶ W') (h : jacobsonRadical W.unop Z) :
    (radicalFunctor Z).map k h = ⟨k.unop ≫ h.1, comp_mem_jacobsonRadical_left k.unop h.2⟩ :=
  rfl

/-- The inclusion `rad(-, Z) ⟶ (-, Z)` sends a radical morphism to itself. -/
@[simp]
theorem radicalFunctorι_app_apply (Z : C) (W : Cᵒᵖ) (h : jacobsonRadical W.unop Z) :
    (radicalFunctorι Z).app W h = h.1 :=
  (rfl)

instance (Z : C) : Mono (radicalFunctorι Z) := by
  have (W : Cᵒᵖ) : Mono ((radicalFunctorι Z).app W) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

/-- A radical morphism `g : Y ⟶ Z` induces `(-, Y) ⟶ rad(-, Z)`, sending `u` to `u ≫ g`. -/
def radicalFunctorLift {Y Z : C} (g : Y ⟶ Z) (hg : g ∈ jacobsonRadical Y Z) :
    preadditiveYoneda.obj Y ⟶ radicalFunctor Z where
  app W := AddCommGrpCat.ofHom ((Preadditive.rightComp W.unop g).codRestrict _ fun u ↦
    comp_mem_jacobsonRadical_left u hg)
  naturality _ _ _ := AddCommGrpCat.ext fun u ↦ Subtype.ext (Category.assoc _ u g)

/-- The map `(-, Y) ⟶ rad(-, Z)` induced by `g` is `(-, g)` corestricted to `rad(-, Z)`. -/
@[reassoc (attr := simp)]
theorem radicalFunctorLift_comp_ι {Y Z : C} (g : Y ⟶ Z) (hg : g ∈ jacobsonRadical Y Z) :
    radicalFunctorLift g hg ≫ radicalFunctorι Z = preadditiveYoneda.map g :=
  (rfl)

/-- The map `(-, Y) ⟶ rad(-, Z)` induced by `g` sends `u` to `u ≫ g`. -/
@[simp]
theorem radicalFunctorLift_app_apply {Y Z : C} (g : Y ⟶ Z) (hg : g ∈ jacobsonRadical Y Z)
    (W : Cᵒᵖ) (u : W.unop ⟶ Y) :
    (radicalFunctorLift g hg).app W u = ⟨u ≫ g, comp_mem_jacobsonRadical_left u hg⟩ :=
  (rfl)

/-- Every morphism `(-, Y) ⟶ rad(-, Z)` is induced by a radical morphism `Y ⟶ Z`. -/
theorem exists_eq_radicalFunctorLift {Y Z : C} (p : preadditiveYoneda.obj Y ⟶ radicalFunctor Z) :
    ∃ (g : Y ⟶ Z) (hg : g ∈ jacobsonRadical Y Z), p = radicalFunctorLift g hg := by
  -- By the Yoneda lemma `p` is determined by the image of `𝟙 Y`, a radical morphism `Y ⟶ Z`.
  let g : jacobsonRadical Y Z := p.app (op Y) (𝟙 Y)
  refine ⟨g.1, g.2, preadditiveYoneda_obj_hom_ext (Subtype.ext ?_)⟩
  exact (Category.id_comp g.1).symm

/-- The **simple functor** `S_Z = (-, Z) / rad(-, Z)`, read as the functor
`W ↦ Hom_{C/rad}(W, Z)` of the quotient of `C` by its radical. It is simple when `End Z` is local
(`TauCeti.simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal`). -/
noncomputable abbrev simpleFunctor (Z : C) : Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (jacobsonRadicalIdeal C).quotientFunctor.op ⋙
    preadditiveYoneda.obj ((jacobsonRadicalIdeal C).quotientFunctor.obj Z)

/-- The projection `(-, Z) ⟶ S_Z`. It is a projective cover
(`TauCeti.isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal`). -/
noncomputable abbrev simpleFunctorπ (Z : C) : preadditiveYoneda.obj Z ⟶ simpleFunctor Z :=
  preadditiveYonedaMap (jacobsonRadicalIdeal C).quotientFunctor Z

/-- The projection `(-, Z) ⟶ S_Z` kills `h : W ⟶ Z` exactly when `h` is radical. -/
theorem simpleFunctorπ_app_eq_zero_iff {Z W : C} (h : W ⟶ Z) :
    (simpleFunctorπ Z).app (op W) h = 0 ↔ h ∈ jacobsonRadical W Z :=
  -- `(-, Z) ⟶ S_Z` applies the quotient functor (`preadditiveYonedaMap_app_apply`), but `rw` cannot
  -- see this through the carrier of `S_Z`.
  ((jacobsonRadicalIdeal C).quotientFunctor_map_eq_zero_iff (f := h)).trans
    (by rw [jacobsonRadicalIdeal_hom])

/-- The projection `(-, Z) ⟶ S_Z` kills `(-, g)` exactly when `g` is radical. -/
theorem preadditiveYoneda_map_comp_simpleFunctorπ_eq_zero_iff {Y Z : C} (g : Y ⟶ Z) :
    preadditiveYoneda.map g ≫ simpleFunctorπ Z = 0 ↔ g ∈ jacobsonRadical Y Z := by
  rw [preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff,
    MorphismIdeal.quotientFunctor_map_eq_zero_iff, jacobsonRadicalIdeal_hom]

/-- The composite `rad(-, Z) ⟶ (-, Z) ⟶ S_Z` is zero. -/
@[reassoc (attr := simp)]
theorem radicalFunctorι_comp_simpleFunctorπ (Z : C) :
    radicalFunctorι Z ≫ simpleFunctorπ Z = 0 := by
  ext W ⟨h, hh⟩
  exact (simpleFunctorπ_app_eq_zero_iff h).2 hh

/-- **The defining sequence of the simple functor.** `0 ⟶ rad(-, Z) ⟶ (-, Z) ⟶ S_Z ⟶ 0` is
exact. -/
theorem shortExact_radicalFunctor (Z : C) :
    (ShortComplex.mk _ _ (radicalFunctorι_comp_simpleFunctorπ Z)).ShortExact where
  exact := by
    refine ShortComplex.exact_of_forall_evaluation _ fun V ↦ ?_
    -- An element of `(-, Z)` at `V` is a morphism `V.unop ⟶ Z`.
    refine (ShortComplex.ab_exact_iff _).2 fun (h : V.unop ⟶ Z) hh ↦ ?_
    exact ⟨⟨h, (simpleFunctorπ_app_eq_zero_iff h).1 hh⟩, rfl⟩
  mono_f := inferInstanceAs (Mono (radicalFunctorι Z))
  epi_g := inferInstanceAs (Epi (simpleFunctorπ Z))

/-! ### Right almost split morphisms -/

section RightAlmostSplit

variable {Y Z : C} {g : Y ⟶ Z}

/-- The map `(-, Y) ⟶ rad(-, Z)` induced by a radical `g` is an epimorphism exactly when every
radical morphism into `Z` factors through `g`. -/
theorem epi_radicalFunctorLift_iff (hg : g ∈ jacobsonRadical Y Z) :
    Epi (radicalFunctorLift g hg) ↔
      ∀ ⦃W : C⦄ (h : W ⟶ Z), h ∈ jacobsonRadical W Z → ∃ u : W ⟶ Y, u ≫ g = h := by
  constructor
  · intro _ W h hh
    obtain ⟨u, hu⟩ := (AddCommGrpCat.epi_iff_surjective ((radicalFunctorLift g hg).app (op W))).1
      inferInstance ⟨h, hh⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · intro H
    have (W : Cᵒᵖ) : Epi ((radicalFunctorLift g hg).app W) := by
      refine (AddCommGrpCat.epi_iff_surjective _).2 fun ⟨h, hh⟩ ↦ ?_
      obtain ⟨u, hu⟩ := H h hh
      exact ⟨u, Subtype.ext hu⟩
    exact NatTrans.epi_of_epi_app _

/-- **Right almost split morphisms and the radical functor.** If `End Z` is local, then
`g : Y ⟶ Z` is right almost split exactly when the image of `(-, g)` is `rad(-, Z)`: it is radical
and `(-, Y) ⟶ rad(-, Z)` is an epimorphism. -/
theorem isRightAlmostSplit_iff_exists_epi_radicalFunctorLift [IsLocalRing (End Z)] :
    IsRightAlmostSplit g ↔
      ∃ hg : g ∈ jacobsonRadical Y Z, Epi (radicalFunctorLift g hg) := by
  simp only [epi_radicalFunctorLift_iff, isRightAlmostSplit_iff_mem_jacobsonRadical_and_forall,
    exists_prop]

/-- **Right almost split morphisms and the simple functor.** If `End Z` is local, then
`g : Y ⟶ Z` is right almost split exactly when `(-, Y) ⟶ (-, Z) ⟶ S_Z ⟶ 0` is exact. -/
theorem isRightAlmostSplit_iff_exists_exact_simpleFunctorπ [IsLocalRing (End Z)] :
    IsRightAlmostSplit g ↔
      ∃ h : preadditiveYoneda.map g ≫ simpleFunctorπ Z = 0, (ShortComplex.mk _ _ h).Exact := by
  simp only [exact_preadditiveYoneda_map_iff, simpleFunctorπ_app_eq_zero_iff,
    preadditiveYoneda_map_comp_simpleFunctorπ_eq_zero_iff,
    isRightAlmostSplit_iff_mem_jacobsonRadical_and_forall, exists_prop]

/-- **Minimal right almost split morphisms are projective covers of the radical functor.** If
`End Z` is local and `g : Y ⟶ Z` is radical, then `(-, Y) ⟶ rad(-, Z)` is a projective cover
exactly when `g` is right almost split and right minimal. -/
theorem isRepresentableProjectiveCover_radicalFunctorLift_iff [IsLocalRing (End Z)]
    (hg : g ∈ jacobsonRadical Y Z) :
    IsRepresentableProjectiveCover (radicalFunctorLift g hg) ↔
      IsRightAlmostSplit g ∧ ∀ φ : Y ⟶ Y, φ ≫ g = g → IsIso φ := by
  have hcomp (φ : Y ⟶ Y) :
      preadditiveYoneda.map φ ≫ radicalFunctorLift g hg = radicalFunctorLift g hg ↔ φ ≫ g = g := by
    rw [← cancel_mono (radicalFunctorι Z), Category.assoc, radicalFunctorLift_comp_ι,
      ← Functor.map_comp]
    exact preadditiveYoneda.map_injective.eq_iff
  constructor
  · rintro ⟨hepi, hmin⟩
    exact ⟨isRightAlmostSplit_iff_exists_epi_radicalFunctorLift.2 ⟨hg, hepi⟩,
      fun φ hφ ↦ hmin φ ((hcomp φ).2 hφ)⟩
  · rintro ⟨hrs, hmin⟩
    obtain ⟨_, hepi⟩ := isRightAlmostSplit_iff_exists_epi_radicalFunctorLift.1 hrs
    exact ⟨hepi, fun φ hφ ↦ hmin φ ((hcomp φ).1 hφ)⟩

/-- A monomorphic right almost split morphism is right minimal, so `(-, Y) ⟶ rad(-, Z)` is then a
projective cover. This is the shape of the inclusion of the radical of an indecomposable projective
module. -/
theorem IsRightAlmostSplit.isRepresentableProjectiveCover_radicalFunctorLift [Mono g]
    (hrs : IsRightAlmostSplit g) :
    IsRepresentableProjectiveCover (radicalFunctorLift g hrs.mem_jacobsonRadical) :=
  have := hrs.isLocalRing_end
  (isRepresentableProjectiveCover_radicalFunctorLift_iff _).2 ⟨hrs, fun φ hφ ↦ by
    rw [(cancel_mono g).1 (hφ.trans (Category.id_comp g).symm)]
    infer_instance⟩

end RightAlmostSplit

/-! ### Finiteness of the radical functor and the simple functor -/

section Finiteness

variable (Z : C) [IsLocalRing (End Z)]

/-- `Z` ends a right almost split morphism exactly when `rad(-, Z)` is finitely generated. -/
theorem isFinitelyGeneratedFunctor_radicalFunctor_iff :
    IsFinitelyGeneratedFunctor (radicalFunctor Z) ↔
      ∃ (Y : C) (g : Y ⟶ Z), IsRightAlmostSplit g := by
  rw [isFinitelyGeneratedFunctor_def]
  constructor
  · rintro ⟨Y, p, hp⟩
    obtain ⟨g, hg, rfl⟩ := exists_eq_radicalFunctorLift p
    exact ⟨Y, g, isRightAlmostSplit_iff_exists_epi_radicalFunctorLift.2 ⟨hg, hp⟩⟩
  · rintro ⟨Y, g, hrs⟩
    obtain ⟨hg, hepi⟩ := isRightAlmostSplit_iff_exists_epi_radicalFunctorLift.1 hrs
    exact ⟨Y, _, hepi⟩

/-- **The finite presentation criterion.** `Z` ends a right almost split morphism exactly when the
simple functor `S_Z` is finitely presented. -/
theorem isFinitelyPresentedFunctor_simpleFunctor_iff :
    IsFinitelyPresentedFunctor (simpleFunctor Z) ↔
      ∃ (Y : C) (g : Y ⟶ Z), IsRightAlmostSplit g := by
  rw [isFinitelyPresentedFunctor_iff_exists_isColimit]
  constructor
  · -- Given a presentation `(-, X) ⟶ (-, Y') ⟶ S_Z ⟶ 0`, the projective cover `(-, Z) ⟶ S_Z` is a
    -- retract of `(-, Y') ⟶ S_Z`, along `u : Y' ⟶ Z`; the composite `X ⟶ Y' ⟶ Z` is the sought map.
    rintro ⟨X, Y', f, q, h, ⟨hc⟩⟩
    have : Epi q := Cofork.IsColimit.epi hc
    have hS := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _ h) hc
    obtain ⟨u, rfl, hsplit⟩ :=
      (isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal
        Z).exists_comp_eq_and_isSplitEpi q
    rw [exact_preadditiveYoneda_map_iff] at hS
    refine ⟨X, f ≫ u, isRightAlmostSplit_iff_exists_exact_simpleFunctorπ.2 ⟨?_, ?_⟩⟩
    · rw [Functor.map_comp, Category.assoc, h]
    · rw [exact_preadditiveYoneda_map_iff]
      intro V k hk
      have hsu : (k ≫ section_ u) ≫ u = k := by simp
      obtain ⟨w, hw⟩ := hS (k ≫ section_ u)
        ((congrArg ((simpleFunctorπ Z).app (op V)) hsu).trans hk)
      exact ⟨w, by rw [← Category.assoc, hw, hsu]⟩
  · rintro ⟨Y, g, hrs⟩
    obtain ⟨h, hS⟩ := isRightAlmostSplit_iff_exists_exact_simpleFunctorπ.1 hrs
    exact ⟨Y, Z, g, simpleFunctorπ Z, h, ⟨hS.gIsCokernel⟩⟩

/-- **Existence of minimal right almost split morphisms.** In a Krull-Schmidt category, if `End Z`
is local and `S_Z` is finitely presented, then `Z` ends a right minimal right almost split
morphism. -/
theorem IsKrullSchmidt.exists_isRightAlmostSplit_and_minimal [HasFiniteBiproducts C]
    [IsKrullSchmidt C] (hZ : IsFinitelyPresentedFunctor (simpleFunctor Z)) :
    ∃ (Y : C) (g : Y ⟶ Z), IsRightAlmostSplit g ∧ ∀ φ : Y ⟶ Y, φ ≫ g = g → IsIso φ := by
  obtain ⟨Y, p, hp⟩ := IsKrullSchmidt.exists_isRepresentableProjectiveCover
    ((isFinitelyGeneratedFunctor_radicalFunctor_iff Z).2
      ((isFinitelyPresentedFunctor_simpleFunctor_iff Z).1 hZ))
  obtain ⟨g, hg, rfl⟩ := exists_eq_radicalFunctorLift p
  exact ⟨Y, g, (isRepresentableProjectiveCover_radicalFunctorLift_iff hg).1 hp⟩

end Finiteness

/-! ### Simple functors -/

section Simple

variable {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

/-- **A simple quotient of `(-, Z)` is `S_Z`.** If `End Z` is local, then an epimorphism from
`(-, Z)` onto a simple functor is the projection onto `S_Z`, up to an isomorphism of targets. -/
theorem exists_iso_simpleFunctor_of_epi [Simple F] {Z : C} [IsLocalRing (End Z)]
    (p : preadditiveYoneda.obj Z ⟶ F) [Epi p] :
    ∃ e : simpleFunctor Z ≅ F, simpleFunctorπ Z ≫ e.hom = p := by
  have hp : p ≠ 0 := fun h ↦ id_ne_zero F (by rw [← cancel_epi p, h]; simp)
  -- `p` kills `rad(-, Z)`: otherwise its restriction is onto, some `r : Z ⟶ Z` in the radical has
  -- the same image as `𝟙 Z`, and then `p` kills the unit `𝟙 Z - r`, so `p = 0`.
  have hrad : radicalFunctorι Z ≫ p = 0 := by
    by_contra hne
    have := epi_of_ne_zero_to_simple hne
    obtain ⟨⟨r, hr⟩, hrp⟩ := (AddCommGrpCat.epi_iff_surjective
      ((radicalFunctorι Z ≫ p).app (op Z))).1 inferInstance (p.app (op Z) (𝟙 Z))
    have hu : IsIso (𝟙 Z - r) := by
      simpa using mem_jacobsonRadical_iff_isIso_id_sub_comp_left.1 hr (𝟙 Z)
    -- `p` at `op Z`, on the morphisms `Z ⟶ Z` that are the elements of `(-, Z)` at `op Z`.
    let φ : (Z ⟶ Z) →+ F.obj (op Z) := (p.app (op Z)).hom
    have hrp' : φ r = φ (𝟙 Z) := hrp
    have h0 : preadditiveYoneda.map (𝟙 Z - r) ≫ p = 0 := preadditiveYoneda_obj_hom_ext (by
      refine (congrArg φ (Category.id_comp (𝟙 Z - r))).trans ?_
      exact (map_sub φ _ _).trans ((sub_eq_zero.2 hrp'.symm).trans rfl))
    refine hp ?_
    rw [← Category.id_comp p, ← preadditiveYoneda.map_id, ← IsIso.inv_hom_id (𝟙 Z - r),
      Functor.map_comp, Category.assoc, h0, comp_zero]
  obtain ⟨e, he⟩ : ∃ e : simpleFunctor Z ⟶ F, simpleFunctorπ Z ≫ e = p :=
    ⟨_, (CokernelCofork.IsColimit.desc' (shortExact_radicalFunctor Z).gIsCokernel p hrad).2⟩
  have hene : e ≠ 0 := fun h ↦ hp (by rw [← he, h, comp_zero])
  have := simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal Z
  have : Mono e := mono_of_ne_zero_from_simple hene
  have : IsIso e := isIso_of_mono_of_ne_zero hene
  exact ⟨asIso e, he⟩

variable [HasFiniteBiproducts C] [IsKrullSchmidt C]

/-- **Finitely generated simple functors.** In a Krull-Schmidt category, a finitely generated
simple functor is `S_Z` for some `Z` with local endomorphism ring. -/
theorem IsKrullSchmidt.exists_iso_simpleFunctor [Simple F] (hF : IsFinitelyGeneratedFunctor F) :
    ∃ Z : C, IsLocalRing (End Z) ∧ Nonempty (simpleFunctor Z ≅ F) := by
  obtain ⟨Y, p, hp⟩ := isFinitelyGeneratedFunctor_def.1 hF
  obtain ⟨n, P, hP, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Y
  let p' := preadditiveYoneda.map e.inv ≫ p
  have hp' : p' ≠ 0 := fun h ↦ id_ne_zero F (by
    rw [← cancel_epi p', h]; simp)
  -- One of the summands of `P₁ ⊞ ⋯ ⊞ Pₙ` is not killed; its map to `F` is onto, as `F` is simple.
  obtain ⟨j, hj⟩ : ∃ j, preadditiveYoneda.map (biproduct.ι P j) ≫ p' ≠ 0 := by
    by_contra! h
    refine hp' ?_
    rw [← Category.id_comp p', ← preadditiveYoneda.map_id, ← biproduct.total, Functor.map_sum,
      Preadditive.sum_comp]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [Functor.map_comp, Category.assoc, h, comp_zero]
  have := hP j
  have := epi_of_ne_zero_to_simple hj
  obtain ⟨e', -⟩ := exists_iso_simpleFunctor_of_epi (preadditiveYoneda.map (biproduct.ι P j) ≫ p')
  exact ⟨P j, hP j, ⟨e'⟩⟩

/-- **Finitely presented simple functors.** In a Krull-Schmidt category, a functor is simple and
finitely presented exactly when it is `S_Z` for some `Z` with local endomorphism ring and `S_Z`
finitely presented. -/
theorem IsKrullSchmidt.simple_and_isFinitelyPresentedFunctor_iff :
    Simple F ∧ IsFinitelyPresentedFunctor F ↔
      ∃ Z : C, IsLocalRing (End Z) ∧ IsFinitelyPresentedFunctor (simpleFunctor Z) ∧
        Nonempty (simpleFunctor Z ≅ F) := by
  constructor
  · rintro ⟨_, hF⟩
    obtain ⟨Z, hZ, ⟨e⟩⟩ := exists_iso_simpleFunctor hF.isFinitelyGeneratedFunctor
    exact ⟨Z, hZ, hF.of_iso e.symm, ⟨e⟩⟩
  · rintro ⟨Z, hZ, hfp, ⟨e⟩⟩
    have := simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal Z
    exact ⟨Simple.of_iso e.symm, hfp.of_iso e⟩

end Simple

end TauCeti
