/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.NatEnd
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Comparison
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Ext
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Derived completeness of the cohomology of functors and comparisons modulo an element

Let `R` be a ring. A functor `Φ : C ⥤ ModuleCat R` gives the coefficient functor
`Φ ⋙ forget₂ (ModuleCat R) AddCommGrpCat` with the action `CategoryTheory.Functor.smulEnd Φ` of
`R` by scalar multiplication, so its cohomology groups `Extⁿ(N, Φ)` are `R`-modules
(`TauCeti.Abelian.ExtWithAction`). This file proves two facts about such modules, which reduce
the bijectivity of a comparison map with `a`-adically complete coefficients to its bijectivity
modulo `a`.

* *Derived completeness.* For `R` commutative, if every value `Φ(A)` is derived `I`-complete, so
  is every `Extⁿ(N, Φ)` (`TauCeti.isDerivedComplete_extWithAction_smulEnd`). Products of functors
  to abelian groups are computed objectwise, so they are exact, and the telescope maps of the
  values of `Φ` assemble into an isomorphism of the coefficient `∏_ℕ Φ`.
* *The adic step.* Let `0 → F → F → G → 0` and `0 → F' → F' → G' → 0` be reductions modulo `a` of
  coefficients with an action of `R` on `C` and `C'`, short exact sequences whose first maps are
  the actions of `a` (for functors to modules, `TauCeti.shortExact_smulEnd` gives them), and let
  `β : φ ⋙ F ⟶ F'` commute with the actions of `a` and induce `γ : φ ⋙ G ⟶ G'`. If the comparison
  for `γ` is bijective along `α`, the long exact sequences show that the kernel of the comparison
  map for `β` is `a`-divisible and that it is onto modulo `a`. When the cohomology groups are
  derived `a`-complete, Nakayama's lemma and successive approximation
  (`TauCeti.IsDerivedComplete.eq_zero_of_mem_of_subset_smul`,
  `TauCeti.IsDerivedComplete.subset_range_of_subset_range_add_smul`), applied to the comparison
  maps between the cohomology groups with their actions
  (`CategoryTheory.Functor.extComparisonWithAction`, in
  `TauCeti/CategoryTheory/Abelian/FunctorCohomology/Comparison.lean`), then show that the
  comparison for `β` is bijective (`CategoryTheory.Functor.IsExtComparisonBijective.of_shortExact`).

## Main results

* `TauCeti.isDerivedComplete_extWithAction_smulEnd`: cohomology with derived complete
  coefficients is derived complete.
* `CategoryTheory.Functor.IsExtComparisonBijective.of_shortExact`: a comparison which is bijective
  modulo `a` is bijective, when the cohomology groups are derived `a`-complete.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Completion.lean` (declarations
  `New.Variety.IsDerivedComplete.cohomology` and `New.Variety.Comparison.IsBijective.of_mod`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The statements are adapted from these declarations,
  for functors to modules and comparisons with an action of a commutative ring, and the proofs
  follow their method.
* [Stacks Project, Tag 091N](https://stacks.math.columbia.edu/tag/091N), for derived
  completeness and the derived Nakayama lemma.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TauCeti TauCeti.Abelian
open scoped Pointwise

universe t t' w v u v' u'

namespace TauCeti

/-! ### Derived completeness -/

section Complete

variable {C : Type u} [Category.{v} C] {R : Type*} [CommRing R]

/-- The endomorphism of `∏_ℕ Φ` with components `πⱼ - πⱼ₊₁ ≫ f` is an isomorphism when the
telescope map of `f` is bijective on every value of `Φ`. -/
private lemma isIso_lift_telescope (Φ : C ⥤ ModuleCat.{w} R) (f : R)
    (h : ∀ A, Function.Bijective (telescope (Φ.obj A) f)) :
    IsIso (Fan.IsLimit.lift (productIsProduct
      fun _ : ℕ ↦ Φ ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})
      fun j ↦ Pi.π _ j - Pi.π _ (j + 1) ≫ (Φ.smulEnd f).asHom) := by
  set G := fun _ : ℕ ↦ Φ ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  set T := Fan.IsLimit.lift (productIsProduct G)
    fun j ↦ Pi.π G j - Pi.π G (j + 1) ≫ (Φ.smulEnd f).asHom
  have hT (j : ℕ) : T ≫ Pi.π G j = Pi.π G j - Pi.π G (j + 1) ≫ (Φ.smulEnd f).asHom :=
    Fan.IsLimit.fac _ _ j
  have (A : C) : IsIso (T.app A) := by
    -- The coordinates of a point of `(∏ G)(A)`, which identify it with `ℕ → Φ(A)`.
    let ev : ToType ((∏ᶜ G).obj A) → (ℕ → Φ.obj A) := fun x j ↦ (Pi.π G j).app A x
    have hev : Function.Bijective ev := by
      have he : ev = Concrete.productEquiv (fun j ↦ (G j).obj A) ∘ (piObjIso G A).hom := by
        ext x j
        simp [ev, ← ConcreteCategory.comp_apply]
      rw [he]
      exact (Concrete.productEquiv _).bijective.comp (ConcreteCategory.bijective_of_isIso _)
    have hsq : ev ∘ T.app A = telescope (Φ.obj A) f ∘ ev := by
      ext x j
      simp only [ev, Function.comp_apply, telescope_apply]
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hT]
      simp only [NatTrans.app_sub, NatTrans.comp_app, AddCommGrpCat.hom_sub, AddCommGrpCat.hom_comp,
        AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply]
      exact congrArg _ (Φ.smulEnd_asHom_app_apply f A _)
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Function.Bijective.of_comp_iff' hev _).1 (hsq ▸ (h A).comp hev)
  exact NatIso.isIso_of_isIso_app T

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [EnoughInjectives (C ⥤ AddCommGrpCat.{w})]

/-- **Derived completeness of the cohomology of functors.** If every value of a functor `Φ` to
`R`-modules is derived `I`-complete, then so is every cohomology group `Extⁿ(N, Φ)`. -/
theorem isDerivedComplete_extWithAction_smulEnd {I : Ideal R} {Φ : C ⥤ ModuleCat.{w} R}
    (hΦ : ∀ A, IsDerivedComplete I (Φ.obj A)) (N : C ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsDerivedComplete I (ExtWithAction Φ.smulEnd N n) :=
  ExtWithAction.isDerivedComplete_of_isIso _ (productIsProduct _)
    (fun f hf ↦ isIso_lift_telescope Φ f fun A ↦ (hΦ A).bijective hf) N n

end Complete

end TauCeti

namespace CategoryTheory.Functor

/-! ### The adic step -/

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})]
  {R : Type*} [CommRing R] {F G : C ⥤ AddCommGrpCat.{w}} {F' G' : C' ⥤ AddCommGrpCat.{w}}
  {ρ : R →+* End F} {ρ' : R →+* End F'} {a : R} {q : F ⟶ G} {q' : F' ⟶ G'}
  {hq : (ρ a).asHom ≫ q = 0} {hq' : (ρ' a).asHom ≫ q' = 0}
  {φ : C' ⥤ C} {β : φ ⋙ F ⟶ F'} {γ : φ ⋙ G ⟶ G'}
  {N : C ⥤ AddCommGrpCat.{w}} {N' : C' ⥤ AddCommGrpCat.{w}} {α : N' ⟶ φ ⋙ N}

omit [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})] in
/-- The map from the restriction along `φ` of the reduction of `F` modulo `a` to the reduction of
`F'`, with components `β`, `β` and `γ`. -/
private def reductionHom (hβ : φ.whiskerLeft (ρ a).asHom ≫ β = β ≫ (ρ' a).asHom)
    (hγ : φ.whiskerLeft q ≫ γ = β ≫ q') :
    (ShortComplex.mk _ _ hq).map ((whiskeringLeft C' C AddCommGrpCat.{w}).obj φ) ⟶
      ShortComplex.mk _ _ hq' where
  τ₁ := β
  τ₂ := β
  τ₃ := γ
  comm₁₂ := hβ.symm
  comm₂₃ := hγ.symm

/-- The comparison maps for `β` and `γ` commute with the connecting maps of the reductions. -/
private lemma extComparison_comp_extClass_reduction (hS : (ShortComplex.mk _ _ hq).ShortExact)
    (hS' : (ShortComplex.mk _ _ hq').ShortExact)
    (hβ : φ.whiskerLeft (ρ a).asHom ≫ β = β ≫ (ρ' a).asHom) (hγ : φ.whiskerLeft q ≫ γ = β ≫ q')
    {n : ℕ} (z : Ext.{t} N G n) :
    extComparison φ β α (n + 1) (z.comp hS.extClass rfl) =
      (extComparison φ γ α n z).comp hS'.extClass rfl :=
  extComparison_comp_extClass φ hS hS' (reductionHom hβ hγ) α z rfl

/-- If the comparison for `γ` is bijective, the kernel of the comparison map for `β` is
`a`-divisible: every class in it is `a` times a class in it. -/
private lemma exists_comp_eq_of_extComparison_eq_zero
    (hS : (ShortComplex.mk _ _ hq).ShortExact) (hS' : (ShortComplex.mk _ _ hq').ShortExact)
    (hβ : φ.whiskerLeft (ρ a).asHom ≫ β = β ≫ (ρ' a).asHom) (hγ : φ.whiskerLeft q ≫ γ = β ≫ q')
    (h : ∀ n, Function.Bijective (extComparison φ γ α n)) {n : ℕ} (x : Ext.{t} N F n)
    (hx : extComparison φ β α n x = 0) :
    ∃ y, extComparison φ β α n y = 0 ∧ y.comp (Ext.mk₀ (ρ a).asHom) (add_zero n) = x := by
  -- `x` vanishes in `Extⁿ(N, G)`, so it is `a` times a class `y₀`.
  have hxq : x.comp (Ext.mk₀ q) (add_zero n) = 0 :=
    (h n).1 (by rw [extComparison_comp_mk₀ φ hγ, hx, Ext.zero_comp, _root_.map_zero])
  obtain ⟨y₀, hy₀⟩ := Ext.covariant_sequence_exact₂ N hS x hxq
  have hay : (extComparison φ β α n y₀).comp (Ext.mk₀ (ρ' a).asHom) (add_zero n) = 0 := by
    rw [← extComparison_comp_mk₀ φ hβ, hy₀, hx]
  cases n with
  | zero =>
    -- In degree zero, multiplication by `a` is injective on `Hom(N', F')`.
    have := hS'.mono_f
    exact ⟨y₀, Ext.postcomp_mk₀_injective_of_mono N' (ρ' a).asHom
      (hay.trans (_root_.map_zero _).symm), hy₀⟩
  | succ m =>
    -- The comparison of `y₀` is killed by `a`, so it comes from `Extᵐ(N', G')`, hence from
    -- `Extᵐ(N, G)`; correct `y₀` by the image of that class.
    obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₁ N' hS' _ hay rfl
    obtain ⟨z, rfl⟩ := (h m).2 z'
    refine ⟨y₀ - z.comp hS.extClass rfl, ?_, ?_⟩
    · rw [_root_.map_sub, extComparison_comp_extClass_reduction hS hS' hβ hγ]
      exact sub_eq_zero.2 hz'.symm
    · rw [Ext.sub_comp, hy₀, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp,
        Ext.comp_zero, sub_zero]

/-- If the comparison for `γ` is bijective and the comparison map for `β` in degree `n + 1` is
injective, every class of `Extⁿ(N', F')` is a comparison plus `a` times a class. -/
private lemma exists_add_comp_eq (hS : (ShortComplex.mk _ _ hq).ShortExact)
    (hS' : (ShortComplex.mk _ _ hq').ShortExact)
    (hβ : φ.whiskerLeft (ρ a).asHom ≫ β = β ≫ (ρ' a).asHom) (hγ : φ.whiskerLeft q ≫ γ = β ≫ q')
    (h : ∀ n, Function.Bijective (extComparison φ γ α n)) {n : ℕ}
    (hinj : Function.Injective (extComparison φ β α (n + 1))) (y : Ext.{t'} N' F' n) :
    ∃ (x : Ext.{t} N F n) (z : Ext.{t'} N' F' n),
      extComparison φ β α n x + z.comp (Ext.mk₀ (ρ' a).asHom) (add_zero n) = y := by
  -- The image of `y` in `Extⁿ(N', G')` is the comparison of a class `w` of `Extⁿ(N, G)`, whose
  -- connecting image vanishes since its comparison does; so `w` comes from a class `x`.
  obtain ⟨w, hw⟩ := (h n).2 (y.comp (Ext.mk₀ q') (add_zero n))
  have hδ : w.comp hS.extClass rfl = 0 := hinj <| by
    rw [extComparison_comp_extClass_reduction hS hS' hβ hγ, _root_.map_zero]
    exact hw ▸ (Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
      (by rw [hS'.comp_extClass, Ext.comp_zero])
  obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₃ N hS w rfl hδ
  -- `y` minus the comparison of `x` vanishes in `Extⁿ(N', G')`, so it is `a` times a class.
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₂ N' hS' (y - extComparison φ β α n x) (by
    rw [Ext.sub_comp, ← extComparison_comp_mk₀ φ hγ, hw, sub_self])
  exact ⟨x, z, by rw [hz, add_sub_cancel]⟩

/-- **The adic step.** Let `0 → F → F → G → 0` and `0 → F' → F' → G' → 0` be short exact, with
first maps the actions of `a ∈ R` on coefficients `F` on `C` and `F'` on `C'`, and let
`β : φ ⋙ F ⟶ F'` commute with the actions of `a` and induce `γ : φ ⋙ G ⟶ G'`. Suppose that
every `Extⁿ(N', F')` is derived `a`-complete, and that `Extⁿ(N, F)` is derived `a`-complete
whenever the kernel of the comparison map `Extⁿ(N, F) ⟶ Extⁿ(N', F')` for `β` is `a`-divisible.
If the comparison for `γ` is bijective along `α`, so is the comparison for `β`. -/
theorem IsExtComparisonBijective.of_shortExact (hS : (ShortComplex.mk _ _ hq).ShortExact)
    (hS' : (ShortComplex.mk _ _ hq').ShortExact)
    (hβ : φ.whiskerLeft (ρ a).asHom ≫ β = β ≫ (ρ' a).asHom)
    (hγ : φ.whiskerLeft q ≫ γ = β ≫ q')
    (hF' : ∀ n, IsDerivedComplete (Ideal.span {a}) (ExtWithAction ρ' N' n))
    (hF : ∀ n, (∀ x, extComparison φ β α n x = 0 →
      ∃ y, extComparison φ β α n y = 0 ∧ y.comp (Ext.mk₀ (ρ a).asHom) (add_zero n) = x) →
        IsDerivedComplete (Ideal.span {a}) (ExtWithAction ρ N n))
    (h : IsExtComparisonBijective.{t, t'} φ γ α) : IsExtComparisonBijective.{t, t'} φ β α := by
  rw [isExtComparisonBijective_iff] at h ⊢
  have ha : a ∈ Ideal.span {a} := Ideal.mem_span_singleton_self a
  have hdiv (n : ℕ) := exists_comp_eq_of_extComparison_eq_zero hS hS' hβ hγ h (n := n)
  -- Nakayama: the kernel is `a`-divisible inside a derived complete module, so it vanishes.
  have hinj (n : ℕ) : Function.Injective (extComparison φ β α n) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    have hK : {x | extComparisonWithAction ρ ρ' φ β α n x = 0} ⊆
        a • {x | extComparisonWithAction ρ ρ' φ β α n x = 0} := fun z hz ↦ by
      obtain ⟨y, hy, hyz⟩ := hdiv n (ExtWithAction.toExt ρ z)
        (by simpa using congrArg (ExtWithAction.toExt ρ') hz)
      refine Set.mem_smul_set.2 ⟨(ExtWithAction.toExt ρ).symm y, ?_, ?_⟩
      · exact (ExtWithAction.toExt ρ').injective (by simpa using hy)
      · exact (ExtWithAction.toExt ρ).injective (by simpa using hyz)
    have h0 := (hF n (hdiv n)).eq_zero_of_mem_of_subset_smul ha hK
      (x := (ExtWithAction.toExt ρ).symm x) ((ExtWithAction.toExt ρ').injective (by simpa using hx))
    simpa using congrArg (ExtWithAction.toExt ρ) h0
  -- Successive approximation: the comparison map is onto modulo `a`, so it is onto.
  refine fun n ↦ ⟨hinj n, fun y ↦ ?_⟩
  have hsub := (hF n (hdiv n)).subset_range_of_subset_range_add_smul (hF' n) ha
    (extComparisonWithAction ρ ρ' φ β α n) (extComparisonWithAction_smul α hβ)
    (S := Set.univ) fun y _ ↦ by
      obtain ⟨x, z, hxz⟩ := exists_add_comp_eq hS hS' hβ hγ h (hinj (n + 1))
        (ExtWithAction.toExt ρ' y)
      refine Set.mem_add.2 ⟨_, ⟨(ExtWithAction.toExt ρ).symm x, rfl⟩,
        a • (ExtWithAction.toExt ρ').symm z, Set.smul_mem_smul_set (Set.mem_univ _),
        (ExtWithAction.toExt ρ').injective ?_⟩
      simpa using hxz
  obtain ⟨x, hx⟩ := hsub (Set.mem_univ ((ExtWithAction.toExt ρ').symm y))
  exact ⟨ExtWithAction.toExt ρ x, by simpa using congrArg (ExtWithAction.toExt ρ') hx⟩

end CategoryTheory.Functor
