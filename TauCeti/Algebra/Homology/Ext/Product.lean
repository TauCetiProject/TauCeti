/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

/-!
# Ext into a product

In an abelian category with enough injectives in which products of shape `J` are exact, `Extⁿ`
into a product of a `J`-indexed family is the product of the `Extⁿ` into its factors, in every
degree `n`. The comparison `CategoryTheory.Abelian.Ext.addEquivProduct` is composition with the
projections. In degree zero this is the universal property of the product. In positive degree
the argument shifts dimension along the product `∏ Yᵢ ⟶ ∏ Iᵢ ⟶ ∏ Qᵢ` of injective
copresentations `Yᵢ ⟶ Iᵢ ⟶ Qᵢ` of the factors, which is short exact because products of shape
`J` are exact, and whose middle term is injective. In degree one every class is the image of a
morphism to `∏ Qᵢ`, and it vanishes exactly when this morphism lifts to `∏ Iᵢ`; both conditions
are checked on the factors. In degree `n + 2` the connecting map identifies `Extⁿ⁺¹(X, ∏ Qᵢ)`
with `Extⁿ⁺²(X, ∏ Yᵢ)`, compatibly with the projections, so the claim for the family `Qᵢ` in
degree `n + 1` gives it for the family `Yᵢ` in degree `n + 2`.

Unlike `Ext` from a coproduct (`CategoryTheory.Abelian.Ext.coproductAddEquiv`), which holds in
every abelian category with enough injectives, this statement assumes that products of shape
`J` are exact: exactness is what makes the product of the copresentations short exact.
Categories of functors to abelian groups satisfy it, so the cohomology of a functor with
coefficients in a product of functors is the product of the cohomology groups. This is what makes
the telescope map `(xⱼ) ↦ (xⱼ - a • xⱼ₊₁)` on coefficients induce the telescope map on
cohomology, and so carries derived completeness from coefficients to `Ext`.

## Main declarations

* `CategoryTheory.Abelian.Ext.addEquivProduct`: `Extⁿ(X, ∏ Yᵢ) ≃+ ∀ i, Extⁿ(X, Yᵢ)`, for a
  limiting fan of a family indexed by a type whose products are exact.
* `CategoryTheory.Abelian.Ext.addEquivProduct_apply` and
  `CategoryTheory.Abelian.Ext.addEquivProduct_symm_comp_mk₀`: the equivalence is composition with
  the projections.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Chapter 2.
* The dimension-shifting argument is that of `CategoryTheory.Abelian.Ext.coproductAddEquiv` in
  `TauCeti.Algebra.Homology.Ext.Coproduct`, with a product of injective copresentations in place of
  a single one.
* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Completion.lean` (declaration
  `New.Variety.IsDerivedComplete.cohomology`, whose proof uses that cohomology commutes with the
  product of countably many copies of the coefficients); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The statement here is for arbitrary products in an abelian category with exact products.
-/

public section

open CategoryTheory Limits

universe w v u t

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {J : Type t}

/-- Composition with the projections of a fan, in degree `n`. -/
private noncomputable def project (X : C) {Y : J → C} (c : Fan Y) (n : ℕ) :
    Ext.{w} X c.pt n →+ ∀ i, Ext.{w} X (Y i) n :=
  AddMonoidHom.pi fun i ↦ (mk₀ (c.proj i)).postcomp X (add_zero n)

private lemma project_apply (X : C) {Y : J → C} (c : Fan Y) (n : ℕ) (e : Ext.{w} X c.pt n)
    (i : J) : project X c n e i = e.comp (mk₀ (c.proj i)) (add_zero n) :=
  (rfl)

private lemma project_mk_apply (X : C) {Y : J → C} {P : C} (p : ∀ i, P ⟶ Y i) (n : ℕ)
    (e : Ext.{w} X P n) (i : J) : project X (Fan.mk P p) n e i = e.comp (mk₀ (p i)) (add_zero n) :=
  (rfl)

/-- In degree zero, composition with the projections is the universal property of the
product. -/
private lemma bijective_project_zero (X : C) {Y : J → C} {c : Fan Y} (hc : IsLimit c) :
    Function.Bijective (project X c 0) := by
  have hhom : Function.Bijective fun (f : X ⟶ c.pt) (i : J) ↦ f ≫ c.proj i :=
    ⟨fun f g h ↦ Fan.IsLimit.hom_ext hc _ _ fun i ↦ congrFun h i,
      fun g ↦ ⟨Fan.IsLimit.lift hc g, funext fun i ↦ Fan.IsLimit.fac hc g i⟩⟩
  have hsq : (fun g : ∀ i, X ⟶ Y i ↦ fun i ↦ mk₀ (g i)) ∘
      (fun (f : X ⟶ c.pt) (i : J) ↦ f ≫ c.proj i) = project X c 0 ∘ mk₀ := by
    ext f i
    simp [project_apply, mk₀_comp_mk₀]
  have h₂ : Function.Bijective fun g : ∀ i, X ⟶ Y i ↦ fun i ↦ mk₀ (g i) :=
    Function.Bijective.piMap fun i ↦ mk₀_bijective X (Y i)
  exact (Function.Bijective.of_comp_iff _ (mk₀_bijective X c.pt)).1 (hsq ▸ h₂.comp hhom)

/-- Composition with the projections is bijective for one limiting fan of a family exactly when
it is for another. -/
private lemma bijective_project_iff (X : C) {Y : J → C} {c d : Fan Y} (hc : IsLimit c)
    (hd : IsLimit d) (n : ℕ) :
    Function.Bijective (project X c n) ↔ Function.Bijective (project X d n) := by
  let e := hc.conePointUniqueUpToIso hd
  have he (i : J) : e.hom ≫ d.proj i = c.proj i := hc.conePointUniqueUpToIso_hom_comp hd ⟨i⟩
  have hsq : project X d n ∘ TauCeti.extAddEquivOfIso (Iso.refl X) e n = project X c n := by
    ext x i
    simp [project_apply, comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, he]
  rw [← hsq]
  exact Function.Bijective.of_comp_iff _ (AddEquiv.bijective _)

section ExactProducts

variable [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C]
  [EnoughInjectives C]

omit [HasExt C] [HasExactLimitsOfShape (Discrete J) C] in
/-- The product `∏ Yᵢ ⟶ ∏ Iᵢ ⟶ ∏ Qᵢ` of the chosen injective copresentations
`Yᵢ ⟶ Iᵢ ⟶ Qᵢ` of the members of a family. -/
private noncomputable abbrev piCopresentation (Y : J → C) : ShortComplex C :=
  ShortComplex.mk (Limits.Pi.map fun i ↦ Injective.ι (Y i))
    (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (Y i))) (by ext; simp)

omit [HasExt C] in
/-- The product of injective copresentations is short exact, because products of shape `J` are
exact. -/
private lemma piCopresentation_shortExact (Y : J → C) : (piCopresentation Y).ShortExact := by
  let S : ShortComplex (Discrete J ⥤ C) := ShortComplex.mk
    (Discrete.natTrans (F := Discrete.functor Y)
      (G := Discrete.functor fun i ↦ Injective.under (Y i)) fun i ↦ Injective.ι (Y i.as))
    (Discrete.natTrans (G := Discrete.functor fun i ↦ cokernel (Injective.ι (Y i)))
      fun i ↦ cokernel.π (Injective.ι (Y i.as))) (by ext; simp)
  have (i : Discrete J) : Mono (S.f.app i) := by dsimp [S]; infer_instance
  have (i : Discrete J) : Epi (S.g.app i) := by dsimp [S]; infer_instance
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have : Epi S.g := NatTrans.epi_of_epi_app _
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_evaluation S).2
    fun i ↦ (TauCeti.injectiveCokernelSequence_shortExact (Y i.as)).exact) inferInstance
    inferInstance
  exact hS.map_of_exact lim

omit [HasExt C] [HasExactLimitsOfShape (Discrete J) C] in
/-- The projection of the product of copresentations to the copresentation of a factor. -/
private noncomputable def piCopresentationπ (Y : J → C) (i : J) :
    piCopresentation Y ⟶ TauCeti.injectiveCokernelSequence (Y i) where
  τ₁ := Pi.π Y i
  τ₂ := Pi.π _ i
  τ₃ := Pi.π _ i
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- The connecting maps of the copresentations are compatible with the projections. -/
private lemma extClass_comp_mk₀_π (Y : J → C) (i : J) :
    (piCopresentation_shortExact Y).extClass.comp (mk₀ (Pi.π Y i)) (add_zero 1) =
      (mk₀ (Pi.π _ i)).comp
        (TauCeti.injectiveCokernelSequence_shortExact (Y i)).extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality (piCopresentation_shortExact Y)
    (TauCeti.injectiveCokernelSequence_shortExact (Y i)) (piCopresentationπ Y i)

/-- In degree one, a class into a product is a morphism to `∏ Qᵢ` up to the morphisms that lift
to `∏ Iᵢ`; both conditions are checked on the factors. -/
private lemma bijective_project_one (X : C) (Y : J → C) :
    Function.Bijective (project X (Fan.mk (∏ᶜ Y) (Pi.π Y)) 1) := by
  have hT := piCopresentation_shortExact Y
  have hS (i : J) := TauCeti.injectiveCokernelSequence_shortExact (Y i)
  have hrep {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂] (e : Ext.{w} X S.X₁ 1) :
      ∃ a : X ⟶ S.X₃, (mk₀ a).comp hS.extClass (zero_add 1) = e := by
    obtain ⟨a, ha⟩ := covariant_sequence_exact₁ X hS e (eq_zero_of_injective _) rfl
    exact ⟨addEquiv₀ a, by simpa using ha⟩
  have hproj (a : X ⟶ (piCopresentation Y).X₃) (i : J) :
      project X (Fan.mk (∏ᶜ Y) (Pi.π Y)) 1 ((mk₀ a).comp hT.extClass (zero_add 1)) i =
        (mk₀ (a ≫ Pi.π _ i)).comp (hS i).extClass (zero_add 1) := by
    rw [project_mk_apply, comp_assoc_of_third_deg_zero, extClass_comp_mk₀_π, mk₀_comp_mk₀_assoc]
  refine ⟨(injective_iff_map_eq_zero _).2 fun e he ↦ ?_, fun e ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hrep hT e
    have hlocal (i : J) :
        ∃ b : X ⟶ Injective.under (Y i), b ≫ cokernel.π _ = a ≫ Pi.π _ i := by
      have hz : (mk₀ (a ≫ Pi.π _ i)).comp (hS i).extClass (zero_add 1) = 0 := by
        rw [← hproj]
        exact congrFun he i
      obtain ⟨b, hb⟩ := covariant_sequence_exact₃ X (hS i) (mk₀ (a ≫ Pi.π _ i)) rfl hz
      refine ⟨addEquiv₀ b, (mk₀_bijective _ _).1 ?_⟩
      simpa only [← mk₀_comp_mk₀, mk₀_addEquiv₀_apply] using hb
    choose b hb using hlocal
    have ha : Pi.lift b ≫ (piCopresentation Y).g = a := by
      ext i
      simp [hb]
    rw [← ha, ← mk₀_comp_mk₀_assoc, hT.comp_extClass, comp_zero]
  · choose a ha using fun i ↦ hrep (hS i) (e i)
    refine ⟨(mk₀ (Pi.lift a)).comp hT.extClass (zero_add 1), funext fun i ↦ ?_⟩
    rw [hproj, Pi.lift_comp_π, ha]

/-- In degree `n + 2`, the connecting maps of the copresentations identify `Extⁿ⁺¹(X, Qᵢ)` with
`Extⁿ⁺²(X, Yᵢ)` and `Extⁿ⁺¹(X, ∏ Qᵢ)` with `Extⁿ⁺²(X, ∏ Yᵢ)`, compatibly with the projections. -/
private lemma bijective_project_add_two (X : C) (Y : J → C) (n : ℕ)
    (h : Function.Bijective (project X (Fan.mk _ (Pi.π fun i ↦ cokernel (Injective.ι (Y i))))
      (n + 1))) :
    Function.Bijective (project X (Fan.mk (∏ᶜ Y) (Pi.π Y)) (n + 2)) := by
  have hT := piCopresentation_shortExact Y
  have hδ {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂] :
      Function.Bijective (hS.extClass.postcomp X (show n + 1 + 1 = n + 2 from rfl)) :=
    hS.extClass_postcomp_bijective X rfl
      ⟨fun _ _ ↦ (eq_zero_of_injective _).trans (eq_zero_of_injective _).symm⟩
      ⟨fun _ _ ↦ (eq_zero_of_injective _).trans (eq_zero_of_injective _).symm⟩
  have hsq : project X (Fan.mk (∏ᶜ Y) (Pi.π Y)) (n + 2) ∘ hT.extClass.postcomp X rfl =
      (fun e i ↦ (TauCeti.injectiveCokernelSequence_shortExact (Y i)).extClass.postcomp X rfl
        (e i)) ∘ project X (Fan.mk _ (Pi.π fun i ↦ cokernel (Injective.ι (Y i)))) (n + 1) := by
    ext e i
    simp only [Function.comp_apply, project_mk_apply, AddMonoidHom.flip_apply,
      bilinearComp_apply_apply]
    rw [comp_assoc_of_third_deg_zero, extClass_comp_mk₀_π, ← comp_assoc_of_second_deg_zero]
  have h₂ : Function.Bijective fun (e : ∀ i, Ext.{w} X (cokernel (Injective.ι (Y i))) (n + 1)) i ↦
      (TauCeti.injectiveCokernelSequence_shortExact (Y i)).extClass.postcomp X rfl (e i) :=
    Function.Bijective.piMap fun i ↦ hδ (TauCeti.injectiveCokernelSequence_shortExact (Y i))
  exact (Function.Bijective.of_comp_iff _ (hδ hT)).1 (hsq ▸ h₂.comp h)

private lemma bijective_project_pi (X : C) (n : ℕ) :
    ∀ Y : J → C, Function.Bijective (project X (Fan.mk (∏ᶜ Y) (Pi.π Y)) n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact fun Y ↦ bijective_project_zero X (productIsProduct Y)
  | one => exact bijective_project_one X
  | more n _ ih => exact fun Y ↦ bijective_project_add_two X Y n (ih _)

/-- `Extⁿ` into a product is the product of the `Extⁿ` into its factors, by composition with the
projections, in every degree, when products of shape `J` are exact. -/
noncomputable def addEquivProduct (X : C) {Y : J → C} {c : Fan Y} (hc : IsLimit c) (n : ℕ) :
    Ext.{w} X c.pt n ≃+ ∀ i, Ext.{w} X (Y i) n :=
  AddEquiv.ofBijective (project X c n)
    ((bijective_project_iff X (productIsProduct Y) hc n).1 (bijective_project_pi X n Y))

/-- The product comparison composes a class with the indicated projection. -/
@[simp]
theorem addEquivProduct_apply (X : C) {Y : J → C} {c : Fan Y} (hc : IsLimit c) (n : ℕ)
    (e : Ext.{w} X c.pt n) (i : J) :
    addEquivProduct X hc n e i = e.comp (mk₀ (c.proj i)) (add_zero n) :=
  (rfl)

/-- The class assembled from a family, composed with a projection, is the indicated member of
the family. -/
@[simp]
theorem addEquivProduct_symm_comp_mk₀ (X : C) {Y : J → C} {c : Fan Y} (hc : IsLimit c) (n : ℕ)
    (e : ∀ i, Ext.{w} X (Y i) n) (i : J) :
    ((addEquivProduct X hc n).symm e).comp (mk₀ (c.proj i)) (add_zero n) = e i :=
  congrFun ((addEquivProduct X hc n).apply_symm_apply e) i

end ExactProducts

end CategoryTheory.Abelian.Ext
