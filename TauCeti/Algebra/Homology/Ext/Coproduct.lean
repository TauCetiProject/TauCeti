/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Ext from a coproduct

In an abelian category with enough injectives, `Extⁿ` from a coproduct is the product of the
`Extⁿ` from its summands, in every degree `n`. The comparison
`CategoryTheory.Abelian.Ext.coproductAddEquiv` is restriction along the coproduct inclusions;
no finiteness of the index set or exactness of coproducts is required, because the argument
shifts dimension in the second variable. In degree zero this is the universal property of the
coproduct. In degree one every class is the image of a morphism to the cokernel `Q` of an
embedding `Y ⟶ I` into an injective object, and two such morphisms give the same class exactly
when they differ by a morphism factoring through `I`; both conditions are checked on the summands.
In degree `n + 2`
the connecting map `Extⁿ⁺¹(-, Q) ⟶ Extⁿ⁺²(-, Y)` is bijective, naturally in the first variable.

This permits extension descent to be checked on summands of a presenting coproduct, for
example on the cyclic quotients presenting an ideal-power torsion module, and it computes the
cohomology of a disjoint union of functors as the product of the cohomology groups of its pieces.

## Main declarations

* `CategoryTheory.Abelian.Ext.coproductAddEquiv`: `Extⁿ(∐ Xᵢ, Y) ≃+ ∀ i, Extⁿ(Xᵢ, Y)`.
* `CategoryTheory.Abelian.Ext.coproductAddEquiv_apply` and
  `CategoryTheory.Abelian.Ext.mk₀_comp_coproductAddEquiv_symm`: the equivalence is restriction
  along the inclusions.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.6.
* The Stacks Project, Lemma 15.91.8 (05EG), for the cyclic-quotient reduction in formal glueing.
* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/General/Algebra/LongExactSequences.lean` (declaration `New.Variety.H.sigma_bijective`,
  the case of free abelian functors on a disjoint union, proved by dimension shifting in the
  second variable); Apache 2.0, Copyright 2026 Anthropic, PBC. The extension of
  `CategoryTheory.Abelian.Ext.coproductAddEquiv` to every degree is adapted from it and stated for
  an arbitrary abelian category with enough injectives.
-/

public section

open CategoryTheory Limits

universe w v u t

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {J : Type t} {X : J → C} {c : Cofan X}

/-- Restriction along the inclusions of a cofan, in degree `n`. -/
private noncomputable def restrict (c : Cofan X) (Y : C) (n : ℕ) :
    Ext.{w} c.pt Y n →+ ∀ i, Ext.{w} (X i) Y n :=
  AddMonoidHom.pi fun i ↦ (mk₀ (c.inj i)).precomp Y (zero_add n)

private lemma restrict_apply (c : Cofan X) (Y : C) (n : ℕ) (e : Ext.{w} c.pt Y n) (i : J) :
    restrict c Y n e i = (mk₀ (c.inj i)).comp e (zero_add n) :=
  (rfl)

/-- In degree zero, restriction is the universal property of the coproduct. -/
private lemma bijective_restrict_zero (hc : IsColimit c) (Y : C) :
    Function.Bijective (restrict c Y 0) := by
  have hhom : Function.Bijective fun (f : c.pt ⟶ Y) (i : J) ↦ c.inj i ≫ f :=
    ⟨fun f g h ↦ Cofan.IsColimit.hom_ext hc _ _ fun i ↦ congrFun h i,
      fun g ↦ ⟨Cofan.IsColimit.desc hc g, funext fun i ↦ by simp⟩⟩
  have hsq : (fun g : ∀ i, X i ⟶ Y ↦ fun i ↦ mk₀ (g i)) ∘
      (fun (f : c.pt ⟶ Y) (i : J) ↦ c.inj i ≫ f) = restrict c Y 0 ∘ mk₀ := by
    ext f i
    simp [restrict_apply]
  have h₂ : Function.Bijective fun g : ∀ i, X i ⟶ Y ↦ fun i ↦ mk₀ (g i) :=
    Function.Bijective.piMap fun i ↦ mk₀_bijective (X i) Y
  exact (Function.Bijective.of_comp_iff _ (mk₀_bijective c.pt Y)).1 (hsq ▸ h₂.comp hhom)

variable [EnoughInjectives C]

/-- In degree one, a class is a morphism to the cokernel of an embedding `Y ⟶ I` into an injective
object, up to the morphisms which factor through `I`; both conditions are checked on summands. -/
private lemma bijective_restrict_one (hc : IsColimit c) (Y : C) :
    Function.Bijective (restrict c Y 1) := by
  -- A single injective copresentation computes every component and the coproduct at once.
  let S := TauCeti.injectiveCokernelSequence Y
  have hS := TauCeti.injectiveCokernelSequence_shortExact Y
  have hrep (Z : C) (e : Ext.{w} Z Y 1) :
      ∃ a : Z ⟶ S.X₃, (mk₀ a).comp hS.extClass (zero_add 1) = e := by
    obtain ⟨a, ha⟩ := covariant_sequence_exact₁ Z hS e (eq_zero_of_injective _) rfl
    exact ⟨addEquiv₀ a, by simpa using ha⟩
  refine ⟨(injective_iff_map_eq_zero _).mpr ?_, ?_⟩
  · intro e he
    obtain ⟨a, rfl⟩ := hrep c.pt e
    have hlocal (i : J) : ∃ b : X i ⟶ S.X₂, b ≫ S.g = c.inj i ≫ a := by
      have hi := congrFun he i
      have hz : (mk₀ (c.inj i ≫ a)).comp hS.extClass (zero_add 1) = 0 := by
        simpa [restrict_apply, ← mk₀_comp_mk₀_assoc] using hi
      obtain ⟨b, hb⟩ := covariant_sequence_exact₃ (X i) hS (mk₀ (c.inj i ≫ a)) rfl hz
      refine ⟨addEquiv₀ b, (mk₀_bijective _ _).1 ?_⟩
      simpa only [← mk₀_comp_mk₀, mk₀_addEquiv₀_apply] using hb
    choose b hb using hlocal
    have ha : Cofan.IsColimit.desc hc b ≫ S.g = a := by
      apply Cofan.IsColimit.hom_ext hc
      intro i
      simp [hb]
    rw [← ha, ← mk₀_comp_mk₀_assoc, hS.comp_extClass, comp_zero]
  · intro e
    choose a ha using fun i ↦ hrep (X i) (e i)
    refine ⟨(mk₀ (Cofan.IsColimit.desc hc a)).comp hS.extClass (zero_add 1), ?_⟩
    ext i
    simpa [restrict_apply] using ha i

/-- In degree `n + 2`, the connecting map of an embedding `Y ⟶ I` into an injective object, with
cokernel `I ⟶ Q`, identifies `Extⁿ⁺¹(-, Q)` with `Extⁿ⁺²(-, Y)`, compatibly with restriction. -/
private lemma bijective_restrict_succ_succ (Y : C) (n : ℕ)
    (h : Function.Bijective (restrict c (TauCeti.injectiveCokernelSequence Y).X₃ (n + 1))) :
    Function.Bijective (restrict c Y (n + 2)) := by
  have hS := TauCeti.injectiveCokernelSequence_shortExact Y
  have hδ (Z : C) : Function.Bijective (hS.extClass.postcomp Z (show n + 1 + 1 = n + 2 from rfl)) :=
    hS.extClass_postcomp_bijective Z rfl
      ⟨fun _ _ ↦ (eq_zero_of_injective _).trans (eq_zero_of_injective _).symm⟩
      ⟨fun _ _ ↦ (eq_zero_of_injective _).trans (eq_zero_of_injective _).symm⟩
  have hsq : restrict c Y (n + 2) ∘ hS.extClass.postcomp c.pt rfl =
      (fun e i ↦ hS.extClass.postcomp (X i) rfl (e i)) ∘ restrict c _ (n + 1) := by
    ext e i
    simp only [Function.comp_apply, restrict_apply]
    exact (comp_assoc _ _ _ (zero_add _) rfl (by lia)).symm
  have h₂ : Function.Bijective fun (e : ∀ i, Ext.{w} (X i) _ (n + 1)) i ↦
      hS.extClass.postcomp (X i) rfl (e i) :=
    Function.Bijective.piMap fun i ↦ hδ (X i)
  exact (Function.Bijective.of_comp_iff _ (hδ c.pt)).1 (hsq ▸ h₂.comp h)

private lemma bijective_restrict (hc : IsColimit c) (n : ℕ) :
    ∀ Y : C, Function.Bijective (restrict c Y n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact bijective_restrict_zero hc
  | one => exact bijective_restrict_one hc
  | more n _ ih => exact fun Y ↦ bijective_restrict_succ_succ Y n (ih _)

/-- `Extⁿ` from a coproduct is the product of the `Extⁿ` from its summands, by restriction along
the coproduct inclusions. This holds in every degree and for arbitrary index sets. -/
noncomputable def coproductAddEquiv (hc : IsColimit c) (Y : C) (n : ℕ) :
    Ext.{w} c.pt Y n ≃+ ∀ i, Ext.{w} (X i) Y n :=
  AddEquiv.ofBijective (restrict c Y n) (bijective_restrict hc n Y)

/-- The coproduct comparison restricts a class along the indicated inclusion. -/
@[simp]
theorem coproductAddEquiv_apply (hc : IsColimit c) (Y : C) (n : ℕ)
    (e : Ext.{w} c.pt Y n) (i : J) :
    coproductAddEquiv hc Y n e i = (mk₀ (c.inj i)).comp e (zero_add n) :=
  (rfl)

/-- Restriction of the class assembled from a family recovers its indicated component. -/
@[simp]
theorem mk₀_comp_coproductAddEquiv_symm (hc : IsColimit c) (Y : C) (n : ℕ)
    (e : ∀ i, Ext.{w} (X i) Y n) (i : J) :
    (mk₀ (c.inj i)).comp ((coproductAddEquiv hc Y n).symm e) (zero_add n) = e i :=
  congrFun ((coproductAddEquiv hc Y n).apply_symm_apply e) i

end CategoryTheory.Abelian.Ext
