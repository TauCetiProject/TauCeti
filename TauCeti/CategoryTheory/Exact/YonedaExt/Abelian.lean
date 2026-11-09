/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.Basic
public import TauCeti.Algebra.Homology.Ext.Realization
public import TauCeti.CategoryTheory.Exact.Abelian

/-!
# Comparing Yoneda extensions with derived Ext

In an abelian category, the class of a conflation in any exact structure determines a
Mathlib degree-one Ext class. This comparison is injective and respects base and cobase
change. Thus computations with derived Ext can detect equality and splitting of Yoneda
extensions without changing their prescribed endpoints.

For the canonical abelian exact structure the comparison is surjective whenever the final
object admits a projective presentation. In particular, in a category with enough projectives
it is an equivalence of pointed sets. This file does not impose enough projectives on the
comparison map, its injectivity, or its naturality statements.

The construction uses `ShortComplex.ShortExact.extClass` and the realization and equality
criteria in `TauCeti/Algebra/Homology/Ext/Realization.lean`. No group structure on Yoneda
extensions is needed here.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 3.4, for the
  description of degree-one Ext by short exact sequences.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {E : ExactStructure C} {X X' Z Z' : C}

namespace Extension

/-- Two conflations with prescribed end terms have the same derived extension class
exactly when they are Yoneda equivalent. -/
theorem extClass_eq_iff_rel (e e' : E.Extension Z X) :
    e.isKernelCokernelPair.shortExact.extClass =
      e'.isKernelCokernelPair.shortExact.extClass ↔ e.Rel e' := by
  rw [Extension.rel_def]
  constructor
  · intro h
    obtain ⟨φ, h₁, h₃⟩ := (e.isKernelCokernelPair.shortExact.exists_hom_iff_extClass_comp_eq
      e'.isKernelCokernelPair.shortExact (𝟙 X) (𝟙 Z)).mpr (by simpa using h)
    exact ⟨φ.τ₂, by simpa [h₁] using φ.comm₁₂.symm,
      by simpa [h₃] using φ.comm₂₃⟩
  · rintro ⟨φ, h₁, h₂⟩
    let ψ : e.shortComplex ⟶ e'.shortComplex :=
      ⟨𝟙 X, φ, 𝟙 Z, by simpa using h₁.symm, by simpa using h₂⟩
    simpa [ψ] using
      e.isKernelCokernelPair.shortExact.extClass_naturality e'.isKernelCokernelPair.shortExact ψ

end Extension

namespace Ext1

/-- The derived extension class of a Yoneda extension in an abelian category. -/
noncomputable def toExt (ξ : E.Ext1 Z X) : Ext.{w} Z X 1 :=
  lift (fun e ↦ e.isKernelCokernelPair.shortExact.extClass)
    (fun e e' h ↦ (e.extClass_eq_iff_rel e').mpr h) ξ

/-- On a representative, the comparison is Mathlib's short exact extension class. -/
@[simp]
theorem toExt_mk (e : E.Extension Z X) :
    (mk e).toExt = e.isKernelCokernelPair.shortExact.extClass := by
  simp [toExt]

/-- The derived extension class determines the Yoneda class. -/
theorem toExt_injective : Function.Injective (toExt : E.Ext1 Z X → Ext.{w} Z X 1) := by
  intro ξ η h
  induction ξ using induction with
  | h e =>
    induction η using induction with
    | h e' =>
      rw [toExt_mk, toExt_mk] at h
      exact (mk_eq_mk_iff e e').mpr ((e.extClass_eq_iff_rel e').mp h)

/-- Cobase change of Yoneda extensions agrees with postcomposition in derived Ext. -/
@[simp]
theorem toExt_pushout (ξ : E.Ext1 Z X) (f : X ⟶ X') :
    (ξ.pushout f).toExt = ξ.toExt.comp (Ext.mk₀ f) (add_zero 1) := by
  induction ξ using induction with
  | h e =>
    let φ : e.shortComplex ⟶ (e.pushout f).shortComplex :=
      ⟨f, e.pushoutInl f, 𝟙 Z, (e.f_pushoutInl f).symm, by simp⟩
    simpa [φ] using (e.isKernelCokernelPair.shortExact.extClass_naturality
      (e.pushout f).isKernelCokernelPair.shortExact φ).symm

/-- Base change of Yoneda extensions agrees with precomposition in derived Ext. -/
@[simp]
theorem toExt_pullback (ξ : E.Ext1 Z X) (g : Z' ⟶ Z) :
    (ξ.pullback g).toExt = (Ext.mk₀ g).comp ξ.toExt (zero_add 1) := by
  induction ξ using induction with
  | h e =>
    let φ : (e.pullback g).shortComplex ⟶ e.shortComplex :=
      ⟨𝟙 X, e.pullbackFst g, g, by simp, e.pullbackFst_g g⟩
    simpa [φ] using (e.pullback g).isKernelCokernelPair.shortExact.extClass_naturality
      e.isKernelCokernelPair.shortExact φ

/-- The split Yoneda extension has zero derived extension class. -/
@[simp]
theorem toExt_zero : (0 : E.Ext1 Z X).toExt = (0 : Ext.{w} Z X 1) := by
  have h := toExt_pushout (0 : E.Ext1 Z X) (0 : X ⟶ X)
  simpa using h

/-- Vanishing of the derived extension class detects split Yoneda extensions. -/
@[simp]
theorem toExt_eq_zero_iff (ξ : E.Ext1 Z X) : ξ.toExt = (0 : Ext.{w} Z X 1) ↔ ξ = 0 := by
  rw [← toExt_zero]
  exact toExt_injective.eq_iff

/-- Every derived degree-one class out of the end of a projective presentation is represented
by a Yoneda extension for the canonical abelian exact structure. -/
theorem toExt_surjective_of_projective_presentation {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₂] (X : C) :
    Function.Surjective
      (toExt : (ExactStructure.abelian C).Ext1 S.X₃ X → Ext.{w} S.X₃ X 1) := by
  intro α
  obtain ⟨Y, i, p, h, hT, hα⟩ := hS.exists_extClass_eq X α
  refine ⟨mk ⟨Y, i, p, h, (abelian_conflation _).mpr hT⟩, ?_⟩
  simpa only [toExt_mk] using hα

/-- With enough projectives, every derived degree-one class is represented by a Yoneda
extension for the canonical abelian exact structure. -/
theorem toExt_surjective [EnoughProjectives C] (Z X : C) :
    Function.Surjective
      (toExt : (ExactStructure.abelian C).Ext1 Z X → Ext.{w} Z X 1) := by
  let S := ShortComplex.mk _ _ (kernel.condition (Projective.π Z))
  have hS : S.ShortExact := by
    simpa only [ShortComplex.kernelSequence] using kernelSequence_shortExact (Projective.π Z)
  exact toExt_surjective_of_projective_presentation hS X

/-- Yoneda extensions for the abelian exact structure agree with Mathlib's degree-one Ext
as pointed sets in a category with enough projectives. -/
noncomputable def abelianEquiv [EnoughProjectives C] (Z X : C) :
    (ExactStructure.abelian C).Ext1 Z X ≃ Ext.{w} Z X 1 :=
  Equiv.ofBijective toExt ⟨toExt_injective, toExt_surjective Z X⟩

/-- The comparison equivalence sends an extension to its derived class. -/
@[simp]
theorem abelianEquiv_apply [EnoughProjectives C] (ξ : (ExactStructure.abelian C).Ext1 Z X) :
    abelianEquiv Z X ξ = ξ.toExt := (rfl)

/-- The inverse comparison recovers a Yoneda class from its derived class. -/
@[simp]
theorem abelianEquiv_symm_toExt [EnoughProjectives C]
    (ξ : (ExactStructure.abelian C).Ext1 Z X) :
    (abelianEquiv Z X).symm ξ.toExt = ξ :=
  (abelianEquiv Z X).symm_apply_apply ξ

end Ext1

end TauCeti.ExactStructure
