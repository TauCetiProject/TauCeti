/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.LinearAlgebra.Exact

/-!
# Low-degree finiteness and the Ext dimension difference

For a short exact sequence `0 → A → B → Q → 0`, finiteness of `Extⁿ(P,Q)` and vanishing of
`Extⁿ⁺¹(P,Q)` make finiteness of `Extⁿ⁺¹(P,A)` equivalent to finiteness of `Extⁿ⁺¹(P,B)`.
In degrees zero and one, the dimension difference `dim Hom - dim Ext¹` is additive when
`Ext¹(P,Q)` vanishes. No finiteness or vanishing in degree two or above is required.

This is the algebraic input for the point-twist induction in analytic Riemann–Roch: Q is a
skyscraper sheaf, its H⁰ is one-dimensional and its H¹ vanishes. It does not prove analytic
cohomology finiteness; that argument must first establish finiteness for the structure sheaf.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16.
* C. Weibel, *An Introduction to Homological Algebra*, §§2.4–2.7.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Module

namespace TauCeti

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (k : Type t) [Field k] [Linear k C] {S : ShortComplex C} (hS : S.ShortExact) (P : C)

include hS

/-- Finiteness propagates in both directions across an extension with a finite cohomology
contribution in degree n and no contribution in degree n+1. No later Ext group is constrained. -/
theorem finiteDimensional_ext_succ_iff_of_subsingleton (n : ℕ)
    [FiniteDimensional k (Ext.{w} P S.X₃ n)] [Subsingleton (Ext.{w} P S.X₃ (n + 1))] :
    FiniteDimensional k (Ext.{w} P S.X₁ (n + 1)) ↔
      FiniteDimensional k (Ext.{w} P S.X₂ (n + 1)) := by
  constructor
  · intro h
    have := h
    exact finiteDimensional_of_exact (exact_postcompOfLinear k hS P (n + 1))
  · intro h
    have := h
    apply finiteDimensional_of_exact
      (f := Ext.postcompOfLinear hS.extClass k P rfl)
      (g := Ext.postcompOfLinear (Ext.mk₀ S.f) k P (add_zero (n + 1)))
    simpa only [coe_postcompOfLinear, AddCommGrpCat.hom_ofHom] using
      (ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.covariant_sequence_exact₁' P hS n (n + 1) rfl)

/-- The degree-zero/one dimension difference is additive across a short exact sequence with
vanishing Ext¹ of the quotient. This needs only the displayed low-degree finiteness. -/
theorem finrank_ext_zero_sub_finrank_ext_one_add
    [FiniteDimensional k (Ext.{w} P S.X₂ 0)]
    [FiniteDimensional k (Ext.{w} P S.X₃ 0)] [FiniteDimensional k (Ext.{w} P S.X₁ 1)]
    [Subsingleton (Ext.{w} P S.X₃ 1)] :
    (finrank k (Ext.{w} P S.X₂ 0) : ℤ) - finrank k (Ext.{w} P S.X₂ 1) =
      ((finrank k (Ext.{w} P S.X₁ 0) : ℤ) - finrank k (Ext.{w} P S.X₁ 1)) +
        finrank k (Ext.{w} P S.X₃ 0) := by
  have : FiniteDimensional k (Ext.{w} P S.X₂ 1) :=
    (finiteDimensional_ext_succ_iff_of_subsingleton k hS P 0).1 inferInstance
  have := hS.mono_f
  let f₀ := Ext.postcompOfLinear (Ext.mk₀ S.f) k P (add_zero 0)
  let g₀ := Ext.postcompOfLinear (Ext.mk₀ S.g) k P (add_zero 0)
  let δ := Ext.postcompOfLinear hS.extClass k P (show 0 + 1 = 1 from rfl)
  let f₁ := Ext.postcompOfLinear (Ext.mk₀ S.f) k P (add_zero 1)
  let g₁ := Ext.postcompOfLinear (Ext.mk₀ S.g) k P (add_zero 1)
  have hfg₀ : Function.Exact f₀ g₀ := exact_postcompOfLinear k hS P 0
  have hgδ : Function.Exact g₀ δ := by
    simpa only [g₀, δ, coe_postcompOfLinear, AddCommGrpCat.hom_ofHom] using
      (ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.covariant_sequence_exact₃' P hS 0 1 rfl)
  have hδf : Function.Exact δ f₁ := by
    simpa only [g₀, δ, f₁, coe_postcompOfLinear, AddCommGrpCat.hom_ofHom] using
      (ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.covariant_sequence_exact₁' P hS 0 1 rfl)
  have hfg₁ : Function.Exact f₁ g₁ := exact_postcompOfLinear k hS P 1
  have hf₀ : Function.Injective f₀ := Ext.postcomp_mk₀_injective_of_mono P S.f
  have hf₁ : Function.Surjective f₁ := fun x ↦ (hfg₁ x).1 (Subsingleton.elim _ _)
  have hdimf₀ := LinearMap.finrank_range_of_inj hf₀
  have hdimg₀ := g₀.finrank_range_add_finrank_ker
  have hdimδ := δ.finrank_range_add_finrank_ker
  have hdimf₁ := f₁.finrank_range_add_finrank_ker
  rw [hfg₀.linearMap_ker_eq, hdimf₀] at hdimg₀
  rw [hgδ.linearMap_ker_eq] at hdimδ
  rw [hδf.linearMap_ker_eq, LinearMap.range_eq_top.2 hf₁, finrank_top] at hdimf₁
  omega

end TauCeti
