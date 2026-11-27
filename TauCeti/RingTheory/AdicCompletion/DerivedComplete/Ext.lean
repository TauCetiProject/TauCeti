/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.Algebra.Homology.Ext.Product
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

/-!
# Derived completeness of `Ext` groups

Let `F` be an object of an abelian category `C` with an action `ρ : R →+* End F` of a commutative
ring `R`, so that every `Extⁿ(P, F)` is an `R`-module (`TauCeti.Abelian.ExtWithAction`).

The telescope map `(xⱼ) ↦ (xⱼ - f • xⱼ₊₁)` defining derived completeness
(`TauCeti.IsDerivedComplete`) has a counterpart on a product `∏_ℕ F` of copies of `F`: the
endomorphism with components `πⱼ - πⱼ₊₁ ≫ ρ(f)`. When `C` has enough injectives and countable
products in `C` are exact, `Extⁿ(P, -)` turns the product into the product of copies of
`Extⁿ(P, F)` (`CategoryTheory.Abelian.Ext.addEquivProduct`), and this endomorphism into the
telescope map of `Extⁿ(P, F)`. So if it is an isomorphism for every `f ∈ I`, every `Extⁿ(P, F)`
is derived `I`-complete (`TauCeti.Abelian.ExtWithAction.isDerivedComplete_of_isIso`). For a functor
to modules, as coefficients in a category of functors, the endomorphism is an isomorphism as soon
as the values of the functor are derived complete, so derived completeness passes from the
coefficients to their cohomology.

A short exact sequence `0 → F → F → G → 0` whose first map is the action of `a ∈ R` is a reduction
of `F` modulo `a`. Its long exact sequence shows that a class of `Extⁿ(P, F)` whose image in
`Extⁿ(P, G)` vanishes is a multiple of `a`
(`TauCeti.Abelian.ExtWithAction.exists_smul_eq_of_comp_eq_zero`).

## Main results

* `TauCeti.Abelian.ExtWithAction.isDerivedComplete_of_isIso`: if the telescope endomorphisms of
  `∏_ℕ F` are isomorphisms for all `f ∈ I`, every `Extⁿ(P, F)` is derived `I`-complete.
* `TauCeti.Abelian.ExtWithAction.exists_smul_eq_of_comp_eq_zero`: along a reduction
  `0 → F → F → G → 0` modulo `a`, the classes of `Extⁿ(P, F)` that vanish in `Extⁿ(P, G)` are the
  multiples of `a`.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Completion.lean` (declarations
  `New.Variety.IsDerivedComplete.cohomology` and
  `New.Variety.ModShortExact.exists_smul_eq_of_push_eq_zero`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The statements are adapted from these declarations and stated for an object with
  an action in an abelian category with exact countable products; the proof of the first follows
  their plan, through the commutation of `Ext` with the product of countably many copies of `F`.
* [Stacks Project, Tag 091N](https://stacks.math.columbia.edu/tag/091N), for derived
  completeness.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext CategoryTheory.Limits

universe w v u

namespace TauCeti.Abelian.ExtWithAction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {R : Type*} {F : C}

section Complete

variable [CommRing R] (ρ : R →+* End F)

/-- **Derived completeness of `Ext`.** Let `c` exhibit `c.pt` as the product `∏_ℕ F` of countably
many copies of an object `F` with an action `ρ` of `R`, in an abelian category with enough
injectives and exact countable products. If for every `f ∈ I` the endomorphism of `c.pt` with
components `πⱼ - πⱼ₊₁ ≫ ρ(f)` is an isomorphism, then every `Extⁿ(P, F)` is derived
`I`-complete. -/
theorem isDerivedComplete_of_isIso [HasLimitsOfShape (Discrete ℕ) C]
    [HasExactLimitsOfShape (Discrete ℕ) C] [EnoughInjectives C] {I : Ideal R}
    {c : Fan fun _ : ℕ ↦ F} (hc : IsLimit c)
    (h : ∀ f ∈ I, IsIso (Fan.IsLimit.lift hc fun j ↦ c.proj j - c.proj (j + 1) ≫ (ρ f).asHom))
    (P : C) (n : ℕ) : IsDerivedComplete I (ExtWithAction ρ P n) := by
  refine isDerivedComplete_iff.2 fun f hf ↦ ?_
  set T := Fan.IsLimit.lift hc fun j ↦ c.proj j - c.proj (j + 1) ≫ (ρ f).asHom
  have := h f hf
  -- `Extⁿ(P, ∏_ℕ F)` is the product of copies of `Extⁿ(P, F)`.
  let e : Ext.{w} P c.pt n ≃+ (ℕ → ExtWithAction ρ P n) :=
    (addEquivProduct P hc n).trans (AddEquiv.piCongrRight fun _ ↦ (toExt ρ).symm)
  have he (x : Ext.{w} P c.pt n) (j : ℕ) :
      toExt ρ (e x j) = x.comp (mk₀ (c.proj j)) (add_zero n) := by
    simp [e]
  -- Under `e`, composition with the isomorphism `T` is the telescope map of `Extⁿ(P, F)`.
  have hsq : ⇑(telescope (ExtWithAction ρ P n) f) ∘ e =
      e ∘ TauCeti.extAddEquivOfIso (Iso.refl P) (asIso T) n := by
    ext x j
    apply (toExt ρ).injective
    simp only [Function.comp_apply, telescope_apply, sub_eq_add_neg, map_add, map_neg, toExt_smul,
      he, TauCeti.extAddEquivOfIso_apply, Iso.refl_inv, mk₀_id_comp, asIso_hom,
      comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, T, Fan.IsLimit.fac, mk₀_add, mk₀_neg, comp_add,
      comp_neg]
  exact (Function.Bijective.of_comp_iff _ e.bijective).1
    (hsq ▸ e.bijective.comp (AddEquiv.bijective _))

end Complete

section Reduction

variable [Semiring R] (ρ : R →+* End F)

/-- **Reduction modulo `a`.** Let `0 → F → F → G → 0` be short exact, with first map the action
`ρ(a)` of `a ∈ R`. A class of `Extⁿ(P, F)` whose image in `Extⁿ(P, G)` vanishes is a multiple of
`a`. -/
theorem exists_smul_eq_of_comp_eq_zero {G : C} {a : R} {q : F ⟶ G} {hq : (ρ a).asHom ≫ q = 0}
    (hS : (ShortComplex.mk _ _ hq).ShortExact) {P : C} {n : ℕ} (x : ExtWithAction ρ P n)
    (hx : (toExt ρ x).comp (mk₀ q) (add_zero n) = 0) : ∃ y, a • y = x := by
  obtain ⟨y, hy⟩ := covariant_sequence_exact₂ P hS (toExt ρ x) hx
  exact ⟨(toExt ρ).symm y, (toExt ρ).injective (by simpa using hy)⟩

end Reduction

end TauCeti.Abelian.ExtWithAction
