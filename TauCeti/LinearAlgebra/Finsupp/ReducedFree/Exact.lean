/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Finsupp.ReducedFree.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Reduced free modules and collapsing a based subset

If a based map makes identifications only over the basepoint, its kernel on reduced free modules
is spanned by the generators of that fibre (`TauCeti.ReducedFreeModule.ker_map_eq_span`). Thus
collapsing a based subset gives a short exact sequence of reduced free modules, and the quotient
by that span is linearly equivalent to the reduced free module on the collapsed type
(`TauCeti.ReducedFreeModule.quotientSpanEquiv`).

This is the degreewise algebra behind the reduced free simplicial module sequence of a
cofibration and its cofiber. No flatness assumption on the coefficient ring is needed.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter III.
-/

public section

namespace TauCeti.ReducedFreeModule

open Function Set

noncomputable section

universe u v w

variable (R : Type*) [Ring R] {α : Type u} {β : Type v} {γ : Type w}
  {a : α} {b : β} {c : γ}

/-- If a based map is injective away from its basepoint fibre, its reduced free kernel is
spanned by the generators of that fibre. Surjectivity of the based map is not required. -/
lemma ker_map_eq_span (f : α → β) (hf : f a = b)
    (hi : ∀ x y, f x = f y → f x ≠ b → x = y) :
    LinearMap.ker (map R f hf) = Submodule.span R (mk R '' (f ⁻¹' {b})) := by
  classical
  let : Nonempty α := ⟨a⟩
  let P := Submodule.span R (mk R (a := a) '' (f ⁻¹' {b}))
  have hP : P ≤ LinearMap.ker (map R f hf) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    simp_all
  let s : ReducedFreeModule R b →ₗ[R] (ReducedFreeModule R a ⧸ P) :=
    lift R (fun y ↦ if y = b then 0 else P.mkQ (mk R (Function.invFun f y))) (by simp)
  have hs : s.comp (map R f hf) = P.mkQ := by
    ext x
    by_cases hx : f x = b
    · have hmem : mk R x ∈ P := Submodule.subset_span ⟨x, hx, rfl⟩
      simp [s, hx, (Submodule.Quotient.mk_eq_zero _).2 hmem]
    · have hinv : Function.invFun f (f x) = x :=
        hi _ _ (Function.invFun_eq ⟨x, rfl⟩) (by simpa [Function.invFun_eq ⟨x, rfl⟩] using hx)
      simp [s, hx, hinv]
  apply le_antisymm _ hP
  intro v hv
  have hzero : P.mkQ v = 0 := by
    rw [← hs]
    simp [LinearMap.mem_ker.1 hv]
  exact (Submodule.Quotient.mk_eq_zero _).1 hzero

/-- Exactness of reduced free modules for a collapse map: the first map parametrizes the
basepoint fibre, and the second map makes no other identifications. The first map need not
be injective, nor the second surjective, for exactness at the middle term. -/
lemma exact_map (i : α → β) (f : β → γ) (hi : i a = b) (hf : f b = c)
    (hrange : Set.range i = f ⁻¹' {c})
    (hinj : ∀ x y, f x = f y → f x ≠ c → x = y) :
    Function.Exact (map R i hi) (map R f hf) := by
  rw [LinearMap.exact_iff, ker_map_eq_span R f hf hinj, range_map, hrange]

/-- The reduced free module on a collapsed pointed type is the quotient by the span of the
collapsed generators. -/
def quotientSpanEquiv (f : α → β) (hf : f a = b) (hs : Surjective f)
    (hi : ∀ x y, f x = f y → f x ≠ b → x = y) :
    (ReducedFreeModule R a ⧸ Submodule.span R (mk R '' (f ⁻¹' {b}))) ≃ₗ[R]
      ReducedFreeModule R b :=
  (Submodule.quotEquivOfEq _ _ (ker_map_eq_span R f hf hi).symm).trans
    ((map R f hf).quotKerEquivOfSurjective (map_surjective R f hf hs))

/-- The quotient comparison agrees with the induced map on every representative. -/
@[simp]
lemma quotientSpanEquiv_mk (f : α → β) (hf : f a = b) (hs : Surjective f)
    (hi : ∀ x y, f x = f y → f x ≠ b → x = y) (v : ReducedFreeModule R a) :
    quotientSpanEquiv R f hf hs hi (Submodule.Quotient.mk v) = map R f hf v := by
  simp [quotientSpanEquiv]

/-- The inverse quotient comparison on the image of an arbitrary reduced free element. -/
@[simp]
lemma quotientSpanEquiv_symm_map (f : α → β) (hf : f a = b) (hs : Surjective f)
    (hi : ∀ x y, f x = f y → f x ≠ b → x = y) (v : ReducedFreeModule R a) :
    (quotientSpanEquiv R f hf hs hi).symm (map R f hf v) = Submodule.Quotient.mk v := by
  apply (quotientSpanEquiv R f hf hs hi).injective
  simp

end

end TauCeti.ReducedFreeModule
