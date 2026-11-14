/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import TauCeti.RingTheory.PicardGroup.RankOne

/-!
# Projective classes of invertible modules

For an invertible module `M` over a commutative ring `A`, the reduced class `[M] - [A]` in
projective `K₀(A)` vanishes exactly when `M` is free. One direction is the stable-freeness
criterion `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff`: a stably free invertible module
is free (`Module.free_of_isStablyFree_of_invertible`). For invertible submodules, and in
particular nonzero finite projective ideals of a domain, freeness is principality.

## Main results

* `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff_free`: an invertible module has zero
  reduced class exactly when it is free.
* `TauCeti.FiniteProjectiveModules.classOf_submodule_eq_zero_iff_isPrincipal`: an invertible
  submodule has zero reduced class exactly when it is principal.
* `TauCeti.FiniteProjectiveModules.classOf_ideal_eq_zero_iff_isPrincipal`: a nonzero finite
  projective ideal of a domain has zero reduced class exactly when it is principal.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter I, Proposition 3.4.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

namespace FiniteProjectiveModules

universe u

variable {A : Type u} [CommRing A]

/-- An invertible module has zero reduced projective class exactly when it is free. -/
theorem classOf_eq_zero_iff_free {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : classOf A M 1 = 0 ↔ Module.Free A M := by
  constructor
  · rw [classOf_eq_zero_iff]
    rintro ⟨k, ⟨e⟩⟩
    -- A stably free invertible module is free.
    have := Module.Free.of_equiv e.symm
    have : Module.IsStablyFree A M := .of_free_prod A _ (Fin k → A)
    exact Module.free_of_isStablyFree_of_invertible A M
  · intro h
    obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp h
    rw [classOf_congr e]
    simp [classOf_def]

/-- An invertible submodule has zero reduced projective class exactly when it is principal. -/
theorem classOf_submodule_eq_zero_iff_isPrincipal {P : Type u} [AddCommGroup P] [Module A P]
    (I : Submodule A P) [Module.Invertible A I] : classOf A I 1 = 0 ↔ I.IsPrincipal := by
  rw [classOf_eq_zero_iff_free, Module.Invertible.free_iff_linearEquiv]
  constructor
  · rintro ⟨f⟩
    exact ⟨_, Submodule.eq_span_singleton_of_surjective f.symm.surjective⟩
  · rintro ⟨x, hx⟩
    -- Multiplication by the generator maps `A` onto `I`, hence isomorphically.
    let f : A →ₗ[A] I :=
      (LinearMap.toSpanSingleton A P x).codRestrict I fun a ↦ by
        rw [hx]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hx ▸ hy : y ∈ Submodule.span A {x})
      exact ⟨a, rfl⟩
    exact ⟨(LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hf)).symm⟩

/-- A nonzero finite projective ideal of a domain has zero reduced projective class exactly when
it is principal. The finiteness and projectivity instances are required to express the left-hand
side using `classOf`. -/
theorem classOf_ideal_eq_zero_iff_isPrincipal [IsDomain A] {I : Ideal A} [Module.Finite A I]
    [Module.Projective A I] (hI : I ≠ ⊥) : classOf A I 1 = 0 ↔ I.IsPrincipal := by
  -- The rank of `I` is constant, and it is one at the generic point.
  have : Module.Invertible A I := .of_rankAtStalk_eq_one fun p ↦ by
    have hle : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ A⁰ := fun _ hx ↦
      mem_nonZeroDivisors_of_ne_zero hx
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat I (bot_le : ⊥ ≤ p), Module.rankAtStalk,
      IsLocalization.finrank_eq (Localization.AtPrime (⊥ : PrimeSpectrum A).asIdeal) _ hle,
      IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ I) hle]
    refine le_antisymm ((Submodule.finrank_le I).trans (by simp)) ?_
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hx⟩, by simpa using hx0⟩
  exact classOf_submodule_eq_zero_iff_isPrincipal I

end FiniteProjectiveModules

end TauCeti
