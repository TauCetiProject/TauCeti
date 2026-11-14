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

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter II,
  Proposition 2.6 (the determinant map), and Chapter I, Proposition 3.5 (invertible ideals).
-/

public section

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
  rw [classOf_eq_zero_iff_free, I.free_iff_isPrincipal]

/-- A nonzero finite projective ideal of a domain has zero reduced projective class exactly when
it is principal. The finiteness and projectivity instances are required to express the left-hand
side using `classOf`. -/
theorem classOf_ideal_eq_zero_iff_isPrincipal [IsDomain A] {I : Ideal A} [Module.Finite A I]
    [Module.Projective A I] (hI : I ≠ ⊥) : classOf A I 1 = 0 ↔ I.IsPrincipal := by
  have : Module.Invertible A I := I.moduleInvertible_of_ne_bot hI
  exact classOf_submodule_eq_zero_iff_isPrincipal I

end FiniteProjectiveModules

end TauCeti
