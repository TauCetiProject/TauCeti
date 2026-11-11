/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Canonical
import TauCeti.Algebra.Lie.AdjointAction.Basic

/-!
# Centralizers of the internal Jordan parts

An element centralizes `x` exactly when it centralizes both internal Jordan parts of `x`.
Likewise, a Lie automorphism fixes `x` exactly when it fixes both parts. These comparisons
identify the infinitesimal centralizer and the automorphism stabilizer without choosing a
representation. They are used to compare algebraic centralizers with intersections of the
centralizers of the two parts.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.4.
-/

public section

open LieAlgebra Module.End

namespace TauCeti.LieAlgebra

variable {K L : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]

/-- Centralizing an element is equivalent to centralizing both of its internal Jordan parts. -/
theorem lie_eq_zero_iff_lie_jordanParts_eq_zero (x y : L) :
    ⁅x, y⁆ = 0 ↔ ⁅nilpotentPart K x, y⁆ = 0 ∧ ⁅semisimplePart K x, y⁆ = 0 := by
  constructor
  · intro h
    exact ⟨lie_eq_zero_of_ad_mem_adjoin (ad_nilpotentPart_mem_adjoin K x) h,
      lie_eq_zero_of_ad_mem_adjoin (ad_semisimplePart_mem_adjoin K x) h⟩
  · rintro ⟨hn, hs⟩
    rw [← nilpotentPart_add_semisimplePart K x, add_lie, hn, hs, add_zero]

/-- The infinitesimal centralizer is the intersection of those of the internal Jordan parts. -/
theorem ker_ad_eq_inf_ker_ad_jordanParts (x : L) :
    LinearMap.ker (ad K L x) = LinearMap.ker (ad K L (nilpotentPart K x)) ⊓
      LinearMap.ker (ad K L (semisimplePart K x)) := by
  ext y
  simpa only [LinearMap.mem_ker, ad_apply, Submodule.mem_inf] using
    lie_eq_zero_iff_lie_jordanParts_eq_zero x y

end TauCeti.LieAlgebra

namespace LieEquiv

open TauCeti.LieAlgebra

variable {K L : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]

/-- An automorphism fixes an element exactly when it fixes both internal Jordan parts. -/
theorem apply_eq_self_iff_jordanParts (e : L ≃ₗ⁅K⁆ L) (x : L) :
    e x = x ↔ e (nilpotentPart K x) = nilpotentPart K x ∧
      e (semisimplePart K x) = semisimplePart K x := by
  constructor
  · intro h
    exact ⟨(e.map_nilpotentPart x).symm.trans (congrArg (nilpotentPart K) h),
      (e.map_semisimplePart x).symm.trans (congrArg (semisimplePart K) h)⟩
  · rintro ⟨hn, hs⟩
    calc
      e x = e (nilpotentPart K x + semisimplePart K x) := by
        rw [nilpotentPart_add_semisimplePart]
      _ = x := by rw [map_add, hn, hs, nilpotentPart_add_semisimplePart]

end LieEquiv
