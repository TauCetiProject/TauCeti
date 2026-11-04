/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Length of a quotient of a discrete valuation ring

The length of `R/I` for a nonzero ideal of a discrete valuation ring is the exponent of its
maximal ideal in `I`. This is the local length calculation used for different ideals.
-/

public section

namespace Ideal

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The length of the quotient by a nonzero ideal of a discrete valuation ring is its
multiplicity at the maximal ideal. -/
theorem length_quotient_eq_multiplicity (I : Ideal R) (hI : I ≠ ⊥) :
    Module.length R (R ⧸ I) = multiplicity (maximalIdeal R) I := by
  have hgen : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro hzero
    apply hI
    rw [← span_singleton_generator I, hzero, span_singleton_zero]
  rw [← span_singleton_generator I, ← Ring.ord]
  exact (Ring.ord_eq_addVal _).trans
    (TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton hgen)

end Ideal

namespace TauCeti.Ring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring a nonzero element is squarefree exactly when the quotient by
its principal ideal has length at most one. -/
theorem squarefree_iff_ord_le_one {f : R} (hf : f ≠ 0) :
    Squarefree f ↔ Ring.ord R f ≤ 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_def' u hπ n]
  constructor
  · intro h
    obtain h | h := h.of_mul_right.eq_zero_or_one_of_pow_of_not_isUnit hπ.not_isUnit <;>
      simp [h]
  · intro hn
    have hn : n ≤ 1 := by exact_mod_cast hn
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · simp
    · simpa using (associated_unit_mul_left π u u.isUnit).squarefree_iff.mpr hπ.squarefree

end TauCeti.Ring
