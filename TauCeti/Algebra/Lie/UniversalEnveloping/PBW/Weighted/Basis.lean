/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Weighted.Basic

/-!
# Coordinates on weighted PBW quotients

The ordered PBW monomials of weight below the cutoff form a basis of the weighted
truncation quotient. Its coordinates are exactly the surviving PBW coefficients.
This makes dimensions and explicit quotient calculations accessible without choosing
an arbitrary basis of the finite target.

The construction uses `Module.Basis.pbwBasis` and Mathlib's
`LinearIndependent.disjoint_span_image` and `Module.Basis.mk`.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

namespace Module.Basis

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι]
  (b : Basis ι R L) (w : ι → ℕ)
  (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0) (N : ℕ)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Q" => U ⧸ b.weightedPBWIdeal w hbracket N

/-- The PBW monomials below the cutoff form a basis of the weighted quotient. -/
noncomputable def weightedPBWQuotientBasis :
    Basis {n : ι →₀ ℕ // Finsupp.weight w n < N} R Q := by
  classical
  let q := (Ideal.Quotient.mkₐ R (b.weightedPBWIdeal w hbracket N)).toLinearMap
  apply Basis.mk ((b.pbwBasis.linearIndependent.comp Subtype.val Subtype.val_injective).map
    (f := q) ?_) ?_
  · have hker : LinearMap.ker q = b.weightedPBWFiltration w N := by
      ext a
      simp [q, Ideal.Quotient.eq_zero_iff_mem]
    rw [hker, weightedPBWFiltration_def]
    have hrange : Set.range (b.pbwBasis ∘
        (Subtype.val : {n : ι →₀ ℕ // Finsupp.weight w n < N} → _)) =
        b.pbwBasis '' {n | Finsupp.weight w n < N} := by
      simp only [Set.range_comp, Subtype.range_val_subtype]
    rw [hrange]
    exact b.pbwBasis.linearIndependent.disjoint_span_image
      (Set.disjoint_left.mpr fun _ hlt hle ↦ Nat.not_lt_of_ge hle hlt)
  · have hrange : Set.range (q ∘ b.pbwBasis ∘
        (Subtype.val : {n : ι →₀ ℕ // Finsupp.weight w n < N} → _)) =
        (fun n ↦ Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (b.pbwBasis n)) ''
          {n | Finsupp.weight w n < N} := by
      simp only [Set.range_comp, Subtype.range_val_subtype, ← Set.image_comp]
      rfl
    rw [hrange, b.span_image_pbwBasis_quotient_weightedPBWIdeal w hbracket N]

/-- Each quotient basis vector is the class of the corresponding ordered PBW monomial. -/
@[simp]
theorem weightedPBWQuotientBasis_apply (n : {n : ι →₀ ℕ // Finsupp.weight w n < N}) :
    b.weightedPBWQuotientBasis w hbracket N n =
      Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (b.pbwBasis n) := by
  classical
  unfold weightedPBWQuotientBasis
  exact Basis.mk_apply _ _ n

/-- Passing to the weighted quotient keeps precisely the PBW coefficients below the cutoff. -/
@[simp]
theorem weightedPBWQuotientBasis_repr_mk (a : U)
    (n : {n : ι →₀ ℕ // Finsupp.weight w n < N}) :
    (b.weightedPBWQuotientBasis w hbracket N).repr
      (Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) a) n = b.pbwBasis.repr a n := by
  classical
  let q := (Ideal.Quotient.mkₐ R (b.weightedPBWIdeal w hbracket N)).toLinearMap
  have h : (b.weightedPBWQuotientBasis w hbracket N).coord n ∘ₗ q =
      b.pbwBasis.coord n := by
    apply b.pbwBasis.ext
    intro m
    by_cases hm : Finsupp.weight w m < N
    · have heq := b.weightedPBWQuotientBasis_apply w hbracket N ⟨m, hm⟩
      simp only [LinearMap.comp_apply, q, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, ← heq, Basis.coord_apply, Basis.repr_self]
      simp [Finsupp.single_apply, Subtype.ext_iff]
    · have hz : Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (b.pbwBasis m) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          ((b.mem_weightedPBWIdeal_iff w hbracket N _).mpr
            (b.pbwBasis_mem_weightedPBWFiltration w (by omega)))
      have hmn : m ≠ n.val := by rintro rfl; exact hm n.property
      simp [q, hz, Basis.coord_apply, hmn]
  exact LinearMap.congr_fun h a

end Module.Basis
