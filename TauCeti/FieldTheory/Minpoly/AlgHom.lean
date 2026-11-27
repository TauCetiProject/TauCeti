/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Minimal-polynomial roots as values of algebra homomorphisms

For a commutative integral algebra `B` over an algebraically closed field `K`, the roots of
`minpoly K y` are precisely the values `χ y` for `K`-algebra homomorphisms `χ : B →ₐ[K] K`.
This permits testing conditions on the roots without choosing a presentation of `B`.
No reducedness or finite-dimensionality assumption on `B` is needed.

A root `r` makes `y - r` a nonunit: its product with the complementary factor of the minimal
polynomial is zero, while that factor does not annihilate `y`. A maximal ideal containing
`y - r` then gives the required homomorphism, since its residue field is integral over `K`.

## References

* The Stacks Project, [Tag 09GU](https://stacks.math.columbia.edu/tag/09GU), for embeddings of
  algebraic field extensions into an algebraic closure.
-/

public section

namespace TauCeti

open Polynomial

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]
  [IsAlgClosed K] [Algebra.IsIntegral K B]

/-- In a commutative integral algebra over an algebraically closed field, a scalar is a root of
an element's minimal polynomial exactly when it is the value of an algebra homomorphism. -/
theorem isRoot_minpoly_iff_exists_algHom {y : B} {r : K} :
    (minpoly K y).IsRoot r ↔ ∃ χ : B →ₐ[K] K, χ y = r := by
  constructor
  · intro hr
    have hy := Algebra.IsIntegral.isIntegral (R := K) y
    let q := minpoly K y /ₘ (X - C r)
    have hq : (X - C r) * q = minpoly K y := mul_divByMonic_eq_iff_isRoot.mpr hr
    have hqm : q.Monic := (monic_X_sub_C r).of_mul_monic_left (hq ▸ minpoly.monic hy)
    have hqn : aeval y q ≠ 0 :=
      minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly hy hqm
        ⟨hqm.ne_zero, X - C r, not_isUnit_X_sub_C r, by rw [mul_comm, hq]⟩
    have hu : ¬ IsUnit (y - algebraMap K B r) := by
      intro hu
      apply hqn
      apply hu.mul_right_eq_zero.mp
      simpa only [map_mul, map_sub, aeval_X, aeval_C, minpoly.aeval] using
        congrArg (aeval y) hq
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {y - algebraMap K B r}) (fun h ↦ hu (Ideal.span_singleton_eq_top.mp h))
    let χ := (IsAlgClosed.lift : B ⧸ m →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)
    refine ⟨χ, ?_⟩
    have hmem : y - algebraMap K B r ∈ m := hle (Ideal.subset_span (by simp))
    have hz : χ (y - algebraMap K B r) = 0 := by
      simp only [χ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero] using hz
  · rintro ⟨χ, rfl⟩
    simpa only [IsRoot.def, coe_aeval_eq_eval] using
      minpoly.aeval_algHom K χ y

end TauCeti
