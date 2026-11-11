/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.ExpLog
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.LogDet
import TauCeti.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Traces of powers and `det (1 - a A)` in Novikov series

Let `K` be a commutative `ℚ`-algebra without zero divisors, for instance `ℚ`, `H` an additive
commutative monoid with a period homomorphism `N : H →+ ℝ`, and `a` a Novikov series of the
positive ideal, for instance a monomial `e^h` with `N h > 0`. For a square matrix `A` over `K`,
`det (1 - a A)` (the reversed characteristic polynomial `Matrix.charpolyRev A` evaluated at `a`)
is a principal unit of the nonnegative subring, and

`log det (1 - a A) = -∑ₖ tr (Aᵏ) aᵏ / k`,  that is,  `exp (∑ₖ tr (Aᵏ) aᵏ / k) = det (1 - a A)⁻¹`.

This is the trace/determinant identity for zeta functions of linear maps. Applied to the action
`φ_*` of a map `φ` on each rational homology group `Hᵢ(S; ℚ)`, it identifies the exponential of
the series `∑ₖ L(φᵏ) tᵏ / k` of alternating traces `L(φᵏ) = ∑ᵢ (-1) ^ i tr (φ_*ᵏ | Hᵢ(S; ℚ))`
with the alternating product `∏ᵢ det (1 - t φ_* | Hᵢ(S; ℚ)) ^ (-(-1) ^ i)`. The Lefschetz fixed
point theorem, which makes `L(φᵏ)` a count of fixed points, is not part of this file.

The identity is proved after extending the coefficients to an algebraic closure `L` of the field
of fractions of `K`. Over `L` the characteristic polynomial of `A` splits, and the identity is
`IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev_of_splits`. The coefficient extension
`Nov(K, H, N) → Nov(L, H, N)` is injective and continuous, so it commutes with the logarithm and
with the summation of the trace series, which brings the identity back to `K`.

## Main results

* `TauCeti.NovikovSeries.aeval_charpolyRev_sub_one_mem_posIdeal`: for `a` in the positive ideal,
  `det (1 - a A)` is a principal unit, that is `det (1 - a A) - 1` lies in the positive ideal.
* `TauCeti.NovikovSeries.hasSum_log_aeval_charpolyRev`: for `a` in the positive ideal,
  `log det (1 - a A) = -∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`.
* `TauCeti.NovikovSeries.exp_tsum_trace_mul_aeval_charpolyRev`: the same identity in the
  Novikov series, as `exp (∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)) * det (1 - a A) = 1`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), 369–396.
-/

public section

noncomputable section

open Polynomial Filter

namespace TauCeti.NovikovSeries

variable {H K : Type*} [AddCommMonoid H] {N : H →+ ℝ} [CommRing K] [IsDomain K] [Algebra ℚ K]
  {n : Type*} [Fintype n] [DecidableEq n]

omit [IsDomain K] [Algebra ℚ K] in
/-- For `a` in the positive ideal, `det (1 - a A) - 1` lies in the positive ideal. -/
theorem aeval_charpolyRev_sub_one_mem_posIdeal {a : nonnegSubring K N}
    (ha : a ∈ posIdeal K N) (A : Matrix n n K) :
    aeval a A.charpolyRev - 1 ∈ posIdeal K N := by
  -- `det (1 - X A) = 1 + X q` for a polynomial `q`.
  obtain ⟨q, hq⟩ := X_dvd_iff.2 (by simp [coeff_zero_eq_eval_zero] :
    (A.charpolyRev - 1).coeff 0 = 0)
  have h : A.charpolyRev = 1 + X * q := by rw [← hq]; ring
  rw [h, _root_.map_add, _root_.map_one, _root_.map_mul, aeval_X, add_sub_cancel_left]
  exact (posIdeal K N).mul_mem_right _ ha

/-- **The logarithm of `det (1 - a A)`.** For a square matrix `A` over a `ℚ`-algebra `K` without
zero divisors and a series `a` of the positive ideal, the logarithm of `det (1 - a A)` is
`-∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1)`. -/
theorem hasSum_log_aeval_charpolyRev {a : nonnegSubring K N} (ha : a ∈ posIdeal K N)
    (A : Matrix n n K) :
    HasSum (fun k : ℕ ↦ -(((k + 1 : ℕ) : ℚ)⁻¹ • ((A ^ (k + 1)).trace • a ^ (k + 1))))
      (NormedSpace.log (aeval a A.charpolyRev)) := by
  have ha' := isTopologicallyNilpotent_of_mem_posIdeal' ha
  set f : ℕ → nonnegSubring K N := fun k ↦ -(((k + 1 : ℕ) : ℚ)⁻¹ •
    ((A ^ (k + 1)).trace • a ^ (k + 1)))
  -- Each term is a multiple of `a ^ (k + 1)`, so the series converges.
  have hsum : Summable f := by
    simpa [f, Algebra.smul_def, mul_assoc] using ((summable_nat_add_iff 1).2
      (ha'.summable_mul_pow fun k ↦ algebraMap ℚ (nonnegSubring K N) (k : ℚ)⁻¹ *
        algebraMap K (nonnegSubring K N) (A ^ k).trace)).neg
  -- Extend the coefficients to an algebraic closure `L` of the field of fractions of `K`.
  let L := AlgebraicClosure (FractionRing K)
  let ι : K →+* L := algebraMap K L
  let ψ := mapNonnegSubring (N := N) (N' := N) ι (AddMonoidHom.id H) exists_period_rescale_id
  have hψc : Continuous ψ := continuous_mapNonnegSubring ..
  have hu := isTopologicallyNilpotent_of_mem_posIdeal' (aeval_charpolyRev_sub_one_mem_posIdeal ha A)
  have hmap : ψ (aeval a A.charpolyRev) = aeval (ψ a) (A.map ι).charpolyRev := by
    rw [map_aeval_eq_aeval_map (mapNonnegSubring_comp_algebraMap ..).symm,
      Matrix.charpolyRev_map]
  -- Over `L` the identity holds, and `ψ` maps both sides of the identity over `K` to it.
  have hL := IsTopologicallyNilpotent.hasSum_log_aeval_charpolyRev_of_splits (A := A.map ι)
    (IsTopologicallyNilpotent.map hψc ha') (IsAlgClosed.splits _)
  have key : ψ (∑' k, f k) = ψ (NormedSpace.log (aeval a A.charpolyRev)) := by
    rw [hu.map_log ψ hψc, hmap]
    refine (hsum.hasSum.map ψ hψc).unique (hL.congr_fun fun k ↦ ?_)
    simp only [f, ψ, Function.comp_apply, _root_.map_neg, map_rat_smul, mapNonnegSubring_smul,
      _root_.map_pow, AddMonoidHom.map_trace, Matrix.map_pow]
  rw [← mapNonnegSubring_injective _ _ _ (FaithfulSMul.algebraMap_injective K L)
    Function.injective_id key]
  exact hsum.hasSum

/-- **The trace/determinant identity.** For a square matrix `A` over a `ℚ`-algebra `K` without
zero divisors and a series `a` of the positive ideal, `exp (∑ₖ tr (Aᵏ⁺¹) aᵏ⁺¹ / (k + 1))` is the
inverse of `det (1 - a A)` in the Novikov series. -/
theorem exp_tsum_trace_mul_aeval_charpolyRev {a : nonnegSubring K N} (ha : a ∈ posIdeal K N)
    (A : Matrix n n K) :
    NormedSpace.exp (∑' k : ℕ, ((k + 1 : ℕ) : ℚ)⁻¹ •
        ((A ^ (k + 1)).trace • (a : NovikovSeries K H N) ^ (k + 1))) *
      aeval (a : NovikovSeries K H N) A.charpolyRev = 1 := by
  set u := aeval a A.charpolyRev
  have hu1 := aeval_charpolyRev_sub_one_mem_posIdeal ha A
  have hu := isTopologicallyNilpotent_of_mem_posIdeal' hu1
  have hlog : -NormedSpace.log u ∈ posIdeal K N := neg_mem (hu.log_mem hu1)
  have hlog' := isTopologicallyNilpotent_of_mem_posIdeal' hlog
  -- The trace series is the image of `-log u` in the Novikov series.
  have hsum : HasSum (fun k : ℕ ↦ ((k + 1 : ℕ) : ℚ)⁻¹ •
      ((A ^ (k + 1)).trace • (a : NovikovSeries K H N) ^ (k + 1)))
      (-NormedSpace.log u : nonnegSubring K N) := by
    convert (hasSum_log_aeval_charpolyRev ha A).neg.map (nonnegSubring K N).subtype
      continuous_subtype_val using 1
    · funext k
      simp
    · simp [u]
  -- In the nonnegative subring, `exp (-log u) * u = exp (-log u) * exp (log u) = 1`.
  have hinv : NormedSpace.exp (-NormedSpace.log u) * u = 1 := by
    calc NormedSpace.exp (-NormedSpace.log u) * u
        = NormedSpace.exp (-NormedSpace.log u) * NormedSpace.exp (NormedSpace.log u) := by
          rw [hu.exp_log]
      _ = 1 := by rw [← hlog'.exp_add hu.log, neg_add_cancel, NormedSpace.exp_zero]
  rw [hsum.tsum_eq, ← coe_exp_of_mem_posIdeal hlog, ← coe_aeval_nonnegSubring, ← Subring.coe_mul,
    hinv, Subring.coe_one]

end TauCeti.NovikovSeries
