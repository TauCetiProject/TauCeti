/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.Data.ENat.Map
public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscreteValuationRing

/-!
# The μ- and λ-invariants as Newton polygon data

Let `O` be a discrete valuation ring with normalised additive valuation `addVal O`, and let
`f ∈ O⟦X⟧`. Its μ-invariant `PowerSeries.muInvariant f` is the least valuation of a coefficient
and its λ-invariant `PowerSeries.lambdaInvariant f` is the first index attaining it. When `O` is
complete for its maximal ideal and `f ≠ 0`, these are the invariants of the factorisation
`f = π ^ μ(f) · u · P` with `P` distinguished of degree `λ(f)`, by
`PowerSeries.exists_pow_mul_distinguished_mul_unit`. The polygon results below need neither
hypothesis.

Embed the coefficients along a ring homomorphism `φ : O →+* S`, for example into the fraction
field, and fix a real additive valuation `v` on `S` extending `addVal O`, so that
`v (φ x) = addVal O x` for every `x : O`, reading `ℕ∞` in `WithTop ℝ` through
`ENat.map Nat.cast`. Then the
Newton polygon of `f.map φ` is read off from these invariants:

* `μ(f)` is the minimum height of the Newton polygon;
* `λ(f)` is the first absolute index at which the Newton polygon attains that minimum.

So for `f ≠ 0` the horizontal supporting line at height `μ(f)` meets the polygon in a face
starting at `λ(f)`. This face may be an infinite ray, as for `∑ Xⁿ`; its right endpoint is not
needed to recover `μ(f)` and `λ(f)`, and is not used here. The left endpoint is absolute: it
includes any order of vanishing of `f` at zero. The zero series has `μ = ⊤`, `λ = 0` and the
all-infinite polygon; there is no finite supporting line, but the two statements above hold for
it as well.

## Main results

* `PowerSeries.muInvariant_le_newtonPolygon_map`: every Newton polygon height is at least
  `μ(f)`.
* `PowerSeries.newtonPolygon_map_lambdaInvariant`: the Newton polygon has height `μ(f)`
  at `λ(f)`.
* `PowerSeries.isLeast_range_newtonPolygon_map`: `μ(f)` is the minimum Newton polygon height.
* `PowerSeries.isLeast_setOf_newtonPolygon_map_eq`: `λ(f)` is the least index at which the
  Newton polygon has height `μ(f)`.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open IsDiscreteValuationRing TauCeti

namespace PowerSeries

variable {O S : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Ring S]
  {φ : O →+* S} {v : AddValuation S (WithTop ℝ)}

variable (hv : ∀ x, v (φ x) = (addVal O x).map ((↑) : ℕ → ℝ))
include hv

/-- The coefficient heights of a series over a discrete valuation ring are nonnegative, hence
admissible. -/
private theorem isAdmissible_addValuation_coeff_map (f : O⟦X⟧) :
    IsAdmissible fun n => v (coeff n (f.map φ)) :=
  isAdmissible_iff.mpr ⟨0, 0, fun n => by
    rw [coeff_map, hv, zero_mul, add_zero, ← Nat.cast_zero, ENat.coe_le_map_iff Nat.strictMono_cast,
      Nat.cast_zero]
    exact zero_le⟩

/-- The horizontal line at a finite μ-invariant supports the coefficient heights. -/
private theorem isSupportingLine_addValuation_coeff_map {f : O⟦X⟧} {m : ℕ}
    (hμ : f.muInvariant = m) : IsSupportingLine (fun k => v (coeff k (f.map φ))) 0 m :=
  isSupportingLine_iff_forall.mpr fun k => by
    rw [coeff_map, hv, zero_mul, add_zero, ENat.coe_le_map_iff Nat.strictMono_cast, ← hμ]
    exact f.muInvariant_le_addVal_coeff k

/-- Every height of the Newton polygon of `f` is at least the μ-invariant of `f`. -/
theorem muInvariant_le_newtonPolygon_map (f : O⟦X⟧) (n : ℕ) :
    f.muInvariant.map ((↑) : ℕ → ℝ) ≤ (f.map φ).newtonPolygon v n := by
  induction hμ : f.muInvariant using ENat.recTopCoe with
  | top =>
    rw [muInvariant_eq_top_iff.mp hμ, map_zero, newtonPolygon_zero]
    exact le_rfl
  | coe m =>
    simpa using le_newtonPolygon (isConvexSeq_affine m 0)
      (isSupportingLine_iff_forall.mp (isSupportingLine_addValuation_coeff_map hv hμ)) n

/-- The Newton polygon of `f` has height `μ(f)` at the index `λ(f)`. -/
theorem newtonPolygon_map_lambdaInvariant (f : O⟦X⟧) :
    (f.map φ).newtonPolygon v f.lambdaInvariant = f.muInvariant.map ((↑) : ℕ → ℝ) := by
  refine le_antisymm ?_ (muInvariant_le_newtonPolygon_map hv f _)
  refine (newtonPolygon_le (isAdmissible_addValuation_coeff_map hv f) _).trans_eq ?_
  rw [coeff_map, hv, addVal_coeff_lambdaInvariant]

/-- The μ-invariant of `f` is the minimum height of the Newton polygon of `f`. -/
theorem isLeast_range_newtonPolygon_map (f : O⟦X⟧) :
    IsLeast (Set.range ((f.map φ).newtonPolygon v)) (f.muInvariant.map ((↑) : ℕ → ℝ)) :=
  ⟨⟨_, newtonPolygon_map_lambdaInvariant hv f⟩,
    Set.forall_mem_range.mpr (muInvariant_le_newtonPolygon_map hv f)⟩

/-- The λ-invariant of `f` is the first absolute index at which the Newton polygon of `f`
attains its minimum height `μ(f)`. The set of such indices may be infinite. -/
theorem isLeast_setOf_newtonPolygon_map_eq (f : O⟦X⟧) :
    IsLeast {n | (f.map φ).newtonPolygon v n = f.muInvariant.map ((↑) : ℕ → ℝ)}
      f.lambdaInvariant := by
  refine ⟨newtonPolygon_map_lambdaInvariant hv f, fun n hn => ?_⟩
  induction hμ : f.muInvariant using ENat.recTopCoe with
  | top =>
    rw [muInvariant_eq_top_iff.mp hμ, lambdaInvariant_zero]
    exact Nat.zero_le n
  | coe m =>
    -- The horizontal line at height `μ(f)` supports the coefficient heights, and the polygon
    -- touches it no earlier than the coefficients do.
    have hface : n ∈ supportingFace ((f.map φ).newtonPolygon v) 0 m := by
      rw [mem_supportingFace, zero_mul, add_zero]
      simpa [hμ] using hn
    obtain ⟨k, hkn, hk⟩ := (isLowerConvexEnvelope_newtonPolygon
      (isAdmissible_addValuation_coeff_map hv f)).exists_le_mem_supportingFace
      (isSupportingLine_addValuation_coeff_map hv hμ) hface
    rw [mem_supportingFace, zero_mul, add_zero, coeff_map, hv, eq_comm,
      ENat.coe_eq_map_iff Nat.cast_injective, ← hμ, eq_comm] at hk
    exact (lambdaInvariant_le hk).trans hkn

end PowerSeries
