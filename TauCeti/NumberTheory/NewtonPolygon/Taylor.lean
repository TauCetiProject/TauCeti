/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Convex.Sequence.Derivative

/-!
# Newton polygons under a translation of the unknown

Let `v` be a real additive valuation on a ring `R` and `P = ∑ aₙ Yⁿ ∈ R[Y]`. The translation
`Y ↦ Y + c`, the Taylor shift `Polynomial.taylor c`, has coefficients
`∑ₖ (k + m).choose m • (a_{k + m} cᵏ)`. If `v c ≥ -σ`, each such term lies on or above the
supporting line of slope `σ` of `P`, so this line stays below the coefficient heights of
`P (Y + c)`. Translating back by `-c` gives the reverse bound: the supporting values of slope
`σ ≥ -v c` do not change.

If `v c > -σ`, the supporting values agree on a neighbourhood of `σ`, so the one-sided
derivatives at `σ`, which are minus the endpoints of the face of slope `σ`, agree as well. Hence
the slopes `σ > -v c` keep their multiplicities. For a split polynomial these are the slopes of
the roots `r` with `v r < v c`, for which `v (r - c) = v r`.

No commutativity, completeness or discreteness is used.

## Main results

* `Polynomial.supportingValue_newtonPolygon_taylor_of_le`: translating the unknown by `c` does
  not change the supporting values of the Newton polygon at slopes `σ ≥ -v c`.
* `Polynomial.count_newtonSlopes_taylor_of_lt`: nor the multiplicity of a slope `σ > -v c`.
* `Polynomial.filter_newtonSlopes_taylor_lt_addValuation`: the slopes `σ > -v c`, counted with
  multiplicity, are the same for `P` and `P (Y + c)`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Filter Set Topology TauCeti

namespace Polynomial

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- If `v c ≥ -σ`, the supporting value at slope `σ` of the coefficient heights of `P (Y + c)` is
at least that of `P`: each term `a_{k + m} cᵏ` of the `m`-th coefficient lies on or above the
supporting line of `P` at `m`. -/
private theorem supportingValue_le_supportingValue_taylor (P : R[X]) {σ : ℝ} {c : R}
    (hc : ((-σ : ℝ) : WithTop ℝ) ≤ v c) :
    supportingValue (fun n => v (P.coeff n)) σ ≤
      supportingValue (fun n => v ((taylor c P).coeff n)) σ := by
  -- A real lower bound for `P` is one for `P (Y + c)`.
  have key (μ : ℝ) (hμ : (μ : EReal) ≤ supportingValue (fun n => v (P.coeff n)) σ) :
      (μ : EReal) ≤ supportingValue (fun n => v ((taylor c P).coeff n)) σ := by
    rw [coe_le_supportingValue_iff] at hμ ⊢
    intro m
    rw [coeff_taylor_eq_sum (Nat.lt_add_one P.natDegree)]
    refine v.map_le_sum fun k _ => le_trans ?_ (v.le_map_nsmul _ _)
    rw [v.map_mul, v.map_pow]
    calc ((μ + σ * m : ℝ) : WithTop ℝ)
        = ((μ + σ * ↑(k + m) : ℝ) : WithTop ℝ) + k • ((-σ : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
          congr 1
          push_cast
          ring
      _ ≤ v (P.coeff (k + m)) + k • v c := add_le_add (hμ _) (nsmul_le_nsmul_right hc k)
  induction h : supportingValue (fun n => v (P.coeff n)) σ using EReal.rec with
  | bot => exact bot_le
  | coe μ => exact key μ h.ge
  | top =>
    refine ((EReal.eq_top_iff_forall_lt _).mpr fun μ => ?_).ge
    exact (EReal.coe_lt_coe_iff.mpr (lt_add_one μ)).trans_le (key (μ + 1) (by simp [h]))

variable (P : R[X]) {σ : ℝ} {c : R}

/-- **Translation of the Newton polygon.** Translating the unknown by `c` does not change the
supporting value of the Newton polygon at any slope `σ ≥ -v c`: the Newton polygons of `P` and of
`P (Y + c)` have the same supporting lines of slope at least `-v c`. -/
theorem supportingValue_newtonPolygon_taylor_of_le (hc : ((-σ : ℝ) : WithTop ℝ) ≤ v c) :
    supportingValue ((taylor c P).newtonPolygon v) σ = supportingValue (P.newtonPolygon v) σ := by
  rw [supportingValue_newtonPolygon, supportingValue_newtonPolygon]
  refine le_antisymm ?_ (supportingValue_le_supportingValue_taylor v P hc)
  have h := supportingValue_le_supportingValue_taylor v (taylor c P) (c := -c)
    (by rwa [v.map_neg])
  rwa [taylor_neg_taylor] at h

/-- **Translation of the slopes.** If `v c > -σ`, translating the unknown by `c` does not change
the multiplicity of `σ` as a slope of the Newton polygon. -/
theorem count_newtonSlopes_taylor_of_lt (hσ : ((-σ : ℝ) : WithTop ℝ) < v c) :
    ((taylor c P).newtonSlopes v).count σ = (P.newtonSlopes v).count σ := by
  -- The supporting values agree near `σ`.
  have hnhds : ∀ᶠ τ in 𝓝 σ, supportingValue ((taylor c P).newtonPolygon v) τ =
      supportingValue (P.newtonPolygon v) τ := by
    induction h : v c using WithTop.recTopCoe with
    | top => exact Eventually.of_forall fun τ =>
        supportingValue_newtonPolygon_taylor_of_le v P (h ▸ le_top)
    | coe r =>
      rw [h, WithTop.coe_lt_coe] at hσ
      filter_upwards [Ioi_mem_nhds (neg_lt.mp hσ)] with τ hτ
      exact supportingValue_newtonPolygon_taylor_of_le v P
        (h ▸ WithTop.coe_le_coe.mpr (neg_le.mpr (le_of_lt hτ)))
  have htop : (taylor c P).newtonPolygon v = ⊤ ↔ P.newtonPolygon v = ⊤ := by
    rw [← supportingValue_eq_top_iff (σ := σ), hnhds.self_of_nhds, supportingValue_eq_top_iff]
  by_cases hP : P.newtonPolygon v = ⊤
  · rw [newtonSlopes_congr ((htop.mpr hP).trans hP.symm)]
  obtain ⟨l, u, hf⟩ := exists_isFiniteFace_newtonPolygon hP σ
  obtain ⟨l', u', hf'⟩ := exists_isFiniteFace_newtonPolygon (htop.not.mpr hP) σ
  obtain ⟨rfl, rfl⟩ := hf.eq_of_eventuallyEq_supportingValue (isConvexSeq_newtonPolygon P v) hf'
    (isConvexSeq_newtonPolygon (taylor c P) v) hnhds
  rw [count_newtonSlopes_of_isFiniteFace hf, count_newtonSlopes_of_isFiniteFace hf']

/-- **Translation of the slopes, with multiplicity.** Translating the unknown by `c` does not change
the slopes `σ` of the Newton polygon with `-σ < v c`, counted with multiplicity. For a split
polynomial these are the slopes of the roots `r` with `v r < v c`, whose valuations
`v (r - c) = v r` the translation preserves. -/
theorem filter_newtonSlopes_taylor_lt_addValuation (c : R) :
    ((taylor c P).newtonSlopes v).filter (fun σ => ((-σ : ℝ) : WithTop ℝ) < v c) =
      (P.newtonSlopes v).filter (fun σ => ((-σ : ℝ) : WithTop ℝ) < v c) := by
  ext σ
  rw [Multiset.count_filter, Multiset.count_filter]
  split_ifs with hσ
  · exact count_newtonSlopes_taylor_of_lt v P hσ
  · rfl

end Polynomial
