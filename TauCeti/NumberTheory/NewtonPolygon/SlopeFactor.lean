/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.ActiveFace
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Entire.Preparation

/-!
# Slope-cutoff factors of entire series

For an entire series `f` with constant coefficient one, preparation at radius `b ^ σ`
separates its Newton slopes into a polynomial factor with slopes at most `σ` and an
entire cofactor with slopes strictly greater than `σ`. The polynomial degree is the
number of finite unit edges of the Newton polygon with slope at most `σ`.

We use the existing normalised entire preparation, rather than introducing another
factorisation predicate. Its factors are coprime in the entire-series ring by
`TauCeti.PowerSeries.IsEntirePreparation.isCoprime`. The multiplicity formulas below
identify exactly which slopes each factor carries, including slopes on the cutoff.
These are the scalar factors used to cut out finite spectral summands of operators.
No algebraic closedness or discreteness of the valuation is required.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open scoped PowerSeries

open TauCeti
open TauCeti.PowerSeries

namespace PowerSeries

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

include hb hv

/-- For an entire series with nonzero constant coefficient, the distinguished degree at
`b ^ σ` counts precisely the finite Newton edges with slope at most `σ`. -/
theorem IsEntire.isDistinguished_ncard_unitSlope_le (hf : f.IsEntire)
    (h0 : constantCoeff f ≠ 0) (σ : ℝ) :
    IsDistinguished (b ^ σ)
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ σ}.ncard f := by
  have hf0 : f ≠ 0 := fun h ↦ h0 (by simp [h])
  obtain ⟨l, d, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  have hstart : f.newtonPolygon v 0 ≠ ⊤ := by
    have hadm := (isAdmissible_addValuation_coeff_iff_exists_isRestricted f v hb hv).2
      ⟨1, zero_lt_one, hf.isRestricted 1⟩
    have hord : f.order = (0 : ℕ) := order_eq_nat.mpr ⟨by simpa using h0, by simp⟩
    rw [newtonPolygon_eq_of_order_eq v hadm hord]
    simpa only [coeff_zero_eq_constantCoeff] using v.ne_top_iff.mpr h0
  have hd := hface.right_eq_start_add_ncard_unitSlope_le
    (f.isConvexSeq_newtonPolygon v) hstart (fun _ _ ↦ Nat.zero_le _)
  simp only [zero_add] at hd
  rw [← hd]
  exact isDistinguished_of_isFiniteFace v hb hv (hf.isRestricted _) hface

variable [IsUltrametricDist K]

/-- An entire series which is a unit on the closed disc of radius `b ^ σ` has every
finite Newton slope strictly greater than `σ`. Entirety is essential: the Newton polygon
of a unit on a single disc may have a terminal ray at the cutoff. -/
theorem IsEntire.lt_unitSlope_of_isUnit (hf : f.IsEntire) {σ : ℝ}
    (hu : IsUnit (⟨f, hf.isRestricted (b ^ σ)⟩ : IsRestricted.subring (R := K) (b ^ σ)))
    {n : ℕ} (hn : n ∈ finiteEdges (f.newtonPolygon v)) :
    σ < unitSlope (f.newtonPolygon v) n := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hD := isDistinguished_zero_of_isUnit hc hu
  have hface : IsFiniteFace (f.newtonPolygon v) σ 0 0 :=
    (isFiniteFace_newtonPolygon_iff f v hb hv
      (hasGaussNorm_of_isRestricted (hf.isRestricted (b ^ (σ + 1)))) (by linarith)).2
      ⟨hD.isLowestDominant_zero, hD⟩
  exact hface.lt_unitSlope (f.isConvexSeq_newtonPolygon v) hn (Nat.zero_le _)

end NormedDivisionRing

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

include hb hv

/-- A normalised entire series has a unique normalised entire preparation at a slope
cutoff. Its polynomial degree is the number of finite Newton edges with slope at most
that cutoff. In particular the polynomial may be `1` when this set is empty. -/
theorem IsEntire.existsUnique_isEntirePreparation_slopeCutoff [CompleteSpace K]
    (hf : f.IsEntire) (h0 : constantCoeff f = 1) (σ : ℝ) :
    ∃! PG : Polynomial K × K⟦X⟧,
      IsEntirePreparation (b ^ σ)
        {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ σ}.ncard
        f PG.1 PG.2 := by
  have hD := hf.isDistinguished_ncard_unitSlope_le v hb hv (h0 ▸ one_ne_zero) σ
  have hM := isMulDistinguished_iff_isUnit.mpr
    ⟨hD, isUnit_iff_ne_zero.mpr hD.coeff_ne_zero⟩
  exact hM.existsUnique_isEntirePreparation
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hf h0

end NormedField

end PowerSeries

namespace TauCeti.PowerSeries.IsEntirePreparation

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {σ : ℝ} {d : ℕ} {f G : K⟦X⟧} {P : Polynomial K}

include hb hv

/-- In a normalised entire preparation at `b ^ σ`, the entire cofactor has zero
multiplicity at every slope at most `σ`. -/
theorem newtonSlopeMultiplicity_series_eq_zero (h : IsEntirePreparation (b ^ σ) d f P G)
    {τ : ℝ} (hτ : τ ≤ σ) : G.newtonSlopeMultiplicity v τ = 0 := by
  rw [PowerSeries.newtonSlopeMultiplicity_def]
  suffices hset : {n | n ∈ finiteEdges (G.newtonPolygon v) ∧
      unitSlope (G.newtonPolygon v) n = τ} = ∅ by rw [hset, Set.ncard_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨hn, heq⟩
  exact (h.isEntire.lt_unitSlope_of_isUnit v hb hv h.isUnit hn).not_ge (heq ▸ hτ)

/-- The polynomial in a normalised entire preparation carries exactly the slopes at
most the cutoff, with the same multiplicities as the original series. -/
theorem newtonSlopeMultiplicity_polynomial (h : IsEntirePreparation (b ^ σ) d f P G)
    (hD : IsDistinguished (b ^ σ) d f) (τ : ℝ) :
    (P.newtonSlopes v).count τ = if τ ≤ σ then f.newtonSlopeMultiplicity v τ else 0 := by
  split_ifs with hτ
  · have hfg : (P : K⟦X⟧) * G ≠ 0 := h.eq_mul ▸ hD.ne_zero
    have hmul := (PowerSeries.isEntire_coe P).newtonSlopeMultiplicity_mul v hb hv
      h.isEntire (left_ne_zero_of_mul hfg) (right_ne_zero_of_mul hfg) τ
    rw [← h.eq_mul, Polynomial.newtonSlopeMultiplicity_coe,
      h.newtonSlopeMultiplicity_series_eq_zero v hb hv hτ, add_zero] at hmul
    exact hmul.symm
  · apply Multiset.count_eq_zero.mpr
    intro hmem
    have hle := PowerSeries.le_of_mem_newtonSlopes_of_isUnit_mul v hb hv hD h.isUnit
      h.natDegree_eq.le (by rw [mul_comm, ← h.eq_mul]) hmem
    exact hτ hle

/-- The entire cofactor in a normalised preparation carries exactly the slopes strictly
above the cutoff, with the same multiplicities as the original series. -/
theorem newtonSlopeMultiplicity_series (h : IsEntirePreparation (b ^ σ) d f P G)
    (hD : IsDistinguished (b ^ σ) d f) (τ : ℝ) :
    G.newtonSlopeMultiplicity v τ = if σ < τ then f.newtonSlopeMultiplicity v τ else 0 := by
  by_cases hτ : τ ≤ σ
  · rw [ite_eq_right (not_lt.mpr hτ)]
    exact h.newtonSlopeMultiplicity_series_eq_zero v hb hv hτ
  · rw [ite_eq_left (lt_of_not_ge hτ)]
    have hfg : (P : K⟦X⟧) * G ≠ 0 := h.eq_mul ▸ hD.ne_zero
    have hmul := (PowerSeries.isEntire_coe P).newtonSlopeMultiplicity_mul v hb hv
      h.isEntire (left_ne_zero_of_mul hfg) (right_ne_zero_of_mul hfg) τ
    rw [← h.eq_mul, Polynomial.newtonSlopeMultiplicity_coe,
      h.newtonSlopeMultiplicity_polynomial v hb hv hD, ite_eq_right hτ, zero_add] at hmul
    exact hmul.symm

end TauCeti.PowerSeries.IsEntirePreparation
