/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Entire.Preparation

/-!
# Slopes of normalised entire preparations

Let `K` be a normed division ring whose norm comes from a real additive valuation `v` with base
`b > 1`, so `‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`, and let `f` be an entire power series over `K`
with `f(0) ≠ 0`. The Newton polygon of `f` starts at `0` and has a finite face of every real slope
`σ`. Its right endpoint is the number of finite unit edges of slope at most `σ`, that is, the
number `∑ᶠ s ∈ Set.Iic σ, f.newtonSlopeMultiplicity v s` of slopes at most `σ` counted with
multiplicity. Consequently `f` is multiplicatively distinguished in exactly this degree at the
radius `b ^ σ`.

Now let `K` be an ultrametric normed field. A normalised entire preparation `f = P * G` of `f` at
`b ^ σ` in this degree, which exists when `K` is complete, splits the slopes of `f` at the cutoff
`σ`. The polynomial factor `P` carries exactly the slopes at most `σ`, with their multiplicities,
and the entire factor `G` carries exactly the slopes greater than `σ`. This is the scalar
factorisation `f = Q_(≤σ) * S_(>σ)` behind the finite-slope decomposition of a compact operator.

## Main results

* `PowerSeries.IsEntire.isMulDistinguished_finsum_newtonSlopeMultiplicity`: an entire series
  with nonzero constant coefficient is multiplicatively distinguished at `b ^ σ` in the degree
  `∑ᶠ s ∈ Set.Iic σ, f.newtonSlopeMultiplicity v s`.
* `TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_left` and
  `TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_right`: the slope
  multiplicities of the two factors of a normalised entire preparation at `b ^ σ`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A3–A4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
-/

public section

open scoped PowerSeries
open TauCeti

namespace PowerSeries.IsEntire

variable {K : Type*} [NormedDivisionRing K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

include hb hv

/-- **The distinguished degree of an entire series is its number of small slopes.** An entire
series `f` with `f(0) ≠ 0` is multiplicatively distinguished at the radius `b ^ σ` in the degree
`∑ᶠ s ∈ Set.Iic σ, f.newtonSlopeMultiplicity v s`, the number of finite slopes of its Newton
polygon at most `σ` counted with multiplicity. -/
theorem isMulDistinguished_finsum_newtonSlopeMultiplicity (hf : f.IsEntire)
    (hf0 : constantCoeff f ≠ 0) (σ : ℝ) :
    TauCeti.PowerSeries.IsMulDistinguished (b ^ σ)
      (∑ᶠ s ∈ Set.Iic σ, f.newtonSlopeMultiplicity v s) f := by
  have hfne : f ≠ 0 := fun h ↦ hf0 (by simp [h])
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hfne σ
  have hd := isDistinguished_of_isFiniteFace v hb hv (hf.isRestricted _) hface
  have hadm : IsAdmissible fun n ↦ v (f.coeff n) :=
    (isAdmissible_addValuation_coeff_iff_exists_isRestricted f v hb hv).mpr
      ⟨1, one_pos, hf.isRestricted 1⟩
  -- The polygon starts at `0`, so the right endpoint `j` counts the edges of slope `≤ σ`.
  have h0 : f.newtonPolygon v 0 ≠ ⊤ := by
    rw [newtonPolygon_eq_of_order_eq v hadm (order_eq_nat.mpr ⟨by simpa using hf0, by simp⟩)]
    exact v.ne_top_iff.mpr (by simpa using hf0)
  have hj := hface.right_eq_start_add_ncard_unitSlope_le (f.isConvexSeq_newtonPolygon v) h0
    fun n _ ↦ n.zero_le
  rw [zero_add, ncard_setOf_unitSlope_newtonPolygon_le
    (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv σ)] at hj
  rw [← hj, TauCeti.PowerSeries.isMulDistinguished_iff_isUnit]
  exact ⟨hd, isUnit_iff_ne_zero.mpr hd.coeff_ne_zero⟩

end PowerSeries.IsEntire

namespace TauCeti.PowerSeries.IsEntirePreparation

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {σ : ℝ} {d : ℕ} {f : K⟦X⟧} {P : Polynomial K} {G : K⟦X⟧}

include hb hv

/-- The entire factor of a normalised preparation at `b ^ σ` has no slopes at most `σ`: it is a
unit at every radius `b ^ s` with `s ≤ σ`, so its Newton polygon has a single-point face of each
such slope. -/
private theorem newtonSlopeMultiplicity_right_of_le (h : IsEntirePreparation (b ^ σ) d f P G)
    {s : ℝ} (hs : s ≤ σ) : G.newtonSlopeMultiplicity v s = 0 := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hcs : 0 < b ^ s := Real.rpow_pos_of_pos hb0 s
  have hunit := (h.mono (c' := b ^ s) (by
    rw [abs_of_pos hcs, abs_of_pos (Real.rpow_pos_of_pos hb0 σ)]
    exact Real.rpow_le_rpow_of_exponent_le hb.le hs)).isUnit
  obtain ⟨l, j, hface⟩ := h.isEntire.exists_isFiniteFace_newtonPolygon v hb hv h.right_ne_zero s
  have hj : j = 0 := ((isDistinguished_of_isFiniteFace v hb hv (h.isEntire.isRestricted _)
    hface).unique (isDistinguished_zero_of_isUnit hcs hunit))
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface, hj, Nat.zero_sub]

/-- The slope multiplicities of `f` are the sums of those of the two factors of a normalised entire
preparation. -/
private theorem newtonSlopeMultiplicity_eq_add (h : IsEntirePreparation (b ^ σ) d f P G) (s : ℝ) :
    f.newtonSlopeMultiplicity v s =
      (P : K⟦X⟧).newtonSlopeMultiplicity v s + G.newtonSlopeMultiplicity v s := by
  rw [h.eq_mul]
  exact (isEntire_coe P).newtonSlopeMultiplicity_mul v hb hv h.isEntire h.coe_ne_zero
    h.right_ne_zero s

/-- **Slopes of the polynomial factor of a normalised entire preparation.** Let `f` be entire and
distinguished of degree `d` at `b ^ σ`, with normalised entire preparation `f = P * G` there. Then
`P` has the slopes of `f` at most `σ`, with the same multiplicities, and no other slopes. -/
theorem newtonSlopeMultiplicity_left (h : IsEntirePreparation (b ^ σ) d f P G)
    (hf : IsDistinguished (b ^ σ) d f) (s : ℝ) :
    (P : K⟦X⟧).newtonSlopeMultiplicity v s =
      if s ≤ σ then f.newtonSlopeMultiplicity v s else 0 := by
  split_ifs with hs
  · rw [h.newtonSlopeMultiplicity_eq_add v hb hv, h.newtonSlopeMultiplicity_right_of_le v hb hv hs,
      add_zero]
  · rw [Polynomial.newtonSlopeMultiplicity_coe, Multiset.count_eq_zero]
    exact fun hmem ↦ hs <| PowerSeries.le_of_mem_newtonSlopes_of_isUnit_mul v hb hv hf h.isUnit
      h.natDegree_eq.le (by rw [mul_comm]; exact h.eq_mul.symm) hmem

/-- **Slopes of the entire factor of a normalised entire preparation.** Let `f` be entire and
distinguished of degree `d` at `b ^ σ`, with normalised entire preparation `f = P * G` there. Then
`G` has the slopes of `f` greater than `σ`, with the same multiplicities, and no other slopes. -/
theorem newtonSlopeMultiplicity_right (h : IsEntirePreparation (b ^ σ) d f P G)
    (hf : IsDistinguished (b ^ σ) d f) (s : ℝ) :
    G.newtonSlopeMultiplicity v s = if s ≤ σ then 0 else f.newtonSlopeMultiplicity v s := by
  split_ifs with hs
  · exact h.newtonSlopeMultiplicity_right_of_le v hb hv hs
  · rw [h.newtonSlopeMultiplicity_eq_add v hb hv, h.newtonSlopeMultiplicity_left v hb hv hf s]
    simp [hs]

end TauCeti.PowerSeries.IsEntirePreparation
