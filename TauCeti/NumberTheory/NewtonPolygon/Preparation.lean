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

The entire factor is characterised by its slopes: over a complete ultrametric field, an entire
series with nonzero constant coefficient is a unit of the ring of series restricted at `b ^ σ`
exactly when it has no slopes at most `σ`. Conversely, therefore, any factorisation `P * G` into a
polynomial `P` with `P(0) = 1` and slopes at most `σ` and an entire `G` with `G(0) = 1` and no
slopes at most `σ` is the normalised entire preparation of `P * G` at `b ^ σ`.

## Main results

* `PowerSeries.IsEntire.isMulDistinguished_finsum_newtonSlopeMultiplicity`: an entire series
  with nonzero constant coefficient is multiplicatively distinguished at `b ^ σ` in the degree
  `∑ᶠ s ∈ Set.Iic σ, f.newtonSlopeMultiplicity v s`.
* `TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_left` and
  `TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_right`: the slope
  multiplicities of the two factors of a normalised entire preparation at `b ^ σ`.
* `PowerSeries.IsEntire.isUnit_iff_forall_newtonSlopeMultiplicity_eq_zero`: units of the ring of
  series restricted at `b ^ σ` are the entire series with no slopes at most `σ`.
* `PowerSeries.IsEntire.isEntirePreparation_finsum_newtonSlopeMultiplicity`: a slope-separated
  factorisation is the normalised entire preparation at the cutoff.

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
  have hd := isDistinguished_of_isFiniteFace v hb hv hface
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

/-- An entire series which is a unit of the ring of series restricted at `b ^ σ` has no slopes at
most `σ`: it is a unit at every radius `b ^ s` with `s ≤ σ`, so its Newton polygon has a
single-point face of each such slope. -/
theorem newtonSlopeMultiplicity_eq_zero_of_isUnit [IsUltrametricDist K] (hf : f.IsEntire)
    {σ : ℝ} (hu : IsUnit (⟨f, hf.isRestricted (b ^ σ)⟩ : IsRestricted.subring (R := K) (b ^ σ)))
    {s : ℝ} (hs : s ≤ σ) : f.newtonSlopeMultiplicity v s = 0 := by
  have hf0 : f ≠ 0 := fun h ↦ hu.ne_zero (Subtype.ext h)
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hcs : 0 < b ^ s := Real.rpow_pos_of_pos hb0 s
  have hunit := hu.map (Subring.inclusion (TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le (by
    rw [abs_of_pos hcs, abs_of_pos (Real.rpow_pos_of_pos hb0 σ)]
    exact Real.rpow_le_rpow_of_exponent_le hb.le hs)))
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 s
  have hj : j = 0 := (isDistinguished_of_isFiniteFace v hb hv hface).unique
    (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcs hunit)
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface, hj, Nat.zero_sub]

end PowerSeries.IsEntire

namespace PowerSeries.IsEntire

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

include hb hv

/-- **Units of the restricted ring at a slope cutoff.** Over a complete ultrametric field, an
entire series `f` with `f(0) ≠ 0` is a unit of the ring of series restricted at `b ^ σ` exactly
when its Newton polygon has no slopes at most `σ`. -/
theorem isUnit_iff_forall_newtonSlopeMultiplicity_eq_zero [CompleteSpace K] (hf : f.IsEntire)
    (hf0 : constantCoeff f ≠ 0) (σ : ℝ) :
    IsUnit (⟨f, hf.isRestricted (b ^ σ)⟩ : IsRestricted.subring (R := K) (b ^ σ)) ↔
      ∀ s ≤ σ, f.newtonSlopeMultiplicity v s = 0 := by
  refine ⟨fun hu s hs ↦ hf.newtonSlopeMultiplicity_eq_zero_of_isUnit v hb hv hu hs, fun h ↦ ?_⟩
  have hd := hf.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv hf0 σ
  rw [finsum_mem_eq_zero_of_forall_eq_zero fun s hs ↦ h s hs] at hd
  exact (TauCeti.PowerSeries.isUnit_iff_isDistinguished_zero
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) _).mpr hd.toIsDistinguished

/-- **Slope factorisations are normalised preparations.** Over a complete ultrametric field, let
`P` be a polynomial with `P(0) = 1` all of whose finite slopes are at most `σ`, and `G` an entire
series with `G(0) = 1` and no slopes at most `σ`. Then `P * G` is a normalised entire preparation
of itself at `b ^ σ`, in the degree `∑ᶠ s ∈ Set.Iic σ, (P * G).newtonSlopeMultiplicity v s` of
slopes of `P * G` at most `σ`, which is the degree of `P`. This is the converse of
`TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_left` and
`TauCeti.PowerSeries.IsEntirePreparation.newtonSlopeMultiplicity_right`. -/
theorem isEntirePreparation_finsum_newtonSlopeMultiplicity [CompleteSpace K] {G : K⟦X⟧}
    (hG : G.IsEntire) (hG0 : constantCoeff G = 1) {P : Polynomial K} (hP0 : P.coeff 0 = 1)
    {σ : ℝ} (hP : ∀ s ∈ P.newtonSlopes v, s ≤ σ)
    (hGσ : ∀ s ≤ σ, G.newtonSlopeMultiplicity v s = 0) :
    TauCeti.PowerSeries.IsEntirePreparation (b ^ σ)
      (∑ᶠ s ∈ Set.Iic σ, ((P : K⟦X⟧) * G).newtonSlopeMultiplicity v s) ((P : K⟦X⟧) * G) P G := by
  have hP0' : P ≠ 0 := fun h ↦ by simp [h] at hP0
  have hG0' : G ≠ 0 := fun h ↦ by simp [h] at hG0
  have hdeg : ∑ᶠ s ∈ Set.Iic σ, ((P : K⟦X⟧) * G).newtonSlopeMultiplicity v s = P.natDegree := by
    rw [finsum_mem_congr rfl fun s hs ↦ by
        rw [(isEntire_coe P).newtonSlopeMultiplicity_mul v hb hv hG
          (fun h ↦ hP0' (Polynomial.coe_eq_zero_iff.mp h)) hG0' s, hGσ s hs, add_zero],
      Polynomial.finsum_mem_Iic_newtonSlopeMultiplicity_coe, Multiset.filter_eq_self.mpr hP,
      Polynomial.card_newtonSlopes P v fun _ ↦ v.top_iff.mp,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp [hP0])), Nat.sub_zero]
  exact
    { coeff_zero_eq_one := hP0
      natDegree_eq := hdeg.symm
      isUnit_leadingCoeff := isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP0')
      isEntire := hG
      constantCoeff_eq_one := hG0
      isUnit := (hG.isUnit_iff_forall_newtonSlopeMultiplicity_eq_zero v hb hv
        (by simp [hG0]) σ).mpr hGσ
      eq_mul := rfl }

end PowerSeries.IsEntire

namespace TauCeti.PowerSeries.IsEntirePreparation

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {σ : ℝ} {d : ℕ} {f : K⟦X⟧} {P : Polynomial K} {G : K⟦X⟧}

include hb hv

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
  · rw [h.newtonSlopeMultiplicity_eq_add v hb hv,
      h.isEntire.newtonSlopeMultiplicity_eq_zero_of_isUnit v hb hv h.isUnit hs,
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
  · exact h.isEntire.newtonSlopeMultiplicity_eq_zero_of_isUnit v hb hv h.isUnit hs
  · rw [h.newtonSlopeMultiplicity_eq_add v hb hv, h.newtonSlopeMultiplicity_left v hb hv hf s]
    simp [hs]

end TauCeti.PowerSeries.IsEntirePreparation
