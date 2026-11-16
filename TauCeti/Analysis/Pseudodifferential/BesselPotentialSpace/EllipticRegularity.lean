/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# Interior elliptic regularity on `H^{s,p}`

Let `1 < p < ∞`, let `P` be a symbol of order `m` on `ℝⁿ`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), with values in operators between finite-dimensional complex
normed spaces, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with
compact spatial support that agrees with `P` near `tsupport φ`. This file proves **interior
elliptic regularity** on the Bessel-potential spaces `H^{s,p}(ℝⁿ)`: if `u ∈ H^{t,p}` and
`Op(a) u ∈ H^{s - m,p}`, then `φ u ∈ H^{s,p}`, with the estimate
`‖φ u‖_{H^{s,p}} ≤ C (‖Op(a) u‖_{H^{s - m,p}} + ‖u‖_{H^{t,p}})`, for all real `s` and `t`.

The argument is that of the case `p = 2`
(`TauCeti/Analysis/Pseudodifferential/EllipticRegularity.lean`), with the operators
`Op(a) : H^{s,p} → H^{s - m,p}` of `TauCeti.Symbol.quantizeBesselPotentialSpace` in place of
`TauCeti.Symbol.quantizeSobolev`. A left parametrix of `P`, localized by `φ`, gives a symbol `q`
of order `-m` and a smoothing symbol `r` with `Op(q) Op(a) = φ + Op(r)` on every `H^{s,p}`. Then
`φ u = Op(q) (Op(a) u) - Op(r) u`, where `Op(q)` gains `m` derivatives and the smoothing `Op(r)`
gains every number of derivatives.

## Main declarations

In the namespace `TauCeti.Symbol`:

* `IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeBesselPotentialSpace_eq_smulLeftCLM_add`:
  the local parametrix identity `Op(q) Op(a) = φ + Op(r)` with `r` smoothing.
* `IsEllipticAbove.memSobolev_smulLeftCLM_of_one_lt`: interior elliptic regularity.
* `IsEllipticAbove.exists_norm_le_of_toDistr_eq_smulLeftCLM`: the interior elliptic estimate.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11) (the local parametrix and elliptic regularity), and Lecture II, (3.1)–(3.8) (their
  `Lᵖ` versions).
-/

public section

noncomputable section

open scoped ENNReal SchwartzMap BesselPotentialSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W] {m : ℝ} {a : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable {R : ℝ} {P : Symbol n V W m}

namespace IsEllipticAbove

/-- **The local parametrix of an elliptic operator on `H^{s,p}`.** Let `P` be elliptic of order
`m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `P` on a neighbourhood of `tsupport φ`. There are a symbol `q` of
order `-m` and a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^{s,p}`, every real `s` and every `1 < p < ∞`. -/
theorem exists_isSmoothing_and_toDistr_quantizeBesselPotentialSpace_eq_smulLeftCLM_add
    (hP : P.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (haP : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = P.coefficient (x, ξ)) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport) (r : Symbol n V V (-m + m))
      (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ (∞ : ℝ≥0∞) →
          ∀ (s : ℝ) (u : H^{s, p}(CoordinateSpace n, V)),
          (q.quantizeBesselPotentialSpace hq (s - m) p
              (a.quantizeBesselPotentialSpace ha s p u)).toDistr =
            TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr +
              (r.quantizeBesselPotentialSpace hr s p u).toDistr := by
  obtain ⟨b, hL, -⟩ := hP.exists_isAsymptoticSum_sharpTerm
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  set q := inclusion (zero_add (-m)).le (F.comp b)
  have hq : q.HasCompactSpatialSupport := (hF.comp_right b).inclusion _
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦ by
    simp [q, F]
  have hF' := hF.inclusion (neg_add_cancel m).ge
  have hr := (hq.sharp ha).sub hF'
  refine ⟨q, hq, _, hr, isSmoothing_sharp_sub_ofSpatial hL (φ.smooth ⊤) hqb ha haP,
    fun p _ hp hp_top s u ↦ ?_⟩
  -- `q # a = F + (q # a - F)`, where `F` is the symbol of the multiplication by `φ`.
  rw [← toDistr_quantizeBesselPotentialSpace_sharp hq ha s hp hp_top,
    toDistr_quantizeBesselPotentialSpace_congr
      (b := inclusion (neg_add_cancel m).ge F + (q.sharp a ha - inclusion (neg_add_cancel m).ge F))
      (by simp) (hq.sharp ha) (hF'.add hr) hp hp_top rfl,
    quantizeBesselPotentialSpace_add hF' hr _ s hp hp_top, add_apply,
    BesselPotentialSpace.toDistr_add,
    toDistr_quantizeBesselPotentialSpace_congr (by simp) hF' hF hp hp_top rfl,
    toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id φ hF s hp hp_top]

/-- **Interior elliptic regularity on `H^{s,p}`.** Let `1 < p < ∞`, let `P` be elliptic of order
`m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `P` on a neighbourhood of `tsupport φ`. If `u ∈ H^{t,p}` and
`Op(a) u ∈ H^{s - m,p}`, then `φ u ∈ H^{s,p}`, for all real `s` and `t`. The case `p = 2` for
Hilbert-space fibres is `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`. -/
theorem memSobolev_smulLeftCLM_of_one_lt (hP : P.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (haP : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = P.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s t : ℝ} {u : H^{t, p}(CoordinateSpace n, V)}
    (hu : (a.quantizeBesselPotentialSpace ha t p u).toDistr.MemSobolev (s - m) p) :
    (TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr).MemSobolev s p := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    hP.exists_isSmoothing_and_toDistr_quantizeBesselPotentialSpace_eq_smulLeftCLM_add ha hφ haP
  -- `φ u = Op(q) (Op(a) u) - Op(r) u`, where `Op(q)` gains `m` derivatives on `Op(a) u` and the
  -- smoothing `Op(r)` gains every number of derivatives.
  have h₁ : (q.quantizeBesselPotentialSpace hq (t - m) p
      (a.quantizeBesselPotentialSpace ha t p u)).toDistr.MemSobolev s p := by
    rw [toDistr_quantizeBesselPotentialSpace_congr rfl hq hq hp hp_top
      (v := hu.toBesselPotentialSpace) hu.toBesselPotentialSpace_toDistr.symm]
    simpa using BesselPotentialSpace.memSobolev_toDistr
      (q.quantizeBesselPotentialSpace hq (s - m) p hu.toBesselPotentialSpace)
  obtain ⟨T, hT⟩ := hrS.exists_continuousLinearMap_toDistr_quantizeBesselPotentialSpace_eq hr hp
    hp_top t s
  have h₂ : (r.quantizeBesselPotentialSpace hr t p u).toDistr.MemSobolev s p := by
    rw [hT rfl]
    exact BesselPotentialSpace.memSobolev_toDistr _
  simpa [h p hp hp_top t u] using h₁.sub h₂

/-- **Interior elliptic estimate on `H^{s,p}`.** Let `1 < p < ∞`, let `P` be elliptic of order
`m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `P` on a neighbourhood of `tsupport φ`. For all real `s` and `t`
there is `C` such that for every `u ∈ H^{t,p}` with `Op(a) u ∈ H^{s - m,p}`,

`‖φ u‖_{H^{s,p}} ≤ C (‖Op(a) u‖_{H^{s - m,p}} + ‖u‖_{H^{t,p}})`,

where `φ u ∈ H^{s,p}` by `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_one_lt`. Here
`f` and `w` are the elements of `H^{s - m,p}` and `H^{s,p}` with the tempered distributions of
`Op(a) u` and `φ u`. The order `t` is arbitrary: `u` need not lie in `H^{s,p}`. -/
theorem exists_norm_le_of_toDistr_eq_smulLeftCLM (hP : P.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (haP : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = P.coefficient (x, ξ))
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (s t : ℝ) :
    ∃ C, ∀ (u : H^{t, p}(CoordinateSpace n, V)) (f : H^{s - m, p}(CoordinateSpace n, W))
      (w : H^{s, p}(CoordinateSpace n, V)),
        f.toDistr = (a.quantizeBesselPotentialSpace ha t p u).toDistr →
        w.toDistr = TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr →
          ‖w‖ ≤ C * (‖f‖ + ‖u‖) := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    hP.exists_isSmoothing_and_toDistr_quantizeBesselPotentialSpace_eq_smulLeftCLM_add ha hφ haP
  obtain ⟨T, hT⟩ := hrS.exists_continuousLinearMap_toDistr_quantizeBesselPotentialSpace_eq hr hp
    hp_top t s
  -- `Op(q)` maps `H^{s - m,p}` to `H^{s - m - (-m),p}`, which is `H^{s,p}`.
  set Q := BesselPotentialSpace.inclusionₚ _ V p (show s ≤ s - m - -m by simp) ∘L
    q.quantizeBesselPotentialSpace hq (s - m) p
  refine ⟨‖Q‖ + ‖T‖, fun u f w hf hw ↦ ?_⟩
  -- `w = Op(q) f - Op(r) u`, with `Op(q) : H^{s - m,p} → H^{s,p}` and `Op(r) : H^{t,p} → H^{s,p}`.
  have hw' : w = Q f - T u := by
    refine BesselPotentialSpace.ext ?_
    rw [hw, BesselPotentialSpace.toDistr_sub, ← hT rfl, ContinuousLinearMap.comp_apply,
      BesselPotentialSpace.toDistr_inclusionₚ,
      toDistr_quantizeBesselPotentialSpace_congr rfl hq hq hp hp_top hf,
      h p hp hp_top t u, add_sub_cancel_right]
  rw [hw']
  calc ‖Q f - T u‖ ≤ ‖Q‖ * ‖f‖ + ‖T‖ * ‖u‖ :=
        (norm_sub_le _ _).trans (add_le_add (Q.le_opNorm f) (T.le_opNorm u))
    _ ≤ (‖Q‖ + ‖T‖) * (‖f‖ + ‖u‖) := by
        nlinarith [norm_nonneg Q, norm_nonneg T, norm_nonneg f, norm_nonneg u]

end IsEllipticAbove

end Symbol

end TauCeti
