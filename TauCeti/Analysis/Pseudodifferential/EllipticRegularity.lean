/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix

/-!
# Interior elliptic regularity

Let `a` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), and let `b` be a left parametrix symbol of `a`, a symbol of
order `-m` with `1 ∼ ∑ₖ sharpTerm b a k`
(`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`).
The composition symbol `b # c` is only available when the right factor `c` has compact spatial
support, so the parametrix is applied to a localization of `Op(a)`: a symbol `c` with compact
spatial support that agrees with `a` on an open set `Ω`, for instance `ψ(x) a(x, ξ)` for a cutoff
`ψ` equal to `1` on `Ω`. For a smooth cutoff `φ` with `tsupport φ ⊆ Ω`, the local left parametrix
identity `(φ b) # c = φ + r` with `r` smoothing (`TauCeti.Symbol.isSmoothing_sharp_sub_ofSmul`)
gives `Op(φ b) Op(c) = φ + Op(r)` on the Bessel-potential spaces `H^s = H^{s,2}(ℝⁿ; V)`. This file
proves this operator identity and its consequences:

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add`
  is the operator identity: for an elliptic `a`, there are a symbol `q` of order `-m` and a
  smoothing symbol `r`, both with compact spatial support, with `Op(q) Op(c) u = φ u + Op(r) u`
  for every `u ∈ H^s` and every real `s`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`: **interior elliptic regularity**. If
  `u ∈ H^t` and `Op(c) u ∈ H^{s - m}`, then `φ u ∈ H^s`, whatever the real numbers `s` and `t`.
* `TauCeti.Symbol.IsEllipticAbove.exists_norm_smulLeftCLM_le`: **the interior elliptic estimate**
  `‖φ u‖_{H^s} ≤ C (‖Op(c) u‖_{H^{s - m}} + ‖u‖_{H^r})` for `u ∈ H^s` and any `r ≤ s`.

## Proof outline

Write `(φ b) # c = φ (b # c)` (`TauCeti.Symbol.coefficient_sharp_of_coefficient_eq_smul`) and
expand `b # c = ∑_{k < N} sharpTerm b c k + R_N` with `R_N` of order `-N`. At a position `x ∈ Ω`
the terms `sharpTerm b c k` only involve the derivatives of `c` at `x`, which are those of `a`
(`TauCeti.Symbol.coefficient_sharpTerm_congr_of_eventually`), while `1 - ∑_{k < N} sharpTerm b a k`
has order `-N` since `b` is a left parametrix symbol. Hence `φ ((b # c) - 1)` is `φ` times a
symbol of order `-N` at every position, for every `N`. On Bessel-potential spaces, the composition
theorem `TauCeti.Symbol.toDistr_quantizeSobolev_sharp` turns this into the operator identity, and
the compatibility of the extensions of `Op(q)` and `Op(r)` to different `H^s`
(`TauCeti.Symbol.toDistr_quantizeSobolev_congr`) lets `Op(q)` gain `m` derivatives on
`Op(c) u ∈ H^{s - m}` and `Op(r)` gain any number of derivatives on `u ∈ H^t`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter
open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Interior elliptic regularity on Bessel-potential spaces -/

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The local parametrix of an elliptic operator.** Let `a` be elliptic of order `m`, let `c`
be a symbol with compact spatial support that agrees with `a` on an open set `Ω`, and let `φ` be a
smooth compactly supported function with `tsupport φ ⊆ Ω`. There are a symbol `q` of order `-m`
and a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(c) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsEllipticAbove R) {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω)
    {c : Symbol n V W m} (hc : c.HasCompactSpatialSupport)
    (hca : ∀ x ∈ Ω, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {φ : CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport) (r : Symbol n V V (-m + m))
      (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ (s : ℝ) (u : H^{s}(CoordinateSpace n, V)),
          (q.quantizeSobolev hq (s - m) (c.quantizeSobolev hc s u)).toDistr =
            TemperedDistribution.smulLeftCLM V φ u.toDistr +
              (r.quantizeSobolev hr s u).toDistr := by
  obtain ⟨b, hL, -⟩ := ha.exists_isAsymptoticSum_sharpTerm
  have he := hasCompactSpatialSupport_ofSmul (V := V) hφ hφc
  set q := inclusion (zero_add (-m)).le ((ofSmul φ hφ).comp b)
  have hq : q.HasCompactSpatialSupport := (he.comp_right b).inclusion _
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦ by
    rw [coefficient_inclusion, coefficient_ofSmul_comp]
  have he' := he.inclusion (neg_add_cancel m).ge
  have hr := (hq.sharp hc).sub he'
  refine ⟨q, hq, _, hr, isSmoothing_sharp_sub_ofSmul hL hΩ hc hca hφ hφΩ hqb, fun s u ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq hc,
    toDistr_quantizeSobolev_congr (hq.sharp hc) (he'.add hr)
      (a' := inclusion (neg_add_cancel m).ge _ + (q.sharp c hc - inclusion (neg_add_cancel m).ge _))
      (by simp) rfl,
    quantizeSobolev_add he' hr, add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_congr he' he (by simp) rfl, toDistr_quantizeSobolev_ofSmul hφ hφc]

/-- **Interior elliptic regularity.** Let `a` be elliptic of order `m`, let `c` be a symbol with
compact spatial support that agrees with `a` on an open set `Ω`, and let `φ` be a smooth compactly
supported function with `tsupport φ ⊆ Ω`. If `u ∈ H^t` and `Op(c) u ∈ H^{s - m}`, then
`φ u ∈ H^s`, for all real `s` and `t`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM {a : Symbol n V W m} {R : ℝ}
    (ha : a.IsEllipticAbove R) {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
    {c : Symbol n V W m} (hc : c.HasCompactSpatialSupport)
    (hca : ∀ x ∈ Ω, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {φ : CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : (c.quantizeSobolev hc t u).toDistr.MemSobolev (s - m) 2) :
    (TemperedDistribution.smulLeftCLM V φ u.toDistr).MemSobolev s 2 := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    ha.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add hΩ hc hca hφ hφc hφΩ
  have h₁ : (q.quantizeSobolev hq (t - m) (c.quantizeSobolev hc t u)).toDistr.MemSobolev s 2 := by
    rw [toDistr_quantizeSobolev_congr hq hq rfl (u' := hu.toBesselPotentialSpace)
      hu.toBesselPotentialSpace_toDistr.symm]
    exact (BesselPotentialSpace.memSobolev_toDistr _).mono (le_of_eq (by ring))
  obtain ⟨r', hr'⟩ := isSmoothing_iff.1 hrS (t - s)
  have h₂ : (r.quantizeSobolev hr t u).toDistr.MemSobolev s 2 := by
    rw [toDistr_quantizeSobolev_congr hr (hr.of_coefficient_eq hr') hr'.symm (u' := u) rfl]
    exact (BesselPotentialSpace.memSobolev_toDistr _).mono (le_of_eq (by ring))
  simpa [h t u] using h₁.sub h₂

/-- **The interior elliptic estimate.** Let `a` be elliptic of order `m`, let `c` be a symbol with
compact spatial support that agrees with `a` on an open set `Ω`, and let `φ` be a smooth compactly
supported function with `tsupport φ ⊆ Ω`. For all real `r ≤ s` there is a constant `C` with
`‖φ u‖_{H^s} ≤ C (‖Op(c) u‖_{H^{s - m}} + ‖u‖_{H^r})` for every `u ∈ H^s`. -/
theorem IsEllipticAbove.exists_norm_smulLeftCLM_le {a : Symbol n V W m} {R : ℝ}
    (ha : a.IsEllipticAbove R) {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
    {c : Symbol n V W m} (hc : c.HasCompactSpatialSupport)
    (hca : ∀ x ∈ Ω, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {φ : CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖BesselPotentialSpace.smulLeftCLM s (hφc.toSchwartzMap hφ) u‖ ≤
        C * (‖c.quantizeSobolev hc s u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨q, hq, e, he, heS, h⟩ :=
    ha.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add hΩ hc hca hφ hφc hφΩ
  obtain ⟨e', he'⟩ := isSmoothing_iff.1 heS (r - s)
  have he'c := he.of_coefficient_eq he'
  refine ⟨max ‖q.quantizeSobolev hq (s - m)‖ ‖e'.quantizeSobolev he'c r‖, fun u ↦ ?_⟩
  have hφS : ⇑(hφc.toSchwartzMap hφ) = φ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hs₁ : s ≤ s - m - -m := by linarith
  have hs₂ : s ≤ r - (r - s) := by linarith
  have hφu : BesselPotentialSpace.smulLeftCLM s (hφc.toSchwartzMap hφ) u =
      BesselPotentialSpace.inclusion hs₁
          (q.quantizeSobolev hq (s - m) (c.quantizeSobolev hc s u)) -
        BesselPotentialSpace.inclusion hs₂
          (e'.quantizeSobolev he'c r (BesselPotentialSpace.inclusion hrs u)) := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_sub, BesselPotentialSpace.toDistr_inclusion,
      BesselPotentialSpace.toDistr_inclusion, h s u,
      ← toDistr_quantizeSobolev_congr he he'c he'.symm
        (BesselPotentialSpace.toDistr_inclusion hrs u).symm,
      BesselPotentialSpace.toDistr_smulLeftCLM, hφS, add_sub_cancel_right]
  calc ‖BesselPotentialSpace.smulLeftCLM s (hφc.toSchwartzMap hφ) u‖
      ≤ ‖q.quantizeSobolev hq (s - m) (c.quantizeSobolev hc s u)‖ +
          ‖e'.quantizeSobolev he'c r (BesselPotentialSpace.inclusion hrs u)‖ := by
        rw [hφu]
        exact (norm_sub_le _ _).trans (add_le_add (BesselPotentialSpace.norm_inclusion_apply_le _ _)
          (BesselPotentialSpace.norm_inclusion_apply_le _ _))
    _ ≤ ‖q.quantizeSobolev hq (s - m)‖ * ‖c.quantizeSobolev hc s u‖ +
          ‖e'.quantizeSobolev he'c r‖ * ‖BesselPotentialSpace.inclusion hrs u‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

end Sobolev

end Symbol

end TauCeti
