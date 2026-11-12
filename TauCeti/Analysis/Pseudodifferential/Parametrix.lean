/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix

/-!
# Local parametrices and interior elliptic regularity

Let `a` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), and let `b` be a left parametrix symbol of `a`, a symbol of
order `-m` with `1 ∼ ∑ₖ sharpTerm b a k`
(`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`).
The composition symbol `b # c` is only available when the right factor `c` has compact spatial
support, so the parametrix is applied to a localization of `Op(a)`: a symbol `c` with compact
spatial support that agrees with `a` on an open set `Ω`, for instance `ψ(x) a(x, ξ)` for a cutoff
`ψ` equal to `1` on `Ω`. For a smooth cutoff `φ` with `tsupport φ ⊆ Ω` this file proves the
**local left parametrix identity**

`(φ b) # c = φ + r` with `r` smoothing,

and its consequences on the Bessel-potential spaces `H^s = H^{s,2}(ℝⁿ; V)`, where
`Op(φ b) Op(c) = φ + Op(r)`:

* `TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`: the local left parametrix identity, for any
  left parametrix symbol `b` of a symbol `a`, elliptic or not.
* `TauCeti.Symbol.IsEllipticAbove.exists_quantizeSobolev_localParametrix`: for an elliptic `a`,
  there are a symbol `q` of order `-m` and a smoothing symbol `r`, both with compact spatial
  support, with `Op(q) Op(c) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`.
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

/-! ### The local left parametrix identity -/

section LocalParametrix

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m} {b : Symbol n W V (-m)}

/-- **The local left parametrix identity.** Let `b` be a left parametrix symbol of `a`, so that
`1 ∼ ∑ₖ sharpTerm b a k`, let `c` be a symbol with compact spatial support that agrees with `a` on
an open set `Ω`, and let `φ` be a smooth function with `tsupport φ ⊆ Ω`. If `q = φ b`, then
`q # c - φ` is smoothing. -/
theorem isSmoothing_sharp_sub_ofSpatial [CompleteSpace V] [CompleteSpace W]
    (hL : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) {c : Symbol n V W m}
    (hc : c.HasCompactSpatialSupport)
    (hca : ∀ x ∈ Ω, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {φ : CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφΩ : tsupport φ ⊆ Ω)
    {q : Symbol n W V (-m)} (hq : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ)) :
    (q.sharp c hc - inclusion (neg_add_cancel m).ge (ofSpatial
      (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) (hφ.smul contDiff_const))).IsSmoothing := by
  refine isSmoothing_iff.2 fun m'' ↦ ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) ≤ m'' := ⟨⌈-m''⌉₊, by linarith [Nat.le_ceil (-m'')]⟩
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hL N
  refine ⟨inclusion (by linarith) ((ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
    (hφ.smul contDiff_const)).comp
    (b.sharpRemainder c hc N - r)), ?_⟩
  funext ⟨x, ξ⟩
  simp only [coefficient_inclusion, coefficient_comp, coefficient_ofSpatial, coefficient_sub,
    Pi.sub_apply, coefficient_sharpRemainder]
  rw [coefficient_sharp_of_coefficient_eq_smul hc (hq x) ξ]
  by_cases hx : x ∈ Ω
  · have hev : ∀ᶠ y in 𝓝 x, ∀ η, c.coefficient (y, η) = a.coefficient (y, η) :=
      eventually_of_mem (hΩ.mem_nhds hx) hca
    have hr' := congrFun hr (x, ξ)
    simp only [coefficient_inclusion, coefficient_const, Pi.sub_apply, Finset.sum_apply] at hr'
    simp only [Finset.sum_apply, coefficient_sharpTerm_congr_of_eventually b hev, ← hr']
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, smul_sub]
    abel
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφΩ h)
    simp [this]

end LocalParametrix

/-! ### Interior elliptic regularity on Bessel-potential spaces -/

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The local parametrix of an elliptic operator.** Let `a` be elliptic of order `m`, let `c`
be a symbol with compact spatial support that agrees with `a` on an open set `Ω`, and let `φ` be a
smooth compactly supported function with `tsupport φ ⊆ Ω`. There are a symbol `q` of order `-m`
and a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(c) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsEllipticAbove.exists_quantizeSobolev_localParametrix {a : Symbol n V W m} {R : ℝ}
    (ha : a.IsEllipticAbove R) {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
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
  obtain ⟨q, hqb⟩ : ∃ q : Symbol n W V (-m),
      ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) :=
    ⟨inclusion (zero_add (-m)).le ((ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      (hφ.smul contDiff_const)).comp b), fun x ξ ↦ by
      rw [coefficient_inclusion, coefficient_comp, coefficient_ofSpatial,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]⟩
  have hq : q.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2
    ⟨tsupport φ, hφc, fun x hx ξ ↦ by rw [hqb, image_eq_zero_of_notMem_tsupport hx, zero_smul]⟩
  have he : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      (hφ.smul contDiff_const)).HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff _).2 (hφc.mono fun x hx h0 ↦ hx (by simp [h0]))
  have he' := he.inclusion (neg_add_cancel m).ge
  have hr := (hq.sharp hc).sub he'
  refine ⟨q, hq, _, hr, isSmoothing_sharp_sub_ofSpatial hL hΩ hc hca hφ hφΩ hqb, fun s u ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq hc,
    toDistr_quantizeSobolev_congr (hq.sharp hc) (he'.add hr)
      (a' := inclusion (neg_add_cancel m).ge _ + (q.sharp c hc - inclusion (neg_add_cancel m).ge _))
      (by simp) rfl,
    quantizeSobolev_add he' hr, add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_congr he' he (by simp) rfl, toDistr_quantizeSobolev_ofSpatial hφ hφc]

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
  obtain ⟨q, hq, r, hr, hrS, h⟩ := ha.exists_quantizeSobolev_localParametrix hΩ hc hca hφ hφc hφΩ
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
  obtain ⟨q, hq, e, he, heS, h⟩ := ha.exists_quantizeSobolev_localParametrix hΩ hc hca hφ hφc hφΩ
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
