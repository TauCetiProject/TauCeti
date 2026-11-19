/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Interior elliptic regularity

Let `p` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), and let `b` be a left parametrix symbol of `p`, a symbol of
order `-m` with `1 ∼ ∑ₖ sharpTerm b p k`
(`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`).
The composition symbol `b # a` is only available when the right factor `a` has compact spatial
support, so the parametrix is applied to a localization of `Op(p)`: a symbol `a` with compact
spatial support that agrees with `p` near the support of a compactly supported Schwartz function
`φ`, for instance `ψ(x) p(x, ξ)` for a cutoff `ψ` equal to `1` near `tsupport φ`. The local left
parametrix identity `(φ b) # a = φ + r` with `r` smoothing
(`TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`) gives `Op(φ b) Op(a) = φ + Op(r)` on
the Bessel-potential spaces `H^s = H^{s,2}(ℝⁿ; V)`. This file proves this operator identity and
its consequence:

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_sharp_sub_ofSpatial` is the symbol identity:
  a symbol `q` of order `-m` with compact spatial support such that `q # a - φ` is smoothing,
  again with compact spatial support.
* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add`
  is the operator identity: for an elliptic `p`, there are a symbol `q` of order `-m` and a
  smoothing symbol `r`, both with compact spatial support, with `Op(q) Op(a) u = φ u + Op(r) u`
  for every `u ∈ H^s` and every real `s`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`: **interior elliptic regularity**. If
  `u ∈ H^t` and `Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`, whatever the real numbers `s` and `t`.

The same holds for scalar symbols acting on arbitrary tempered distributions, with no a priori
Sobolev regularity, since the smoothing remainder `Op(r)` maps every tempered distribution into
every `H^s` (`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`):

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add`:
  the operator identity `Op(q) Op(a) T = φ T + Op(r) T` for every tempered distribution `T`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered`: if `T`
  is a tempered distribution with `Op(a) T ∈ H^{s - m}`, then `φ T ∈ H^s`.
* `TauCeti.Symbol.IsEllipticAbove.exists_contDiff_smulLeftCLM_eq_integral_of_forall_memSobolev`:
  **hypoellipticity**. If `Op(a) T` lies in every `H^s`, for instance `Op(a) T = 0`, then `φ T`
  is a smooth function.

The corresponding interior estimate
`‖φ u‖_{H^s} ≤ C (‖Op(a) u‖_{H^{s - m}} + ‖u‖_{H^r})` is
`TauCeti.Symbol.IsEllipticAbove.exists_norm_smulLeftCLM_le`.

## Proof outline

Write `(φ b) # a = φ (b # a)` (`TauCeti.Symbol.coefficient_sharp_of_coefficient_eq_smul`) and
expand `b # a = ∑_{k < N} sharpTerm b a k + R_N` with `R_N` of order `-N`. At a position `x` near
`tsupport φ` the terms `sharpTerm b a k` only involve the derivatives of `a` at `x`, which are
those of `p` (`TauCeti.Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq`), while
`1 - ∑_{k < N} sharpTerm b p k` has order `-N` since `b` is a left parametrix symbol. Hence
`φ ((b # a) - 1)` is `φ` times a symbol of order `-N` at every position, for every `N`. On
Bessel-potential spaces, the composition theorem `TauCeti.Symbol.toDistr_quantizeSobolev_sharp`
turns this into the operator identity, and the compatibility of the extensions of `Op(q)` to
different `H^s` (`TauCeti.Symbol.toDistr_quantizeSobolev_congr`) lets `Op(q)` gain `m`
derivatives on `Op(a) u ∈ H^{s - m}`, while `Op(r)` gains any number of derivatives on `u ∈ H^t`
(`TauCeti.Symbol.IsSmoothing.exists_continuousLinearMap_toDistr_quantizeSobolev_eq`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}
  {p a : Symbol n V W m}

/-- **The local parametrix symbol of an elliptic symbol.** Let `p` be elliptic of order `m`, let
`φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact spatial support
that agrees with `p` on a neighbourhood of `tsupport φ`. There is a symbol `q` of order `-m` with
compact spatial support such that `q # a - φ` is smoothing and has compact spatial support. -/
theorem IsEllipticAbove.exists_isSmoothing_sharp_sub_ofSpatial (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ q : Symbol n W V (-m), q.HasCompactSpatialSupport ∧
      let r := q.sharp a ha - inclusion (neg_add_cancel m).ge
        (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const))
      r.HasCompactSpatialSupport ∧ r.IsSmoothing := by
  obtain ⟨b, hL, -⟩ := hp.exists_isAsymptoticSum_sharpTerm
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  set q := inclusion (zero_add (-m)).le (F.comp b)
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦ by
    simp [q, F]
  have hq : q.HasCompactSpatialSupport := (hF.comp_right b).inclusion _
  exact ⟨q, hq, (hq.sharp ha).sub (hF.inclusion _),
    isSmoothing_sharp_sub_ofSpatial hL (φ.smooth ⊤) hqb ha hap⟩

/-- **The local parametrix of an elliptic operator.** Let `p` be elliptic of order `m`, let `φ`
be a compactly supported Schwartz function, and let `a` be a symbol with compact spatial support
that agrees with `p` on a neighbourhood of `tsupport φ`. There are a symbol `q` of order `-m` and
a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport) (r : Symbol n V V (-m + m))
      (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ (s : ℝ) (u : H^{s}(CoordinateSpace n, V)),
          (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)).toDistr =
            (BesselPotentialSpace.smulLeftCLM s φ u).toDistr +
              (r.quantizeSobolev hr s u).toDistr := by
  obtain ⟨q, hq, hr, hrS⟩ := hp.exists_isSmoothing_sharp_sub_ofSpatial ha hφ hap
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  have hF' := hF.inclusion (neg_add_cancel m).ge
  refine ⟨q, hq, _, hr, hrS, fun s u ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq ha,
    toDistr_quantizeSobolev_congr
      (b := inclusion (neg_add_cancel m).ge F + (q.sharp a ha - inclusion (neg_add_cancel m).ge F))
      (by simp) (hq.sharp ha) (hF'.add hr) rfl,
    quantizeSobolev_add hF' hr, add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_congr (by simp) hF' hF rfl, toDistr_quantizeSobolev_ofSpatial_smul_id]

/-- **Interior elliptic regularity.** Let `p` be elliptic of order `m`, let `φ` be a compactly
supported Schwartz function, and let `a` be a symbol with compact spatial support that agrees with
`p` on a neighbourhood of `tsupport φ`. If `u ∈ H^t` and `Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`,
for all real `s` and `t`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM (hp : p.IsEllipticAbove R)
    (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    (hu : (a.quantizeSobolev ha t u).toDistr.MemSobolev (s - m) 2) :
    (BesselPotentialSpace.smulLeftCLM t φ u).toDistr.MemSobolev s 2 := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    hp.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add ha hφ hap
  have h₁ : (q.quantizeSobolev hq (t - m) (a.quantizeSobolev ha t u)).toDistr.MemSobolev s 2 := by
    rw [toDistr_quantizeSobolev_congr rfl hq hq (v := hu.toBesselPotentialSpace)
      hu.toBesselPotentialSpace_toDistr.symm]
    exact (BesselPotentialSpace.memSobolev_toDistr _).mono (le_of_eq (by ring))
  obtain ⟨T, hT⟩ := hrS.exists_continuousLinearMap_toDistr_quantizeSobolev_eq hr t s
  have h₂ : (r.quantizeSobolev hr t u).toDistr.MemSobolev s 2 := by
    rw [hT rfl]
    exact BesselPotentialSpace.memSobolev_toDistr _
  simpa [h t u] using h₁.sub h₂

/-! ### Tempered distributions -/

section Tempered

variable {p a : Symbol n ℂ ℂ m}

/-- **The local parametrix on tempered distributions.** Let `p` be a scalar symbol elliptic of
order `m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. There are a symbol `q` of
order `-m` and a smoothing symbol `r`, both with compact spatial support, such that
`Op(q) Op(a) T = φ T + Op(r) T` for every tempered distribution `T`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul ℂ F] (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n ℂ ℂ (-m)) (hq : q.HasCompactSpatialSupport) (r : Symbol n ℂ ℂ (-m + m))
      (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ T : 𝓢'(CoordinateSpace n, F),
          quantizeTempered F q hq.isUniform (quantizeTempered F a ha.isUniform T) =
            TemperedDistribution.smulLeftCLM F φ T + quantizeTempered F r hr.isUniform T := by
  obtain ⟨q, hq, hr, hrS⟩ := hp.exists_isSmoothing_sharp_sub_ofSpatial ha hφ hap
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := ℂ) hφ
  set M := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ ℂ) ((φ.smooth ⊤).smul contDiff_const)
  have hF' := hF.inclusion (neg_add_cancel m).ge
  refine ⟨q, hq, _, hr, hrS, fun T ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply, ← quantizeTempered_sharp hq.isUniform ha,
    quantizeTempered_congr (hq.sharp ha).isUniform (hF'.add hr).isUniform
      (b := inclusion (neg_add_cancel m).ge M + (q.sharp a ha - inclusion (neg_add_cancel m).ge M))
      (by simp),
    quantizeTempered_add hF'.isUniform hr.isUniform, add_apply,
    quantizeTempered_inclusion hF.isUniform, quantizeTempered_ofSpatial_smul_id]

/-- **Interior elliptic regularity for tempered distributions.** Let `p` be a scalar symbol
elliptic of order `m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol
with compact spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. If
`Op(a) T ∈ H^{s - m}` for a tempered distribution `T`, then `φ T ∈ H^s`. Unlike
`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`, `T` is not assumed to lie in any
Bessel-potential space: the smoothing remainder of the local parametrix maps every tempered
distribution into every `H^s` (`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`). -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : (quantizeTempered ℂ a ha.isUniform T).MemSobolev (s - m) 2) :
    (TemperedDistribution.smulLeftCLM ℂ φ T).MemSobolev s 2 := by
  obtain ⟨q, hq, r, hr, hrS, h⟩ :=
    hp.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add ℂ ha hφ hap
  have h₁ := memSobolev_quantizeTempered hq hT
  rw [h, sub_neg_eq_add, sub_add_cancel] at h₁
  convert h₁.sub (hrS.memSobolev_quantizeTempered hr T s) using 1
  exact (add_sub_cancel_right _ _).symm

/-- **Hypoellipticity on tempered distributions.** Let `p` be a scalar symbol elliptic of order
`m`, let `φ` be a compactly supported Schwartz function, and let `a` be a symbol with compact
spatial support that agrees with `p` on a neighbourhood of `tsupport φ`. If `Op(a) T` lies in
every `H^s` for a tempered distribution `T`, for instance if `Op(a) T = 0`, then `φ T` is a smooth
function `g`: it pairs with every Schwartz function `ψ` as `∫ ψ • g`. -/
theorem IsEllipticAbove.exists_contDiff_smulLeftCLM_eq_integral_of_forall_memSobolev
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : ∀ s, (quantizeTempered ℂ a ha.isUniform T).MemSobolev s 2) :
    ∃ g : CoordinateSpace n → ℂ, ContDiff ℝ ∞ g ∧
      ∀ ψ : 𝓢(CoordinateSpace n, ℂ), TemperedDistribution.smulLeftCLM ℂ φ T ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    hp.memSobolev_smulLeftCLM_of_memSobolev_quantizeTempered ha hφ hap (hT (s - m))

end Tempered

end Symbol

end TauCeti
