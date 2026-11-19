/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Pseudolocality
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

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
its consequences:

* `TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add`
  is the operator identity: for an elliptic `p`, there are a symbol `q` of order `-m`, vanishing
  at positions outside `tsupport φ`, and a smoothing symbol `r`, both with compact spatial
  support, with `Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`: **interior elliptic regularity**. If
  `u ∈ H^t` and `Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`, whatever the real numbers `s` and `t`.
* `TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_smulLeftCLM_quantizeSobolev`:
  **local elliptic regularity**. It suffices that `Op(a) u` is `H^{s - m}` near `tsupport φ`:
  if `χ Op(a) u ∈ H^{s - m}` for a compactly supported `χ` equal to `1` on a neighbourhood of
  `tsupport φ`, then `φ u ∈ H^s`.
* `TauCeti.Symbol.IsEllipticAbove.exists_contDiff_smulLeftCLM_of_forall_memSobolev`:
  **hypoellipticity**. If `χ Op(a) u` lies in every `H^s`, then `φ u` is a smooth function.

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
Since `q = φ b` vanishes at positions outside `tsupport φ`, the operator `Op(q)` only sees
`Op(a) u` near `tsupport φ`
(`TauCeti.Symbol.memSobolev_toDistr_quantizeSobolev_of_memSobolev_smulLeftCLM`), which gives the
local version.

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

/-- **The local parametrix of an elliptic operator.** Let `p` be elliptic of order `m`, let `φ`
be a compactly supported Schwartz function, and let `a` be a symbol with compact spatial support
that agrees with `p` on a neighbourhood of `tsupport φ`. There are a symbol `q` of order `-m`,
vanishing at positions outside `tsupport φ`, and a smoothing symbol `r`, both with compact spatial
support, such that `Op(q) Op(a) u = φ u + Op(r) u` for every `u ∈ H^s` and every real `s`. -/
theorem IsEllipticAbove.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ)
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ)) :
    ∃ (q : Symbol n W V (-m)) (hq : q.HasCompactSpatialSupport),
      (∀ x ∉ tsupport φ, ∀ ξ, q.coefficient (x, ξ) = 0) ∧
      ∃ (r : Symbol n V V (-m + m)) (hr : r.HasCompactSpatialSupport), r.IsSmoothing ∧
        ∀ (s : ℝ) (u : H^{s}(CoordinateSpace n, V)),
          (q.quantizeSobolev hq (s - m) (a.quantizeSobolev ha s u)).toDistr =
            (BesselPotentialSpace.smulLeftCLM s φ u).toDistr +
              (r.quantizeSobolev hr s u).toDistr := by
  obtain ⟨b, hL, -⟩ := hp.exists_isAsymptoticSum_sharpTerm
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hφ
  set F := ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V) ((φ.smooth ⊤).smul contDiff_const)
  set q := inclusion (zero_add (-m)).le (F.comp b)
  have hq : q.HasCompactSpatialSupport := (hF.comp_right b).inclusion _
  have hqb : ∀ x ξ, q.coefficient (x, ξ) = φ x • b.coefficient (x, ξ) := fun x ξ ↦ by
    simp [q, F]
  have hF' := hF.inclusion (neg_add_cancel m).ge
  have hr := (hq.sharp ha).sub hF'
  refine ⟨q, hq, fun x hx ξ ↦ by rw [hqb, image_eq_zero_of_notMem_tsupport hx, zero_smul], _, hr,
    isSmoothing_sharp_sub_ofSpatial hL (φ.smooth ⊤) hqb ha hap, fun s u ↦ ?_⟩
  rw [← toDistr_quantizeSobolev_sharp hq ha,
    toDistr_quantizeSobolev_congr
      (b := inclusion (neg_add_cancel m).ge F + (q.sharp a ha - inclusion (neg_add_cancel m).ge F))
      (by simp) (hq.sharp ha) (hF'.add hr) rfl,
    quantizeSobolev_add hF' hr, add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_congr (by simp) hF' hF rfl, toDistr_quantizeSobolev_ofSpatial_smul_id]

/-- **Local elliptic regularity.** Let `p` be elliptic of order `m`, let `a` be a symbol with
compact spatial support that agrees with `p` on a neighbourhood of `tsupport φ`, and let the
compactly supported Schwartz function `χ` equal `1` on a neighbourhood of `tsupport φ`. If
`u ∈ H^t` and `χ Op(a) u ∈ H^{s - m}`, then `φ u ∈ H^s`, for all real `s` and `t`: where
`Op(a) u` is `H^{s - m}`, `u` is `H^s`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_smulLeftCLM_quantizeSobolev
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ χ : 𝓢(CoordinateSpace n, ℂ)}
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    (hχ : HasCompactSupport χ) (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {s t : ℝ}
    {u : H^{t}(CoordinateSpace n, V)}
    (hu : (BesselPotentialSpace.smulLeftCLM (t - m) χ (a.quantizeSobolev ha t u)).toDistr.MemSobolev
      (s - m) 2) :
    (BesselPotentialSpace.smulLeftCLM t φ u).toDistr.MemSobolev s 2 := by
  have hφ : HasCompactSupport φ :=
    hχ.of_forall_mem_support_eq_one fun x hx ↦ hχφ.self_of_nhdsSet x (subset_tsupport φ hx)
  obtain ⟨q, hq, hqφ, r, hr, hrS, h⟩ :=
    hp.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_smulLeftCLM_add ha hφ hap
  -- `φ u = Op(q) Op(a) u - Op(r) u`, where `Op(q)` only sees `Op(a) u` near `tsupport φ`.
  have h₁ := memSobolev_toDistr_quantizeSobolev_of_memSobolev_smulLeftCLM hq hqφ hχ hχφ hu
  rw [sub_neg_eq_add, sub_add_cancel, h t u] at h₁
  simpa using h₁.sub (hrS.memSobolev_toDistr_quantizeSobolev hr t s u)

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
  obtain ⟨χ, hχ, -, hχφ⟩ := IsCompact.exists_schwartzMap_cutoff hφ isOpen_univ (Set.subset_univ _)
  refine hp.memSobolev_smulLeftCLM_of_memSobolev_smulLeftCLM_quantizeSobolev ha hap hχ hχφ ?_
  rw [BesselPotentialSpace.toDistr_smulLeftCLM]
  exact hu.smulLeftCLM χ

/-- **Elliptic operators are hypoelliptic.** Let `p` be elliptic, let `a` be a symbol with compact
spatial support that agrees with `p` on a neighbourhood of `tsupport φ`, and let the compactly
supported Schwartz function `χ` equal `1` on a neighbourhood of `tsupport φ`. If `u ∈ H^t` and
`χ Op(a) u` lies in every `H^s`, then `φ u` is a smooth function `g`: it pairs with every Schwartz
function `ψ` as `∫ ψ • g`. So `u` is smooth wherever `Op(a) u` is. -/
theorem IsEllipticAbove.exists_contDiff_smulLeftCLM_of_forall_memSobolev
    (hp : p.IsEllipticAbove R) (ha : a.HasCompactSpatialSupport) {φ χ : 𝓢(CoordinateSpace n, ℂ)}
    (hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ))
    (hχ : HasCompactSupport χ) (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {t : ℝ}
    {u : H^{t}(CoordinateSpace n, V)}
    (hu : ∀ s, TemperedDistribution.MemSobolev s 2
      (BesselPotentialSpace.smulLeftCLM (t - m) χ (a.quantizeSobolev ha t u)).toDistr) :
    ∃ g : CoordinateSpace n → V, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(CoordinateSpace n, ℂ),
      (BesselPotentialSpace.smulLeftCLM t φ u).toDistr ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    hp.memSobolev_smulLeftCLM_of_memSobolev_smulLeftCLM_quantizeSobolev ha hap hχ hχφ (hu (s - m))

end Symbol

end TauCeti
