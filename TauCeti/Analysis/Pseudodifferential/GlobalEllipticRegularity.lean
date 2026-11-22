/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.UniformSobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Elliptic estimates and regularity on all of `ℝⁿ` for uniform symbols

Let `a` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, for complex Hilbert spaces
`V` and `W`, whose estimates hold uniformly in the position (`TauCeti.Symbol.IsUniform`) and which
is uniformly elliptic above some radius: `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for `‖ξ‖ ≥ R`, with `C` and `R`
independent of `x` (`TauCeti.Symbol.IsUniformlyEllipticAbove`). Its quantization `Op(a)` extends to
bounded operators `T : H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` for every real `s`
(`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`). This file proves the elliptic estimate
and elliptic regularity for these operators on the whole space, with no cutoff:

* `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_norm_le`: **the global elliptic estimate.** For
  all real `r ≤ s` there is a constant `C` with

  `‖u‖_{H^s} ≤ C (‖T u‖_{H^{s - m}} + ‖u‖_{H^r})` for all `u ∈ H^s(ℝⁿ; V)`.

* `TauCeti.Symbol.IsUniformlyEllipticAbove.memSobolev_toDistr_of_memSobolev`: **global elliptic
  regularity.** If `u ∈ H^t` and `T u ∈ H^{s - m}`, then `u ∈ H^s`, for all real `s` and `t`.
* `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_contDiff_of_forall_memSobolev`:
  **hypoellipticity.** If `u ∈ H^t` and `T u` lies in every `H^σ`, for instance if `T u = 0`, then
  `u` is a smooth function.

The interior versions `TauCeti.Symbol.IsEllipticAbove.exists_norm_smulLeftCLM_le` and
`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM` only need ellipticity above a radius on a
compact set of positions, and conclude for `φ u` with a compactly supported cutoff `φ`, with
constants depending on `φ`. The lower-order term `‖u‖_{H^r}` cannot be dropped, since a uniformly
elliptic operator may have a kernel: for a smooth compactly supported `ψ` equal to `1` near `0`,
the symbol `1 - ψ(ξ)` is uniformly elliptic of order `0`, and its quantization, a Fourier
multiplier, vanishes on the nonzero Schwartz functions whose Fourier transforms are supported in a
small enough ball around `0`.

## Proof outline

The uniform parametrix
(`TauCeti.Symbol.IsUniformlyEllipticAbove.exists_quantizeUniformCLM_comp_eq_id_add`) is a uniform
symbol `b` of order `-m` with `Op(b) Op(a) = 1 + Op(r)` on Schwartz space, for a uniformly
smoothing symbol `r`. Both `Op(b) : H^{s - m} → H^s` and `Op(r) : H^r → H^s` are bounded, for all
real `r` and `s` (`TauCeti.Symbol.IsUniformlySmoothing.hasSobolevExtension_quantizeUniformCLM`),
and by density of the Schwartz functions the identity `u = Op(b) (T u) - Op(r) u` holds on every
`H^t`, as an identity of tempered distributions. For `u ∈ H^s` this gives the estimate. For
`u ∈ H^t` with `T u ∈ H^{s - m}`, the first term lies in `H^s` and so does the second, because `r`
is smoothing; Sobolev realizations of `Op(b)` at different orders agree as maps of tempered
distributions (`SchwartzMap.toDistr_apply_congr_of_comp_eq`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ} {a : Symbol n V W m}

/-- The left parametrix identity on Bessel-potential spaces: if `Op(b) Op(a) = 1 + Op(r)` on
Schwartz space, then `B (T u) = u + Rr u` as tempered distributions for all Sobolev realizations
`T` of `Op(a)`, `B` of `Op(b)` and `Rr` of `Op(r)` on `H^σ`, whatever their target orders. -/
private theorem toDistr_apply_apply_eq_add {hau : a.IsUniform} {b : Symbol n W V (-m)}
    {hb : b.IsUniform} {r : Symbol n V V 0} {hr : r.IsUniform}
    (hbar : quantizeUniformCLM b hb ∘L quantizeUniformCLM a hau =
      ContinuousLinearMap.id ℂ _ + quantizeUniformCLM r hr)
    {σ ρ ρ' : ℝ} {T : H^{σ}(CoordinateSpace n, V) →L[ℂ] H^{σ - m}(CoordinateSpace n, W)}
    (hT : T ∘L SchwartzMap.toBesselPotentialSpaceCLM σ 2 =
      SchwartzMap.toBesselPotentialSpaceCLM (σ - m) 2 ∘L quantizeUniformCLM a hau)
    {B : H^{σ - m}(CoordinateSpace n, W) →L[ℂ] H^{ρ}(CoordinateSpace n, V)}
    (hB : B ∘L SchwartzMap.toBesselPotentialSpaceCLM (σ - m) 2 =
      SchwartzMap.toBesselPotentialSpaceCLM ρ 2 ∘L quantizeUniformCLM b hb)
    {Rr : H^{σ}(CoordinateSpace n, V) →L[ℂ] H^{ρ'}(CoordinateSpace n, V)}
    (hRr : Rr ∘L SchwartzMap.toBesselPotentialSpaceCLM σ 2 =
      SchwartzMap.toBesselPotentialSpaceCLM ρ' 2 ∘L quantizeUniformCLM r hr)
    (u : H^{σ}(CoordinateSpace n, V)) :
    (B (T u)).toDistr = u.toDistr + (Rr u).toDistr := by
  have key : BesselPotentialSpace.inclusion (min_le_left ρ (min σ ρ')) ∘L B ∘L T =
      BesselPotentialSpace.inclusion ((min_le_right ρ _).trans (min_le_left σ ρ')) +
        BesselPotentialSpace.inclusion ((min_le_right ρ _).trans (min_le_right σ ρ')) ∘L Rr := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun w ↦
      BesselPotentialSpace.ext ?_
    have hw := congrArg (fun A ↦ (A w : 𝓢'(CoordinateSpace n, V))) hbar
    have hTw := congrArg (fun A ↦ A w) hT
    have hBw := congrArg (fun A ↦ A (quantizeUniformCLM a hau w)) hB
    have hRw := congrArg (fun A ↦ (A w).toDistr) hRr
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply, map_add, SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
      at hw hTw hBw hRw
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      BesselPotentialSpace.toDistr_add, BesselPotentialSpace.toDistr_inclusion, hTw, hBw, hRw,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM, hw]
  simpa using congrArg (fun A ↦ (A u).toDistr) key

/-! ### The global elliptic estimate -/

/-- **The global elliptic estimate.** Let `a` be a symbol of order `m` whose estimates hold
uniformly in the position and which is uniformly elliptic above some radius, and let
`T : H^s → H^{s - m}` be the bounded operator extending `Op(a)` from Schwartz functions. For every
real `r ≤ s` there is a constant `C` with

`‖u‖_{H^s} ≤ C (‖T u‖_{H^{s - m}} + ‖u‖_{H^r})`

for all `u ∈ H^s(ℝⁿ; V)`. No cutoff in the position is needed. -/
theorem IsUniformlyEllipticAbove.exists_norm_le (ha : a.IsUniformlyEllipticAbove R)
    (hau : a.IsUniform) {r s : ℝ} (hrs : r ≤ s)
    {T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W)}
    (hT : T ∘L SchwartzMap.toBesselPotentialSpaceCLM s 2 =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 ∘L quantizeUniformCLM a hau) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖u‖ ≤ C * (‖T u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨b, hb, ⟨q, hq, hbar⟩, -⟩ := ha.exists_quantizeUniformCLM_comp_eq_id_add hau
  obtain ⟨B, hB⟩ := SchwartzMap.hasSobolevExtension_iff.1 <|
    hasSobolevExtension_quantizeUniformCLM b hb (s - m)
  obtain ⟨Q, hQ⟩ := SchwartzMap.hasSobolevExtension_iff.1 <|
    hq.hasSobolevExtension_quantizeUniformCLM r s
  have hQ' : (Q ∘L BesselPotentialSpace.inclusion hrs) ∘L
      SchwartzMap.toBesselPotentialSpaceCLM s 2 =
        SchwartzMap.toBesselPotentialSpaceCLM s 2 ∘L quantizeUniformCLM q hq.isUniform := by
    rw [← hQ]
    ext1 w
    simp
  refine ⟨‖B‖ + ‖Q‖, fun u ↦ ?_⟩
  -- `u + Op(q) u = Op(b) (T u)` as tempered distributions.
  have hu : ‖u + Q (BesselPotentialSpace.inclusion hrs u)‖ ≤ ‖B (T u)‖ :=
    BesselPotentialSpace.norm_le_of_toDistr_eq (by linarith) (by
      rw [toDistr_apply_apply_eq_add hbar hT hB hQ' u, ContinuousLinearMap.comp_apply,
        BesselPotentialSpace.toDistr_add])
  calc ‖u‖ = ‖(u + Q (BesselPotentialSpace.inclusion hrs u)) -
        Q (BesselPotentialSpace.inclusion hrs u)‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖B‖ * ‖T u‖ + ‖Q‖ * ‖BesselPotentialSpace.inclusion hrs u‖ :=
        (norm_sub_le _ _).trans (add_le_add (hu.trans (B.le_opNorm _)) (Q.le_opNorm _))
    _ ≤ (‖B‖ + ‖Q‖) * (‖T u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
        nlinarith [norm_nonneg B, norm_nonneg Q, norm_nonneg (T u),
          norm_nonneg (BesselPotentialSpace.inclusion hrs u)]

/-! ### Global elliptic regularity -/

/-- **Global elliptic regularity.** Let `a` be a symbol of order `m` whose estimates hold uniformly
in the position and which is uniformly elliptic above some radius, and let
`T : H^t → H^{t - m}` be the bounded operator extending `Op(a)` from Schwartz functions. If
`u ∈ H^t(ℝⁿ; V)` and `T u ∈ H^{s - m}`, then `u ∈ H^s`, for all real `s` and `t`. -/
theorem IsUniformlyEllipticAbove.memSobolev_toDistr_of_memSobolev
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) {s t : ℝ}
    {T : H^{t}(CoordinateSpace n, V) →L[ℂ] H^{t - m}(CoordinateSpace n, W)}
    (hT : T ∘L SchwartzMap.toBesselPotentialSpaceCLM t 2 =
      SchwartzMap.toBesselPotentialSpaceCLM (t - m) 2 ∘L quantizeUniformCLM a hau)
    {u : H^{t}(CoordinateSpace n, V)} (hu : (T u).toDistr.MemSobolev (s - m) 2) :
    u.toDistr.MemSobolev s 2 := by
  obtain ⟨b, hb, ⟨q, hq, hbar⟩, -⟩ := ha.exists_quantizeUniformCLM_comp_eq_id_add hau
  obtain ⟨B, hB⟩ := SchwartzMap.hasSobolevExtension_iff.1 <|
    hasSobolevExtension_quantizeUniformCLM b hb (t - m)
  obtain ⟨B', hB'⟩ := SchwartzMap.hasSobolevExtension_iff.1 <|
    hasSobolevExtension_quantizeUniformCLM b hb (s - m)
  obtain ⟨Q, hQ⟩ := SchwartzMap.hasSobolevExtension_iff.1 <|
    hq.hasSobolevExtension_quantizeUniformCLM t s
  -- `u = Op(b) (T u) - Op(q) u`, where `Op(b) (T u)` only depends on the tempered distribution
  -- `T u ∈ H^{s - m}`, and `Op(q) u ∈ H^s`.
  have hBv : (B (T u)).toDistr = (B' hu.toBesselPotentialSpace).toDistr :=
    SchwartzMap.toDistr_apply_congr_of_comp_eq ENNReal.ofNat_ne_top hB hB'
      hu.toBesselPotentialSpace_toDistr.symm
  have hid : u.toDistr = (B' hu.toBesselPotentialSpace).toDistr - (Q u).toDistr := by
    rw [← hBv, toDistr_apply_apply_eq_add hbar hT hB hQ u, add_sub_cancel_right]
  rw [hid]
  exact (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring)).sub
    (BesselPotentialSpace.memSobolev_toDistr _)

/-- **Hypoellipticity of uniformly elliptic operators.** Let `a` be a symbol of order `m` whose
estimates hold uniformly in the position and which is uniformly elliptic above some radius, and
let `T : H^t → H^{t - m}` be the bounded operator extending `Op(a)` from Schwartz functions. If
`u ∈ H^t(ℝⁿ; V)` and `T u` lies in every `H^σ`, for instance if `T u = 0`, then `u` is a smooth
function `g`: it pairs with every Schwartz function `ψ` as `∫ ψ • g`. -/
theorem IsUniformlyEllipticAbove.exists_contDiff_of_forall_memSobolev
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) {t : ℝ}
    {T : H^{t}(CoordinateSpace n, V) →L[ℂ] H^{t - m}(CoordinateSpace n, W)}
    (hT : T ∘L SchwartzMap.toBesselPotentialSpaceCLM t 2 =
      SchwartzMap.toBesselPotentialSpaceCLM (t - m) 2 ∘L quantizeUniformCLM a hau)
    {u : H^{t}(CoordinateSpace n, V)} (hu : ∀ σ : ℝ, (T u).toDistr.MemSobolev σ 2) :
    ∃ g : CoordinateSpace n → V, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(CoordinateSpace n, ℂ),
      u.toDistr ψ = ∫ x, ψ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    ha.memSobolev_toDistr_of_memSobolev hau hT (hu (s - m))

end Symbol

end TauCeti
