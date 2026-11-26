/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Lp.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Distribution

/-!
# Elliptic estimates and regularity on `H^{s,p}(ℝⁿ)` for uniform symbols

Let `a` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`, for complex Hilbert spaces
`V` and `W`, whose estimates hold uniformly in the position (`TauCeti.Symbol.IsUniform`) and which
is uniformly elliptic above some radius: `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for `‖ξ‖ ≥ R`, with `C` and `R`
independent of `x` (`TauCeti.Symbol.IsUniformlyEllipticAbove`). For `1 < p < ∞` its quantization is
a bounded operator `T = Op(a) : H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)` between Bessel-potential
spaces for every real `s` (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace`). This file proves
the `Lᵖ` elliptic theory of `T` on the whole space, in the namespace `TauCeti.Symbol`:

* `IsUniformlyEllipticAbove.exists_quantizeUniformBesselPotentialSpace_parametrix`:
  **the parametrix on `H^{s,p}`.** There is a bounded operator `B : H^{s - m,p} → H^{s,p}` with

  `B T = 1 + K ι` and `T B = 1 + K' ι'`,

  where for every `r ≤ s` the operator `K` is bounded `H^{r,p} → H^{s,p}` and `ι` is the inclusion
  `H^{s,p} ⊆ H^{r,p}`, and likewise for `K'` and `ι'` below the order `s - m`. So `T` is invertible
  modulo operators that gain any number of derivatives.
* `IsUniformlyEllipticAbove.exists_norm_le_quantizeUniformBesselPotentialSpace`:
  **the global elliptic estimate.** For all real `r ≤ s` there is a constant `C` with

  `‖u‖_{H^{s,p}} ≤ C (‖T u‖_{H^{s - m,p}} + ‖u‖_{H^{r,p}})` for all `u ∈ H^{s,p}(ℝⁿ; V)`.

* `IsUniformlyEllipticAbove.memSobolev_of_memSobolev_quantizeUniformBesselPotentialSpace`:
  **global elliptic regularity.** If `u ∈ H^{t,p}` and `T u ∈ H^{s - m,p}`, then `u ∈ H^{s,p}`, for
  all real `s` and `t`.
* `IsUniformlyEllipticAbove.map_toDistrCLM_ker_quantizeUniformBesselPotentialSpace`:
  **the kernel does not depend on the order.** As a space of tempered distributions, the kernel of
  `T` on `H^{s,p}` is the same for every real `s`.
* `IsUniformlySmoothing.exists_quantizeBesselPotentialSpace`: the quantization of a uniformly
  smoothing symbol extends to a bounded operator `H^{r,p} → H^{σ,p}` for all real `r` and `σ`, the
  `Lᵖ` form of `TauCeti.Symbol.IsUniformlySmoothing.hasSobolevExtension_quantizeUniformCLM`.

The lower-order term `‖u‖_{H^{r,p}}` in the estimate cannot be dropped, since a uniformly elliptic
operator may have a kernel: for a smooth compactly supported `ψ` equal to `1` near `0`, the symbol
`1 - ψ(ξ)` is uniformly elliptic of order `0`, and its quantization, a Fourier multiplier, vanishes
on the nonzero Schwartz functions whose Fourier transforms are supported where `ψ = 1`. For `p = 2`
the estimate and regularity are proved with Plancherel's theorem alone in
`TauCeti.Analysis.Pseudodifferential.GlobalEllipticRegularity`; for `p ≠ 2` the boundedness of `T`
rests on the Calderón–Zygmund theory of `TauCeti.Analysis.Pseudodifferential.Lp.CalderonZygmund`.

## The argument

The uniform parametrix
(`TauCeti.Symbol.IsUniformlyEllipticAbove.exists_quantizeUniformCLM_comp_eq_id_add`) is a uniform
symbol `b` of order `-m` with `Op(b) Op(a) = 1 + Op(q)` and `Op(a) Op(b) = 1 + Op(q')` on Schwartz
space, for uniformly smoothing symbols `q` and `q'`. A uniformly smoothing symbol is uniform of
every order, so `Op(q)` is bounded `H^{r,p} → H^{σ,p}` for all real `r` and `σ`
(`TauCeti.Symbol.IsUniformlySmoothing.exists_quantizeBesselPotentialSpace`). By density of the
Schwartz functions in `H^{s,p}`, the two operator identities hold on `H^{s,p}`, which gives the
parametrix and the estimate. For `u ∈ H^{t,p}` with `T u ∈ H^{s - m,p}` the identity
`u = Op(b) (T u) - Op(q) u` of tempered distributions shows `u ∈ H^{s,p}`: the operators `Op(b)` on
the different spaces `H^{σ,p}` agree on tempered distributions
(`HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_congr` in the
namespace `TauCeti.Symbol`), so `Op(b) (T u)` lies in `H^{s,p}`, and `Op(q) u` lies in every
`H^{σ,p}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture II,
  (3.1)–(3.8).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ENNReal

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Uniformly smoothing symbols on `H^{s,p}` -/

/-- **Uniformly smoothing symbols gain every number of derivatives on `H^{s,p}`.** Let
`1 < p < ∞`. The quantization of a uniformly smoothing symbol extends from Schwartz functions to a
bounded operator `H^{r,p} → H^{σ,p}` for all real `r` and `σ`. -/
theorem IsUniformlySmoothing.exists_quantizeBesselPotentialSpace {q : Symbol n V W m}
    (hq : q.IsUniformlySmoothing) (hp : 1 < p) (hp_top : p ≠ ∞) (r σ : ℝ) :
    ∃ K : H^{r, p}(CoordinateSpace n, V) →L[ℂ] H^{σ, p}(CoordinateSpace n, W),
      K ∘L SchwartzMap.toBesselPotentialSpaceCLM r p =
        SchwartzMap.toBesselPotentialSpaceCLM σ p ∘L quantizeUniformCLM q hq.isUniform := by
  obtain ⟨q', hq', hqq'⟩ := isUniformlySmoothing_iff.1 hq (r - σ)
  refine ⟨BesselPotentialSpace.inclusion (by linarith) ∘L
    q'.quantizeUniformBesselPotentialSpace hq' r p, ContinuousLinearMap.ext fun u ↦ ?_⟩
  simp [quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM hq' r hp hp_top,
    quantizeUniformCLM_congr hq.isUniform hq' hqq'.symm]

/-! ### The parametrix -/

variable {a : Symbol n V W m}

/-- The parametrix identity on Bessel-potential spaces: if `Op(b) Op(a) = 1 + Op(q)` on Schwartz
space and `K` extends `Op(q)` to `H^{σ,p} → H^{ρ,p}`, then `Op(b) (Op(a) u) = u + K u` as tempered
distributions for every `u ∈ H^{σ,p}`. -/
private theorem toDistr_quantizeUniformBesselPotentialSpace_comp_eq_add (hp : 1 < p)
    (hp_top : p ≠ ∞) {m' : ℝ} {hau : a.IsUniform} {b : Symbol n W V m'} {hb : b.IsUniform}
    {q : Symbol n V V 0} {hq : q.IsUniform}
    (hbaq : quantizeUniformCLM b hb ∘L quantizeUniformCLM a hau =
      ContinuousLinearMap.id ℂ _ + quantizeUniformCLM q hq)
    {σ ρ : ℝ} {K : H^{σ, p}(CoordinateSpace n, V) →L[ℂ] H^{ρ, p}(CoordinateSpace n, V)}
    (hK : K ∘L SchwartzMap.toBesselPotentialSpaceCLM σ p =
      SchwartzMap.toBesselPotentialSpaceCLM ρ p ∘L quantizeUniformCLM q hq)
    (u : H^{σ, p}(CoordinateSpace n, V)) :
    (b.quantizeUniformBesselPotentialSpace hb (σ - m) p
        (a.quantizeUniformBesselPotentialSpace hau σ p u)).toDistr =
      u.toDistr + (K u).toDistr := by
  have key : BesselPotentialSpace.toDistrCLM _ V _ p ∘L
      b.quantizeUniformBesselPotentialSpace hb (σ - m) p ∘L
        a.quantizeUniformBesselPotentialSpace hau σ p =
      BesselPotentialSpace.toDistrCLM _ V _ p +
        BesselPotentialSpace.toDistrCLM _ V _ p ∘L K := by
    refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun w ↦ ?_
    have hw := congr($hbaq w)
    have hKw := congr($hK w)
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply] at hw hKw
    simp [quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM hau σ hp hp_top,
      quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM hb (σ - m) hp hp_top, hw, hKw]
  simpa using congr($key u)

/-- **The parametrix on `H^{s,p}`.** Let `a` be a symbol of order `m` whose estimates hold uniformly
in the position and which is uniformly elliptic above some radius, let `1 < p < ∞`, and let
`T : H^{s,p} → H^{s - m,p}` be its quantization. There is a bounded operator
`B : H^{s - m,p} → H^{s,p}` inverting `T` on both sides modulo operators that gain any number of
derivatives: for every `r ≤ s` there is a bounded `K : H^{r,p} → H^{s,p}` with `B T = 1 + K ι`, and
for every `r ≤ s - m` a bounded `K' : H^{r,p} → H^{s - m,p}` with `T B = 1 + K' ι'`, where `ι` and
`ι'` are the inclusions into `H^{r,p}`. -/
theorem IsUniformlyEllipticAbove.exists_quantizeUniformBesselPotentialSpace_parametrix
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) (hp : 1 < p) (hp_top : p ≠ ∞)
    (s : ℝ) :
    ∃ B : H^{s - m, p}(CoordinateSpace n, W) →L[ℂ] H^{s, p}(CoordinateSpace n, V),
      (∀ r (hrs : r ≤ s), ∃ K : H^{r, p}(CoordinateSpace n, V) →L[ℂ] H^{s, p}(CoordinateSpace n, V),
        B ∘L a.quantizeUniformBesselPotentialSpace hau s p =
          ContinuousLinearMap.id ℂ _ + K ∘L BesselPotentialSpace.inclusion hrs) ∧
      ∀ r (hrs : r ≤ s - m), ∃ K' : H^{r, p}(CoordinateSpace n, W) →L[ℂ]
          H^{s - m, p}(CoordinateSpace n, W),
        a.quantizeUniformBesselPotentialSpace hau s p ∘L B =
          ContinuousLinearMap.id ℂ _ + K' ∘L BesselPotentialSpace.inclusion hrs := by
  obtain ⟨b, hb, ⟨q, hq, hbaq⟩, ⟨q', hq', habq⟩⟩ := ha.exists_quantizeUniformCLM_comp_eq_id_add hau
  refine ⟨BesselPotentialSpace.inclusion (by linarith) ∘L
    b.quantizeUniformBesselPotentialSpace hb (s - m) p, fun r hrs ↦ ?_, fun r hrs ↦ ?_⟩
  · obtain ⟨K, hK⟩ := hq.exists_quantizeBesselPotentialSpace hp hp_top r s
    refine ⟨K, ContinuousLinearMap.ext fun u ↦ BesselPotentialSpace.ext ?_⟩
    simpa using toDistr_quantizeUniformBesselPotentialSpace_comp_eq_add hp hp_top hbaq
      (K := K ∘L BesselPotentialSpace.inclusion hrs)
      (ContinuousLinearMap.ext fun w ↦ by simpa using congr($hK w)) u
  · obtain ⟨K', hK'⟩ := hq'.exists_quantizeBesselPotentialSpace hp hp_top r (s - m)
    have ha' := hau.hasBesselPotentialSpaceExtension hp hp_top
    refine ⟨K', ContinuousLinearMap.ext fun f ↦ BesselPotentialSpace.ext ?_⟩
    -- `Op(a)` on `H^{s,p}` and on `H^{s - m + m,p}` agree on tempered distributions.
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ha'.toDistr_quantizeUniformBesselPotentialSpace_congr ha' rfl hp_top
        (BesselPotentialSpace.toDistr_inclusion _ _)]
    simpa using toDistr_quantizeUniformBesselPotentialSpace_comp_eq_add hp hp_top habq
      (K := K' ∘L BesselPotentialSpace.inclusion hrs)
      (ContinuousLinearMap.ext fun w ↦ by simpa using congr($hK' w)) f

/-! ### The global elliptic estimate -/

/-- **The global elliptic estimate on `H^{s,p}`.** Let `a` be a symbol of order `m` whose estimates
hold uniformly in the position and which is uniformly elliptic above some radius, and let
`1 < p < ∞`. For every real `r ≤ s` there is a constant `C` with

`‖u‖_{H^{s,p}} ≤ C (‖Op(a) u‖_{H^{s - m,p}} + ‖u‖_{H^{r,p}})`

for all `u ∈ H^{s,p}(ℝⁿ; V)`. No cutoff in the position is needed. -/
theorem IsUniformlyEllipticAbove.exists_norm_le_quantizeUniformBesselPotentialSpace
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) (hp : 1 < p) (hp_top : p ≠ ∞)
    {r s : ℝ} (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s, p}(CoordinateSpace n, V),
      ‖u‖ ≤ C * (‖a.quantizeUniformBesselPotentialSpace hau s p u‖ +
        ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨B, hB, -⟩ := ha.exists_quantizeUniformBesselPotentialSpace_parametrix hau hp hp_top s
  obtain ⟨K, hK⟩ := hB r hrs
  refine ⟨‖B‖ + ‖K‖, fun u ↦ ?_⟩
  set T := a.quantizeUniformBesselPotentialSpace hau s p
  -- `u = B (T u) - K u`.
  have hu : u = B (T u) - K (BesselPotentialSpace.inclusion hrs u) := by
    have := congr($hK u)
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply] at this
    rw [this, add_sub_cancel_right]
  calc ‖u‖ = ‖B (T u) - K (BesselPotentialSpace.inclusion hrs u)‖ := congrArg _ hu
    _ ≤ ‖B‖ * ‖T u‖ + ‖K‖ * ‖BesselPotentialSpace.inclusion hrs u‖ :=
        (norm_sub_le _ _).trans (add_le_add (B.le_opNorm _) (K.le_opNorm _))
    _ ≤ (‖B‖ + ‖K‖) * (‖T u‖ + ‖BesselPotentialSpace.inclusion hrs u‖) := by
        nlinarith [norm_nonneg B, norm_nonneg K, norm_nonneg (T u),
          norm_nonneg (BesselPotentialSpace.inclusion hrs u)]

/-! ### Global elliptic regularity -/

/-- **Global elliptic regularity on `H^{s,p}`.** Let `a` be a symbol of order `m` whose estimates
hold uniformly in the position and which is uniformly elliptic above some radius, and let
`1 < p < ∞`. If `u ∈ H^{t,p}(ℝⁿ; V)` and `Op(a) u ∈ H^{s - m,p}`, then `u ∈ H^{s,p}`, for all real
`s` and `t`. -/
theorem IsUniformlyEllipticAbove.memSobolev_of_memSobolev_quantizeUniformBesselPotentialSpace
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) (hp : 1 < p) (hp_top : p ≠ ∞)
    {s t : ℝ} {u : H^{t, p}(CoordinateSpace n, V)}
    (hu : (a.quantizeUniformBesselPotentialSpace hau t p u).toDistr.MemSobolev (s - m) p) :
    u.toDistr.MemSobolev s p := by
  obtain ⟨b, hb, ⟨q, hq, hbaq⟩, -⟩ := ha.exists_quantizeUniformCLM_comp_eq_id_add hau
  obtain ⟨K, hK⟩ := hq.exists_quantizeBesselPotentialSpace hp hp_top t s
  have hb' := hb.hasBesselPotentialSpaceExtension hp hp_top
  -- `u = Op(b) (Op(a) u) - Op(q) u`, where `Op(b) (Op(a) u)` only depends on the tempered
  -- distribution `Op(a) u ∈ H^{s - m,p}`, and `Op(q) u ∈ H^{s,p}`.
  have hBv : (b.quantizeUniformBesselPotentialSpace hb (t - m) p
        (a.quantizeUniformBesselPotentialSpace hau t p u)).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb (s - m) p hu.toBesselPotentialSpace).toDistr :=
    hb'.toDistr_quantizeUniformBesselPotentialSpace_congr hb' rfl hp_top
      hu.toBesselPotentialSpace_toDistr.symm
  have hid : u.toDistr = (b.quantizeUniformBesselPotentialSpace hb (s - m) p
      hu.toBesselPotentialSpace).toDistr - (K u).toDistr := by
    rw [← hBv, toDistr_quantizeUniformBesselPotentialSpace_comp_eq_add hp hp_top hbaq hK u,
      add_sub_cancel_right]
  rw [hid]
  exact (BesselPotentialSpace.memSobolev_toDistr_of_eq _ (by ring)).sub
    (BesselPotentialSpace.memSobolev_toDistr _)

/-- **The kernel of a uniformly elliptic operator does not depend on the order.** Let `a` be a
symbol of order `m` whose estimates hold uniformly in the position and which is uniformly elliptic
above some radius, and let `1 < p < ∞`. The kernels of `Op(a) : H^{s,p} → H^{s - m,p}` and of
`Op(a) : H^{t,p} → H^{t - m,p}` consist of the same tempered distributions, for all real `s` and
`t`. -/
theorem IsUniformlyEllipticAbove.map_toDistrCLM_ker_quantizeUniformBesselPotentialSpace
    (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) (hp : 1 < p) (hp_top : p ≠ ∞)
    (s t : ℝ) :
    (LinearMap.ker (a.quantizeUniformBesselPotentialSpace hau s p :
        H^{s, p}(CoordinateSpace n, V) →ₗ[ℂ] H^{s - m, p}(CoordinateSpace n, W))).map
        (BesselPotentialSpace.toDistrCLM (CoordinateSpace n) V s p :
          H^{s, p}(CoordinateSpace n, V) →ₗ[ℂ] 𝓢'(CoordinateSpace n, V)) =
      (LinearMap.ker (a.quantizeUniformBesselPotentialSpace hau t p :
        H^{t, p}(CoordinateSpace n, V) →ₗ[ℂ] H^{t - m, p}(CoordinateSpace n, W))).map
        (BesselPotentialSpace.toDistrCLM (CoordinateSpace n) V t p :
          H^{t, p}(CoordinateSpace n, V) →ₗ[ℂ] 𝓢'(CoordinateSpace n, V)) := by
  have ha' := hau.hasBesselPotentialSpaceExtension hp hp_top
  -- An element of the kernel on `H^{s,p}` lies in `H^{t,p}`, and there it is in the kernel.
  have key (s t : ℝ) (u : H^{s, p}(CoordinateSpace n, V))
      (hu : a.quantizeUniformBesselPotentialSpace hau s p u = 0) :
      ∃ v : H^{t, p}(CoordinateSpace n, V),
        a.quantizeUniformBesselPotentialSpace hau t p v = 0 ∧ v.toDistr = u.toDistr := by
    have hmem : u.toDistr.MemSobolev t p :=
      ha.memSobolev_of_memSobolev_quantizeUniformBesselPotentialSpace hau hp hp_top
        (by simp [hu])
    refine ⟨hmem.toBesselPotentialSpace, BesselPotentialSpace.ext ?_,
      hmem.toBesselPotentialSpace_toDistr⟩
    rw [ha'.toDistr_quantizeUniformBesselPotentialSpace_congr ha' rfl hp_top
      hmem.toBesselPotentialSpace_toDistr, hu, BesselPotentialSpace.toDistr_zero,
      BesselPotentialSpace.toDistr_zero]
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    BesselPotentialSpace.toDistrCLM_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact key s t u hu
  · rintro ⟨u, hu, rfl⟩
    exact key t s u hu

end Symbol

end TauCeti
