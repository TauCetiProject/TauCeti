/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Pseudolocality on Bessel-potential spaces

Let `a` be a symbol of order `m` on `ℝⁿ` with compact spatial support, so that its quantization
is a bounded operator `Op(a) : H^r → H^{r - m}` on the Bessel-potential spaces `H^r = H^{r,2}(ℝⁿ)`
for every real `r` (`TauCeti.Symbol.quantizeSobolev`). This file shows that `Op(a)` is
**pseudolocal** at the level of Sobolev regularity: near a point it loses at most `m` derivatives
of the regularity that its argument has near that point, whatever that argument does elsewhere.
Precisely, let `φ` and `χ` be Schwartz functions, `χ` compactly supported and equal to `1` on a
neighbourhood of `tsupport φ`, and let `u ∈ H^r`.

* `TauCeti.Symbol.memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM`: if
  `χ u ∈ H^s`, then `φ Op(a) u ∈ H^{s - m}`.
* `TauCeti.Symbol.exists_norm_smulLeftCLM_quantizeSobolev_le`: the corresponding estimate
  `‖φ Op(a) u‖_{H^{s - m}} ≤ C (‖χ u‖_{H^s} + ‖u‖_{H^r})` on `H^s`, for every `r ≤ s`.
* `TauCeti.Symbol.exists_contDiff_smulLeftCLM_quantizeSobolev`: if `χ u` lies in every `H^s`, then
  `φ Op(a) u` is a smooth function. So `Op(a) u` is smooth near every point near which `u` is
  smooth.

The order `r` is arbitrary, so `u` may be a distribution of negative order which is only regular
near `tsupport φ`. The underlying statement is about symbols vanishing outside a set `K`:

* `TauCeti.Symbol.memSobolev_quantizeSobolev_of_memSobolev_smulLeftCLM`: if `c` vanishes at
  positions outside `K` and `χ = 1` on a neighbourhood of `K`, then `χ u ∈ H^s` implies
  `Op(c) u ∈ H^{s - m}`. The values of `u` away from `K` only enter `Op(c) u` through a
  smoothing operator.

## Proof

Write `χ` also for the symbol `χ(x) id` of multiplication by `χ`. Since `c` vanishes outside `K`
and `χ = 1` near `K`, the pointwise composition `c ∘ χ` is `c`, and the composition symbol
`c # χ` of `Op(c) ∘ χ` agrees with `c ∘ χ` up to a smoothing symbol
(`TauCeti.Symbol.isSmoothing_sharp_sub_comp`): all terms of its asymptotic expansion beyond the
first involve derivatives of `χ`, which vanish near `K`. Hence
`Op(c) u = Op(c) (χ u) - Op(c # χ - c ∘ χ) u`
(`TauCeti.Symbol.exists_isSmoothing_toDistr_quantizeSobolev_eq_smulLeftCLM_sub`). The first
term lies in `H^{s - m}` by the Sobolev mapping theorem applied to `χ u ∈ H^s`, and the second
lies in every `H^t`. For the pseudolocality of `a`, apply this to the symbol `c = φ a`
(`TauCeti.Symbol.smulSpatial`), which vanishes outside `tsupport φ` and quantizes to `φ Op(a)`
(`TauCeti.Symbol.quantizeSobolev_smulSpatial`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, §1 (pseudolocality) and (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Set TemperedDistribution
open scoped Topology BesselPotentialSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Locality of quantizations in Sobolev regularity.** Let the symbol `c` of order `m` with
compact spatial support vanish at positions outside `K`, and let the Schwartz function `χ` have
compact support and equal `1` on a neighbourhood of `K`. If `u ∈ H^r` and `χ u ∈ H^s`, then
`Op(c) u ∈ H^{s - m}`. -/
theorem memSobolev_quantizeSobolev_of_memSobolev_smulLeftCLM {c : Symbol n V W m}
    (hc : c.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
    (hcK : ∀ x ∉ K, ∀ ξ, c.coefficient (x, ξ) = 0) {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) {r s : ℝ}
    {u : H^{r}(CoordinateSpace n, V)}
    (hu : MemSobolev s 2 (smulLeftCLM V (χ : CoordinateSpace n → ℂ) u.toDistr)) :
    MemSobolev (s - m) 2 (c.quantizeSobolev hc r u).toDistr := by
  obtain ⟨R, hR, hsm, hloc⟩ :=
    exists_isSmoothing_toDistr_quantizeSobolev_eq_smulLeftCLM_sub hc hcK hχ hχK
  -- `Op(c) u = Op(c) (χ u) - Op(R) u`, where `χ u ∈ H^s` and `R` is smoothing.
  rw [hloc r u, toDistr_quantizeSobolev_congr rfl hc hc
    (v := hu.toBesselPotentialSpace) (by simp)]
  exact (c.quantizeSobolev hc s _).memSobolev_toDistr.sub
    (hsm.memSobolev_toDistr_quantizeSobolev hR r (s - m) u)

variable {a : Symbol n V W m} {φ χ : 𝓢(CoordinateSpace n, ℂ)}

/-- **Pseudolocality in Sobolev regularity.** Let `a` be a symbol of order `m` with compact
spatial support, and let the Schwartz function `χ` have compact support and equal `1` on a
neighbourhood of `tsupport φ`. If `u ∈ H^r` and `χ u ∈ H^s`, then `φ Op(a) u ∈ H^{s - m}`: near
`tsupport φ`, `Op(a) u` has the regularity of `u` there, minus `m` derivatives. -/
theorem memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM
    (ha : a.HasCompactSpatialSupport) (hχ : HasCompactSupport χ)
    (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {r s : ℝ} {u : H^{r}(CoordinateSpace n, V)}
    (hu : MemSobolev s 2 (smulLeftCLM V (χ : CoordinateSpace n → ℂ) u.toDistr)) :
    MemSobolev (s - m) 2
      (smulLeftCLM W (φ : CoordinateSpace n → ℂ) (a.quantizeSobolev ha r u).toDistr) := by
  rw [← BesselPotentialSpace.toDistr_smulLeftCLM, ← ContinuousLinearMap.comp_apply,
    ← quantizeSobolev_smulSpatial ha φ (ha.smulSpatial φ)]
  exact memSobolev_quantizeSobolev_of_memSobolev_smulLeftCLM (ha.smulSpatial φ)
    (fun x hx ξ ↦ by rw [coefficient_smulSpatial, image_eq_zero_of_notMem_tsupport hx, zero_smul])
    hχ hχφ hu

/-- **The pseudolocal estimate.** Let `a` be a symbol of order `m` with compact spatial support,
and let the Schwartz function `χ` have compact support and equal `1` on a neighbourhood of
`tsupport φ`. For all real `r ≤ s` there is a constant `C` with
`‖φ Op(a) u‖_{H^{s - m}} ≤ C (‖χ u‖_{H^s} + ‖u‖_{H^r})` for every `u ∈ H^s`. -/
theorem exists_norm_smulLeftCLM_quantizeSobolev_le (ha : a.HasCompactSpatialSupport)
    (hχ : HasCompactSupport χ) (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {r s : ℝ}
    (hrs : r ≤ s) :
    ∃ C, ∀ u : H^{s}(CoordinateSpace n, V),
      ‖BesselPotentialSpace.smulLeftCLM (s - m) φ (a.quantizeSobolev ha s u)‖ ≤
        C * (‖BesselPotentialSpace.smulLeftCLM s χ u‖ +
          ‖BesselPotentialSpace.inclusion hrs u‖) := by
  obtain ⟨C, hC⟩ := exists_norm_quantizeSobolev_le_smulLeftCLM (ha.smulSpatial φ)
    (fun x hx ξ ↦ by rw [coefficient_smulSpatial, image_eq_zero_of_notMem_tsupport hx, zero_smul])
    hχ hχφ hrs
  refine ⟨C, fun u ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply, ← quantizeSobolev_smulSpatial ha φ (ha.smulSpatial φ)]
  exact hC u

/-- **Quantizations preserve local smoothness.** Let `a` be a symbol of order `m` with compact
spatial support, and let the Schwartz function `χ` have compact support and equal `1` on a
neighbourhood of `tsupport φ`. If `u ∈ H^r` and `χ u` lies in `H^s` for every real `s`, then
`φ Op(a) u` is a smooth function `g`: it pairs with every Schwartz function `ψ` as
`∫ ψ • g`. -/
theorem exists_contDiff_smulLeftCLM_quantizeSobolev (ha : a.HasCompactSpatialSupport)
    (hχ : HasCompactSupport χ) (hχφ : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) {r : ℝ}
    {u : H^{r}(CoordinateSpace n, V)}
    (hu : ∀ s, MemSobolev s 2 (smulLeftCLM V (χ : CoordinateSpace n → ℂ) u.toDistr)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(CoordinateSpace n, ℂ),
      smulLeftCLM W (φ : CoordinateSpace n → ℂ) (a.quantizeSobolev ha r u).toDistr ψ =
        ∫ x, ψ x • g x :=
  exists_contDiff_eq_integral_of_forall_memSobolev fun t ↦ by
    simpa only [add_sub_cancel_right] using
      memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM ha hχ hχφ (hu (t + m))

end Symbol

end TauCeti
