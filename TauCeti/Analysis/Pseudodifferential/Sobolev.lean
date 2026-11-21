/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Map
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Parametric
import TauCeti.Analysis.Pseudodifferential.FourierSchur
import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Sobolev mapping of pseudodifferential operators with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) that vanishes for positions
outside a compact set, with values in operators between complex Hilbert spaces `V` and `W`. Its
left quantization `Op(a)`, defined on Schwartz functions by `TauCeti.quantizeSchwartzValue`, extends
to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Mathlib's Bessel-potential spaces,
for every real `s` (`TauCeti.Symbol.quantizeSobolev`). The order `m` of the symbol is thus the
number of derivatives `Op(a)` loses.

The same holds for finite-dimensional complex normed `V` and `W`, whose norms need not come from
inner products (`TauCeti.Symbol.exists_quantizeSobolev`): isomorphisms with `ℂ^k` and `ℂ^l`
induce isomorphisms of the Bessel-potential spaces (`BesselPotentialSpace.postcomp`) and
conjugate `a` to a symbol between Hilbert spaces (`TauCeti.Symbol.map`).

## The Fourier argument

For a fixed frequency `ξ`, the position slice `x ↦ a(x, ξ)` is smooth with support in a fixed
compact set, so its Fourier transform `â(η, ξ)` decays rapidly in `η`; the symbol estimates in
the position give, for every `N`,
`(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C_N ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`), where
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. Taking the Fourier transform of
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` in `x` gives the convolution-type formula
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`). Peetre's inequality
`⟨ξ⟩ ^ (s - m) ≤ 2 ^ (|s - m| / 2) ⟨ξ - ζ⟩ ^ |s - m| ⟨ζ⟩ ^ (s - m)` turns this into the bound
`⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(a) u) ξ‖ ≤ C ∫ k(ξ - ζ) ⟨ζ⟩ ^ s ‖𝓕 u ζ‖ dζ` with an integrable kernel
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)`, `N > n + |s - m|`, and Schur's test bounds the right side in
`L²`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`).
These steps use only the continuity of `a`, its compact spatial support and the decay of `â`; they
are proved for general coefficients in `TauCeti.Analysis.Pseudodifferential.FourierSchur`
(`TauCeti.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay`).
Since the `H^s` norm is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`, this is the estimate
`‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}` on Schwartz functions, and density of Schwartz functions in
`H^s` gives the bounded extension.

## Dependence on the symbol

The constants depend on `a` only through finitely many seminorms `p_{K,α,[]}(a)` of its position
derivatives on a compact set `K` outside which `a` vanishes; no frequency derivatives enter
(`TauCeti.Symbol.exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm`,
`TauCeti.Symbol.exists_norm_quantizeSobolev_le_sum_seminorm`). Since `Op(a)` is linear in `a`
(`TauCeti.Symbol.quantizeSobolev_add`, `TauCeti.Symbol.quantizeSobolev_smul`), a continuous family
of symbols vanishing outside a fixed compact set has quantizations that depend continuously on the
parameter in the operator norm of `H^s → H^{s - m}` (`TauCeti.Symbol.continuous_quantizeSobolev`).
This is the form in which the estimate is used for symbol homotopies and for parameter-dependent
families of operators.

## Main declarations

* `TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`,
  `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_le`: rapid decay of the
  Fourier transform in the position.
* Further facts about the Fourier transform `â(η, ξ)` of the position slices: linearity in `a`
  (`TauCeti.Symbol.HasCompactSpatialSupport.fourier_slice_add`,
  `TauCeti.Symbol.HasCompactSpatialSupport.fourier_slice_smul`), integrability in `η` and Fourier
  inversion (`TauCeti.Symbol.HasCompactSpatialSupport.integrable_fourier_slice`,
  `TauCeti.Symbol.HasCompactSpatialSupport.fourierInv_fourier_slice`), joint continuity
  (`TauCeti.Symbol.HasCompactSpatialSupport.continuous_fourier_slice`), differentiability in `ξ`
  with the Fourier transform of `∂_ξ a` as derivative
  (`TauCeti.Symbol.HasCompactSpatialSupport.hasFDerivAt_fourier_slice`,
  `TauCeti.Symbol.HasCompactSpatialSupport.coordinateDeriv_fourier_slice`), smoothness in `ξ`
  with the symbol estimates `‖D_ξ^k â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ (m - k) ⟨η⟩ ^ (-r)`
  (`TauCeti.Symbol.HasCompactSpatialSupport.contDiff_fourier_slice`,
  `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_le`), the
  same at the angular frequency `ξ = 2πζ`
  (`TauCeti.Symbol.HasCompactSpatialSupport.contDiff_fourier_slice_smul`,
  `TauCeti.Symbol.HasCompactSpatialSupport.norm_iteratedFDeriv_fourier_slice_smul_le`,
  `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_smul_le`),
  with constants given by a continuous seminorm of `a`, uniformly over the symbols vanishing
  outside a fixed compact set (`TauCeti.Symbol.exists_norm_fourier_slice_le_seminorm`,
  `TauCeti.Symbol.exists_norm_coordinateDeriv_fourier_slice_le_seminorm`,
  `TauCeti.Symbol.exists_norm_iteratedFDeriv_fourier_slice_le_seminorm`), and
  `(∂_{x_j} a)^(η, ξ) = 2πi ηⱼ â(η, ξ)`
  (`TauCeti.Symbol.HasCompactSpatialSupport.fourier_spatialDeriv_slice`).
* `TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`: the Fourier transform
  of `Op(a) u`, a case of
  `TauCeti.Symbol.HasCompactSpatialSupport.fourier_integral_fourierChar_smul_apply` for
  `x ↦ ∫ exp(2πi ⟪ζ, x⟫) a(x, g ζ) (𝓕 u ζ) dζ` with a general frequency map `g`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`:
  the Sobolev estimate on Schwartz functions, on the Fourier side.
* `TauCeti.Symbol.quantizeSobolev`: the bounded operator `H^s → H^{s - m}`, with
  `TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply` and
  `TauCeti.Symbol.HasCompactSpatialSupport.quantizeSobolev_toBesselPotentialSpaceCLM` identifying
  its values on Schwartz functions.
* `TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`: Sobolev
  extensions of quantizations are compatible with isomorphisms of the fibres.
* `TauCeti.Symbol.exists_quantizeSobolev`: the mapping property for finite-dimensional normed
  `V` and `W`.
* `TauCeti.Symbol.exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm`,
  `TauCeti.Symbol.exists_norm_fourier_slice_le_sum_seminorm` and
  `TauCeti.Symbol.exists_norm_quantizeSobolev_le_sum_seminorm`: the decay of `â` and the operator
  norm of `Op(a)` are bounded by finitely many seminorms of the position derivatives of `a`,
  uniformly over the symbols vanishing outside a fixed compact set.
* `TauCeti.Symbol.quantizeSobolev_add`, `TauCeti.Symbol.quantizeSobolev_smul`,
  `TauCeti.Symbol.quantizeSobolev_sub`, `TauCeti.Symbol.toDistr_quantizeSobolev_sub_apply`:
  linearity of `Op(a)` in the symbol.
* `TauCeti.Symbol.toDistr_apply_eq_toDistr_quantizeSobolev`: every bounded operator `H^s → H^r`
  agreeing with `Op(a)` on Schwartz functions gives the same tempered distributions as
  `Op(a) : H^s → H^{s - m}`.
* `TauCeti.Symbol.quantizeSobolev_inclusion`, `TauCeti.Symbol.quantizeSobolev_comp_inclusion`:
  compatibility with the inclusions of symbol classes and of Bessel-potential spaces, so that the
  tempered distribution `Op(a) u` depends neither on the order of the symbol nor on the space in
  which `u` is considered (`TauCeti.Symbol.toDistr_quantizeSobolev_congr`).
* `TauCeti.Symbol.quantizeSobolev_ofSpatial_smul`: the symbol `ψ(x)` quantizes to the
  multiplication by `ψ`.
* `TauCeti.Symbol.continuous_quantizeSobolev`: continuity in operator norm along continuous
  families of symbols vanishing outside a fixed compact set.
* `TauCeti.Symbol.toDistr_quantizeSobolev_congr`: the operators for different Sobolev orders `s`
  and different symbol orders `m` agree, as maps of tempered distributions, on symbols with the same
  coefficient.
* `TauCeti.Symbol.toDistr_quantizeSobolev_ofSpatial_smul_id`: for a Schwartz function `φ` such
  that the symbol `φ(x) id` has compact spatial support, for instance a compactly supported `φ`
  (`TauCeti.Symbol.hasCompactSpatialSupport_ofSpatial_smul_id`), this symbol quantizes to
  multiplication by `φ` (`BesselPotentialSpace.smulLeftCLM`).
* `TauCeti.Symbol.IsSmoothing.exists_continuousLinearMap_toDistr_quantizeSobolev_eq`: a smoothing
  symbol with compact spatial support quantizes, on every `H^t`, to a bounded operator
  `H^r → H^s` for arbitrary orders `r` and `s`.
* `TauCeti.Symbol.IsSmoothing.memSobolev_toDistr_quantizeSobolev`: such a symbol quantizes every
  element of `H^s` into `H^t` for all real `s` and `t`.
* `TauCeti.Symbol.memSobolev_toDistr_quantizeSobolev`: `Op(a)` sends a tempered distribution in
  `H^s` into `H^{s - m}`, whichever Bessel-potential space it is applied on.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution TopologicalSpace
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace RealInnerProductSpace ContDiff Topology
  LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Decay

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-! ### Rapid decay of the Fourier transform in the position -/

/-- The position slice `y ↦ a(y, ξ)` of a symbol with compact spatial support, as a Schwartz
function. -/
def HasCompactSpatialSupport.sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : 𝓢(CoordinateSpace n, V →L[ℂ] W) :=
  (ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)

@[simp]
theorem HasCompactSpatialSupport.coe_sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : ⇑(ha.sliceSchwartz ξ) = fun y ↦ a.coefficient (y, ξ) :=
  funext (HasCompactSupport.toSchwartzMap_toFun _ _)

/-- The Fourier transform of the Schwartz slice is the Fourier transform of the position slice. -/
theorem HasCompactSpatialSupport.fourier_sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ η : CoordinateSpace n) :
    𝓕 (ha.sliceSchwartz ξ) η = 𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  rw [SchwartzMap.fourier_coe, ha.coe_sliceSchwartz]

/-- The Fourier transform of the position slice is additive in the symbol. -/
theorem HasCompactSpatialSupport.fourier_slice_add {b : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) (ξ η : CoordinateSpace n) :
    𝓕 (fun y ↦ (a + b).coefficient (y, ξ)) η =
      𝓕 (fun y ↦ a.coefficient (y, ξ)) η + 𝓕 (fun y ↦ b.coefficient (y, ξ)) η := by
  have h : (ha.add hb).sliceSchwartz ξ = ha.sliceSchwartz ξ + hb.sliceSchwartz ξ := by
    ext y
    simp
  rw [← (ha.add hb).fourier_sliceSchwartz, h, FourierTransform.fourier_add, add_apply,
    ha.fourier_sliceSchwartz, hb.fourier_sliceSchwartz]

/-- The Fourier transform of the position slice is homogeneous in the symbol. -/
theorem HasCompactSpatialSupport.fourier_slice_smul (ha : a.HasCompactSpatialSupport) (c : ℂ)
    (ξ η : CoordinateSpace n) :
    𝓕 (fun y ↦ (c • a).coefficient (y, ξ)) η = c • 𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  have h : (ha.smul c).sliceSchwartz ξ = c • ha.sliceSchwartz ξ := by
    ext y
    simp
  rw [← (ha.smul c).fourier_sliceSchwartz, h, FourierTransform.fourier_smul,
    ← ha.fourier_sliceSchwartz]
  rfl

/-- The Fourier transform `η ↦ â(η, ξ)` of each position slice is integrable. -/
theorem HasCompactSpatialSupport.integrable_fourier_slice (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : Integrable (𝓕 fun y ↦ a.coefficient (y, ξ)) := by
  rw [← ha.coe_sliceSchwartz, ← SchwartzMap.fourier_coe]
  exact (𝓕 (ha.sliceSchwartz ξ)).integrable

/-- **Fourier inversion for the position slices**: `a(x, ξ) = ∫ exp(2πi ⟪η, x⟫) â(η, ξ) dη`. -/
theorem HasCompactSpatialSupport.fourierInv_fourier_slice [CompleteSpace W]
    (ha : a.HasCompactSpatialSupport) (ξ : CoordinateSpace n) :
    𝓕⁻ (𝓕 fun y ↦ a.coefficient (y, ξ)) = fun y ↦ a.coefficient (y, ξ) := by
  rw [← ha.coe_sliceSchwartz, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
    fourierInv_fourier_eq]

/-- The Schwartz seminorms of the position slices of a symbol vanishing outside a compact set `K`
grow at most like `⟨ξ⟩ ^ m`, with a constant given by the seminorms `p_{K,α,[]}(a)` of its
position derivatives. -/
private theorem HasCompactSpatialSupport.seminorm_slice_le (ha : a.HasCompactSpatialSupport)
    {K : Compacts (CoordinateSpace n)} (haK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) {R : ℝ}
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ) (ξ : CoordinateSpace n) :
    SchwartzMap.seminorm ℂ k l (ha.sliceSchwartz ξ) ≤
        R ^ k * (∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a) *
          (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  refine SchwartzMap.seminorm_le_bound ℂ k l _ (by positivity) fun x ↦ ?_
  rw [ha.coe_sliceSchwartz]
  by_cases hx : x ∈ K
  · have hD : ‖iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x‖ ≤
        ∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
      refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
        ((a.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)) x).trans
          (Finset.sum_le_sum fun r _ ↦ ?_)
      simpa [mixedDeriv_def, coordinateDeriv_nil] using le_seminorm K (List.ofFn r) [] a hx ξ
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x‖
        ≤ R ^ k * ∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a *
            (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hKR x hx) k) hD (norm_nonneg _)
            (pow_nonneg hR k)
      _ = _ := by rw [← Finset.sum_mul, mul_assoc]
  · -- Outside `K` the slice vanishes near `x`, so all its derivatives vanish at `x`.
    have hsupp : Function.support (fun y ↦ a.coefficient (y, ξ)) ⊆ K := fun y hy ↦
      by_contra fun h ↦ hy (haK y h ξ)
    have hzero : iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x = 0 :=
      Function.notMem_support.mp fun hmem ↦
        hx (closure_minimal hsupp K.isCompact.isClosed (support_iteratedFDeriv_subset l hmem))
    rw [hzero, norm_zero, mul_zero]
    positivity

/-- A sum of seminorms `p_{K,α,[]}` over the words `α` of a fixed length `l` is at most the sum
over any finite set of words containing all of them. -/
private theorem sum_seminorm_ofFn_le (K : Compacts (CoordinateSpace n)) (a : Symbol n V W m)
    {l : ℕ} {t : Finset (List (Fin n))} (ht : ∀ r : Fin l → Fin n, List.ofFn r ∈ t) :
    ∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a ≤
      ∑ α ∈ t, Symbol.seminorm K α [] a :=
  Finset.sum_le_sum_of_injOn List.ofFn List.ofFn_injective.injOn
    (fun α hα ↦ by obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hα; exact ht r)
    (fun _ _ ↦ le_rfl) fun _ _ _ ↦ apply_nonneg _ _

/-- **Rapid decay of the Fourier transform in the position, uniformly in the symbol.** For a
compact set `K` and every `N` there are finitely many words `α` and a constant `C` such that every
symbol `a` of order `m` vanishing at positions outside `K` satisfies
`(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C (∑_α p_{K,α,[]}(a)) ⟨ξ⟩ ^ m`, where `â(η, ξ)` is the Fourier
transform of the position slice `x ↦ a(x, ξ)` at `η`. Only position derivatives of `a` enter the
constant. -/
theorem exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm
    (K : Compacts (CoordinateSpace n)) (N : ℕ) :
    ∃ (t : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤
          C * (∑ α ∈ t, Symbol.seminorm K α [] a) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hKR : ∀ x ∈ K, ‖x‖ ≤ max R 0 := fun x hx ↦
    (mem_closedBall_zero_iff.mp (hR hx)).trans (le_max_left _ _)
  obtain ⟨s₀, c₀, hc₀, h₀⟩ :=
    SchwartzMap.exists_seminorm_fourier_le_sum_seminorm (E := CoordinateSpace n)
      (F := V →L[ℂ] W) 0
  obtain ⟨s₁, c₁, hc₁, h₁⟩ :=
    SchwartzMap.exists_seminorm_fourier_le_sum_seminorm (E := CoordinateSpace n)
      (F := V →L[ℂ] W) N
  set t := (s₀ ∪ s₁).biUnion fun i ↦ Finset.univ.image fun r : Fin i.2 → Fin n ↦ List.ofFn r
  set D := c₀ * ∑ i ∈ s₀, max R 0 ^ i.1 + c₁ * ∑ i ∈ s₁, max R 0 ^ i.1
  refine ⟨t, 2 ^ N * D, by positivity, fun a haK η ξ ↦ ?_⟩
  have ha : a.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
  set g := ha.sliceSchwartz ξ
  set P := ∑ α ∈ t, Symbol.seminorm K α [] a
  set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  -- Each seminorm of `g` occurring in `key` is bounded by `max R 0 ^ k * P * w`.
  have hs {k : ℕ} {s : Finset (ℕ × ℕ)} {c : ℝ} (hc : 0 ≤ c) (hss : s ⊆ s₀ ∪ s₁)
      (h : ∀ g : 𝓢(CoordinateSpace n, V →L[ℂ] W),
        SchwartzMap.seminorm ℂ k 0 (𝓕 g) ≤ c * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 g) :
      SchwartzMap.seminorm ℂ k 0 (𝓕 g) ≤ c * (∑ i ∈ s, max R 0 ^ i.1) * P * w := by
    refine (h g).trans ?_
    calc c * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 g
        ≤ c * ∑ i ∈ s, max R 0 ^ i.1 * P * w := by
          gcongr with i hi
          refine (ha.seminorm_slice_le haK (le_max_right R 0) hKR i.1 i.2 ξ).trans ?_
          gcongr
          exact sum_seminorm_ofFn_le K a fun r ↦ Finset.mem_biUnion.2
            ⟨i, hss hi, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
      _ = c * (∑ i ∈ s, max R 0 ^ i.1) * P * w := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have hF : 𝓕 (fun x ↦ a.coefficient (x, ξ)) η = 𝓕 g η :=
    (ha.fourier_sliceSchwartz ξ η).symm
  have e₀ : ‖𝓕 g η‖ ≤ c₀ * (∑ i ∈ s₀, max R 0 ^ i.1) * P * w :=
    (SchwartzMap.norm_le_seminorm ℂ _ η).trans (hs hc₀ Finset.subset_union_left h₀)
  have e₁ : ‖η‖ ^ N * ‖𝓕 g η‖ ≤ c₁ * (∑ i ∈ s₁, max R 0 ^ i.1) * P * w := by
    simpa using (SchwartzMap.le_seminorm ℂ N 0 (𝓕 g) η).trans
      (hs hc₁ Finset.subset_union_right h₁)
  have hpow : (1 + ‖η‖) ^ N ≤ 2 ^ N * (1 + ‖η‖ ^ N) := by
    refine (add_pow_le zero_le_one (norm_nonneg η) N).trans ?_
    rw [one_pow]
    gcongr
    · norm_num
    · exact Nat.sub_le N 1
  rw [hF]
  calc (1 + ‖η‖) ^ N * ‖𝓕 g η‖ ≤ 2 ^ N * (1 + ‖η‖ ^ N) * ‖𝓕 g η‖ := by gcongr
    _ = 2 ^ N * (‖𝓕 g η‖ + ‖η‖ ^ N * ‖𝓕 g η‖) := by ring
    _ ≤ 2 ^ N * (c₀ * (∑ i ∈ s₀, max R 0 ^ i.1) * P * w +
          c₁ * (∑ i ∈ s₁, max R 0 ^ i.1) * P * w) := by gcongr
    _ = 2 ^ N * D * P * w := by ring

/-- **Rapid decay of the Fourier transform in the position.** For a symbol `a` of order `m` with
compact spatial support and every `N`, the Fourier transform `â(η, ξ)` of the position slice
`x ↦ a(x, ξ)` satisfies `(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, uniformly in `η` and `ξ`. -/
theorem HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le
    (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨t, C, hC, h⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm (V := V) (W := W) (m := m) ⟨K, hK⟩ N
  exact ⟨C * ∑ α ∈ t, Symbol.seminorm ⟨K, hK⟩ α [] a,
    mul_nonneg hC (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _), h a hKa⟩

/-- **Rapid decay with seminorm constants.** For a compact set `K` and every `r` there are finitely
many words `α` and a constant `C` such that every symbol `a` of order `m` vanishing at positions
outside `K` satisfies `‖â(η, ξ)‖ ≤ C (∑_α p_{K,α,[]}(a)) ⟨ξ⟩ ^ m ⟨η⟩ ^ (-r)`. -/
theorem exists_norm_fourier_slice_le_sum_seminorm (K : Compacts (CoordinateSpace n)) (r : ℝ) :
    ∃ (t : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ ≤
          C * (∑ α ∈ t, Symbol.seminorm K α [] a) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
            (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨t, C, hC0, hC⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm (V := V) (W := W) (m := m) K ⌈r⌉₊
  refine ⟨t, C, hC0, fun a haK η ξ ↦ ?_⟩
  -- `⟨η⟩ ^ r ≤ (1 + ‖η‖) ^ ⌈r⌉₊`
  have hw : (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ ⌈r⌉₊ :=
    one_add_norm_sq_rpow_le_one_add_norm_pow_of_le η (Nat.le_ceil r)
  have hpos : 0 < (1 + ‖η‖ ^ 2) ^ (r / 2) := by positivity
  rw [show -r / 2 = -(r / 2) by ring, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  calc ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ * (1 + ‖η‖ ^ 2) ^ (r / 2)
      ≤ ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ * (1 + ‖η‖) ^ ⌈r⌉₊ := by gcongr
    _ ≤ C * (∑ α ∈ t, Symbol.seminorm K α [] a) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
      rw [mul_comm]; exact hC a haK η ξ

/-- **Rapid decay, uniformly in the symbol.** For a compact set `K` and every `r` there is a
continuous seminorm `q` on the symbols of order `m` such that every symbol `a` vanishing at
positions outside `K` satisfies `‖â(η, ξ)‖ ≤ q(a) ⟨ξ⟩ ^ m ⟨η⟩ ^ (-r)`. -/
theorem exists_norm_fourier_slice_le_seminorm (K : Compacts (CoordinateSpace n)) (r : ℝ) :
    ∃ q : Seminorm ℂ (Symbol n V W m), Continuous q ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ ≤
          q a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨t, C, hC0, hC⟩ := exists_norm_fourier_slice_le_sum_seminorm
    (V := V) (W := W) (m := m) K r
  refine ⟨C.toNNReal • ∑ α ∈ t, Symbol.seminorm K α [], ?_, fun a haK η ξ ↦ ?_⟩
  · have hcont : Continuous (∑ α ∈ t, Symbol.seminorm K α [] : Seminorm ℂ (Symbol n V W m)) :=
      Seminorm.continuous_finsetSum fun α _ ↦ by
        simpa using (withSeminorms (n := n) (V := V) (W := W) (m := m)).continuous_seminorm
          (K, α, [])
    simpa using hcont.const_smul C.toNNReal
  have hq : (C.toNNReal • ∑ α ∈ t, Symbol.seminorm K α [] : Seminorm ℂ (Symbol n V W m)) a =
      C * ∑ α ∈ t, Symbol.seminorm K α [] a := by
    simp [NNReal.smul_def, hC0]
  rw [hq]
  exact hC a haK η ξ

/-- **Rapid decay.** For every `r`, the Fourier transform of the position slice satisfies
`‖â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ m ⟨η⟩ ^ (-r)`. -/
theorem HasCompactSpatialSupport.exists_norm_fourier_slice_le (ha : a.HasCompactSpatialSupport)
    (r : ℝ) : ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨q, -, hq⟩ := exists_norm_fourier_slice_le_seminorm (V := V) (W := W) (m := m) ⟨K, hK⟩ r
  exact ⟨q a, apply_nonneg _ _, hq a hKa⟩

/-! ### Regularity of the Fourier transform in the position -/

/-- The Fourier transform `â(η, ξ)` of the position slice of a symbol with compact spatial support
is jointly continuous in `η` and `ξ`. -/
theorem HasCompactSpatialSupport.continuous_fourier_slice (ha : a.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, q.2)) q.1 := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  simpa only [Real.fourier_eq, Circle.smul_def] using
    continuous_integral_fourierChar_smul a.contDiff_coefficient.continuous hK hKa

/-- The Fourier transform in the position of the spatial derivative `∂_{x_j} a` is
`2πi ηⱼ â(η, ξ)`. -/
theorem HasCompactSpatialSupport.fourier_spatialDeriv_slice (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (η ξ : CoordinateSpace n) :
    𝓕 (fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ)) η =
      ((2 * π * Complex.I) * ⟪η, EuclideanSpace.single j (1 : ℝ)⟫) •
        𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  have hd : ⇑(∂_{EuclideanSpace.single j (1 : ℝ)} (ha.sliceSchwartz ξ) :
      𝓢(CoordinateSpace n, V →L[ℂ] W)) = fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ) := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply, (ha.sliceSchwartz ξ).differentiableAt.lineDeriv_eq_fderiv,
      ha.coe_sliceSchwartz, fderiv_coefficient_single]
  rw [← hd, ← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_apply,
    ha.fourier_sliceSchwartz]

/-- **Differentiation in the frequency.** The Fourier transform `â(η, ξ)` of the position slice
of a symbol with compact spatial support is differentiable in `ξ`, with the Fourier transform of
the frequency derivative as derivative. -/
theorem HasCompactSpatialSupport.hasFDerivAt_fourier_slice (ha : a.HasCompactSpatialSupport)
    (η ξ₀ : CoordinateSpace n) :
    HasFDerivAt (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η)
      (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ a.coefficient (y, ξ)) ξ₀) ξ₀ := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  simpa only [Real.fourier_eq, Circle.smul_def] using
    hasFDerivAt_integral_fourierChar_smul (ξ₀ := ξ₀) (a.contDiff_coefficient.of_le (by simp)) hK
      (.of_forall fun ξ y hy ↦ hKa y hy ξ) η

/-- The coordinate derivative `∂_{ξ_j} â(η, ξ)` is the Fourier transform of the position slice of
the frequency derivative `∂_{ξ_j} a`. -/
theorem HasCompactSpatialSupport.coordinateDeriv_fourier_slice (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (η ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ =
      𝓕 (fun y ↦ (Symbol.frequencyDeriv j a).coefficient (y, ξ)) η := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  rw [coordinateDeriv_cons, coordinateDeriv_nil, (ha.hasFDerivAt_fourier_slice η ξ).fderiv,
    integral_fourierChar_smul_fderiv_apply (ξ := ξ) (a.contDiff_coefficient.of_le (by simp)) hK
      (.of_forall fun ξ y hy ↦ hKa y hy ξ) η,
    Real.fourier_eq]
  simp only [Circle.smul_def, coefficient_frequencyDeriv, coordinateDeriv_cons,
    coordinateDeriv_nil]

/-- **Smoothness in the frequency.** The Fourier transform `â(η, ξ)` of the position slice of a
symbol with compact spatial support is smooth in the frequency `ξ`. -/
theorem HasCompactSpatialSupport.contDiff_fourier_slice (ha : a.HasCompactSpatialSupport)
    (η : CoordinateSpace n) :
    ContDiff ℝ ∞ fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    -- Elaborating the composition first, without the expected type, avoids unfolding `𝓕`.
    have hc := ha.continuous_fourier_slice.comp (Continuous.prodMk_right (X := CoordinateSpace n) η)
    exact hc
  | succ k ih =>
    -- The derivative is `v ↦ ∑ⱼ vⱼ (∂_{ξⱼ} a)^(η, ξ)`, built from the slices of the frequency
    -- derivatives, which are `C^k` by induction.
    set D : CoordinateSpace n → CoordinateSpace n →L[ℝ] (V →L[ℂ] W) := fun ξ ↦
      ∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (𝓕 (fun y ↦ (Symbol.frequencyDeriv j a).coefficient (y, ξ)) η)
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨D, ?_, fun ξ ↦ ?_⟩
    · exact ContDiff.sum fun j _ ↦
        contDiff_const.smulRight (ih (ha.frequencyDeriv j))
    · convert ha.hasFDerivAt_fourier_slice η ξ using 1
      refine ContinuousLinearMap.coe_injective
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun j ↦ ?_)
      have h := ha.coordinateDeriv_fourier_slice j η ξ
      rw [coordinateDeriv_cons, coordinateDeriv_nil,
        (ha.hasFDerivAt_fourier_slice η ξ).fderiv] at h
      simp [D, h, EuclideanSpace.proj, Finset.sum_apply]

/-- **Frequency derivatives of `â`, uniformly in the symbol.** For a compact set `K`, a word `w`
and every `r` there is a continuous seminorm `q` on the symbols of order `m` such that every symbol
`a` vanishing at positions outside `K` satisfies
`‖∂_ξ^w â(η, ξ)‖ ≤ q(a) ⟨ξ⟩ ^ (m - |w|) ⟨η⟩ ^ (-r)`. -/
theorem exists_norm_coordinateDeriv_fourier_slice_le_seminorm (K : Compacts (CoordinateSpace n))
    (w : List (Fin n)) (r : ℝ) :
    ∃ q : Seminorm ℂ (Symbol n V W m), Continuous q ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        ‖coordinateDeriv w (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ‖ ≤
          q a * (1 + ‖ξ‖ ^ 2) ^ ((m - w.length) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  induction w using List.reverseRecOn generalizing m with
  | nil => simpa using exists_norm_fourier_slice_le_seminorm (V := V) (W := W) (m := m) K r
  | append_singleton w j ih =>
    obtain ⟨q, hq, hqa⟩ := ih (m := m - 1)
    refine ⟨q.comp (frequencyDerivCLM j : Symbol n V W m →L[ℂ] Symbol n V W (m - 1)).toLinearMap,
      hq.comp (frequencyDerivCLM j).continuous, fun a haK η ξ ↦ ?_⟩
    have ha : a.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
    have hjK (x : CoordinateSpace n) (hx : x ∉ K) (ξ : CoordinateSpace n) :
        (Symbol.frequencyDeriv j a).coefficient (x, ξ) = 0 := by
      rw [coefficient_frequencyDeriv,
        show (fun η ↦ a.coefficient (x, η)) = 0 from funext (haK x hx), coordinateDeriv_zero,
        Pi.zero_apply]
    have hd : coordinateDeriv [j] (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) =
        fun ξ ↦ 𝓕 (fun y ↦ (Symbol.frequencyDeriv j a).coefficient (y, ξ)) η :=
      funext (ha.coordinateDeriv_fourier_slice j η)
    rw [coordinateDeriv_append, hd, Seminorm.comp_apply, ContinuousLinearMap.coe_coe,
      frequencyDerivCLM_apply]
    convert hqa _ hjK η ξ using 4
    rw [List.length_append, List.length_singleton]
    push_cast
    ring

/-- **Fréchet derivatives of `â` in the frequency, uniformly in the symbol.** For a compact set
`K` and every `k` and `r` there is a continuous seminorm `q` on the symbols of order `m` such that
every symbol `a` vanishing at positions outside `K` satisfies
`‖D_ξ^k â(η, ξ)‖ ≤ q(a) ⟨ξ⟩ ^ (m - k) ⟨η⟩ ^ (-r)`. -/
theorem exists_norm_iteratedFDeriv_fourier_slice_le_seminorm (K : Compacts (CoordinateSpace n))
    (k : ℕ) (r : ℝ) :
    ∃ q : Seminorm ℂ (Symbol n V W m), Continuous q ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        ‖iteratedFDeriv ℝ k (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ‖ ≤
          q a * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  choose q hq hqa using fun w : Fin k → Fin n ↦
    exists_norm_coordinateDeriv_fourier_slice_le_seminorm (V := V) (W := W) (m := m) K
      (List.ofFn w) r
  refine ⟨∑ w, q w, Seminorm.continuous_finsetSum fun w _ ↦ hq w, fun a haK η ξ ↦ ?_⟩
  have ha : a.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
    ((ha.contDiff_fourier_slice η).of_le (mod_cast le_top)) ξ).trans ?_
  rw [FunLike.coe_sum, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  simpa using hqa w a haK η ξ

/-- **Fréchet derivatives of `â` in the frequency.** For a symbol `a` of order `m` with compact
spatial support, `‖D_ξ^k â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ (m - k) ⟨η⟩ ^ (-r)`, for every `k` and `r`. -/
theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_le
    (ha : a.HasCompactSpatialSupport) (k : ℕ) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨q, -, hq⟩ :=
    exists_norm_iteratedFDeriv_fourier_slice_le_seminorm (V := V) (W := W) (m := m) ⟨K, hK⟩ k r
  exact ⟨q a, apply_nonneg _ _, hq a hKa⟩

/-- The rescaled position-Fourier slice `ζ ↦ â(η, 2πζ)` is smooth. -/
theorem HasCompactSpatialSupport.contDiff_fourier_slice_smul
    (ha : a.HasCompactSpatialSupport) (η : CoordinateSpace n) :
    ContDiff ℝ ∞ fun ζ : CoordinateSpace n ↦ 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η :=
  (ha.contDiff_fourier_slice η).comp (contDiff_const_smul _)

/-- The rescaled slice `ζ ↦ â(η, 2πζ)` inherits the derivative bounds of `ξ ↦ â(η, ξ)`: a bound
`B ⟨ξ⟩ ^ (m - j) ⟨η⟩ ^ (-r)` on the `j`-th derivative gives
`‖D^j‖ ≤ (2π) ^ j (2π) ^ |m - j| B ⟨ζ⟩ ^ (m - j) ⟨η⟩ ^ (-r)`. -/
theorem HasCompactSpatialSupport.norm_iteratedFDeriv_fourier_slice_smul_le
    (ha : a.HasCompactSpatialSupport) {j : ℕ} {r B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ η ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ j (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m - j) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2))
    (η ζ : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ j (fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η) ζ‖ ≤
      (2 * π) ^ j * (2 * π) ^ |m - j| * B * (1 + ‖ζ‖ ^ 2) ^ ((m - j) / 2) *
        (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have hw := one_add_norm_smul_sq_rpow_le h2π (m - j) ζ
  rw [iteratedFDeriv_comp_const_smul (2 * π)
    ((ha.contDiff_fourier_slice η).of_le (mod_cast le_top)), norm_smul, norm_pow,
    Real.norm_of_nonneg (by positivity)]
  calc (2 * π) ^ j * ‖iteratedFDeriv ℝ j (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η)
        ((2 * π) • ζ)‖
      ≤ (2 * π) ^ j * (B * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m - j) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2)) := by
        gcongr
        exact hB η _
    _ ≤ (2 * π) ^ j * (B * ((2 * π) ^ |m - j| * (1 + ‖ζ‖ ^ 2) ^ ((m - j) / 2)) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2)) := by gcongr
    _ = _ := by ring

/-- **Fréchet derivatives of the rescaled slice.** For a symbol `a` of order `m` with compact
spatial support, the slice `ζ ↦ â(η, 2πζ)` at the angular frequency `2πζ` has derivatives
`‖D^j â(η, 2πζ)‖ ≤ B ⟨ζ⟩ ^ (m - j) ⟨η⟩ ^ (-r)`, for every `j` and `r`. -/
theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_smul_le
    (ha : a.HasCompactSpatialSupport) (j : ℕ) (r : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ η ζ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ j (fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η) ζ‖ ≤
        B * (1 + ‖ζ‖ ^ 2) ^ ((m - j) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_iteratedFDeriv_fourier_slice_le j r
  exact ⟨(2 * π) ^ j * (2 * π) ^ |m - j| * C, by positivity,
    ha.norm_iteratedFDeriv_fourier_slice_smul_le hC0 hC⟩

end Decay

/-! ### The Fourier transform of the quantization -/

section Quantization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- **The Fourier transform of a quantization integral.** For a symbol `a` with compact spatial
support and a continuous frequency map `g` such that `⟨g ζ⟩ ^ m ‖𝓕 u ζ‖` is integrable, the Fourier
transform of `x ↦ ∫ exp(2πi ⟪ζ, x⟫) a(x, g ζ) (𝓕 u ζ) dζ` is `ξ ↦ ∫ â(ξ - ζ, g ζ) (𝓕 u ζ) dζ`,
where `â(η, ξ)` is the Fourier transform of the position slice `x ↦ a(x, ξ)` at `η`. For
`g ζ = 2πζ` this is the Fourier transform of the quantization
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`). -/
theorem HasCompactSpatialSupport.fourier_integral_fourierChar_smul_apply
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    {g : CoordinateSpace n → CoordinateSpace n} (hg : Continuous g)
    (hgu : Integrable fun ζ ↦ (1 + ‖g ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) (ξ : CoordinateSpace n) :
    𝓕 (fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • a.coefficient (x, g ζ) (𝓕 u ζ)) ξ =
      ∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, g ζ)) (ξ - ζ) (𝓕 u ζ) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient K hK
  exact TauCeti.fourier_integral_fourierChar_smul_apply a.contDiff_coefficient.continuous hK hC hKa
    u hg hgu ξ

/-- **The Fourier transform of the quantization.** For a symbol `a` with compact spatial support,
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`, where `â(η, ξ)` is the Fourier transform of the
position slice `x ↦ a(x, ξ)` at `η`. -/
theorem HasCompactSpatialSupport.fourier_quantizeSchwartzValue (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    𝓕 (quantizeSchwartzValue a.coefficient u) ξ =
      ∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient K hK
  exact TauCeti.fourier_quantizeSchwartzValue a.contDiff_coefficient.continuous hK hC hKa u ξ

/-- **The Sobolev estimate on Schwartz functions.** For a symbol `a` of order `m` with compact
spatial support and every real `s`, there is a constant `C` with
`‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)‖_{L²} ≤ C ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}` for every Schwartz function `u`, that
is, `‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}`. -/
theorem HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C', -, hC'⟩ := a.exists_bound_coefficient K hK
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le (⌈|s - m|⌉₊ + n + 1)
  obtain ⟨C, hC, h⟩ :=
    exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay (V := V) (W := W) n m s
  exact ⟨C * C₀, mul_nonneg hC hC₀,
    h a.coefficient K C' C₀ a.contDiff_coefficient.continuous hK hC' hKa hdecay⟩

/-- The symbol `φ(x) id` of multiplication by a compactly supported Schwartz function `φ` has
compact spatial support. -/
theorem hasCompactSpatialSupport_ofSpatial_smul_id {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : HasCompactSupport φ) :
    (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      ((φ.smooth ⊤).smul contDiff_const)).HasCompactSpatialSupport :=
  (hasCompactSpatialSupport_ofSpatial_iff _).2 (hφ.mono fun x hx h ↦ hx (by simp [h]))

end Quantization

/-! ### The bounded operator on Bessel-potential spaces -/

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- The quantization of a symbol with compact spatial support, as a linear map from Schwartz
functions to `L²`. -/
private def HasCompactSpatialSupport.quantizeLp (ha : a.HasCompactSpatialSupport) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] Lp W 2 (volume : Measure (CoordinateSpace n)) where
  toFun u := (ha.memLp_quantizeSchwartzValue u 2).toLp _
  map_add' u v := by
    obtain ⟨C, -, hC⟩ := isUniform_iff.mp ha.isUniform [] []
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
    exact quantizeSchwartzValue_add_right (a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (fun ξ ↦ by simpa using hC x ξ) u v
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ quantizeSchwartzValue_smul_right c u)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.quantizeLp_apply (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) :
    ha.quantizeLp u = (ha.memLp_quantizeSchwartzValue u 2).toLp _ :=
  (rfl)

omit [CompleteSpace V] in
/-- The weighted Fourier transform of the quantization is the tempered distribution of the
`L²` function `⟨ξ⟩ ^ r 𝓕 (Op(a) u)`, whenever the latter lies in `L²`. -/
private theorem HasCompactSpatialSupport.smulLeftCLM_fourier_quantizeLp
    (ha : a.HasCompactSpatialSupport) (r : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (hG : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2) :
    smulLeftCLM W (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
        (𝓕 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W))) =
      (hG.toLp _ : 𝓢'(CoordinateSpace n, W)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, ha.quantizeLp_apply,
    Lp.fourier_toTemperedDistribution_apply _ (ha.integrable_quantizeSchwartzValue u)
      (MemLp.coeFn_toLp _),
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ((hG.coeFn_toLp).mono fun ξ hξ ↦ ?_)
  dsimp only
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_eq_mul, mul_comm, mul_smul]

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.memLp_smul_fourier_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 := by
  obtain ⟨C, -, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  exact (hC u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2))

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.memSobolev_quantizeLp (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemSobolev (s - m) 2 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨_, ha.smulLeftCLM_fourier_quantizeLp (s - m) u
    (ha.memLp_smul_fourier_quantizeSchwartzValue s u)⟩

omit [CompleteSpace V] in
/-- The quantization of a symbol of order `m` with compact spatial support, as a linear map from
Schwartz functions to `H^{s - m}`. -/
private def HasCompactSpatialSupport.quantizeBessel (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] H^{s - m}(CoordinateSpace n, W) where
  toFun u := (ha.memSobolev_quantizeLp s u).toBesselPotentialSpace
  map_add' u v := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_add,
      map_add]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_add _ _)
  map_smul' c u := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_smul,
      map_smul, RingHom.id_apply]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_smul _ _)

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.toDistr_quantizeBessel (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    (ha.quantizeBessel s u).toDistr = (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- On Schwartz functions the quantization is bounded from `H^s` to `H^{s - m}`, with any
constant of the Sobolev estimate on the Fourier side. -/
private theorem HasCompactSpatialSupport.norm_quantizeBessel_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    ‖ha.quantizeBessel s u‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  have hG := ha.memLp_smul_fourier_quantizeSchwartzValue s u
  rw [BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq
      ((ha.toDistr_quantizeBessel s u).symm ▸ ha.smulLeftCLM_fourier_quantizeLp (s - m) u hG),
    Lp.norm_toLp, SchwartzMap.norm_toBesselPotentialSpaceCLM, ← ENNReal.toReal_ofReal hC0,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2).eLpNorm_ne_top) (hC u)

private theorem HasCompactSpatialSupport.exists_norm_quantizeBessel_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖ha.quantizeBessel s u‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  exact ⟨C, ha.norm_quantizeBessel_le s hC0 hC⟩

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** The left
quantization `Op(a)` of a symbol `a` of order `m` with compact spatial support extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Bessel-potential
spaces, for every real `s`. On a Schwartz function `u` it is the tempered distribution of the
function `Op(a) u` (`TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply`), and
it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). -/
def quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  (ha.quantizeBessel s).extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

/-- On a Schwartz function `u`, the operator `Op(a) : H^s → H^{s - m}` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`. -/
@[simp]
theorem toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨C, hC⟩ := ha.exists_norm_quantizeBessel_le s
  have h := LinearMap.extendOfNorm_eq (f := ha.quantizeBessel s)
    (e := (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap)
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM s ENNReal.ofNat_ne_top) ⟨C, hC⟩ u
  rw [ContinuousLinearMap.coe_coe] at h
  rw [quantizeSobolev, h, ha.toDistr_quantizeBessel, ha.quantizeLp_apply,
    Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((ha.memLp_quantizeSchwartzValue u 2).coeFn_toLp.mono fun x hx ↦ by
    simp only [hx])

/-- On a Schwartz function `u`, the operator `Op(a) : H^s → H^{s - m}` gives the element of
`H^{s - m}` defined by the Schwartz function `Op(a) u`, which has compact support. -/
theorem HasCompactSpatialSupport.quantizeSobolev_toBesselPotentialSpaceCLM
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
        ((ha.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (a.contDiff_quantizeSchwartzValue u)) := by
  refine BesselPotentialSpace.ext ?_
  ext φ
  simp

/-- The operator norm of `Op(a) : H^s → H^{s - m}` is at most any constant of the Sobolev
estimate on the Fourier side. -/
private theorem norm_quantizeSobolev_le_of_eLpNorm_le (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume) :
    ‖a.quantizeSobolev ha s‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC0
    (ha.norm_quantizeBessel_le s hC0 hC)

/-- **The operator norm is controlled by finitely many symbol seminorms.** For a compact set `K`
and a real `s` there are finitely many words `α` and a constant `C` such that every symbol `a` of
order `m` vanishing at positions outside `K` satisfies
`‖Op(a)‖_{H^s → H^{s - m}} ≤ C ∑_α p_{K,α,[]}(a)`. Only position derivatives of `a` enter. -/
theorem exists_norm_quantizeSobolev_le_sum_seminorm (K : Compacts (CoordinateSpace n)) (s : ℝ) :
    ∃ (t : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          ‖a.quantizeSobolev ha s‖ ≤ C * ∑ α ∈ t, Symbol.seminorm K α [] a := by
  obtain ⟨t, C, hC, h⟩ := exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm
    (V := V) (W := W) (m := m) K (⌈|s - m|⌉₊ + n + 1)
  obtain ⟨D, hD, hE⟩ :=
    exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay (V := V) (W := W) n m s
  refine ⟨t, D * C, mul_nonneg hD hC, fun a ha haK ↦ ?_⟩
  have hP : 0 ≤ ∑ α ∈ t, Symbol.seminorm K α [] a := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  obtain ⟨C', -, hC'⟩ := a.exists_bound_coefficient K K.isCompact
  rw [mul_assoc]
  exact norm_quantizeSobolev_le_of_eLpNorm_le ha s (mul_nonneg hD (mul_nonneg hC hP))
    (hE a.coefficient K C' _ a.contDiff_coefficient.continuous K.isCompact hC' haK (h a haK))

/-- The operator `Op(a)` does not depend on the proof that `a` has compact spatial support, and
equal symbols give equal operators. -/
private theorem quantizeSobolev_congr {b : Symbol n V W m} (hab : a = b)
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) (s : ℝ) :
    a.quantizeSobolev ha s = b.quantizeSobolev hb s := by
  subst hab
  rfl

/-- The operator `Op(a) : H^s → H^{s - m}` is additive in the symbol. -/
theorem quantizeSobolev_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a + b).HasCompactSpatialSupport) (s : ℝ) :
    (a + b).quantizeSobolev hab s = a.quantizeSobolev ha s + b.quantizeSobolev hb s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ
  have hia : Integrable fun x ↦ φ x • quantizeSchwartzValue a.coefficient u x :=
    (ha.integrable_quantizeSchwartzValue u).smul_of_top_right (φ.memLp ⊤)
  have hib : Integrable fun x ↦ φ x • quantizeSchwartzValue b.coefficient u x :=
    (hb.integrable_quantizeSchwartzValue u).smul_of_top_right (φ.memLp ⊤)
  simp only [add_apply, BesselPotentialSpace.toDistr_add,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  rw [← integral_add hia hib]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [coefficient_add, quantizeSchwartzValue_coefficient_add, smul_add]

/-- The operator `Op(a) : H^s → H^{s - m}` is homogeneous in the symbol. -/
theorem quantizeSobolev_smul (ha : a.HasCompactSpatialSupport) (c : ℂ)
    (hca : (c • a).HasCompactSpatialSupport) (s : ℝ) :
    (c • a).quantizeSobolev hca s = c • a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ
  simp only [smul_apply, BesselPotentialSpace.toDistr_smul,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply, coefficient_smul,
    quantizeSchwartzValue_smul_left, smul_comm (φ _) c]
  exact integral_smul c _

/-- The zero symbol quantizes to the zero operator `H^s → H^{s - m}`. -/
@[simp]
theorem quantizeSobolev_zero (h : (0 : Symbol n V W m).HasCompactSpatialSupport) (s : ℝ) :
    (0 : Symbol n V W m).quantizeSobolev h s = 0 := by
  have h₀ := quantizeSobolev_add h h (by rwa [add_zero]) s
  rwa [quantizeSobolev_congr (add_zero 0) _ h s, left_eq_add] at h₀

/-- The operator `Op(a) : H^s → H^{s - m}` takes the negated symbol to the negated operator. -/
theorem quantizeSobolev_neg (ha : a.HasCompactSpatialSupport)
    (hna : (-a).HasCompactSpatialSupport) (s : ℝ) :
    (-a).quantizeSobolev hna s = -a.quantizeSobolev ha s := by
  rw [quantizeSobolev_congr (neg_one_smul ℂ a).symm hna (ha.smul (-1)) s,
    quantizeSobolev_smul ha, neg_one_smul]

/-- The operator `Op(a) : H^s → H^{s - m}` is additive in the symbol, so it takes differences of
symbols to differences of operators. -/
theorem quantizeSobolev_sub {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a - b).HasCompactSpatialSupport) (s : ℝ) :
    (a - b).quantizeSobolev hab s = a.quantizeSobolev ha s - b.quantizeSobolev hb s := by
  rw [eq_sub_iff_add_eq, ← quantizeSobolev_add hab hb (by rwa [sub_add_cancel]) s]
  exact quantizeSobolev_congr (sub_add_cancel a b) _ _ s

/-- The tempered distribution of `Op(a - b) u` is the difference of those of `Op(a) u` and
`Op(b) u`. -/
theorem toDistr_quantizeSobolev_sub_apply {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a - b).HasCompactSpatialSupport) (s : ℝ)
    (u : H^{s}(CoordinateSpace n, V)) :
    ((a - b).quantizeSobolev hab s u).toDistr =
      (a.quantizeSobolev ha s u).toDistr - (b.quantizeSobolev hb s u).toDistr := by
  rw [quantizeSobolev_sub ha hb hab, _root_.sub_apply,
    BesselPotentialSpace.toDistr_sub]

/-- **Continuity in the symbol.** If `t ↦ a t` is a continuous family of symbols of order `m`
that all vanish at positions outside a fixed compact set `K`, then `t ↦ Op(a t)` is continuous
into the bounded operators `H^s → H^{s - m}` with the operator norm. -/
theorem continuous_quantizeSobolev {X : Type*} [TopologicalSpace X] {a : X → Symbol n V W m}
    (hcont : Continuous a) {K : Compacts (CoordinateSpace n)}
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (s : ℝ) :
    Continuous fun t ↦
      (a t).quantizeSobolev (hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩) s := by
  obtain ⟨u, C, -, hbound⟩ :=
    exists_norm_quantizeSobolev_le_sum_seminorm (V := V) (W := W) (m := m) K s
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  have hK (t : X) : (a t).HasCompactSpatialSupport :=
    hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_)
    (g := fun t ↦ C * ∑ α ∈ u, Symbol.seminorm K α [] (a t - a t₀)) ?_
  · rw [← quantizeSobolev_sub (hK t) (hK t₀) ((hK t).sub (hK t₀))]
    exact hbound _ _ fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]
  · have h : Filter.Tendsto (fun t ↦ ∑ α ∈ u, Symbol.seminorm K α [] (a t - a t₀))
        (𝓝 t₀) (𝓝 0) := by
      simpa using tendsto_finsetSum u fun α _ ↦
        ((withSeminorms.continuous_seminorm (K, α, [])).comp
          (hcont.sub continuous_const)).tendsto' t₀ 0 (by simp)
    simpa using h.const_mul C

/-- **Extensions of a quantization agree as distributions.** If a bounded operator
`T : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` agrees on Schwartz functions with the quantization of a symbol `a`
with compact spatial support, then `T u` and `Op(a) u ∈ H^{s - m}` are the same tempered
distribution for every `u ∈ H^s`, whatever the target order `r`. -/
theorem toDistr_apply_eq_toDistr_quantizeSobolev (ha : a.HasCompactSpatialSupport) {s r : ℝ}
    {T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W)}
    (hT : ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue a.coefficient u x)
    (u : H^{s}(CoordinateSpace n, V)) :
    (T u).toDistr = (a.quantizeSobolev ha s u).toDistr := by
  -- Both operators, followed by the inclusions into `H^{min r (s - m)}`, agree on Schwartz
  -- functions, which are dense in `H^s`.
  have h : BesselPotentialSpace.inclusion (min_le_left r (s - m)) ∘L T =
      BesselPotentialSpace.inclusion (min_le_right r (s - m)) ∘L a.quantizeSobolev ha s :=
    BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun v ↦
      BesselPotentialSpace.ext <| by
        ext φ
        simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion, hT,
          toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  simpa only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion] using
    congrArg BesselPotentialSpace.toDistr (DFunLike.congr_fun h u)

/-- **Compatibility of the Sobolev extensions.** The operator `Op(a) : H^s → H^{s - m}` only
depends on the coefficient of `a` and on the tempered distribution of its argument: symbols `a`
and `b` of orders `m` and `m'` with the same coefficient give the same tempered distribution on
`u ∈ H^s` and `v ∈ H^t` whenever `u` and `v` have the same tempered distribution. -/
theorem toDistr_quantizeSobolev_congr {m' : ℝ} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) {s t : ℝ} {u : H^{s}(CoordinateSpace n, V)}
    {v : H^{t}(CoordinateSpace n, V)} (huv : u.toDistr = v.toDistr) :
    (a.quantizeSobolev ha s u).toDistr = (b.quantizeSobolev hb t v).toDistr := by
  refine SchwartzMap.toDistr_apply_congr_of_comp_eq ENNReal.ofNat_ne_top
    (A := quantizeUniformCLM a ha.isUniform) ?_ ?_ huv
  · refine ContinuousLinearMap.ext fun u ↦ BesselPotentialSpace.ext ?_
    ext φ
    simp
  · refine ContinuousLinearMap.ext fun u ↦ BesselPotentialSpace.ext ?_
    ext φ
    simp [hab]

/-- **Multiplication operators.** For a Schwartz function `φ` such that the symbol `φ(x) id` of
order `0` has compact spatial support, for instance a compactly supported `φ`
(`TauCeti.Symbol.hasCompactSpatialSupport_ofSpatial_smul_id`), this symbol quantizes to
multiplication by `φ` on `H^s`. -/
theorem toDistr_quantizeSobolev_ofSpatial_smul_id (φ : 𝓢(CoordinateSpace n, ℂ))
    (h : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      ((φ.smooth ⊤).smul contDiff_const)).HasCompactSpatialSupport)
    (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((ofSpatial _ _).quantizeSobolev h s u).toDistr =
      (BesselPotentialSpace.smulLeftCLM s φ u).toDistr := by
  have key : (ofSpatial _ _).quantizeSobolev h s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L BesselPotentialSpace.smulLeftCLM s φ := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦
      BesselPotentialSpace.ext ?_
    ext ψ
    simp only [toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
      quantizeSchwartzValue_ofSpatial, _root_.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
      BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      smulLeftCLM_apply_apply, SchwartzMap.coe_apply,
      SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, smul_eq_mul, mul_smul]
    exact integral_congr_ae (.of_forall fun x ↦ smul_comm _ _ _)
  rw [key, ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]

/-- **Smoothing operators gain every number of derivatives.** A smoothing symbol `a` with
compact spatial support quantizes to a bounded operator `T : H^r → H^s` for arbitrary real orders
`r` and `s`: for every `v ∈ H^t` and `u ∈ H^r` with the same tempered distribution, `Op(a) v` and
`T u` have the same tempered distribution. -/
theorem IsSmoothing.exists_continuousLinearMap_toDistr_quantizeSobolev_eq (hsm : a.IsSmoothing)
    (ha : a.HasCompactSpatialSupport) (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr → (a.quantizeSobolev ha t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.mp hsm (r - s)
  have hbK := ha.of_coefficient_eq hb
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L b.quantizeSobolev hbK r,
    fun huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact toDistr_quantizeSobolev_congr hb.symm ha hbK huv

/-- **Changing the order of the symbol.** Viewing a symbol of order `m` as a symbol of order
`m' ≥ m` gives the operator `H^s → H^{s - m}` followed by the inclusion `H^{s - m} ⊆ H^{s - m'}`. -/
theorem quantizeSobolev_inclusion {m' : ℝ} (h : m ≤ m') (ha : a.HasCompactSpatialSupport)
    (ha' : (inclusion h a).HasCompactSpatialSupport) (s : ℝ) :
    (inclusion h a).quantizeSobolev ha' s =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ
  simp [coefficient_inclusion]

/-- **Changing the Sobolev order.** The operators `Op(a) : H^s → H^{s - m}` for the different
orders `s` are compatible with the inclusions `H^s ⊆ H^r`. -/
theorem quantizeSobolev_comp_inclusion (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r ≤ s) :
    a.quantizeSobolev ha r ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ
  simp

/-- **Multiplication operators.** The symbol `ψ(x)` of multiplication by a compactly supported
Schwartz function `ψ` quantizes to the multiplication operator `u ↦ ψ u` on `H^s`. -/
theorem quantizeSobolev_ofSpatial_smul {ψ : 𝓢(CoordinateSpace n, ℂ)} (hψ : ContDiff ℝ ∞
      fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
    (h : (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) hψ).HasCompactSpatialSupport)
    (s : ℝ) :
    (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) hψ).quantizeSobolev h s =
      BesselPotentialSpace.inclusion (by simp) ∘L BesselPotentialSpace.smulLeftCLM s ψ := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ
  simp only [toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    quantizeSchwartzValue_ofSpatial, _root_.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
    BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    smulLeftCLM_toTemperedDistributionCLM_eq, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]

/-- **Smoothing operators gain every order of regularity.** For a smoothing symbol `a` with compact
spatial support, the quantization `Op(a) u` of any `u ∈ H^s` lies in `H^t` for every real `t`. -/
theorem IsSmoothing.memSobolev_toDistr_quantizeSobolev (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) (s t : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    MemSobolev t 2 (a.quantizeSobolev hc s u).toDistr := by
  -- A symbol of order `s - t` with the same coefficient maps `H^s` into `H^t`.
  obtain ⟨b, hb⟩ := isSmoothing_iff.mp ha (s - t)
  have hbc := hc.of_coefficient_eq hb
  rw [toDistr_quantizeSobolev_congr hb.symm hc hbc (v := u) rfl]
  simpa only [sub_sub_cancel] using (b.quantizeSobolev hbc s u).memSobolev_toDistr

/-- **A symbol of order `m` costs `m` derivatives at every Sobolev order.** If `u ∈ H^t` has a
tempered distribution lying in `H^s`, then `Op(a) u ∈ H^{s - m}`, whatever the order `t` at which
`Op(a)` is applied. -/
theorem memSobolev_toDistr_quantizeSobolev (ha : a.HasCompactSpatialSupport) {s t : ℝ}
    {u : H^{t}(CoordinateSpace n, V)} (hu : MemSobolev s 2 u.toDistr) :
    MemSobolev (s - m) 2 (a.quantizeSobolev ha t u).toDistr := by
  rw [toDistr_quantizeSobolev_congr rfl ha ha hu.toBesselPotentialSpace_toDistr.symm]
  exact (a.quantizeSobolev ha s _).memSobolev_toDistr

end Sobolev

section Transport

variable {V W V' W' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup V']
  [NormedSpace ℂ V'] [CompleteSpace V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
  [CompleteSpace W']

/-- **Change of fibres for Sobolev extensions of quantizations.** Let `e₁ : V ≃L[ℂ] V'` and
`e₂ : W ≃L[ℂ] W'`, and let `T : H^s(ℝⁿ; V') → H^r(ℝⁿ; W')` agree on Schwartz functions with the
quantization of the conjugated symbol `e₂ a e₁⁻¹`. Then `e₂⁻¹ ∘ T ∘ e₁ : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)`
agrees on Schwartz functions with the quantization of `a`
(`TauCeti.quantizeSchwartzValue_arrowCongr`). -/
theorem toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply
    (a : Symbol n V W m) (e₁ : V ≃L[ℂ] V') (e₂ : W ≃L[ℂ] W') {r s : ℝ}
    {T : H^{s}(CoordinateSpace n, V') →L[ℂ] H^{r}(CoordinateSpace n, W')}
    (hT : ∀ (u : 𝓢(CoordinateSpace n, V')) (φ : 𝓢(CoordinateSpace n, ℂ)),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue
          (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient u x)
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    ((BesselPotentialSpace.postcomp _ r 2 (e₂.symm : W' →L[ℂ] W) ∘L T ∘L
        BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] V'))
        (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  have hq (x : CoordinateSpace n) :
      quantizeSchwartzValue
          (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient
          (u.postcompCLM (e₁ : V →L[ℂ] V')) x =
        e₂ (quantizeSchwartzValue a.coefficient u x) := by
    rw [coefficient_map_arrowCongr, quantizeSchwartzValue_arrowCongr]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    BesselPotentialSpace.toDistr_postcomp_apply, hT]
  simp only [hq, ← map_smul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

end Transport

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** For a
symbol `a` of order `m` with compact spatial support between finite-dimensional complex normed
spaces and every real `s`, the quantization `Op(a)` extends from Schwartz functions to a bounded
operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.

The norms of `V` and `W` need not come from inner products: isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` induce isomorphisms of the Bessel-potential spaces
(`BesselPotentialSpace.postcomp`), and the operator is `e₂⁻¹ ∘ Op(e₂ a e₁⁻¹) ∘ e₁` with the
Hilbert-space operator `TauCeti.Symbol.quantizeSobolev`
(`TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`). -/
theorem exists_quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂
    (toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply (ha.map _) s)⟩

end FiniteDimensional

end Symbol

end TauCeti
