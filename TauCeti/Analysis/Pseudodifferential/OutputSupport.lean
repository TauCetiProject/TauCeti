/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Support
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport

/-!
# The quantization determines the symbol, and output support

The Kohn–Nirenberg quantization `Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` of
`TauCeti.quantizeSchwartzValue` determines the full coefficient `a`, already from its values on
compactly supported smooth inputs: at each position `x`, if `ξ ↦ a(x, ξ)` is continuous and of
polynomial growth, the functional `u ↦ Op(a) u (x)` vanishes on compactly supported Schwartz
functions only when `a(x, ξ) = 0` for every `ξ`. Thus full quantization is injective, with no
quotient by smoothing operators.

The proof uses the density of compactly supported functions in Schwartz space and the continuity
of `u ↦ Op(a) u (x)` to pass to all Schwartz inputs. Since the Fourier transform is a bijection of
Schwartz space, the continuous function `ζ ↦ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) v` then integrates to zero
against every compactly supported smooth function, so it vanishes.

The main consequence concerns supports. For a closed set `K` of positions, the quantization
has output support in `K`, meaning that `Op(a) u` is supported in `K` for every compactly
supported smooth `u`, exactly when the coefficient vanishes at every position outside `K`
(`TauCeti.tsupport_quantizeSchwartzValue_subset_iff`). This is a statement about the position
support of the full symbol. It differs from compact support in the input variable, and from
proper support of the kernel: the identity, whose symbol is `1`, preserves the support of every
input but has output support in no closed proper subset
(`TauCeti.exists_not_tsupport_quantizeSchwartzValue_id_subset`).

## Main results

* `TauCeti.eq_of_forall_quantizeSchwartzValue_eq`: two coefficients with equal quantizations at
  `x` on compactly supported inputs agree at `x`.
* `TauCeti.tsupport_quantizeSchwartzValue_subset_iff`: output support in a closed set `K` is
  equivalent to vanishing of the coefficient outside `K`.
* `TauCeti.Symbol.quantizeSchwartzValue_injective` and
  `TauCeti.Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq`: a symbol is determined by
  its quantization, even across different orders.
* `TauCeti.Symbol.hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset`: a
  symbol has compact spatial support exactly when its quantization has output support in a
  compact set.

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  §2.8, (2.75)–(2.77): the full symbol is recovered from the operator.
* R. Melrose, *Introduction to Microlocal Analysis*, §1.7, Corollary 1.1: injectivity of the
  Fourier transform on tempered distributions.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory Real FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

section Pointwise

variable {a b : E × E → V →L[ℂ] W} {x : E}

/-- **The quantization determines the coefficient.** At a position `x`, let `ξ ↦ a(x, ξ)` and
`ξ ↦ b(x, ξ)` be continuous with polynomial growth. If `Op(a) u (x) = Op(b) u (x)` for every
compactly supported Schwartz function `u`, then `a(x, ξ) = b(x, ξ)` for every frequency `ξ`. -/
theorem eq_of_forall_quantizeSchwartzValue_eq (ha : Continuous fun ξ ↦ a (x, ξ))
    (hb : Continuous fun ξ ↦ b (x, ξ)) {C m C' m' : ℝ}
    (hCa : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hCb : ∀ ξ, ‖b (x, ξ)‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (h : ∀ u : 𝓢(E, V), HasCompactSupport u →
      quantizeSchwartzValue a u x = quantizeSchwartzValue b u x) (ξ : E) :
    a (x, ξ) = b (x, ξ) := by
  -- By density and continuity, the two quantizations agree at `x` on all Schwartz functions.
  have hall : ∀ u : 𝓢(E, V), quantizeSchwartzValue a u x = quantizeSchwartzValue b u x :=
    congrFun <| (continuous_quantizeSchwartzValue_input ha hCa).ext_on
      SchwartzMap.dense_hasCompactSupport (continuous_quantizeSchwartzValue_input hb hCb)
      fun u hu ↦ h u hu
  -- Since `𝓕` is onto Schwartz space, the Fourier-side integrands agree against every `f`.
  have hzero : ∀ f : 𝓢(E, V),
      ∫ ζ, ((𝐞 ⟪ζ, x⟫ : ℂ) • (a (x, (2 * π) • ζ) - b (x, (2 * π) • ζ))) (f ζ) = 0 := by
    intro f
    have hf := hall (𝓕⁻ f)
    have hia := integrable_quantizeSchwartzValue_integrand ha.aestronglyMeasurable hCa f
    have hib := integrable_quantizeSchwartzValue_integrand hb.aestronglyMeasurable hCb f
    rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, fourier_fourierInv_eq] at hf
    simp only [Circle.smul_def] at hf hia hib
    simp only [smul_apply, sub_apply, smul_sub]
    rw [integral_sub hia hib, hf, sub_self]
  have hcont : Continuous fun ζ : E ↦
      (𝐞 ⟪ζ, x⟫ : ℂ) • (a (x, (2 * π) • ζ) - b (x, (2 * π) • ζ)) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))).smul
      ((ha.comp (continuous_const_smul _)).sub (hb.comp (continuous_const_smul _)))
  have hξ := eq_zero_of_forall_integral_apply_eq_zero hcont hzero ((2 * π)⁻¹ • ξ)
  rwa [smul_inv_smul₀ two_pi_pos.ne', smul_eq_zero, or_iff_right (Circle.coe_ne_zero _),
    sub_eq_zero] at hξ

/-- At a position `x` where `ξ ↦ a(x, ξ)` is continuous with polynomial growth, if
`Op(a) u (x) = 0` for every compactly supported Schwartz function `u`, then `a(x, ξ) = 0` for
every frequency `ξ`. -/
theorem eq_zero_of_forall_quantizeSchwartzValue_eq_zero (ha : Continuous fun ξ ↦ a (x, ξ))
    {C m : ℝ} (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (h : ∀ u : 𝓢(E, V), HasCompactSupport u → quantizeSchwartzValue a u x = 0) (ξ : E) :
    a (x, ξ) = 0 :=
  eq_of_forall_quantizeSchwartzValue_eq (b := 0) ha continuous_const hC (C' := 0) (m' := 0)
    (fun _ ↦ by simp) (fun u hu ↦ by rw [h u hu, quantizeSchwartzValue_zero_left]) ξ

end Pointwise

section Support

variable {a : E × E → V →L[ℂ] W}

/-- **Output support.** Let `K` be a closed set of positions, and let every frequency slice
`ξ ↦ a(x, ξ)` with `x ∉ K` be continuous with polynomial growth. Then `Op(a) u` is supported in
`K` for every compactly supported Schwartz function `u` if and only if `a(x, ξ) = 0` for every
`x ∉ K` and every frequency `ξ`. -/
theorem tsupport_quantizeSchwartzValue_subset_iff {K : Set E} (hK : IsClosed K)
    (ha : ∀ x ∉ K, Continuous fun ξ ↦ a (x, ξ))
    (hC : ∀ x ∉ K, ∃ C m : ℝ, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    (∀ u : 𝓢(E, V), HasCompactSupport u → tsupport (quantizeSchwartzValue a u) ⊆ K) ↔
      ∀ x ∉ K, ∀ ξ, a (x, ξ) = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h u _ ↦ closure_minimal ?_ hK⟩
  · obtain ⟨C, m, hCx⟩ := hC x hx
    exact eq_zero_of_forall_quantizeSchwartzValue_eq_zero (ha x hx) hCx fun u hu ↦
      image_eq_zero_of_notMem_tsupport fun hxu ↦ hx (h u hu hxu)
  · refine Function.support_subset_iff'.2 fun x hx ↦ ?_
    rw [quantizeSchwartzValue_congr_left (b := 0) (h x hx), quantizeSchwartzValue_zero_left]

/-- The identity, the quantization of the constant symbol `1`, has output support in no closed
proper subset `K`, although it preserves the support of every input. -/
theorem exists_not_tsupport_quantizeSchwartzValue_id_subset [Nontrivial V] {K : Set E}
    (hK : IsClosed K) (hKne : K ≠ Set.univ) :
    ∃ u : 𝓢(E, V), HasCompactSupport u ∧
      ¬tsupport (quantizeSchwartzValue (fun _ ↦ ContinuousLinearMap.id ℂ V) u) ⊆ K := by
  by_contra! h
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem K).1 hKne
  have hid := (tsupport_quantizeSchwartzValue_subset_iff hK (fun _ _ ↦ continuous_const)
    (fun _ _ ↦ ⟨1, 0, fun _ ↦ by simp⟩)).1 h x hx 0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (by simpa using congr($hid v))

end Support

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-- **A symbol is determined by its quantization.** If two symbols, possibly of different
orders, have the same quantization on compactly supported Schwartz functions, their coefficients
are equal. -/
theorem coefficient_eq_of_forall_quantizeSchwartzValue_eq {a : Symbol n V W m}
    {b : Symbol n V W m'}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
      quantizeSchwartzValue a.coefficient u = quantizeSchwartzValue b.coefficient u) :
    a.coefficient = b.coefficient := by
  ext1 ⟨x, ξ⟩
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  obtain ⟨C', hC'⟩ := b.exists_norm_coefficient_le {x} isCompact_singleton
  exact eq_of_forall_quantizeSchwartzValue_eq (a.continuous_coefficient_slice x)
    (b.continuous_coefficient_slice x) (hC x rfl) (hC' x rfl) (fun u hu ↦ congrFun (h u hu) x) ξ

/-- Full quantization on Schwartz input is injective on symbols of a fixed order. -/
theorem quantizeSchwartzValue_injective :
    Function.Injective fun a : Symbol n V W m ↦ quantizeSchwartzValue a.coefficient :=
  fun _ _ h ↦ Symbol.ext <| coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦
    congrFun h u

/-- A symbol has compact spatial support exactly when its quantization has output support in a
compact set: `Op(a) u` is supported in one compact set `K` for every compactly supported
Schwartz function `u`. -/
theorem hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset
    {a : Symbol n V W m} :
    a.HasCompactSpatialSupport ↔ ∃ K : Set (CoordinateSpace n), IsCompact K ∧
      ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
        tsupport (quantizeSchwartzValue a.coefficient u) ⊆ K := by
  have hiff {K : Set (CoordinateSpace n)} (hK : IsCompact K) :=
    tsupport_quantizeSchwartzValue_subset_iff (V := V) hK.isClosed
      (fun x _ ↦ a.continuous_coefficient_slice x)
      (fun x _ ↦ (a.exists_norm_coefficient_le {x} isCompact_singleton).imp fun _ hC ↦
        ⟨m, hC x rfl⟩)
  rw [hasCompactSpatialSupport_iff]
  exact exists_congr fun K ↦ and_congr_right fun hK ↦ (hiff hK).symm

end Symbol

end TauCeti
