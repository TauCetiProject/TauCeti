/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform.Quantize
public import TauCeti.Analysis.Pseudodifferential.L2
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexInterpolation

/-!
# Sobolev mapping of uniform symbols

Let `a` be a symbol of order `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). This file proves that its left quantization `Op(a)` extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between
Bessel-potential spaces for every real `s`, for complex Hilbert fibres of any dimension
(`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`) and for finite-dimensional normed fibres
(`TauCeti.Symbol.exists_quantizeUniformSobolev`). In contrast to
`TauCeti.Symbol.exists_quantizeSobolev`, no compact spatial support is assumed; the case
`s = m = 0` is the Calderón–Vaillancourt theorem `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`,
from which everything else is derived.

We also name the continuous linear extension `TauCeti.Symbol.quantizeUniform` by density of
Schwartz functions in `H^s`, establish its algebraic and order-compatibility properties, transfer
uniform symbol composition `Op(a #_u b) = Op(a) ∘ Op(b)` (`TauCeti.Symbol.uniformSharp`) to all
Bessel-potential spaces, deduce that uniformly smoothing operators map every `H^r` into every
`H^s`, and record operator-level boundary checks (`Op(1) = id` of norm `1` on `H^0`, the sharp `L²`
bound for uniform spatial multipliers, and failure of `L²`-boundedness for coordinate multiplication
`x_j • T`).

## The commutator with the Laplacian

The derivative of `Op(a) u` falls either on `u` or on the position variable of `a`
(`TauCeti.Symbol.lineDerivOp_quantizeUniformCLM`), and a derivative on the right is exactly the
multiplication of the symbol by `i ξ_j` (`TauCeti.Symbol.quantizeUniformCLM_lineDerivOp`).
Applying both twice in every coordinate gives the exact formula

`Δ (Op(a) u) = Op(a) (Δ u) + Op((Δ_x + 2i ⟪ξ, ∇_x⟫) a) u`

(`TauCeti.Symbol.laplacian_quantizeUniformCLM`, in
`TauCeti.Analysis.Pseudodifferential.SchwartzMapping`), whose commutator symbol
`TauCeti.Symbol.laplacianCommutator a` is a uniform symbol of order `m + 1`.

## Even steps

Mathlib's Bessel multiplier of order `2` is the differential operator `J² = 1 - (2π)⁻² Δ`
(`SchwartzMap.fourierMultiplierCLM_one_add_norm_sq`), and composition with a Bessel multiplier on
the right is exact: `Op(a) ∘ J^t` is the quantization of `a(x, ξ) ⟨ξ / 2π⟩^t`
(`TauCeti.Symbol.quantizeUniformCLM_comp_besselMultiplier`). With the commutator formula
(`TauCeti.Symbol.quantizeUniformCLM_comp_besselPotential_two`, in
`TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier`), `J² ∘ Op(a)` is therefore the
quantization of a uniform symbol of order `m + 2`, and `Op(a)` is a combination of `J² ∘ Op(c)`
and `Op(c')` for uniform symbols `c`, `c'` of order `m - 2`. Since `J^t : H^s → H^{s - t}` is an
isometry, induction on `k` from the Calderón–Vaillancourt theorem shows that symbols of order `-2k`
map `L²` to `H^{2k}` and symbols of order `2k` map `L²` to `H^{-2k}`; composing with `J^s` on the
right gives the mapping `H^s → H^{s - m}` whenever `s - m` is an even integer.

## All real orders

Every real `s` lies between two consecutive orders `s₀ = m + 2k` and `s₁ = m + 2k + 2` at which
`s - m` is even, say `s = (1 - θ) s₀ + θ s₁` with `0 ≤ θ < 1`; then also
`s - m = (1 - θ) (s₀ - m) + θ (s₁ - m)`. Complex interpolation of the Hilbert scale `H^s`
(`SchwartzMap.HasSobolevExtension.interpolate`) turns the two even-step mappings into the mapping
`H^s → H^{s - m}`.

## Main results

* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_zero`: the Calderón–Vaillancourt
  theorem in the form `SchwartzMap.HasSobolevExtension` of an operator `L² → L²`.
* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`: the Sobolev mapping `H^s → H^{s - m}`
  for uniform symbols and every real `s`, for complex Hilbert fibres, in the composable form
  `SchwartzMap.HasSobolevExtension`.
* `TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`: the same mapping as an extension acting
  on tempered distributions.
* `TauCeti.Symbol.exists_quantizeUniformSobolev`: the same mapping for finite-dimensional complex
  normed fibres.
* `TauCeti.Symbol.quantizeUniform`: the explicit bounded operator
  `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`, agreeing with `quantizeSobolev` under compact spatial
  support and with `quantizeUniformOrderZero` at `m = s = 0`.
* `TauCeti.Symbol.quantizeUniform_comp_quantizeUniform` and
  `TauCeti.Symbol.toDistr_quantizeUniform_uniformSharp`: composition
  `Op(a) ∘ Op(b) = Op(a #_u b)` on Bessel-potential spaces.
* `TauCeti.Symbol.exists_continuousLinearMap_toDistr_quantizeUniform_eq`: uniformly smoothing
  operators map every `H^r` into every `H^s`.
* `TauCeti.Symbol.quantizeUniformOrderZero_const_id`,
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_const_id`,
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_ofSpatial_le`, and
  `TauCeti.Symbol.not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le`: operator-level
  boundary checks.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §§4.1, 6.4.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv Laplacian ContDiff
  BesselPotentialSpace
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Extension to Bessel-potential spaces -/

section Extension

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {s r : ℝ}

/-- **Calderón–Vaillancourt.** The quantization of a uniform symbol of order at most `0` extends
to a bounded operator on `H⁰ = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 := by
  obtain ⟨T, hT⟩ := exists_quantizeUniformOrderZeroLp (inclusion hm b) (hb.inclusion hm)
  refine SchwartzMap.hasSobolevExtension_iff.mpr
    ⟨((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) W 0 2).symm.toContinuousLinearEquiv :
      Lp W 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] H^{0}(CoordinateSpace n, W)) ∘L T ∘L
    ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V 0 2).toContinuousLinearEquiv :
      H^{0}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))), ?_⟩
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero, LinearIsometryEquiv.symm_apply_eq]
  refine Lp.ext ((hT u).trans ?_)
  filter_upwards [(quantizeUniformCLM b hb u).coeFn_toLp 2] with x hx
  rw [hx, coefficient_inclusion, quantizeUniformCLM_apply]

/-- On a Schwartz function, an extension of `Op(b)` gives the tempered distribution of
`Op(b) u`. -/
private theorem exists_toDistr_of_hasSobolevExtension {b : Symbol n V W m} {hb : b.IsUniform}
    (h : SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) s r) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue b.coefficient u x := by
  obtain ⟨T, hT⟩ := SchwartzMap.hasSobolevExtension_iff.mp h
  refine ⟨T, fun u φ ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply T, hT, ContinuousLinearMap.comp_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
  simp only [quantizeUniformCLM_apply]

/-- Uniform symbols of order at most `-2k` quantize to bounded operators `L² → H^{2k}`. -/
private theorem hasSobolevExtension_quantizeUniformCLM_of_le_neg (k : ℕ) :
    ∀ {μ : ℝ} (b : Symbol n V W μ) (hb : b.IsUniform), μ ≤ -(2 * k) →
      SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 (2 * k) := by
  induction k with
  | zero =>
    intro μ b hb hμ
    simpa using hasSobolevExtension_quantizeUniformCLM_zero hb (by simpa using hμ)
  | succ k ih =>
    intro μ b hb hμ
    push_cast at hμ ⊢
    -- `J² Op(b) = Op(b ⟨ξ / 2π⟩²) - (2π)⁻² Op(c)` with `c = (Δ_x + 2i ⟪ξ, ∇_x⟫) b`, and both
    -- symbols have order at most `-2k`.
    have h₁ := ih (b.comp (besselPotential 2)) (hb.comp (isUniform_besselPotential 2))
      (by linarith)
    have h₂ := ih b.laplacianCommutator hb.laplacianCommutator (by linarith)
    rw [← ContinuousLinearMap.id_comp (quantizeUniformCLM b hb),
      ← SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_neg_comp_fourierMultiplierCLM 2,
      ContinuousLinearMap.comp_assoc]
    refine (SchwartzMap.hasSobolevExtension_besselMultiplier (-2) (r := 2 * (k + 1))
      (s := 2 * k) (by ring)).comp ?_
    rw [eq_sub_of_add_eq (quantizeUniformCLM_comp_besselPotential_two b hb).symm]
    exact h₁.sub (h₂.smul_real _)

/-- Uniform symbols of order at most `2k` quantize to bounded operators `L² → H^{-2k}`. -/
private theorem hasSobolevExtension_quantizeUniformCLM_of_le (k : ℕ) :
    ∀ {μ : ℝ} (b : Symbol n V W μ) (hb : b.IsUniform), μ ≤ 2 * k →
      SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 (-(2 * k)) := by
  induction k with
  | zero =>
    intro μ b hb hμ
    simpa using hasSobolevExtension_quantizeUniformCLM_zero hb (by simpa using hμ)
  | succ k ih =>
    intro μ b hb hμ
    push_cast at hμ ⊢
    -- Write `L c = (Δ_x + 2i ⟪ξ, ∇_x⟫) c`. With `c = b ⟨ξ / 2π⟩⁻²` and `c' = (L c) ⟨ξ / 2π⟩⁻²`,
    -- the commutator with `J²` twice gives
    -- `Op(b) = J² Op(c) + (2π)⁻² (J² Op(c') + (2π)⁻² Op(L c'))`,
    -- where `c`, `c'` and `L c'` have order at most `2k`.
    set c := b.comp (besselPotential (-2))
    have hc : c.IsUniform := hb.comp (isUniform_besselPotential _)
    set c' := c.laplacianCommutator.comp (besselPotential (-2))
    have hc' : c'.IsUniform := hc.laplacianCommutator.comp (isUniform_besselPotential _)
    have hb' : quantizeUniformCLM b hb =
        quantizeUniformCLM (c.comp (besselPotential 2)) (hc.comp (isUniform_besselPotential 2)) :=
      quantizeUniformCLM_congr _ _ (by
        rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
          coefficient_comp_besselPotential_zero])
    have hlc : quantizeUniformCLM c.laplacianCommutator hc.laplacianCommutator =
        quantizeUniformCLM (c'.comp (besselPotential 2)) (hc'.comp (isUniform_besselPotential 2)) :=
      quantizeUniformCLM_congr _ _ (by
        rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
          coefficient_comp_besselPotential_zero])
    have hJ (r : ℝ) := SchwartzMap.hasSobolevExtension_besselMultiplier (F := W)
      (E := CoordinateSpace n) 2
      (r := r - 2) (s := r) (by ring)
    rw [hb', quantizeUniformCLM_comp_besselPotential_two c hc, hlc,
      quantizeUniformCLM_comp_besselPotential_two c' hc']
    have e₁ := (hJ (-(2 * k))).comp (ih c hc (by linarith))
    have e₂ := (hJ (-(2 * k))).comp (ih c' hc' (by linarith))
    have e₃ := (ih _ hc'.laplacianCommutator (by linarith)).mono (r' := -(2 * k) - 2)
      (by linarith)
    have hr : -(2 * ((k : ℝ) + 1)) = -(2 * k) - 2 := by ring
    rw [hr]
    exact e₁.add ((e₂.add (e₃.smul_real _)).smul_real _)

/-- Uniform symbols of order `m` quantize to bounded operators `H^s → H^{s - m}` when
`s - m ∈ 2ℤ`. -/
private theorem hasSobolevExtension_quantizeUniformCLM_of_sub_eq_two_mul (a : Symbol n V W m)
    (ha : a.IsUniform) {s : ℝ} {k : ℤ} (hk : s - m = 2 * k) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) := by
  -- `Op(a) = Op(a ⟨ξ / 2π⟩ ^ (-s)) ∘ J^s`, and `J^s : H^s → L²` is an isometry.
  have hb := ha.comp (isUniform_besselPotential (V := V) (n := n) (-s))
  have hJ := SchwartzMap.hasSobolevExtension_besselMultiplier (F := V) (E := CoordinateSpace n) s
    (r := 0) (s := s) (by ring)
  have ha' : quantizeUniformCLM a ha = quantizeUniformCLM _ hb ∘L
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
    rw [quantizeUniformCLM_comp_besselMultiplier]
    exact quantizeUniformCLM_congr _ _ (by
      rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
        coefficient_comp_besselPotential_zero])
  rw [ha']
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [hk]
    exact (hasSobolevExtension_quantizeUniformCLM_of_le_neg j _ hb
      (by push_cast at hk ⊢; linarith)).comp hJ
  · rw [hk]
    have h := (hasSobolevExtension_quantizeUniformCLM_of_le j _ hb
      (by push_cast at hk ⊢; linarith)).comp hJ
    simpa using h

/-- **Sobolev mapping of uniform symbols**, in composable form. Let `a` be a symbol of order `m`
whose estimates are uniform in the position, between complex Hilbert spaces. For every real `s`,
the quantization `Op(a)` extends to a bounded operator `H^s → H^{s - m}`. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) := by
  -- Interpolate between the even steps `s₀ = m + 2k` and `s₁ = m + 2(k + 1)`, `k = ⌊(s - m) / 2⌋`,
  -- with weight `θ = (s - m) / 2 - k ∈ [0, 1)`.
  set k := ⌊(s - m) / 2⌋
  set θ := (s - m) / 2 - k with hθ
  have hθ₀ : 0 ≤ θ := sub_nonneg.mpr (Int.floor_le _)
  have hθ₁ : θ ≤ 1 := by linarith [Int.lt_floor_add_one ((s - m) / 2)]
  have h₀ := hasSobolevExtension_quantizeUniformCLM_of_sub_eq_two_mul a ha
    (s := m + 2 * k) (k := k) (by ring)
  have h₁ := hasSobolevExtension_quantizeUniformCLM_of_sub_eq_two_mul a ha
    (s := m + 2 * (k + 1)) (k := k + 1) (by push_cast; ring)
  have h := h₀.interpolate h₁ ⟨hθ₀, hθ₁⟩
  rwa [show (1 - θ) * (m + 2 * k) + θ * (m + 2 * (k + 1)) = s by rw [hθ]; ring,
    show (1 - θ) * (m + 2 * k - m) + θ * (m + 2 * (k + 1) - m) = s - m by rw [hθ]; ring] at h

/-- **Sobolev mapping of uniform symbols**, for complex Hilbert fibres. Let `a` be a symbol of
order `m` whose estimates are uniform in the position. For every real `s`, the quantization
`Op(a)` extends from Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.
No compact spatial support and no finite dimension is needed. -/
theorem exists_quantizeUniformSobolevHilbert (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  exists_toDistr_of_hasSobolevExtension (hasSobolevExtension_quantizeUniformCLM a ha s)

end Extension

/-! ### Sobolev mapping -/

section Mapping

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of uniform symbols.** Let `a` be a symbol of order `m` whose estimates are
uniform in the position, between finite-dimensional complex normed spaces. For every real `s`,
the quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support is needed.

The norms of `V` and `W` need not come from inner products: as for
`TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms with `ℂ^k` and `ℂ^l` reduce the statement
to complex Hilbert fibres
(`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`). -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨T, hT⟩ := exists_quantizeUniformSobolevHilbert _ (ha.map
    ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)) s
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂ hT⟩

end Mapping

/-! ### Explicit operator `quantizeUniform` and finite-dimensional bounds -/

section NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **Sobolev mapping of uniform pseudodifferential operators.** For a uniform symbol `a` of real
order `m` and every real `s`, `quantizeUniform a ha s` is the continuous linear extension of `Op(a)`
from Schwartz functions to `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`. -/
def quantizeUniform (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

private theorem quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ)
    (hC : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC u

private theorem quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ)
    (L : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W))
    (hL : ∀ u : 𝓢(CoordinateSpace n, V),
      L (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
        SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)) :
    a.quantizeUniform ha s = L := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s
    ⟨‖L‖, fun v ↦ (hL v).symm ▸ L.le_opNorm _⟩ u, hL u]

/-- The zero symbol quantizes to `0 : H^s →L[ℂ] H^{s - m}`. -/
@[simp]
theorem quantizeUniform_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).quantizeUniform h s = 0 :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM h s 0 fun _ ↦ by simp

/-- For finite-dimensional complex normed spaces `V` and `W`, a uniform symbol `a` of order `m`
satisfies the `H^s → H^{s - m}` norm estimate on Schwartz functions. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨T, hT⟩ := exists_quantizeUniformSobolev a ha s
  refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
  have hu : T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) := by
    refine BesselPotentialSpace.ext ?_
    ext φ
    rw [hT u φ, SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
    simp only [quantizeUniformCLM_apply]
  rw [← hu]
  exact T.le_opNorm _

/-- On Schwartz functions between finite-dimensional complex normed spaces, `quantizeUniform`
agrees with `quantizeUniformCLM`. -/
theorem quantizeUniform_toBesselPotentialSpaceCLM_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) := by
  obtain ⟨C, -, hC⟩ :=
    ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s
  exact quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨C, hC⟩ u

end NormedSpace

/-! ### Complex Hilbert coefficient spaces and operator calculus on `H^s` -/

section InnerProductSpace

variable {m' : ℝ} {V W U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

/-- For complex Hilbert spaces `V` and `W`, a uniform symbol `a` of order `m` satisfies the
`H^s → H^{s - m}` norm estimate on Schwartz functions. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ :=
  SchwartzMap.hasSobolevExtension_iff_exists_norm_le.mp
    (hasSobolevExtension_quantizeUniformCLM a ha s)

/-- On Schwartz functions between complex Hilbert spaces, `quantizeUniform` agrees with
`quantizeUniformCLM`. -/
@[simp]
theorem quantizeUniform_toBesselPotentialSpaceCLM {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s
  exact quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨C, hC⟩ u

/-- On a Schwartz function `u`, `Op(a) : H^s → H^{s - m}` evaluates as a tempered distribution to
the quantization integral `quantizeSchwartzValue a.coefficient u`. -/
theorem toDistr_quantizeUniform_toBesselPotentialSpaceCLM_apply {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniform_toBesselPotentialSpaceCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.coe_apply, coe_quantizeUniformCLM]

private theorem quantizeUniform_congr {a b : Symbol n V W m} (hab : a = b) (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) : a.quantizeUniform ha s = b.quantizeUniform hb s :=
  hab ▸ rfl

/-- `Op(a) : H^s → H^{s - m}` is additive in the uniform symbol `a`. -/
theorem quantizeUniform_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a + b).quantizeUniform (ha.add hb) s = a.quantizeUniform ha s + b.quantizeUniform hb s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformCLM_add ha hb]

/-- `Op(a) : H^s → H^{s - m}` is homogeneous in the uniform symbol `a`. -/
theorem quantizeUniform_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).quantizeUniform (ha.smul c) s = c • a.quantizeUniform ha s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformCLM_smul ha c]

/-- Negating a uniform symbol negates its Sobolev extension. -/
theorem quantizeUniform_neg {a : Symbol n V W m} (ha : a.IsUniform)
    (hna : (-a).IsUniform := ha.neg) (s : ℝ) :
    (-a).quantizeUniform hna s = -a.quantizeUniform ha s := by
  rw [quantizeUniform_congr (neg_one_smul ℂ a).symm hna (ha.smul (-1)) s,
    quantizeUniform_smul ha, neg_one_smul]

/-- Subtracting uniform symbols subtracts their Sobolev extensions. -/
theorem quantizeUniform_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (hab : (a - b).IsUniform := ha.sub hb) (s : ℝ) :
    (a - b).quantizeUniform hab s = a.quantizeUniform ha s - b.quantizeUniform hb s :=
  eq_sub_iff_add_eq.2 ((quantizeUniform_add hab hb s).symm.trans
    (quantizeUniform_congr (sub_add_cancel a b) _ _ s))

/-- Order inclusion `m ≤ m'` composes `quantizeUniform` with `H^{s - m} ⊆ H^{s - m'}`. -/
theorem quantizeUniform_inclusion {a : Symbol n V W m} (h : m ≤ m') (ha : a.IsUniform) (s : ℝ) :
    (inclusion h a).quantizeUniform (ha.inclusion h) s =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniform ha s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformCLM_inclusion ha h]

/-- The Sobolev extensions `Op(a) : H^s → H^{s - m}` commute with `H^s ⊆ H^r`. -/
theorem quantizeUniform_comp_inclusion {a : Symbol n V W m} (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) :
    a.quantizeUniform ha r ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniform ha s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by simp

private theorem toDistr_quantizeUniform_inclusion {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    (hts : t ≤ s) (u : H^{s}(CoordinateSpace n, V)) :
    (a.quantizeUniform ha s u).toDistr =
      (b.quantizeUniform hb t (BesselPotentialSpace.inclusion hts u)).toDistr := by
  have key : BesselPotentialSpace.inclusion (min_le_left (s - m) (t - m')) ∘L
        a.quantizeUniform ha s =
      BesselPotentialSpace.inclusion (min_le_right (s - m) (t - m')) ∘L
        b.quantizeUniform hb t ∘L BesselPotentialSpace.inclusion hts :=
    BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun v ↦
      BesselPotentialSpace.ext <| by ext φ; simp [hab]
  simpa using congrArg (fun T ↦ (T u).toDistr) key

/-- **Compatibility across orders.** Uniform symbols with the same coefficient act identically on
elements of `H^s` and `H^t` representing the same tempered distribution. -/
theorem toDistr_quantizeUniform_congr {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    {u : H^{s}(CoordinateSpace n, V)} {v : H^{t}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniform ha s u).toDistr = (b.quantizeUniform hb t v).toDistr := by
  rcases le_total t s with h | h
  · rw [toDistr_quantizeUniform_inclusion hab ha hb h u]
    congr 2; exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])
  · rw [toDistr_quantizeUniform_inclusion hab.symm hb ha h v]
    congr 2; exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])

/-- **Compatibility with compact spatial support:** `quantizeUniform` agrees with
`quantizeSobolev`. -/
theorem quantizeUniform_eq_quantizeSobolev {a : Symbol n V W m} (hc : a.HasCompactSpatialSupport)
    (ha : a.IsUniform := hc.isUniform) (s : ℝ) :
    a.quantizeUniform ha s = a.quantizeSobolev hc s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun _ ↦
    BesselPotentialSpace.ext <| by ext φ; simp

/-- **Compatibility at order zero:** at `m = s = 0`, `quantizeUniform` agrees with
`quantizeUniformOrderZero`. -/
theorem quantizeUniform_zero_eq_quantizeUniformOrderZero {a : Symbol n V W 0} (ha : a.IsUniform) :
    BesselPotentialSpace.inclusion (sub_zero (0 : ℝ)).ge ∘L a.quantizeUniform ha 0 =
      a.quantizeUniformOrderZero ha :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformOrderZero_toBesselPotentialSpaceCLM ha
      ha.exists_eLpNorm_quantizeSchwartzValue_le]

/-- **Operator composition of uniform symbols on Bessel-potential spaces:**
`Op(a) ∘ Op(b) = Op(a #_u b)` as bounded operators `H^s →L[ℂ] H^{s - m - m'}`. -/
theorem quantizeUniform_comp_quantizeUniform {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a.quantizeUniform ha (s - m)).comp (b.quantizeUniform hb s) =
      BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - m - m' ≤ s - (m' + m)) ∘L
        (a.uniformSharp b hb).quantizeUniform (ha.uniformSharp hb) s :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformCLM_uniformSharp ha hb]

/-- **Composition of uniform quantizations as tempered distributions.** -/
theorem toDistr_quantizeUniform_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniform (ha.uniformSharp hb) s u).toDistr =
      (a.quantizeUniform ha (s - m) (b.quantizeUniform hb s u)).toDistr := by
  simpa using (congrArg (fun T ↦ (T u).toDistr) (quantizeUniform_comp_quantizeUniform ha hb s)).symm

/-- **Uniform smoothing operators:** `Symbol.IsUniformlySmoothing` maps any `H^r` into any `H^s`. -/
theorem exists_continuousLinearMap_toDistr_quantizeUniform_eq {a : Symbol n V W m}
    (ha : a.IsUniform) (hsm : a.IsUniformlySmoothing) (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr → (a.quantizeUniform ha t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hcoeff⟩ := isUniformlySmoothing_iff.1 hsm (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L b.quantizeUniform hb r,
    fun huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact toDistr_quantizeUniform_congr hcoeff.symm ha hb huv

/-- A constant symbol `const T` quantizes on `H^s` to postcomposition with `T`. -/
theorem quantizeUniform_const (T : V →L[ℂ] W) (s : ℝ) :
    (const T : Symbol n V W 0).quantizeUniform (isUniform_const T) s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L BesselPotentialSpace.postcomp _ s 2 T :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM (isUniform_const T) s _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_const,
      ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- The constant identity symbol `1` quantizes on `H^s` to `H^s →L[ℂ] H^{s - 0}`. -/
@[simp]
theorem quantizeUniform_const_id (s : ℝ) :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniform (isUniform_const _) s =
      BesselPotentialSpace.inclusion (sub_zero s).le :=
  BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ by
    rw [quantizeUniform_toBesselPotentialSpaceCLM, quantizeUniformCLM_const,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]; congr 1

/-- Multiplication by a Schwartz scalar function `χ` on `H^s` is the Sobolev quantization of the
uniform spatial symbol `χ(x) id`. -/
theorem quantizeUniform_ofSpatial_smul (χ : 𝓢(CoordinateSpace n, ℂ))
    (hχ : ContDiff ℝ ∞ fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
    (hu : (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).IsUniform) (s : ℝ) :
    (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).quantizeUniform hu s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L BesselPotentialSpace.smulLeftCLM s χ :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM hu s _ fun u ↦
    BesselPotentialSpace.ext <| by
      have hc : (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).coefficient =
          fun p ↦ χ p.1 • ContinuousLinearMap.id ℂ V := funext (coefficient_ofSpatial _ hχ)
      have hq (x : CoordinateSpace n) :
          quantizeSchwartzValue (fun p ↦ χ p.1 • ContinuousLinearMap.id ℂ V) u x = χ x • u x := by
        simpa using quantizeSchwartzValue_comp_fst (fun y ↦ χ y • ContinuousLinearMap.id ℂ V) u x
      ext φ
      simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
        BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
        TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq,
        SchwartzMap.toTemperedDistributionCLM_apply_apply,
        SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, coe_quantizeUniformCLM, hc, hq]

end InnerProductSpace

/-! ### Constant symbols, spatial multipliers, and sharpness of uniformity -/

section SpatialBounds

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

private def unitBump (n : ℕ) : ContDiffBump (0 : CoordinateSpace n) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

private def unitBumpSchwartz (n : ℕ) (v : V) : 𝓢(CoordinateSpace n, V) :=
  (unitBump n).hasCompactSupport.smul_right.toSchwartzMap
    ((unitBump n).contDiff.smul (contDiff_const (c := v)))

omit [CompleteSpace V] in
private theorem unitBumpSchwartz_apply (v : V) (x : CoordinateSpace n) :
    unitBumpSchwartz n v x = unitBump n x • v :=
  HasCompactSupport.toSchwartzMap_toFun _ _ x

omit [CompleteSpace W] in
private theorem eLpNorm_unitBumpSchwartz_ne_zero {u : 𝓢(CoordinateSpace n, W)} (hu0 : u 0 ≠ 0) :
    eLpNorm u 2 volume ≠ 0 := by
  rw [ne_eq, eLpNorm_eq_zero_iff two_ne_zero]
  exact fun hae ↦ hu0 (congrFun ((u.continuous.ae_eq_iff_eq volume continuous_zero).1 hae) 0)

/-- **The constant symbol `1` quantizes to the identity on `H^0`.** -/
@[simp]
theorem quantizeUniformOrderZero_const_id :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _) =
      ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V) := by
  have h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue
          (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume :=
    ⟨1, zero_le_one, fun u ↦ by
      rw [← coe_quantizeUniformCLM _ (isUniform_const _), quantizeUniformCLM_const,
        ENNReal.ofReal_one, one_mul]
      exact le_of_eq (congrArg (fun v : 𝓢(CoordinateSpace n, V) ↦ eLpNorm v 2 volume)
        (by ext x; simp))⟩
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM (isUniform_const _) h1 u,
    quantizeUniformCLM_const, ContinuousLinearMap.id_apply]
  congr 1

/-- On a nontrivial Banach fibre `V`, the order-zero `L²` quantization of `1` has operator norm
equal to `1`. -/
theorem norm_quantizeUniformOrderZero_const_id [Nontrivial V] :
    ‖(const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let u := unitBumpSchwartz n v
  have hu0 : u 0 ≠ 0 := by
    simpa [u, unitBumpSchwartz_apply,
      (unitBump n).one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] using hv
  have hnorm_ne : ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ ≠ 0 := by
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero]
    exact ENNReal.toReal_ne_zero.2 ⟨eLpNorm_unitBumpSchwartz_ne_zero hu0,
      (u.memLp 2).eLpNorm_ne_top⟩
  have : Nontrivial H^{0}(CoordinateSpace n, V) :=
    ⟨⟨SchwartzMap.toBesselPotentialSpaceCLM 0 2 u, 0, fun h ↦ hnorm_ne (by simp [h])⟩⟩
  rw [quantizeUniformOrderZero_const_id, ContinuousLinearMap.norm_id]

/-- **Sharp `L²` norm bound for spatial multiplication symbols.** If `f(x)` defines a uniform
spatial symbol of order `0` with `‖f(x)‖ ≤ C` everywhere (`0 ≤ C`), then
`‖Op(f)‖_{H^0 → H^0} ≤ C`. -/
theorem norm_quantizeUniformOrderZero_ofSpatial_le {f : CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (hu : (ofSpatial f hf).IsUniform) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(ofSpatial f hf).quantizeUniformOrderZero hu‖ ≤ C := by
  refine norm_quantizeUniformOrderZero_le hu hC0 fun u ↦ ?_
  have hc : (ofSpatial f hf).coefficient = fun p ↦ f p.1 := funext (coefficient_ofSpatial f hf)
  have hq : quantizeSchwartzValue (ofSpatial f hf).coefficient u = fun x ↦ f x (u x) := by
    funext x; rw [hc, quantizeSchwartzValue_comp_fst]
  have hle : eLpNorm (fun x ↦ f x (u x)) 2 volume ≤ eLpNorm (C • ⇑u) 2 volume := by
    refine eLpNorm_mono (hf.continuous.clm_apply u.continuous).aestronglyMeasurable fun x ↦ ?_
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hC0]
    exact (ContinuousLinearMap.le_opNorm (f x) (u x)).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hc_norm : ‖C‖ₑ = ENNReal.ofReal C := by rw [← ofReal_norm, Real.norm_of_nonneg hC0]
  rw [hq, ← hc_norm, ← eLpNorm_const_smul C (⇑u) 2 volume]
  exact hle

/-- **Multiplication by a coordinate is not `L²`-bounded.** For any coordinate index `j` and
nonzero operator `T : V →L[ℂ] W`, the symbol `(x, ξ) ↦ x_j • T` has local order `0`
(`TauCeti.Symbol.ofSpatial`), fails to be uniform (`TauCeti.Symbol.not_isUniform_ofSpatial_smul`),
and satisfies no `L²` bound on Schwartz functions. -/
theorem not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le (j : Fin n) {T : V →L[ℂ] W}
    (hT : T ≠ 0) (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬∃ C : ℝ, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (ofSpatial (fun x ↦ x j • T) hf).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by by_contra! h; exact hT (ContinuousLinearMap.ext h)
  set u₀ := unitBumpSchwartz n v
  set N := eLpNorm u₀ 2 volume
  set M := eLpNorm (u₀.postcompCLM T) 2 volume
  have hM_ne : M ≠ 0 := eLpNorm_unitBumpSchwartz_ne_zero <| by
    simpa [u₀, unitBumpSchwartz_apply,
      (unitBump n).one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] using hv
  have hM_pos : 0 < M.toReal := ENNReal.toReal_pos hM_ne ((u₀.postcompCLM T).memLp 2).eLpNorm_ne_top
  set R : ℝ := max C 0 * N.toReal / M.toReal + 3
  have hR2 : 0 ≤ R - 2 := by
    have : 0 ≤ max C 0 * N.toReal / M.toReal := by positivity
    linarith
  set aR : CoordinateSpace n := R • EuclideanSpace.single j (1 : ℝ)
  set uR : 𝓢(CoordinateSpace n, V) := u₀.compSubConstCLM ℂ aR
  have huR_norm : eLpNorm uR 2 volume = N :=
    eLpNorm_comp_measurePreserving u₀.continuous.aestronglyMeasurable
      (measurePreserving_sub_right volume aR)
  have hTuR : eLpNorm (fun x ↦ T (uR x)) 2 volume = M :=
    eLpNorm_comp_measurePreserving (u₀.postcompCLM T).continuous.aestronglyMeasurable
      (measurePreserving_sub_right volume aR)
  have hpt (x : CoordinateSpace n) :
      ‖(R - 2) • T (uR x)‖ ≤
        ‖quantizeSchwartzValue (ofSpatial (fun y ↦ y j • T) hf).coefficient uR x‖ := by
    have hc : (ofSpatial (fun y ↦ y j • T) hf).coefficient = fun p ↦ p.1 j • T :=
      funext (coefficient_ofSpatial _ hf)
    have hq : quantizeSchwartzValue (ofSpatial (fun y ↦ y j • T) hf).coefficient uR x =
        x j • T (uR x) := by
      rw [hc]; simpa using quantizeSchwartzValue_comp_fst (fun y : CoordinateSpace n ↦ y j • T) uR x
    rw [hq, norm_smul, norm_smul, Real.norm_of_nonneg hR2, Real.norm_eq_abs]
    by_cases hsupp : x - aR ∈ Function.support (unitBump n)
    · rw [(unitBump n).support_eq, show (unitBump n).rOut = 2 from rfl, Metric.mem_ball,
        dist_zero_right] at hsupp
      have hcoord : |(x - aR) j| ≤ 2 := (PiLp.norm_apply_le (x - aR) j).trans hsupp.le
      rw [PiLp.sub_apply, show aR j = R by simp [aR], abs_le] at hcoord
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (x j)]) (norm_nonneg _)
    · simp [uR, u₀, SchwartzMap.compSubConstCLM_apply, unitBumpSchwartz_apply,
        Function.notMem_support.1 hsupp]
  have hc_norm : ‖R - 2‖ₑ = ENNReal.ofReal (R - 2) := by
    rw [← ofReal_norm, Real.norm_of_nonneg hR2]
  have hlow : ENNReal.ofReal (R - 2) * M ≤ ENNReal.ofReal (max C 0) * N :=
    calc ENNReal.ofReal (R - 2) * M
        = eLpNorm ((R - 2) • fun x ↦ T (uR x)) 2 volume := by
            rw [eLpNorm_const_smul, hc_norm, hTuR]
      _ ≤ eLpNorm (quantizeSchwartzValue (ofSpatial (fun y ↦ y j • T) hf).coefficient uR)
            2 volume :=
          eLpNorm_mono ((T.continuous.comp uR.continuous).const_smul _).aestronglyMeasurable hpt
      _ ≤ ENNReal.ofReal (max C 0) * N :=
          (huR_norm ▸ hC uR).trans
            (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C 0)) zero_le)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (u₀.memLp 2).eLpNorm_ne_top) hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR2,
    ENNReal.toReal_ofReal (le_max_right C 0)] at hreal
  have hRM : (R - 2) * M.toReal = max C 0 * N.toReal + M.toReal := by
    rw [show R - 2 = max C 0 * N.toReal / M.toReal + 1 by simp only [R]; ring,
      add_mul, one_mul, div_mul_cancel₀ _ hM_pos.ne']
  linarith

end SpatialBounds

end Symbol

end TauCeti
