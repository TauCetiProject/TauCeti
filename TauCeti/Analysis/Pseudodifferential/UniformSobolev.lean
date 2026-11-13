/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Extension

/-!
# Sobolev mapping of uniform symbols at even steps

Let `a` be a symbol of order `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). This file proves that its left quantization `Op(a)` extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between
Bessel-potential spaces whenever `s - m` is an even integer, for complex Hilbert fibres of any
dimension (`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul`) and for
finite-dimensional normed fibres (`TauCeti.Symbol.exists_quantizeUniformSobolev_of_sub_eq_two_mul`).
In contrast to `TauCeti.Symbol.exists_quantizeSobolev`, no compact spatial support is assumed; the
case `s = m = 0` is the Calderón–Vaillancourt theorem
`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`, from which everything else is derived.

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
right gives the general statement.

Only even steps arise because `J²` is the only Bessel multiplier used on the left. Intermediate
orders need either interpolation of the scale `H^s` between consecutive even orders, or the
composition of `J^t` with `Op(a)` on the left for every real `t`.

## Main results

* `TauCeti.Symbol.exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul`: the Sobolev mapping
  `H^s → H^{s - m}` for uniform symbols when `s - m ∈ 2ℤ`, for complex Hilbert fibres.
* `TauCeti.Symbol.exists_quantizeUniformSobolev_of_sub_eq_two_mul`: the same mapping for
  finite-dimensional complex normed fibres.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv Laplacian ContDiff
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
private theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 := by
  obtain ⟨T, hT⟩ := exists_quantizeUniformOrderZeroLp (inclusion hm b) (hb.inclusion hm)
  refine ⟨((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) W 0 2).symm.toContinuousLinearEquiv :
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
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun u φ ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply T, hT, ContinuousLinearMap.comp_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
  simp only [quantizeUniformCLM_apply]

omit [CompleteSpace V] in
/-- `Op(b) = J^{-2} (J² Op(b))` on Schwartz space. -/
private theorem besselMultiplier_neg_two_comp_besselMultiplier_two
    (A : 𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, W)) :
    SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((-2 : ℝ) / 2) : ℝ) : ℂ)) ∘L
      (SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) ∘L A) = A := by
  ext1 u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM]
  norm_num

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
    rw [← besselMultiplier_neg_two_comp_besselMultiplier_two (quantizeUniformCLM b hb)]
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
private theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform)
    {s : ℝ} {k : ℤ} (hk : s - m = 2 * k) :
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

/-- **Sobolev mapping of uniform symbols at even steps**, for complex Hilbert fibres. Let `a` be a
symbol of order `m` whose estimates are uniform in the position. If `s - m` is an even integer, the
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support and no finite dimension is needed. -/
theorem exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul (a : Symbol n V W m)
    (ha : a.IsUniform) {s : ℝ} {k : ℤ} (hk : s - m = 2 * k) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  exists_toDistr_of_hasSobolevExtension (hasSobolevExtension_quantizeUniformCLM a ha hk)

end Extension

/-! ### Sobolev mapping -/

section Mapping

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of uniform symbols at even steps.** Let `a` be a symbol of order `m` whose
estimates are uniform in the position, between finite-dimensional complex normed spaces. If
`s - m` is an even integer, the quantization `Op(a)` extends from Schwartz functions to a bounded
operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support is needed.

The norms of `V` and `W` need not come from inner products: as for
`TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms with `ℂ^k` and `ℂ^l` reduce the statement
to complex Hilbert fibres
(`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul`). -/
theorem exists_quantizeUniformSobolev_of_sub_eq_two_mul (a : Symbol n V W m) (ha : a.IsUniform)
    {s : ℝ} {k : ℤ} (hk : s - m = 2 * k) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨T, hT⟩ := exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul _ (ha.map
    ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)) hk
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂ hT⟩

end Mapping

end Symbol

end TauCeti
