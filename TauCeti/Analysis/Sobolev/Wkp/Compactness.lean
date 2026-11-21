/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.GraphStep.Compactness
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Ehrling

/-!
# Compactness criteria for `W^{k+1,p}`

An operator into `W^{k+1,p}(Ω)` is compact as soon as its lower-order part in `W^{k,p}(Ω)` and its
highest weak-derivative field are compact. The graph norm of `W^{k+1,p}(Ω)` is bounded by the sum
of the norms of these two components, so the pair of component maps is an antilipschitz embedding
and total boundedness transfers back along it. No boundedness or boundary regularity of `Ω` is
used.

This is the induction step shared by the higher-order Rellich–Kondrachov theorems, both on
compactly contained subdomains and on bounded Lipschitz domains.

Combined with the coordinatewise step `TauCeti.WeakDerivStep.isCompactOperator_comp_prevL`, it
lifts first-order compactness to every order: if the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is compact,
then forgetting the highest weak derivative `W^{k+1,p}(Ω) → W^{k,p}(Ω)` is compact for every `k`.
Any domain with a first-order Rellich theorem therefore has the higher-order one.

Compactness of the truncations gives the interpolation inequalities of `W^{k,p}(Ω)` with a
non-explicit constant, by Ehrling's inequality: lower-order norms are bounded by an arbitrarily
small multiple of a higher norm plus a multiple of the `Lᵖ` norm, which is injective on
`W^{k,p}(Ω)` because weak derivatives are unique. This is how lower-order terms are absorbed in
global a priori estimates on domains with a Rellich theorem.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL`: the
  componentwise compactness criterion.
* `TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isCompactOperator_valueL`: higher-order
  compactness from first-order compactness.
* `TauCeti.Wkp.isCompactOperator_toOrderL_of_isCompactOperator_lowerOrderL` and
  `TauCeti.Wkp.isCompactOperator_valueL_of_isCompactOperator_lowerOrderL`: compactness of
  forgetting the highest weak derivative makes every truncation, and the `Lᵖ` value map, compact.
* `TauCeti.Wkp.exists_norm_toOrderL_le_of_isCompactOperator`: Ehrling's inequality
  `‖u‖_{W^{j,p}} ≤ ε ‖u‖_{W^{k,p}} + C ‖u‖_{Lᵖ}` when truncation to order `j` is compact.
* `TauCeti.Wkp.exists_norm_lowerOrder_le_of_isCompactOperator`: the lower-order part bounded by
  the top derivative, `‖u‖_{W^{k,p}} ≤ ε ‖D^{k+1} u‖ + C ‖u‖_{Lᵖ}`.
* `TauCeti.Wkp.exists_norm_iteratedGradient_lowerOrder_le_of_isCompactOperator`: the interpolation
  inequality `‖D^{k+1} u‖ ≤ ε ‖D^{k+2} u‖ + C ‖u‖_{Lᵖ}`.
* `TauCeti.Wkp.exists_norm_le_of_norm_iteratedGradient_le_of_isCompactOperator`: absorption of the
  lower-order terms in an estimate of the top derivative.

## References

* G. Ehrling, *On a type of eigenvalue problem for certain elliptic differential operators*,
  Math. Scand. **2** (1954), 267–285.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.28 and the proof of Theorem 9.13.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- An operator into `W^{k+1,p}` is compact as soon as its lower-order part and its highest
derivative field are compact, since the graph norm is controlled by these two components. -/
theorem isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : ℕ)
    (T : X →L[ℝ] Wkp mu Omega p (k + 1))
    (hlo : IsCompactOperator ((lowerOrderL k).comp T))
    (hD : IsCompactOperator ((iteratedGradientL k).comp T)) : IsCompactOperator T := by
  let J := (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k).prod (iteratedGradientL k)
  have hj : AntilipschitzWith 2 J := J.antilipschitz_of_bound fun u => by
    have h := norm_le_norm_lowerOrder_add_norm_iteratedGradient k u
    have hJu : J u = (lowerOrder k u, iteratedGradient k u) := by
      dsimp only [J]
      rw [ContinuousLinearMap.prod_apply, lowerOrderL_apply k u, iteratedGradientL_apply k u]
    have h₁ : ‖lowerOrder k u‖ ≤ ‖J u‖ := by
      rw [hJu, Prod.norm_def]
      exact le_max_left _ _
    have h₂ : ‖iteratedGradient k u‖ ≤ ‖J u‖ := by
      rw [hJu, Prod.norm_def]
      exact le_max_right _ _
    norm_num only [NNReal.coe_ofNat]
    linarith
  have hJT : IsCompactOperator (J.comp T) := by
    have heq : J.comp T =
        (ContinuousLinearMap.inl ℝ _ _).comp ((lowerOrderL k).comp T) +
          (ContinuousLinearMap.inr ℝ _ _).comp ((iteratedGradientL k).comp T) := by
      apply ContinuousLinearMap.ext
      intro u
      simp [J]
    rw [heq]
    simpa only [FunLike.coe_add, ContinuousLinearMap.coe_comp] using
      (hlo.clm_comp (ContinuousLinearMap.inl ℝ _ _)).add
        (hD.clm_comp (ContinuousLinearMap.inr ℝ _ _))
  apply (isCompactOperator_iff_totallyBounded_image_closedBall _ zero_lt_one).mpr
  apply (totallyBounded_image_iff (hj.isUniformInducing J.uniformContinuous)).mp
  simpa only [Set.image_image, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_def] using
    hJT.totallyBounded_image_closedBall 1

/-- **Higher-order Rellich compactness from first-order compactness.** If the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is compact, then forgetting the highest weak derivative is a compact operator
`W^{k+1,p}(Ω) → W^{k,p}(Ω)` for every `k`. -/
theorem isCompactOperator_lowerOrderL_of_isCompactOperator_valueL
    (h : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := p))) :
    ∀ k : ℕ, IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k) := by
  intro k
  induction k with
  | zero =>
      have heq : lowerOrderL (mu := mu) (Omega := Omega) (p := p) 0 = W1p.valueL := by
        apply ContinuousLinearMap.ext
        intro u
        rw [lowerOrderL_apply 0 u, lowerOrder_zero u]
        exact (W1p.valueL_apply _).symm
      rw [heq]
      exact h
  | succ k ih =>
      let base := (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL
      have heq : (iteratedGradientL (mu := mu) (Omega := Omega) (p := p) k).comp
          (lowerOrderL (k + 1)) =
          base.comp (WeakDerivStep.prevL base) := by
        apply ContinuousLinearMap.ext
        intro (u : Wkp mu Omega p (k + 2))
        exact ((congrArg (iteratedGradientL k) (lowerOrderL_apply (k + 1) u)).trans
          (iteratedGradientL_apply k _)).trans
          ((iteratedGradient_eq_sobolevStage_iteratedGradientL k _).trans
            (congrArg base ((lowerOrder_succ k u).trans (WeakDerivStep.prevL_apply base u).symm)))
      refine isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL k
        (lowerOrderL (k + 1)) (ih.comp_clm _) ?_
      rw [heq]
      exact WeakDerivStep.isCompactOperator_comp_prevL base h

/-- **Compactness of every truncation from one-step compactness.** If forgetting the highest weak
derivative `W^{m+1,p}(Ω) → W^{m,p}(Ω)` is compact, then so is truncation
`W^{m+1,p}(Ω) → W^{j,p}(Ω)` for every `j ≤ m`. -/
theorem isCompactOperator_toOrderL_of_isCompactOperator_lowerOrderL {j m : ℕ} (h : j ≤ m)
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    IsCompactOperator (toOrderL (mu := mu) (Omega := Omega) (p := p) (Nat.le_succ_of_le h)) := by
  rw [toOrderL_succ h]
  exact hK.clm_comp _

/-- **Compactness of the value map from one-step compactness.** If forgetting the highest weak
derivative `W^{m+1,p}(Ω) → W^{m,p}(Ω)` is compact, then so is the `Lᵖ` value map
`W^{m+1,p}(Ω) → Lᵖ(Ω)`. -/
theorem isCompactOperator_valueL_of_isCompactOperator_lowerOrderL {m : ℕ}
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) m)) :
    IsCompactOperator (valueL (mu := mu) (Omega := Omega) (p := p) (m + 1)) := by
  rw [← toOrderL_zero_left (m + 1) (Nat.zero_le _)]
  exact isCompactOperator_toOrderL_of_isCompactOperator_lowerOrderL (Nat.zero_le m) hK

/-! ### Interpolation inequalities from compactness -/

/-- **Ehrling's inequality for `W^{k,p}(Ω)`.** If forgetting the weak derivatives above order
`j ≤ k` is a compact operator `W^{k,p}(Ω) → W^{j,p}(Ω)`, then for every `ε > 0` there is `C` with
`‖u‖_{W^{j,p}(Ω)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every `u ∈ W^{k,p}(Ω)`. -/
theorem exists_norm_toOrderL_le_of_isCompactOperator {j k : ℕ} (h : j ≤ k)
    (hK : IsCompactOperator (toOrderL (mu := mu) (Omega := Omega) (p := p) h)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp mu Omega p k, ‖toOrderL h u‖ ≤ ε * ‖u‖ + C * ‖value k u‖ := by
  have hinj : Function.Injective (valueL (mu := mu) (Omega := Omega) (p := p) j) :=
    fun u v huv ↦ ext j (by simpa only [valueL_apply] using huv)
  obtain ⟨C, hC, hle⟩ := hK.exists_norm_le_mul_norm_add_mul_norm hinj hε
  refine ⟨C, hC, fun u ↦ ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, valueL_apply, value_toOrderL] using hle u

/-- **The lower-order part is controlled by the top derivative.** If forgetting the highest weak
derivative `W^{k+1,p}(Ω) → W^{k,p}(Ω)` is compact, then for every `ε > 0` there is `C` with
`‖u‖_{W^{k,p}(Ω)} ≤ ε ‖D^{k+1} u‖_{Lᵖ(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every `u ∈ W^{k+1,p}(Ω)`, where the
left side is the norm of the lower-order part `lowerOrder k u`. -/
theorem exists_norm_lowerOrder_le_of_isCompactOperator {k : ℕ}
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp mu Omega p (k + 1),
      ‖lowerOrder k u‖ ≤ ε * ‖iteratedGradient k u‖ + C * ‖value (k + 1) u‖ := by
  -- Ehrling's inequality with `ε / (1 + ε)`, then absorb the lower-order part of `‖u‖`.
  have hε' : 0 < ε / (1 + ε) := by positivity
  rw [← toOrderL_le_succ k (Nat.le_succ k)] at hK
  obtain ⟨C, hC, hle⟩ := exists_norm_toOrderL_le_of_isCompactOperator _ hK hε'
  refine ⟨(1 + ε) * C, by positivity, fun u ↦ ?_⟩
  have h1 := hle u
  rw [toOrderL_le_succ, lowerOrderL_apply] at h1
  have h2 := norm_le_norm_lowerOrder_add_norm_iteratedGradient k u
  have h3 : ε / (1 + ε) * (1 + ε) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith [norm_nonneg (lowerOrder k u), norm_nonneg (iteratedGradient k u),
    norm_nonneg (value (k + 1) u)]

/-- **The interpolation inequality from compactness.** If forgetting the highest weak derivative
`W^{k+2,p}(Ω) → W^{k+1,p}(Ω)` is compact, then for every `ε > 0` there is `C` with
`‖D^{k+1} u‖_{Lᵖ(Ω)} ≤ ε ‖D^{k+2} u‖_{Lᵖ(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every `u ∈ W^{k+2,p}(Ω)`.
At `k = 0` this is `‖∇u‖ ≤ ε ‖D²u‖ + C ‖u‖`. -/
theorem exists_norm_iteratedGradient_lowerOrder_le_of_isCompactOperator {k : ℕ}
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) (k + 1))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp mu Omega p (k + 2),
      ‖iteratedGradient k (lowerOrder (k + 1) u)‖ ≤
        ε * ‖iteratedGradient (k + 1) u‖ + C * ‖value (k + 2) u‖ := by
  obtain ⟨C, hC, hle⟩ := exists_norm_lowerOrder_le_of_isCompactOperator hK hε
  exact ⟨C, hC, fun u ↦ (norm_iteratedGradient_le k _).trans (hle u)⟩

/-- **Absorbing lower-order terms in an a priori estimate.** Suppose that forgetting the highest
weak derivative `W^{k+1,p}(Ω) → W^{k,p}(Ω)` is compact. If the top derivative of every
`u ∈ W^{k+1,p}(Ω)` satisfies `‖D^{k+1} u‖ ≤ C₀ (‖T u‖ + ‖u‖_{W^{k,p}})` for some map `T` into a
seminormed group, then there is `D` with `‖u‖_{W^{k+1,p}} ≤ D (‖T u‖ + ‖u‖_{Lᵖ})` for every `u`.
For a second-order operator `T`, this removes the terms `‖∇u‖` and `‖u‖` of the `W^{1,p}` norm
from an estimate `‖D²u‖ ≤ C₀ (‖T u‖ + ‖∇u‖ + ‖u‖)`, keeping only `‖u‖_{Lᵖ}`. -/
theorem exists_norm_le_of_norm_iteratedGradient_le_of_isCompactOperator {k : ℕ}
    (hK : IsCompactOperator (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k))
    {G : Type*} [SeminormedAddCommGroup G] {T : Wkp mu Omega p (k + 1) → G} {C₀ : ℝ}
    (hT : ∀ u, ‖iteratedGradient k u‖ ≤ C₀ * (‖T u‖ + ‖lowerOrder k u‖)) :
    ∃ D, 0 ≤ D ∧ ∀ u, ‖u‖ ≤ D * (‖T u‖ + ‖value (k + 1) u‖) := by
  -- The hypothesis also holds with the nonnegative constant `C = max C₀ 0`.
  set C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hinj : Function.Injective (valueL (mu := mu) (Omega := Omega) (p := p) k) :=
    fun u v huv ↦ ext k (by simpa only [valueL_apply] using huv)
  -- `‖u‖ ≤ C ‖T u‖ + (C + 1) ‖u‖_{W^{k,p}}`, where the last term is a compact operator applied to
  -- `u`, so its norm may be weakened to `‖u‖_{Lᵖ}`.
  have hnorm (u : Wkp mu Omega p (k + 1)) :
      ‖((C + 1) • lowerOrderL k) u‖ = (C + 1) * ‖lowerOrder k u‖ := by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity),
      lowerOrderL_apply]
  have hval (u : Wkp mu Omega p (k + 1)) :
      ‖valueL k (((C + 1) • lowerOrderL k) u)‖ = (C + 1) * ‖value (k + 1) u‖ := by
    rw [smul_apply, map_smul, norm_smul, Real.norm_of_nonneg (by positivity),
      valueL_apply, ← toOrderL_le_succ k (Nat.le_succ k), value_toOrderL]
  obtain ⟨A, hA, hle⟩ := (hK.smul (C + 1)).exists_norm_le_of_compact_estimate hinj (T := T)
    (C := C) fun u ↦ by
      have h2 := (hT u).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0)
        (add_nonneg (norm_nonneg (T u)) (norm_nonneg (lowerOrder k u))))
      rw [ContinuousLinearMap.coe_coe, hnorm]
      linarith [norm_le_norm_lowerOrder_add_norm_iteratedGradient k u]
  refine ⟨2 * C + A * (C + 1), by positivity, fun u ↦ ?_⟩
  have h := hle u
  rw [ContinuousLinearMap.coe_coe, hval] at h
  nlinarith [norm_nonneg (T u), norm_nonneg (value (k + 1) u), mul_nonneg hA hC]

end TauCeti.Wkp
