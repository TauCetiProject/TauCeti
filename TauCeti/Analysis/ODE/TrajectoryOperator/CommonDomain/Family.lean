/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Estimates for the trajectory operator of a family over a common domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be an essentially bounded, strongly measurable family of operators, given as
a class in `L∞(ℝ, D →L[ℝ] H)`. For instance `A(s)` can be an unbounded operator on `H`, such as
`J ∂ₜ + S(s, t)` acting on paths `t ↦ ξ(t)` with `D = H¹` and `H = L²`, which is bounded only as a
map from its domain `D`. The operator `u ↦ (ι ∘ u)' + A(s) u(s)` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is
`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι A`
(`TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain`); a constant coefficient `A₀` gives the
autonomous operator `TauCeti.WeakDerivStep.domainTrajectoryOperator ι A₀`.

On the whole line in `L²`, the autonomous operator of an invertible `ι`-symmetric `A₀`
(`⟪A₀ x, ι y⟫ = ⟪ι x, A₀ y⟫`) is invertible with inverse of norm at most
`M = √(1 + ‖A₀⁻¹‖²)`. Comparing with it gives the estimates for a coefficient that is close to
`A₀`, without any symmetry of `A(s)` itself:

* if `‖A(s) - A₀‖ ≤ δ` for almost every `s` in a set `S` and the path `u` vanishes off `S`, then
  `(1 - M δ) ‖u‖ ≤ M ‖(ι ∘ u)' + A u‖`
  (`TauCeti.WeakDerivStep.mul_norm_le_mul_norm_familyDomainTrajectoryOperator`);
* if `M ‖A - A₀‖_{L∞} < 1`, the operator is invertible, with inverse of norm at most
  `M / (1 - M ‖A - A₀‖_{L∞})`
  (`TauCeti.WeakDerivStep.isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt` and
  `TauCeti.WeakDerivStep.norm_inverse_familyDomainTrajectoryOperator_le`);
* if `A(s)` converges to an invertible `ι`-symmetric `B` as `s → ∞`, there are `C` and `T` with
  `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` for every path `u` vanishing on `(-∞, T)`
  (`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop`),
  and likewise at `-∞`.

The last estimate is the control of the ends in the Fredholm theory of `∂ₛ + A(s)` for a family
with invertible limits `A±`: after cutting a path off near the two ends, only a piece supported in a
bounded interval remains, which is where the compactness of `D → H` enters.

## Main declarations

* `TauCeti.WeakDerivStep.mul_norm_le_mul_norm_familyDomainTrajectoryOperator`: the estimate for
  paths supported where the coefficient is close to `A₀`.
* `TauCeti.WeakDerivStep.isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt`:
  invertibility near an invertible symmetric constant.
* `exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto`:
  the estimate for paths supported where `A` is near its limit along a filter, with the versions
  `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop`
  and `..._atBot` at the two ends.
* `TauCeti.WeakDerivStep.inner_apply_eq_inner_of_tendsto`: a limit of `ι`-symmetric operators is
  `ι`-symmetric.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

section Symmetric

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A₀ : D →L[ℝ] H}

omit [CompleteSpace D] in
/-- If `‖A(s) - A₀‖ ≤ δ` for almost every `s` in `S` and the path `u` vanishes almost everywhere
off `S`, the operators of `A` and of the constant `A₀` differ on `u` by at most `δ ‖u‖`. -/
private theorem norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le
    {A : Lp (D →L[ℝ] H) ∞ μ₀} {S : Set ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ᵐ s ∂volume, s ∈ S → ‖A s - A₀‖ ≤ δ)
    {u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hu : ∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) :
    ‖familyDomainTrajectoryOperator ι A u - domainTrajectoryOperator ι A₀ u‖ ≤ δ * ‖u‖ := by
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev (ι.compLpL 2 μ₀) u) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) hδ)
  filter_upwards [familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι A A₀ u,
    ae_restrict_of_ae hA, ae_restrict_of_ae hu] with s hM hAs hus
  rw [hM]
  by_cases hs : s ∈ S
  · exact ((A s - A₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAs hs) (norm_nonneg _))
  · rw [hus hs]; simp

/-- **Estimate near an invertible symmetric constant.** Let `A₀` be invertible and `ι`-symmetric,
and put `M = √(1 + ‖A₀⁻¹‖²)`. If `‖A(s) - A₀‖ ≤ δ` for almost every `s` in `S` and the path `u`
vanishes almost everywhere off `S`, then `(1 - M δ) ‖u‖ ≤ M ‖(ι ∘ u)' + A u‖` on `L²(ℝ)`. -/
theorem mul_norm_le_mul_norm_familyDomainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀} {S : Set ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ᵐ s ∂volume, s ∈ S → ‖A s - A₀‖ ≤ δ)
    {u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hu : ∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) :
    (1 - √(1 + ‖A₀.inverse‖ ^ 2) * δ) * ‖u‖ ≤
      √(1 + ‖A₀.inverse‖ ^ 2) * ‖familyDomainTrajectoryOperator ι A u‖ := by
  set M := √(1 + ‖A₀.inverse‖ ^ 2)
  have h₀ := norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hA₀ u
  have hdiff :=
    norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le (ι := ι) hδ hA hu
  have htri : ‖domainTrajectoryOperator ι A₀ u‖ ≤
      ‖familyDomainTrajectoryOperator ι A u‖ + δ * ‖u‖ := by
    have := norm_sub_le (familyDomainTrajectoryOperator ι A u)
      (familyDomainTrajectoryOperator ι A u - domainTrajectoryOperator ι A₀ u)
    rw [sub_sub_cancel] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg (1 + ‖A₀.inverse‖ ^ 2))]

/-- **Invertibility near an invertible symmetric constant.** If `A₀` is invertible and
`ι`-symmetric and `√(1 + ‖A₀⁻¹‖²) ‖A - A₀‖_{L∞} < 1`, then `u ↦ (ι ∘ u)' + A u` is invertible from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` onto `L²(ℝ, H)`. -/
theorem isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀}
    (h : √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖ < 1) :
    (familyDomainTrajectoryOperator (p := 2) ι A).IsInvertible := by
  have hle := norm_familyDomainTrajectoryOperator_sub_le (p := 2) ι A
    ((memLp_top_const (μ := μ₀) A₀).toLp _)
  rw [familyDomainTrajectoryOperator_toLp_const] at hle
  exact (isInvertible_domainTrajectoryOperator hSymm hA₀).of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀)
    ((mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)).trans_lt h)

/-- Under the hypotheses of
`isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt`, with
`M = √(1 + ‖A₀⁻¹‖²)`, the inverse of `u ↦ (ι ∘ u)' + A u` has norm at most
`M / (1 - M ‖A - A₀‖_{L∞})`. -/
theorem norm_inverse_familyDomainTrajectoryOperator_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀}
    (h : √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖ < 1) :
    ‖(familyDomainTrajectoryOperator (p := 2) ι A).inverse‖ ≤
      √(1 + ‖A₀.inverse‖ ^ 2) /
        (1 - √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖) := by
  have hle := norm_familyDomainTrajectoryOperator_sub_le (p := 2) ι A
    ((memLp_top_const (μ := μ₀) A₀).toLp _)
  rw [familyDomainTrajectoryOperator_toLp_const] at hle
  replace hle := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (1 + ‖A₀.inverse‖ ^ 2))
  refine ((isInvertible_domainTrajectoryOperator hSymm hA₀).norm_inverse_le_of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀) (lt_of_le_of_lt hle h)).trans ?_
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (sub_pos.2 h) (by linarith)

/-- **The estimate along a filter.** If `A(s)` converges along a filter `l` on `ℝ` to an invertible
`ι`-symmetric operator `A₀`, there are a set `S ∈ l` and a constant `C` with
`‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u` vanishing almost everywhere off `S`. -/
theorem exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) {l : Filter ℝ}
    (hA : Tendsto A l (𝓝 A₀)) :
    ∃ C : ℝ, ∃ S ∈ l, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  set M := √(1 + ‖A₀.inverse‖ ^ 2)
  have hM : 0 < M := Real.sqrt_pos.2 (by positivity)
  have hδ : 0 < (2 * M)⁻¹ := by positivity
  refine ⟨2 * M, {s | ‖A s - A₀‖ ≤ (2 * M)⁻¹},
    (hA.eventually (Metric.closedBall_mem_nhds A₀ hδ)).mono fun s hs ↦ by
      simpa [dist_eq_norm] using hs, fun u hu ↦ ?_⟩
  have hae : ae volume = ae μ₀ := by simp
  have hAs : ∀ᵐ s ∂volume, s ∈ {s | ‖A s - A₀‖ ≤ (2 * M)⁻¹} → ‖AL s - A₀‖ ≤ (2 * M)⁻¹ := by
    filter_upwards [hAL.filter_mono hae.le] with s hs h
    rwa [hs]
  have := mul_norm_le_mul_norm_familyDomainTrajectoryOperator hSymm hA₀ hδ.le hAs hu
  rw [show M * (2 * M)⁻¹ = 1 / 2 by field_simp] at this
  linarith

/-- **The estimate at `+∞`.** If `A(s)` converges as `s → ∞` to an invertible `ι`-symmetric
operator `B`, there are `C` and `T` with `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u`
vanishing almost everywhere on `(-∞, T)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
    {B : D →L[ℝ] H} (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hA : Tendsto A atTop (𝓝 B)) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s < T → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  obtain ⟨C, S, hS, hC⟩ :=
    exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto hSymm hB hAL hA
  obtain ⟨T, hT⟩ := mem_atTop_sets.1 hS
  exact ⟨C, T, fun u hu ↦ hC u (hu.mono fun s hs hsS ↦
    hs (lt_of_not_ge fun h ↦ hsS (hT s h)))⟩

/-- **The estimate at `-∞`.** If `A(s)` converges as `s → -∞` to an invertible `ι`-symmetric
operator `B`, there are `C` and `T` with `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u`
vanishing almost everywhere on `(T, ∞)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
    {B : D →L[ℝ] H} (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hA : Tendsto A atBot (𝓝 B)) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, T < s → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  obtain ⟨C, S, hS, hC⟩ :=
    exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto hSymm hB hAL hA
  obtain ⟨T, hT⟩ := mem_atBot_sets.1 hS
  exact ⟨C, T, fun u hu ↦ hC u (hu.mono fun s hs hsS ↦
    hs (lt_of_not_ge fun h ↦ hsS (hT s h)))⟩

omit [CompleteSpace D] [CompleteSpace H] in
/-- **A limit of `ι`-symmetric operators is `ι`-symmetric.** If `A s → B` along `l` and `A s` is
`ι`-symmetric (`⟪A s x, ι y⟫ = ⟪ι x, A s y⟫`) for `s` frequently along `l`, then `B` is
`ι`-symmetric. -/
theorem inner_apply_eq_inner_of_tendsto {α : Type*} {l : Filter α} {A : α → D →L[ℝ] H}
    {B : D →L[ℝ] H} (hSymm : ∃ᶠ s in l, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hA : Tendsto A l (𝓝 B)) (x y : D) :
    ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ := by
  have hx := ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto B).comp hA
  have hy := ((ContinuousLinearMap.apply ℝ H y).continuous.tendsto B).comp hA
  exact tendsto_nhds_unique_of_frequently_eq (hx.inner tendsto_const_nhds)
    (tendsto_const_nhds.inner hy) (hSymm.mono fun s hs ↦ hs x y)

end Symmetric

end TauCeti.WeakDerivStep
