/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Convex.Cone.InfDist
import TauCeti.Analysis.Distribution.TestFunction.DominatedSeries
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.LatticeSeries
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.NonstationaryPhase.Basic
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Continuity of changes of variables in the normal topology

Let `e` be a smooth change of variables of a finite-dimensional real inner product space `E`: a
smooth open partial homeomorphism with smooth inverse. A complex distribution `T` on an open set
`Ω` pulls back along `e` to the distribution `e^* T` on an open subset `U` of the source of `e`
mapped into `Ω` (`Distribution.compCLMOfOpenPartialHomeomorph`), and covectors pull back by the
transpose of the derivative (`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`). So for a
fixed set `Γ`, the distributions with wave front set in `Γ` are all sent into the fixed set

`e^* Γ = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ Γ}` (`TauCeti.covectorPullback`)

(`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph_subset`). This file proves that for a
closed cone `Γ` of nonzero covectors over `Ω` the pullback is continuous for the normal topologies
of Hörmander's spaces (`TauCeti.WaveFrontSpace.compCLMOfOpenPartialHomeomorph`):

`e^* : 𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{e^* Γ}(U)`.

This is the invariance of the normal topology under changes of coordinates, which makes the spaces
`𝓓'_Γ` and their topology well defined on manifolds, and it is the change-of-variables step of the
pullback along a smooth map.

## The estimates

Continuity into `𝓓'(U)` is that of the pullback itself. Let `‖·‖_{φ,V,N}` be a seminorm of the
target. Since the localized Fourier transform is additive in the cutoff, a partition of unity
reduces it to cutoffs `ψ` supported near a point `x₀` of `supp φ`. With `P = De(x₀)ᵀ`, the
closed cone `Γ` contains no covector over a neighbourhood of `e x₀` in a direction of the closed
cone `A = {η | dist (P η, V) ≤ ε ‖η‖}` for small `ε > 0`, by compactness.
Take a cutoff `χ` equal to one near `e x₀`, supported there, in a compact set meeting none of its
nonzero translates by a lattice `L`. The localized Fourier transform of `e^* T` is the lattice
series

`e^* T (ψ e_ξ) = ∑ m, (covolume L)⁻¹ a(ξ, m) T (χ e_(-m))`,

`a(ξ, m) = ∫ ψ(x) 𝐞(⟪e x, -m⟫ - ⟪x, ξ⟫) dx`

(`Distribution.hasSum_localFourier_compCLMOfOpenPartialHomeomorph`). The phase of `a(ξ, m)` has
gradient `-(De(x)ᵀ m + ξ)`. When `ψ` is supported where `De(x)ᵀ` is close to `P`, this gradient is
comparable to `‖m‖ + ‖ξ‖` for `ξ ∈ V` and `-m ∉ A`, and also whenever `‖ξ‖` is large compared with
`‖m‖`; there `a(ξ, m)` decays faster than every power of `1 + ‖m‖ + ‖ξ‖` by non-stationary
phase (`TauCeti.exists_one_add_norm_add_norm_pow_mul_norm_integral_mul_fourierChar_le`). Hence:

* the terms with `-m ∈ A` are controlled by the seminorms `‖T‖_{χ,A,M}` of the source, since
  `(1 + ‖ξ‖) ^ N ‖a(ξ, m)‖ ≤ C (1 + ‖m‖) ^ N` for all `ξ` and `m`;
* the terms with `-m ∉ A` sum to the pairing of `T` with the single test function
  `∑ m, (covolume L)⁻¹ a(ξ, m) χ e_(-m)` over these `m`. Weighted by `(1 + ‖ξ‖) ^ N`, these test
  functions depend continuously on `ξ ∈ V` and tend to zero at infinity, so together with `0` they
  form a compact set, on which `T` is bounded by a continuous seminorm of `𝓓'_Γ(Ω)`.

This good/bad splitting of the lattice series and the compactness argument follow the proof of
`TauCeti.WaveFrontSpace.pullbackInlCLM` (`NormalTopology/Pullback.lean`), with the coefficients
`a(ξ, m)` in place of `𝓕 ψ (ξ + m.fst)`; the domination and compactness of the weighted lattice
series are shared with it
(`ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate`).

## Main declarations

* `TauCeti.WaveFrontSpace.compCLMOfOpenPartialHomeomorph`: the pullback
  `e^* : 𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{e^* Γ}(U)`, continuous in the normal topologies.
* `TauCeti.WaveFrontSpace.toDistribution_compCLMOfOpenPartialHomeomorph`: it is
  `Distribution.compCLMOfOpenPartialHomeomorph`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the wave front set of a pullback and its sequential continuity on
  `𝓓'_Γ`) and Theorem 7.7.1 (non-stationary phase).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, §§3–5 (the normal topology and the continuity of pullbacks in it).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory Distribution
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff InnerProduct
  Pointwise Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace TauCeti

/-! ### The cone `A` of the source seminorms -/

section Cone

/-- The closed cone `{η | dist (P η, V) ≤ ε ‖η‖}` of the frequencies whose image under `P` lies
within relative distance `ε` of `V`. -/
private def nearCone (P : E →L[ℝ] E) (V : Set E) (ε : ℝ) : Set E :=
  {η | infDist (P η) V ≤ ε * ‖η‖}

omit [FiniteDimensional ℝ E] in
private theorem isClosed_nearCone (P : E →L[ℝ] E) (V : Set E) (ε : ℝ) :
    IsClosed (nearCone P V ε) :=
  isClosed_le ((continuous_infDist_pt V).comp P.continuous) (continuous_const.mul continuous_norm)

omit [FiniteDimensional ℝ E] in
private theorem smul_mem_nearCone (P : E →L[ℝ] E) {V : Set E}
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ε : ℝ} (t : ℝ) (ht : 0 < t)
    (η : E) (hη : η ∈ nearCone P V ε) : t • η ∈ nearCone P V ε := by
  simp only [nearCone, mem_ofPred_eq, map_smul, norm_smul, Real.norm_of_nonneg ht.le] at hη ⊢
  calc infDist (t • P η) V ≤ t * infDist (P η) V :=
        (infDist_smul_of_smul_mem hVcone ht _).le
    _ ≤ t * (ε * ‖η‖) := by gcongr
    _ = ε * (t * ‖η‖) := by ring

/-- Since `Γ` is a closed cone of nonzero covectors over `Ω`, if no covector `η` of `Γ` over `y₀`
has `P η` in the closed cone `V`, then no covector of `Γ` over a neighbourhood of `y₀` lies in the
cone `{η | dist (P η, V) ≤ ε ‖η‖}`, for small `ε > 0`. The function
`max (dist (y, y₀), dist (P η, V))` is positive on the compact set of unit covectors of `Γ` over
a closed ball around `y₀`, so it is bounded below there by some `κ > 0`. -/
private theorem exists_forall_notMem_of_infDist_le {Ω : Opens E} {Γ : Set (E × E)}
    (hΓ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {y₀ : E} (hy₀ : y₀ ∈ Ω) (P : E →L[ℝ] E) {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) (h : ∀ η, P η ∈ V → (y₀, η) ∉ Γ) :
    ∃ ε > 0, ∀ y, dist y y₀ < ε → ∀ η ∈ nearCone P V ε, (y, η) ∉ Γ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen y₀ hy₀
  set C : Set (E × E) := closedBall y₀ (r / 2) ×ˢ sphere (0 : E) 1
  have hCΩ : C ⊆ (Ω : Set E) ×ˢ {0}ᶜ := fun p hp ↦
    ⟨hrΩ (closedBall_subset_ball (half_lt_self hr) hp.1),
      ne_zero_of_mem_unit_sphere (⟨p.2, hp.2⟩ : sphere (0 : E) 1)⟩
  -- The unit covectors of `Γ` over `closedBall y₀ (r / 2)` form a compact set `S`.
  set S := C \ (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ)
  have hS : IsCompact S := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).diff hΓ
  set k : E × E → ℝ := fun p ↦ max (dist p.1 y₀) (infDist (P p.2) V)
  have hk : Continuous k := (continuous_fst.dist continuous_const).max
    ((continuous_infDist_pt V).comp (P.continuous.comp continuous_snd))
  have hkpos : ∀ p ∈ S, 0 < k p := by
    rintro ⟨y, η⟩ ⟨hpC, hpΓ⟩
    have hΓ' : (y, η) ∈ Γ := by
      by_contra hn
      exact hpΓ ⟨hCΩ hpC, hn⟩
    by_contra hle
    push Not at hle
    have hy : y = y₀ := dist_le_zero.1 ((le_max_left _ _).trans hle)
    have hPη : P η ∈ V := (hV.mem_iff_infDist_zero ⟨0, hV0⟩).2
      (le_antisymm ((le_max_right _ _).trans hle) infDist_nonneg)
    exact h η hPη (hy ▸ hΓ')
  obtain ⟨κ, hκ, hκS⟩ : ∃ κ > 0, ∀ p ∈ S, κ ≤ k p := by
    rcases S.eq_empty_or_nonempty with hS0 | hS0
    · exact ⟨1, one_pos, by simp [hS0]⟩
    · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hS0 hk.continuousOn
      exact ⟨k p, hkpos p hp, fun q hq ↦ hmin hq⟩
  refine ⟨min (r / 2) κ / 2, by positivity, fun y hy η hη hyη ↦ ?_⟩
  -- Rescale `η` to the unit sphere: `(y, η / ‖η‖)` lies in `S` but `k` is less than `κ` there.
  have hηpos : 0 < ‖η‖ := norm_pos_iff.2 (hΓ0 _ hyη)
  set t := ‖η‖⁻¹
  have ht : 0 < t := inv_pos.2 hηpos
  have hmem : (y, t • η) ∈ S := by
    refine ⟨⟨?_, ?_⟩, fun h' ↦ h'.2 (hcone _ hyη t ht)⟩
    · rw [mem_closedBall]
      linarith [min_le_left (r / 2) κ]
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg ht.le,
        inv_mul_cancel₀ hηpos.ne']
  have h2 : infDist (P (t • η)) V < κ := by
    rw [map_smul]
    calc infDist (t • P η) V ≤ t * infDist (P η) V :=
          (infDist_smul_of_smul_mem hVcone ht _).le
      _ ≤ t * (min (r / 2) κ / 2 * ‖η‖) := by gcongr; exact hη
      _ = min (r / 2) κ / 2 := by rw [mul_left_comm, inv_mul_cancel₀ hηpos.ne', mul_one]
      _ < κ := by linarith [min_le_right (r / 2) κ]
  exact absurd (hκS _ hmem) (not_le.2 (max_lt (by linarith [min_le_right (r / 2) κ]) h2))

end Cone

/-! ### Non-stationary phase for the coefficients -/

section Coefficient

variable [MeasurableSpace E] [BorelSpace E]

/-- The coefficient `a(ξ, m) = ∫ ψ(x) 𝐞(-(⟪g x, m⟫ + ⟪x, ξ⟫)) dx` of the lattice series of the
pullback, for a smooth map `g` agreeing with the change of variables on the support of `ψ`. -/
private def coeff (ψ : E → ℂ) (g : E → E) (ξ m : E) : ℂ :=
  ∫ x, ψ x * 𝐞 (-(⟪g x, m⟫ + ⟪x, ξ⟫))

private theorem norm_coeff_le (ψ : E → ℂ) (g : E → E) (ξ m : E) :
    ‖coeff ψ g ξ m‖ ≤ ∫ x, ‖ψ x‖ :=
  (norm_integral_le_integral_norm _).trans_eq (by simp)

/-- The coefficients depend continuously on the frequency `ξ`. -/
private theorem continuous_coeff {ψ : E → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {g : E → E} (hg : Continuous g) (m : E) : Continuous fun ξ ↦ coeff ψ g ξ m := by
  refine continuous_of_dominated (bound := fun x ↦ ‖ψ x‖) (fun ξ ↦ ?_) (fun ξ ↦ ?_)
    (hψ.norm.integrable_of_hasCompactSupport hψc.norm) (ae_of_all _ fun x ↦ ?_)
  · exact (hψ.mul (Real.continuous_fourierChar.comp (((hg.inner continuous_const).add
      (continuous_id.inner continuous_const)).neg)).subtypeVal).aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ by simp
  · exact continuous_const.mul (Real.continuous_fourierChar.comp
      ((continuous_const.add (continuous_const.inner continuous_id)).neg)).subtypeVal

/-- **The coefficients off the cone, and at large frequencies.** Let `De(x)ᵀ = Dg(x)ᵀ` stay within
`ε / 2` of `P` and below `M₁ ≥ 1` in norm on the support of `ψ`. If `ξ ∈ V` and `-m` lies outside
the cone `{η | dist (P η, V) ≤ ε ‖η‖}`, or if `2 M₁ ‖m‖ ≤ ‖ξ‖`, the gradient `Dg(x)ᵀ m + ξ` of the
phase of `a(ξ, m)` is comparable to `‖m‖ + ‖ξ‖`, so `a(ξ, m)` decays faster than every power of
`1 + ‖m‖ + ‖ξ‖`. -/
private theorem exists_one_add_norm_pow_mul_norm_coeff_le {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {g : E → E} (hg : ContDiff ℝ ∞ g) {P : E →L[ℝ] E} {V : Set E}
    {ε M₁ : ℝ} (hε : 0 < ε) (hM₁ : 1 ≤ M₁)
    (hgP : ∀ x ∈ tsupport ψ, ‖(fderiv ℝ g x)† - P‖ ≤ ε / 2)
    (hgM : ∀ x ∈ tsupport ψ, ‖fderiv ℝ g x‖ ≤ M₁) (M : ℕ) :
    ∃ C, ∀ m ξ : E, (ξ ∈ V ∧ infDist (P (-m)) V > ε * ‖-m‖) ∨ 2 * M₁ * ‖m‖ ≤ ‖ξ‖ →
      (1 + ‖m‖ + ‖ξ‖) ^ M * ‖coeff ψ g ξ m‖ ≤ C := by
  set c := min (1 / 3) (ε / (2 * (2 * M₁ + ε)))
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  obtain ⟨C, hC⟩ :=
    exists_one_add_norm_add_norm_pow_mul_norm_integral_mul_fourierChar_le volume hψ hψc hg hc M
  refine ⟨C, fun m ξ h ↦ hC m ξ fun x hx ↦ ?_⟩
  set D := (fderiv ℝ g x)†
  set s := ‖D m + ξ‖
  have hDm : ‖D m‖ ≤ M₁ * ‖m‖ :=
    (D.le_opNorm m).trans (by rw [LinearIsometryEquiv.norm_map]; gcongr; exact hgM x hx)
  -- The gradient is at least `‖ξ‖ - M₁ ‖m‖`.
  have hlow : ‖ξ‖ - M₁ * ‖m‖ ≤ s := by
    have : ‖ξ‖ ≤ ‖D m + ξ‖ + ‖D m‖ :=
      calc ‖ξ‖ = ‖(D m + ξ) - D m‖ := by rw [add_sub_cancel_left]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hm0 := norm_nonneg m
  have hs0 := norm_nonneg (D m + ξ)
  rcases h with ⟨hξ, hm⟩ | hξm
  · -- `‖P m + ξ‖ > ε ‖m‖`, and `D` is within `ε / 2` of `P`, so the gradient is `≥ ε / 2 ‖m‖`.
    have h1 : ε * ‖m‖ < ‖P m + ξ‖ :=
      calc ε * ‖m‖ = ε * ‖-m‖ := by rw [norm_neg]
        _ < infDist (P (-m)) V := hm
        _ ≤ dist (P (-m)) ξ := infDist_le_dist_of_mem hξ
        _ = ‖P m + ξ‖ := by rw [dist_eq_norm, map_neg, ← norm_neg]; congr 1; abel
    have h2 : ‖(D - P) m‖ ≤ ε / 2 * ‖m‖ :=
      ((D - P).le_opNorm m).trans (by gcongr; exact hgP x hx)
    have h3 : ‖P m + ξ‖ ≤ s + ‖(D - P) m‖ :=
      calc ‖P m + ξ‖ = ‖(D m + ξ) - (D - P) m‖ := by
            congr 1
            simp only [FunLike.coe_sub, Pi.sub_apply]
            abel
        _ ≤ _ := norm_sub_le _ _
    have hs1 : ε / 2 * ‖m‖ ≤ s := by linarith
    calc c * (‖m‖ + ‖ξ‖) ≤ ε / (2 * (2 * M₁ + ε)) * (‖m‖ + ‖ξ‖) := by
          gcongr; exact min_le_right _ _
      _ ≤ s := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have k1 : ε * (‖ξ‖ - M₁ * ‖m‖) ≤ ε * s := mul_le_mul_of_nonneg_left hlow hε.le
          have k2 : M₁ * (ε / 2 * ‖m‖) ≤ M₁ * s := mul_le_mul_of_nonneg_left hs1 (by linarith)
          have k3 : 0 ≤ (2 * M₁ + ε - 2) * s := mul_nonneg (by linarith) hs0
          nlinarith
  · -- `‖ξ‖ ≥ 2 M₁ ‖m‖`, so the gradient is at least `‖ξ‖ / 2 ≥ (‖m‖ + ‖ξ‖) / 3`.
    have k : 2 * ‖m‖ ≤ 2 * M₁ * ‖m‖ := by nlinarith
    calc c * (‖m‖ + ‖ξ‖) ≤ 1 / 3 * (‖m‖ + ‖ξ‖) := by gcongr; exact min_le_left _ _
      _ ≤ s := by nlinarith

/-- **The coefficients at all frequencies.** Under the hypotheses of
`exists_one_add_norm_pow_mul_norm_coeff_le`, `(1 + ‖ξ‖) ^ N ‖a(ξ, m)‖ ≤ C (1 + ‖m‖) ^ N` for all
`ξ` and `m`: when `‖ξ‖ < 2 M₁ ‖m‖` the weight `1 + ‖ξ‖` is at most `(1 + 2 M₁) (1 + ‖m‖)`, and
otherwise the phase is non-stationary. -/
private theorem exists_one_add_norm_pow_mul_norm_coeff_le_mul {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {g : E → E} (hg : ContDiff ℝ ∞ g) {P : E →L[ℝ] E}
    {ε M₁ : ℝ} (hε : 0 < ε) (hM₁ : 1 ≤ M₁)
    (hgP : ∀ x ∈ tsupport ψ, ‖(fderiv ℝ g x)† - P‖ ≤ ε / 2)
    (hgM : ∀ x ∈ tsupport ψ, ‖fderiv ℝ g x‖ ≤ M₁) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ m ξ : E, (1 + ‖ξ‖) ^ N * ‖coeff ψ g ξ m‖ ≤ C * (1 + ‖m‖) ^ N := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_coeff_le (V := ∅) hψ hψc hg hε hM₁ hgP hgM N
  set I := ∫ x, ‖ψ x‖
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨max C 0 + (1 + 2 * M₁) ^ N * I, by positivity, fun m ξ ↦ ?_⟩
  have h1 : 1 ≤ (1 + ‖m‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg m])
  rcases le_or_gt (2 * M₁ * ‖m‖) ‖ξ‖ with hξm | hξm
  · calc (1 + ‖ξ‖) ^ N * ‖coeff ψ g ξ m‖ ≤ (1 + ‖m‖ + ‖ξ‖) ^ N * ‖coeff ψ g ξ m‖ := by
          gcongr; linarith [norm_nonneg m]
      _ ≤ max C 0 := (hC m ξ (Or.inr hξm)).trans (le_max_left _ _)
      _ ≤ max C 0 * (1 + ‖m‖) ^ N := le_mul_of_one_le_right (le_max_right _ _) h1
      _ ≤ _ := by gcongr; nlinarith [norm_nonneg m, pow_nonneg (by positivity : (0 : ℝ) ≤
            (1 + 2 * M₁)) N]
  · have hw : 1 + ‖ξ‖ ≤ (1 + 2 * M₁) * (1 + ‖m‖) := by nlinarith [norm_nonneg m]
    calc (1 + ‖ξ‖) ^ N * ‖coeff ψ g ξ m‖ ≤ ((1 + 2 * M₁) * (1 + ‖m‖)) ^ N * I := by
          gcongr
          exact norm_coeff_le ψ g ξ m
      _ = (1 + 2 * M₁) ^ N * I * (1 + ‖m‖) ^ N := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (le_max_right _ _)

end Coefficient

/-! ### The terms of the lattice series off the cone

The coefficients off the cone, `badCoeff`, adapt the private helper of the same name in
`NormalTopology/Pullback.lean` to coefficients `a(ξ, m)` that are not translates of one function.
The domination and compactness of their weighted lattice series are the shared
`ContDiffMapSupportedIn.exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le` and
`ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate`. -/

section Series

variable [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E}

/-- The coefficients `(covolume L)⁻¹ a(ξ, m)` of the lattice series, for the `m` with `-m ∉ A`. -/
private def badCoeff (L : Submodule ℤ E) (A : Set E) (a : E → E → ℂ) (ξ : E)
    (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : E) ∉ A}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * a ξ m) m

/-- If `a(ξ, m)` decays rapidly in `1 + ‖m‖ + ‖ξ‖` for `ξ ∈ V` and `-m ∉ A`, the coefficients off
`A` decay rapidly in `1 + ‖ξ‖ + ‖m‖` for `ξ ∈ V` and all `m`. -/
private theorem exists_one_add_add_pow_mul_norm_badCoeff_le {A V : Set E} {a : E → E → ℂ}
    (ha : ∀ M : ℕ, ∃ C, ∀ m ξ : E, ξ ∈ V → -m ∉ A → (1 + ‖m‖ + ‖ξ‖) ^ M * ‖a ξ m‖ ≤ C) (M : ℕ) :
    ∃ C, ∀ (ξ : V) (m : ZLattice.dual L),
      (1 + ‖(ξ : E)‖ + ‖(m : E)‖) ^ M * ‖badCoeff L A a ξ m‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha M
  refine ⟨‖(ZLattice.covolume L : ℂ)⁻¹‖ * max C 0, fun ξ m ↦ ?_⟩
  by_cases hm : -(m : E) ∈ A
  · simp only [badCoeff, indicator_of_notMem (s := {m : ZLattice.dual L | -(m : E) ∉ A})
      (by simpa using hm), norm_zero, mul_zero]
    positivity
  rw [badCoeff, indicator_of_mem (s := {m : ZLattice.dual L | -(m : E) ∉ A}) hm, norm_mul,
    add_right_comm, mul_left_comm]
  gcongr
  exact (hC m ξ ξ.property hm).trans (le_max_left _ _)

/-- The coefficients off `A` depend continuously on `ξ` when `a(ξ, m)` does. -/
private theorem continuous_badCoeff {A : Set E} {a : E → E → ℂ}
    (hac : ∀ m, Continuous fun ξ ↦ a ξ m) (m : ZLattice.dual L) :
    Continuous fun ξ ↦ badCoeff L A a ξ m := by
  by_cases hm : -(m : E) ∈ A
  · simp only [badCoeff, mem_ofPred_eq, hm, not_true_eq_false, not_false_eq_true,
      indicator_of_notMem]
    exact continuous_const
  · simp only [badCoeff, indicator_of_mem (s := {m : ZLattice.dual L | -(m : E) ∉ A}) hm]
    exact continuous_const.mul (hac m)

end Series

/-! ### The seminorm estimates -/

namespace WaveFrontSpace

variable {e : OpenPartialHomeomorph E E} {U Ω : Opens E} {Γ : Set (E × E)}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A term of the lattice series in the cone: if `w ‖a‖ ≤ C₁ (1 + t) ^ N` and
`(1 + t) ^ (N + q) ‖F‖ ≤ S`, then `c ‖a‖ ‖F‖ ≤ c C₁ S w⁻¹ ((1 + t) ^ q)⁻¹`. -/
private theorem mul_mul_le_of_le {w t α β c C₁ S : ℝ} {N q : ℕ} (hw : 0 < w) (ht : 0 ≤ t)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c) (h1 : w * α ≤ C₁ * (1 + t) ^ N)
    (h2 : (1 + t) ^ (N + q) * β ≤ S) :
    c * α * β ≤ c * C₁ * S * w⁻¹ * ((1 + t) ^ q)⁻¹ := by
  have key : (w * α) * ((1 + t) ^ (N + q) * β) ≤ (C₁ * (1 + t) ^ N) * S :=
    mul_le_mul h1 h2 (by positivity) ((mul_nonneg hw.le hα).trans h1)
  calc c * α * β = c * ((w * α) * ((1 + t) ^ (N + q) * β)) *
        (w⁻¹ * ((1 + t) ^ N)⁻¹ * ((1 + t) ^ q)⁻¹) := by
        rw [pow_add]; field_simp
    _ ≤ c * ((C₁ * (1 + t) ^ N) * S) * (w⁻¹ * ((1 + t) ^ N)⁻¹ * ((1 + t) ^ q)⁻¹) := by gcongr
    _ = c * C₁ * S * w⁻¹ * ((1 + t) ^ q)⁻¹ := by field_simp

/-- **The lattice series of the pullback**, with the coefficients `a(ξ, m)` written with a smooth
`g` agreeing with `e` on the support of `ψ`
(`Distribution.hasSum_localFourier_compCLMOfOpenPartialHomeomorph`). -/
private theorem hasSum_coeff_mul_localFourier (T : 𝓓'(Ω, ℂ)) {ψ : 𝓓(U, ℂ)} {g : E → E}
    (hge : ∀ x ∈ tsupport ψ, g x = e x) {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω)
    {χ : 𝓓_{K}(E, ℂ)} (hχ : ∀ x ∈ tsupport ψ, χ (e x) = 1) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0) (ξ : E) :
    HasSum (fun m : ZLattice.dual L ↦ ((ZLattice.covolume L : ℂ)⁻¹ * coeff (ψ : E → ℂ) g ξ m) *
        T.localFourier (ofSupportedIn hKΩ χ) (-(m : E)))
      ((Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier ψ ξ) := by
  refine (hasSum_localFourier_compCLMOfOpenPartialHomeomorph (he := he) (he' := he')
    (hU := hU) (hUΩ := hUΩ) T hKΩ L hL hχ ξ).congr_fun fun m ↦ ?_
  simp only [smul_eq_mul, coeff]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : ψ x = 0
  · simp [hx]
  dsimp only
  rw [hge x (subset_tsupport _ hx), inner_neg_right]
  congr 3
  ring

/-- **The terms off the cone sum to a pairing.** The terms `badCoeff ξ m · T (χ e_(-m))` of the
lattice series sum to the pairing of `T` with the series of the modulated cutoffs `χ e_(-m)`. -/
private theorem hasSum_badCoeff_mul_localFourier (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) (χ : 𝓓_{K}(E, ℂ)) {L : Submodule ℤ E} {A : Set E} {a : E → E → ℂ}
    {ξ : E} (hbs : Summable fun m ↦ badCoeff L A a ξ m • χ.modulate (m : E)) :
    HasSum (fun m : ZLattice.dual L ↦ badCoeff L A a ξ m *
        T.localFourier (ofSupportedIn hKΩ χ) (-(m : E)))
      (T.complexPairing (ofSupportedIn hKΩ (∑' m, badCoeff L A a ξ m • χ.modulate (m : E)))) := by
  refine ((T.complexPairing.comp (ofSupportedInCLM ℂ hKΩ)).hasSum hbs.hasSum).congr_fun
    fun m ↦ ?_
  rw [ContinuousLinearMap.comp_apply, map_smul, map_smul, smul_eq_mul, coe_ofSupportedInCLM,
    localFourier_eq_complexPairing_modulate T hKΩ (f := χ) (fun x ↦ rfl), neg_neg]

/-- **The bound at one frequency.** Split the lattice series of `e^* T (ψ e_ξ)` into the terms with
`-m ∈ A` and the others. If the coefficients satisfy `(1 + ‖ξ‖) ^ N ‖a(ξ, m)‖ ≤ C₁ (1 + ‖m‖) ^ N`,
`T (χ e_(-m))` decays to order `N + q` with constant `S` for `-m ∈ A`, and the pairing of `T` with
the weighted series of the other terms is at most `P'`, then
`(1 + ‖ξ‖) ^ N ‖e^* T (ψ e_ξ)‖ ≤ ‖(covolume L)⁻¹‖ C₁ (∑ m, (1 + ‖m‖)^(-q)) S + P'`. -/
private theorem one_add_pow_mul_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) {ψ : 𝓓(U, ℂ)} {g : E → E}
    (hge : ∀ x ∈ tsupport ψ, g x = e x) {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω)
    {χ : 𝓓_{K}(E, ℂ)} (hχ : ∀ x ∈ tsupport ψ, χ (e x) = 1) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0)
    {A : Set E} {N q : ℕ} (hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : E)‖) ^ q)⁻¹)
    {C₁ S P' : ℝ} (hC₁0 : 0 ≤ C₁) (hS0 : 0 ≤ S) {ξ : E}
    (hC₁ : ∀ m : E, (1 + ‖ξ‖) ^ N * ‖coeff (ψ : E → ℂ) g ξ m‖ ≤ C₁ * (1 + ‖m‖) ^ N)
    (hS : ∀ m : E, -m ∈ A →
      (1 + ‖m‖) ^ (N + q) * ‖T.localFourier (ofSupportedIn hKΩ χ) (-m)‖ ≤ S)
    (hbs : Summable fun m ↦ badCoeff L A (coeff (ψ : E → ℂ) g) ξ m • χ.modulate (m : E))
    (hP' : ‖T.complexPairing (ofSupportedIn hKΩ (∑' m : ZLattice.dual L,
      ((((1 + ‖ξ‖) ^ N : ℝ) : ℂ) * badCoeff L A (coeff (ψ : E → ℂ) g) ξ m) •
        χ.modulate (m : E)))‖ ≤ P') :
    (1 + ‖ξ‖) ^ N * ‖(Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier
      ψ ξ‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C₁ *
        (∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ q)⁻¹) * S + P' := by
  set a := coeff (ψ : E → ℂ) g
  set cL : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set F := T.localFourier (ofSupportedIn hKΩ χ)
  set w : ℝ := (1 + ‖ξ‖) ^ N
  have hw : 0 < w := by positivity
  -- The terms with `-m ∈ A`.
  set good : ZLattice.dual L → ℂ := {m : ZLattice.dual L | -(m : E) ∈ A}.indicator
    fun m ↦ (cL * a ξ m) * F (-(m : E))
  have hgood (m : ZLattice.dual L) :
      ‖good m‖ ≤ ‖cL‖ * C₁ * S * w⁻¹ * ((1 + ‖(m : E)‖) ^ q)⁻¹ := by
    by_cases hm : -(m : E) ∈ A
    · simpa only [good, indicator_of_mem (s := {m : ZLattice.dual L | -(m : E) ∈ A}) hm,
        norm_mul] using mul_mul_le_of_le hw (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) (hC₁ (m : E)) (hS _ hm)
    · simp only [good, indicator_of_notMem (s := {m : ZLattice.dual L | -(m : E) ∈ A}) hm,
        norm_zero]
      positivity
  have hgs : Summable good := Summable.of_norm_bounded (hq.mul_left _) hgood
  have hsplit := (hasSum_coeff_mul_localFourier (he := he) (he' := he') (hU := hU)
    (hUΩ := hUΩ) T hge hKΩ hχ L hL ξ).unique ((hgs.hasSum.add
      (hasSum_badCoeff_mul_localFourier T hKΩ χ hbs)).congr_fun fun m ↦ by
        by_cases hm : -(m : E) ∈ A
        · simp [good, badCoeff, hm, a, cL, F]
        · simp [good, badCoeff, hm, mul_assoc, cL, a])
  have h1 : w * ‖∑' m, good m‖ ≤
      ‖cL‖ * C₁ * (∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ q)⁻¹) * S := by
    have := tsum_of_norm_bounded (hq.hasSum.mul_left (‖cL‖ * C₁ * S * w⁻¹)) hgood
    calc w * ‖∑' m, good m‖ ≤ w * (‖cL‖ * C₁ * S * w⁻¹ *
          ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ q)⁻¹) := by gcongr
      _ = _ := by field_simp
  rw [← mul_norm_complexPairing_tsum_smul T hKΩ hw.le hbs] at hP'
  rw [hsplit]
  calc w * ‖∑' m, good m + T.complexPairing (ofSupportedIn hKΩ
        (∑' m, badCoeff L A a ξ m • χ.modulate (m : E)))‖
      ≤ w * ‖∑' m, good m‖ + w * ‖T.complexPairing (ofSupportedIn hKΩ
          (∑' m, badCoeff L A a ξ m • χ.modulate (m : E)))‖ := by
        rw [← mul_add]; gcongr; exact norm_add_le _ _
    _ ≤ _ := add_le_add h1 hP'

/-- **The estimate for a cutoff near a point.** Let `ψ` be a cutoff on whose support a smooth `g`
agrees with `e`, `Dg(x)ᵀ` stays within `ε / 2` of `P` and `‖Dg(x)‖ ≤ M₁`, and let `χ` be a
cutoff equal to one on `e (supp ψ)`, supported in a compact set `K` meeting none of its nonzero
translates by a lattice `L`, over which `Γ` has no covector in the cone
`A = {η | dist (P η, V) ≤ ε ‖η‖}`. Then `(1 + ‖ξ‖) ^ N ‖e^* T (ψ e_ξ)‖ ≤ p T` for `ξ ∈ V`, for a
continuous seminorm `p` of `𝓓'_Γ(Ω)`: the terms of the lattice series with `-m ∈ A` are bounded
through the seminorm `‖T‖_{χ,A,N+q}`, and the others sum to the pairing of `T` with a test
function lying, after weighting, in a fixed compact set. -/
private theorem exists_seminorm_localFourier_le_of_cutoff
    {V : Set E} (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    {ψ : 𝓓(U, ℂ)} {g : E → E} (hg : ContDiff ℝ ∞ g) (hge : ∀ x ∈ tsupport ψ, g x = e x)
    {P : E →L[ℝ] E} {ε M₁ : ℝ} (hε : 0 < ε) (hM₁ : 1 ≤ M₁)
    (hgP : ∀ x ∈ tsupport ψ, ‖(fderiv ℝ g x)† - P‖ ≤ ε / 2)
    (hgM : ∀ x ∈ tsupport ψ, ‖fderiv ℝ g x‖ ≤ M₁)
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) {χ : 𝓓_{K}(E, ℂ)}
    (hχ : ∀ x ∈ tsupport ψ, χ (e x) = 1) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hL : ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0)
    (hKΓ : Disjoint ((K : Set E) ×ˢ nearCone P V ε) Γ) (N : ℕ) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ, ∀ ξ ∈ V,
      (1 + ‖ξ‖) ^ N * ‖(Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ
        u.toDistribution).localFourier ψ ξ‖ ≤ p u := by
  set A := nearCone P V ε
  -- The seminorm data `(χ, A, M)` of the source.
  let i (M : ℕ) : WaveFrontSeminormIndex Ω Γ :=
    { cutoff := ofSupportedIn hKΩ χ, cone := A, order := M,
      isClosed_cone := isClosed_nearCone P V ε, smul_mem_cone := smul_mem_nearCone P hVcone,
      disjoint := hKΓ.mono_left (prod_mono χ.tsupport_subset subset_rfl) }
  -- The decay of the coefficients, and the compact set of weighted series off `A`.
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_one_add_norm_pow_mul_norm_coeff_le_mul ψ.contDiff
    ψ.hasCompactSupport hg hε hM₁ hgP hgM N
  have ha (M : ℕ) : ∃ C, ∀ m ξ : E, ξ ∈ V → -m ∉ A →
      (1 + ‖m‖ + ‖ξ‖) ^ M * ‖coeff (ψ : E → ℂ) g ξ m‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_coeff_le (V := V) ψ.contDiff
      ψ.hasCompactSupport hg hε hM₁ hgP hgM M
    exact ⟨C, fun m ξ hξ hm ↦ hC m ξ (Or.inl ⟨hξ, not_le.1 hm⟩)⟩
  have ha' := exists_one_add_add_pow_mul_norm_badCoeff_le (L := L) ha
  obtain ⟨p', hp', hp'le⟩ := exists_continuous_seminorm_norm_complexPairing_le (Γ := Γ)
    ((ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate
      (ZLattice.dual L) (w := fun ξ : V ↦ ‖(ξ : E)‖)
      (a := fun ξ m ↦ badCoeff L A (coeff (ψ : E → ℂ) g) ξ m) (fun _ ↦ norm_nonneg _)
      (continuous_norm.comp continuous_subtypeVal)
      (tendsto_norm_cocompact_atTop.comp hV.isClosedEmbedding_subtypeVal.tendsto_cocompact)
      (fun m ↦ (continuous_badCoeff (continuous_coeff ψ.continuous ψ.hasCompactSupport
        hg.continuous) m).comp continuous_subtypeVal) ha' χ N).image
          (continuous_ofSupportedIn hKΩ))
  obtain ⟨b, hb, -, hbound⟩ :=
    ContDiffMapSupportedIn.exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le
      (ZLattice.dual L) (w := fun ξ : V ↦ ‖(ξ : E)‖) (fun _ ↦ norm_nonneg _) ha' χ 0
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  set K₀ : ℝ := ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C₁ *
    ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ q)⁻¹
  have hK₀ : 0 ≤ K₀ := mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ by positivity)
  refine ⟨K₀.toNNReal • WaveFrontSpace.seminorm (i (N + q)) + p',
    ((continuous_seminorm _).const_smul _).add hp', fun u ξ hξ ↦ ?_⟩
  have h := one_add_pow_mul_norm_localFourier_le (he := he) (he' := he') (hU := hU)
    (hUΩ := hUΩ) u.toDistribution hge hKΩ hχ L hL hq hC₁0 (apply_nonneg _ u) (hC₁ · ξ)
    (fun m hm ↦ by simpa using le_seminorm (i (N + q)) u (η := -m) hm)
    (ContDiffMapSupportedIn.summable_smul_of_le hb fun k m ↦ by simpa using hbound ⟨ξ, hξ⟩ k m)
    (hp'le u _ (mem_image_of_mem _ (mem_insert_of_mem _ ⟨⟨ξ, hξ⟩, rfl⟩)))
  refine h.trans_eq ?_
  simp only [add_apply, smul_apply, NNReal.smul_def, Real.coe_toNNReal _ hK₀,
    smul_eq_mul, K₀]

/-- **The estimate near a point.** If no covector of `e^* Γ` over `x₀ ∈ U` lies in the closed cone
`V`, then for every cutoff `ψ` supported in a suitable neighbourhood of `x₀`,
`(1 + ‖ξ‖) ^ N ‖e^* T (ψ e_ξ)‖ ≤ p T` for `ξ ∈ V`, for a continuous seminorm `p` of `𝓓'_Γ(Ω)`.
With `P = De(x₀)ᵀ`, the neighbourhood is where `e` agrees with a smooth `g`, where `e` maps into
the region on which the cutoff `χ` is one, and where `Dg` stays within `ε / 2` of `De(x₀)`. -/
private theorem exists_mem_nhds_forall_exists_seminorm_le
    (hΓ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hx₀V : ∀ ξ ∈ V, (x₀, ξ) ∉ covectorPullback e U Γ) (N : ℕ) :
    ∃ O ∈ 𝓝 x₀, ∀ ψ : 𝓓(U, ℂ), tsupport ψ ⊆ O →
      ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ, ∀ ξ ∈ V,
        (1 + ‖ξ‖) ^ N * ‖(compCLMOfOpenPartialHomeomorph e he he' hU hUΩ
          u.toDistribution).localFourier ψ ξ‖ ≤ p u := by
  have hx₀s : x₀ ∈ e.source := hU hx₀
  have hy₀ : e x₀ ∈ Ω := hUΩ hx₀
  -- No covector of `Γ` near `e x₀` lies in the cone `{η | dist (De(x₀)ᵀ η, V) ≤ ε ‖η‖}`.
  obtain ⟨ε, hε, hεΓ⟩ := exists_forall_notMem_of_infDist_le hΓ hcone hΓ0 hy₀
    ((fderiv ℝ e x₀)†) hV hV0 hVcone fun η hη hΓη ↦
      hx₀V _ hη (mem_covectorPullback.2 ⟨hx₀, η, hΓη, rfl⟩)
  -- A smooth `g` equal to `e` near `x₀`.
  obtain ⟨g, hg, -, hge⟩ :=
    he.exists_contDiff_eventuallyEq_of_finiteDimensional (e.open_source.mem_nhds hx₀s)
  have hgx₀ : fderiv ℝ g x₀ = fderiv ℝ e x₀ := hge.fderiv_eq
  -- A compact set `K ⊆ Ω` within `ε` of `e x₀`, a cutoff equal to one near `e x₀`, a lattice.
  obtain ⟨K, K₁, hKsub, hK₁, -, ⟨χ, hχ⟩, L, _, _, hL⟩ :=
    ContDiffMapSupportedIn.exists_compacts_cutoff_lattice
      (inter_mem (ball_mem_nhds (e x₀) hε) (Ω.isOpen.mem_nhds hy₀))
  have hKΓ : Disjoint ((K : Set E) ×ˢ nearCone ((fderiv ℝ e x₀)†) V ε) Γ :=
    disjoint_left.2 fun ⟨y, η⟩ ⟨hy, hη⟩ ↦ hεΓ y (hKsub hy).1 η hη
  have hDg : {x | ‖fderiv ℝ g x - fderiv ℝ g x₀‖ < ε / 2} ∈ 𝓝 x₀ :=
    ((hg.continuous_fderiv (by simp)).continuousAt.eventually
      (Metric.ball_mem_nhds _ (half_pos hε))).mono fun x hx ↦ by simpa [dist_eq_norm] using hx
  refine ⟨_, inter_mem (inter_mem hge ((e.continuousAt hx₀s).preimage_mem_nhds hK₁)) hDg,
    fun ψ hψ ↦ exists_seminorm_localFourier_le_of_cutoff hV hVcone hg
      (fun x hx ↦ (hψ hx).1.1) hε (M₁ := ‖fderiv ℝ e x₀‖ + ε / 2 + 1)
      (by linarith [norm_nonneg (fderiv ℝ e x₀)]) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (hKsub.trans inter_subset_right) (fun x hx ↦ hχ _ (hψ hx).1.2) L hL hKΓ N⟩
  · have hx' : ‖fderiv ℝ g x - fderiv ℝ g x₀‖ < ε / 2 := (hψ hx).2
    rw [← hgx₀, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hx'.le
  · calc ‖fderiv ℝ g x‖ ≤ ‖fderiv ℝ g x - fderiv ℝ g x₀‖ + ‖fderiv ℝ g x₀‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ ε / 2 + ‖fderiv ℝ e x₀‖ := by
          have hx' : ‖fderiv ℝ g x - fderiv ℝ g x₀‖ < ε / 2 := (hψ hx).2
          rw [hgx₀] at hx' ⊢
          linarith
      _ ≤ _ := by linarith

/-- **The seminorms of the pullback.** For the data `(φ, V, N)` of a seminorm of
`𝓓'_{e^* Γ}(U)`, the decay estimate `(1 + ‖ξ‖) ^ N ‖e^* T (φ e_ξ)‖ ≤ p T` on `V` holds for a
continuous seminorm `p` of `𝓓'_Γ(Ω)`: a partition of unity splits `φ` into finitely many cutoffs,
each supported near a point of `supp φ` where the local estimate holds. -/
private theorem exists_seminorm_localFourier_le
    (hΓ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (j : WaveFrontSeminormIndex U (covectorPullback e U Γ)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ, ∀ ξ ∈ j.cone,
      (1 + ‖ξ‖) ^ j.order * ‖(compCLMOfOpenPartialHomeomorph e he he' hU hUΩ
        u.toDistribution).localFourier j.cutoff ξ‖ ≤ p u := by
  rcases j.cone.eq_empty_or_nonempty with hV | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ by simp [hV] at hξ⟩
  have hV0 := j.isClosed_cone.zero_mem_of_smul_mem j.smul_mem_cone hξ₀
  -- Around each point of the support of the cutoff, a neighbourhood with the local estimate.
  have hloc (x : tsupport (j.cutoff : E → ℂ)) := exists_mem_nhds_forall_exists_seminorm_le
    (he := he) (he' := he') (hU := hU) (hUΩ := hUΩ) hΓ hcone hΓ0 j.isClosed_cone hV0 j.smul_mem_cone
    (j.cutoff.tsupport_subset x.property)
    (fun ξ hξ hmem ↦ disjoint_left.1 j.disjoint (mk_mem_prod x.property hξ) hmem) j.order
  choose O hO hOp using hloc
  obtain ⟨s, ψ, hψO, hsum, -⟩ := j.cutoff.exists_sum_subordinate (fun x ↦ interior (O x))
    (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hO ⟨x, hx⟩)⟩
  choose p hp hpψ using fun i : s ↦ hOp i (ψ i) ((hψO i).trans interior_subset)
  have happly (u : WaveFrontSpace Ω Γ) : (∑ i, p i) u = ∑ i, p i u := by simp
  refine ⟨∑ i, p i, ?_, fun u ξ hξ ↦ ?_⟩
  · rw [show ⇑(∑ i, p i) = fun u ↦ ∑ i, p i u from funext happly]
    exact continuous_finsetSum _ fun i _ ↦ hp i
  set T' := compCLMOfOpenPartialHomeomorph e he he' hU hUΩ u.toDistribution
  have hsplit : T'.localFourier j.cutoff ξ = ∑ i, T'.localFourier (ψ i) ξ := by
    rw [← localFourier_sum_cutoff]
    exact congr_arg (T'.localFourier · ξ) hsum.symm
  rw [happly, hsplit]
  calc (1 + ‖ξ‖) ^ j.order * ‖∑ i, T'.localFourier (ψ i) ξ‖
      ≤ (1 + ‖ξ‖) ^ j.order * ∑ i, ‖T'.localFourier (ψ i) ξ‖ := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ i, (1 + ‖ξ‖) ^ j.order * ‖T'.localFourier (ψ i) ξ‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ i, p i u := Finset.sum_le_sum fun i _ ↦ hpψ i u ξ hξ

end Measurable

/-! ### The pullback as a continuous linear map -/

/-- The pullback `e^* : 𝓓'_Γ(Ω) → 𝓓'_{e^* Γ}(U)` as a linear map, before its continuity is
proved. -/
private def compCLMOfOpenPartialHomeomorphₗ (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) :
    WaveFrontSpace Ω Γ →ₗ[ℂ] WaveFrontSpace U (covectorPullback e U Γ) where
  toFun u := mk (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ u.toDistribution)
    (waveFrontSet_compCLMOfOpenPartialHomeomorph_subset u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext (by simp)
  map_smul' c u := ext (by ext φ; simp)

private theorem toDistribution_compCLMOfOpenPartialHomeomorphₗ (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) (u : WaveFrontSpace Ω Γ) :
    (compCLMOfOpenPartialHomeomorphₗ e he he' hU hUΩ u).toDistribution =
      Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ u.toDistribution :=
  toDistribution_mk _ _

/-- **Continuity of changes of variables in the normal topology.** Let `Γ` be a cone of nonzero
covectors over `Ω`, closed in `Ω × (E \ {0})`. Then the pullback `e^* T` along a smooth change of
variables `e` (`Distribution.compCLMOfOpenPartialHomeomorph`) is a continuous linear map from
`𝓓'_Γ(Ω)` to `𝓓'_{e^* Γ}(U)`, where `e^* Γ = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ Γ}`
(`TauCeti.covectorPullback`). So the normal topology is invariant under changes
of coordinates. -/
def compCLMOfOpenPartialHomeomorph (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω)
    (hΓ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) :
    WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace U (covectorPullback e U Γ) :=
  ⟨compCLMOfOpenPartialHomeomorphₗ e he he' hU hUΩ, by
    borelize E
    refine continuous_linearMap_of_le _ ?_ fun j ↦ ?_
    · have h : ⇑(toDistribution ∘ₗ compCLMOfOpenPartialHomeomorphₗ (Γ := Γ) e he he' hU hUΩ) =
          Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ ∘ toDistribution := by
        funext u
        exact toDistribution_compCLMOfOpenPartialHomeomorphₗ e he he' hU hUΩ u
      rw [h]
      exact (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ).continuous.comp
        continuous_toDistribution
    · obtain ⟨p, hp, hpj⟩ := exists_seminorm_localFourier_le hΓ hcone hΓ0 j
      refine ⟨p, hp, fun u ↦ seminorm_le_bound j _ (apply_nonneg _ _) fun ξ hξ ↦ ?_⟩
      rw [toDistribution_compCLMOfOpenPartialHomeomorphₗ]
      exact hpj u ξ hξ⟩

@[simp]
theorem toDistribution_compCLMOfOpenPartialHomeomorph (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω)
    (hΓ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (u : WaveFrontSpace Ω Γ) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ hΓ hcone hΓ0 u).toDistribution =
      Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ u.toDistribution :=
  toDistribution_compCLMOfOpenPartialHomeomorphₗ e he he' hU hUΩ u

end WaveFrontSpace

end TauCeti
