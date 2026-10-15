/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# The area formula for injective maps with injective derivative

Let `U` and `V` be finite-dimensional real inner product spaces, `m = dim U`, and let `f : U → V`
be injective on a measurable set `s`, differentiable at every point of `s` with injective
derivative. This file proves the **area formula**

`∫⁻ x in s, J f x = μHE[m] (f '' s)`,

where `J f x = (fderiv ℝ f x).normDet` is the `m`-dimensional Jacobian (`LinearMap.normDet`) and
`μHE[m]` is the `m`-dimensional Euclidean Hausdorff measure on `V`, normalized to agree with
Lebesgue measure on `m`-dimensional subspaces. For `V = U`, where `normDet` is `|det|` and
`μHE[m]` is the volume, this is the case of Mathlib's change of variables formula
`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` with invertible derivative; for
`dim V > m` it measures `m`-dimensional surfaces in `V`, such as the graph `y ↦ (y, γ y)` of a
differentiable function, whose derivative is always injective.

Differentiability is required at the points of `s`, not merely within `s`, so that the Jacobian is
the measurable function `x ↦ (fderiv ℝ f x).normDet`. For a Lipschitz map, Rademacher's theorem
provides this at almost every point.

## The argument

The linear case is Mathlib's `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`:
`μHE[m] (A '' s) = J A · vol s`. If `f` is approximated on `s` by an injective linear map `A` up to
`δ`, in the sense of `ApproximatesLinearOn`, and `‖x‖ ≤ K ‖A x‖`, then `f ∘ A⁻¹` is
`(1 + δ K)`-Lipschitz on `A '' s` and `A ∘ f⁻¹` is `(1 - δ K)⁻¹`-Lipschitz on `f '' s`. Since a
`L`-Lipschitz map increases `μHE[m]` by at most `Lᵐ`, the image measure `μHE[m] (f '' s)` lies
between `(1 - δ K)ᵐ J A vol s` and `(1 + δ K)ᵐ J A vol s`
(`ApproximatesLinearOn.euclideanHausdorffMeasure_image_le`,
`ApproximatesLinearOn.ofReal_normDet_mul_volume_le`).

To globalize, fix `τ > 1`. The injective linear maps form an open set, on which `J` is continuous
and positive (`ContinuousLinearMap.continuous_normDet`); cover it by countably many balls on each
of which `J` varies by a factor at most `τ` and the antilipschitz constant is uniform. Splitting
`s` according to which ball contains `fderiv ℝ f x`, and then by Mathlib's partition
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, gives countably many disjoint
measurable pieces on which both the integral and the image measure are within a factor `τ³` of
`J A vol`. The images of the pieces are disjoint and measurable (Lusin–Souslin), so summing gives
the two inequalities up to `τ³`, and `τ → 1` gives the formula.

## Main declarations

* `ApproximatesLinearOn.euclideanHausdorffMeasure_image_le`,
  `ApproximatesLinearOn.ofReal_normDet_mul_volume_le`: the area formula up to a controlled factor
  for a map approximated by an injective linear map.
* `MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`: the area formula.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Section 3.3 (the area formula), whose proof for injective maps with positive Jacobian this
  follows.
* H. Federer, *Geometric Measure Theory*, 3.2.3.
-/

public section

open MeasureTheory Measure Set Filter Metric Module Function
open scoped NNReal ENNReal Topology

section InnerProduct

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {A : U →L[ℝ] V} {s : Set U} {δ K : ℝ≥0}

/-- **Upper area bound near a linear map.** If `f` is approximated on `s` up to `δ` by a linear map
`A` with `‖x‖ ≤ K ‖A x‖`, then `μHE[m] (f '' s) ≤ (1 + δ K)ᵐ J A vol s`, where `m = dim U` and
`J A = A.normDet`. -/
theorem ApproximatesLinearOn.euclideanHausdorffMeasure_image_le
    (hf : ApproximatesLinearOn f A s δ) (hA : AntilipschitzWith K A) :
    μHE[finrank ℝ U] (f '' s) ≤
      ((1 + δ * K) ^ finrank ℝ U : ℝ≥0) * (ENNReal.ofReal A.normDet * volume s) := by
  -- `f = g ∘ A` on `s`, where `g = f ∘ A⁻¹` is `(1 + δ K)`-Lipschitz on `A '' s`.
  set g : V → V := f ∘ invFun A
  have hg (x : U) : g (A x) = f x := by simp [g, leftInverse_invFun hA.injective x]
  have himage : f '' s = g '' (A '' s) := by rw [image_image]; simp only [hg]
  have hlip : LipschitzOnWith (1 + δ * K) g (A '' s) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy : ‖x - y‖ ≤ K * ‖A x - A y‖ := by
      simpa [dist_eq_norm] using hA.le_mul_dist x y
    rw [hg, hg, dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
    calc ‖f x - f y‖ = ‖(A x - A y) + (f x - f y - A (x - y))‖ := by rw [map_sub]; abel_nf
      _ ≤ ‖A x - A y‖ + ‖f x - f y - A (x - y)‖ := norm_add_le _ _
      _ ≤ ‖A x - A y‖ + δ * (K * ‖A x - A y‖) := by
          gcongr
          exact (hf x hx y hy).trans (by gcongr)
      _ = (1 + δ * K) * ‖A x - A y‖ := by ring
  rw [himage, ENNReal.coe_pow,
    ← (A : U →ₗ[ℝ] V).euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
  exact hlip.euclideanHausdorffMeasure_image_le _

/-- **Lower area bound near a linear map.** If `f` is approximated on `s` up to `δ` by a linear map
`A` with `‖x‖ ≤ K ‖A x‖` and `δ K < 1`, then `J A vol s ≤ (1 - δ K)⁻ᵐ μHE[m] (f '' s)`, where
`m = dim U` and `J A = A.normDet`. -/
theorem ApproximatesLinearOn.ofReal_normDet_mul_volume_le
    (hf : ApproximatesLinearOn f A s δ) (hA : AntilipschitzWith K A) (hδ : δ * K < 1) :
    ENNReal.ofReal A.normDet * volume s ≤
      ((1 - δ * K)⁻¹ ^ finrank ℝ U : ℝ≥0) * μHE[finrank ℝ U] (f '' s) := by
  have hδ' : (δ : ℝ) * K < 1 := by exact_mod_cast hδ
  -- `f` expands distances by at least the factor `1 - δ K` relative to `A`.
  have hkey : ∀ x ∈ s, ∀ y ∈ s, (1 - δ * K) * ‖A x - A y‖ ≤ ‖f x - f y‖ := by
    intro x hx y hy
    have hxy : ‖x - y‖ ≤ K * ‖A x - A y‖ := by
      simpa [dist_eq_norm] using hA.le_mul_dist x y
    have h1 : ‖A x - A y‖ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := by
      calc ‖A x - A y‖ = ‖(f x - f y) - (f x - f y - A (x - y))‖ := by rw [map_sub]; abel_nf
        _ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := norm_sub_le _ _
    have h2 : ‖f x - f y - A (x - y)‖ ≤ δ * (K * ‖A x - A y‖) :=
      (hf x hx y hy).trans (by gcongr)
    nlinarith
  have hpos : (0 : ℝ) < 1 - δ * K := by linarith
  have hinj : InjOn f s := fun x hx y hy hfxy => by
    have h := hkey x hx y hy
    rw [hfxy, sub_self, norm_zero] at h
    exact hA.injective (sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h hpos)))
  -- `A = g ∘ f` on `s`, where `g = A ∘ f⁻¹` is `(1 - δ K)⁻¹`-Lipschitz on `f '' s`.
  set g : V → V := A ∘ invFunOn f s
  have hg : ∀ x ∈ s, g (f x) = A x := fun x hx => by
    simp [g, hinj.leftInvOn_invFunOn hx]
  have himage : A '' s = g '' (f '' s) := by
    rw [image_image]
    exact image_congr fun x hx => (hg x hx).symm
  have hlip : LipschitzOnWith (1 - δ * K)⁻¹ g (f '' s) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hg x hx, hg y hy, dist_eq_norm, dist_eq_norm, NNReal.coe_inv,
      NNReal.coe_sub hδ.le, NNReal.coe_one, NNReal.coe_mul, inv_mul_eq_div,
      le_div_iff₀ hpos, mul_comm]
    exact hkey x hx y hy
  have h := hlip.euclideanHausdorffMeasure_image_le (finrank ℝ U)
  rw [← himage] at h
  rw [ENNReal.coe_pow]
  calc ENNReal.ofReal A.normDet * volume s = μHE[finrank ℝ U] (A '' s) :=
        ((A : U →ₗ[ℝ] V).euclideanHausdorffMeasure_image_eq_normDet_mul_volume s).symm
    _ ≤ _ := h

namespace MeasureTheory

/-- The area formula on one piece, up to factors: if `f` is approximated on `Q` by `A` with a
precision `δ` for which `(1 + δ K)ᵐ` and `(1 - δ K)⁻ᵐ` are at most `τ`, and `j` agrees with `J A` on
`Q` up to the factor `σ`, then `∫⁻ x in Q, j x` and `μHE[m] (f '' Q)` agree up to the factor
`τ σ`. -/
private theorem euclideanHausdorffMeasure_image_le_and_lintegral_le {Q : Set U}
    (hQ : MeasurableSet Q) {j : U → ℝ≥0∞} {τ σ : ℝ} (hσ : 0 ≤ σ)
    (hf : ApproximatesLinearOn f A Q δ) (hA : AntilipschitzWith K A) (hδK : δ * K < 1)
    (h₁ : (((1 + δ * K) ^ finrank ℝ U : ℝ≥0) : ℝ) ≤ τ)
    (h₂ : ((((1 - δ * K)⁻¹) ^ finrank ℝ U : ℝ≥0) : ℝ) ≤ τ)
    (hj : ∀ x ∈ Q, ENNReal.ofReal A.normDet ≤ ENNReal.ofReal σ * j x ∧
      j x ≤ ENNReal.ofReal σ * ENNReal.ofReal A.normDet) :
    μHE[finrank ℝ U] (f '' Q) ≤ ENNReal.ofReal (τ * σ) * ∫⁻ x in Q, j x ∧
      ∫⁻ x in Q, j x ≤ ENNReal.ofReal (σ * τ) * μHE[finrank ℝ U] (f '' Q) := by
  have hτ : 0 ≤ τ := (NNReal.coe_nonneg _).trans h₁
  have h₁' : (((1 + δ * K) ^ finrank ℝ U : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal τ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h₁
  have h₂' : ((((1 - δ * K)⁻¹) ^ finrank ℝ U : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal τ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h₂
  constructor
  · calc μHE[finrank ℝ U] (f '' Q)
        ≤ ((1 + δ * K) ^ finrank ℝ U : ℝ≥0) * (ENNReal.ofReal A.normDet * volume Q) :=
          hf.euclideanHausdorffMeasure_image_le hA
      _ ≤ ENNReal.ofReal τ * ∫⁻ x in Q, ENNReal.ofReal σ * j x := by
          rw [← setLIntegral_const]
          exact mul_le_mul' h₁' (setLIntegral_mono' hQ fun x hx => (hj x hx).1)
      _ = ENNReal.ofReal (τ * σ) * ∫⁻ x in Q, j x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
            ENNReal.ofReal_mul hτ]
  · calc ∫⁻ x in Q, j x ≤ ∫⁻ x in Q, ENNReal.ofReal σ * ENNReal.ofReal A.normDet :=
          setLIntegral_mono' hQ fun x hx => (hj x hx).2
      _ = ENNReal.ofReal σ * (ENNReal.ofReal A.normDet * volume Q) := by
          rw [setLIntegral_const, mul_assoc]
      _ ≤ ENNReal.ofReal σ * (ENNReal.ofReal τ * μHE[finrank ℝ U] (f '' Q)) := by
          exact mul_le_mul' le_rfl
            ((hf.ofReal_normDet_mul_volume_le hA hδK).trans (mul_le_mul' h₂' le_rfl))
      _ = ENNReal.ofReal (σ * τ) * μHE[finrank ℝ U] (f '' Q) := by
          rw [← mul_assoc, ENNReal.ofReal_mul hσ]

variable [FiniteDimensional ℝ V]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
/-- A nonempty set `W` of injective linear maps is covered by countably many balls
`ball (B k) (ρ k)` on each of which the antilipschitz constant `K k` is uniform and the Jacobian
varies by a factor at most `τ`, together with approximation precisions `δ k` for which the factors
`(1 + δ k K k)ᵐ` and `(1 - δ k K k)⁻ᵐ` of the linear area bounds are at most `τ`. -/
private theorem exists_seq_ball_cover {W : Set (U →L[ℝ] V)} (hW : W.Nonempty)
    (hWinj : ∀ C ∈ W, Injective C) {τ : ℝ} (hτ : 1 < τ) :
    ∃ (B : ℕ → U →L[ℝ] V) (ρ : ℕ → ℝ) (K δ : ℕ → ℝ≥0),
      (∀ k, 0 < δ k ∧ δ k * K k < 1 ∧ (((1 + δ k * K k) ^ finrank ℝ U : ℝ≥0) : ℝ) ≤ τ ∧
        ((((1 - δ k * K k)⁻¹) ^ finrank ℝ U : ℝ≥0) : ℝ) ≤ τ) ∧
      (∀ k, ∀ C : U →L[ℝ] V, dist C (B k) < ρ k →
        AntilipschitzWith (K k) C ∧ C.normDet ≤ τ * (B k).normDet ∧
          (B k).normDet ≤ τ * C.normDet) ∧
      ∀ C ∈ W, ∃ k, dist C (B k) < ρ k := by
  set G := {B : U →L[ℝ] V | Injective B}
  choose ρ hρ K hK using fun B : G =>
    (B : U →L[ℝ] V).exists_ball_antilipschitzWith_normDet_le B.2 hτ
  -- For each antilipschitz constant `K` there is a positive precision `δ` for which the factors
  -- `(1 + δ K)ᵐ` and `(1 - δ K)⁻ᵐ` of the linear area bounds are at most `τ`.
  have hδex (K : ℝ≥0) (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧ δ * K < 1 ∧
      (((1 + δ * K) ^ m : ℝ≥0) : ℝ) ≤ τ ∧ ((((1 - δ * K)⁻¹) ^ m : ℝ≥0) : ℝ) ≤ τ := by
    have h₁ : ∀ᶠ δ : ℝ in 𝓝 0, (1 + δ * K) ^ m < τ :=
      (((continuous_const.add (continuous_id.mul continuous_const)).pow m).tendsto' 0 1
        (by simp)).eventually_lt_const hτ
    have h₂ : ∀ᶠ δ : ℝ in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < τ := by
      have hc : ContinuousAt (fun δ : ℝ => ((1 - δ * K)⁻¹) ^ m) 0 :=
        ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).inv₀ (by simp)).pow m
      have ht := hc.tendsto
      rw [zero_mul, sub_zero, inv_one, one_pow] at ht
      exact ht.eventually_lt_const hτ
    have h₃ : ∀ᶠ δ : ℝ in 𝓝 0, δ * K < 1 :=
      ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually_lt_const one_pos
    obtain ⟨δ, ⟨⟨h₁, h₂⟩, h₃⟩, hδ⟩ :=
      ((((h₁.and h₂).and h₃).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
    have hδK : δ.toNNReal * K < 1 := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_mul, Real.coe_toNNReal _ (le_of_lt hδ)]
      exact h₃
    refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, hδK, ?_, ?_⟩
    · rw [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
        Real.coe_toNNReal _ (le_of_lt hδ)]
      exact h₁.le
    · rw [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one, NNReal.coe_mul,
        Real.coe_toNNReal _ (le_of_lt hδ)]
      exact h₂.le
  choose δ hδ using fun B : G => hδex (K B) (finrank ℝ U)
  -- Second countability extracts a countable subcover, which `W ≠ ∅` makes nonempty.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun B : G => ball (B : U →L[ℝ] V) (ρ B)) fun _ => isOpen_ball
  have hcover : ∀ C ∈ W, ∃ B ∈ T, C ∈ ball (B : U →L[ℝ] V) (ρ B) := by
    intro C hC
    have hmem : C ∈ ⋃ B : G, ball (B : U →L[ℝ] V) (ρ B) :=
      mem_iUnion.2 ⟨⟨C, hWinj C hC⟩, mem_ball_self (hρ _)⟩
    rw [← hTU] at hmem
    simpa only [mem_iUnion, exists_prop] using hmem
  obtain ⟨C₀, hC₀⟩ := hW
  obtain ⟨b, rfl⟩ := hTc.exists_eq_range (let ⟨B, hB, _⟩ := hcover C₀ hC₀; ⟨B, hB⟩)
  refine ⟨fun k => b k, fun k => ρ (b k), fun k => K (b k), fun k => δ (b k),
    fun k => hδ (b k), fun k => hK (b k), fun C hC => ?_⟩
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hcover C hC
  exact ⟨k, hk⟩

/-- A measurable set `s` on which `f` is differentiable with injective derivative splits into
countably many disjoint measurable pieces, on each of which the area formula holds up to the factor
`τ³`. -/
private theorem exists_partition_le_and_le (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x))
    (hsne : s.Nonempty) {τ : ℝ} (hτ : 1 < τ) :
    ∃ P : ℕ × ℕ → Set U, (∀ p, MeasurableSet (P p)) ∧ Pairwise (Disjoint on P) ∧
      ⋃ p, P p = s ∧ ∀ p,
        μHE[finrank ℝ U] (f '' P p) ≤
            ENNReal.ofReal (τ ^ 3) * ∫⁻ x in P p, ENNReal.ofReal (fderiv ℝ f x).normDet ∧
          ∫⁻ x in P p, ENNReal.ofReal (fderiv ℝ f x).normDet ≤
            ENNReal.ofReal (τ ^ 3) * μHE[finrank ℝ U] (f '' P p) := by
  obtain ⟨B, ρ, K, δ, hδ, hK, hcover⟩ := exists_seq_ball_cover (hsne.image (fderiv ℝ f))
    (by rintro _ ⟨x, hx, rfl⟩; exact hinj x hx) hτ
  -- Split `s` according to which ball contains `fderiv ℝ f x`, then into pieces on which `f` is
  -- approximated by a linear map.
  set S : ℕ → Set U := fun k => s ∩ fderiv ℝ f ⁻¹' ball (B k) (ρ k)
  have hSm (k : ℕ) : MeasurableSet (S k) :=
    hs.inter (measurable_fderiv ℝ f isOpen_ball.measurableSet)
  set D := disjointed S
  have hDS (k : ℕ) : D k ⊆ S k := disjointed_subset S k
  choose t A ht_disj ht_meas ht_cover ht_approx ht_A using fun k =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (D k) (fderiv ℝ f)
      (fun x hx => (hd x (hDS k hx).1).hasFDerivAt.hasFDerivWithinAt) (fun _ => δ k)
      fun _ => (hδ k).1.ne'
  refine ⟨fun p => D p.1 ∩ t p.1 p.2, fun p => (MeasurableSet.disjointed hSm p.1).inter
    (ht_meas p.1 p.2), ?_, ?_, ?_⟩
  · rintro ⟨k, n⟩ ⟨k', n'⟩ hne
    by_cases hk : k = k'
    · subst hk
      exact (ht_disj k fun hn => hne (Prod.ext rfl hn)).mono inter_subset_right
        inter_subset_right
    · exact (disjoint_disjointed S hk).mono inter_subset_left inter_subset_left
  · refine Subset.antisymm (iUnion_subset fun p => inter_subset_left.trans
      ((hDS p.1).trans inter_subset_left)) fun x hx => ?_
    obtain ⟨k, hk⟩ := hcover _ (mem_image_of_mem _ hx)
    obtain ⟨k', hk'⟩ := mem_iUnion.1 (by rw [iUnion_disjointed]; exact mem_iUnion.2 ⟨k, hx, hk⟩ :
      x ∈ ⋃ k, D k)
    obtain ⟨n, hn⟩ := mem_iUnion.1 (ht_cover k' hk')
    exact mem_iUnion.2 ⟨(k', n), hk', hn⟩
  · -- On a nonempty piece, `A` and every `fderiv ℝ f x` lie in the same ball, so their Jacobians
    -- agree up to the factor `τ²`.
    rintro ⟨k, n⟩
    rcases (D k ∩ t k n).eq_empty_or_nonempty with h | ⟨x₁, hx₁⟩
    · simp [h]
    obtain ⟨y, hy, hAy⟩ := ht_A k ⟨x₁, hx₁.1⟩ n
    obtain ⟨hAanti, hA₁, hA₂⟩ := hK k (A k n) (by rw [hAy]; exact (hDS k hy).2)
    -- The helper below states its two bounds with the factors `τ * σ` and `σ * τ`, for `σ = τ²`.
    have hτ3 : τ ^ 3 = τ * τ ^ 2 := by ring
    rw [hτ3]
    nth_rewrite 2 [mul_comm τ]
    refine euclideanHausdorffMeasure_image_le_and_lintegral_le
      ((MeasurableSet.disjointed hSm k).inter (ht_meas k n)) (sq_nonneg τ) (ht_approx k n) hAanti
      (hδ k).2.1 (hδ k).2.2.1 (hδ k).2.2.2 fun x hx => ?_
    obtain ⟨-, hx₁', hx₂'⟩ := hK k (fderiv ℝ f x) (hDS k hx.1).2
    have hJB := (B k).normDet_nonneg
    rw [← ENNReal.ofReal_mul (sq_nonneg τ), ← ENNReal.ofReal_mul (sq_nonneg τ)]
    constructor <;> apply ENNReal.ofReal_le_ofReal
    · calc (A k n).normDet ≤ τ * (B k).normDet := hA₁
        _ ≤ τ * (τ * (fderiv ℝ f x).normDet) := by gcongr
        _ = τ ^ 2 * (fderiv ℝ f x).normDet := by ring
    · calc (fderiv ℝ f x).normDet ≤ τ * (B k).normDet := hx₁'
        _ ≤ τ * (τ * (A k n).normDet) := by gcongr
        _ = τ ^ 2 * (A k n).normDet := by ring

/-- The area formula up to the factor `τ³`, for every `τ > 1`: sum the estimates on the pieces of
`exists_partition_le_and_le`, whose images are disjoint and measurable. -/
private theorem euclideanHausdorffMeasure_image_le_and_lintegral_le_of_one_lt
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) {τ : ℝ} (hτ : 1 < τ) :
    μHE[finrank ℝ U] (f '' s) ≤
        ENNReal.ofReal (τ ^ 3) * ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet ∧
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet ≤
        ENNReal.ofReal (τ ^ 3) * μHE[finrank ℝ U] (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  obtain ⟨P, hPm, hPd, hPU, hpiece⟩ := exists_partition_le_and_le hs hd hinj hsne hτ
  have hPs (p : ℕ × ℕ) : P p ⊆ s := hPU ▸ subset_iUnion P p
  have himg_meas (p : ℕ × ℕ) : MeasurableSet (f '' P p) :=
    (hPm p).image_of_continuousOn_injOn
      (fun x hx => (hd x (hPs p hx)).continuousAt.continuousWithinAt) (hf.mono (hPs p))
  have himg_disj : Pairwise (Disjoint on fun p => f '' P p) := by
    intro p q hpq
    refine disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact disjoint_left.1 (hPd hpq) hx (hf (hPs q hy) (hPs p hx) hxy ▸ hy)
  rw [← hPU, image_iUnion, measure_iUnion himg_disj himg_meas, lintegral_iUnion hPm hPd,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun p => (hpiece p).1, ENNReal.tsum_le_tsum fun p => (hpiece p).2⟩

/-- **The area formula** for injective maps with injective derivative. Let `U` and `V` be
finite-dimensional real inner product spaces and let `f : U → V` be injective on a measurable set
`s`, differentiable at every point of `s` with injective derivative. Then the integral over `s`
of the `dim U`-dimensional Jacobian `(fderiv ℝ f x).normDet` is the `dim U`-dimensional Euclidean
Hausdorff measure of `f '' s`. -/
theorem lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x))
    (hf : InjOn f s) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet = μHE[finrank ℝ U] (f '' s) := by
  -- Both inequalities hold up to the factor `τ³` for every `τ > 1`; let `τ → 1`.
  have hlim {a b : ℝ≥0∞} (h : ∀ τ : ℝ, 1 < τ → a ≤ ENNReal.ofReal (τ ^ 3) * b) : a ≤ b := by
    rcases eq_or_ne b ⊤ with rfl | hb
    · exact le_top
    have ht : Tendsto (fun τ : ℝ => ENNReal.ofReal (τ ^ 3) * b) (𝓝[>] 1) (𝓝 b) := by
      have h1 : Tendsto (fun τ : ℝ => ENNReal.ofReal (τ ^ 3)) (𝓝[>] 1) (𝓝 1) := by
        simpa using (ENNReal.tendsto_ofReal ((continuous_pow 3).tendsto (1 : ℝ))).mono_left
          nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hb)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun τ hτ => h τ hτ)
  exact le_antisymm
    (hlim fun _ hτ =>
      (euclideanHausdorffMeasure_image_le_and_lintegral_le_of_one_lt hs hd hinj hf hτ).2)
    (hlim fun _ hτ =>
      (euclideanHausdorffMeasure_image_le_and_lintegral_le_of_one_lt hs hd hinj hf hτ).1)

end MeasureTheory

end InnerProduct
