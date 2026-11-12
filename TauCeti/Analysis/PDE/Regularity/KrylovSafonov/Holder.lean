/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
import Mathlib.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence

/-!
# The interior Hölder estimate of Krylov and Safonov

Let `a` be uniformly elliptic on a ball `B(x₀, 2 r) ⊆ ℝⁿ`, `n ≥ 1`, with constants
`λ ≤ Λ ≤ κ λ`, and let `u` be a `C²` solution of the non-divergence-form equation

`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` in `B(x₀, 2 r)`

with `|u| ≤ M` there and `f ∈ Lⁿ(B(x₀, 2 r))`. Then `u` is `α`-Hölder on `B(x₀, r)` with

`|u(x) - u(y)| ≤ C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ) ‖x - y‖^α`

(`TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq`), where `0 < α ≤ 1` and `C`
depend only on the dimension and on `κ`. The coefficients need no regularity, not even
measurability, and need not be symmetric. This is the interior Hölder estimate of Krylov and
Safonov (Gilbarg–Trudinger, Corollary 9.24) for classical solutions.

## The argument

The estimate follows from the power decay of the superlevel sets of a nonnegative supersolution
(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`), without passing through the
weak Harnack inequality.

* **Oscillation decay.** Let `m ≤ u ≤ m + L` on `closedBall c ρ`. Translate a dyadic cube `Q` of
  side `2ᵏ ≈ ρ / (4 √n)` to be centred at `c`. The functions `v₁ = (u - m) / s` and
  `v₂ = (m + L - u) / s` are nonnegative supersolutions of equations with right-hand sides
  `± f / s`, and `v₁ + v₂ = L / s`. With `s = L / (2 T)`, one of them is at least `T` at every
  point, so the two superlevel sets `{vᵢ ≥ T}` cover `Q`. For `T` large the power decay forbids
  this when both `vᵢ` are at most `1` somewhere near `c`. So one of them exceeds `1` on
  `closedBall c (ρ / 4)`, and there the oscillation of `u` is at most `(1 - δ) L`, with
  `δ = 1 / (2 T)`. The power decay needs `ρ ‖f / s‖_{Lⁿ} ≤ ε₀ λ`; when this fails, `L` is already
  at most a multiple of `ρ ‖f‖_{Lⁿ} / λ`. In both cases the oscillation on `closedBall c (ρ / 4)`
  is at most `(1 - δ) L + K ρ ‖f‖_{Lⁿ} / λ`.
* **Iteration.** On the balls of radii `ρ / 4ʲ` the quantity `Lⱼ + 4 K (ρ / 4ʲ) ‖f‖ / λ` decreases
  geometrically, with ratio `θ = max (1 - δ) (1 / 2)`.
* **Hölder bound.** With `θ = 4^(-α)`, two points at distance `d ≤ r / 4ʲ` differ by at most
  `θʲ (2 M + 4 K r ‖f‖ / λ) ≤ 4 (d / r)^α (2 M + 4 K r ‖f‖ / λ)`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq`: **the interior Hölder estimate
  of Krylov and Safonov** for classical solutions.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Proposition 4.10.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7, Corollary 9.24.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The power decay about an arbitrary centre.** The power decay
`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`, stated for dyadic cubes about
their own centres, transported by the translation `x ↦ x + d` that takes the centre
`c₀ = (2ᵏ / 2, …, 2ᵏ / 2)` of `dyadicCube k 0` to an arbitrary point `c`. -/
private theorem exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        4 * 2 ^ k * √(Fintype.card ι) ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), u x ≤ 1) →
        ∀ ⦃t : ℝ⦄, 0 < t →
          volume ({x | t ≤ u (x + (c - WithLp.toLp 2 fun _ ↦ 2⁻¹ * 2 ^ k))} ∩
            WithLp.ofLp ⁻¹' dyadicCube k 0) ≤
            ENNReal.ofReal (C * t ^ (-ε)) *
              volume (WithLp.ofLp ⁻¹' dyadicCube k 0 : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  refine ⟨C, ε, ε₀, hC, hε, hε₀, ?_⟩
  intro lam Lam R k c a u f hR ha hLam hcont hu hnonneg hsuper hf hx t ht
  set c₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 2⁻¹ * 2 ^ k
  set d := c - c₀
  have hd (x : EuclideanSpace ℝ ι) : dist (x + d) c = dist x c₀ := by
    rw [← dist_add_right x c₀ d]
    simp [d]
  have hball : MapsTo (· + d) (ball c₀ R) (ball c R) := fun x hx ↦ by
    rw [mem_ball, hd]
    exact hx
  have hcball : MapsTo (· + d) (closedBall c₀ R) (closedBall c R) := fun x hx ↦ by
    rw [mem_closedBall, hd]
    exact hx
  have hpre : (· + d) ⁻¹' ball c R = ball c₀ R := by
    ext x
    simp only [mem_preimage, mem_ball, hd]
  have he : MeasurableEmbedding (· + d : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    measurableEmbedding_addRight d
  have hfd : eLpNorm (fun x ↦ (f (x + d))⁺) (Fintype.card ι) (volume.restrict (ball c₀ R)) =
      eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) := by
    rw [← hpre]
    -- Present the integrand as a composition with the translation, the form of
    -- `MeasurableEmbedding.eLpNorm_map_measure`; the two agree by beta reduction.
    change eLpNorm ((fun x ↦ (f x)⁺) ∘ (· + d)) _ _ = _
    rw [← he.eLpNorm_map_measure, ← he.restrict_map, map_add_right_eq_self]
  have ha' : UniformlyEllipticOn (ball c₀ R) (fun x ↦ a (x + d)) lam Lam :=
    .of_bounds ha.pos ha.le (fun _ hx ξ ↦ ha.lower_bound (hball hx) ξ)
      (fun _ hx η ξ ↦ ha.upper_bound (hball hx) η ξ)
  refine H (m := 0) (c := c₀) (a := fun x ↦ a (x + d)) (u := fun x ↦ u (x + d))
    (f := fun x ↦ f (x + d)) (by simp [c₀]) hR
    ha' hLam
    (hcont.comp (continuous_id.add continuous_const).continuousOn hcball)
    (hu.comp (contDiff_id.add contDiff_const).contDiffOn hball)
    (fun x hx ↦ hnonneg _ (hcball hx)) (fun x hx ↦ ?_) (by rwa [hfd]) ?_ ht
  · have h1 : fderiv ℝ (fun y ↦ u (y + d)) = fun y ↦ fderiv ℝ u (y + d) :=
      funext fun y ↦ fderiv_comp_add_right d
    rw [h1, fderiv_comp_add_right d]
    exact hsuper _ (hball hx)
  · obtain ⟨x, hx, hux⟩ := hx
    refine ⟨x - d, ?_, by simpa using hux⟩
    rw [mem_ball, ← hd, sub_add_cancel]
    exact hx

/-- **One step of oscillation decay.** There are `0 < δ < 1` and `K ≥ 0`, depending only on the
dimension and on `κ`, with the following property. Let `a` be uniformly elliptic on `B(c, ρ)`
with `λ ≤ Λ ≤ κ λ`, and let `u` be continuous on `closedBall c ρ` and `C²` in `B(c, ρ)` with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` there and `‖f‖_{Lⁿ(B(c, ρ))} ≤ F`. If `m ≤ u ≤ m + L` on `closedBall c ρ`,
then on `closedBall c (ρ / 4)` the function `u` takes values in an interval of length
`(1 - δ) L + K ρ F / λ`. -/
private theorem exists_mem_Icc_closedBall_div_four {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ K ∧
      ∀ ⦃lam Lam ρ m L F : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < ρ → 0 ≤ F →
        UniformlyEllipticOn (ball c ρ) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c ρ) → ContDiffOn ℝ 2 u (ball c ρ) →
        (∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = f x) →
        eLpNorm f (Fintype.card ι) (volume.restrict (ball c ρ)) ≤ ENNReal.ofReal F →
        (∀ x ∈ closedBall c ρ, u x ∈ Icc m (m + L)) →
        ∃ m', ∀ x ∈ closedBall c (ρ / 4),
          u x ∈ Icc m' (m' + ((1 - δ) * L + K * ρ * F / lam)) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  set T := max 1 ((4 * C) ^ ε⁻¹)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 < T := one_pos.trans_le hT1
  -- `2 C T^(-ε) ≤ 1 / 2`.
  have hCT : 2 * (C * T ^ (-ε)) ≤ 2⁻¹ := by
    have h4C : ((4 * C) ^ ε⁻¹) ^ (-ε) = (4 * C)⁻¹ := by
      rw [← Real.rpow_mul (by positivity), inv_mul_eq_div, neg_div, div_self hε.ne',
        Real.rpow_neg_one]
    have hle : T ^ (-ε) ≤ (4 * C)⁻¹ :=
      h4C ▸ Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _) (neg_nonpos.2 hε.le)
    calc 2 * (C * T ^ (-ε)) ≤ 2 * (C * (4 * C)⁻¹) := by gcongr
      _ = 2⁻¹ := by field_simp; norm_num
  refine ⟨(2 * T)⁻¹, ε₀⁻¹, by positivity, inv_lt_one_of_one_lt₀ (by linarith), by positivity, ?_⟩
  intro lam Lam ρ m L F c a u f hρ hF ha hLam hcont hu heq hf hmem
  have hlam : 0 < lam := ha.pos
  have hL : 0 ≤ L := by
    have h := hmem c (mem_closedBall_self hρ.le)
    linarith [h.1, h.2]
  have hρ4 : closedBall c (ρ / 4) ⊆ closedBall c ρ := closedBall_subset_closedBall (by linarith)
  by_cases hsmall : L ≤ 2 * T * ρ * F / (ε₀ * lam)
  · -- The oscillation is already controlled by the right-hand side.
    refine ⟨m, fun x hx ↦ ?_⟩
    have h := hmem x (hρ4 hx)
    have key : (2 * T)⁻¹ * L ≤ ε₀⁻¹ * ρ * F / lam :=
      calc (2 * T)⁻¹ * L ≤ (2 * T)⁻¹ * (2 * T * ρ * F / (ε₀ * lam)) := by gcongr
        _ = ε₀⁻¹ * ρ * F / lam := by field_simp
    exact ⟨h.1, by linarith [h.2]⟩
  push Not at hsmall
  set s := L / (2 * T)
  have hρF : 0 ≤ ρ * F / (ε₀ * lam) := by positivity
  have hsF : ρ * F / (ε₀ * lam) < s := by
    rw [lt_div_iff₀ (by positivity)]
    calc ρ * F / (ε₀ * lam) * (2 * T) = 2 * T * ρ * F / (ε₀ * lam) := by ring
      _ < L := hsmall
  have hs : 0 < s := hρF.trans_lt hsF
  have hLpos : 0 < L := by
    have : 0 < L / (2 * T) := hs
    exact (div_pos_iff_of_pos_right (by positivity)).1 this
  -- A dyadic scale with `2ᵏ ≤ ρ / (4 √n) < 2ᵏ⁺¹`.
  have hn : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (x := ρ / (4 * √(Fintype.card ι : ℝ)))
    (by positivity) one_lt_two
  rw [le_div_iff₀ (by positivity)] at hk1
  rw [div_lt_iff₀ (by positivity), zpow_add_one₀ two_ne_zero] at hk2
  have hR : 4 * 2 ^ k * √(Fintype.card ι : ℝ) ≤ ρ := by linarith
  have hsub : closedBall c (ρ / 4) ⊆ ball c (2 * 2 ^ k * √(Fintype.card ι)) :=
    closedBall_subset_ball (by linarith)
  have hball : ball c ρ ⊆ closedBall c ρ := ball_subset_closedBall
  -- The right-hand side `‖f‖ / s` is small.
  have hfm : AEStronglyMeasurable f (volume.restrict (ball c ρ)) :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hf.trans_lt ENNReal.ofReal_lt_top).ne
  have hg : ENNReal.ofReal ρ * eLpNorm (fun x ↦ (s⁻¹ * ‖f x‖)⁺) (Fintype.card ι)
      (volume.restrict (ball c ρ)) ≤ ENNReal.ofReal (ε₀ * lam) := by
    have h1 : (fun x ↦ (s⁻¹ * ‖f x‖)⁺) = s⁻¹ • fun x ↦ ‖f x‖ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      exact posPart_eq_self.2 (by positivity)
    rw [h1, eLpNorm_const_smul, eLpNorm_norm _ hfm, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal ρ * (ENNReal.ofReal s⁻¹ * eLpNorm f (Fintype.card ι)
          (volume.restrict (ball c ρ))) ≤
          ENNReal.ofReal ρ * (ENNReal.ofReal s⁻¹ * ENNReal.ofReal F) := by gcongr
      _ = ENNReal.ofReal (ρ * (s⁻¹ * F)) := by
        rw [ENNReal.ofReal_mul hρ.le, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (ε₀ * lam) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_lt_iff₀ (by positivity)] at hsF
        rw [← div_eq_inv_mul, mul_div_assoc', div_le_iff₀ hs]
        linarith
  -- `v₁ = (u - m) / s` and `v₂ = (m + L - u) / s` are nonnegative supersolutions.
  set v₁ := fun x ↦ s⁻¹ * (u x - m)
  set v₂ := fun x ↦ s⁻¹ * (m + L - u x)
  have hv₁ : ∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v₁) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ s⁻¹ * ‖f x‖ := by
    intro x hx
    have h : fderiv ℝ (fun y ↦ u y - m) = fderiv ℝ u := funext fun y ↦ fderiv_sub_const m
    rw [sum_mul_fderiv_fderiv_const_mul, h, heq x hx]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have hv₂ : ∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v₂) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ s⁻¹ * ‖f x‖ := by
    intro x hx
    have h : fderiv ℝ (fun y ↦ m + L - u y) = -fderiv ℝ u :=
      funext fun y ↦ fderiv_const_sub (m + L)
    rw [sum_mul_fderiv_fderiv_const_mul, h]
    have h2 : fderiv ℝ (-fderiv ℝ u) x = -fderiv ℝ (fderiv ℝ u) x :=
      fderiv_neg (f := fderiv ℝ u)
    simp only [h2, _root_.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [heq x hx, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (Real.norm_eq_abs (f x) ▸ neg_le_abs _) (by positivity)
  have hcont₁ : ContinuousOn v₁ (closedBall c ρ) :=
    continuousOn_const.mul (hcont.sub continuousOn_const)
  have hcont₂ : ContinuousOn v₂ (closedBall c ρ) :=
    continuousOn_const.mul (continuousOn_const.sub hcont)
  have hu₁ : ContDiffOn ℝ 2 v₁ (ball c ρ) := contDiffOn_const.mul (hu.sub contDiffOn_const)
  have hu₂ : ContDiffOn ℝ 2 v₂ (ball c ρ) := contDiffOn_const.mul (contDiffOn_const.sub hu)
  have hnn₁ : ∀ x ∈ closedBall c ρ, 0 ≤ v₁ x := fun x hx ↦
    mul_nonneg (by positivity) (by linarith [(hmem x hx).1])
  have hnn₂ : ∀ x ∈ closedBall c ρ, 0 ≤ v₂ x := fun x hx ↦
    mul_nonneg (by positivity) (by linarith [(hmem x hx).2])
  -- They cannot both be at most `1` near `c`: their superlevel sets at `T` would cover `Q`.
  set d : EuclideanSpace ℝ ι := c - WithLp.toLp 2 fun _ ↦ 2⁻¹ * 2 ^ k
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k 0
  have hQ : volume Q = volume (dyadicCube k 0) :=
    (PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k 0).nullMeasurableSet
  have hcover : Q ⊆ ({x | T ≤ v₁ (x + d)} ∩ Q) ∪ ({x | T ≤ v₂ (x + d)} ∩ Q) := by
    intro x hx
    have hsum : v₁ (x + d) + v₂ (x + d) = 2 * T := by
      have h : v₁ (x + d) + v₂ (x + d) = s⁻¹ * L := by
        simp only [v₁, v₂]
        ring
      rw [h]
      simp only [s]
      field_simp [hLpos.ne']
    by_cases h : T ≤ v₁ (x + d)
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨show T ≤ v₂ (x + d) by linarith [not_le.1 h], hx⟩
  have hnot : ¬ ((∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), v₁ x ≤ 1) ∧
      ∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), v₂ x ≤ 1) := by
    rintro ⟨h₁, h₂⟩
    have H₁ := H hR ha hLam hcont₁ hu₁ hnn₁ hv₁ hg h₁ hT0
    have H₂ := H hR ha hLam hcont₂ hu₂ hnn₂ hv₂ hg h₂ hT0
    have hpos : 0 < volume Q := hQ ▸ volume_dyadicCube_pos k 0
    have hfin : volume Q ≠ ∞ := hQ ▸ volume_dyadicCube_ne_top k 0
    have hle : volume Q ≤ ENNReal.ofReal 2⁻¹ * volume Q :=
      calc volume Q ≤ volume ({x | T ≤ v₁ (x + d)} ∩ Q) + volume ({x | T ≤ v₂ (x + d)} ∩ Q) :=
            (measure_mono hcover).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (C * T ^ (-ε)) * volume Q +
            ENNReal.ofReal (C * T ^ (-ε)) * volume Q := add_le_add H₁ H₂
        _ = ENNReal.ofReal (2 * (C * T ^ (-ε))) * volume Q := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), two_mul]
        _ ≤ ENNReal.ofReal 2⁻¹ * volume Q := by gcongr
    have h2 : ENNReal.ofReal 2⁻¹ * volume Q < volume Q := by
      conv_rhs => rw [← one_mul (volume Q)]
      exact ENNReal.mul_lt_mul_left hpos.ne' hfin
        (by rw [ENNReal.ofReal_lt_one]; norm_num)
    exact (hle.trans_lt h2).false
  rw [not_and_or] at hnot
  push Not at hnot
  have hδL : (1 - (2 * T)⁻¹) * L = L - s := by
    simp only [s]
    ring
  have hK : 0 ≤ ε₀⁻¹ * ρ * F / lam := by positivity
  rcases hnot with h₁ | h₂
  · -- `u > m + s` on `closedBall c (ρ / 4)`.
    refine ⟨m + s, fun x hx ↦ ?_⟩
    have h := hmem x (hρ4 hx)
    have hv := h₁ x (hsub hx)
    have : s < u x - m := by
      rwa [lt_inv_mul_iff₀ hs, mul_one] at hv
    exact ⟨by linarith, by linarith [h.2]⟩
  · -- `u < m + L - s` on `closedBall c (ρ / 4)`.
    refine ⟨m, fun x hx ↦ ?_⟩
    have h := hmem x (hρ4 hx)
    have hv := h₂ x (hsub hx)
    have : s < m + L - u x := by
      rwa [lt_inv_mul_iff₀ hs, mul_one] at hv
    exact ⟨h.1, by linarith⟩

/-- **Iterated oscillation decay.** There are `1 / 2 ≤ θ < 1` and `K ≥ 0`, depending only on the
dimension and on `κ`, with the following property. Under the hypotheses of
`exists_mem_Icc_closedBall_div_four`, for every `j` the function `u` takes values on
`closedBall c (ρ / 4ʲ)` in an interval of length `θʲ (L + K ρ F / λ)`. -/
private theorem exists_mem_Icc_closedBall_div_four_pow {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ K : ℝ, 2⁻¹ ≤ θ ∧ θ < 1 ∧ 0 ≤ K ∧
      ∀ ⦃lam Lam ρ m L F : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < ρ → 0 ≤ F →
        UniformlyEllipticOn (ball c ρ) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c ρ) → ContDiffOn ℝ 2 u (ball c ρ) →
        (∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = f x) →
        eLpNorm f (Fintype.card ι) (volume.restrict (ball c ρ)) ≤ ENNReal.ofReal F →
        (∀ x ∈ closedBall c ρ, u x ∈ Icc m (m + L)) →
        ∀ j : ℕ, ∃ m', ∀ x ∈ closedBall c (ρ / 4 ^ j),
          u x ∈ Icc m' (m' + θ ^ j * (L + K * ρ * F / lam)) := by
  obtain ⟨δ, K, hδ0, hδ1, hK, H⟩ := exists_mem_Icc_closedBall_div_four (ι := ι) hκ
  refine ⟨max (1 - δ) 2⁻¹, 4 * K, le_max_right _ _, max_lt (by linarith) (by norm_num),
    by positivity, ?_⟩
  intro lam Lam ρ m L F c a u f hρ hF ha hLam hcont hu heq hf hmem
  have hlam : 0 < lam := ha.pos
  set θ := max (1 - δ) 2⁻¹
  have hθ1 : 1 - δ ≤ θ := le_max_left _ _
  have hθ2 : 2⁻¹ ≤ θ := le_max_right _ _
  -- Induction on `j`, carrying the length `L'` of the interval together with the bound
  -- `L' + 4 K (ρ / 4ʲ) F / λ ≤ θʲ (L + 4 K ρ F / λ)`.
  suffices h : ∀ j : ℕ, ∃ m' L', L' + 4 * K * (ρ / 4 ^ j) * F / lam ≤
      θ ^ j * (L + 4 * K * ρ * F / lam) ∧ ∀ x ∈ closedBall c (ρ / 4 ^ j), u x ∈ Icc m' (m' + L') by
    intro j
    obtain ⟨m', L', hL', hmem'⟩ := h j
    refine ⟨m', fun x hx ↦ ⟨(hmem' x hx).1, (hmem' x hx).2.trans ?_⟩⟩
    have : 0 ≤ 4 * K * (ρ / 4 ^ j) * F / lam := by positivity
    linarith
  intro j
  induction j with
  | zero => exact ⟨m, L, by simp, by simpa using hmem⟩
  | succ j ih =>
    obtain ⟨m', L', hL', hmem'⟩ := ih
    set ρj := ρ / 4 ^ j
    have hρj : 0 < ρj := by positivity
    have hρjρ : ρj ≤ ρ := div_le_self hρ.le (one_le_pow₀ (by norm_num))
    have hsub : ball c ρj ⊆ ball c ρ := ball_subset_ball hρjρ
    have hcsub : closedBall c ρj ⊆ closedBall c ρ := closedBall_subset_closedBall hρjρ
    have hL'0 : 0 ≤ L' := by
      have h := hmem' c (mem_closedBall_self hρj.le)
      linarith [h.1, h.2]
    obtain ⟨m'', hm''⟩ := H hρj hF (ha.mono_set hsub) hLam (hcont.mono hcsub) (hu.mono hsub)
      (fun x hx ↦ heq x (hsub hx))
      ((eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans hf) hmem'
    have h4 : ρ / 4 ^ (j + 1) = ρj / 4 := by
      rw [pow_succ, ← div_div]
    refine ⟨m'', (1 - δ) * L' + K * ρj * F / lam, ?_, h4 ▸ hm''⟩
    rw [h4, pow_succ]
    have hKF : 0 ≤ K * ρj * F / lam := by positivity
    have e1 : (1 - δ) * L' ≤ θ * L' := mul_le_mul_of_nonneg_right hθ1 hL'0
    have e2 : 2 * (K * ρj * F / lam) ≤ θ * (4 * (K * ρj * F / lam)) := by nlinarith
    have hθ0 : 0 ≤ θ := by linarith
    calc (1 - δ) * L' + K * ρj * F / lam + 4 * K * (ρj / 4) * F / lam
        = (1 - δ) * L' + 2 * (K * ρj * F / lam) := by ring
      _ ≤ θ * L' + θ * (4 * (K * ρj * F / lam)) := by linarith
      _ = θ * (L' + 4 * K * ρj * F / lam) := by ring
      _ ≤ θ * (θ ^ j * (L + 4 * K * ρ * F / lam)) := mul_le_mul_of_nonneg_left hL' hθ0
      _ = θ ^ j * θ * (L + 4 * K * ρ * F / lam) := by ring

/-- **The interior Hölder estimate of Krylov and Safonov** (Gilbarg–Trudinger, Corollary 9.24,
for classical solutions). Let `κ > 0`. There are `0 < α ≤ 1` and `C > 0`, depending only on the
dimension and on `κ`, with the following property. Let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u` be `C²` in `B(x₀, 2 r)` with `|u| ≤ M`
and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` there, where `f ∈ Lⁿ(B(x₀, 2 r))`. Then `u` is `α`-Hölder on `B(x₀, r)`
with constant `C r^(-α) (M + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq {κ : ℝ} (hκ : 0 < κ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ ⦃lam Lam r M : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < r →
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContDiffOn ℝ 2 u (ball x₀ (2 * r)) → (∀ x ∈ ball x₀ (2 * r), |u x| ≤ M) →
        (∀ x ∈ ball x₀ (2 * r), ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (M + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam)).toNNReal α u (ball x₀ r) := by
  obtain ⟨θ, K, hθ2, hθ1, hK, H⟩ := exists_mem_Icc_closedBall_div_four_pow (ι := ι) hκ
  have hθ0 : 0 < θ := by linarith
  -- The exponent `α = log₄ θ⁻¹`, so that `4^α = θ⁻¹`.
  set α := Real.logb 4 θ⁻¹
  have hα0 : 0 < α := Real.logb_pos (by norm_num) ((one_lt_inv₀ hθ0).2 hθ1)
  have hα1 : α ≤ 1 := by
    have h : θ⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hθ0 (by norm_num)]
      linarith
    calc α ≤ Real.logb 4 4 := (Real.logb_le_logb (by norm_num) (by positivity) (by norm_num)).2 h
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  have h4α : (4 : ℝ) ^ α = θ⁻¹ := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  refine ⟨⟨α, hα0.le⟩, 4 * max 2 K, hα0, by exact_mod_cast hα1, by positivity, ?_⟩
  intro lam Lam r M x₀ a u f hr ha hLam hu hM heq hf
  have hlam : 0 < lam := ha.pos
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hfF : eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) = ENNReal.ofReal F :=
    (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_ball_self (by linarith)))
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  -- `u` takes values in `[-M, M]`, and the oscillation decays on the balls about `x`.
  have hxball : closedBall x r ⊆ ball x₀ (2 * r) := fun z hz ↦ by
    rw [mem_closedBall] at hz
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle z x x₀]
  have hsub : ball x r ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hxball
  have hdec := H hr hF (ha.mono_set hsub) hLam (hu.continuousOn.mono hxball) (hu.mono hsub)
    (fun z hz ↦ heq z (hsub hz))
    (hfF ▸ eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
    (m := -M) (L := 2 * M) fun z hz ↦ by
      have h := abs_le.1 (hM z (hxball hz))
      exact ⟨h.1, by linarith [h.2]⟩
  set d := dist x y
  have hMF : 0 ≤ M + r * F / lam := by positivity
  have hrd : r ^ (-α) * d ^ α = (d / r) ^ α := by
    rw [Real.div_rpow dist_nonneg hr.le, Real.rpow_neg hr.le, div_eq_inv_mul]
  suffices key : dist (u x) (u y) ≤ 4 * max 2 K * ((d / r) ^ α * (M + r * F / lam)) by
    calc dist (u x) (u y) ≤ 4 * max 2 K * ((d / r) ^ α * (M + r * F / lam)) := key
      _ = 4 * max 2 K * r ^ (-α) * (M + r * F / lam) * d ^ α := by rw [← hrd]; ring
  have hΨ : 2 * M + K * r * F / lam ≤ max 2 K * (M + r * F / lam) := by
    have h1 : 2 * M ≤ max 2 K * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
    have h2 : K * (r * F / lam) ≤ max 2 K * (r * F / lam) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    rw [mul_add]
    calc 2 * M + K * r * F / lam = 2 * M + K * (r * F / lam) := by ring
      _ ≤ _ := add_le_add h1 h2
  rcases lt_or_ge d r with hdr | hdr
  · rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ d) with hd0 | hd0
    · rw [dist_eq_zero.1 hd0.symm, dist_self]
      positivity
    -- The scale `4ʲ ≤ r / d < 4ʲ⁺¹`.
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := r / d) (y := 4)
      ((one_le_div hd0).2 hdr.le) (by norm_num)
    obtain ⟨m', hm'⟩ := hdec j
    have hdj : d ≤ r / 4 ^ j := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hd0] at hj1
      linarith
    have hxj : x ∈ closedBall x (r / 4 ^ j) := mem_closedBall_self (by positivity)
    have hyj : y ∈ closedBall x (r / 4 ^ j) := by
      rw [mem_closedBall, dist_comm]
      exact hdj
    have hdist : dist (u x) (u y) ≤ θ ^ j * (2 * M + K * r * F / lam) := by
      have h := Real.dist_le_of_mem_Icc (hm' x hxj) (hm' y hyj)
      linarith
    -- `θʲ = (4ʲ)^(-α) ≤ 4 (d / r)^α`.
    have hθj : θ ^ j ≤ 4 * (d / r) ^ α := by
      have hθ : θ = ((4 : ℝ) ^ α)⁻¹ := by rw [h4α, inv_inv]
      have hr4 : r / (4 * d) ≤ 4 ^ j := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd0, pow_succ] at hj2
        linarith
      calc θ ^ j = (((4 : ℝ) ^ j) ^ α)⁻¹ := by
            rw [hθ, inv_pow, Real.rpow_pow_comm (by norm_num)]
        _ ≤ ((r / (4 * d)) ^ α)⁻¹ :=
            inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hr4 hα0.le)
        _ = 4 ^ α * (d / r) ^ α := by
            rw [← Real.inv_rpow (by positivity), inv_div, ← Real.mul_rpow (by norm_num)
              (by positivity)]
            ring_nf
        _ ≤ 4 * (d / r) ^ α := by
            gcongr
            calc (4 : ℝ) ^ α ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
              _ = 4 := Real.rpow_one 4
    calc dist (u x) (u y) ≤ θ ^ j * (2 * M + K * r * F / lam) := hdist
      _ ≤ 4 * (d / r) ^ α * (max 2 K * (M + r * F / lam)) := by gcongr
      _ = 4 * max 2 K * ((d / r) ^ α * (M + r * F / lam)) := by ring
  · -- At distance at least `r` the bound `|u| ≤ M` suffices.
    have h1 : 1 ≤ (d / r) ^ α := Real.one_le_rpow ((one_le_div hr).2 hdr) hα0.le
    have hux := abs_le.1 (hM x (ball_subset_ball (by linarith) hx))
    have huy := abs_le.1 (hM y (ball_subset_ball (by linarith) hy))
    have hdist : dist (u x) (u y) ≤ 2 * M := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    have h2K : 2 ≤ max 2 K := le_max_left _ _
    have hrF : 0 ≤ r * F / lam := by positivity
    calc dist (u x) (u y) ≤ 2 * M := hdist
      _ ≤ 4 * max 2 K * (1 * (M + r * F / lam)) := by nlinarith
      _ ≤ 4 * max 2 K * ((d / r) ^ α * (M + r * F / lam)) := by gcongr

end PDE

end TauCeti
