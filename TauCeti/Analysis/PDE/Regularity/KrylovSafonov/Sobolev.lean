/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Power decay for strong supersolutions

The Krylov–Safonov power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`
is proved for classical supersolutions: functions `C²` in a ball satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` at
every point. Equations with measurable coefficients have, in general, only strong solutions:
functions `u ∈ W^{2,n}`, `n` the dimension, with a continuous representative `ū`, satisfying the
inequality almost everywhere with the weak Hessian `D²u`. This file proves the power decay for
them, by approximation with classical supersolutions.

The approximation step does not depend on the estimate. Mollifying `u` gives smooth functions `v`
close to `ū` uniformly on a compact set `K` and with Hessians close to `D²u` in `Lᵖ(K)`
(`TauCeti.Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le`). With the same
coefficients, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ f + N ‖D²v - D²u‖` almost everywhere, where `N` depends only on the
dimension and a bound for the entries of the coefficients. So `v` is a classical supersolution
with a right-hand side whose positive part is at most `‖f⁺‖_{Lᵖ} + η` in `Lᵖ`
(`TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp`). No regularity or
measurability of the coefficients is needed.

The power decay reads: if `u ≥ 0` is a strong supersolution near the closed ball `B(c, R)`,
centred at the centre of a dyadic cube `Q₀` of side `ℓ` with `R ≥ 4 ℓ √n`, with `ū ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then

`|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`), for coefficients with
ellipticity constants `λ ≤ Λ ≤ κ λ` and with `C`, `ε` and `ε₀` depending only on `n` and `κ`. It is
the step from the measure estimate to the weak Harnack inequality and to the interior Hölder
estimate of Krylov and Safonov for strong solutions.

## The argument

Given `ζ > 0`, take an approximation `v` with `|v - ū| ≤ ζ` on `closedBall c R` and an `Lⁿ` error
in the right-hand side at most `ζ ε₀ λ / R`. The function `w = (v + ζ) / (1 + 3 ζ)` is nonnegative
on the closed ball, at most `1` where `ū ≤ 1`, and a classical supersolution with right-hand side
small enough for the classical power decay. On `Q₀ ⊆ closedBall c R`, `w ≥ ū / (1 + 3 ζ)`, so
`{ū ≥ t} ∩ Q₀` lies in the superlevel set of `w` at `t / (1 + 3 ζ)`. Letting `ζ → 0` gives the
bound at `t`.

## Main declarations

* `TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp`: a strong
  supersolution is uniformly approximated by smooth classical supersolutions whose right-hand
  sides have nearly the same `Lᵖ` norm of the positive part.
* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: the power decay
  `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for strong supersolutions.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions).
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6.
* L. C. Evans, *Partial Differential Equations*, §5.3.1 (interior mollification).
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Approximation of a strong supersolution by classical ones.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`,
have a representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth function `v` with
`|v - ū| ≤ η` on `K` and a function `g` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ g` at every point of `S` and
`‖g⁺‖_{Lᵖ(S)} ≤ ‖f⁺‖_{Lᵖ(S)} + η`. The coefficients need not be measurable. -/
theorem exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp volume Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ v g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (volume.restrict S) ≤
        eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) + ENNReal.ofReal η := by
  -- `N` bounds the contraction with `a` of an endomorphism of norm one.
  set N : ℝ := (Fintype.card ι : ℝ) ^ 2 * max Λ 0 + 1
  have hN : 0 < N := by positivity
  have hN1 : 1 ≤ N := le_add_of_nonneg_left (by positivity)
  obtain ⟨v, hv, hvK, hvH⟩ := Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le hp
    u hcont hū hK hKΩ (div_pos hη hN)
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun x ↦ fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x
  set L : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  -- Off a null set of `S`, the principal part of `v` exceeds that of `u` by at most `N ‖D‖`.
  have hL : ∀ᵐ x ∂volume.restrict S, L x ≤ (f x)⁺ + N * ‖D x‖ := by
    filter_upwards [hf, ha] with x hfx hax
    -- `L x` is the contraction of `fderiv (∇ v) x = D²u(x) + D x` with `a x`.
    have hLx : L x =
        ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i +
          ∑ i, ∑ j, a x i j * D x (EuclideanSpace.single j 1) i := by
      simp only [L, D, ← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hessianOperator_single_apply ((contDiff_infty.1 hv 2).contDiffAt), ← fderiv_gradient]
      simp
    have hD : ∑ i, ∑ j, a x i j * D x (EuclideanSpace.single j 1) i ≤ N * ‖D x‖ := by
      refine (le_abs_self _).trans ((Matrix.abs_sum_sum_mul_apply_single_le _ _).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ∑ i, ∑ j, |a x i j| ≤ ∑ _i : ι, ∑ _j : ι, max Λ 0 :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hax i j).trans
              (le_max_left _ _)
        _ ≤ N := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            nlinarith [le_max_right Λ 0]
    rw [hLx]
    exact add_le_add (hfx.trans (le_max_left _ _)) hD
  refine ⟨v, fun x ↦ max (L x) ((f x)⁺ + N * ‖D x‖), hv,
    fun y hy ↦ (hvK y hy).trans (div_le_self hη.le hN1), fun x _ ↦ le_max_left _ _, ?_⟩
  -- Almost everywhere on `S` the maximum is its nonnegative second argument.
  have hae : (fun x ↦ (max (L x) ((f x)⁺ + N * ‖D x‖))⁺) =ᵐ[volume.restrict S]
      (fun x ↦ (f x)⁺) + N • fun x ↦ ‖D x‖ := by
    filter_upwards [hL] with x hx
    rw [max_eq_right hx, posPart_eq_self.2 (by positivity)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hD : AEStronglyMeasurable D (volume.restrict S) :=
    (measurable_fderiv ℝ (∇ v)).aestronglyMeasurable.sub ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hSK.trans hKΩ) le_rfl))
  have hDK : eLpNorm (fun x ↦ ‖D x‖) p (volume.restrict S) ≤ ENNReal.ofReal (η / N) := by
    rw [eLpNorm_norm _ hD]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hSK le_rfl)).trans hvH
  calc _ = eLpNorm ((fun x ↦ (f x)⁺) + N • fun x ↦ ‖D x‖) p (volume.restrict S) :=
        eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) +
          ‖N‖ₑ * eLpNorm (fun x ↦ ‖D x‖) p (volume.restrict S) := by
        rw [← eLpNorm_const_smul]
        exact eLpNorm_add_le Fact.out
    _ ≤ eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) +
          ENNReal.ofReal N * ENNReal.ofReal (η / N) := by
        rw [Real.enorm_eq_ofReal hN.le]
        gcongr
    _ = eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) + ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_mul hN.le, mul_div_cancel₀ _ hN.ne']

/-- **Power decay of the superlevel sets of a strong supersolution** (Gilbarg–Trudinger,
Section 9.7; Caffarelli–Cabré, Lemma 4.6). Let `κ > 0`. There are constants `C > 0`, `ε > 0` and
`ε₀ > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following property. Let
`Q₀` be a dyadic cube of level `k`, so of side `2ᵏ`, with centre `c`, let `R ≥ 4 · 2ᵏ √n`, and let
`Ω` be an open set containing `closedBall c R`. Let the coefficient matrix `a` be uniformly
elliptic on `B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` have a representative
`ū` continuous on `Ω` and nonnegative on `closedBall c R`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost
everywhere in `B(c, R)` for the weak Hessian and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `ū ≤ 1`
somewhere in `B(c, 2 · 2ᵏ √n)`, then `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`. The
coefficients need not be measurable or symmetric. -/
theorem exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄ (u : Wkp volume Ω (Fintype.card ι) 2),
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R → closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), ū x ≤ 1) →
        ∀ ⦃t : ℝ⦄, 0 < t → volume ({x | t ≤ ū x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (C * t ^ (-ε)) *
            volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
  -- The classical estimate is applied, for each `ζ > 0`, to a mollification of `u` shifted up by
  -- `ζ` and divided by `1 + 3 ζ` (`key`); then `ζ → 0`.
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  refine ⟨C, ε, ε₀, hC, hε, hε₀, ?_⟩
  intro lam Lam R k m c Ω a ū f u hc hR hRΩ ha hLam hcont hū hnonneg hsuper hf hx t ht
  set n := Fintype.card ι
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k m
  have hn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hk : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hlam : 0 < lam := ha.pos
  have hQ : Q ⊆ closedBall c R := fun y hy ↦ by
    have h := dist_toLp_lt_of_mem_dyadicCube hy (centre_mem_dyadicCube k m)
    rw [WithLp.toLp_ofLp, ← hc] at h
    rw [mem_closedBall]
    nlinarith [mul_pos hk hn]
  obtain ⟨x₀, hx₀, hux₀⟩ := hx
  have hx₀R : x₀ ∈ closedBall c R :=
    ball_subset_closedBall (ball_subset_ball (by nlinarith [mul_pos hk hn]) hx₀)
  -- For every `ζ > 0` the classical estimate, applied to a mollification of `u` shifted up by
  -- `ζ` and divided by `1 + 3 ζ`, bounds the superlevel set at `t` by the value at `t / (1 + 3 ζ)`.
  have key : ∀ ζ > 0, volume ({x | t ≤ ū x} ∩ Q) ≤
      ENNReal.ofReal (C * (t / (1 + 3 * ζ)) ^ (-ε)) * volume Q := by
    intro ζ hζ
    set η := min ζ (ζ * (ε₀ * lam) / R)
    have hη : 0 < η := lt_min hζ (by positivity)
    obtain ⟨v, g, hv, hvū, hvg, hg⟩ :=
      exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp (ENNReal.natCast_ne_top n) u
        hcont hū (isCompact_closedBall c R) hRΩ ball_subset_closedBall
        ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ha.abs_apply_le hx) hsuper hη
    set σ := 1 + 3 * ζ
    have hσ : 0 < σ := by positivity
    have hv2 : ContDiff ℝ 2 v := contDiff_infty.1 hv 2
    have hvū' (y : EuclideanSpace ℝ ι) (hy : y ∈ closedBall c R) : |v y - ū y| ≤ ζ :=
      (hvū y hy).trans (min_le_left _ _)
    -- The principal part of `w = (v + ζ) / σ` is that of `v` divided by `σ`.
    have hsum (x : EuclideanSpace ℝ ι) : ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ fun y ↦
          σ⁻¹ * (v y + ζ)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        σ⁻¹ * ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      rw [sum_mul_fderiv_fderiv_const_mul]
      have h : fderiv ℝ (fun y ↦ v y + ζ) = fderiv ℝ v := funext fun y ↦ fderiv_add_const ζ
      rw [h]
    -- The right-hand side `g / σ` is small enough.
    have hgσ : ENNReal.ofReal R * eLpNorm (fun x ↦ (σ⁻¹ * g x)⁺) n
        (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) := by
      have hpos : (fun x ↦ (σ⁻¹ * g x)⁺) = σ⁻¹ • fun x ↦ (g x)⁺ := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _
          (inv_pos.2 hσ).le, mul_zero]
      have hRη : R * η ≤ ζ * (ε₀ * lam) := by
        calc R * η ≤ R * (ζ * (ε₀ * lam) / R) := mul_le_mul_of_nonneg_left (min_le_right _ _)
              hR0.le
          _ = ζ * (ε₀ * lam) := mul_div_cancel₀ _ hR0.ne'
      calc ENNReal.ofReal R * eLpNorm (fun x ↦ (σ⁻¹ * g x)⁺) n (volume.restrict (ball c R))
          = ENNReal.ofReal σ⁻¹ *
              (ENNReal.ofReal R * eLpNorm (fun x ↦ (g x)⁺) n (volume.restrict (ball c R))) := by
            rw [hpos, eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_pos.2 hσ).le]
            ring
        _ ≤ ENNReal.ofReal σ⁻¹ * (ENNReal.ofReal (ε₀ * lam) + ENNReal.ofReal (R * η)) := by
            gcongr
            calc ENNReal.ofReal R * eLpNorm (fun x ↦ (g x)⁺) n (volume.restrict (ball c R))
                ≤ ENNReal.ofReal R * (eLpNorm (fun x ↦ (f x)⁺) n (volume.restrict (ball c R)) +
                    ENNReal.ofReal η) := by gcongr
              _ ≤ ENNReal.ofReal (ε₀ * lam) + ENNReal.ofReal (R * η) := by
                  rw [mul_add, ENNReal.ofReal_mul hR0.le]
                  gcongr
        _ = ENNReal.ofReal (σ⁻¹ * (ε₀ * lam + R * η)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (inv_pos.2 hσ).le]
        _ ≤ ENNReal.ofReal (ε₀ * lam) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [inv_mul_le_iff₀ hσ]
            nlinarith [mul_pos hε₀ hlam]
    have hw := H (u := fun y ↦ σ⁻¹ * (v y + ζ)) (f := fun x ↦ σ⁻¹ * g x) hc hR ha hLam
      (continuousOn_const.mul ((hv2.continuous.add continuous_const).continuousOn))
      (contDiffOn_const.mul (hv2.add contDiff_const).contDiffOn)
      (fun y hy ↦ mul_nonneg (inv_pos.2 hσ).le (by
        linarith [hnonneg y hy, (abs_le.1 (hvū' y hy)).1]))
      (fun x hx ↦ by
        rw [hsum]
        exact mul_le_mul_of_nonneg_left (hvg x hx) (inv_pos.2 hσ).le)
      hgσ
      ⟨x₀, hx₀, by
        rw [inv_mul_le_iff₀ hσ]
        linarith [(abs_le.1 (hvū' x₀ hx₀R)).2]⟩
      (div_pos ht hσ)
    refine le_trans (measure_mono fun y hy ↦ ?_) hw
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, hy2⟩
    -- On the cube, `w ≥ ū / σ`.
    rw [mem_ofPred_eq] at hy1 ⊢
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hvū' y (hQ hy2))).1])
      (inv_pos.2 hσ).le
  -- Let `ζ → 0`.
  have hQfin : volume Q ≠ ∞ :=
    ((measure_mono hQ).trans_lt measure_closedBall_lt_top).ne
  have hlim : Tendsto (fun ζ : ℝ ↦ ENNReal.ofReal (C * (t / (1 + 3 * ζ)) ^ (-ε)) * volume Q)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (C * t ^ (-ε)) * volume Q)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hQfin)
    refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have h : ContinuousAt (fun ζ : ℝ ↦ C * (t / (1 + 3 * ζ)) ^ (-ε)) 0 := by
      refine continuousAt_const.mul (ContinuousAt.rpow_const ?_ (Or.inl (by simp [ht.ne'])))
      exact continuousAt_const.div (by fun_prop) (by norm_num)
    simpa using h.tendsto
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ζ hζ ↦ key ζ hζ)

end PDE

end TauCeti
