/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.MeasureEstimate
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.SpecificLimits.GeometricLevels
import TauCeti.MeasureTheory.Integral.CalderonZygmund.KrylovSafonov
import TauCeti.MeasureTheory.Measure.InterComplement

/-!
# The power decay of Krylov and Safonov

Let `u ≥ 0` be a `C²` supersolution of a non-divergence-form equation `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f`, with
`a` uniformly elliptic with constants `λ ≤ Λ ≤ κ λ`, on a ball `B(x₀, K r) ⊆ ℝⁿ`, `n ≥ 1`. If
`u ≤ 1` somewhere in `B(x₀, r)` and the right-hand side is small,
`r ‖f⁺‖_{Lⁿ(B(x₀, K r))} ≤ ε₀ λ`, then the superlevel sets of `u` decay like a power:

`|{u ≥ t} ∩ B(x₀, r)| ≤ C t^(-ε) |B(x₀, r)|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_ball_le_rpow_mul_volume_ball`). The constants
`K, C, ε, ε₀ > 0` depend only on the dimension and on `κ`. Integrated over `t`, the bound
controls the averages of `u^p` on `B(x₀, r)` for `p < ε`; this is the input to the weak Harnack
inequality, from which the Harnack inequality and the interior Hölder estimate of Krylov and
Safonov follow.

## The argument

The proof iterates the basic measure estimate
(`TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`) through the Krylov–Safonov
covering lemma on dyadic cubes (`TauCeti.volume_le_pow_mul_volume_dyadicCube`). For a dyadic
cube `Q` of side `s`, let `B_Q` be the ball of radius `8 n s` about its centre. The measure
estimate on `B_Q`, applied to `u / t`, says that if `u ≤ t` somewhere in the parent of `Q`, then
`u < M t` on a fixed fraction of `Q`, that is `|{u ≥ M t} ∩ Q| ≤ δ |Q|` with `δ < 1`. Every such
ball `B_Q` for a dyadic subcube `Q` of a cube `Q₀` lies in `B_{Q₀}`, so the hypotheses on
`B_{Q₀}` serve all scales at once; the smallness of `f` only improves on smaller balls. The
covering lemma, applied to the sets `Aⱼ = {u ≥ M^(j+1)} ∩ Q₀`, then gives the geometric decay
`|{u ≥ M^j} ∩ Q₀| ≤ δ^j |Q₀|`, which is the power decay with `ε = log (1/δ) / log M`
(`TauCeti.le_ofReal_inv_mul_rpow_mul_of_forall_le_pow_mul`). The ball `B(x₀, r)` is placed inside
a translate of a dyadic cube of side comparable to `r`.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_le_inter_ball_le_rpow_mul_volume_ball`: **the power decay**
  of the superlevel sets of a nonnegative supersolution.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

open Metric MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*}

variable [Fintype ι]

/-- A point whose image in `EuclideanSpace ℝ ι`, translated by `w`, is within `2ᵏ / 2` of the
translated centre of a dyadic cube of level `k` lies in that cube. -/
private theorem preimage_ball_subset_dyadicCube (k : ℤ) (m : ι → ℤ) (w : EuclideanSpace ℝ ι) :
    (fun y : ι → ℝ ↦ WithLp.toLp 2 y + w) ⁻¹'
      ball (WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) + w) (2 ^ k / 2) ⊆
      dyadicCube k m := fun y hy ↦ by
  rw [mem_preimage, mem_ball, dist_add_right] at hy
  exact ball_subset_dyadicCube k m (PiLp.ball_subset_preimage_ofLp_ball _ _ hy)

/-- Points of a dyadic cube of level `j`, mapped to `EuclideanSpace ℝ ι` and translated by `w`, are
at distance less than `n 2ʲ`. -/
private theorem dist_toLp_add_lt_of_mem_dyadicCube [Nonempty ι] {j : ℤ} {m : ι → ℤ}
    {a b : ι → ℝ} (ha : a ∈ dyadicCube j m) (hb : b ∈ dyadicCube j m) (w : EuclideanSpace ℝ ι) :
    dist (WithLp.toLp 2 a + w) (WithLp.toLp 2 b + w) < Fintype.card ι * 2 ^ j := by
  have hN : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  rw [dist_add_right]
  refine (PiLp.dist_le_sqrt_card_mul_dist_ofLp _ _).trans_lt ?_
  calc Real.sqrt (Fintype.card ι) * dist a b < Real.sqrt (Fintype.card ι) * 2 ^ j :=
        mul_lt_mul_of_pos_left (dist_lt_of_mem_dyadicCube ha hb) (by positivity)
    _ ≤ Fintype.card ι * 2 ^ j := by gcongr; exact Real.sqrt_le_self_iff.2 (Or.inr hN)

/-- A translated dyadic cube of level `k` lies in the closed ball of radius `8 n 2ᵏ` about its
translated centre. -/
private theorem toLp_add_mem_closedBall_of_mem_dyadicCube [Nonempty ι] {k : ℤ} {m : ι → ℤ}
    {c w : EuclideanSpace ℝ ι} {R : ℝ} {y : ι → ℝ}
    (hc : c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) + w)
    (hR : R = 8 * Fintype.card ι * 2 ^ k) (hy : y ∈ dyadicCube k m) :
    WithLp.toLp 2 y + w ∈ closedBall c R := by
  refine mem_closedBall.2 ((hc ▸ dist_toLp_add_lt_of_mem_dyadicCube hy
    (center_mem_dyadicCube k m) w).le.trans ?_)
  rw [hR]
  nlinarith [(by positivity : (0 : ℝ) < Fintype.card ι * 2 ^ k)]

/-- The balls attached to the dyadic subcubes of a cube `Q₀` lie in the ball attached to `Q₀`: if
`Q` has level `k < k₀` and lies in `Q₀`, the closed ball of radius `8 n 2ᵏ` about the centre of `Q`
lies in the open ball of radius `8 n 2^k₀` about the centre of `Q₀`. -/
private theorem closedBall_subset_ball_of_dyadicCube_subset [Nonempty ι] {k k₀ : ℤ}
    {m m₀ : ι → ℤ} (hk : k < k₀) (hQ : dyadicCube k m ⊆ dyadicCube k₀ m₀)
    (w : EuclideanSpace ℝ ι) :
    closedBall (WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) + w)
        (8 * Fintype.card ι * 2 ^ k) ⊆
      ball (WithLp.toLp 2 (fun i ↦ ((m₀ i : ℝ) + 2⁻¹) * 2 ^ k₀) + w)
        (8 * Fintype.card ι * 2 ^ k₀) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd := dist_toLp_add_lt_of_mem_dyadicCube (hQ (center_mem_dyadicCube k m))
    (center_mem_dyadicCube k₀ m₀) w
  have hk' : 2 * (2 : ℝ) ^ k ≤ 2 ^ k₀ := by
    rw [← zpow_one_add₀ two_ne_zero, add_comm]
    exact zpow_le_zpow_right₀ one_le_two (Int.add_one_le_iff.2 hk)
  refine closedBall_subset_ball' ?_
  nlinarith [(by positivity : (0 : ℝ) < Fintype.card ι * 2 ^ k₀)]

/-- Translating by `w` after passing from `ι → ℝ` to `EuclideanSpace ℝ ι` preserves volume. -/
private theorem volume_preimage_toLp_add (w : EuclideanSpace ℝ ι) (s : Set (EuclideanSpace ℝ ι)) :
    volume ((fun y : ι → ℝ ↦ WithLp.toLp 2 y + w) ⁻¹' s) = volume s :=
  MeasurePreserving.measure_preimage_equiv
    (f := (MeasurableEquiv.toLp 2 (ι → ℝ)).trans (MeasurableEquiv.addRight w))
    ((measurePreserving_add_right volume w).comp (PiLp.volume_preserving_toLp ι)) s

/-- The part of a dyadic cube on which `u (y + w) ≥ s` is measurable, when `u` is continuous on a
closed ball containing the translated cube. -/
private theorem measurableSet_setOf_le_inter_dyadicCube {u : EuclideanSpace ℝ ι → ℝ}
    {c w : EuclideanSpace ℝ ι} {R s : ℝ} {k : ℤ} {m : ι → ℤ} (hu : ContinuousOn u (closedBall c R))
    (hQ : ∀ y ∈ dyadicCube k m, WithLp.toLp 2 y + w ∈ closedBall c R) :
    MeasurableSet ({y | s ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k m) := by
  have he : Continuous fun y : ι → ℝ ↦ WithLp.toLp 2 y + w :=
    (PiLp.continuous_toLp 2 _).add continuous_const
  have hK : IsClosed ((fun y : ι → ℝ ↦ WithLp.toLp 2 y + w) ⁻¹' closedBall c R ∩
      (fun y ↦ u (WithLp.toLp 2 y + w)) ⁻¹' Ici s) :=
    (hu.comp he.continuousOn fun _ hy ↦ hy).preimage_isClosed_of_isClosed
      (isClosed_closedBall.preimage he) isClosed_Ici
  convert hK.measurableSet.inter (measurableSet_dyadicCube k m) using 1
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici]
  exact ⟨fun h ↦ ⟨⟨hQ y h.2, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩

/-- The volume `ω` of the unit ball is positive. -/
private theorem toReal_volume_ball_zero_one_pos :
    0 < (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The ball of radius `2ᵏ / 2` has volume `ω 2⁻ⁿ |Q|` for a dyadic cube `Q` of level `k`, where `ω`
is the volume of the unit ball. -/
private theorem volume_ball_eq_ofReal_mul_volume_dyadicCube (c : EuclideanSpace ℝ ι)
    (k : ℤ) (m : ι → ℤ) :
    volume (ball c (2 ^ k / 2)) = ENNReal.ofReal
      ((volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal / 2 ^ Fintype.card ι) *
        volume (dyadicCube k m) := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace, volume_dyadicCube,
    ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ ι))
      (r := 1)).ne, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  congr 1
  rw [div_pow]
  ring

/-- A dyadic cube of side `2ᵏ ≤ 4 r` has volume at most `4ⁿ / ω` times that of a ball of radius
`r`, where `ω` is the volume of the unit ball. -/
private theorem volume_dyadicCube_le_ofReal_mul_volume_ball {k : ℤ} {r : ℝ}
    (hr : 0 < r) (hk : (2 : ℝ) ^ k ≤ 4 * r) (m : ι → ℤ) (x : EuclideanSpace ℝ ι) :
    volume (dyadicCube k m) ≤ ENNReal.ofReal
      (4 ^ Fintype.card ι / (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal) *
        volume (ball x r) := by
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω := toReal_volume_ball_zero_one_pos
  have hB1 : volume (ball (0 : EuclideanSpace ℝ ι) 1) = ENNReal.ofReal ω :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  rw [volume_dyadicCube, Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace, hB1,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((2 : ℝ) ^ k) ^ Fintype.card ι ≤ (4 * r) ^ Fintype.card ι := by gcongr
    _ = _ := by field_simp; ring

/-- The scale-invariant size `R ‖g‖_{Lᵖ(B(x, R))}` of `g` on a ball of radius `R ≤ K r` is at most
`K` times its size `r ‖g‖_{Lᵖ(B(x, K r))}` on the larger ball. -/
private theorem ofReal_mul_eLpNorm_ball_le {g : EuclideanSpace ℝ ι → ℝ} {p : ℝ≥0∞}
    {x : EuclideanSpace ℝ ι} {R K r : ℝ} (hK : 0 ≤ K) (hRK : R ≤ K * r) :
    ENNReal.ofReal R * eLpNorm g p (volume.restrict (ball x R)) ≤
      ENNReal.ofReal K * (ENNReal.ofReal r * eLpNorm g p (volume.restrict (ball x (K * r)))) := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hK]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hRK)
    (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hRK) le_rfl))

variable [DecidableEq ι]

/-- Dividing a supersolution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ F` by `t ≥ 1` gives a supersolution with
right-hand side `F⁺`. -/
private theorem sum_mul_fderiv_fderiv_inv_smul_le_posPart {a : Matrix ι ι ℝ}
    {u : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} {t F : ℝ} (ht : 1 ≤ t)
    (h : ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ F) :
    ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ (t⁻¹ • u)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ F⁺ := by
  have ht0 : 0 < t := one_pos.trans_le ht
  have hsum : ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ (t⁻¹ • u)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = t⁻¹ * ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    simp only [fderiv_fderiv_const_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsum]
  calc t⁻¹ * _ ≤ t⁻¹ * F⁺ := by gcongr; exact h.trans (le_posPart F)
    _ ≤ F⁺ := mul_le_of_le_one_left (posPart_nonneg F) (inv_le_one_of_one_le₀ ht)

variable [Nonempty ι]

/-- **The measure estimate on dyadic cubes** (Caffarelli–Cabré, Lemma 4.5, in the scaled form
used in their Lemma 4.6). There are `M > 1`, `0 < δ < 1` and `ε₀ > 0`, depending only on the
dimension and `κ`, with the following property. Let `Q` be a dyadic cube of side `s = 2ᵏ`,
translated by `w` after passing to `EuclideanSpace ℝ ι`, with centre `c`, and let `R = 8 n s`.
Let `a` be uniformly elliptic on `B(c, R)` with `Λ ≤ κ λ`, and let `u` be continuous on
`closedBall c R`, `C²` in `B(c, R)`, nonnegative on the sphere, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` and
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `t ≥ 1` and `u ≤ t` somewhere in `B(c, R / 2)`, then
`|{u ≥ M t} ∩ Q| ≤ δ |Q|`. -/
private theorem exists_volume_setOf_le_inter_dyadicCube_le {κ : ℝ} (hκ : 0 < κ) :
    ∃ M δ ε₀ : ℝ, 1 < M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam t R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c w : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) + w →
        R = 8 * Fintype.card ι * 2 ^ k →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ sphere c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        1 ≤ t → (∃ x ∈ ball c (R / 2), u x ≤ t) →
        volume ({y | M * t ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k m) ≤
          ENNReal.ofReal δ * volume (dyadicCube k m) := by
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨M₀, μ, ε₀, -, hμ, hε₀, hME⟩ := exists_mul_volume_ball_le_volume_setOf_lt_inter_ball
    (ι := ι) hκ (θ := (16 * N)⁻¹) (τ := 2⁻¹) (by positivity) (by norm_num) (by norm_num)
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω := toReal_volume_ball_zero_one_pos
  set η := μ * ω / 2 ^ Fintype.card ι
  have hη : 0 < η := by positivity
  refine ⟨max M₀ 2, max (1 - η) 2⁻¹, ε₀, by simp, by positivity,
    max_lt (by linarith) (by norm_num), hε₀, ?_⟩
  intro lam Lam t R k m c w a u f hc hR ha hLam hcont hu hbdry hsuper hf ht ⟨x₁, hx₁, hux₁⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hR0 : 0 < R := by rw [hR]; positivity
  have hθR : (16 * N)⁻¹ * R = 2 ^ k / 2 := by rw [hR]; field_simp; ring
  -- The measure estimate for `u / t`, a supersolution with right-hand side `f⁺`.
  have key := hME hR0 ha hLam (hcont.const_smul t⁻¹) (hu.const_smul t⁻¹)
    (fun x hx ↦ by simpa using mul_nonneg (inv_pos.2 ht0).le (hbdry x hx))
    (fun x hx ↦ sum_mul_fderiv_fderiv_inv_smul_le_posPart ht (hsuper x hx))
    (by simpa only [posPart_nonneg, posPart_of_nonneg] using hf)
    ⟨x₁, (by rwa [← div_eq_inv_mul]), by simpa using (inv_mul_le_one₀ ht0).2 hux₁⟩
  rw [hθR] at key
  -- The ball of radius `s / 2` fills a fixed fraction `η` of the cube.
  have hball : ENNReal.ofReal η * volume (dyadicCube k m) =
      ENNReal.ofReal μ * volume (ball c (2 ^ k / 2)) := by
    rw [volume_ball_eq_ofReal_mul_volume_dyadicCube c k m, ← mul_assoc,
      ← ENNReal.ofReal_mul hμ.le]
    exact congrArg (ENNReal.ofReal · * _) (mul_div_assoc _ _ _)
  -- On that ball, `u / t < M₀` forces `u < M t`, so the complement of the superlevel set fills
  -- a fraction `η` of the cube.
  set A := {y : ι → ℝ | max M₀ 2 * t ≤ u (WithLp.toLp 2 y + w)}
  have hcompl : ENNReal.ofReal η * volume (dyadicCube k m) ≤ volume (dyadicCube k m \ A) := by
    rw [hball]
    refine key.trans ?_
    rw [← volume_preimage_toLp_add w]
    refine measure_mono fun y hy ↦ ?_
    obtain ⟨hyu, hyQ⟩ := hy
    simp only [Pi.smul_apply, smul_eq_mul] at hyu
    refine ⟨preimage_ball_subset_dyadicCube k m w (hc ▸ hyQ), fun hA ↦ ?_⟩
    have hA' : max M₀ 2 * t ≤ u (WithLp.toLp 2 y + w) := hA
    nlinarith [(inv_mul_lt_iff₀ ht0).1 hyu, mul_le_mul_of_nonneg_right (le_max_left M₀ 2) ht0.le]
  -- The superlevel set is measurable on the cube, so its measure there is the rest of `|Q|`.
  have hmeas : MeasurableSet (A ∩ dyadicCube k m) := measurableSet_setOf_le_inter_dyadicCube hcont
    fun y hy ↦ toLp_add_mem_closedBall_of_mem_dyadicCube hc hR hy
  refine (measure_inter_le_one_sub_mul hmeas.nullMeasurableSet (volume_dyadicCube_ne_top k m)
    hcompl).trans ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hη.le]
  gcongr
  exact le_max_left _ _

/-- **Geometric decay on a dyadic cube** (Caffarelli–Cabré, Lemma 4.6, in its discrete form).
There are `M > 1`, `0 < δ < 1` and `ε₀ > 0`, depending only on the dimension and `κ`, with the
following property. Let `Q` be a dyadic cube of side `s = 2ᵏ`, translated by `w` after passing to
`EuclideanSpace ℝ ι`, with centre `c`, and let `R = 8 n s`. Let `a` be uniformly elliptic on
`B(c, R)` with `Λ ≤ κ λ`, and let `u ≥ 0` be continuous on `closedBall c R`, `C²` in `B(c, R)`,
with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `u ≤ 1` somewhere in
`B(c, R / 2)`, then `|{u ≥ Mʲ} ∩ Q| ≤ δʲ |Q|` for every `j`. -/
private theorem exists_volume_setOf_pow_le_inter_dyadicCube_le {κ : ℝ} (hκ : 0 < κ) :
    ∃ M δ ε₀ : ℝ, 1 < M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c w : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) + w →
        R = 8 * Fintype.card ι * 2 ^ k →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (R / 2), u x ≤ 1) → ∀ j : ℕ,
        volume ({y | M ^ j ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k m) ≤
          ENNReal.ofReal δ ^ j * volume (dyadicCube k m) := by
  obtain ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, hcube⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le (ι := ι) hκ
  refine ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, ?_⟩
  intro lam Lam R k₀ m₀ c w a u f hc hR ha hLam hcont hu hnonneg hsuper hf hx₁ j
  rcases j with - | j
  · simpa using measure_mono inter_subset_right
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hQ₀ : ∀ y ∈ dyadicCube k₀ m₀, WithLp.toLp 2 y + w ∈ closedBall c R := fun _ hy ↦
    toLp_add_mem_closedBall_of_mem_dyadicCube hc hR hy
  -- The covering lemma, applied to the superlevel sets `Aⱼ = {u ≥ M^(j+1)} ∩ Q₀`.
  set A : ℕ → Set (ι → ℝ) := fun j ↦ {y | M ^ (j + 1) ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k₀ m₀
  refine volume_le_pow_mul_volume_dyadicCube (A := A)
    (fun j ↦ (measurableSet_setOf_le_inter_dyadicCube hcont hQ₀).nullMeasurableSet)
    (fun i j hij y hy ↦ ⟨(pow_le_pow_right₀ hM.le (by omega)).trans hy.1, hy.2⟩)
    (ENNReal.ofReal_lt_one.2 hδ1) inter_subset_right ?_ ?_ j
  · -- The first superlevel set is controlled by the measure estimate on `Q₀` itself.
    simpa [A] using hcube hc hR ha hLam hcont hu
      (fun x hx ↦ hnonneg x (sphere_subset_closedBall hx))
      hsuper hf le_rfl hx₁
  -- If `u < M^(j+1)` somewhere in the parent `P` of a subcube `Q`, the measure estimate on `Q`
  -- bounds the density of `A_(j+1)` in `Q` by `δ`.
  intro j k m m' hk hQ hQP hlt y hyP
  have hPQ₀ : dyadicCube (k + 1) m' ⊆ dyadicCube k₀ m₀ :=
    (dyadicCube_subset_or_disjoint (Int.add_one_le_iff.2 hk) m' m₀).resolve_right fun hdisj ↦
      (dyadicCube_nonempty k m).ne_empty (eq_empty_of_subset_empty (hdisj (hQP) hQ))
  refine ⟨?_, hPQ₀ hyP⟩
  by_contra hy
  have hsub := closedBall_subset_ball_of_dyadicCube_subset hk hQ w
  rw [← hc, ← hR] at hsub
  have hRk : 8 * (Fintype.card ι : ℝ) * 2 ^ k ≤ R := by
    have := (zpow_lt_zpow_iff_right₀ (one_lt_two (α := ℝ))).2 hk
    rw [hR]
    nlinarith
  have hball := ball_subset_closedBall.trans hsub
  have h := hcube rfl rfl (ha.mono_set hball) hLam (hcont.mono (hsub.trans ball_subset_closedBall))
    (hu.mono hball)
    (fun x hx ↦ hnonneg x (ball_subset_closedBall (hsub (sphere_subset_closedBall hx))))
    (fun x hx ↦ hsuper x (hball hx))
    ((mul_le_mul' (ENNReal.ofReal_le_ofReal hRk) (eLpNorm_mono_measure _
      (Measure.restrict_mono hball le_rfl))).trans hf)
    (one_le_pow₀ hM.le) ⟨WithLp.toLp 2 y + w, ?_, (not_le.1 hy).le⟩
  · have hAQ : A (j + 1) ∩ dyadicCube k m ⊆
        {z | M * M ^ (j + 1) ≤ u (WithLp.toLp 2 z + w)} ∩ dyadicCube k m :=
      fun z hz ↦ ⟨by simpa [pow_succ, mul_comm] using hz.1.1, hz.2⟩
    exact hlt.not_ge ((measure_mono hAQ).trans h)
  · rw [mem_ball]
    refine (dist_toLp_add_lt_of_mem_dyadicCube hyP (hQP (center_mem_dyadicCube k m)) w).trans_le ?_
    rw [zpow_add_one₀ two_ne_zero]
    nlinarith [(by positivity : (0 : ℝ) < Fintype.card ι * 2 ^ k)]

/-- **The power decay of Krylov and Safonov** (Caffarelli–Cabré, Lemma 4.6, for classical
supersolutions of linear equations). Let `κ > 0`. There are constants `K ≥ 1` and `C, ε, ε₀ > 0`,
depending only on the dimension and `κ`, with the following property. Let `r > 0`, let `a` be
uniformly elliptic on `B(x₀, K r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be continuous on
`closedBall x₀ (K r)` and `C²` in `B(x₀, K r)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and
`r ‖f⁺‖_{Lⁿ(B(x₀, K r))} ≤ ε₀ λ`. If `u ≤ 1` somewhere in `B(x₀, r)`, then for every `t > 0`,
`|{u ≥ t} ∩ B(x₀, r)| ≤ C t^(-ε) |B(x₀, r)|`.

As in `TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`, no measurability,
continuity or symmetry of `a` is assumed. -/
theorem exists_volume_setOf_le_inter_ball_le_rpow_mul_volume_ball {κ : ℝ} (hκ : 0 < κ) :
    ∃ K C ε ε₀ : ℝ, 1 ≤ K ∧ 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam r t : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < r →
        UniformlyEllipticOn (ball x₀ (K * r)) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall x₀ (K * r)) → ContDiffOn ℝ 2 u (ball x₀ (K * r)) →
        (∀ x ∈ closedBall x₀ (K * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (K * r), ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal r * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball x₀ (K * r))) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball x₀ r, u x ≤ 1) → 0 < t →
        volume ({x | t ≤ u x} ∩ ball x₀ r) ≤
          ENNReal.ofReal (C * t ^ (-ε)) * volume (ball x₀ r) := by
  obtain ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, hdecay⟩ :=
    exists_volume_setOf_pow_le_inter_dyadicCube_le (ι := ι) hκ
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.2 Fintype.card_pos
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω := toReal_volume_ball_zero_one_pos
  have hε : 0 < -(Real.log δ / Real.log M) :=
    neg_pos.2 (div_neg_of_neg_of_pos (Real.log_neg hδ0 hδ1) (Real.log_pos hM))
  refine ⟨32 * N, δ⁻¹ * 4 ^ Fintype.card ι / ω, -(Real.log δ / Real.log M), ε₀ / (32 * N),
    by linarith, by positivity, hε, by positivity, ?_⟩
  intro lam Lam r t x₀ a u f hr ha hLam hcont hu hnonneg hsuper hf hx₁ ht
  -- Place `B(x₀, r)` in a translate of the dyadic cube `Q(k, 0)` of side `2ᵏ ∈ (2r, 4r]`, centred
  -- at `x₀`.
  obtain ⟨k', hk'⟩ := exists_mem_Ico_zpow (by positivity : 0 < 2 * r) one_lt_two
  set k := k' + 1
  have h2k : 2 * r < 2 ^ k := hk'.2
  have h4k : (2 : ℝ) ^ k ≤ 4 * r := by
    rw [zpow_add_one₀ two_ne_zero]
    linarith [hk'.1]
  set z : ι → ℝ := fun i ↦ (((0 : ι → ℤ) i : ℝ) + 2⁻¹) * 2 ^ k
  set w := x₀ - WithLp.toLp 2 z
  have hc : x₀ = WithLp.toLp 2 z + w := by simp [w]
  have hRK : 8 * N * 2 ^ k ≤ 32 * N * r := by nlinarith
  have hball := ball_subset_ball (x := x₀) hRK
  have hclosedBall := closedBall_subset_closedBall (x := x₀) hRK
  have hf' : ENNReal.ofReal (8 * N * 2 ^ k) * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
      (volume.restrict (ball x₀ (8 * N * 2 ^ k))) ≤ ENNReal.ofReal (ε₀ * lam) := by
    refine (ofReal_mul_eLpNorm_ball_le (by positivity) hRK).trans ?_
    calc _ ≤ ENNReal.ofReal (32 * N) * ENNReal.ofReal (ε₀ / (32 * N) * lam) := by gcongr
      _ = ENNReal.ofReal (ε₀ * lam) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  obtain ⟨x₁, hx₁, hux₁⟩ := hx₁
  have hdec := hdecay hc rfl (ha.mono_set hball) hLam (hcont.mono hclosedBall) (hu.mono hball)
    (fun x hx ↦ hnonneg x (hclosedBall hx)) (fun x hx ↦ hsuper x (hball hx)) hf'
    ⟨x₁, ball_subset_ball (by nlinarith) hx₁, hux₁⟩
  -- The ball lies in the translated cube.
  have hsub : (fun y : ι → ℝ ↦ WithLp.toLp 2 y + w) ⁻¹' ({x | t ≤ u x} ∩ ball x₀ r) ⊆
      {y | t ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k 0 := fun y hy ↦
    ⟨hy.1, preimage_ball_subset_dyadicCube k 0 w (by
      rw [mem_preimage, ← hc]
      exact ball_subset_ball (by linarith) hy.2)⟩
  have hvol := volume_dyadicCube_le_ofReal_mul_volume_ball hr h4k (0 : ι → ℤ) x₀
  rw [← volume_preimage_toLp_add w]
  refine (measure_mono hsub).trans ((le_ofReal_inv_mul_rpow_mul_of_forall_le_pow_mul (g := fun s ↦
    volume ({y | s ≤ u (WithLp.toLp 2 y + w)} ∩ dyadicCube k 0)) hM hδ0 hδ1.le
    (fun s s' hss' ↦ measure_mono fun y hy ↦ ⟨hss'.trans hy.1, hy.2⟩)
    (fun _ ↦ measure_mono inter_subset_right) hdec ht).trans ?_)
  rw [neg_neg]
  calc ENNReal.ofReal (δ⁻¹ * t ^ (Real.log δ / Real.log M)) * volume (dyadicCube k 0)
      ≤ ENNReal.ofReal (δ⁻¹ * t ^ (Real.log δ / Real.log M)) *
        (ENNReal.ofReal (4 ^ Fintype.card ι / ω) * volume (ball x₀ r)) := by gcongr
    _ = ENNReal.ofReal (δ⁻¹ * 4 ^ Fintype.card ι / ω * t ^ (Real.log δ / Real.log M)) *
        volume (ball x₀ r) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end PDE

end TauCeti
