/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import TauCeti.Analysis.Sobolev.Wkp.NormRpow

/-!
# `W^{2,p}` regularity fails for a discontinuous coefficient

For `b ≥ 0` let `a = TauCeti.PDE.radialCoefficient b` be the coefficient field on `ℝⁿ`

`a(x) = I + b x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

whose eigenvalue in the radial direction `x̂` is `1 + b` and in the directions orthogonal to `x`
is `1`. It is measurable, symmetric and uniformly elliptic with constants `1` and `1 + b`, and
for `n ≥ 2` and `b ≠ 0` it has no limit at the origin. In the plane it is `1 + b` times Meyers'
coefficient field `TauCeti.PDE.meyersCoefficient μ` with `μ² = 1 / (1 + b)`, the corresponding
counterexample for divergence-form equations. Away from the origin the power
`u(x) = ‖x‖ ^ γ` satisfies

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = γ (n + γ - 2 + b (γ - 1)) ‖x‖ ^ (γ - 2)`,

because the Hessian of `u` is `γ ‖x‖ ^ (γ - 2)` on the directions orthogonal to `x` and
`γ (γ - 1) ‖x‖ ^ (γ - 2)` on `x`. For `n ≥ 2`, `0 < γ < 1` and `b = (n + γ - 2) / (1 - γ) > 0`
the right side vanishes, so `u` solves the homogeneous non-divergence equation almost everywhere,
with its weak Hessian. On a bounded open set containing the origin, `u` lies in `W^{2,p}` exactly
for `p < n / (2 - γ)`, an exponent strictly between `n / 2` and `n`
(`TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`).

So for coefficients that are bounded, measurable and uniformly elliptic but discontinuous, a
`W^{2,p₀}` strong solution of `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = 0` need not lie in `W^{2,p}` for `p > p₀`, not
even for `p = n`: the interior `W^{2,p}` regularity of strong solutions needs a regularity
hypothesis on the coefficients, such as continuity, under which the interior estimate of
`TauCeti/Analysis/PDE/Regularity/Hessian/ContinuousCoefficient.lean` holds, or vanishing mean
oscillation. The ellipticity ratio `1 + b` of the counterexample tends to infinity as
`n / (2 - γ)` approaches `n`.

## Main declarations

* `TauCeti.PDE.radialCoefficient`: the coefficient field `I + b x̂ x̂ᵀ`.
* `TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`: for `b ≥ 0` it is uniformly elliptic with
  constants `1` and `1 + b`.
* `TauCeti.PDE.not_exists_tendsto_radialCoefficient`: for `n ≥ 2` and `b ≠ 0` it has no limit at
  the origin.
* `TauCeti.PDE.ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq`: the non-divergence
  operator applied to an element of `W^{2,p}` equal to `‖x‖ ^ γ`, with its weak Hessian.
* `TauCeti.PDE.exists_radialCoefficient_not_exists_wkp`: for `1 ≤ p₀ < p < ∞` with `p₀ < n` and
  `n / 2 < p`, some such coefficient field has a `W^{2,p₀}` strong solution of the homogeneous
  equation on every bounded open set containing the origin that is not in `W^{2,p}` there.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9, for the `W^{2,p}` theory of strong solutions.
* F. Chiarenza, M. Frasca, P. Longo, *Interior `W^{2,p}` estimates for non divergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. 40 (1991), 149–168, for the theory
  with coefficients of vanishing mean oscillation.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped InnerProductSpace ENNReal Topology Matrix

namespace TauCeti

namespace PDE

variable {n : ℕ} {b γ : ℝ}

/-- The coefficient field `a(x) = I + b x xᵀ / ‖x‖²` on `ℝⁿ`. Its eigenvalue in the radial
direction `x` is `1 + b` and in the directions orthogonal to `x` is `1`. At the origin, where the
direction is undefined, it is `I`. -/
def radialCoefficient (b : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  1 + (b / ‖x‖ ^ 2) • Matrix.vecMulVec x x

/-- Unfolding `TauCeti.PDE.radialCoefficient`. -/
theorem radialCoefficient_apply (x : EuclideanSpace ℝ (Fin n)) :
    radialCoefficient b x = 1 + (b / ‖x‖ ^ 2) • Matrix.vecMulVec x x :=
  (rfl)

/-- The entries of `TauCeti.PDE.radialCoefficient`: `aᵢⱼ(x) = δᵢⱼ + b xᵢ xⱼ / ‖x‖²`. -/
theorem radialCoefficient_apply_apply (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    radialCoefficient b x i j = (if i = j then 1 else 0) + b / ‖x‖ ^ 2 * (x i * x j) := by
  simp [radialCoefficient, Matrix.one_apply, Matrix.vecMulVec_apply]

/-- The radial coefficient is symmetric. -/
theorem isSymm_radialCoefficient (x : EuclideanSpace ℝ (Fin n)) :
    (radialCoefficient b x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, radialCoefficient_apply_apply, eq_comm (a := i),
    mul_comm (x i)]

/-- The bilinear form of the radial coefficient:
`ηᵀ a(x) ξ = ⟪η, ξ⟫ + b ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`. -/
theorem dotProduct_radialCoefficient_mulVec (x η ξ : EuclideanSpace ℝ (Fin n)) :
    η ⬝ᵥ (radialCoefficient b x *ᵥ ξ) =
      ⟪η, ξ⟫_ℝ + b / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ) := by
  simp only [dotProduct, Matrix.mulVec, radialCoefficient_apply_apply, add_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mul_add, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- For `b ≥ 0`, the radial coefficient is uniformly elliptic with constants `1` and `1 + b`, so
its ellipticity ratio is `1 + b`. -/
theorem uniformlyEllipticOn_radialCoefficient (hb : 0 ≤ b) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    UniformlyEllipticOn Ω (radialCoefficient b) 1 (1 + b) := by
  refine UniformlyEllipticOn.of_bounds one_pos (by linarith) (fun x _ ξ => ?_)
    (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_radialCoefficient_mulVec,
      real_inner_self_eq_norm_sq, real_inner_comm x ξ]
    have : 0 ≤ b / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) :=
      mul_nonneg (div_nonneg hb (by positivity)) (mul_self_nonneg _)
    linarith
  · have hcx : b / ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ b := by
      rcases eq_or_ne ‖x‖ 0 with h | h
      · simp [h, hb]
      · rw [div_mul_cancel₀ _ (pow_ne_zero 2 h)]
    rw [dotProduct_radialCoefficient_mulVec]
    calc |⟪η, ξ⟫_ℝ + b / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ)|
        ≤ ‖η‖ * ‖ξ‖ + b / ‖x‖ ^ 2 * ((‖η‖ * ‖x‖) * (‖x‖ * ‖ξ‖)) := by
          refine (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hb (by positivity))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (abs_real_inner_le_norm _ _)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity))
            (div_nonneg hb (by positivity))
      _ = (1 + b / ‖x‖ ^ 2 * ‖x‖ ^ 2) * ‖η‖ * ‖ξ‖ := by ring
      _ ≤ (1 + b) * ‖η‖ * ‖ξ‖ := by gcongr

/-- The radial coefficient is strongly measurable. -/
theorem stronglyMeasurable_radialCoefficient :
    StronglyMeasurable (radialCoefficient (n := n) b) := by
  have : Measurable (radialCoefficient (n := n) b) := by
    unfold radialCoefficient
    fun_prop
  -- The matrix space is metrizable through its underlying function type.
  exact Measurable.stronglyMeasurable (β := Fin n → Fin n → ℝ) this

/-- **The radial coefficient is discontinuous at the origin.** For `n ≥ 2` and `b ≠ 0` it has no
limit at the origin: along the ray through `e₀` its entry `a₀₀` is `1 + b`, and along the ray
through `e₁` it is `1`. -/
theorem not_exists_tendsto_radialCoefficient (hn : 2 ≤ n) (hb : b ≠ 0) :
    ¬ ∃ L, Tendsto (radialCoefficient (n := n) b) (𝓝[≠] 0) (𝓝 L) := by
  rintro ⟨L, hL⟩
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  -- Along the ray `t ↦ t eⱼ`, `t > 0`, the entry `a₀₀` is constant.
  have key : ∀ j : Fin n, L i₀ i₀ = 1 + (if j = i₀ then b else 0) := by
    intro j
    have hray : Tendsto (fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ)) (𝓝[>] 0)
        (𝓝[≠] (0 : EuclideanSpace ℝ (Fin n))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
          (f := fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ))
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        simp [ht.ne']
    have hent : Tendsto (fun t : ℝ => radialCoefficient b (t • EuclideanSpace.single j 1) i₀ i₀)
        (𝓝[>] 0) (𝓝 (L i₀ i₀)) :=
      ((continuous_id.matrix_elem i₀ i₀).tendsto L).comp (hL.comp hray)
    refine tendsto_nhds_unique hent (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [radialCoefficient_apply_apply, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg ht.le]
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, ite_true]
    by_cases hj : j = i₀
    · subst hj
      simp only [ite_true, mul_one]
      field_simp
    · simp [hj, Ne.symm hj]
  have h := (key i₀).symm.trans (key i₁)
  simp only [ite_true, hne, ite_false, add_zero] at h
  exact hb (by linarith)

/-- The double sum of the radial coefficient against a matrix of the form
`A δᵢⱼ + B xᵢ xⱼ`. -/
private theorem sum_radialCoefficient_mul (x : EuclideanSpace ℝ (Fin n)) (A B : ℝ) :
    ∑ i, ∑ j, radialCoefficient b x i j * (A * (if i = j then 1 else 0) + B * (x i * x j)) =
      n * A + (B + b / ‖x‖ ^ 2 * A) * ‖x‖ ^ 2 + b / ‖x‖ ^ 2 * B * (‖x‖ ^ 2) ^ 2 := by
  have hsq : ∑ i, x i * x i = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm
  simp only [radialCoefficient_apply_apply, add_mul, mul_add, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ i, b / ‖x‖ ^ 2 * (x i * x i) * A = b / ‖x‖ ^ 2 * A * ‖x‖ ^ 2 := by
    rw [← hsq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, B * (x i * x i) = B * ‖x‖ ^ 2 := by rw [← hsq, Finset.mul_sum]
  have h3 : ∑ i, ∑ j, b / ‖x‖ ^ 2 * (x i * x j) * (B * (x i * x j)) =
      b / ‖x‖ ^ 2 * B * (‖x‖ ^ 2) ^ 2 := by
    rw [← hsq, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3]
  ring

/-- **The non-divergence operator of the radial coefficient on a norm power.** Let `γ > 2 - n`
and let `W ∈ W^{2,p}(Ω)` be equal to `‖x‖ ^ γ`. Then, with its weak Hessian `D²W`,

`∑ᵢⱼ aᵢⱼ(x) ⟪D²W eᵢ, eⱼ⟫ = γ (n + γ - 2 + b (γ - 1)) ‖x‖ ^ (γ - 2)`

almost everywhere on `Ω`, for the radial coefficient `a = TauCeti.PDE.radialCoefficient b`. -/
theorem ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq (hγ : 2 - (n : ℝ) < γ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (W : Wkp volume Ω p 2)
    (hW : Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
      fun x => ‖x‖ ^ γ) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
      ∑ i, ∑ j, radialCoefficient b x i j *
        ⟪Wkp.iteratedGradient 1 W x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        γ * (n + γ - 2 + b * (γ - 1)) * ‖x‖ ^ (γ - 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- In dimension zero both sides vanish, since `γ > 2`.
    refine Eventually.of_forall fun x => ?_
    have hγ2 : γ - 2 ≠ 0 := by
      simp only [CharP.cast_eq_zero, sub_zero] at hγ
      linarith
    simp [Subsingleton.elim x 0, Real.zero_rpow hγ2]
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  have hH := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_norm_rpow
    (by simpa only [finrank_euclideanSpace_fin] using hγ) W hW
  filter_upwards [hH, ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin n)))]
    with x hx hx0
  have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx0)
  have h42 : ‖x‖ ^ (γ - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (γ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 hx0)]
    congr 1
    ring
  -- The entries of `w ↦ A w + B ⟪x, w⟫ x` are `A δᵢⱼ + B xᵢ xⱼ`.
  have hentry : ∀ (A B : ℝ) (i j : Fin n),
      ⟪(A • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + B • (innerSL ℝ x).smulRight x)
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        A * (if i = j then 1 else 0) + B * (x i * x j) := by
    intro A B i j
    by_cases h : i = j
    · subst h
      simp [inner_add_left, EuclideanSpace.inner_single_right]
    · simp [inner_add_left, EuclideanSpace.inner_single_right, h, Ne.symm h]
  rw [hx]
  calc _ = ∑ i, ∑ j, radialCoefficient b x i j * (γ * ‖x‖ ^ (γ - 2) * (if i = j then 1 else 0) +
        γ * (γ - 2) * ‖x‖ ^ (γ - 4) * (x i * x j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [hentry]
    _ = _ := by
        rw [sum_radialCoefficient_mul, ← h42]
        field_simp
        ring

/-- For `1 ≤ p₀ < p < ∞` with `p₀ < n` and `n / 2 < p` there is `0 < γ < 1` with
`p₀ < n / (2 - γ) ≤ p`, stated as `(γ - 2) p₀ > -n ≥ (γ - 2) p`. -/
private theorem exists_exponent_lt_of_lt (hn : 2 ≤ n) {p₀ p : ℝ≥0∞} (hp : p ≠ ∞) (hp₀n : p₀ < n)
    (hpn : (n : ℝ≥0∞) / 2 < p) (hp₀p : p₀ < p) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ -(n : ℝ) < (γ - 2) * p₀.toReal ∧ (γ - 2) * p.toReal ≤ -n := by
  have hp₀top : p₀ ≠ ∞ := hp₀n.ne_top
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hP₀n : p₀.toReal < n := by
    simpa using (ENNReal.toReal_lt_toReal hp₀top (ENNReal.natCast_ne_top n)).2 hp₀n
  have hPn : (n : ℝ) / 2 < p.toReal := by
    simpa [ENNReal.toReal_div] using
      (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (ENNReal.natCast_ne_top n) two_ne_zero)
        hp).2 hpn
  have hP₀P : p₀.toReal < p.toReal := (ENNReal.toReal_lt_toReal hp₀top hp).2 hp₀p
  -- The critical exponent `t = n / (2 - γ)` lies strictly between `max p₀ (n / 2)` and
  -- `min p n`.
  have hlt : max p₀.toReal (n / 2) < min p.toReal n :=
    max_lt (lt_min hP₀P hP₀n) (lt_min hPn (by linarith))
  set t : ℝ := (max p₀.toReal (n / 2) + min p.toReal n) / 2
  have ht₁ : max p₀.toReal (n / 2) < t := by simp only [t]; linarith
  have ht₂ : t < min p.toReal n := by simp only [t]; linarith
  have htn : n / 2 < t := (le_max_right _ _).trans_lt ht₁
  have htp₀ : p₀.toReal < t := (le_max_left _ _).trans_lt ht₁
  have htp : t < p.toReal := ht₂.trans_le (min_le_left _ _)
  have htn' : t < n := ht₂.trans_le (min_le_right _ _)
  have ht0 : 0 < t := by linarith
  have hγt : ∀ q : ℝ, (2 - n / t - 2) * q = -(n * (q / t)) := fun q => by
    field_simp
    ring
  refine ⟨2 - n / t, ?_, ?_, ?_, ?_⟩
  · have : (n : ℝ) / t < 2 := by rw [div_lt_iff₀ ht0]; linarith
    linarith
  · have : 1 < (n : ℝ) / t := by rw [lt_div_iff₀ ht0]; linarith
    linarith
  · rw [hγt, neg_lt_neg_iff]
    have : p₀.toReal / t < 1 := (div_lt_one ht0).2 htp₀
    nlinarith
  · rw [hγt, neg_le_neg_iff]
    have : 1 ≤ p.toReal / t := (one_le_div ht0).2 htp.le
    nlinarith

/-- **`W^{2,p}` regularity fails for discontinuous coefficients.** Let `n ≥ 2` and
`1 ≤ p₀ < p < ∞` with `p₀ < n` and `n / 2 < p`. Then there are `b > 0` and `0 < γ < 1` such that,
for the coefficient field `a = TauCeti.PDE.radialCoefficient b`, uniformly elliptic with constants
`1` and `1 + b` (`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`) but discontinuous at the
origin (`TauCeti.PDE.not_exists_tendsto_radialCoefficient`), and for every bounded open
`Ω ⊆ ℝⁿ` containing the origin, the function `‖x‖ ^ γ` lies in `W^{2,p₀}(Ω)` and solves
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on `Ω` with its weak Hessian, but does not lie in
`W^{2,p}(Ω)`. -/
theorem exists_radialCoefficient_not_exists_wkp (hn : 2 ≤ n) {p₀ p : ℝ≥0∞} [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp₀n : p₀ < n) (hpn : (n : ℝ≥0∞) / 2 < p) (hp₀p : p₀ < p) :
    ∃ b γ : ℝ, 0 < b ∧ 0 < γ ∧ γ < 1 ∧ ∀ {Ω : Opens (EuclideanSpace ℝ (Fin n))},
      Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin n))) →
      (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω →
      (∃ W : Wkp volume Ω p₀ 2,
        Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
          (fun x => ‖x‖ ^ γ) ∧
        ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
          ∑ i, ∑ j, radialCoefficient b x i j * ⟪Wkp.iteratedGradient 1 W x
            (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0) ∧
      ¬ ∃ W : Wkp volume Ω p 2,
        Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
          fun x => ‖x‖ ^ γ := by
  have hp₀top : p₀ ≠ ∞ := hp₀n.ne_top
  obtain ⟨γ, hγ0, hγ1, hγp₀, hγp⟩ := exists_exponent_lt_of_lt hn hp hp₀n hpn hp₀p
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(n + γ - 2) / (1 - γ), γ, div_pos (by linarith) (by linarith), hγ0, hγ1,
    fun {Ω} hb h0 => ⟨?_, ?_⟩⟩
  · obtain ⟨W, hW⟩ := exists_wkp_two_value_ae_eq_norm_rpow (μ := volume) (s := γ) hb hp₀top
      (by rwa [finrank_euclideanSpace_fin])
    refine ⟨W, hW, ?_⟩
    filter_upwards [ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq
      (b := (n + γ - 2) / (1 - γ)) (by linarith) W hW] with x hx
    rw [hx]
    have : (1 : ℝ) - γ ≠ 0 := by linarith
    field_simp
    ring
  · rw [exists_wkp_two_value_ae_eq_norm_rpow_iff hb hp h0 hγ0.ne' (by
      rw [finrank_euclideanSpace_fin]
      linarith), finrank_euclideanSpace_fin, not_lt]
    exact hγp

end PDE

end TauCeti
