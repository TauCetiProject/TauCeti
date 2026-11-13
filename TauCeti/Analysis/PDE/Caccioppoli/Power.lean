/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-!
# The Caccioppoli inequality for powers of a positive supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, which is bounded below by a constant
`ε > 0`. For every exponent `p < 1` and every smooth `ψ` compactly supported in `Ω`, this file
proves

`∫_Ω ψ² u^{p-2} ‖∇u‖² ≤ (2Λ / ((1 - p) λ))² ∫_Ω ‖∇ψ‖² u^p`.

For `p ≠ 0` the left side is `(2/p)² ∫_Ω ψ² ‖∇(u^{p/2})‖²`, so this is a Caccioppoli
inequality for the power `u^{p/2}`; for `p = 0` it bounds `∫_Ω ψ² ‖∇ log u‖²`. These are the
energy estimates of Moser's iteration: the case `0 < p < 1` feeds the reverse Hölder inequality
for small positive powers of a supersolution, the case `p < 0` the bound for its negative powers,
and the case `p = 0` the bounded mean oscillation of `log u`. The constant depends only on `λ`,
`Λ` and `p`, and blows up as `p → 1`; no regularity of the coefficients beyond measurability is
used, and the lower bound `ε` serves only to make the powers of `u` Sobolev functions.

The inequality is proved by testing the supersolution inequality against `ψ² u^{p-1}`, which is
nonnegative and lies in `H¹₀(Ω)`. Its gradient is `(p - 1) ψ² u^{p-2} ∇u + 2 ψ u^{p-1} ∇ψ`, and
the coefficient `p - 1 < 0` of the first term turns the supersolution inequality into an upper
bound for `∫ ψ² u^{p-2} ⟨a ∇u, ∇u⟩`; Young's inequality absorbs the cross term.

The same test function handles the full operator `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` with measurable
`‖b‖ ≤ β` and `|c| ≤ γ`, with no sign condition on `c`. The drift term `⟪b, ∇u⟫ ψ² u^{p-1}` is
absorbed by a second application of Young's inequality and the mass term `c ψ² u^p` is bounded
directly, which gives

`∫_Ω ψ² u^{p-2} ‖∇u‖² ≤ (2 / ((1 - p) λ))² (2Λ² ∫_Ω ‖∇ψ‖² u^p + (β² + (1 - p) λ γ) ∫_Ω ψ² u^p)`.

The new zeroth-order term in `ψ` is comparable to the cutoff term on a ball of radius `R` when
`βR/λ` and `γR²/λ` are bounded, which is how Moser's estimates extend to equations with
lower-order terms.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le`: the
  Caccioppoli inequality for powers of a positive supersolution.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow`: its
  form as a Caccioppoli inequality for the power `u^{p/2}`.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le_lowerOrder`
  and
  `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder`:
  the same two inequalities for supersolutions of the equation with lower-order terms.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6, the proofs of Theorems 8.18 and 8.20, where the lower-order terms are included.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- The test function `ψ² u^{p-1}` of the Caccioppoli inequality for powers. If `u ∈ H¹(Ω)` is
bounded below by a positive constant, `p < 1` and `ψ` is smooth and compactly supported in `Ω`,
then `ψ² u^{p-1} ∈ H¹₀(Ω)`, with weak gradient `(p - 1) ψ² u^{p-2} ∇u + 2 ψ u^{p-1} ∇ψ`. -/
private theorem exists_w1p0_value_gradient_ae_eq_sq_mul_rpow {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega,
        W1p.value (v : W1p mu Omega 2) x = ψ x ^ 2 * W1p.value u x ^ (p - 1)) ∧
      ∀ᵐ x ∂mu.restrict Omega, W1p.gradient (v : W1p mu Omega 2) x =
        (ψ x ^ 2 * ((p - 1) * W1p.value u x ^ (p - 1 - 1))) • W1p.gradient u x +
          (2 * ψ x * W1p.value u x ^ (p - 1)) • ∇ ψ x := by
  -- The Sobolev function `u^{p-1}`, with weak gradient `(p - 1) u^{p-2} ∇u`.
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hε
    (by linarith : p - 1 ≤ 1) hεu
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- `ψ² u^{p-1} = ψ (ψ u^{p-1})`, by the Leibniz rule twice.
  set w₁ := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w₁
  refine ⟨⟨v, W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM'
    hgradM' hcpt hts w₁⟩, ?_, ?_⟩
  · filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w₁,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w, hwv] with x h1 h2 h3
    rw [h1, h2, h3, smul_eq_mul, smul_eq_mul]
    ring
  · filter_upwards [hwv, hwg, W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w₁,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with x hwvx hwgx hg1 hg2 hv2
    rw [hg1, hg2, hv2, hwgx, hwvx]
    simp only [smul_eq_mul]
    module

/-- The first integrability fact of the Caccioppoli inequality for powers: if `u ∈ H¹(Ω)` is
bounded below by a positive constant, `p < 1`, and `ψ` is continuous with `|ψ| ≤ M`, then
`ψ² u^{p-2} ‖∇u‖²` is integrable. -/
private theorem integrable_sq_mul_rpow_mul_norm_gradient_sq {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : Continuous ψ) {M : ℝ} (hψM : ∀ x, |ψ x| ≤ M) :
    Integrable (fun x => ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
      (mu.restrict Omega) := by
  refine ((W1p.integrable_norm_gradient_sq u).const_mul (M ^ 2 * ε ^ (p - 2))).mono' ?_ ?_
  · exact (hψ.pow 2).aestronglyMeasurable.mul
      (((Lp.aestronglyMeasurable (W1p.value u)).aemeasurable.pow_const _).mul
        ((Lp.aestronglyMeasurable (W1p.gradient u)).aemeasurable.norm.pow_const 2)
        ).aestronglyMeasurable
  · filter_upwards [hεu] with x hx
    have hU : 0 < W1p.value u x := hε.trans_le hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (sq_le_sq' (abs_le.1 (hψM x)).1 (abs_le.1 (hψM x)).2)
      (Real.rpow_le_rpow_of_nonpos hε hx (by linarith)) (by positivity) (by positivity))
      (by positivity)

/-- The second integrability fact of the Caccioppoli inequality for powers: if `u ∈ H¹(Ω)` is
bounded below by a positive constant and `p < 1`, then `g u^p` is integrable for every continuous
bounded weight `g`, because `u^p = (u^{p/2})²` for the Sobolev function `u^{p/2}`. -/
private theorem integrable_mul_rpow {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Continuous g) {M : ℝ} (hgM : ∀ x, |g x| ≤ M) :
    Integrable (fun x => g x * W1p.value u x ^ p) (mu.restrict Omega) := by
  obtain ⟨w, hwv, -⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hε
    (by linarith : p / 2 ≤ 1) hεu
  refine ((Lp.memLp (W1p.value w)).integrable_sq.bdd_mul hg.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgM x)).congr ?_
  filter_upwards [hwv, hεu] with x hx hux
  rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (hε.le.trans hux)]
  norm_num

/-- The weight `‖∇ψ‖²` of the cutoff term is continuous and bounded by `M²` when `‖∇ψ‖ ≤ M`. -/
private theorem integrable_norm_gradient_sq_mul_rpow {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M) :
    Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p) (mu.restrict Omega) :=
  integrable_mul_rpow hε hεu hp ((ContDiff.continuous_gradient hψ (by simp)).norm.pow 2)
    fun x => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgradM x) 2

variable [DecidableEq ι]

/-- The pointwise form of the Caccioppoli inequality for powers. At a point where `u` has value
`U > 0` and gradient `G`, and the cutoff has value `z` and gradient `q`, the test function
`ψ² u^{p-1}` has gradient `(p - 1) z² U^{p-2} G + 2 z U^{p-1} q`. Pairing it with `G` through a
matrix `A` that is elliptic and bounded with constants `λ, Λ` controls `z² U^{p-2} ‖G‖²` up to the
error `‖q‖² U^p`. -/
private theorem mul_sq_mul_rpow_mul_norm_sq_le_neg_matrixBilinearForm_add {A : Matrix ι ι ℝ}
    (hlam : 0 < lam) (hlower : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hupper : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    {p : ℝ} (hp : p < 1) {U : ℝ} (hU : 0 < U) (z : ℝ) (G q : EuclideanSpace ℝ ι) :
    lam * (z ^ 2 * (U ^ (p - 2) * ‖G‖ ^ 2)) ≤
      -(1 - p)⁻¹ * matrixBilinearForm A
          ((z ^ 2 * ((p - 1) * U ^ (p - 1 - 1))) • G + (2 * z * U ^ (p - 1)) • q) G
        + lam / 2 * (z ^ 2 * (U ^ (p - 2) * ‖G‖ ^ 2))
        + 2 * Lam ^ 2 / lam / (1 - p) ^ 2 * (‖q‖ ^ 2 * U ^ p) := by
  -- In terms of `g = U^{p/2-1} G`, the gradient of `u^{p/2}` up to the factor `p/2`, this is the
  -- absorption estimate `mul_sq_mul_norm_sq_le_matrixBilinearForm_add` with the weight
  -- `W = -U^{p/2} / (1 - p)`.
  set s := U ^ (p / 2 - 1)
  set g : EuclideanSpace ℝ ι := s • G
  set W := -(U ^ (p / 2) / (1 - p))
  have hs : 0 < s := Real.rpow_pos_of_pos hU _
  have hs2 : s ^ 2 = U ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
    norm_num
    ring_nf
  have hs2' : U ^ (p - 1 - 1) = s ^ 2 := by
    rw [hs2]
    ring_nf
  have hUs : U ^ (p - 1) = U ^ (p / 2) * s := by
    rw [← Real.rpow_add hU]
    ring_nf
  have hUp : U ^ p = (U ^ (p / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
    norm_num
  have hg : ‖g‖ ^ 2 = U ^ (p - 2) * ‖G‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hs2]
  have key := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam z W g q (hlower g)
    (hupper q g)
  set X := z • (z • g + W • q) + (z * W) • q
  have hη : (z ^ 2 * ((p - 1) * U ^ (p - 1 - 1))) • G + (2 * z * U ^ (p - 1)) • q =
      ((p - 1) * s) • X := by
    simp only [X, g, W, hs2', hUs, smul_add, smul_smul]
    match_scalars
    all_goals field_simp
    ring
  have hB : -(1 - p)⁻¹ * matrixBilinearForm A (((p - 1) * s) • X) G =
      matrixBilinearForm A X g := by
    simp only [g, map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hW : W ^ 2 = U ^ p / (1 - p) ^ 2 := by
    rw [hUp]
    simp only [W]
    field_simp
  rw [hη, hB, ← hg]
  rw [hW] at key
  calc lam * (z ^ 2 * ‖g‖ ^ 2)
      ≤ matrixBilinearForm A X g + lam / 2 * (z ^ 2 * ‖g‖ ^ 2) +
          2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * (U ^ p / (1 - p) ^ 2)) := key
    _ = _ := by
        field_simp

/-- The pointwise estimate of the Caccioppoli inequality for powers, almost everywhere on `Ω`:
if the test function `v` has gradient `(p - 1) ψ² u^{p-2} ∇u + 2 ψ u^{p-1} ∇ψ` almost everywhere,
then `λ ψ² u^{p-2} ‖∇u‖²` is bounded by the energy integrand of `u` and `v` (times `-(1 - p)⁻¹`),
half of the left side, and `(2Λ² / λ / (1 - p)²) ‖∇ψ‖² u^p`. -/
private theorem UniformlyEllipticOn.ae_mul_sq_mul_rpow_mul_norm_sq_le_energyIntegrand
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    {u v : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ}
    (hvg : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x =
      (ψ x ^ 2 * ((p - 1) * W1p.value u x ^ (p - 1 - 1))) • W1p.gradient u x +
        (2 * ψ x * W1p.value u x ^ (p - 1)) • ∇ ψ x) :
    ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2)) ≤
        -(1 - p)⁻¹ * energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
          + 2 * Lam ^ 2 / lam / (1 - p) ^ 2 * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p) := by
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hlam := h.pos
  filter_upwards [hmem, hεu, hvg] with x hx hux hgx
  rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgx]
  simp only [Pi.zero_apply, driftForm_apply, massForm_apply, inner_zero_left, zero_mul,
    add_zero]
  exact mul_sq_mul_rpow_mul_norm_sq_le_neg_matrixBilinearForm_add hlam (h.lower_bound hx)
    (h.upper_bound hx) hp (hε.trans_le hux) (ψ x) (W1p.gradient u x) (∇ ψ x)

omit [DecidableEq ι] in
/-- The drift term of the Caccioppoli inequality for powers, at a point where `u` has value
`U > 0` and gradient of norm `g`, and the cutoff has value `z`. By Young's inequality,
`(1 - p)⁻¹ β g z² U^{p-1}` is at most `(λ/4) z² U^{p-2} g² + β² / (λ (1 - p)²) z² U^p`. -/
private theorem inv_mul_mul_mul_sq_mul_rpow_le (hlam : 0 < lam) {p : ℝ} (hp : p < 1) {U : ℝ}
    (hU : 0 < U) (z g β : ℝ) :
    (1 - p)⁻¹ * (β * g * (z ^ 2 * U ^ (p - 1))) ≤
      lam / 4 * (z ^ 2 * (U ^ (p - 2) * g ^ 2)) +
        β ^ 2 / (lam * (1 - p) ^ 2) * (z ^ 2 * U ^ p) := by
  have h1p : 1 - p ≠ 0 := by linarith
  set s := U ^ (p / 2 - 1)
  set t := U ^ (p / 2)
  have hts : U ^ (p - 1) = t * s := by
    rw [← Real.rpow_add hU]
    ring_nf
  have hs2 : U ^ (p - 2) = s ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
    ring_nf
  have ht2 : U ^ p = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
    norm_num
  rw [hts, hs2, ht2]
  -- Weighted Young's inequality for `z s g` and `β / (1 - p) z t` with weight `λ / 2`.
  have hy := two_mul_le_add_mul_sq (a := z * s * g) (b := β / (1 - p) * (z * t))
    (half_pos hlam)
  field_simp at hy ⊢
  linarith

/-- The pointwise estimate of the Caccioppoli inequality for powers with lower-order terms. If
`‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and the test function `v` has value `ψ² u^{p-1}` and gradient
`(p - 1) ψ² u^{p-2} ∇u + 2 ψ u^{p-1} ∇ψ` almost everywhere, then `λ ψ² u^{p-2} ‖∇u‖²` is bounded
by the energy integrand of `u` and `v` (times `-(1 - p)⁻¹`), three quarters of the left side,
`(2Λ² / λ / (1 - p)²) ‖∇ψ‖² u^p` and `(β² / (λ (1 - p)²) + γ / (1 - p)) ψ² u^p`. -/
private theorem UniformlyEllipticOn.ae_mul_sq_mul_rpow_mul_norm_sq_le_energyIntegrand_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {u v : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ}
    (hvv : ∀ᵐ x ∂mu.restrict Omega, W1p.value v x = ψ x ^ 2 * W1p.value u x ^ (p - 1))
    (hvg : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x =
      (ψ x ^ 2 * ((p - 1) * W1p.value u x ^ (p - 1 - 1))) • W1p.gradient u x +
        (2 * ψ x * W1p.value u x ^ (p - 1)) • ∇ ψ x) :
    ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2)) ≤
        -(1 - p)⁻¹ * energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x)
          + 3 * lam / 4 * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
          + 2 * Lam ^ 2 / lam / (1 - p) ^ 2 * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p)
          + (beta ^ 2 / (lam * (1 - p) ^ 2) + gamma / (1 - p)) *
            (ψ x ^ 2 * W1p.value u x ^ p) := by
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hlam := h.pos
  have h1p : 0 < 1 - p := by linarith
  filter_upwards [hmem, hεu, hvv, hvg] with x hx hux hvx hgx
  set U := W1p.value u x
  set G := W1p.gradient u x
  have hU : 0 < U := hε.trans_le hux
  -- The principal part, as in the case without lower-order terms.
  have hprin := mul_sq_mul_rpow_mul_norm_sq_le_neg_matrixBilinearForm_add hlam (h.lower_bound hx)
    (h.upper_bound hx) hp hU (ψ x) G (∇ ψ x)
  -- The drift term `⟪b, ∇u⟫ ψ² u^{p-1}`, by Young's inequality.
  have hdrift : (1 - p)⁻¹ * (⟪b x, G⟫_ℝ * (ψ x ^ 2 * U ^ (p - 1))) ≤
      lam / 4 * (ψ x ^ 2 * (U ^ (p - 2) * ‖G‖ ^ 2)) +
        beta ^ 2 / (lam * (1 - p) ^ 2) * (ψ x ^ 2 * U ^ p) := by
    refine le_trans ?_ (inv_mul_mul_mul_sq_mul_rpow_le hlam hp hU (ψ x) ‖G‖ beta)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1p.le)
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hb_bound x hx) (norm_nonneg _))))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hU.le _))
  -- The mass term `c u ψ² u^{p-1} = c ψ² u^p`.
  have hUp : U ^ p = U * U ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring, Real.rpow_add hU, Real.rpow_one]
  have hmass : (1 - p)⁻¹ * (c x * U * (ψ x ^ 2 * U ^ (p - 1))) ≤
      gamma / (1 - p) * (ψ x ^ 2 * U ^ p) := by
    rw [div_eq_inv_mul, mul_assoc (1 - p)⁻¹ gamma]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1p.le)
    rw [show c x * U * (ψ x ^ 2 * U ^ (p - 1)) = c x * (ψ x ^ 2 * U ^ p) by rw [hUp]; ring]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hc_bound x hx))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hU.le _))
  rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgx, hvx]
  simp only [driftForm_apply, massForm_apply]
  have hsplit : -(1 - p)⁻¹ * (matrixBilinearForm (a x)
        ((ψ x ^ 2 * ((p - 1) * U ^ (p - 1 - 1))) • G + (2 * ψ x * U ^ (p - 1)) • ∇ ψ x) G +
        ⟪b x, G⟫_ℝ * (ψ x ^ 2 * U ^ (p - 1)) + c x * U * (ψ x ^ 2 * U ^ (p - 1))) =
      -(1 - p)⁻¹ * matrixBilinearForm (a x)
        ((ψ x ^ 2 * ((p - 1) * U ^ (p - 1 - 1))) • G + (2 * ψ x * U ^ (p - 1)) • ∇ ψ x) G -
        (1 - p)⁻¹ * (⟪b x, G⟫_ℝ * (ψ x ^ 2 * U ^ (p - 1))) -
        (1 - p)⁻¹ * (c x * U * (ψ x ^ 2 * U ^ (p - 1))) := by ring
  rw [hsplit]
  linarith

/-- **The Caccioppoli inequality for powers of a positive supersolution.** Let `a` be measurable
and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, with `u ≥ ε` almost everywhere for some `ε > 0`. Then for every `p < 1` and every
smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² u^{p-2} ‖∇u‖² ≤ (2Λ / ((1 - p) λ))² ∫_Ω ‖∇ψ‖² u^p`.

For `p ≠ 0` the integrand on the left is `(2/p)² ψ² ‖∇(u^{p/2})‖²`; for `p = 0` it is
`ψ² ‖∇ log u‖²`. The constant depends on neither `u` nor `ε`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2) ∂mu ≤
      (2 * Lam / ((1 - p) * lam)) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu := by
  have hlam := h.pos
  have h1p : 0 < 1 - p := by linarith
  -- Test the inequality against `v = ψ² u^{p-1} ≥ 0`.
  obtain ⟨v, hvv, hvg⟩ := exists_w1p0_value_gradient_ae_eq_sq_mul_rpow hε hεu hp hψ hcpt hts
  have hpos := hu v (by
    filter_upwards [hvv, hεu] with x h1 h2
    rw [h1]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hε.le.trans h2) _))
  rw [energyFormH1_def] at hpos
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u (v : W1p mu Omega 2)
  have hpt := h.ae_mul_sq_mul_rpow_mul_norm_sq_le_energyIntegrand hε hεu hp hvg
  -- Integrability of the three terms.
  obtain ⟨M, _, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hF := integrable_sq_mul_rpow_mul_norm_gradient_sq hε hεu hp hψ.continuous hψM
  have hY := integrable_norm_gradient_sq_mul_rpow (u := u) hε hεu hp hψ hgradM
  -- Integrate the pointwise estimate and absorb half of the left side.
  have hI : ∫ x in Omega, lam * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
      ∂mu ≤ ∫ x in Omega, (-(1 - p)⁻¹ * energyIntegrand (a x)
            ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)
            (jetField u x) (jetField (v : W1p mu Omega 2) x)
          + lam / 2 * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
          + 2 * Lam ^ 2 / lam / (1 - p) ^ 2 * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p)) ∂mu :=
    integral_mono_ae (hF.const_mul lam)
      (((hE.const_mul _).add (hF.const_mul _)).add (hY.const_mul _)) hpt
  rw [integral_const_mul, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul] at hI
  rotate_left
  · exact hE.const_mul _
  · exact hF.const_mul _
  · exact (hE.const_mul _).add (hF.const_mul _)
  · exact hY.const_mul _
  set X := ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2) ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu
  have hneg : -(1 - p)⁻¹ * ∫ x in Omega, energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)
      (jetField u x) (jetField (v : W1p mu Omega 2) x) ∂mu ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (inv_nonneg.2 h1p.le)) hpos
  have hhalf : lam / 2 * X ≤ 2 * Lam ^ 2 / lam / (1 - p) ^ 2 * Y := by linarith
  calc X = 2 / lam * (lam / 2 * X) := by field_simp
    _ ≤ 2 / lam * (2 * Lam ^ 2 / lam / (1 - p) ^ 2 * Y) := by gcongr
    _ = (2 * Lam / ((1 - p) * lam)) ^ 2 * Y := by field_simp

/-- **The Caccioppoli inequality for powers of a positive supersolution, with lower-order
terms.** Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`. Let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with drift `b` and mass coefficient `c`, with
`u ≥ ε` almost everywhere for some `ε > 0`. Then for every `p < 1` and every smooth `ψ` compactly
supported in `Ω`,

`∫_Ω ψ² u^{p-2} ‖∇u‖² ≤ (2 / ((1 - p) λ))² (2Λ² ∫_Ω ‖∇ψ‖² u^p + (β² + (1 - p) λ γ) ∫_Ω ψ² u^p)`.

No sign condition on `c` is needed. The lower-order terms contribute a zeroth-order term in `ψ`,
which on a ball of radius `R` is comparable to the cutoff term when `βR/λ` and `γR²/λ` are
bounded. The constant depends on neither `u` nor `ε`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {p : ℝ} (hp : p < 1)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2) ∂mu ≤
      (2 / ((1 - p) * lam)) ^ 2 *
        (2 * Lam ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu +
          (beta ^ 2 + (1 - p) * lam * gamma) * ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ p ∂mu) := by
  have hlam := h.pos
  have h1p : 0 < 1 - p := by linarith
  -- Test the inequality against `v = ψ² u^{p-1} ≥ 0`.
  obtain ⟨v, hvv, hvg⟩ := exists_w1p0_value_gradient_ae_eq_sq_mul_rpow hε hεu hp hψ hcpt hts
  have hpos := hu v (by
    filter_upwards [hvv, hεu] with x h1 h2
    rw [h1]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hε.le.trans h2) _))
  rw [energyFormH1_def] at hpos
  have hE := h.integrable_energyIntegrand_jetField ha hb hc hb_bound hc_bound u
    (v : W1p mu Omega 2)
  have hpt := h.ae_mul_sq_mul_rpow_mul_norm_sq_le_energyIntegrand_lowerOrder hb_bound hc_bound hε
    hεu hp hvv hvg
  -- Integrability of the four terms.
  obtain ⟨M, _, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hF := integrable_sq_mul_rpow_mul_norm_gradient_sq hε hεu hp hψ.continuous hψM
  have hY := integrable_norm_gradient_sq_mul_rpow (u := u) hε hεu hp hψ hgradM
  have hZ := integrable_mul_rpow (u := u) hε hεu hp (hψ.continuous.pow 2) (M := M ^ 2) fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.1 (hψM x)).1 (abs_le.1 (hψM x)).2
  set K := 2 * Lam ^ 2 / lam / (1 - p) ^ 2
  set K' := beta ^ 2 / (lam * (1 - p) ^ 2) + gamma / (1 - p)
  -- Integrate the pointwise estimate and absorb three quarters of the left side.
  have hI : ∫ x in Omega, lam * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
      ∂mu ≤ ∫ x in Omega, (-(1 - p)⁻¹ * energyIntegrand (a x) (b x) (c x) (jetField u x)
            (jetField (v : W1p mu Omega 2) x)
          + 3 * lam / 4 * (ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2))
          + K * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p) + K' * (ψ x ^ 2 * W1p.value u x ^ p)) ∂mu :=
    integral_mono_ae (hF.const_mul lam)
      ((((hE.const_mul _).add (hF.const_mul _)).add (hY.const_mul _)).add (hZ.const_mul _)) hpt
  rw [integral_const_mul, integral_add, integral_add, integral_add, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hI
  rotate_left
  · exact hE.const_mul _
  · exact hF.const_mul _
  · exact (hE.const_mul _).add (hF.const_mul _)
  · exact hY.const_mul _
  · exact ((hE.const_mul _).add (hF.const_mul _)).add (hY.const_mul _)
  · exact hZ.const_mul _
  set X := ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2) ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu
  set Z := ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ p ∂mu
  have hneg : -(1 - p)⁻¹ * ∫ x in Omega, energyIntegrand (a x) (b x) (c x) (jetField u x)
      (jetField (v : W1p mu Omega 2) x) ∂mu ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (inv_nonneg.2 h1p.le)) hpos
  have hquarter : lam / 4 * X ≤ K * Y + K' * Z := by linarith
  calc X = 4 / lam * (lam / 4 * X) := by field_simp
    _ ≤ 4 / lam * (K * Y + K' * Z) := by gcongr
    _ = _ := by
        simp only [K, K']
        field_simp
        ring

omit [DecidableEq ι] in
/-- The two sides of a Caccioppoli inequality for `w = u^{p/2}` in terms of `u`. If `w ∈ H¹(Ω)`
has value `u^{p/2}`, then `‖∇w‖² = (p/2)² u^{p-2} ‖∇u‖²` and `w² = u^p` almost everywhere, so
`∫_Ω ψ² ‖∇w‖² = (p/2)² ∫_Ω ψ² u^{p-2} ‖∇u‖²` and `∫_Ω g w² = ∫_Ω g u^p` for every weight `g`. -/
private theorem setIntegral_sq_mul_norm_gradient_sq_eq_and_setIntegral_mul_value_sq_eq
    {u : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {p : ℝ} (hp : p < 1) {w : W1p mu Omega 2}
    (hwv : W1p.value w =ᵐ[mu.restrict Omega] fun x => W1p.value u x ^ (p / 2))
    (ψ : EuclideanSpace ℝ ι → ℝ) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu = (p / 2) ^ 2 *
        ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) * ‖W1p.gradient u x‖ ^ 2) ∂mu ∧
      ∀ g : EuclideanSpace ℝ ι → ℝ, ∫ x in Omega, g x * W1p.value w x ^ 2 ∂mu =
        ∫ x in Omega, g x * W1p.value u x ^ p ∂mu := by
  -- The weak gradient of `w` is determined by its value, hence is that of `u ^ (p / 2)`.
  have hwg : W1p.gradient w =ᵐ[mu.restrict Omega]
      fun x => (p / 2 * W1p.value u x ^ (p / 2 - 1)) • W1p.gradient u x := by
    obtain ⟨w', hw'v, hw'g⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hε
      (by linarith : p / 2 ≤ 1) hεu
    have hww' := W1p.ext_value (Lp.ext (hwv.trans hw'v.symm))
    simpa only [hww'] using hw'g
  refine ⟨?_, fun g => ?_⟩
  · rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hwg, hεu] with x hx hux
    have hU : 0 < W1p.value u x := hε.trans_le hux
    rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, abs_mul, mul_pow, sq_abs, sq_abs,
      ← Real.rpow_natCast (W1p.value u x ^ (p / 2 - 1)), ← Real.rpow_mul hU.le]
    push_cast
    ring_nf
  · refine integral_congr_ae ?_
    filter_upwards [hwv, hεu] with x hx hux
    rw [hx, ← Real.rpow_mul_natCast (hε.le.trans hux)]
    norm_num

/-- **The Caccioppoli inequality for the power `w = u^{p/2}` of a positive supersolution.** Under
the hypotheses of `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le`,
let `w ∈ H¹(Ω)` have value `u^{p/2}`, as provided by
`TauCeti.W1p.exists_value_gradient_ae_eq_rpow`; its weak gradient is then `(p/2) u^{p/2-1} ∇u`.
Then for every `p < 1` and every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² ‖∇w‖² ≤ (|p| Λ / ((1 - p) λ))² ∫_Ω ‖∇ψ‖² w²`.

This is the energy estimate that Moser's iteration combines with a Sobolev inequality for `ψ w`;
at `p = 0` both sides vanish, since `w` is then constant. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {p : ℝ} (hp : p < 1) {w : W1p mu Omega 2}
    (hwv : W1p.value w =ᵐ[mu.restrict Omega] fun x => W1p.value u x ^ (p / 2))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (|p| * Lam / ((1 - p) * lam)) ^ 2 *
        ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu := by
  have hlam := h.pos
  have hc := h.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le ha hu hε hεu hp hψ hcpt hts
  obtain ⟨hl, hr⟩ :=
    setIntegral_sq_mul_norm_gradient_sq_eq_and_setIntegral_mul_value_sq_eq hε hεu hp hwv ψ
  rw [hl, hr]
  calc (p / 2) ^ 2 * ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) *
          ‖W1p.gradient u x‖ ^ 2) ∂mu
      ≤ (p / 2) ^ 2 * ((2 * Lam / ((1 - p) * lam)) ^ 2 *
          ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu) := by gcongr
    _ = (|p| * Lam / ((1 - p) * lam)) ^ 2 *
          ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu := by
        simp only [div_pow, mul_pow, sq_abs]
        field_simp

/-- **The Caccioppoli inequality for the power `w = u^{p/2}` of a positive supersolution, with
lower-order terms.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le_lowerOrder`, let
`w ∈ H¹(Ω)` have value `u^{p/2}`. Then for every `p < 1` and every smooth `ψ` compactly supported
in `Ω`,

`∫_Ω ψ² ‖∇w‖² ≤ (|p| / ((1 - p) λ))² (2Λ² ∫_Ω ‖∇ψ‖² w² + (β² + (1 - p) λ γ) ∫_Ω ψ² w²)`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {p : ℝ} (hp : p < 1) {w : W1p mu Omega 2}
    (hwv : W1p.value w =ᵐ[mu.restrict Omega] fun x => W1p.value u x ^ (p / 2))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (|p| / ((1 - p) * lam)) ^ 2 *
        (2 * Lam ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu +
          (beta ^ 2 + (1 - p) * lam * gamma) * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu) := by
  have hlam := h.pos
  have hcacc := h.setIntegral_sq_mul_rpow_mul_norm_gradient_sq_le_lowerOrder ha hb hc hb_bound
    hc_bound hu hε hεu hp hψ hcpt hts
  obtain ⟨hl, hr⟩ :=
    setIntegral_sq_mul_norm_gradient_sq_eq_and_setIntegral_mul_value_sq_eq hε hεu hp hwv ψ
  rw [hl, hr, hr]
  calc (p / 2) ^ 2 * ∫ x in Omega, ψ x ^ 2 * (W1p.value u x ^ (p - 2) *
          ‖W1p.gradient u x‖ ^ 2) ∂mu
      ≤ (p / 2) ^ 2 * ((2 / ((1 - p) * lam)) ^ 2 *
          (2 * Lam ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ p ∂mu +
            (beta ^ 2 + (1 - p) * lam * gamma) *
              ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ p ∂mu)) := by gcongr
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        simp only [div_pow, mul_pow, sq_abs]
        field_simp

end PDE

end TauCeti
