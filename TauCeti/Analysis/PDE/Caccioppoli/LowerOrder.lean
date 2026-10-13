/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The Caccioppoli inequality for truncations with lower-order terms

Let `u ∈ H¹(Ω)` be a weak subsolution of the full divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u ≤ f` in `Ω`,

that is, `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy
form with drift `b` and mass coefficient `c`. Let `a` be measurable and uniformly elliptic with
constants `0 < λ ≤ Λ`, and let `b` and `c` be measurable and bounded, with `‖b‖ ≤ β`. For a level
`k` with `w = (u - k)⁺ ∈ L²(Ω)`, every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w² + (4/λ) ∫_Ω ψ² (f - c u) w`.

The drift is absorbed into the left-hand side by Young's inequality, at the cost of the
zeroth-order term `(2β/λ)² ∫ ψ² w²`. The mass term is kept on the right-hand side next to the
forcing, where its sign is visible: under the sign condition `c ≥ 0` and at a level `k ≥ 0`, the
product `c u w` is nonnegative, because `w > 0` forces `u > k ≥ 0`, so the term can be dropped.
That is the form on concentric balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` for subsolutions of `L u ≤ 0`:

`∫_{B(x₀, r)} ‖∇w‖² ≤ (2 (2Λ/λ)² (C/(R - r))² + (2β/λ)²) ∫_{B(x₀, R)} w²`,

with `C` depending only on the dimension. Unlike the principal-part inequality
`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le`, this is not invariant
under dilations: the drift term is comparable to the cutoff term only on balls with `βR/λ`
bounded. This is the energy estimate that De Giorgi's iteration needs for equations with
lower-order terms. The boundedness hypothesis on `c` serves only to make the energy form
integrable.

## Main declarations

All four are in the namespace `TauCeti.PDE`.

* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp_of_lowerOrder`:
  Caccioppoli's inequality for `(u - k)⁺` at an arbitrary level with an `L²` hypothesis.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_lowerOrder`: the
  nonnegative-level specialization, whose `L²` hypothesis is automatic.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos_of_lowerOrder`:
  the cutoff form for subsolutions of `L u ≤ 0` with `c ≥ 0`, at a level `k ≥ 0`, where the
  forcing and mass term drop out.
* `exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_of_lowerOrder`: the form on
  concentric balls for subsolutions of `L u ≤ 0` with `c ≥ 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.5 and §8.6.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}

/-- The pointwise Caccioppoli estimate with a drift `‖b‖ ≤ β`: the principal part is bounded as
in `mul_sq_mul_norm_sq_le_matrixBilinearForm_add`, and Young's inequality absorbs the drift
term `⟪b, g⟫ z² w` into a quarter of the ellipticity floor and `(β²/λ) z² w²`. -/
private theorem mul_sq_mul_norm_sq_le_matrixBilinearForm_add_inner_mul_add {A : Matrix ι ι ℝ}
    {g q bx : EuclideanSpace ℝ ι} (hlam : 0 < lam) (z w : ℝ)
    (hlower : lam * ‖g‖ ^ 2 ≤ A.toQuadraticForm' g)
    (hupper : |q ⬝ᵥ (A *ᵥ g)| ≤ Lam * ‖q‖ * ‖g‖) (hb : ‖bx‖ ≤ beta) :
    lam * (z ^ 2 * ‖g‖ ^ 2) ≤
      (matrixBilinearForm A (z • (z • g + w • q) + (z * w) • q) g + ⟪bx, g⟫_ℝ * (z * (z * w))
          + (lam / 4 * (z ^ 2 * ‖g‖ ^ 2) + beta ^ 2 / lam * (z ^ 2 * w ^ 2)))
        + lam / 2 * (z ^ 2 * ‖g‖ ^ 2) + 2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * w ^ 2) := by
  have hkey := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam z w g q hlower hupper
  -- `|⟪b, g⟫ z² w| ≤ β ‖g‖ z² |w|`.
  have hinner : -(⟪bx, g⟫_ℝ * (z * (z * w))) ≤ beta * ‖g‖ * (z ^ 2 * |w|) := by
    have hzzw : z * (z * w) = z ^ 2 * w := by ring
    refine (neg_le_abs _).trans ?_
    rw [abs_mul, hzzw, abs_mul, abs_of_nonneg (sq_nonneg z)]
    exact mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm bx g).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg g))) (by positivity)
  -- Young's inequality `β ‖g‖ z² |w| ≤ (λ/4) z² ‖g‖² + (β²/λ) z² w²`.
  have hyoung : beta * ‖g‖ * (z ^ 2 * |w|) ≤
      lam / 4 * (z ^ 2 * ‖g‖ ^ 2) + beta ^ 2 / lam * (z ^ 2 * w ^ 2) := by
    have h := two_mul_le_add_mul_sq (a := |z| * ‖g‖) (b := beta * |z| * |w| / 2)
      (by positivity : 0 < lam / 4)
    have hlhs : 2 * (|z| * ‖g‖) * (beta * |z| * |w| / 2) = beta * ‖g‖ * (z ^ 2 * |w|) := by
      rw [← sq_abs z]; ring
    have hrhs : lam / 4 * (|z| * ‖g‖) ^ 2 + (lam / 4)⁻¹ * (beta * |z| * |w| / 2) ^ 2 =
        lam / 4 * (z ^ 2 * ‖g‖ ^ 2) + beta ^ 2 / lam * (z ^ 2 * w ^ 2) := by
      simp only [mul_pow, div_pow, sq_abs]
      field_simp
      ring
    rwa [hlhs, hrhs] at h
  linarith

/-- **The Caccioppoli inequality for a positive truncation of a weak subsolution with
lower-order terms.** Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, and let `b` and `c` be measurable with `‖b‖ ≤ β` and `‖c‖ ≤ γ` on `Ω`. Let
`u ∈ H¹(Ω)` satisfy

`a(u, v) ≤ ∫_Ω f v`

for every nonnegative `v ∈ H¹₀(Ω)`, where `a` is the energy form of
`-∂ⱼ(aⁱʲ ∂ᵢ ·) + bⁱ ∂ᵢ + c`. At any level `k` for which `w = (u - k)⁺` belongs to `L²(Ω)`, every
smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w² + (4/λ) ∫_Ω ψ² (f - c u) w`.

The bound `γ` on the mass coefficient does not enter the estimate. -/
theorem
    UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp_of_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu := by
  -- Test the subsolution inequality against `v = ψ² w`. Pointwise, the principal part and the
  -- drift are bounded by `mul_sq_mul_norm_sq_le_matrixBilinearForm_add_inner_mul_add`, with the
  -- mass term `c u v` moved next to the forcing. The integration and half-absorption step
  -- `W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise` then applies, with the drift's
  -- quarter of the gradient term carried on both sides and absorbed at the end.
  dsimp only
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- Build the nonnegative test function `v = ψ² (u - k)⁺` in `H¹₀(Ω)`.
  set w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' z
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM'
      hgradM' hcpt hts z
  have hvval : ∀ᵐ x ∂mu.restrict Omega, W1p.value v x = ψ x ^ 2 * W1p.value w x := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with x hvx hzx
    rw [hvx, hzx, smul_eq_mul, smul_eq_mul]
    ring
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x := by
    filter_upwards [hvval, W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp] with x hvx hwx
    rw [hvx, hwx]
    exact mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hsub := hu ⟨v, hv⟩ hnonneg
  simp only at hsub
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  -- Integrability of the energy density, the mass term, and the weighted squares.
  have hE := h.integrable_energyIntegrand_jetField ha hb hc hb_bound hc_bound u v
  have hcu : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) :=
    (memLp_top_of_bound hc gamma (ae_restrict_of_forall_mem Omega.isOpen.measurableSet
      hc_bound)).fun_mul (Lp.memLp _)
  have hmass : Integrable (fun x => c x * W1p.value u x * W1p.value v x) (mu.restrict Omega) :=
    hcu.integrable_mul (Lp.memLp _)
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hX : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq w).bdd_mul hψ2 hψ2M
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_value_sq w).bdd_mul hψ2 hψ2M
  have hF : Integrable (fun x => ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x)
      (mu.restrict Omega) := by
    refine ((((Lp.memLp f).sub hcu).integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2
      hψ2M).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hR : Integrable (fun x => lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
      + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2)) (mu.restrict Omega) :=
    (hX.const_mul _).add (hZ.const_mul _)
  -- The energy density without its mass term, plus the drift's share of the absorption.
  set e : EuclideanSpace ℝ ι → ℝ := fun x =>
    energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x)
        - c x * W1p.value u x * W1p.value v x
      + (lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
        + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2))
  have he : Integrable e (mu.restrict Omega) := (hE.sub' hmass).add hR
  -- On the active set the truncation gradient is `∇u`; off it, the test jet vanishes.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ≤
        e x + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) := by
    filter_upwards [hmem, W1p.gradient_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z] with
        x hx hwg hwv hgv hgz hzv hvv
    by_cases hxu : k < W1p.value u x
    · have hwg_active : W1p.gradient w x = W1p.gradient u x := by
        rw [hwg]
        have hxmem : x ∈ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        exact Set.indicator_of_mem hxmem (⇑(W1p.gradient u))
      have hkey := mul_sq_mul_norm_sq_le_matrixBilinearForm_add_inner_mul_add hlam (ψ x)
        (W1p.value w x) (h.lower_bound hx (W1p.gradient u x))
        (h.upper_bound hx (∇ ψ x) (W1p.gradient u x)) (hb_bound x hx)
      simp only [e]
      rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgz, hvv, hzv, hwg_active]
      simpa [massForm_apply, smul_eq_mul] using hkey
    · have hwg_zero : W1p.gradient w x = 0 := by
        rw [hwg]
        have hxmem : x ∉ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        exact Set.indicator_of_notMem hxmem (⇑(W1p.gradient u))
      have hwv_zero : W1p.value w x = 0 := by
        rw [hwv, max_eq_right (sub_nonpos.mpr (le_of_not_gt hxu))]
      simp only [e]
      rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgz, hvv, hzv, hwg_zero,
        hwv_zero]
      simp [massForm_apply]
  -- The weak subsolution inequality bounds `∫ e` by the forcing, the mass term and `∫ R`.
  have hforce : ∫ x in Omega, e x ∂mu ≤
      ∫ x in Omega, (ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x
        + (lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2))) ∂mu := by
    have hfv : Integrable (fun x => f x * W1p.value v x) (mu.restrict Omega) :=
      (Lp.memLp f).integrable_mul (Lp.memLp _)
    have hFeq : ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu =
        ∫ x in Omega, f x * W1p.value v x ∂mu -
          ∫ x in Omega, c x * W1p.value u x * W1p.value v x ∂mu := by
      rw [← integral_sub hfv hmass]
      refine integral_congr_ae ?_
      filter_upwards [hvval] with x hvx
      rw [hvx]
      ring
    simp only [e]
    rw [integral_add (hE.sub' hmass) hR, integral_sub hE hmass, integral_add hF hR, hFeq,
      ← energyFormH1_def]
    linarith
  have hcacc := W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise hlam w hψ hψM hgradM he
    hpt hforce
  rw [integral_add hF hR, integral_add (hX.const_mul _) (hZ.const_mul _), integral_const_mul,
    integral_const_mul] at hcacc
  -- Absorb the drift's quarter of the gradient term into the left-hand side.
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  set Z := ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
  set F := ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu
  have hsplit : 2 / lam * (F + (lam / 4 * X + beta ^ 2 / lam * Z)) =
      2 / lam * F + X / 2 + (2 * beta / lam) ^ 2 / 2 * Z := by
    field_simp
    ring
  have h4 : 4 / lam * F = 2 * (2 / lam * F) := by ring
  rw [hsplit] at hcacc
  linarith

/-- **The Caccioppoli inequality for a nonnegative-level truncation of a weak subsolution with
lower-order terms.** This specializes
`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp_of_lowerOrder`;
the condition `k ≥ 0` makes `(u - k)⁺ ∈ L²(Ω)` automatic even when `Ω` has infinite measure. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAbove (by norm_num) hk u
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu := by
  have hgeneral := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp_of_lowerOrder
    ha hb hc hb_bound hc_bound hu (W1p.memLp_posPartAbove hk u) hψ hcpt hts
  rw [W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) hk u
    (W1p.memLp_posPartAbove hk u)] at hgeneral
  exact hgeneral

/-- **The zero-forcing Caccioppoli inequality for a nonnegative-level truncation with
lower-order terms.** Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u ≤ 0`. At any level `k ≥ 0`,
with `w = (u - k)⁺`, every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w²`.

This specializes
`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_lowerOrder`: the
mass term `c u w` is nonnegative because `w > 0` forces `u > k ≥ 0`. -/
theorem
    UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos_of_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    {k : ℝ} (hk : 0 ≤ k) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAbove (by norm_num) hk u
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu := by
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_lowerOrder ha hb hc
    hb_bound hc_bound (f := 0) (fun v hv => (hu v hv).trans_eq (integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
      rw [hx, Pi.zero_apply, zero_mul])).symm) hk hψ hcpt hts
  dsimp only at hcacc ⊢
  set w := W1p.posPartAbove (by norm_num) hk u
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  -- Under `c ≥ 0` and `k ≥ 0`, the mass term `c u w` is nonnegative, so the forcing term is not.
  have hforce : ∫ x in Omega, ψ x ^ 2 * ((0 : Lp ℝ 2 (mu.restrict Omega)) x -
      c x * W1p.value u x) * W1p.value w x ∂mu ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [hmem, W1p.value_posPartAbove_ae (by norm_num) hk u,
      Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx hwx hzero
    rw [hwx, hzero, Pi.zero_apply, zero_sub]
    by_cases hxu : k < W1p.value u x
    · have hcu : 0 ≤ c x * W1p.value u x := mul_nonneg (hc_nonneg x hx) (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (neg_nonpos.2 hcu)) (le_max_right _ _)
    · rw [max_eq_right (sub_nonpos.2 (le_of_not_gt hxu)), mul_zero]
  have hlam := h.pos
  linarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 / lam) hforce]

/-- **The Caccioppoli inequality on concentric balls, with lower-order terms.** There is a
constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u ≤ 0`. At any level `k ≥ 0`,
with `w = (u - k)⁺`, and for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `0 < r < R`,

`∫_{B(x₀, r)} ‖∇w‖² ≤ (2 (2Λ/λ)² (C / (R - r))² + (2β/λ)²) ∫_{B(x₀, R)} w²`. -/
theorem exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_of_lowerOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient (W1p.posPartAbove (by norm_num) hk u) x‖ ^ 2 ∂mu ≤
        (2 * (2 * Lam / lam) ^ 2 * (C / (R - r)) ^ 2 + (2 * beta / lam) ^ 2) *
          ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u k hk x₀ r R h ha hb hc hb_bound hc_bound hc_nonneg
    hu hr hrR hball
  -- A cutoff equal to one on `ball x₀ r` and supported in
  -- `closedBall x₀ ((r + R) / 2) ⊆ ball x₀ R`.
  obtain ⟨ψ, hψ, hrange, hone, hts, hgrad⟩ := hC x₀ hr (by linarith : r < (r + R) / 2)
  have htsR : tsupport ψ ⊆ ball x₀ R :=
    hts.trans (closedBall_subset_ball (by linarith))
  have htsΩ : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := htsR.trans hball
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ((r + R) / 2)).of_isClosed_subset (isClosed_tsupport ψ) hts
  set G : ℝ := 2 * (C + 1) / (R - r)
  have hG : ∀ x, ‖∇ ψ x‖ ≤ G := fun x => (hgrad x).trans (by
    rw [(by ring : (r + R) / 2 - r = (R - r) / 2), div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith))
  set w := W1p.posPartAbove (by norm_num) hk u
  have hwv := W1p.value_posPartAbove_ae (by norm_num) hk u
  have hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega) :=
    W1p.memLp_posPartAbove hk u
  -- Caccioppoli's inequality for `w`, with the forcing and mass term dropped.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos_of_lowerOrder ha
    hb hc hb_bound hc_bound hc_nonneg hu hk hψ hcpt htsΩ
  -- On `B(x₀, r)` the cutoff is one.
  have hleft : ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu :=
    MeasureTheory.setIntegral_le_setIntegral_sq_mul_of_eqOn (W1p.integrable_norm_gradient_sq w)
      (fun x => sq_nonneg _) hψ.continuous.aestronglyMeasurable hrange measurableSet_ball
      (hone.mono ball_subset_closedBall) ((ball_subset_ball hrR.le).trans hball)
  -- `∇ψ` vanishes off `B(x₀, R)`, where it is bounded by `G`.
  have hright : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      G ^ 2 * ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu :=
    (W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hG measurableSet_ball htsR
      hwLp.integrable_sq (by
        filter_upwards [hwv] with x hx
        rw [hx])).trans_eq (by rw [inter_eq_right.2 hball])
  -- `ψ² ≤ 1` on `B(x₀, R)`, and `ψ` vanishes off it.
  have hzeroth : ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
    have hψ1 : ∀ x, ψ x ^ 2 ≤ 1 := fun x => by
      obtain ⟨h0, h1⟩ := hrange (mem_range_self x)
      exact pow_le_one₀ h0 h1
    calc ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
        ≤ ∫ x in Omega, (ball x₀ R).indicator (fun x => max (W1p.value u x - k) 0 ^ 2) x ∂mu :=
          integral_mono_ae ((W1p.integrable_value_sq w).bdd_mul
            (hψ.continuous.pow 2).aestronglyMeasurable (c := 1) (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              exact hψ1 x))
            (hwLp.integrable_sq.indicator measurableSet_ball) (by
              filter_upwards [hwv] with x hx
              rw [hx]
              by_cases hxR : x ∈ ball x₀ R
              · rw [indicator_of_mem hxR]
                exact mul_le_of_le_one_left (sq_nonneg _) (hψ1 x)
              · rw [indicator_of_notMem hxR,
                  image_eq_zero_of_notMem_tsupport (fun hx' => hxR (htsR hx'))]
                simp)
      _ = ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
        rw [setIntegral_indicator measurableSet_ball, inter_eq_right.2 hball]
  set I := ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hlam := h.pos
  calc ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu
      ≤ 2 * (2 * Lam / lam) ^ 2 * (G ^ 2 * I) + (2 * beta / lam) ^ 2 * I := by
        refine hleft.trans (hcacc.trans ?_)
        gcongr
    _ = (2 * (2 * Lam / lam) ^ 2 * G ^ 2 + (2 * beta / lam) ^ 2) * I := by ring
    _ = _ := by rw [div_pow]

end PDE

end TauCeti
