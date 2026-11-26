/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The Taylor-remainder operator kernel and its potential bounds

Averaging the integral remainder of the degree-`m` Taylor polynomial (order `m + 1` in
Brenner–Scott) at `x` against a weight function `φ` expresses the remainder integral in terms of a
double integral over `y` and the segment parameter `s ∈ (0, 1)` evaluated at `z = x + s • (y - x)`.
Passing from `(y, s)` to `(z, s)` via the homothety of ratio `s` centred at `x` introduces the Haar
Jacobian `s ^ (-n)` (`n = finrank ℝ E`), while scaling the direction `x - y = s⁻¹ • (x - z)` inside
the `(m + 1)`-homogeneous contraction `IteratedGradient.fullContractL m` contributes
`(s⁻¹) ^ (m + 1)`. Against the Taylor factor `s ^ m`, `m` cancels out of the scalar ray weight:

`w(x, z) = ∫_{s ∈ (0, 1)} φ(x + s⁻¹ • (z - x)) s ^ (-n - 1) ds`.

Multiplying `(m !)⁻¹ * w(x, z)` by `IteratedGradient.fullContractL m (x - z)` produces an
operator-valued kernel `taylorRemainderKernel φ m x z : IteratedGradient E m →L[ℝ] ℝ` that
depends neither on the target function nor on the normalization of the additive Haar measure:

* its support in `z` lies in the star-cone of open segments between `x` and `support φ`, hence in
  `convexHull ℝ (insert x B)` whenever `support φ ⊆ B`, and in `Ω` whenever `x ∈ Ω` and `Ω` is
  star-convex with respect to every point of `support φ`;
* when `support φ ⊆ closedBall x D` (`0 ≤ D`) and `∀ y, ‖φ y‖ ≤ M`, it satisfies the
  Riesz-potential domination
  `‖taylorRemainderKernel φ m x z‖ ≤ (M * D ^ n / (n * m !)) * ‖x - z‖ ^ (m + 1 - n)` at every
  pair `(x, z)` without any measurability hypothesis on `φ`;
* on any bounded set `Ω`, for a measurable cutoff `φ` with `support φ ⊆ closure Ω` and
  `∀ y, ‖φ y‖ ≤ M`, integrating against `taylorRemainderKernel φ m` defines a bounded integral
  operator from `L¹(Ω; IteratedGradient E m)` into `L¹(Ω)`.

## Main declarations

* `TauCeti.taylorRemainderWeight`: the scalar ray integral along `s ∈ (0, 1)`.
* `TauCeti.taylorRemainderKernel`: the operator-valued remainder kernel
  `x z ↦ ((m !)⁻¹ * taylorRemainderWeight φ x z) • IteratedGradient.fullContractL m (x - z)`.
* `TauCeti.support_taylorRemainderKernel_subset_convexHull`,
  `TauCeti.support_taylorRemainderKernel_subset_of_starConvex`: support localization in the convex
  hull and in star-shaped domains.
* `TauCeti.norm_taylorRemainderKernel_le`, `TauCeti.norm_taylorRemainderKernel_le_of_diam_le`:
  pointwise `O(‖x - z‖ ^ (m + 1 - n))` Riesz-kernel bounds, including the chunkiness form.
* `TauCeti.setLIntegral_eNorm_taylorRemainderKernel_le`,
  `TauCeti.eLpNorm_one_setIntegral_taylorRemainderKernel_le`: single-variable and
  `L¹(Ω) → L¹(Ω)` potential estimates on bounded sets.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Proposition 4.2.8, pp. 97–99.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer,
  §7.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set

namespace TauCeti

/-! ### The scalar ray weight -/

section Weight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar ray weight obtained by integrating a cutoff `φ` along the ray from `x` through `z`
against `s ^ (-finrank ℝ E - 1)` over `s ∈ (0, 1)`. -/
def taylorRemainderWeight (φ : E → ℝ) (x z : E) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1)

theorem taylorRemainderWeight_def (φ : E → ℝ) (x z : E) :
    taylorRemainderWeight φ x z =
      ∫ s in Ioo (0 : ℝ) 1, φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) :=
  (rfl)

@[simp]
theorem taylorRemainderWeight_zero (x z : E) :
    taylorRemainderWeight (0 : E → ℝ) x z = 0 := by
  simp [taylorRemainderWeight]

theorem taylorRemainderWeight_const_mul (c : ℝ) (φ : E → ℝ) (x z : E) :
    taylorRemainderWeight (fun y ↦ c * φ y) x z = c * taylorRemainderWeight φ x z := by
  simp only [taylorRemainderWeight, mul_assoc, integral_const_mul]

theorem taylorRemainderWeight_add_right (φ : E → ℝ) (x z v : E) :
    taylorRemainderWeight (fun y ↦ φ (y + v)) x z =
      taylorRemainderWeight φ (x + v) (z + v) := by
  simp only [taylorRemainderWeight, add_sub_add_right_eq_sub]
  congr 1 with s
  rw [add_right_comm x v _]

/-- If the open ray segment `{x + s⁻¹ • (z - x) | s ∈ (0, 1)}` misses `support φ`, the ray weight
at `(x, z)` vanishes. -/
theorem taylorRemainderWeight_eq_zero_of_forall_notMem_support {φ : E → ℝ} {x z : E}
    (h : ∀ s ∈ Ioo (0 : ℝ) 1, x + s⁻¹ • (z - x) ∉ Function.support φ) :
    taylorRemainderWeight φ x z = 0 := by
  rw [taylorRemainderWeight, setIntegral_eq_zero_of_forall_eq_zero]
  intro s hs
  rw [Function.notMem_support.1 (h s hs), zero_mul]

/-- Joint measurability of `taylorRemainderWeight φ` when `φ` is Borel measurable on a
second-countable normed space. -/
theorem measurable_taylorRemainderWeight [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {φ : E → ℝ} (hφ : Measurable φ) :
    Measurable fun p : E × E ↦ taylorRemainderWeight φ p.1 p.2 := by
  let ψ : (E × E) × ℝ → ℝ := fun q ↦
    φ (q.1.1 + q.2⁻¹ • (q.1.2 - q.1.1)) * q.2 ^ (-(finrank ℝ E : ℝ) - 1)
  have hψ : Measurable ψ := by
    refine (hφ.comp (measurable_fst.fst.add ?_)).mul (measurable_snd.pow_const _)
    exact measurable_snd.inv.smul (measurable_fst.snd.sub measurable_fst.fst)
  exact (hψ.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))).measurable

/-- If `s > 0` and `s * D < ‖z - x‖`, the ray point `x + s⁻¹ • (z - x)` lies strictly outside
`closedBall x D`. -/
private theorem ray_notMem_closedBall {x z : E} {D s : ℝ} (hs : 0 < s) (hlt : s * D < ‖z - x‖) :
    x + s⁻¹ • (z - x) ∉ closedBall x D := fun hmem ↦ by
  have hle : dist (x + s⁻¹ • (z - x)) x ≤ D := mem_closedBall.1 hmem
  rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
    inv_mul_le_iff₀ hs] at hle
  exact hlt.not_ge hle

/-- Truncation of `taylorRemainderWeight` to `[‖z - x‖ / D, 1]` when `0 < ‖z - x‖ < D` and
`support φ ⊆ closedBall x D`. -/
private theorem taylorRemainderWeight_eq_intervalIntegral {φ : E → ℝ} {x z : E} {D : ℝ}
    (hdist : 0 < ‖z - x‖) (hleD : ‖z - x‖ < D)
    (hsupp : Function.support φ ⊆ closedBall x D) :
    taylorRemainderWeight φ x z =
      ∫ s in (‖z - x‖ / D)..1,
        φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) := by
  have hDpos : 0 < D := hdist.trans hleD
  set r := ‖z - x‖ / D
  have hr0 : 0 < r := div_pos hdist hDpos
  have hr1 : r < 1 := (div_lt_one hDpos).2 hleD
  let f : ℝ → ℝ := fun s ↦ φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1)
  have heq : EqOn f ((Ico r 1).indicator f) (Ioo (0 : ℝ) 1) := fun s hs ↦ by
    by_cases hsr : r ≤ s
    · exact (indicator_of_mem (s := Ico r 1) ⟨hsr, hs.2⟩ f).symm
    · rw [indicator_of_notMem (s := Ico r 1) fun h ↦ hsr h.1]
      have hlt : s * D < ‖z - x‖ := (lt_div_iff₀ hDpos).1 (lt_of_not_ge hsr)
      have hmiss : x + s⁻¹ • (z - x) ∉ Function.support φ :=
        fun hmem ↦ ray_notMem_closedBall hs.1 hlt (hsupp hmem)
      dsimp only [f]
      rw [Function.notMem_support.1 hmiss, zero_mul]
  have hinter : Ioo (0 : ℝ) 1 ∩ Ico r 1 = Ico r 1 :=
    inter_eq_right.2 fun s hs ↦ ⟨hr0.trans_le hs.1, hs.2⟩
  rw [taylorRemainderWeight, setIntegral_congr_fun measurableSet_Ioo heq,
    setIntegral_indicator measurableSet_Ico, hinter, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hr1.le]

/-- Off the diagonal `z ≠ x`, if `support φ ⊆ closedBall x D` (`0 ≤ D`) and `‖φ y‖ ≤ M`
everywhere, then `‖taylorRemainderWeight φ x z‖ ≤ (M * D ^ n / n) * ‖x - z‖ ^ (-n)` where
`n = finrank ℝ E`. No measurability assumption on `φ` is needed. -/
theorem norm_taylorRemainderWeight_le [FiniteDimensional ℝ E] {φ : E → ℝ} {x z : E} {D M : ℝ}
    (hzx : z ≠ x) (hD : 0 ≤ D) (hsupp : Function.support φ ⊆ closedBall x D)
    (hM : ∀ y, ‖φ y‖ ≤ M) :
    ‖taylorRemainderWeight φ x z‖ ≤
      (M * D ^ finrank ℝ E / finrank ℝ E) * ‖x - z‖ ^ (-(finrank ℝ E : ℝ)) := by
  have : Nontrivial E := ⟨⟨z, x, hzx⟩⟩
  set n := finrank ℝ E
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  have hdist : 0 < ‖z - x‖ := norm_sub_pos_iff.2 hzx
  by_cases hleD : D ≤ ‖z - x‖
  · rw [taylorRemainderWeight_eq_zero_of_forall_notMem_support fun s hs hmem ↦
      ray_notMem_closedBall hs.1 (calc
        s * D ≤ s * ‖z - x‖ := mul_le_mul_of_nonneg_left hleD hs.1.le
        _ < 1 * ‖z - x‖ := mul_lt_mul_of_pos_right hs.2 hdist
        _ = ‖z - x‖ := one_mul _) (hsupp hmem), norm_zero]
    positivity
  · push Not at hleD
    have hDpos : 0 < D := hdist.trans hleD
    set r := ‖z - x‖ / D
    have hr0 : 0 < r := div_pos hdist hDpos
    have hr1 : r < 1 := (div_lt_one hDpos).2 hleD
    have hcont : ContinuousOn (fun s : ℝ ↦ M * s ^ (-(n : ℝ) - 1)) (Icc r 1) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun s hs ↦
        Or.inl (hr0.trans_le hs.1).ne')
    have hint_le : ‖∫ s in r..1, φ (x + s⁻¹ • (z - x)) * s ^ (-(n : ℝ) - 1)‖ ≤
        ∫ s in r..1, M * s ^ (-(n : ℝ) - 1) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hr1.le
        (Eventually.of_forall fun s hs ↦ ?_) (hcont.intervalIntegrable_of_Icc hr1.le)
      have hs0 : 0 < s := hr0.trans hs.1
      rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)]
      exact mul_le_mul_of_nonneg_right (hM _) (Real.rpow_nonneg hs0.le _)
    have hrpow : ∫ s in r..1, M * s ^ (-(n : ℝ) - 1) = M * ((r ^ (-(n : ℝ)) - 1) / n) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by
        have : (0 : ℝ) < n := Nat.cast_pos.2 finrank_pos; linarith, fun h0 ↦ by
        rw [uIcc_of_le hr1.le] at h0; linarith [h0.1]⟩), sub_add_cancel, Real.one_rpow]
      ring
    have hr_val : r ^ (-(n : ℝ)) = D ^ n * ‖x - z‖ ^ (-(n : ℝ)) := by
      have hd_nn : 0 ≤ D / ‖x - z‖ := div_nonneg hD (norm_nonneg _)
      have hr_inv : r = (D / ‖x - z‖)⁻¹ := by rw [norm_sub_rev, inv_div]
      rw [hr_inv, Real.inv_rpow hd_nn, ← Real.rpow_neg hd_nn, neg_neg,
        Real.div_rpow hD (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv,
        ← Real.rpow_neg (norm_nonneg _)]
    rw [taylorRemainderWeight_eq_intervalIntegral hdist hleD hsupp]
    calc
      ‖∫ s in r..1, φ (x + s⁻¹ • (z - x)) * s ^ (-(n : ℝ) - 1)‖ ≤
          M * ((r ^ (-(n : ℝ)) - 1) / n) := hint_le.trans_eq hrpow
      _ ≤ M * (r ^ (-(n : ℝ)) / n) := by gcongr; linarith
      _ = (M * D ^ n / n) * ‖x - z‖ ^ (-(n : ℝ)) := by rw [hr_val]; ring

end Weight

/-! ### The operator-valued Taylor-remainder kernel -/

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator-valued kernel for the degree-`m` Taylor remainder (order `m + 1` in Brenner–Scott)
associated with a cutoff `φ`: at `(x, z)` it scales the full contraction
`IteratedGradient.fullContractL m (x - z)` by `(m.factorial)⁻¹ * taylorRemainderWeight φ x z`. -/
def taylorRemainderKernel (φ : E → ℝ) (m : ℕ) (x z : E) : IteratedGradient E m →L[ℝ] ℝ :=
  ((m.factorial : ℝ)⁻¹ * taylorRemainderWeight φ x z) • IteratedGradient.fullContractL m (x - z)

theorem taylorRemainderKernel_def (φ : E → ℝ) (m : ℕ) (x z : E) :
    taylorRemainderKernel φ m x z =
      ((m.factorial : ℝ)⁻¹ * taylorRemainderWeight φ x z) •
        IteratedGradient.fullContractL m (x - z) :=
  (rfl)

@[simp]
theorem taylorRemainderKernel_apply (φ : E → ℝ) (m : ℕ) (x z : E) (G : IteratedGradient E m) :
    taylorRemainderKernel φ m x z G =
      (m.factorial : ℝ)⁻¹ * taylorRemainderWeight φ x z *
        IteratedGradient.fullContractL m (x - z) G :=
  (rfl)

@[simp]
theorem taylorRemainderKernel_zero_weight (m : ℕ) (x z : E) :
    taylorRemainderKernel (0 : E → ℝ) m x z = 0 := by
  simp [taylorRemainderKernel]

@[simp]
theorem taylorRemainderKernel_self (φ : E → ℝ) (m : ℕ) (x : E) :
    taylorRemainderKernel φ m x x = 0 := by
  simp [taylorRemainderKernel]

@[simp]
theorem taylorRemainderKernel_of_subsingleton [Subsingleton E] (φ : E → ℝ) (m : ℕ) (x z : E) :
    taylorRemainderKernel φ m x z = 0 := by
  rw [Subsingleton.elim z x, taylorRemainderKernel_self]

theorem taylorRemainderKernel_const_mul (c : ℝ) (φ : E → ℝ) (m : ℕ) (x z : E) :
    taylorRemainderKernel (fun y ↦ c * φ y) m x z = c • taylorRemainderKernel φ m x z := by
  ext G
  simp only [taylorRemainderKernel_apply, taylorRemainderWeight_const_mul,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- For fixed `x`, every point `z` in `support (taylorRemainderKernel φ m x)` lies on the open
segment from `x` to some point `y ∈ support φ`. -/
theorem support_taylorRemainderKernel_subset_image (φ : E → ℝ) (m : ℕ) (x : E) :
    Function.support (taylorRemainderKernel φ m x) ⊆
      (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Ioo (0 : ℝ) 1 ×ˢ Function.support φ) := by
  intro z hz
  rw [Function.mem_support] at hz
  have hw : taylorRemainderWeight φ x z ≠ 0 := fun hw0 ↦ by
    simp [taylorRemainderKernel, hw0] at hz
  by_contra hnot
  refine hw (taylorRemainderWeight_eq_zero_of_forall_notMem_support fun s hs hmem ↦ hnot ?_)
  refine ⟨(s, x + s⁻¹ • (z - x)), ⟨hs, hmem⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs.1.ne', one_smul, add_sub_cancel]

/-- Whenever `support φ ⊆ B`, the kernel `z ↦ taylorRemainderKernel φ m x z` is supported in the
convex hull of `insert x B`. -/
theorem support_taylorRemainderKernel_subset_convexHull {φ : E → ℝ} {B : Set E}
    (hB : Function.support φ ⊆ B) (m : ℕ) (x : E) :
    Function.support (taylorRemainderKernel φ m x) ⊆ convexHull ℝ (insert x B) := by
  refine (support_taylorRemainderKernel_subset_image φ m x).trans ?_
  rintro _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  exact segment_subset_convexHull (mem_insert x B) (mem_insert_of_mem x (hB hy))
    (segment_eq_image' ℝ x y ▸ mem_image_of_mem _ (Ioo_subset_Icc_self hs))

/-- If `Ω` is star-convex with respect to every point of `support φ`, then for each `x ∈ Ω` the
support of `z ↦ taylorRemainderKernel φ m x z` is contained in `Ω`. -/
theorem support_taylorRemainderKernel_subset_of_starConvex {φ : E → ℝ} {Ω : Set E} {x : E}
    (hx : x ∈ Ω) (hstar : ∀ y ∈ Function.support φ, StarConvex ℝ y Ω) (m : ℕ) :
    Function.support (taylorRemainderKernel φ m x) ⊆ Ω := by
  refine (support_taylorRemainderKernel_subset_image φ m x).trans ?_
  rintro _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  exact (hstar y hy).segment_subset hx
    (segment_symm ℝ y x ▸ segment_eq_image' ℝ x y ▸ mem_image_of_mem _ (Ioo_subset_Icc_self hs))

/-- When `φ` has compact support, the topological support of `z ↦ taylorRemainderKernel φ m x z`
lies in the compact star-cone over `tsupport φ` with vertex `x`. -/
theorem tsupport_taylorRemainderKernel_subset_image {φ : E → ℝ} (hcpt : HasCompactSupport φ)
    (m : ℕ) (x : E) :
    tsupport (taylorRemainderKernel φ m x) ⊆
      (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ) := by
  have hK : IsCompact ((fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ)) :=
    (isCompact_Icc.prod hcpt).image (by fun_prop)
  refine closure_minimal ((support_taylorRemainderKernel_subset_image φ m x).trans ?_) hK.isClosed
  exact image_mono (prod_mono Ioo_subset_Icc_self (subset_tsupport φ))

theorem hasCompactSupport_taylorRemainderKernel {φ : E → ℝ} (hcpt : HasCompactSupport φ)
    (m : ℕ) (x : E) :
    HasCompactSupport (taylorRemainderKernel φ m x) :=
  ((isCompact_Icc.prod hcpt).image (by fun_prop)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_taylorRemainderKernel_subset_image hcpt m x)

/-- Joint strong measurability of `(x, z) ↦ taylorRemainderKernel φ m x z` when `φ` is Borel
measurable on a finite-dimensional real inner product space. -/
theorem stronglyMeasurable_taylorRemainderKernel [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {φ : E → ℝ} (hφ : Measurable φ) (m : ℕ) :
    StronglyMeasurable fun p : E × E ↦ taylorRemainderKernel φ m p.1 p.2 := by
  have hw : StronglyMeasurable fun p : E × E ↦
      (m.factorial : ℝ)⁻¹ * taylorRemainderWeight φ p.1 p.2 :=
    (measurable_const.mul (measurable_taylorRemainderWeight hφ)).stronglyMeasurable
  have hc : StronglyMeasurable fun p : E × E ↦ IteratedGradient.fullContractL m (p.1 - p.2) :=
    ((IteratedGradient.continuous_fullContractL m).comp
      (continuous_fst.sub continuous_snd)).stronglyMeasurable
  exact hw.smul hc

/-- **Pointwise Riesz-kernel domination of `taylorRemainderKernel`.** If
`support φ ⊆ closedBall x D` (`0 ≤ D`) and `‖φ y‖ ≤ M` for all `y`, then at every pair `(x, z)`
(including `x = z` and dimension zero),
`‖taylorRemainderKernel φ m x z‖ ≤ (M * D ^ n / (n * m.factorial)) * ‖x - z‖ ^ (m + 1 - n)`,
where `n = finrank ℝ E`. No measurability assumption on `φ` is needed. -/
theorem norm_taylorRemainderKernel_le [FiniteDimensional ℝ E] {φ : E → ℝ} (m : ℕ) {x z : E}
    {D M : ℝ} (hD : 0 ≤ D) (hsupp : Function.support φ ⊆ closedBall x D) (hM : ∀ y, ‖φ y‖ ≤ M) :
    ‖taylorRemainderKernel φ m x z‖ ≤
      (M * D ^ finrank ℝ E / (finrank ℝ E * m.factorial)) *
        ‖x - z‖ ^ ((m + 1 : ℝ) - finrank ℝ E) := by
  set n := finrank ℝ E
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  rcases eq_or_ne x z with rfl | hxz
  · rw [taylorRemainderKernel_self, norm_zero]
    positivity
  · have hpos : 0 < ‖x - z‖ := norm_sub_pos_iff.2 hxz
    have hw := norm_taylorRemainderWeight_le hxz.symm hD hsupp hM
    have hc := IteratedGradient.norm_fullContractL_le m (x - z)
    rw [taylorRemainderKernel, norm_smul, norm_mul,
      Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg m.factorial))]
    calc
      (m.factorial : ℝ)⁻¹ * ‖taylorRemainderWeight φ x z‖ *
          ‖IteratedGradient.fullContractL m (x - z)‖ ≤
          (m.factorial : ℝ)⁻¹ * ((M * D ^ n / n) * ‖x - z‖ ^ (-(n : ℝ))) * ‖x - z‖ ^ (m + 1) := by
        gcongr
      _ = (M * D ^ n / (n * m.factorial)) * (‖x - z‖ ^ (-(n : ℝ)) * ‖x - z‖ ^ (m + 1 : ℝ)) := by
        rw [← Real.rpow_natCast ‖x - z‖ (m + 1), Nat.cast_add, Nat.cast_one]
        ring
      _ = (M * D ^ n / (n * m.factorial)) * ‖x - z‖ ^ ((m + 1 : ℝ) - n) := by
        rw [← Real.rpow_add hpos]
        congr 2
        ring

/-- **Chunkiness form of the kernel bound** (Brenner–Scott, Proposition 4.2.8). When `Ω` is bounded
with `diam Ω ≤ γ * ρ` (`0 < ρ`), `support φ ⊆ closure Ω`, and `‖φ y‖ ≤ C₀ * ρ ^ (-n)`, every
`x ∈ closure Ω` and `z : E` satisfy
`‖taylorRemainderKernel φ m x z‖ ≤ (C₀ * γ ^ n / (n * m.factorial)) * ‖x - z‖ ^ (m + 1 - n)`. -/
theorem norm_taylorRemainderKernel_le_of_diam_le [FiniteDimensional ℝ E] {φ : E → ℝ} {Ω : Set E}
    (hb : Bornology.IsBounded Ω) (hsupp : Function.support φ ⊆ closure Ω) {ρ γ C₀ : ℝ}
    (hρ : 0 < ρ) (hdiam : diam Ω ≤ γ * ρ) (hφ : ∀ y, ‖φ y‖ ≤ C₀ * ρ ^ (-(finrank ℝ E : ℝ)))
    (m : ℕ) {x : E} (hx : x ∈ closure Ω) (z : E) :
    ‖taylorRemainderKernel φ m x z‖ ≤
      (C₀ * γ ^ finrank ℝ E / (finrank ℝ E * m.factorial)) *
        ‖x - z‖ ^ ((m + 1 : ℝ) - finrank ℝ E) := by
  have hγρ : 0 ≤ γ * ρ := diam_nonneg.trans hdiam
  have hball : Function.support φ ⊆ closedBall x (γ * ρ) := fun y hy ↦ by
    rw [mem_closedBall]
    exact (dist_le_diam_of_mem hb.closure (hsupp hy) hx).trans
      ((diam_closure (s := Ω)).le.trans hdiam)
  refine (norm_taylorRemainderKernel_le m hγρ hball hφ).trans_eq ?_
  congr 1
  have hr_pow : ρ ^ (-(finrank ℝ E : ℝ)) * ρ ^ finrank ℝ E = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hρ, neg_add_cancel, Real.rpow_zero]
  calc
    C₀ * ρ ^ (-(finrank ℝ E : ℝ)) * (γ * ρ) ^ finrank ℝ E / (finrank ℝ E * m.factorial) =
        C₀ * γ ^ finrank ℝ E * (ρ ^ (-(finrank ℝ E : ℝ)) * ρ ^ finrank ℝ E) /
          (finrank ℝ E * m.factorial) := by rw [mul_pow]; ring
    _ = C₀ * γ ^ finrank ℝ E / (finrank ℝ E * m.factorial) := by rw [hr_pow, mul_one]

end Kernel

/-! ### Bounded-domain `L¹(Ω) → L¹(Ω)` potential estimate -/

section PotentialL1

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- On a bounded set `Ω`, if `support φ ⊆ closure Ω` and `‖φ y‖ ≤ M` for all `y`, then for
`z ∈ closure Ω` integrating `x ↦ ‖taylorRemainderKernel φ m x z‖ₑ` over `Ω` is bounded by
`M * μ(B(0, 1)) / (m + 1)! * (diam Ω) ^ (n + m + 1)`, where `n = finrank ℝ E`, with no
measurability hypothesis on `Ω` or `φ`. -/
theorem setLIntegral_eNorm_taylorRemainderKernel_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hsupp : Function.support φ ⊆ closure Ω) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (m : ℕ) {z : E} (hz : z ∈ closure Ω) :
    ∫⁻ x in Ω, ‖taylorRemainderKernel φ m x z‖ₑ ∂μ ≤
      ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial *
        diam Ω ^ (finrank ℝ E + m + 1)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [taylorRemainderKernel_of_subsingleton, ← ofReal_norm, norm_zero,
      ENNReal.ofReal_zero, lintegral_zero, zero_le]
  set n := finrank ℝ E
  set D := diam Ω
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 finrank_pos
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  have hD : 0 ≤ D := diam_nonneg
  let C_K : ℝ := M * D ^ n / (n * m.factorial)
  have hCK0 : 0 ≤ C_K := by positivity
  have hpt : ∀ x ∈ closure Ω, ‖taylorRemainderKernel φ m x z‖ₑ ≤
      ENNReal.ofReal C_K * ‖z - x‖ₑ ^ ((m + 1 : ℝ) - n) := fun x hx ↦ by
    rcases eq_or_ne x z with rfl | hxz
    · simp only [taylorRemainderKernel_self, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_le]
    · have hball : Function.support φ ⊆ closedBall x D := fun y hy ↦ mem_closedBall.2 <|
        (dist_le_diam_of_mem hb.closure (hsupp hy) hx).trans_eq (diam_closure Ω)
      have hpos : 0 < ‖z - x‖ := norm_sub_pos_iff.2 hxz.symm
      rw [← ofReal_norm, ← ofReal_norm (z - x), ENNReal.ofReal_rpow_of_pos hpos,
        ← ENNReal.ofReal_mul hCK0, norm_sub_rev z x]
      exact ENNReal.ofReal_le_ofReal (norm_taylorRemainderKernel_le m hD hball hM)
  have hsub_ball : closure Ω ⊆ closedBall z D := fun x hx ↦
    mem_closedBall.2 <| (dist_le_diam_of_mem hb.closure hx hz).trans_eq (diam_closure Ω)
  calc
    ∫⁻ x in Ω, ‖taylorRemainderKernel φ m x z‖ₑ ∂μ
      ≤ ∫⁻ x in closure Ω, ‖taylorRemainderKernel φ m x z‖ₑ ∂μ :=
        lintegral_mono' (Measure.restrict_mono subset_closure le_rfl) le_rfl
    _ ≤ ∫⁻ x in closure Ω, ENNReal.ofReal C_K * ‖z - x‖ₑ ^ ((m + 1 : ℝ) - n) ∂μ :=
        lintegral_mono_ae (ae_restrict_of_forall_mem isClosed_closure.measurableSet hpt)
    _ ≤ ∫⁻ x in closedBall z D, ENNReal.ofReal C_K * ‖z - x‖ₑ ^ ((m + 1 : ℝ) - n) ∂μ :=
        lintegral_mono' (Measure.restrict_mono hsub_ball le_rfl) le_rfl
    _ = ENNReal.ofReal C_K * ∫⁻ x in closedBall z D, ‖z - x‖ₑ ^ ((m + 1 : ℝ) - n) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial * D ^ (n + m + 1)) := by
        rw [setLIntegral_closedBall_enorm_sub_rpow (by linarith) hD z, ← ENNReal.ofReal_mul hCK0]
        congr 1
        have hexp : (n : ℝ) + ((m + 1 : ℝ) - n) = (m + 1 : ℝ) := by ring
        have hpow : D ^ (m + 1 : ℝ) = D ^ (m + 1) := by
          rw [← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
        have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * m.factorial := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hadd : n + m + 1 = n + (m + 1) := by omega
        rw [hexp, hpow, hfac, hadd]
        dsimp only [C_K, n] at hn0 ⊢
        field_simp [hn0.ne']
        rw [pow_add, pow_succ]
        ring

/-- Joint product integrability for `(x, z) ↦ taylorRemainderKernel φ m x z (G z)` on
`(μ.restrict Ω).prod (μ.restrict Ω)` when `Ω` is bounded and `G` is integrable on `Ω`. -/
private theorem integrable_taylorRemainderKernel_prod {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    Integrable (fun p : E × E ↦ taylorRemainderKernel φ m p.1 p.2 (G p.2))
      ((μ.restrict Ω).prod (μ.restrict Ω)) := by
  let ν : Measure E := μ.restrict Ω
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  let F : E × E → ℝ := fun p ↦ taylorRemainderKernel φ m p.1 p.2 (G p.2)
  let C : ℝ := M * μ.real (ball (0 : E) 1) / (m + 1).factorial * diam Ω ^ (finrank ℝ E + m + 1)
  have hF_meas : AEStronglyMeasurable F (ν.prod ν) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((stronglyMeasurable_taylorRemainderKernel hφ_meas m).aestronglyMeasurable.prodMk
        hG.aestronglyMeasurable.comp_snd)
  have hae_cl : ∀ᵐ z ∂ν, z ∈ closure Ω :=
    (ae_restrict_iff isClosed_closure.measurableSet).2 (.of_forall fun _ hz ↦ subset_closure hz)
  have hbound : ∫⁻ p, ‖F p‖ₑ ∂ν.prod ν ≤ ENNReal.ofReal C * eLpNorm G 1 ν := by
    calc
      ∫⁻ p, ‖F p‖ₑ ∂ν.prod ν
        = ∫⁻ z, ∫⁻ x, ‖F (x, z)‖ₑ ∂ν ∂ν := lintegral_prod_symm _ hF_meas.eNorm
      _ ≤ ∫⁻ z, ∫⁻ x, ‖taylorRemainderKernel φ m x z‖ₑ * ‖G z‖ₑ ∂ν ∂ν :=
          lintegral_mono fun z ↦ lintegral_mono fun x ↦ (taylorRemainderKernel φ m x z).le_opENorm _
      _ = ∫⁻ z, (∫⁻ x, ‖taylorRemainderKernel φ m x z‖ₑ ∂ν) * ‖G z‖ₑ ∂ν :=
          lintegral_congr fun z ↦ lintegral_mul_const' _ _ eNorm_ne_top
      _ ≤ ∫⁻ z, ENNReal.ofReal C * ‖G z‖ₑ ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae_cl] with z hz
          gcongr
          exact setLIntegral_eNorm_taylorRemainderKernel_le hb hsupp hM m hz
      _ = ENNReal.ofReal C * eLpNorm G 1 ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            eLpNorm_one_eq_lintegral_eNorm hG.aestronglyMeasurable]
  refine ⟨hF_meas, ?_⟩
  rw [hasFiniteIntegral_def]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (memLp_one_iff_integrable.2 hG).eLpNorm_lt_top)

/-- On a bounded set `Ω`, for a measurable cutoff `φ` with `support φ ⊆ closure Ω` and
`∀ y, ‖φ y‖ ≤ M`, if `G` is integrable on `Ω`, then for almost every `x ∈ Ω` the slice
`z ↦ taylorRemainderKernel φ m x z (G z)` is integrable on `Ω`. -/
theorem ae_integrableOn_taylorRemainderKernel_apply {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    ∀ᵐ x ∂μ.restrict Ω, IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (G z)) Ω μ := by
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  exact (integrable_taylorRemainderKernel_prod hb hφ_meas hsupp hM hG).prod_right_ae

/-- On a bounded set `Ω`, for a measurable cutoff `φ` with `support φ ⊆ closure Ω` and
`∀ y, ‖φ y‖ ≤ M`, the integral operator `x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z)` maps
`L¹(Ω; IteratedGradient E m)` into `L¹(Ω)`. -/
theorem integrableOn_setIntegral_taylorRemainderKernel_apply {Ω : Set E}
    (hb : Bornology.IsBounded Ω) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hsupp : Function.support φ ⊆ closure Ω) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    {G : E → IteratedGradient E m} (hG : IntegrableOn G Ω μ) :
    IntegrableOn (fun x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z) ∂μ) Ω μ :=
  (integrable_taylorRemainderKernel_prod hb hφ_meas hsupp hM hG).integral_prod_left

/-- **`L¹(Ω) → L¹(Ω)` norm bound for the Taylor-remainder integral operator** on a bounded set
`Ω`, for a measurable cutoff `φ` with `support φ ⊆ closure Ω` and `∀ y, ‖φ y‖ ≤ M`, stated in
terms of `eLpNorm · 1 (μ.restrict Ω)`. -/
theorem eLpNorm_one_setIntegral_taylorRemainderKernel_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    eLpNorm (fun x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z) ∂μ) 1 (μ.restrict Ω) ≤
      ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial *
        diam Ω ^ (finrank ℝ E + m + 1)) * eLpNorm G 1 (μ.restrict Ω) := by
  have hcol : ∀ᵐ z ∂μ.restrict Ω, ∫⁻ x in Ω, ‖taylorRemainderKernel φ m x z‖ₑ ∂μ ≤
      ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial *
        diam Ω ^ (finrank ℝ E + m + 1)) :=
    ((ae_restrict_iff isClosed_closure.measurableSet).2
      (.of_forall fun _ hz ↦ subset_closure hz)).mono fun _ hz ↦
        setLIntegral_eNorm_taylorRemainderKernel_le hb hsupp hM m hz
  exact (eLpNorm_integral_apply_le
      (stronglyMeasurable_taylorRemainderKernel hφ_meas m).aestronglyMeasurable
      hG.aestronglyMeasurable le_rfl (.of_forall fun _ ↦ le_top) hcol).trans_eq (by simp)

end PotentialL1

/-! ### Concrete checks -/

section Examples

/-- Dimension-zero boundary check: on `EuclideanSpace ℝ (Fin 0)`, `taylorRemainderKernel` vanishes
identically for every cutoff `φ` and degree `m`. -/
example (φ : EuclideanSpace ℝ (Fin 0) → ℝ) (m : ℕ) (x z : EuclideanSpace ℝ (Fin 0)) :
    taylorRemainderKernel φ m x z = 0 :=
  taylorRemainderKernel_of_subsingleton φ m x z

end Examples

end TauCeti
