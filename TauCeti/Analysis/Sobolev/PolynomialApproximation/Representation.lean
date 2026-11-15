/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.IteratedGradient.Taylor
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.MeasureTheory.Integral.Dilation
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The Taylor-remainder kernel and Sobolev representation formula

Averaging Taylor's integral remainder of order `m` at `x` against a weight function `φ` with unit
integral expresses the error `u x - ∫ φ(y) T^m_y u(x) dy` as a double integral over `y` and the
segment parameter `s ∈ (0, 1)` evaluated at `z = x + s • (y - x)`. Passing from `(y, s)` to
`(z, s)` via the homothety of ratio `s` centred at `x` picks up the Haar Jacobian `s ^ (-n)`
(`n = finrank ℝ E`), while scaling the direction `x - y = s⁻¹ • (x - z)` inside the `(m + 1)`-linear
contraction `IteratedGradient.fullContractL m` contributes `(s⁻¹) ^ (m + 1)`. Against the Taylor
factor `s ^ m`, the order `m` cancels out of the ray weight:

`w(x, z) = ∫_{s ∈ (0, 1)} φ(x + s⁻¹ • (z - x)) s ^ (-n - 1) ds`.

Multiplying `(m !)⁻¹ * w(x, z)` by `IteratedGradient.fullContractL m (x - z)` produces an
operator-valued kernel `taylorRemainderKernel φ m x z : IteratedGradient E m →L[ℝ] ℝ` that
depends neither on `u` nor on the normalization of the additive Haar measure:

* its support in `z` lies in the star-cone of segments between `x` and `support φ`, hence in
  `convexHull ℝ (insert x B)` whenever `support φ ⊆ B`, and in `Ω` whenever `Ω` is star-convex
  with respect to every point of `support φ`;
* when `support φ ⊆ closedBall x D` and `‖φ‖_∞ ≤ M`, it satisfies the Riesz-potential domination
  `‖taylorRemainderKernel φ m x z‖ ≤ (M * D ^ n / (n * m !)) * ‖x - z‖ ^ (m + 1 - n)` at every
  pair `(x, z)` without any measurability hypothesis on `φ`;
* on a bounded open set `Ω` star-convex with respect to `tsupport φ`, integrating against
  `taylorRemainderKernel φ m` defines a bounded integral operator on `L¹(Ω)`, so Meyers–Serrin
  density extends the smooth representation identity to every `u ∈ W^{m+1,p}(Ω)` (`1 ≤ p ≤ ∞`).

## Main declarations

* `TauCeti.taylorRemainderWeight`: the scalar ray integral along `s ∈ (0, 1)`.
* `TauCeti.taylorRemainderKernel`: the operator-valued remainder kernel
  `x z ↦ ((m !)⁻¹ * taylorRemainderWeight φ x z) • IteratedGradient.fullContractL m (x - z)`.
* `TauCeti.support_taylorRemainderKernel_subset_convexHull`,
  `TauCeti.support_taylorRemainderKernel_subset_of_starConvex`: support localization in the convex
  hull and in star-shaped domains.
* `TauCeti.norm_taylorRemainderKernel_le`, `TauCeti.norm_taylorRemainderKernel_le_of_diam_le`:
  pointwise `O(‖x - z‖ ^ (m + 1 - n))` Riesz-kernel bounds, including the chunkiness form.
* `TauCeti.sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel`: the pointwise
  representation formula for `C^{m+1}` functions on star-shaped open sets.
* `TauCeti.eLpNorm_one_setIntegral_taylorRemainderKernel_le`: the `L¹(Ω) → L¹(Ω)` potential bound on
  bounded sets.
* `TauCeti.Wkp.averagedTaylorEval`: the derivative-form averaged Taylor polynomial of a Sobolev
  function `u ∈ W^{m,p}(Ω)` evaluated at `x`, with linearity lemmas `averagedTaylorEval_add` and
  `averagedTaylorEval_smul`.
* `TauCeti.Wkp.ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel`: the Sobolev
  representation formula on `W^{m+1,p}(Ω)` for every `1 ≤ p ≤ ∞`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Proposition 4.2.8, pp. 97–99.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer,
  §7.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Topology

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
      have hmiss : x + s⁻¹ • (z - x) ∉ Function.support φ := fun hmem ↦ by
        have hle : dist (x + s⁻¹ • (z - x)) x ≤ D := mem_closedBall.1 (hsupp hmem)
        rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.1.le),
          inv_mul_le_iff₀ hs.1] at hle
        exact hlt.not_ge hle
      dsimp only [f]
      rw [Function.notMem_support.1 hmiss, zero_mul]
  have hinter : Ioo (0 : ℝ) 1 ∩ Ico r 1 = Ico r 1 :=
    inter_eq_right.2 fun s hs ↦ ⟨hr0.trans_le hs.1, hs.2⟩
  rw [taylorRemainderWeight, setIntegral_congr_fun measurableSet_Ioo heq,
    setIntegral_indicator measurableSet_Ico, hinter, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hr1.le]

/-- Off the diagonal `z ≠ x`, if `support φ ⊆ closedBall x D` and `‖φ y‖ ≤ M` everywhere, then
`‖taylorRemainderWeight φ x z‖ ≤ (M * D ^ n / n) * ‖x - z‖ ^ (-n)` where `n = finrank ℝ E`. No
measurability assumption on `φ` is needed. -/
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
  · rw [taylorRemainderWeight_eq_zero_of_forall_notMem_support fun s hs hmem ↦ by
      have hle : dist (x + s⁻¹ • (z - x)) x ≤ D := mem_closedBall.1 (hsupp hmem)
      rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.1.le),
        inv_mul_le_iff₀ hs.1] at hle
      exact (calc s * D ≤ s * ‖z - x‖ := mul_le_mul_of_nonneg_left hleD hs.1.le
        _ < 1 * ‖z - x‖ := mul_lt_mul_of_pos_right hs.2 hdist
        _ = ‖z - x‖ := one_mul _).not_ge hle, norm_zero]
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

/-- The operator-valued Taylor-remainder kernel of order `m` associated with a cutoff `φ`: at
`(x, z)` it scales the full contraction `IteratedGradient.fullContractL m (x - z)` by
`(m.factorial)⁻¹ * taylorRemainderWeight φ x z`. -/
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
      (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ Function.support φ) := by
  intro z hz
  rw [Function.mem_support] at hz
  have hw : taylorRemainderWeight φ x z ≠ 0 := fun hw0 ↦ by
    simp [taylorRemainderKernel, hw0] at hz
  by_contra hnot
  refine hw (taylorRemainderWeight_eq_zero_of_forall_notMem_support fun s hs hmem ↦ hnot ?_)
  refine ⟨(s, x + s⁻¹ • (z - x)), ⟨Ioo_subset_Icc_self hs, hmem⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs.1.ne', one_smul, add_sub_cancel]

/-- Whenever `support φ ⊆ B`, the kernel `z ↦ taylorRemainderKernel φ m x z` is supported in the
convex hull of `insert x B`. -/
theorem support_taylorRemainderKernel_subset_convexHull {φ : E → ℝ} {B : Set E}
    (hB : Function.support φ ⊆ B) (m : ℕ) (x : E) :
    Function.support (taylorRemainderKernel φ m x) ⊆ convexHull ℝ (insert x B) := by
  refine (support_taylorRemainderKernel_subset_image φ m x).trans ?_
  rintro _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  have hseg : x + s • (y - x) ∈ segment ℝ x y :=
    ⟨1 - s, s, sub_nonneg.2 hs.2, hs.1, sub_add_cancel 1 s, by module⟩
  exact segment_subset_convexHull (mem_insert x B) (mem_insert_of_mem x (hB hy)) hseg

/-- If `Ω` is star-convex with respect to every point of `support φ`, then for each `x ∈ Ω` the
support of `z ↦ taylorRemainderKernel φ m x z` is contained in `Ω`. -/
theorem support_taylorRemainderKernel_subset_of_starConvex {φ : E → ℝ} {Ω : Set E} {x : E}
    (hx : x ∈ Ω) (hstar : ∀ y ∈ Function.support φ, StarConvex ℝ y Ω) (m : ℕ) :
    Function.support (taylorRemainderKernel φ m x) ⊆ Ω := by
  refine (support_taylorRemainderKernel_subset_image φ m x).trans ?_
  rintro _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  have hcomb : s • y + (1 - s) • x = x + s • (y - x) := by module
  simpa only [hcomb] using hstar y hy hx hs.1 (sub_nonneg.2 hs.2) (add_sub_cancel s 1)

/-- When `φ` has compact support, the topological support of `z ↦ taylorRemainderKernel φ m x z`
lies in the compact star-cone over `tsupport φ` with vertex `x`. -/
theorem tsupport_taylorRemainderKernel_subset_image {φ : E → ℝ} (hcpt : HasCompactSupport φ)
    (m : ℕ) (x : E) :
    tsupport (taylorRemainderKernel φ m x) ⊆
      (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ) := by
  have hK : IsCompact ((fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ)) :=
    (isCompact_Icc.prod hcpt).image (by fun_prop)
  refine closure_minimal ((support_taylorRemainderKernel_subset_image φ m x).trans ?_) hK.isClosed
  exact image_mono (prod_mono_right (subset_tsupport φ))

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

/-- Pointwise rescaling identity relating the `(y, s)` segment integrand and the `(z, s)` spatial
ray integrand along the homothety `y ↦ x + s • (y - x)` for `s > 0`. -/
private theorem ray_integrand_comp_homothety (φ : E → ℝ) {m : ℕ} (G : E → IteratedGradient E m)
    (x y : E) {s : ℝ} (hs : 0 < s) :
    φ (x + s⁻¹ • (AffineMap.homothety x s y - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - AffineMap.homothety x s y)
          (G (AffineMap.homothety x s y)) =
      (s ^ finrank ℝ E)⁻¹ * (φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) := by
  set n := finrank ℝ E
  have hhom : AffineMap.homothety x s y = x + s • (y - x) := by
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  have hinv : x + s⁻¹ • (x + s • (y - x) - x) = y := by
    rw [add_sub_cancel_left, inv_smul_smul₀ hs.ne', add_sub_cancel]
  have hdir : x - (x + s • (y - x)) = s • (x - y) := by
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← smul_neg, neg_sub]
  have hexp : s ^ (-(n : ℝ) - 1) * s ^ (m + 1) = (s ^ n)⁻¹ * s ^ m := by
    rw [← Real.rpow_natCast s (m + 1), ← Real.rpow_add hs, ← Real.rpow_natCast s n,
      ← Real.rpow_neg hs.le, ← Real.rpow_natCast s m, ← Real.rpow_add hs]
    congr 1; push_cast; ring
  rw [hhom, hinv, hdir, IteratedGradient.fullContractL_smul_direction,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  calc
    φ y * s ^ (-(n : ℝ) - 1) * (s ^ (m + 1) *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) =
      φ y * (s ^ (-(n : ℝ) - 1) * s ^ (m + 1)) *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x))) := by ring
    _ = (s ^ n)⁻¹ * (φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) := by
      rw [hexp]; ring

end Kernel

/-! ### Smooth representation formula via homothety ray change of variables -/

section SmoothRepresentation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Product integrability of the `(y, s)` segment integrand when `φ` has compact support and both
`φ` and `G` are bounded and strongly measurable. -/
private theorem integrable_segment_prod {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    {G : E → IteratedGradient E m} (hG_meas : StronglyMeasurable G) {C : ℝ}
    (hG_bound : ∀ z, ‖G z‖ ≤ C) (x : E) :
    Integrable
      (fun p : E × ℝ ↦ φ p.1 * p.2 ^ m *
        IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x))))
      (μ.prod ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hH_meas : StronglyMeasurable fun p : E × ℝ ↦ φ p.1 * p.2 ^ m *
      IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x))) := by
    refine (((hφ_meas.comp measurable_fst).mul (measurable_snd.pow_const m)).stronglyMeasurable).mul
      ?_
    exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((((IteratedGradient.continuous_fullContractL m).comp
        (continuous_const.sub continuous_fst)).stronglyMeasurable).prodMk
        (hG_meas.comp_measurable (measurable_const.add (measurable_snd.smul
          (measurable_fst.sub measurable_const)))))
  obtain ⟨R₀, hR₀⟩ := hcpt.isBounded.subset_closedBall x
  set R := max R₀ 0
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ_bound 0)
  have hC0 : 0 ≤ C := (norm_nonneg (G 0)).trans (hG_bound 0)
  have hdom : Integrable ((tsupport φ ×ˢ (univ : Set ℝ)).indicator
      (fun _ : E × ℝ ↦ M * (C * R ^ (m + 1)))) (μ.prod ν) := by
    rw [integrable_indicator_iff (hcpt.isClosed.measurableSet.prod MeasurableSet.univ)]
    exact integrableOn_const ((Measure.prod_prod (tsupport φ) univ).trans_lt
      (ENNReal.mul_lt_top hcpt.measure_lt_top (measure_lt_top ν univ))).ne
  have hae_s : ∀ᵐ p : E × ℝ ∂μ.prod ν, p.2 ∈ Ioo (0 : ℝ) 1 := by
    have hnull : (μ.prod ν) (univ ×ˢ (Ioo (0 : ℝ) 1)ᶜ) = 0 := by
      rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl,
        compl_inter_self, measure_empty, mul_zero]
    exact Filter.eventually_of_mem (compl_mem_ae_iff.2 hnull) fun p hp ↦
      by_contra fun hnot ↦ hp ⟨mem_univ p.1, hnot⟩
  refine hdom.mono' hH_meas.aestronglyMeasurable ?_
  filter_upwards [hae_s] with p hp
  by_cases hp1 : p.1 ∈ tsupport φ
  · rw [indicator_of_mem (s := tsupport φ ×ˢ (univ : Set ℝ)) ⟨hp1, mem_univ p.2⟩,
      norm_mul, norm_mul]
    have hdist : ‖x - p.1‖ ≤ R := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact (mem_closedBall.1 (hR₀ hp1)).trans (le_max_left R₀ 0)
    have hs1 : ‖p.2 ^ m‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (pow_nonneg hp.1.le m)]
      exact pow_le_one₀ hp.1.le hp.2.le
    have hfc : ‖IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x)))‖ ≤
        C * R ^ (m + 1) :=
      (IteratedGradient.norm_fullContractL_apply_le m _ _).trans
        (mul_le_mul (hG_bound _) (pow_le_pow_left₀ (norm_nonneg _) hdist (m + 1))
          (by positivity) hC0)
    exact (mul_le_mul (mul_le_mul (hφ_bound p.1) hs1 (norm_nonneg _) hM0) hfc
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [indicator_of_notMem (s := tsupport φ ×ˢ (univ : Set ℝ)) fun h ↦ hp1 h.1,
      image_eq_zero_of_notMem_tsupport hp1, zero_mul, zero_mul, norm_zero]

/-- For a fixed slice `s > 0`, the homothety `y ↦ x + s • (y - x)` equates both the `L¹` lower
integrals and the Bochner integrals of the `(y, s)` segment integrand and the `(z, s)` spatial ray
integrand. -/
private theorem ray_slice_homothety_eq (φ : E → ℝ) {m : ℕ} (G : E → IteratedGradient E m)
    (x : E) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z, ‖φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - z) (G z)‖ₑ ∂μ =
      ∫⁻ y, ‖φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))‖ₑ ∂μ) ∧
    (∫ y, φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x))) ∂μ =
      ∫ z, φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - z) (G z) ∂μ) := by
  set n := finrank ℝ E
  let h : E → ℝ := fun y ↦
    φ y * s ^ m * IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))
  let ht : E → ℝ := fun z ↦
    φ (x + s⁻¹ • (z - x)) * s ^ (-(n : ℝ) - 1) * IteratedGradient.fullContractL m (x - z) (G z)
  have hpos : 0 < (s ^ n)⁻¹ := inv_pos.2 (pow_pos hs n)
  have hcomp : ∀ y, ht (AffineMap.homothety x s y) = (s ^ n)⁻¹ * h y :=
    fun y ↦ ray_integrand_comp_homothety φ G x y hs
  refine ⟨?_, ?_⟩
  · have hhom := Measure.lintegral_comp_homothety μ (fun z ↦ ‖ht z‖ₑ) x hs.ne'
    have hpt : ∀ y, ‖ht (AffineMap.homothety x s y)‖ₑ = ENNReal.ofReal |(s ^ n)⁻¹| * ‖h y‖ₑ :=
      fun y ↦ by rw [hcomp y, eNorm_mul, abs_of_pos hpos, Real.eNorm_eq_ofReal hpos.le]
    simp_rw [hpt] at hhom
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hhom
    exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (abs_pos.2 hpos.ne')).ne'
      ENNReal.ofReal_ne_top).1 hhom.symm
  · apply mul_left_cancel₀ hpos.ne'
    have hboch : ∫ y, ht (x + s • (y - x)) ∂μ = (s ^ n)⁻¹ * ∫ z, ht z ∂μ := by
      rw [integral_sub_right_eq_self (fun w ↦ ht (x + s • w)) x,
        Measure.integral_comp_smul (μ := μ) (fun w ↦ ht (x + w)) s,
        integral_add_left_eq_self ht x, smul_eq_mul, abs_of_pos hpos]
    rw [← integral_const_mul, ← hboch]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have hhom : x + s • (y - x) = AffineMap.homothety x s y := by
      simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    exact ((congrArg ht hhom).trans (hcomp y)).symm

/-- Core Fubini-homothety identity for a strongly measurable, bounded derivative field `G`. -/
private theorem integral_segment_eq_integral_taylorRemainderKernel {φ : E → ℝ}
    (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {m : ℕ} {G : E → IteratedGradient E m} (hG_meas : StronglyMeasurable G)
    {C : ℝ} (hG_bound : ∀ z, ‖G z‖ ≤ C) (x : E) :
    Integrable (fun z ↦ taylorRemainderKernel φ m x z (G z)) μ ∧
      (m.factorial : ℝ)⁻¹ * ∫ y, φ y * (∫ s in Ioo (0 : ℝ) 1,
          s ^ m * IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) ∂μ =
        ∫ z, taylorRemainderKernel φ m x z (G z) ∂μ := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  let H : E × ℝ → ℝ := fun p ↦
    φ p.1 * p.2 ^ m * IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x)))
  let Ht : E × ℝ → ℝ := fun p ↦
    φ (x + p.2⁻¹ • (p.1 - x)) * p.2 ^ (-(finrank ℝ E : ℝ) - 1) *
      IteratedGradient.fullContractL m (x - p.1) (G p.1)
  have hH_int : Integrable H (μ.prod ν) :=
    integrable_segment_prod hφ_meas hcpt hφ_bound hG_meas hG_bound x
  have hHt_meas : StronglyMeasurable Ht := by
    refine (((hφ_meas.comp (measurable_const.add (measurable_snd.inv.smul
        (measurable_fst.sub measurable_const)))).mul
        (measurable_snd.pow_const _)).stronglyMeasurable).mul ?_
    exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((((IteratedGradient.continuous_fullContractL m).comp
        (continuous_const.sub continuous_fst)).stronglyMeasurable).prodMk
        (hG_meas.comp_measurable measurable_fst))
  have hHt_int : Integrable Ht (μ.prod ν) := by
    refine ⟨hHt_meas.aestronglyMeasurable, ?_⟩
    have hlint_ae : (fun s ↦ ∫⁻ z, ‖Ht (z, s)‖ₑ ∂μ) =ᵐ[ν] fun s ↦ ∫⁻ y, ‖H (y, s)‖ₑ ∂μ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (ray_slice_homothety_eq (μ := μ) φ G x hs.1).1
    rw [hasFiniteIntegral_def, lintegral_prod_symm _ hHt_meas.eNorm.aemeasurable,
      lintegral_congr_ae hlint_ae, ← lintegral_prod_symm _ hH_int.aestronglyMeasurable.eNorm]
    exact hH_int.hasFiniteIntegral
  have hz_eq : ∀ z, (m.factorial : ℝ)⁻¹ * ∫ s, Ht (z, s) ∂ν = taylorRemainderKernel φ m x z (G z) :=
    fun z ↦ by
      dsimp only [Ht, ν]
      rw [integral_mul_const, taylorRemainderKernel_apply, taylorRemainderWeight, mul_assoc]
  refine ⟨by
    simpa only [← hz_eq] using hHt_int.integral_prod_left.const_mul (m.factorial : ℝ)⁻¹, ?_⟩
  have hy_in : (∫ y, φ y * (∫ s, s ^ m * IteratedGradient.fullContractL m (x - y)
      (G (x + s • (y - x))) ∂ν) ∂μ) = ∫ y, (∫ s, H (y, s) ∂ν) ∂μ := by
    congr 1 with y; simp only [H, mul_assoc, integral_const_mul]
  rw [hy_in, integral_integral_swap hH_int,
    setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ (ray_slice_homothety_eq φ G x hs.1).2,
    ← integral_integral_swap hHt_int, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall hz_eq)

/-- Compact-cone localization of `integral_segment_eq_integral_taylorRemainderKernel` to a
`C^{m+1}` function on an open set `Ω` star-convex with respect to `tsupport φ`. -/
private theorem integral_segment_iteratedGradientChain_eq_setIntegral {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) {M : ℝ}
    (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω)
    {x : E} (hx : x ∈ Ω) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) Ω μ ∧
      (m.factorial : ℝ)⁻¹ * ∫ y, φ y * (∫ s in Ioo (0 : ℝ) 1,
          s ^ m * IteratedGradient.fullContractL m (x - y)
            (iteratedGradientChain u m (x + s • (y - x)))) ∂μ =
        ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  let L : Set E := (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ)
  have hL_cpt : IsCompact L := (isCompact_Icc.prod hcpt).image (by fun_prop)
  have hL_sub : L ⊆ Ω := fun _ ⟨⟨s, y⟩, ⟨hs, hy⟩, h⟩ ↦ h ▸ by
    have hcomb : s • y + (1 - s) • x = x + s • (y - x) := by module
    simpa only [hcomb] using hstar y hy hx hs.1 (sub_nonneg.2 hs.2) (add_sub_cancel s 1)
  let G : E → IteratedGradient E m := L.indicator (iteratedGradientChain u m)
  have hG_cont : ContinuousOn (iteratedGradientChain u m) L := fun z hz ↦
    (contDiffAt_iteratedGradientChain (m := (0 : ℕ∞ω))
      (hu.contDiffAt (hΩ.mem_nhds (hL_sub hz))) m (by simp)).continuousAt.continuousWithinAt
  have hG_meas : StronglyMeasurable G := by
    have h1 : L.domRestrict G = L.domRestrict (iteratedGradientChain u m) :=
      funext fun ⟨y, hy⟩ ↦ indicator_of_mem hy _
    have h0 : Lᶜ.domRestrict G = fun _ ↦ 0 :=
      funext fun ⟨y, hy⟩ ↦ indicator_of_notMem hy _
    refine stronglyMeasurable_of_restrict_of_restrict_compl hL_cpt.isClosed.measurableSet ?_ ?_
    · rw [h1]; exact hG_cont.domRestrict.stronglyMeasurable
    · rw [h0]; exact stronglyMeasurable_const
  obtain ⟨C₀, hC₀⟩ := hL_cpt.exists_bound_of_continuousOn hG_cont
  have hG_bound : ∀ z, ‖G z‖ ≤ max C₀ 0 := fun z ↦ by
    by_cases hz : z ∈ L
    · simp only [G, indicator_of_mem hz]; exact (hC₀ z hz).trans (le_max_left C₀ 0)
    · simp only [G, indicator_of_notMem hz, norm_zero]; exact le_max_right C₀ 0
  obtain ⟨hKG_int, hcore⟩ := integral_segment_eq_integral_taylorRemainderKernel (μ := μ)
    hφ_meas hcpt hφ_bound hG_meas hG_bound x
  have hK_eq : (fun z ↦ taylorRemainderKernel φ m x z (G z)) =
      Ω.indicator (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) := by
    ext z; by_cases hz : z ∈ L
    · simp only [G, indicator_of_mem hz, indicator_of_mem (hL_sub hz)]
    · have hK0 : taylorRemainderKernel φ m x z = 0 := image_eq_zero_of_notMem_tsupport
        fun hts ↦ hz (tsupport_taylorRemainderKernel_subset_image hcpt m x hts)
      by_cases hzΩ : z ∈ Ω
      · simp only [hK0, zero_apply, indicator_of_mem hzΩ]
      · simp only [hK0, zero_apply, indicator_of_notMem hzΩ]
  refine ⟨by rwa [← integrable_indicator_iff hΩ.measurableSet, ← hK_eq], ?_⟩
  rw [← integral_indicator hΩ.measurableSet, ← hK_eq, ← hcore]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  by_cases hy : y ∈ tsupport φ
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    dsimp only [G]
    rw [indicator_of_mem (s := L) ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Pointwise representation formula for `C^{m+1}` functions on star-shaped open sets.** Let `Ω`
be an open set, `φ` a bounded measurable function with compact support in `Ω` and `∫ φ ∂μ = 1`,
and `u` a `C^{m+1}` function on `Ω`. If `x ∈ Ω` and `Ω` is star-convex with respect to every point
of `tsupport φ`, then `z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)` is
integrable on `Ω` and
`u x - ∫ y, φ y * T^m_y u(x) ∂μ = ∫ z in Ω, taylorRemainderKernel φ m x z (D^{m+1} u z) ∂μ`.
No boundedness of `Ω` or global integrability of `D^{m+1} u` is required. -/
theorem sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel {Ω : Set E}
    (hΩ : IsOpen Ω) {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ Ω) (hφ_int : ∫ y, φ y ∂μ = 1) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω) {x : E} (hx : x ∈ Ω)
    (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) Ω μ ∧
      u x - ∫ y, φ y * (∑ j ∈ Finset.range (m + 1),
          (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) ∂μ =
        ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  obtain ⟨hint_K, hseg_eq⟩ := integral_segment_iteratedGradientChain_eq_setIntegral (μ := μ)
    hΩ hφ_meas hcpt hφ_bound hu hx hstar
  refine ⟨hint_K, ?_⟩
  have hint_mul : ∀ ψ : E → ℝ, ContinuousOn ψ Ω → Integrable (fun y ↦ φ y * ψ y) μ := fun ψ hψ ↦
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left φ ψ).trans (subset_tsupport φ))).1
      (((hψ.mono hφ_supp).integrableOn_compact hcpt).bdd_mul
        hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))
  have hux : u x = ∫ y, φ y * u x ∂μ := by rw [integral_mul_const, hφ_int, one_mul]
  have hsum_cont : ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) Ω := by
    simpa only [smul_eq_mul] using continuousOn_sum_iteratedFDeriv hΩ (hu.of_le (by simp)) x
  rw [← hseg_eq, hux, ← integral_sub (hint_mul _ continuousOn_const) (hint_mul _ hsum_cont),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  by_cases hy : y ∈ tsupport φ
  · have hseg_Ω : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ Ω := fun s hs ↦ by
      have hcomb : s • y + (1 - s) • x = x + s • (y - x) := by module
      simpa only [hcomb] using hstar y hy hx hs.1 (sub_nonneg.2 hs.2) (add_sub_cancel s 1)
    rw [← mul_sub, sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL u m x y
      fun s hs ↦ hu.contDiffAt (hΩ.mem_nhds (hseg_Ω s hs))]
    ring
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- Set-integral variant of `sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel`,
writing the averaged Taylor integral over `Ω` rather than the ambient space. -/
theorem sub_setIntegral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel {Ω : Set E}
    (hΩ : IsOpen Ω) {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ Ω) (hφ_int : ∫ y, φ y ∂μ = 1) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω) {x : E} (hx : x ∈ Ω)
    (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    u x - ∫ y in Ω, φ y * (∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) ∂μ =
      ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  have hsupp : Function.support (fun y ↦ φ y * (∑ j ∈ Finset.range (m + 1),
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y))) ⊆ Ω :=
    (Function.support_mul_subset_left _ _).trans ((subset_tsupport φ).trans hφ_supp)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
    Function.notMem_support.1 fun h ↦ hy (hsupp h)]
  exact (sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel hΩ hφ_meas hcpt
    hφ_supp hφ_int hφ_bound hu hx hstar).2

end SmoothRepresentation

/-! ### Bounded-domain `L¹(Ω) → L¹(Ω)` potential estimate -/

section PotentialL1

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Integrating `x ↦ ‖taylorRemainderKernel φ m x z‖ₑ` over a bounded set `Ω` for `z ∈ closure Ω`
is bounded by `M * μ(B(0, 1)) / (m + 1)! * (diam Ω) ^ (n + m + 1)`, with no measurability
hypothesis on `Ω` or `φ`. -/
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

/-- Joint product integrability and `L¹` bound for `(x, z) ↦ taylorRemainderKernel φ m x z (G z)`
on `(μ.restrict Ω).prod (μ.restrict Ω)` when `Ω` is bounded and `G` is integrable on `Ω`. -/
private theorem integrable_taylorRemainderKernel_prod {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    Integrable (fun p : E × E ↦ taylorRemainderKernel φ m p.1 p.2 (G p.2))
      ((μ.restrict Ω).prod (μ.restrict Ω)) ∧
    ∫⁻ p, ‖taylorRemainderKernel φ m p.1 p.2 (G p.2)‖ₑ ∂((μ.restrict Ω).prod (μ.restrict Ω)) ≤
      ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial *
        diam Ω ^ (finrank ℝ E + m + 1)) * eLpNorm G 1 (μ.restrict Ω) := by
  let ν : Measure E := μ.restrict Ω
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  let F : E × E → ℝ := fun p ↦ taylorRemainderKernel φ m p.1 p.2 (G p.2)
  let C : ℝ := M * μ.real (ball (0 : E) 1) / (m + 1).factorial * diam Ω ^ (finrank ℝ E + m + 1)
  have hF_meas : AEStronglyMeasurable F (ν.prod ν) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((stronglyMeasurable_taylorRemainderKernel hφ_meas m).aestronglyMeasurable.prodMk
        hG.aestronglyMeasurable.comp_snd)
  have hae_cl : ∀ᵐ z ∂ν, z ∈ closure Ω := by
    have hemp : (closure Ω)ᶜ ∩ Ω = ∅ :=
      Set.ext fun x ↦ iff_false_intro fun ⟨h1, h2⟩ ↦ h1 (subset_closure h2)
    rw [ae_iff, ← compl_def, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      hemp, measure_empty]
  have hbound : ∫⁻ p, ‖F p‖ₑ ∂ν.prod ν ≤ ENNReal.ofReal C * eLpNorm G 1 ν := by
    calc
      ∫⁻ p, ‖F p‖ₑ ∂ν.prod ν
        = ∫⁻ z, ∫⁻ x, ‖F (x, z)‖ₑ ∂ν ∂ν := lintegral_prod_symm _ hF_meas.eNorm
      _ ≤ ∫⁻ z, ∫⁻ x, ‖taylorRemainderKernel φ m x z‖ₑ * ‖G z‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun z ↦ lintegral_mono fun x ↦ ?_
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
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
  refine ⟨⟨hF_meas, ?_⟩, hbound⟩
  rw [hasFiniteIntegral_def]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (memLp_one_iff_integrable.2 hG).eLpNorm_lt_top)

/-- On a bounded set `Ω`, if `G` is integrable on `Ω`, then for almost every `x ∈ Ω` the slice
`z ↦ taylorRemainderKernel φ m x z (G z)` is integrable on `Ω`. -/
theorem ae_integrableOn_taylorRemainderKernel_apply {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    ∀ᵐ x ∂μ.restrict Ω, IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (G z)) Ω μ := by
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  exact (integrable_taylorRemainderKernel_prod hb hφ_meas hsupp hM hG).1.prod_right_ae

/-- On a bounded set `Ω`, the integral operator `x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z)`
maps `L¹(Ω; IteratedGradient E m)` into `L¹(Ω)`. -/
theorem integrableOn_setIntegral_taylorRemainderKernel_apply {Ω : Set E}
    (hb : Bornology.IsBounded Ω) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hsupp : Function.support φ ⊆ closure Ω) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    {G : E → IteratedGradient E m} (hG : IntegrableOn G Ω μ) :
    IntegrableOn (fun x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z) ∂μ) Ω μ :=
  (integrable_taylorRemainderKernel_prod hb hφ_meas hsupp hM hG).1.integral_prod_left

/-- **`L¹(Ω) → L¹(Ω)` norm bound for the Taylor-remainder integral operator** on a bounded set
`Ω`, stated in terms of `eLpNorm · 1 (μ.restrict Ω)`. -/
theorem eLpNorm_one_setIntegral_taylorRemainderKernel_le {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hsupp : Function.support φ ⊆ closure Ω)
    {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) {m : ℕ} {G : E → IteratedGradient E m}
    (hG : IntegrableOn G Ω μ) :
    eLpNorm (fun x ↦ ∫ z in Ω, taylorRemainderKernel φ m x z (G z) ∂μ) 1 (μ.restrict Ω) ≤
      ENNReal.ofReal (M * μ.real (ball (0 : E) 1) / (m + 1).factorial *
        diam Ω ^ (finrank ℝ E + m + 1)) * eLpNorm G 1 (μ.restrict Ω) := by
  let ν : Measure E := μ.restrict Ω
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨hF_int, hbound⟩ := integrable_taylorRemainderKernel_prod hb hφ_meas hsupp hM hG
  rw [eLpNorm_one_eq_lintegral_eNorm hF_int.integral_prod_left.aestronglyMeasurable]
  calc
    ∫⁻ x, ‖∫ z, taylorRemainderKernel φ m x z (G z) ∂ν‖ₑ ∂ν
      ≤ ∫⁻ x, ∫⁻ z, ‖taylorRemainderKernel φ m x z (G z)‖ₑ ∂ν ∂ν :=
        lintegral_mono fun _ ↦ eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ p : E × E, ‖taylorRemainderKernel φ m p.1 p.2 (G p.2)‖ₑ ∂ν.prod ν :=
        (lintegral_prod _ hF_int.aestronglyMeasurable.eNorm).symm
    _ ≤ _ := hbound

end PotentialL1

/-! ### The Sobolev representation formula -/

section SobolevRepresentation

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The derivative-form averaged Taylor polynomial of order `m` of a Sobolev function
`u ∈ W^{m,p}(Ω)` with respect to a weight `φ : E → ℝ`, evaluated at `x : E`:
`∑_{j ≤ m} (j!)⁻¹ ∫_{y ∈ Ω} φ y * ⟨D^j u(y), (x - y)^{⊗ j}⟩ dμ`. -/
def averagedTaylorEval (φ : E → ℝ) : (m : ℕ) → Wkp mu Omega p m → E → ℝ
  | 0, u, _ => ∫ y in Omega, φ y * u y ∂mu
  | m + 1, u, x =>
    averagedTaylorEval φ m (lowerOrder m u) x +
      ((m + 1).factorial : ℝ)⁻¹ *
        ∫ y in Omega, φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu

@[simp]
theorem averagedTaylorEval_zero (φ : E → ℝ) (u : Wkp mu Omega p 0) (x : E) :
    averagedTaylorEval φ 0 u x = ∫ y in Omega, φ y * u y ∂mu :=
  (rfl)

@[simp]
theorem averagedTaylorEval_succ (φ : E → ℝ) (m : ℕ) (u : Wkp mu Omega p (m + 1)) (x : E) :
    averagedTaylorEval φ (m + 1) u x =
      averagedTaylorEval φ m (lowerOrder m u) x +
        ((m + 1).factorial : ℝ)⁻¹ *
          ∫ y in Omega,
            φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu :=
  (rfl)

@[simp]
theorem averagedTaylorEval_zero_weight (m : ℕ) (u : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval (0 : E → ℝ) m u x = 0 := by
  induction m with
  | zero => simp [averagedTaylorEval]
  | succ m ih => simp [averagedTaylorEval_succ, ih]

/-- Scalar multiplication commutes with `averagedTaylorEval` for every `1 ≤ p ≤ ∞`. -/
theorem averagedTaylorEval_smul (φ : E → ℝ) (m : ℕ) (c : ℝ) (u : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval φ m (c • u) x = c * averagedTaylorEval φ m u x := by
  induction m with
  | zero =>
    rw [averagedTaylorEval_zero, averagedTaylorEval_zero, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c u] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  | succ m ih =>
    have htop : (∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m (c • u) y) ∂mu) =
        c * ∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu := by
      rw [← iteratedGradientL_apply m (c • u), map_smul, iteratedGradientL_apply m u,
        ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (iteratedGradient m u)] with y hy
      rw [hy, Pi.smul_apply, map_smul, smul_eq_mul, mul_left_comm]
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, ← lowerOrderL_apply m (c • u), map_smul,
      lowerOrderL_apply m u, ih, htop]
    ring

@[simp]
theorem averagedTaylorEval_zero_right (φ : E → ℝ) (m : ℕ) (x : E) :
    averagedTaylorEval φ m (0 : Wkp mu Omega p m) x = 0 := by
  simpa using averagedTaylorEval_smul φ m 0 (0 : Wkp mu Omega p m) x

/-- Compact support and boundedness of `φ` ensure integrability of `φ y * ⟨g y, (x - y)^{⊗ m+1}⟩`
on `Ω` for any `g ∈ Lᵖ(Ω; IteratedGradient E m)` (`1 ≤ p ≤ ∞`). -/
private theorem integrableOn_mul_fullContractL_Lp {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    (g : Lp (IteratedGradient E m) p (mu.restrict Omega)) (x : E) :
    IntegrableOn
      (fun y ↦ φ y * IteratedGradient.fullContractL m (x - y) (g y)) Omega mu := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure (ν.restrict (tsupport φ)) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  obtain ⟨R₀, hR₀⟩ := hcpt.isBounded.subset_closedBall x
  set R := max R₀ 0
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  have hg_int : Integrable g (ν.restrict (tsupport φ)) :=
    ((Lp.memLp g).restrict (tsupport φ)).integrable Fact.out
  have hmeas : AEStronglyMeasurable
      (fun y ↦ φ y * IteratedGradient.fullContractL m (x - y) (g y)) (ν.restrict (tsupport φ)) :=
    (hφ_meas.aestronglyMeasurable.mul
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((((IteratedGradient.continuous_fullContractL m).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable).prodMk
          (Lp.aestronglyMeasurable g)))).restrict
  refine (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left φ _).trans (subset_tsupport φ))).1 ?_
  refine (hg_int.norm.const_mul (max M 0 * R ^ (m + 1))).mono' hmeas
    (ae_restrict_of_forall_mem hcpt.isClosed.measurableSet fun y hy ↦ ?_)
  have hdist : ‖x - y‖ ≤ R := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact (mem_closedBall.1 (hR₀ hy)).trans (le_max_left R₀ 0)
  rw [norm_mul]
  exact (mul_le_mul ((hφ_bound y).trans (le_max_left M 0))
    ((IteratedGradient.norm_fullContractL_apply_le m _ _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist (m + 1))
        (norm_nonneg _))) (norm_nonneg _) hM0).trans_eq (by ring)

/-- Addition commutes with `averagedTaylorEval` for every `1 ≤ p ≤ ∞` whenever `φ` is measurable,
bounded, and compactly supported. -/
theorem averagedTaylorEval_add {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (u v : Wkp mu Omega p m) (x : E) :
    averagedTaylorEval φ m (u + v) x =
      averagedTaylorEval φ m u x + averagedTaylorEval φ m v x := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure (ν.restrict (tsupport φ)) := isFiniteMeasure_restrict.2
    ((Measure.restrict_apply_le _ _).trans_lt hcpt.measure_lt_top).ne
  induction m with
  | zero =>
    have hint : ∀ w : Wkp mu Omega p 0, Integrable (fun y ↦ φ y * w y) ν := fun w ↦
      (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_left φ w).trans (subset_tsupport φ))).1
        ((((Lp.memLp w).restrict (tsupport φ)).integrable Fact.out).bdd_mul
          hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))
    rw [averagedTaylorEval_zero, averagedTaylorEval_zero, averagedTaylorEval_zero,
      ← integral_add (hint u) (hint v)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u v] with y hy
    rw [hy, Pi.add_apply, mul_add]
  | succ m ih =>
    have htop : (∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m (u + v) y) ∂mu) =
        (∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu) +
        ∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m v y) ∂mu := by
      rw [← iteratedGradientL_apply m (u + v), map_add, iteratedGradientL_apply m u,
        iteratedGradientL_apply m v, ← integral_add
          (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m u) x)
          (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m v) x)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (iteratedGradient m u) (iteratedGradient m v)] with y hy
      rw [hy, Pi.add_apply, map_add, mul_add]
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, averagedTaylorEval_succ,
      ← lowerOrderL_apply m (u + v), map_add, lowerOrderL_apply m u, lowerOrderL_apply m v,
      ih (lowerOrder m u) (lowerOrder m v), htop]
    ring

/-- Lowering the Sobolev integrability exponent does not change `averagedTaylorEval`. -/
theorem averagedTaylorEval_ofExponentLEL [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) (φ : E → ℝ) (m : ℕ) (u : Wkp mu Omega q m) (x : E) :
    averagedTaylorEval φ m (ofExponentLEL hpq m u) x = averagedTaylorEval φ m u x := by
  induction m with
  | zero =>
    refine integral_congr_ae ?_
    filter_upwards [value_ofExponentLEL_ae hpq 0 u] with y hy
    simp only [value_zero] at hy
    rw [hy]
  | succ m ih =>
    rw [averagedTaylorEval_succ, averagedTaylorEval_succ, lowerOrder_ofExponentLEL, ih]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [iteratedGradient_ofExponentLEL_ae hpq m u] with y hy
    rw [hy]

/-- On a `C^m` representative `f` of `u ∈ W^{m,p}(Ω)`, `averagedTaylorEval φ m u x` agrees with the
classical averaged Taylor integral `∫_{y ∈ Ω} φ y * T^m_y f(x) dμ`. -/
theorem averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) {M : ℝ}
    (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (u : Wkp mu Omega p m) {f : E → ℝ}
    (hf : ContDiffOn ℝ m f Omega) (hu : (value m u : E → ℝ) =ᵐ[mu.restrict Omega] f) (x : E) :
    averagedTaylorEval φ m u x =
      ∫ y in Omega, φ y * (∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) ∂mu := by
  have hint_on : ∀ ψ : E → ℝ, ContinuousOn ψ Omega → IntegrableOn (fun y ↦ φ y * ψ y) Omega mu :=
    fun ψ hψ ↦ ((integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left φ ψ).trans (subset_tsupport φ))).1
        (((hψ.mono hφ_supp).integrableOn_compact hcpt).bdd_mul
          hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))).integrableOn
  induction m with
  | zero =>
    refine integral_congr_ae ?_
    filter_upwards [hu] with y hy
    simp only [value_zero] at hy
    simp [hy]
  | succ m ih =>
    have hlow : (value m (lowerOrder m u) : E → ℝ) =ᵐ[mu.restrict Omega] f := by
      simpa only [value_succ] using hu
    have hf_m : ContDiffOn ℝ m f Omega := hf.of_le (by simp)
    rw [averagedTaylorEval_succ, ih (lowerOrder m u) hf_m hlow]
    have hgrad_ae := iteratedGradient_ae_eq_of_contDiffOn m u hf hu
    have htop_eq : ((m + 1).factorial : ℝ)⁻¹ *
        (∫ y in Omega,
          φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu) =
        ∫ y in Omega, φ y * (((m + 1).factorial : ℝ)⁻¹ *
          iteratedFDeriv ℝ (m + 1) f y (fun _ ↦ x - y)) ∂mu := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hgrad_ae] with y hy
      rw [hy, fullContractL_iteratedGradientChain]
      ring
    have hsum_cont : ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Omega := by
      simpa only [smul_eq_mul] using continuousOn_sum_iteratedFDeriv Omega.isOpen hf_m x
    have htop_cont : ContinuousOn (fun y ↦ ((m + 1).factorial : ℝ)⁻¹ *
        iteratedFDeriv ℝ (m + 1) f y (fun _ ↦ x - y)) Omega :=
      continuousOn_const.mul (continuous_eval.comp_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv (k := m + 1) hf Omega.isOpen (by simp)).prodMk
          (continuous_pi fun _ ↦ continuous_const.sub continuous_id).continuousOn))
    rw [htop_eq, ← integral_add (hint_on _ hsum_cont) (hint_on _ htop_cont)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [Finset.sum_range_succ _ (m + 1), mul_add]

/-- Operator-norm bound on `W^{m,1}(Ω)` for `u ↦ averagedTaylorEval φ m u x` when `φ` is measurable,
bounded, and compactly supported. -/
private theorem exists_norm_averagedTaylorEval_one_le {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    ∃ C : ℝ, ∀ u : Wkp mu Omega 1 m, ‖averagedTaylorEval φ m u x‖ ≤ C * ‖u‖ := by
  let ν : Measure E := mu.restrict Omega
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  induction m with
  | zero =>
    refine ⟨max M 0, fun u ↦ (norm_integral_le_integral_norm _).trans ?_⟩
    have hint : Integrable (fun y ↦ φ y * u y) ν := (L1.integrable_coeFn u).bdd_mul
      hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound)
    refine (integral_mono hint.norm ((L1.integrable_coeFn u).norm.const_mul (max M 0))
      fun y ↦ ?_).trans_eq (by rw [integral_const_mul, L1.norm_eq_integral_norm])
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hφ_bound y).trans (le_max_left M 0)) (norm_nonneg _)
  | succ m ih =>
    obtain ⟨C₀, hC₀⟩ := ih
    obtain ⟨R₀, hR₀⟩ := hcpt.isBounded.subset_closedBall x
    set A := max C₀ 0
    set R := max R₀ 0
    set B := max M 0 * R ^ (m + 1)
    let L_low := lowerOrderL (mu := mu) (Omega := Omega) (p := 1) m
    let L_grad := iteratedGradientL (mu := mu) (Omega := Omega) (p := 1) m
    refine ⟨A * ‖L_low‖ + ((m + 1).factorial : ℝ)⁻¹ * (B * ‖L_grad‖), fun u ↦ ?_⟩
    have hlow_le : ‖averagedTaylorEval φ m (lowerOrder m u) x‖ ≤ A * (‖L_low‖ * ‖u‖) :=
      (hC₀ _).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _)).trans <| by
        rw [← lowerOrderL_apply]
        exact mul_le_mul_of_nonneg_left (L_low.le_opNorm u) (le_max_right C₀ 0)
    have htop_le : ‖∫ y in Omega,
        φ y * IteratedGradient.fullContractL m (x - y) (iteratedGradient m u y) ∂mu‖ ≤
        B * (‖L_grad‖ * ‖u‖) := by
      refine (norm_integral_le_integral_norm _).trans <| (integral_mono
        (integrableOn_mul_fullContractL_Lp hφ_meas hcpt hφ_bound (iteratedGradient m u) x).norm
        ((L1.integrable_coeFn (iteratedGradient m u)).norm.const_mul B) fun y ↦ ?_).trans
        (by rw [integral_const_mul, ← L1.norm_eq_integral_norm, ← iteratedGradientL_apply]
            exact mul_le_mul_of_nonneg_left (L_grad.le_opNorm u) (by positivity))
      by_cases hy : y ∈ tsupport φ
      · have hdist : ‖x - y‖ ≤ R := by
          rw [norm_sub_rev, ← dist_eq_norm]
          exact (mem_closedBall.1 (hR₀ hy)).trans (le_max_left R₀ 0)
        rw [norm_mul]
        exact (mul_le_mul ((hφ_bound y).trans (le_max_left M 0))
          ((IteratedGradient.norm_fullContractL_apply_le m _ _).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist (m + 1))
              (norm_nonneg _))) (norm_nonneg _) hM0).trans_eq (by ring)
      · simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul, norm_zero]; positivity
    rw [averagedTaylorEval_succ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    exact (add_le_add hlow_le
      (mul_le_mul_of_nonneg_left htop_le (by positivity))).trans_eq (by ring)

/-- For a bounded measurable cutoff `φ` with compact support, `u ↦ averagedTaylorEval φ m u x` is
continuous on `W^{m,1}(Ω)`. -/
theorem continuous_averagedTaylorEval_one {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (m : ℕ) (x : E) :
    Continuous fun u : Wkp mu Omega 1 m ↦ averagedTaylorEval φ m u x := by
  obtain ⟨C, hC⟩ := exists_norm_averagedTaylorEval_one_le (mu := mu) (Omega := Omega)
    hφ_meas hcpt hφ_bound m x
  exact (LinearMap.mkContinuous
    ({ toFun := fun u ↦ averagedTaylorEval φ m u x
       map_add' := fun u v ↦ averagedTaylorEval_add hφ_meas hcpt hφ_bound m u v x
       map_smul' := fun c u ↦ averagedTaylorEval_smul φ m c u x } :
      Wkp mu Omega 1 m →ₗ[ℝ] ℝ) C hC).continuous

/-- Convergence in `L¹(Ω)` of a derivative sequence implies convergence in measure on `Ω` of its
Taylor-remainder kernel integral. -/
private theorem tendstoInMeasure_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hsupp_cl : Function.support φ ⊆ closure (Omega : Set E)) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {m : ℕ} {g : ℕ → Lp (IteratedGradient E m) 1 (mu.restrict Omega)}
    {g₀ : Lp (IteratedGradient E m) 1 (mu.restrict Omega)} (hg : Tendsto g atTop (𝓝 g₀)) :
    TendstoInMeasure (mu.restrict Omega)
      (fun j x ↦ ∫ z in Omega, taylorRemainderKernel φ m x z (g j z) ∂mu) atTop
      (fun x ↦ ∫ z in Omega, taylorRemainderKernel φ m x z (g₀ z) ∂mu) := by
  let ν : Measure E := mu.restrict Omega
  let T : (E → IteratedGradient E m) → E → ℝ := fun G x ↦
    ∫ z in Omega, taylorRemainderKernel φ m x z (G z) ∂mu
  let C : ℝ := M * mu.real (ball (0 : E) 1) / (m + 1).factorial *
    diam (Omega : Set E) ^ (finrank ℝ E + m + 1)
  have hzero_lim : Tendsto (fun j ↦ ENNReal.ofReal C * ENNReal.ofReal ‖g j - g₀‖) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      (ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hg))
      (Or.inr ENNReal.ofReal_ne_top)
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero <|
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero_lim (fun _ ↦ zero_le)
      fun j ↦ ?_
  have hsub_ae : T (g j) - T g₀ =ᵐ[ν] T ↑(g j - g₀) := by
    filter_upwards [ae_integrableOn_taylorRemainderKernel_apply hb hφ_meas hsupp_cl hφ_bound
      (L1.integrable_coeFn (g j)),
      ae_integrableOn_taylorRemainderKernel_apply hb hφ_meas hsupp_cl hφ_bound
      (L1.integrable_coeFn g₀)] with x hxj hx0
    dsimp only [Pi.sub_apply, T]
    rw [← integral_sub hxj hx0]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (g j) g₀] with z hz
    rw [hz, Pi.sub_apply, map_sub]
  rw [eLpNorm_congr_ae hsub_ae]
  exact (eLpNorm_one_setIntegral_taylorRemainderKernel_le hb hφ_meas hsupp_cl hφ_bound
    (L1.integrable_coeFn (g j - g₀))).trans_eq (by
      rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (g j - g₀)),
        ← L1.ofReal_norm_eq_lintegral])

/-- Private `p = 1` core for the Sobolev representation formula via Meyers–Serrin density and the
`L¹(Ω) → L¹(Ω)` potential bound. -/
private theorem ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel_one
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (m : ℕ) (u : Wkp mu Omega 1 (m + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂mu := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hsupp_cl : Function.support φ ⊆ closure (Omega : Set E) :=
    (subset_tsupport φ).trans (hφ_supp.trans subset_closure)
  obtain ⟨v, f, hf, hae_v, hv⟩ := exists_contDiffOn_approximation ENNReal.one_ne_top (m + 1) u
  have hrep_j : ∀ j, ∀ᵐ x ∂ν, value (m + 1) (v j) x -
      averagedTaylorEval φ m (lowerOrder m (v j)) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m (v j) z) ∂mu := fun j ↦ by
    have hf_m1 : ContDiffOn ℝ (m + 1) (f j) Omega := (hf j).of_le (by simp)
    have hgrad_j := iteratedGradient_ae_eq_of_contDiffOn m (v j) hf_m1 (hae_v j)
    filter_upwards [hae_v j, ae_restrict_mem Omega.isOpen.measurableSet] with x hxv hxΩ
    have hlow_j : (value m (lowerOrder m (v j)) : E → ℝ) =ᵐ[ν] f j := by
      simpa only [value_succ] using hae_v j
    rw [hxv, averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv hφ_meas hcpt hφ_supp hφ_bound m
      (lowerOrder m (v j)) ((hf j).of_le (by simp)) hlow_j x,
      sub_setIntegral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel Omega.isOpen hφ_meas
        hcpt hφ_supp hφ_int hφ_bound hf_m1 hxΩ hstar]
    refine integral_congr_ae ?_
    filter_upwards [hgrad_j] with z hz
    rw [hz]
  have hv_val : Tendsto (fun j ↦ value (m + 1) (v j)) atTop (𝓝 (value (m + 1) u)) := by
    rw [← valueL_apply (m + 1) u]
    exact (((valueL (mu := mu) (Omega := Omega) (p := 1) (m + 1)).continuous.tendsto u).comp
      hv).congr fun j ↦ valueL_apply (m + 1) (v j)
  obtain ⟨ns₁, hns₁_mono, hae_val⟩ := (tendstoInMeasure_of_tendsto_Lp hv_val).exists_seq_tendsto_ae
  have hg : Tendsto (fun j ↦ iteratedGradient m (v j)) atTop (𝓝 (iteratedGradient m u)) := by
    rw [← iteratedGradientL_apply m u]
    exact (((iteratedGradientL (mu := mu) (Omega := Omega) (p := 1) m).continuous.tendsto u).comp
      hv).congr fun j ↦ iteratedGradientL_apply m (v j)
  obtain ⟨ns₂, hns₂_mono, hae_T⟩ :=
    ((tendstoInMeasure_setIntegral_taylorRemainderKernel hb hφ_meas hsupp_cl hφ_bound hg).comp
      hns₁_mono.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hae_val, hae_T, ae_all_iff.2 hrep_j] with x hx_val hx_T hx_rep
  have hlow_x : Continuous fun w : Wkp mu Omega 1 (m + 1) ↦
      averagedTaylorEval φ m (lowerOrder m w) x :=
    ((continuous_averagedTaylorEval_one hφ_meas hcpt hφ_bound m x).comp
      (lowerOrderL (mu := mu) (Omega := Omega) (p := 1) m).continuous).congr
      fun w ↦ by dsimp only [Function.comp_apply]; rw [lowerOrderL_apply]
  have hsub_tendsto := (hx_val.comp hns₂_mono.tendsto_atTop).sub
    ((hlow_x.tendsto u).comp (hv.comp (hns₁_mono.comp hns₂_mono).tendsto_atTop))
  exact tendsto_nhds_unique hsub_tendsto
    (hx_T.congr fun k ↦ (hx_rep (ns₁ (ns₂ k))).symm)

/-- **The Sobolev representation formula** (Brenner–Scott, Proposition 4.2.8). Let `Ω` be a bounded
open set, `φ` a bounded measurable cutoff with compact support in `Ω` and `∫ φ ∂μ = 1`, and assume
`Ω` is star-convex with respect to every point of `tsupport φ`. For every `1 ≤ p ≤ ∞`, every
`m : ℕ`, and every `u ∈ W^{m+1,p}(Ω)`, almost everywhere on `Ω`,
`value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
  ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂μ`. -/
theorem ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂mu := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  let u₁ : Wkp mu Omega 1 (m + 1) := ofExponentLEL hp1 (m + 1) u
  have hgrad_ae := iteratedGradient_ofExponentLEL_ae hp1 m u
  filter_upwards [value_ofExponentLEL_ae hp1 (m + 1) u,
    ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel_one hb hφ_meas hcpt hφ_supp
      hφ_int hφ_bound hstar m u₁] with x hval hrep
  rw [← hval, ← averagedTaylorEval_ofExponentLEL hp1 φ m (lowerOrder m u) x,
    ← lowerOrder_ofExponentLEL hp1 m u, hrep]
  refine integral_congr_ae ?_
  filter_upwards [hgrad_ae] with z hz
  rw [hz]

/-- First-order (`m = 0`) specialization of the Sobolev representation formula on `W^{1,p}(Ω)`. -/
theorem ae_sub_setIntegral_mul_eq_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (u : Wkp mu Omega p 1) :
    ∀ᵐ x ∂mu.restrict Omega,
      value 1 u x - (∫ y in Omega, φ y * value 1 u y ∂mu) =
        ∫ z in Omega, taylorRemainderKernel φ 0 x z (iteratedGradient 0 u z) ∂mu := by
  simpa only [averagedTaylorEval_zero, value_succ, value_zero] using
    ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel hb hφ_meas hcpt hφ_supp hφ_int
      hφ_bound hstar 0 u

end Wkp

end SobolevRepresentation

/-! ### Concrete checks -/

section Examples

/-- One-dimensional first-order sign check: on `Ω = (-1, 1)` with cutoff
`φ = 1_{[-1/2, 1/2]}`, `u = id`, `m = 0`, and `x = 1/2`, the kernel integral against `D¹(id)`
evaluates to `+1/2` (`id (1/2) - ∫_{-1/2}^{1/2} y dy = 1/2`). -/
example :
    let φ : ℝ → ℝ := (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun _ ↦ 1
    ∫ z in Ioo (-1 : ℝ) 1, taylorRemainderKernel φ 0 (1 / 2) z (iteratedGradientChain id 0 z) =
      1 / 2 := by
  intro φ
  have hφ_meas : Measurable φ := measurable_const.indicator measurableSet_Icc
  have hsub_supp : Function.support φ ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := fun y hy ↦
    by_contra fun hnot ↦ hy (indicator_of_notMem hnot _)
  have hcpt : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub_supp
  have hφ_supp : tsupport φ ⊆ Ioo (-1 : ℝ) 1 :=
    (closure_minimal hsub_supp isClosed_Icc).trans fun y hy ↦
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hle : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hφ_int : ∫ y, φ y = 1 := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const]
    norm_num
  have hφ_bound : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    dsimp only [φ]
    by_cases hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [indicator_of_mem hy]; norm_num
    · rw [indicator_of_notMem hy]; norm_num
  have hx_mem : (1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hrep := (sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel isOpen_Ioo
    hφ_meas hcpt hφ_supp hφ_int hφ_bound (u := id) (m := 0) contDiffOn_id hx_mem
    fun y hy ↦ (convex_Ioo (-1 : ℝ) 1).starConvex (hφ_supp hy)).2
  have hmean : ∫ y, φ y * (∑ j ∈ Finset.range 1,
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j (id : ℝ → ℝ) y (fun _ ↦ 1 / 2 - y)) = 0 := by
    have heq : (fun y : ℝ ↦ φ y * (∑ j ∈ Finset.range 1,
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j (id : ℝ → ℝ) y (fun _ ↦ 1 / 2 - y))) =
        (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun y ↦ y := by
      ext y
      dsimp only [φ]
      by_cases hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)
      · rw [indicator_of_mem hy, indicator_of_mem hy]; simp
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
    rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, integral_id]
    norm_num
  rw [← hrep, hmean]
  norm_num

/-- Polynomial exactness check: for `u = id` and `m = 1` on `Ω = (-1, 1)`, the second iterated
gradient vanishes everywhere, so the Taylor-remainder kernel integral is `0`. -/
example (x : ℝ) :
    let φ : ℝ → ℝ := (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun _ ↦ 1
    ∫ z in Ioo (-1 : ℝ) 1,
      taylorRemainderKernel φ 1 x z (iteratedGradientChain (id : ℝ → ℝ) 1 z) = 0 := by
  intro φ
  have h1 : iteratedGradientChain (id : ℝ → ℝ) 0 = fun _ ↦ (1 : ℝ) := by
    ext y
    apply ext_inner_right ℝ fun v ↦ ?_
    rw [iteratedGradientChain_zero, gradient, InnerProductSpace.toDual_symm_apply, fderiv_id]
    simp
  have hzero : ∀ z : ℝ, iteratedGradientChain (id : ℝ → ℝ) 1 z = 0 := fun z ↦ by
    rw [iteratedGradientChain_succ, h1, fderiv_const_apply]
  simp [hzero]

/-- Dimension-zero boundary check: on `EuclideanSpace ℝ (Fin 0)`, `taylorRemainderKernel` vanishes
identically for every cutoff `φ` and order `m`. -/
example (φ : EuclideanSpace ℝ (Fin 0) → ℝ) (m : ℕ) (x z : EuclideanSpace ℝ (Fin 0)) :
    taylorRemainderKernel φ m x z = 0 :=
  taylorRemainderKernel_of_subsingleton φ m x z

end Examples

end TauCeti
