/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth extension from a closed real interval

Every smooth map on a closed real interval with values in a complete real
normed space admits a globally smooth extension. The proof realizes arbitrary endpoint
jets by shrinking polynomial cutoffs, then glues the successive derivatives.
This supplies closed-interval endpoint representatives for reduced-length variations.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace TauCeti

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A fixed smooth compactly supported cutoff equal to one near the origin. -/
private def endpointJetCutoff : ContDiffBump (0 : ℝ) := default

/-- The divided monomial realizing one prescribed derivative at the origin. -/
private def endpointJetPolynomial (k : ℕ) (A : E) (x : ℝ) : E :=
  (x ^ k / (k.factorial : ℝ)) • A

/-- The divided jet monomial is smooth. -/
private theorem endpointJetPolynomial_contDiff (k : ℕ) (A : E) :
    ContDiff ℝ ∞ (endpointJetPolynomial k A) :=
  ((contDiff_id.pow k).div_const _).smul_const A

/-- At the origin, its only nonzero iterated derivative is the prescribed derivative of the
given order. -/
private theorem endpointJetPolynomial_deriv (k m : ℕ) (A : E) :
    iteratedDeriv m (endpointJetPolynomial k A) 0 = if m = k then A else 0 := by
  unfold endpointJetPolynomial
  have hp : ContDiffAt ℝ m (fun x : ℝ ↦ x ^ k / (k.factorial : ℝ)) 0 := by fun_prop
  rw [iteratedDeriv_smul_const hp A, iteratedDeriv_div_const,
    iteratedDeriv_fun_pow_zero]
  by_cases h : m = k <;> simp [h, Nat.factorial_ne_zero]

/-- The compactly supported cutoff of one divided jet monomial. -/
private def endpointJetBase (k : ℕ) (A : E) (x : ℝ) : E :=
  endpointJetCutoff x • endpointJetPolynomial k A x

/-- The cutoff jet monomial is smooth. -/
private theorem endpointJetBase_contDiff (k : ℕ) (A : E) :
    ContDiff ℝ ∞ (endpointJetBase k A) :=
  endpointJetCutoff.contDiff.smul (endpointJetPolynomial_contDiff k A)

/-- The cutoff jet monomial has compact support. -/
private theorem endpointJetBase_hasCompactSupport (k : ℕ) (A : E) :
    HasCompactSupport (endpointJetBase k A) :=
  endpointJetCutoff.hasCompactSupport.smul_right

/-- The cutoff jet agrees with its divided monomial near the origin. -/
private theorem endpointJetBase_eventually_eq (k : ℕ) (A : E) :
    endpointJetBase k A =ᶠ[𝓝 0] endpointJetPolynomial k A := by
  filter_upwards [endpointJetCutoff.eventuallyEq_one] with x hx
  simp only [endpointJetBase, hx, Pi.one_apply, one_smul]

/-- Cutting off preserves every iterated derivative at the origin. -/
private theorem endpointJetBase_deriv (k m : ℕ) (A : E) :
    iteratedDeriv m (endpointJetBase k A) 0 = if m = k then A else 0 := by
  rw [(endpointJetBase_eventually_eq k A).iteratedDeriv_eq m,
    endpointJetPolynomial_deriv]

/-- A single jet can be made uniformly small in every strictly lower derivative. -/
private theorem exists_small_endpointJet (k : ℕ) (A : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ m < k, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ ε) ∧
      (∀ m, iteratedDeriv m f 0 = if m = k then A else 0) := by
  let φ := endpointJetBase k A
  have hφ : ContDiff ℝ ∞ φ := endpointJetBase_contDiff k A
  have hsupp : HasCompactSupport φ := endpointJetBase_hasCompactSupport k A
  choose B hB using fun m : ℕ ↦
    (hsupp.iteratedFDeriv m).exists_bound_of_continuous
      ((hφ.of_le (show (m : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv')
  let C := 1 + ∑ m ∈ Finset.range k, max 0 (B m)
  have hsum : 0 ≤ ∑ m ∈ Finset.range k, max 0 (B m) :=
    Finset.sum_nonneg (fun m _ ↦ le_max_left _ _)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hBC (m : ℕ) (hm : m < k) : B m ≤ C := by
    have h := Finset.single_le_sum (s := Finset.range k) (f := fun i ↦ max 0 (B i))
      (fun i _ ↦ le_max_left 0 (B i)) (Finset.mem_range.mpr hm)
    dsimp only [C]
    linarith [le_max_right 0 (B m)]
  let r := min 1 (ε / C)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hε hC)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrC : r * C ≤ ε := (le_div_iff₀ hC).mp (min_le_right 1 (ε / C))
  let f : ℝ → E := fun x ↦ r ^ k • φ (r⁻¹ * x)
  have hf : ContDiff ℝ ∞ f :=
    (hφ.comp (contDiff_const.mul contDiff_id)).const_smul (r ^ k)
  have hfsupp : HasCompactSupport f := by
    exact (hsupp.comp_smul (inv_ne_zero hr.ne')).smul_left
  have hderiv (m : ℕ) (x : ℝ) :
      iteratedFDeriv ℝ m f x =
        (r ^ k * (r⁻¹) ^ m) • iteratedFDeriv ℝ m φ (r⁻¹ * x) := by
    have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hc : ContDiff ℝ ∞ (fun y : ℝ ↦ φ (r⁻¹ • y)) :=
      hφ.comp ((contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)).const_smul r⁻¹)
    -- Real scalar action on ℝ is multiplication; expose the local scaled function.
    have hfdef : f = (fun x ↦ r ^ k • φ (r⁻¹ • x)) := rfl
    rw [hfdef]
    rw [iteratedFDeriv_const_smul_apply' (i := m) (a := r ^ k)
      (hc.of_le hm).contDiffAt]
    rw [iteratedFDeriv_comp_const_smul r⁻¹ (hφ.of_le hm)]
    simp only [smul_smul, smul_eq_mul]
  have hsmall (m : ℕ) (hm : m < k) (x : ℝ) : ‖iteratedFDeriv ℝ m f x‖ ≤ ε := by
    have hfactor : r ^ k * (r⁻¹) ^ m = r ^ (k - m) := by
      rw [pow_sub₀ r hr.ne' hm.le, inv_pow]
    have hpow : r ^ (k - m) ≤ r := by
      simpa only [pow_one] using
        pow_le_pow_of_le_one hr.le hr1 (show 1 ≤ k - m by omega)
    rw [hderiv, hfactor, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le _)]
    calc
      r ^ (k - m) * ‖iteratedFDeriv ℝ m φ (r⁻¹ * x)‖ ≤ r ^ (k - m) * C :=
        mul_le_mul_of_nonneg_left ((hB m _).trans (hBC m hm)) (pow_nonneg hr.le _)
      _ ≤ r * C := mul_le_mul_of_nonneg_right hpow hC.le
      _ ≤ ε := hrC
  have hnear : f =ᶠ[𝓝 0] endpointJetPolynomial k A := by
    have hc : Tendsto (fun x : ℝ ↦ r⁻¹ * x) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ ↦ r⁻¹ * x) :=
        continuous_const.mul continuous_id
      simpa only [ContinuousAt, mul_zero] using
        hc.continuousAt (x := (0 : ℝ))
    filter_upwards [hc.eventually (endpointJetBase_eventually_eq k A)] with x hx
    -- The local f is the scaled endpointJetBase, and φ denotes that base.
    change r ^ k • endpointJetBase k A (r⁻¹ * x) = endpointJetPolynomial k A x
    rw [hx]
    unfold endpointJetPolynomial
    rw [smul_smul]
    congr 1
    rw [mul_pow, ← mul_div_assoc, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  exact ⟨f, hf, hfsupp, hsmall, fun m ↦
    (hnear.iteratedDeriv_eq m).trans (endpointJetPolynomial_deriv k m A)⟩

variable [CompleteSpace E]

/-- Endpoint jets have a genuine smooth representative on the real line. -/
theorem exists_smooth_endpoint_jets (A : ℕ → E) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ ∀ m, iteratedDeriv m f 0 = A m := by
  choose f hf hsupp hsmall hjet using fun k : ℕ ↦
    exists_small_endpointJet k (A k) (ε := (1 / 2 : ℝ) ^ k) (by positivity)
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  choose B hB using fun m k : ℕ ↦
    ((hsupp k).iteratedFDeriv m).exists_bound_of_continuous
      (((hf k).of_le (show (m : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv')
  let C : ℕ → ℕ → ℝ := fun m k ↦ if m < k then (1 / 2 : ℝ) ^ k else B m k
  have hCsummable (m : ℕ) : Summable (C m) := by
    apply hgeom.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop m] with k hk
    simp only [C, ite_eq_left hk]
  have hbound (m k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ m (f k) x‖ ≤ C m k := by
    by_cases h : m < k
    · simpa only [C, ite_eq_left h] using hsmall k m h x
    · simpa only [C, ite_eq_right h] using hB m k x
  let g : ℝ → E := fun x ↦ ∑' k, f k x
  have hg : ContDiff ℝ ∞ g :=
    contDiff_tsum hf (fun m _ ↦ hCsummable m) (fun m k x _ ↦ hbound m k x)
  refine ⟨g, hg, ?_⟩
  intro m
  have hd : iteratedFDeriv ℝ m g 0 = ∑' k, iteratedFDeriv ℝ m (f k) 0 :=
    iteratedFDeriv_tsum_apply hf (fun j _ ↦ hCsummable j)
      (fun j k x _ ↦ hbound j k x) (by simp) 0
  have hj : iteratedDeriv m g 0 = ∑' k, iteratedDeriv m (f k) 0 := by
    simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
    rw [hd]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) E).symm.toContinuousLinearEquiv.map_tsum
  rw [hj]
  simp only [hjet]
  simpa only [eq_comm] using (tsum_ite_eq m (fun k ↦ A k))

end Jets

section Pasting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Paste left, closed-interval and right derivative towers with the two specified break points. -/
private def pasteEndpointDerivatives (a b : ℝ) (f l r : ℕ → ℝ → E)
    (k : ℕ) (x : ℝ) : E :=
  if x ≤ a then l k x else if x ≤ b then f k x else r k x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The pasted tower equals the left tower on the left closed half-line. -/
private theorem pasteEndpointDerivatives_eq_left {a b : ℝ} {f l r : ℕ → ℝ → E}
    (k : ℕ) {x : ℝ} (hx : x ≤ a) : pasteEndpointDerivatives a b f l r k x = l k x :=
  ite_eq_left hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Matching left endpoint jets make the pasted tower agree with the middle tower on the closed
interval. -/
private theorem pasteEndpointDerivatives_eq_middle {a b : ℝ} {f l r : ℕ → ℝ → E}
    (hl : ∀ k, l k a = f k a) (k : ℕ) {x : ℝ} (hx : x ∈ Icc a b) :
    pasteEndpointDerivatives a b f l r k x = f k x := by
  by_cases ha : x ≤ a
  · have hxa : x = a := le_antisymm ha hx.1
    simpa only [pasteEndpointDerivatives, hxa, le_refl, ite_eq_left] using hl k
  · simp only [pasteEndpointDerivatives, ite_eq_right ha, ite_eq_left hx.2]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Matching right endpoint jets make the pasted tower agree with the right tower on the right
closed half-line. -/
private theorem pasteEndpointDerivatives_eq_right {a b : ℝ} (hab : a < b)
    {f l r : ℕ → ℝ → E} (hr : ∀ k, r k b = f k b)
    (k : ℕ) {x : ℝ} (hx : b ≤ x) :
    pasteEndpointDerivatives a b f l r k x = r k x := by
  have hxa : ¬ x ≤ a := not_le.mpr (hab.trans_le hx)
  by_cases hxb : x ≤ b
  · have hxb' : x = b := le_antisymm hxb hx
    simpa only [pasteEndpointDerivatives, hxb', not_le.mpr hab, ite_false, le_refl, ite_true]
      using (hr k).symm
  · simp only [pasteEndpointDerivatives, ite_eq_right hxa, ite_eq_right hxb]

/-- Matching endpoint values for every derivative make the pasted derivative tower
differentiable through both break points. -/
private theorem pasteEndpointDerivatives_hasDerivAt {a b : ℝ} (hab : a < b)
    (f l r : ℕ → ℝ → E)
    (hf : ∀ k x, x ∈ Icc a b → HasDerivWithinAt (f k) (f (k + 1) x) (Icc a b) x)
    (hl : ∀ k x, HasDerivAt (l k) (l (k + 1) x) x)
    (hr : ∀ k x, HasDerivAt (r k) (r (k + 1) x) x)
    (hla : ∀ k, l k a = f k a) (hrb : ∀ k, r k b = f k b)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (pasteEndpointDerivatives a b f l r k)
      (pasteEndpointDerivatives a b f l r (k + 1) x) x := by
  let F := pasteEndpointDerivatives a b f l r
  have hL : EqOn (F k) (l k) (Iic a) := fun _ hx ↦ pasteEndpointDerivatives_eq_left k hx
  have hC : EqOn (F k) (f k) (Icc a b) :=
    fun _ hx ↦ pasteEndpointDerivatives_eq_middle hla k hx
  have hR : EqOn (F k) (r k) (Ici b) :=
    fun _ hx ↦ pasteEndpointDerivatives_eq_right hab hrb k hx
  rcases lt_trichotomy x a with hxa | hxa | hax
  · rw [pasteEndpointDerivatives_eq_left (k + 1) hxa.le]
    exact (hl k x).congr_of_eventuallyEq (eventuallyEq_of_mem (Iic_mem_nhds hxa) hL)
  · subst x
    have hleft : HasDerivWithinAt (F k) (f (k + 1) a) (Iic a) a := by
      rw [← hla (k + 1)]
      exact (hl k a).hasDerivWithinAt.congr_of_mem hL self_mem_Iic
    have hcenter : HasDerivWithinAt (F k) (f (k + 1) a) (Icc a b) a :=
      (hf k a ⟨le_rfl, hab.le⟩).congr_of_mem hC ⟨le_rfl, hab.le⟩
    rw [pasteEndpointDerivatives_eq_middle hla (k + 1) ⟨le_rfl, hab.le⟩]
    apply (hleft.union hcenter).hasDerivAt
    rw [Iic_union_Icc_eq_Iic hab.le]
    exact Iic_mem_nhds hab
  · rcases lt_trichotomy x b with hxb | hxb | hbx
    · rw [pasteEndpointDerivatives_eq_middle hla (k + 1) ⟨hax.le, hxb.le⟩]
      exact ((hf k x ⟨hax.le, hxb.le⟩).congr_of_mem hC ⟨hax.le, hxb.le⟩).hasDerivAt
        (Icc_mem_nhds hax hxb)
    · subst x
      have hcenter : HasDerivWithinAt (F k) (f (k + 1) b) (Icc a b) b :=
        (hf k b ⟨hab.le, le_rfl⟩).congr_of_mem hC ⟨hab.le, le_rfl⟩
      have hright : HasDerivWithinAt (F k) (f (k + 1) b) (Ici b) b := by
        rw [← hrb (k + 1)]
        exact (hr k b).hasDerivWithinAt.congr_of_mem hR self_mem_Ici
      rw [pasteEndpointDerivatives_eq_middle hla (k + 1) ⟨hab.le, le_rfl⟩]
      apply (hcenter.union hright).hasDerivAt
      rw [Icc_union_Ici_eq_Ici hab.le]
      exact Ici_mem_nhds hab
    · rw [pasteEndpointDerivatives_eq_right hab hrb (k + 1) hbx.le]
      exact (hr k x).congr_of_eventuallyEq (eventuallyEq_of_mem (Ici_mem_nhds hbx) hR)

/-- Smooth functions with all matching left and right endpoint jets paste to a globally smooth
representative of the closed-interval function. -/
theorem smooth_pasting_of_matching_endpoint_jets {a b : ℝ} (hab : a < b)
    (f l r : ℝ → E) (hf : ContDiffOn ℝ ∞ f (Icc a b))
    (hl : ContDiff ℝ ∞ l) (hr : ContDiff ℝ ∞ r)
    (hla : ∀ k, iteratedDeriv k l a = iteratedDerivWithin k f (Icc a b) a)
    (hrb : ∀ k, iteratedDeriv k r b = iteratedDerivWithin k f (Icc a b) b) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ EqOn g f (Icc a b) := by
  let F := pasteEndpointDerivatives a b
    (fun k ↦ iteratedDerivWithin k f (Icc a b)) (fun k ↦ iteratedDeriv k l)
      (fun k ↦ iteratedDeriv k r)
  have hk (k : ℕ) : (k : ℕ∞ω) < ∞ := by
    -- ℕ∞ω is a second WithTop; compare the embedded finite order below smoothness.
    change (↑(k : ℕ∞) : ℕ∞ω) < ↑(⊤ : ℕ∞)
    exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)
  have hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x := by
    apply pasteEndpointDerivatives_hasDerivAt hab _ _ _ _ _ _ hla hrb
    · intro k x hx
      rw [iteratedDerivWithin_succ]
      exact ((hf.differentiableOn_iteratedDerivWithin (hk k)
        (uniqueDiffOn_Icc hab)) x hx).hasDerivWithinAt
    · intro k x
      rw [iteratedDeriv_succ]
      exact (hl.differentiable_iteratedDeriv k (hk k) x).hasDerivAt
    · intro k x
      rw [iteratedDeriv_succ]
      exact (hr.differentiable_iteratedDeriv k (hk k) x).hasDerivAt
  refine ⟨F 0, contDiff_of_derivative_tower F hF, ?_⟩
  intro x hx
  simpa only [iteratedDerivWithin_zero] using pasteEndpointDerivatives_eq_middle hla 0 hx

end Pasting

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth map from a closed real interval to a complete real normed space has a
globally smooth extension agreeing on the interval. -/
theorem exists_smooth_extension_Icc {a b : ℝ}
    (f : ℝ → E) (hf : ContDiffOn ℝ ∞ f (Icc a b)) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ EqOn g f (Icc a b) := by
  by_cases hab : a < b
  · obtain ⟨L, hL, hLa⟩ := exists_smooth_endpoint_jets
      (fun k ↦ iteratedDerivWithin k f (Icc a b) a)
    obtain ⟨R, hR, hRb⟩ := exists_smooth_endpoint_jets
      (fun k ↦ iteratedDerivWithin k f (Icc a b) b)
    apply smooth_pasting_of_matching_endpoint_jets hab f
      (fun x ↦ L (x - a)) (fun x ↦ R (x - b)) hf
      (hL.comp (contDiff_id.sub contDiff_const)) (hR.comp (contDiff_id.sub contDiff_const))
    · intro k
      simpa only [iteratedDeriv_comp_sub_const, sub_self] using hLa k
    · intro k
      simpa only [iteratedDeriv_comp_sub_const, sub_self] using hRb k
  · refine ⟨fun _ ↦ f a, contDiff_const, ?_⟩
    intro x hx
    have hxa : x = a := le_antisymm (hx.2.trans (le_of_not_gt hab)) hx.1
    simp only [hxa]

end Euclidean

end TauCeti
