/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Multivariate Cauchy expansions on polydiscs

The Cauchy integral on a polydisc expands into an unconditionally convergent series indexed
by exponent vectors. For a function continuous on the closed polydisc and holomorphic separately
in each open coordinate disc, the coefficients are its Cauchy integrals and the series recovers
the function throughout the open polydisc. A common boundary bound gives uniform convergence
in both parameters and evaluation points on every smaller closed polydisc. The codomain may be
any complex Banach space, and dimension zero is included.

The kernel expansion and interchange of integration and summation require only torus
integrability of the boundary values. The identification with the original function then
uses `ContinuousOn.torusIntegral_prod_sub_inv_smul`.

The partial sums of the expansion are polynomials, hence entire. So a function holomorphic on an
open polydisc is uniformly approximated by entire functions on every closed polydisc of smaller
polyradius (`DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`), the several-variable form
of `DifferentiableOn.exists_differentiable_norm_sub_lt`.

For a function complex differentiable on an open polydisc, the Cauchy coefficients on every
smaller torus are its multi-index Taylor coefficients `TauCeti.mvTaylorCoeff`
(`DifferentiableOn.mvTaylorCoeff_eq_torusIntegral`). So its Taylor series at the centre converges
on the whole open polydisc (`DifferentiableOn.hasSum_mvTaylorCoeff`), and a bound `M` on the
polydisc of radius `r` gives Cauchy's inequality `‖mvTaylorCoeff f z α‖ ≤ M r⁻¹ ^ |α|`
(`DifferentiableOn.norm_mvTaylorCoeff_le`).

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter MeasureTheory Metric Real Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

/-- Expanding the product Cauchy kernel and integrating term by term is valid for every
torus-integrable function. The sum is unconditional over all multi-indices. -/
theorem hasSum_torusIntegral_prod_geometric {f : (Fin n → ℂ) → E}
    {c w : Fin n → ℂ} {R : Fin n → ℝ} (hf : TorusIntegrable f c R)
    (hw : ∀ i, ‖w i‖ < R i) :
    HasSum (fun α : Fin n → ℕ ↦ ∯ z in T(c, R),
      (∏ i, (w i / (z i - c i)) ^ α i / (z i - c i)) • f z)
      (∯ z in T(c, R), (∏ i, (z i - (c i + w i))⁻¹) • f z) := by
  have hR (i) : 0 < R i := (norm_nonneg _).trans_lt (hw i)
  have hnorm (θ : Fin n → ℝ) (i : Fin n) :=
    norm_torusMap_apply_sub_center (c := c) θ i (hR i).le
  have hne (θ : Fin n → ℝ) (i : Fin n) : torusMap c R θ i - c i ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm]; exact (hR i).ne')
  let q : Fin n → ℝ := fun i ↦ ‖w i‖ / R i
  have hq₀ (i) : 0 ≤ q i := div_nonneg (norm_nonneg _) (hR i).le
  have hq₁ (i) : q i < 1 := (div_lt_one (hR i)).mpr (hw i)
  have hs : Summable (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) :=
    (hasSum_prod_geometric_of_norm_lt_one (fun i ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hq₀ i)] using hq₁ i)).summable
  -- The Jacobian cancels the reciprocal factors in the kernel, leaving a geometric majorant.
  have hb (α : Fin n → ℕ) (θ : Fin n → ℝ) :
      ‖(∏ i, (R i : ℂ) * exp (θ i * I) * I) •
        ((∏ i, (w i / (torusMap c R θ i - c i)) ^ α i /
          (torusMap c R θ i - c i)) • f (torusMap c R θ))‖ =
        ‖f (torusMap c R θ)‖ * ∏ i, q i ^ α i := by
    simp only [norm_smul, norm_prod, norm_mul, norm_I, mul_one, norm_real,
      norm_exp_ofReal_mul_I, norm_div, norm_pow, hnorm]
    rw [← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    dsimp [q]
    rw [abs_of_pos (hR i)]
    field_simp [(hR i).ne']
  -- Integrate the absolutely summable kernel expansion using the integrable boundary norm.
  unfold torusIntegral
  apply hasSum_integral_of_dominated_convergence
    (fun α θ ↦ ‖f (torusMap c R θ)‖ * ∏ i, q i ^ α i)
  · intro α
    apply AEStronglyMeasurable.smul
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · apply AEStronglyMeasurable.smul
      · exact Continuous.aestronglyMeasurable (by fun_prop (disch := intro θ; exact hne θ _))
      · exact hf.1
  · intro α
    exact ae_of_all _ fun θ ↦ (hb α θ).le
  · exact ae_of_all _ fun θ ↦ hs.mul_left _
  · simpa only [tsum_mul_left] using hf.norm.mul_const (∑' α : Fin n → ℕ, ∏ i, q i ^ α i)
  · apply ae_of_all
    intro θ
    have hg := hasSum_prod_geometric_div (z := fun i ↦ torusMap c R θ i - c i)
      (w := w) (fun i ↦ by simpa only [hnorm] using hw i)
    simpa only [sub_sub] using (hg.smul_const (f (torusMap c R θ))).const_smul
      (∏ i, (R i : ℂ) * exp (θ i * I) * I)

/-- A uniform bound on the distinguished boundary gives the geometric bound on every
multivariate Cauchy coefficient. No regularity of the boundary values is needed. -/
theorem norm_torusIntegral_cauchyCoeff_le {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R : Fin n → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hf : ∀ z ∈ univ.pi (fun i ↦ sphere (c i) (R i)), ‖f z‖ ≤ M)
    (α : Fin n → ℕ) :
    ‖(2 * π * I : ℂ)⁻¹ ^ n •
      ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z‖ ≤
      M * ∏ i, (R i)⁻¹ ^ α i := by
  have hk (θ : Fin n → ℝ) :
      ‖(∏ i, (torusMap c R θ i - c i) ^ (α i + 1))⁻¹ • f (torusMap c R θ)‖ ≤
        (∏ i, (R i ^ (α i + 1))⁻¹) * M := by
    simp only [norm_smul, norm_inv, norm_prod, norm_pow,
      norm_torusMap_apply_sub_center θ _ (hR _).le, ← Finset.prod_inv_distrib]
    exact mul_le_mul_of_nonneg_left
      (hf _ (torusMap_mem_pi_sphere (fun i ↦ (hR i).le) θ))
      (Finset.prod_nonneg fun i _ ↦ inv_nonneg.mpr (pow_nonneg (hR i).le _))
  have hb := norm_torusIntegral_le_of_norm_le_const
    (f := fun z ↦ (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z) hk
  calc
    _ ≤ ‖(2 * π * I : ℂ)⁻¹ ^ n‖ *
        (((2 * π) ^ n * ∏ i, |R i|) * ((∏ i, (R i ^ (α i + 1))⁻¹) * M)) :=
      (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ = M * ((∏ i, R i) * (∏ i, (R i ^ (α i + 1))⁻¹)) := by
      simp only [norm_pow, norm_inv, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos pi_pos, abs_of_pos (hR _), Complex.norm_ofNat]
      rw [inv_pow]
      field_simp
    _ = M * ∏ i, (R i)⁻¹ ^ α i := by
      rw [← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [← inv_pow, pow_succ]
      field_simp [(hR i).ne']

variable [CompleteSpace E]

/-- **The multivariate Cauchy expansion.** A function continuous on the closed polydisc and
holomorphic separately in each open coordinate disc is represented throughout the open polydisc
by its Cauchy coefficients. The exponent vector indexes an unconditionally convergent series,
so no choice of an enumeration is required. -/
theorem _root_.ContinuousOn.hasSum_torusIntegral_cauchyCoeff
    {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : ContinuousOn f (univ.pi fun i ↦ closedBall (c i) (R i)))
    (hd : ∀ z ∈ univ.pi (fun i ↦ closedBall (c i) (R i)), ∀ i, z i ∈ ball (c i) (R i) →
      DifferentiableAt ℂ (fun x ↦ f (Function.update z i x)) (z i))
    (hw : ∀ i, ‖w i‖ < R i) :
    HasSum (fun α : Fin n → ℕ ↦ (∏ i, w i ^ α i) •
      ((2 * π * I : ℂ)⁻¹ ^ n •
        ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z))
      (f (c + w)) := by
  have hR (i) : 0 < R i := (norm_nonneg _).trans_lt (hw i)
  have ht : TorusIntegrable f c R :=
    (hf.comp_continuous (continuous_torusMap c R) fun θ i _ ↦
      sphere_subset_closedBall (torusMap_mem_pi_sphere (fun i ↦ (hR i).le) θ i trivial))
      |>.integrableOn_Icc
  have h := (hasSum_torusIntegral_prod_geometric ht hw).const_smul
    ((2 * π * I : ℂ)⁻¹ ^ n)
  have hterm (α : Fin n → ℕ) :
      (∯ z in T(c, R), (∏ i, (w i / (z i - c i)) ^ α i / (z i - c i)) • f z) =
        (∏ i, w i ^ α i) •
          ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z := by
    rw [← torusIntegral_smul]
    congr 1
    funext z
    rw [smul_smul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [pow_succ, div_eq_mul_inv, mul_pow, mul_comm, mul_left_comm]
  simp only [hterm, smul_comm ((2 * π * I : ℂ)⁻¹ ^ n)] at h
  have hc : c + w ∈ univ.pi (fun i ↦ ball (c i) (R i)) := by
    intro i _
    simpa only [mem_ball, dist_eq_norm, Pi.add_apply, add_sub_cancel_left] using hw i
  have hi := hf.torusIntegral_prod_sub_inv_smul hd hc
  simp only [Pi.add_apply] at hi
  simp only [Finset.prod_inv_distrib] at h
  rw [hi] at h
  simpa only [inv_pow, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ two_pi_I_ne_zero), one_smul] using h

/-- Multivariate Cauchy expansions converge uniformly in the parameter and the evaluation
point on every smaller closed polydisc, if each function is continuous on the closed polydisc
and holomorphic separately in each open coordinate disc, with a common bound on the distinguished
boundary. No topology on the parameter set is needed. -/
theorem tendstoUniformlyOn_torusIntegral_cauchyCoeff {P : Type*} {S : Set P}
    {f : P → (Fin n → ℂ) → E} {c : Fin n → ℂ} {R r : Fin n → ℝ} {M : ℝ}
    (hrR : ∀ i, r i < R i)
    (hf : ∀ x ∈ S, ContinuousOn (f x) (univ.pi fun i ↦ closedBall (c i) (R i)))
    (hd : ∀ x ∈ S, ∀ z ∈ univ.pi (fun i ↦ closedBall (c i) (R i)), ∀ i,
      z i ∈ ball (c i) (R i) →
        DifferentiableAt ℂ (fun t ↦ f x (Function.update z i t)) (z i))
    (hb : ∀ x ∈ S, ∀ z ∈ univ.pi (fun i ↦ sphere (c i) (R i)), ‖f x z‖ ≤ M) :
    TendstoUniformlyOn
      (fun A : Finset (Fin n → ℕ) ↦ fun b : P × (Fin n → ℂ) ↦
        ∑ α ∈ A, (∏ i, b.2 i ^ α i) • ((2 * π * I : ℂ)⁻¹ ^ n •
          ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f b.1 z))
      (fun b ↦ f b.1 (c + b.2)) atTop
      (S ×ˢ univ.pi fun i ↦ closedBall 0 (r i)) := by
  by_cases hr : ∀ i, 0 ≤ r i
  swap
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    have hempty : (S ×ˢ univ.pi fun i ↦ closedBall (0 : ℂ) (r i)) = ∅ := by
      refine Set.prod_eq_empty_iff.mpr (Or.inr ?_)
      exact Set.univ_pi_eq_empty (i := i) (Metric.closedBall_eq_empty.mpr hi)
    rw [hempty]
    exact tendstoUniformlyOn_empty
  have hR (i) : 0 < R i := (hr i).trans_lt (hrR i)
  have hs : Summable (fun α : Fin n → ℕ ↦ ∏ i, (r i / R i) ^ α i) :=
    (hasSum_prod_geometric_of_norm_lt_one (r := fun i ↦ r i / R i) (fun i ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hr i) (hR i).le)]
      exact (div_lt_one (hR i)).mpr (hrR i))).summable
  apply (tendstoUniformlyOn_tsum (hs.mul_left M) ?_).congr_right
  · intro b hb'
    have hw (i : Fin n) : ‖b.2 i‖ < R i := by
      have hi : ‖b.2 i‖ ≤ r i := by
        simpa only [mem_closedBall, dist_zero_right] using hb'.2 i trivial
      exact hi.trans_lt (hrR i)
    exact ((hf b.1 hb'.1).hasSum_torusIntegral_cauchyCoeff (hd b.1 hb'.1) hw).tsum_eq
  · intro α b hb'
    rw [norm_smul, norm_prod]
    calc
      _ ≤ (∏ i, r i ^ α i) * (M * ∏ i, (R i)⁻¹ ^ α i) :=
        mul_le_mul
          (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _)
            (fun i _ ↦ by
              rw [norm_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (by
                simpa only [mem_closedBall, dist_zero_right] using hb'.2 i trivial) _))
          (norm_torusIntegral_cauchyCoeff_le hR (hb b.1 hb'.1) α)
          (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr i) _)
      _ = M * ∏ i, (r i / R i) ^ α i := by
        rw [mul_left_comm, ← Finset.prod_mul_distrib]
        simp only [← mul_pow, div_eq_mul_inv]

/-- The case `ι = Fin n` of `DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`: partial
sums of the Cauchy expansion on a polydisc of intermediate polyradius. -/
private theorem exists_differentiable_norm_sub_lt_of_fin {h : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {r s : Fin n → ℝ} {ε : ℝ} (hh : DifferentiableOn ℂ h (univ.pi fun i ↦ ball (c i) (s i)))
    (hrs : ∀ i, r i < s i) (hε : 0 < ε) :
    ∃ P : (Fin n → ℂ) → E, Differentiable ℂ P ∧
      ∀ z ∈ univ.pi fun i ↦ closedBall (c i) (r i), ‖h z - P z‖ < ε := by
  by_cases hr : ∃ i, r i < 0
  · obtain ⟨i, hi⟩ := hr
    exact ⟨0, differentiable_const 0, fun z hz ↦
      absurd (dist_nonneg.trans (mem_closedBall.1 (hz i trivial))) hi.not_ge⟩
  push Not at hr
  -- Expand on the closed polydisc of polyradius `R`, `r < R < s`, which lies in the open one.
  set R : Fin n → ℝ := fun i ↦ (r i + s i) / 2
  have hrR (i : Fin n) : r i < R i := by simp only [R]; linarith [hrs i]
  have hsub : (univ.pi fun i ↦ closedBall (c i) (R i)) ⊆ univ.pi fun i ↦ ball (c i) (s i) :=
    pi_mono fun i _ ↦ closedBall_subset_ball (by simp only [R]; linarith [hrs i])
  have hcont : ContinuousOn h (univ.pi fun i ↦ closedBall (c i) (R i)) :=
    hh.continuousOn.mono hsub
  have hopen : IsOpen (univ.pi fun i ↦ ball (c i) (s i)) :=
    isOpen_set_pi finite_univ fun i _ ↦ isOpen_ball
  obtain ⟨M, hM⟩ :=
    (isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) (R i)).exists_bound_of_continuousOn hcont
  have hU := tendstoUniformlyOn_torusIntegral_cauchyCoeff (S := (univ : Set Unit))
    (f := fun _ ↦ h) (R := R) (r := r) (M := M) hrR (fun _ _ ↦ hcont)
    (fun _ _ z hz i _ ↦ by
      have hz' : Function.update z i (z i) = z := Function.update_eq_self i z
      refine DifferentiableAt.comp (z i) ?_ (hasFDerivAt_update z (z i)).differentiableAt
      rw [hz']
      exact hh.differentiableAt (hopen.mem_nhds (hsub hz)))
    fun _ _ z hz ↦ hM z fun i _ ↦ sphere_subset_closedBall (hz i trivial)
  obtain ⟨A, hA⟩ := (Metric.tendstoUniformlyOn_iff.1 hU ε hε).exists
  refine ⟨fun z ↦ ∑ α ∈ A, (∏ i, (z - c) i ^ α i) • ((2 * π * I : ℂ)⁻¹ ^ n •
      ∯ w in T(c, R), (∏ i, (w i - c i) ^ (α i + 1))⁻¹ • h w), ?_, fun z hz ↦ ?_⟩
  · refine Differentiable.fun_sum fun α _ ↦ Differentiable.smul_const ?_ _
    intro z
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ ↦
      ((differentiableAt_apply i z).sub_const (c i)).pow (α i) |>.hasFDerivAt).differentiableAt
  · have hzc : z - c ∈ univ.pi fun i ↦ closedBall (0 : ℂ) (r i) := fun i _ ↦ by
      rw [mem_closedBall, dist_zero_right, Pi.sub_apply, ← dist_eq_norm]
      exact hz i trivial
    have := hA ((), z - c) ⟨trivial, hzc⟩
    rw [dist_eq_norm, add_sub_cancel] at this
    exact this

/-- **Polynomial approximation on polydiscs.** A function holomorphic on the open polydisc
`∏ B(c_i, s_i)` of `ι → ℂ` is uniformly approximated on every smaller closed polydisc
`∏ closedBall(c_i, r_i)`, `r_i < s_i`, by entire functions: partial sums of its multivariate Cauchy
expansion at `c`. -/
theorem _root_.DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi {ι : Type*} [Finite ι]
    {h : (ι → ℂ) → E} {c : ι → ℂ} {r s : ι → ℝ} {ε : ℝ}
    (hh : DifferentiableOn ℂ h (univ.pi fun i ↦ ball (c i) (s i))) (hrs : ∀ i, r i < s i)
    (hε : 0 < ε) :
    ∃ P : (ι → ℂ) → E, Differentiable ℂ P ∧
      ∀ z ∈ univ.pi fun i ↦ closedBall (c i) (r i), ‖h z - P z‖ < ε := by
  -- Transport to `Fin n → ℂ` along the complex-linear equivalence `L x = x ∘ e.symm` given by an
  -- enumeration `e` of `ι`.
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let L : (ι → ℂ) ≃L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toContinuousLinearEquiv
  have hL {t : ι → ℝ} {B : ℂ → ℝ → Set ℂ} {x : ι → ℂ} :
      L x ∈ (univ.pi fun k ↦ B (L c k) (t (e.symm k))) ↔ x ∈ univ.pi fun i ↦ B (c i) (t i) := by
    simp only [mem_univ_pi]
    refine e.symm.forall_congr_left.trans ?_
    simp [L, LinearEquiv.funCongrLeft_apply]
  obtain ⟨P, hP, hPh⟩ := exists_differentiable_norm_sub_lt_of_fin (c := L c) (h := h ∘ L.symm)
    (r := r ∘ e.symm) (s := s ∘ e.symm)
    (hh.comp L.symm.differentiable.differentiableOn fun y hy ↦ by
      rw [← L.apply_symm_apply y] at hy
      exact hL.1 hy) (fun k ↦ hrs _) hε
  refine ⟨P ∘ L, hP.comp L.differentiable, fun z hz ↦ ?_⟩
  simpa using hPh (L z) (hL.2 hz)

/-! ### Multi-index Taylor coefficients on polydiscs -/

section TaylorCoeff

variable {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} {z : Fin n → ℂ} {r : ℝ}

/-- On a closed polydisc inside an open set where `f` is complex differentiable, the Cauchy
coefficients of `f` are its multi-index Taylor coefficients. -/
private theorem mvTaylorCoeff_eq_cauchyCoeff (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hzr : closedBall z r ⊆ U) :
    (∀ w : Fin n → ℂ, ‖w‖ < r → HasSum (fun α : Fin n → ℕ ↦ (∏ i, w i ^ α i) •
      ((2 * π * I : ℂ)⁻¹ ^ n • ∯ ζ in T(z, fun _ ↦ r), (∏ i, (ζ i - z i) ^ (α i + 1))⁻¹ • f ζ))
      (f (z + w))) ∧
    ∀ α, mvTaylorCoeff f z α = (2 * π * I : ℂ)⁻¹ ^ n •
      ∯ ζ in T(z, fun _ ↦ r), (∏ i, (ζ i - z i) ^ (α i + 1))⁻¹ • f ζ := by
  rw [closedBall_pi z hr.le] at hzr
  have hcont : ContinuousOn f (univ.pi fun i ↦ closedBall (z i) r) := hf.continuousOn.mono hzr
  have hd (y) (hy : y ∈ univ.pi fun i ↦ closedBall (z i) r) (i) (_ : y i ∈ ball (z i) r) :
      DifferentiableAt ℂ (fun x ↦ f (Function.update y i x)) (y i) := by
    refine DifferentiableAt.comp (y i) ?_ (hasFDerivAt_update y (y i)).differentiableAt
    rw [Function.update_eq_self]
    exact hf.differentiableAt (hU.mem_nhds (hzr hy))
  have hexp (w : Fin n → ℂ) (hw : ‖w‖ < r) := hcont.hasSum_torusIntegral_cauchyCoeff hd
    (R := fun _ ↦ r) fun i ↦ (norm_le_pi_norm w i).trans_lt hw
  refine ⟨hexp, fun α ↦ ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun i ↦ isCompact_closedBall (z i) r)
    |>.exists_bound_of_continuousOn hcont
  have hbound (β : Fin n → ℕ) := norm_torusIntegral_cauchyCoeff_le (f := f) (c := z)
    (R := fun _ ↦ r) (M := M) (fun _ ↦ hr)
    (fun y hy ↦ hM y fun i _ ↦ sphere_subset_closedBall (hy i trivial)) β
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  set ρ : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hρ : (ρ : ℝ) = r / 2 := rfl
  refine mvTaylorCoeff_eq_of_hasSum (ρ := ρ) (NNReal.coe_pos.1 (by rw [hρ]; positivity))
    ((hasSum_prod_geometric_of_norm_lt_one fun _ : Fin n ↦ hhalf).summable.mul_left M
      |>.of_nonneg_of_le (fun _ ↦ by positivity) fun β ↦ ?_)
    (fun w hw ↦ hexp w (hw.trans (by rw [hρ]; linarith))) α
  rw [hρ]
  calc _ ≤ M * (∏ i, r⁻¹ ^ β i) * (r / 2) ^ (∑ i, β i) := by
        gcongr
        exact hbound β
    _ = M * ∏ i, (1 / 2 : ℝ) ^ β i := by
        rw [mul_assoc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [← mul_pow]
        congr 1
        field_simp

/-- **Cauchy's integral formula for Taylor coefficients on a polydisc.** If `f` is complex
differentiable on the open polydisc `ball z R` of `Fin n → ℂ` and `0 < r < R`, then the
multi-index Taylor coefficient `mvTaylorCoeff f z α` is the Cauchy integral
`(2πi)⁻ⁿ ∯ ζ in T(z, r), (∏ i, (ζ i - z i) ^ (α i + 1))⁻¹ • f ζ`. -/
theorem _root_.DifferentiableOn.mvTaylorCoeff_eq_torusIntegral {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z R)) (hr : 0 < r) (hrR : r < R) (α : Fin n → ℕ) :
    mvTaylorCoeff f z α = (2 * π * I : ℂ)⁻¹ ^ n •
      ∯ ζ in T(z, fun _ ↦ r), (∏ i, (ζ i - z i) ^ (α i + 1))⁻¹ • f ζ :=
  (mvTaylorCoeff_eq_cauchyCoeff isOpen_ball hf hr (closedBall_subset_ball hrR)).2 α

/-- **Taylor expansion on a polydisc.** If `f` is complex differentiable on the open polydisc
`ball z r` of `Fin n → ℂ`, then its multi-index Taylor series at `z` converges to `f (z + w)`
throughout that polydisc, `‖w‖ < r`. -/
theorem _root_.DifferentiableOn.hasSum_mvTaylorCoeff (hf : DifferentiableOn ℂ f (ball z r))
    {w : Fin n → ℂ} (hw : ‖w‖ < r) :
    HasSum (fun α : Fin n → ℕ ↦ (∏ i, w i ^ α i) • mvTaylorCoeff f z α) (f (z + w)) := by
  obtain ⟨r', hwr', hr'⟩ := exists_between hw
  obtain ⟨hexp, hcoeff⟩ := mvTaylorCoeff_eq_cauchyCoeff isOpen_ball hf
    ((norm_nonneg w).trans_lt hwr') (closedBall_subset_ball hr')
  simpa only [hcoeff] using hexp w hwr'

/-- **Cauchy's inequality on a polydisc.** If `f` is complex differentiable on the open polydisc
`ball z r` of `Fin n → ℂ`, `0 < r`, and `‖f‖ ≤ M` there, then
`‖mvTaylorCoeff f z α‖ ≤ M * r⁻¹ ^ (∑ i, α i)` for every multi-index `α`. -/
theorem _root_.DifferentiableOn.norm_mvTaylorCoeff_le (hf : DifferentiableOn ℂ f (ball z r))
    (hr : 0 < r) {M : ℝ} (hM : ∀ w ∈ ball z r, ‖f w‖ ≤ M) (α : Fin n → ℕ) :
    ‖mvTaylorCoeff f z α‖ ≤ M * r⁻¹ ^ (∑ i, α i) := by
  -- Cauchy's inequality on each smaller closed polydisc, then let its radius tend to `r`.
  have h (r' : ℝ) (hr' : r' ∈ Ioo 0 r) : ‖mvTaylorCoeff f z α‖ ≤ M * r'⁻¹ ^ (∑ i, α i) := by
    rw [hf.mvTaylorCoeff_eq_torusIntegral hr'.1 hr'.2 α, ← Finset.prod_pow_eq_pow_sum]
    refine norm_torusIntegral_cauchyCoeff_le (R := fun _ ↦ r') (fun _ ↦ hr'.1)
      (fun y hy ↦ hM y (closedBall_subset_ball hr'.2 ?_)) α
    rw [closedBall_pi z hr'.1.le]
    exact fun i _ ↦ sphere_subset_closedBall (hy i trivial)
  have hc : ContinuousAt (fun r' : ℝ ↦ M * r'⁻¹ ^ (∑ i, α i)) r :=
    continuousAt_const.mul ((continuousAt_inv₀ hr.ne').pow _)
  exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT hr) h)

end TaylorCoeff

end TauCeti
