/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Symmetry

/-!
# Endpoint norm formulas for the complex interpolation method

At the boundary points `θ = 0` and `θ = 1`, the complex interpolation norm of the class of an
admissible trace pair `g = (g₀, g₁)` reduces to the endpoint norm of the trace evaluated at `0`:

* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_mk_zero`: `‖mk 0 g‖ = ‖g₀ 0‖`;
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_mk_one`: `‖mk 1 g‖ = ‖g₁ 0‖`.

Both identities hold for any compatible couple of normed spaces without completeness or density
assumptions, by multiplying with Gaussian-type holomorphic cutoff factors `exp (A (z² - 2 z))` and
using symmetry (`ComplexMethodSpace.swap`).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines Set TauCeti.Complex.HadamardThreeLines
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

/-- Multiplying an admissible trace pair by a bounded `DiffContOnCl` scalar function `c` on the
open unit strip produces an admissible trace pair whose boundary traces are `c • g` on the two
vertical lines and whose quotient class at `θ ∈ [0, 1]` is `c θ • mk θ g`. -/
theorem exists_stripTraces_smul_of_diffContOnCl (g : C.stripTraces) {c : ℂ → ℂ}
    (hc : DiffContOnCl ℂ c (verticalStrip 0 1)) {K : ℝ}
    (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) :
    ∃ g' : C.stripTraces,
      (∀ t : ℝ, (g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
        c (t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) ∧
      (∀ t : ℝ, (g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
        c (1 + t * I) • (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) ∧
      ∀ ⦃θ : ℝ⦄, θ ∈ Icc 0 1 → mk θ g' = c θ • mk θ g := by
  have hcl {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : z ∈ closure (verticalStrip 0 1) := by
    rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
    exact hz
  have hT : IsBoundedAnalyticFamily
      (fun z => c z • ContinuousLinearMap.id ℂ C.SumSpace)
      (fun t => c (t * I) • ContinuousLinearMap.id ℂ X₀)
      (fun t => c (1 + t * I) • ContinuousLinearMap.id ℂ X₁) :=
    { differentiableOn :=
        (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ C.SumSpace)).differentiable
          |>.comp_differentiableOn hc.differentiableOn
      continuousOn_apply := fun _ =>
        (hc.continuousOn.mono fun _ => hcl).smul continuousOn_const
      exists_norm_le := ⟨max K 0, fun z hz =>
        ContinuousLinearMap.opNorm_le_bound _ (le_max_right K 0) fun x => by
          simpa [norm_smul] using mul_le_mul_of_nonneg_right
            ((hK z hz).trans (le_max_left _ _)) (norm_nonneg x)⟩
      continuous_fst := fun _ =>
        (hc.continuousOn.comp_continuous (by fun_prop) fun t =>
          hcl (by simp [verticalClosedStrip])).smul continuous_const
      continuous_snd := fun _ =>
        (hc.continuousOn.comp_continuous (by fun_prop) fun t =>
          hcl (by simp [verticalClosedStrip])).smul continuous_const
      exists_norm_fst_le := ⟨max K 0, fun t =>
        ContinuousLinearMap.opNorm_le_bound _ (le_max_right K 0) fun x => by
          simpa [norm_smul] using mul_le_mul_of_nonneg_right
            ((hK _ (by simp [verticalClosedStrip])).trans (le_max_left _ _)) (norm_nonneg x)⟩
      exists_norm_snd_le := ⟨max K 0, fun t =>
        ContinuousLinearMap.opNorm_le_bound _ (le_max_right K 0) fun x => by
          simpa [norm_smul] using mul_le_mul_of_nonneg_right
            ((hK _ (by simp [verticalClosedStrip])).trans (le_max_left _ _)) (norm_nonneg x)⟩
      apply_mul_I := fun _ _ => by simp
      apply_one_add_mul_I := fun _ _ => by simp }
  refine ⟨hT.stripTracesMap g,
    fun t => by simp,
    fun t => by simp,
    fun θ _ => toSum_injective ?_⟩
  rw [toSum_mk, map_smul, toSum_mk, hT.stripEval_stripTracesMap]
  simp

/-- Multiplying an admissible trace pair by a bounded holomorphic scalar function `c` on the strip
scales `mk θ g` by `c θ` and bounds its norm by the boundary suprema of `c • g`. -/
theorem norm_smul_mk_le_of_diffContOnCl {θ : ℝ} (hθ : θ ∈ Icc 0 1) (g : C.stripTraces)
    {c : ℂ → ℂ} (hc : DiffContOnCl ℂ c (verticalStrip 0 1))
    {K B : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) (hB : 0 ≤ B)
    (hb₀ : ∀ t : ℝ, ‖c (t * I) • g.val.1 t‖ ≤ B)
    (hb₁ : ∀ t : ℝ, ‖c (1 + t * I) • g.val.2 t‖ ≤ B) :
    ‖c θ‖ * ‖mk θ g‖ ≤ B := by
  obtain ⟨g', hg₀', hg₁', heq⟩ := exists_stripTraces_smul_of_diffContOnCl g hc hK
  rw [← norm_smul, ← heq hθ]
  refine ((norm_mk_le g').trans_eq (Submodule.norm_coe g').symm).trans (max_le ?_ ?_)
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₀']; exact hb₀ t
  · exact (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => by rw [hg₁']; exact hb₁ t

private theorem exp_neg_mul_norm_le {E : Type*} [NormedAddCommGroup E] {x y : ℝ} {f : C₀(ℝ, E)}
    {ε : ℝ} (hx : 0 < x) (hy : x ≤ y) (hε : 0 < ε) (hA : 2 * ‖f‖ / ε < x) (t : ℝ) :
    Real.exp (-y) * ‖f t‖ ≤ ε / 2 := by
  have h1 : Real.exp (-y) ≤ x⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hx (by linarith [Real.add_one_le_exp y])
  have h2 : ‖f‖ / x ≤ ε / 2 := (div_le_iff₀ hx).2 (by nlinarith [(div_lt_iff₀ hε).1 hA])
  exact (mul_le_mul h1 (ZeroAtInftyContinuousMap.norm_coe_le_norm f t) (norm_nonneg _)
    (inv_pos.2 hx).le).trans ((inv_mul_eq_div _ _).trans_le h2)

/-- Evaluating `mk 0 g` in the sum space recovers the left boundary trace at `0`. -/
theorem toSum_mk_zero (g : C.stripTraces) :
    toSum (mk 0 g) = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) := by
  rw [toSum_mk, stripEval_apply, ofReal_zero, ← zero_mul I, ← ofReal_zero, C.stripFunction_mul_I]

private theorem norm_mk_zero_le (g : C.stripTraces) : ‖mk 0 g‖ ≤ ‖g.val.1 0‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1
    ((map_continuous g.val.1).continuousAt (x := 0)) (ε / 2) (half_pos hε)
  obtain ⟨A, hAgt⟩ := exists_gt (max 0 (max (2 * ‖g.val.1‖ / (δ ^ 2 * ε)) (2 * ‖g.val.2‖ / ε)))
  have hA : 0 < A := (le_max_left _ _).trans_lt hAgt
  let c : ℂ → ℂ := fun z => Complex.exp ((A : ℂ) * (z ^ 2 - 2 * z))
  have hc_re (z : ℂ) : ((A : ℂ) * (z ^ 2 - 2 * z)).re = A * (z.re ^ 2 - z.im ^ 2 - 2 * z.re) := by
    simp [sq]
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ 1 := by
    rw [Complex.norm_exp, hc_re]
    exact Real.exp_le_one_iff.2
      (mul_nonpos_of_nonneg_of_nonpos hA.le (by nlinarith [hz.1, hz.2, sq_nonneg z.im]))
  have hbound := norm_smul_mk_le_of_diffContOnCl ⟨le_rfl, zero_le_one⟩ g
    (by unfold c; fun_prop : Differentiable ℂ c).diffContOnCl hc_le
    (B := ‖g.val.1 0‖ + ε / 2) (by positivity)
    (fun t => by
      rw [norm_smul]
      by_cases ht : |t| < δ
      · have hd := hclose (by simpa [Real.dist_eq] using ht)
        rw [dist_eq_norm] at hd
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (hc_le (t * I) (by simp [verticalClosedStrip]))).trans
          (by linarith [norm_sub_norm_le (g.val.1 t) (g.val.1 0)])
      · have hsq : δ ^ 2 ≤ t ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ hδ.le (not_lt.1 ht) 2
        have hA1 := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hAgt
        have hA1' : 2 * ‖g.val.1‖ / ε < A * δ ^ 2 :=
          (div_lt_iff₀ hε).2 (by nlinarith [(div_lt_iff₀ (by positivity)).1 hA1])
        have hc_norm : ‖c (t * I)‖ = Real.exp (-(A * t ^ 2)) := by
          rw [Complex.norm_exp, hc_re]; simp
        rw [hc_norm]
        exact (exp_neg_mul_norm_le (by positivity) (by nlinarith) hε hA1' t).trans
          (le_add_of_nonneg_left (norm_nonneg _)))
    (fun t => by
      have hc_norm : ‖c (1 + t * I)‖ = Real.exp (-(A * (1 + t ^ 2))) := by
        rw [Complex.norm_exp, hc_re]
        congr 1
        simp
        ring
      rw [norm_smul, hc_norm]
      exact (exp_neg_mul_norm_le hA (by nlinarith [sq_nonneg t]) hε
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hAgt) t).trans
        (le_add_of_nonneg_left (norm_nonneg _)))
  have hc0 : ‖c ((0 : ℝ) : ℂ)‖ = 1 := by simp [c]
  rw [hc0, one_mul] at hbound
  linarith [half_lt_self hε]

/-- At `θ = 0`, the quotient norm of an admissible trace pair is the norm in `X₀` of its left
boundary trace at `0`. -/
@[simp]
theorem norm_mk_zero (g : C.stripTraces) :
    ‖mk 0 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ := by
  refine le_antisymm (norm_mk_zero_le g) (le_of_forall_gt fun r hr => ?_)
  obtain ⟨h, heq, hh⟩ := norm_lt_iff.1 hr
  have hsum : C.fstToSum (h.val.1 0) = C.fstToSum (g.val.1 0) := by
    have heval := congrArg toSum heq
    rwa [toSum_mk_zero, toSum_mk_zero] at heval
  have h0 : h.val.1 0 = g.val.1 0 := C.fstToSum_injective hsum
  rw [← h0]
  exact ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ 0).trans (norm_fst_le h.val)).trans_lt
    (by rwa [Submodule.norm_coe])

/-- At `θ = 1`, the quotient norm of an admissible trace pair is the norm in `X₁` of its right
boundary trace at `0`. -/
@[simp]
theorem norm_mk_one (g : C.stripTraces) :
    ‖mk 1 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0‖ := by
  rw [← (swap C 1).norm_map (mk 1 g), swap_mk, sub_self, norm_mk_zero]
  simp only [stripTracesSwap_apply_fst, neg_zero]

end TauCeti.CompatibleCouple.ComplexMethodSpace
