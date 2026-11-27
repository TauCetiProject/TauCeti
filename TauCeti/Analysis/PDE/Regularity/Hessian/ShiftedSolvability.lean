/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.ZeroOrderShift
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.Regularity.Hessian.Resolvent
import TauCeti.MeasureTheory.Function.Lp.Trace
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Solvability of Krylov's shifted whole-space equation in `W^{2,p}`

Let `a` be a coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants `0 < λ ≤ Λ`,
neither symmetric nor continuous in general, whose operators `a(x)` have vanishing mean
oscillation, and let `2 < p < ∞`. This file proves that there is `λ₀ > 0` such that for every
`μ ≥ λ₀` and every `f ∈ Lᵖ(ℝ^{n+1})` the equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u = f` almost everywhere in `ℝ^{n+1}`

has exactly one strong solution `u ∈ W^{2,p}(ℝ^{n+1})`
(`TauCeti.PDE.exists_forall_existsUnique_sum_mul_inner_sub_mul_eq_of_memVMO`). Together with the
a priori estimate
`TauCeti.PDE.exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO`,

`μ ‖u‖_{Lᵖ} + √μ ‖∇u‖_{Lᵖ} + ‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

this is Krylov's whole-space theorem for `2 < p < ∞`: for `μ` above both thresholds,
`u ↦ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u` is a bijection from `W^{2,p}(ℝ^{n+1})` onto `Lᵖ(ℝ^{n+1})` whose inverse
obeys the estimate.

## The argument

* **The segment.** The coefficients `aₜ = t a + (1 - t) I`, `t ∈ [0, 1]`, are uniformly elliptic
  with the constants `min λ 1` and `max Λ 1`, and have vanishing mean oscillation. So the a priori
  estimate holds for each of them with one constant `C`, above a threshold `λ₀(t)` that depends on
  `t` through the radius below which the mean oscillation of `aₜ` is small.
* **One threshold.** The operators `Lₜ u = ∑ᵢⱼ (aₜ)ᵢⱼ ∂ᵢ∂ⱼu - μ u` satisfy
  `Lₜ u - Lₛ u = (t - s) ∑ᵢⱼ (aᵢⱼ - δᵢⱼ) ∂ᵢ∂ⱼu`, which is at most `K |t - s| ‖D²u‖`. The a priori
  estimate controls `‖D²u‖` by `C ‖Lₜ u‖` with no factor of `μ`, so for
  `|s - t| < 1 / (2 (C K + 1))` the estimate passes from `t` to `s` with the constant `2 C`, at
  every `μ ≥ λ₀(t)`: the radius does not depend on `μ`. Finitely many such neighbourhoods
  cover `[0, 1]`, and the largest of their thresholds serves the whole segment.
* **The method of continuity.** For `μ ≥ 1` this bounds the `W^{2,p}` norm of `u` by `2 C ‖Lₜ u‖`
  uniformly in `t`. At `t = 0` the operator is `Δ - μ`, which is onto
  (`TauCeti.Wkp.smul_valueL_sub_laplacianL_surjective`), so the method of continuity
  (`IsPreconnected.surjective_iff_of_forall_norm_le`) makes `L₁` onto, and the bound makes it
  injective.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

open Matrix

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The segment from the identity to `a` -/

section Segment

variable {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The coefficients `t a + (1 - t) I`, `0 ≤ t ≤ 1`, are uniformly elliptic with the constants
`min λ 1` and `max Λ 1`. -/
private theorem uniformlyEllipticOn_smul_add_one_sub_smul_one {lam Lam t : ℝ}
    (hell : UniformlyEllipticOn univ a lam Lam) (ht : t ∈ Icc (0 : ℝ) 1) :
    UniformlyEllipticOn univ (fun x => t • a x + (1 - t) • 1) (min lam 1) (max Lam 1) := by
  have hone : UniformlyEllipticOn univ (fun _ : EuclideanSpace ℝ (Fin (n + 1)) =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) (min lam 1) (max Lam 1) := by
    simpa using uniformlyEllipticOn_const_smul_one (n := Fin (n + 1)) univ (c := 1)
      (lt_min hell.pos one_pos) (min_le_right _ _) (le_max_right _ _)
  exact (hell.mono_constants (lt_min hell.pos one_pos) (min_le_left _ _)
    (le_max_left _ _)).smul_add_one_sub_smul hone (χ := fun _ => t) (fun _ => ht)
    (fun x hx => absurd (mem_univ x) hx)

/-- The coefficients `t a + (1 - t) I` have vanishing mean oscillation when `a` has. -/
private theorem memVMO_smul_add_one_sub_smul_one
    (hvmo : MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume) (t : ℝ) :
    MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ)
      (t • a x + (1 - t) • 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) volume := by
  have hone : MemVMO (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => (1 - t) •
      toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) volume := memVMO_const _
  refine ((hvmo.const_smul t).add hone).congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]

/-- **The operators along the segment.** There are bounded operators `T t`, `t ∈ ℝ`, on the `Lᵖ`
fields of endomorphisms of `ℝ^{n+1}`, Lipschitz in `t`, with `T t G` the contraction of `G` with
the coefficients `t a + (1 - t) I`. -/
private theorem exists_lipschitz_contraction_smul_add_one_sub_smul_one {lam Lam : ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) :
    ∃ (T : ℝ → Lp (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) →L[ℝ]
        Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))) (K : ℝ), 0 ≤ K ∧ Continuous T ∧
      (∀ s t G, ‖T s G - T t G‖ ≤ K * |s - t| * ‖G‖) ∧
      ∀ t G, ∀ᵐ x, T t G x = contraction (t • a x + (1 - t) • 1) (G x) := by
  -- Contraction with a uniformly elliptic field is a bounded operator.
  have hR : ∀ {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {l L : ℝ}, AEStronglyMeasurable b volume → UniformlyEllipticOn univ b l L →
      ∃ R : Lp (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
          ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
            (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) →L[ℝ]
          Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
            (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))),
        ∀ G, ∀ᵐ x, R G x = contraction (b x) (G x) := fun {b l L} hb hbell => by
    obtain ⟨R, hR⟩ := exists_continuousLinearMap_traceCLM_comp (p := p)
      (A := fun x => toEuclideanCLM (𝕜 := ℝ) (b x)) (Λ := L)
      (aestronglyMeasurable_toEuclideanCLM_iff.2 hb).restrict
      (ae_of_all _ fun x => by
        rw [← norm_matrixBilinearForm_eq_norm_toEuclideanCLM]
        exact hbell.opNorm_matrixBilinearForm_le (mem_univ x))
    refine ⟨R, fun G => ?_⟩
    have h := hR G
    rw [Measure.ae_restrict_coe_opens_top] at h
    filter_upwards [h] with x hx
    rw [hx, contraction_apply_eq_traceCLM]
  obtain ⟨R₀, hR₀⟩ := hR aestronglyMeasurable_const (uniformlyEllipticOn_const_one_one univ)
  obtain ⟨R₁, hR₁⟩ := hR ha hell
  refine ⟨fun t => R₀ + t • (R₁ - R₀), ‖R₁ - R₀‖, (R₁ - R₀).opNorm_nonneg,
    continuous_const.add (continuous_id.smul continuous_const), fun s t G => ?_, fun t G => ?_⟩
  · have h : (R₀ + s • (R₁ - R₀)) G - (R₀ + t • (R₁ - R₀)) G = (s - t) • (R₁ - R₀) G := by
      rw [_root_.add_apply, _root_.add_apply, _root_.smul_apply, _root_.smul_apply, sub_smul]
      abel
    rw [h, norm_smul, Real.norm_eq_abs, mul_comm ‖R₁ - R₀‖, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((R₁ - R₀).le_opNorm G) (abs_nonneg _)
  · filter_upwards [hR₀ G, hR₁ G,
      (Lp.coeFn_add (R₀ G) ((t • (R₁ - R₀)) G)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top,
      (Lp.coeFn_smul t ((R₁ - R₀) G)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top,
      (Lp.coeFn_sub (R₁ G) (R₀ G)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
      with x h₀ h₁ h₂ h₃ h₄
    rw [_root_.add_apply, h₂, Pi.add_apply, _root_.smul_apply, h₃, Pi.smul_apply,
      _root_.sub_apply, h₄, Pi.sub_apply, h₀, h₁, contraction_add, contraction_smul,
      contraction_smul, _root_.add_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring

end Segment

/-! ### One threshold for the whole segment -/

/-- **One threshold for the whole segment.** Let `T t`, `t ∈ [0, 1]`, be operators on the `Lᵖ`
fields of endomorphisms of `ℝ^{n+1}` with `‖T s G - T t G‖ ≤ K |s - t| ‖G‖`. Suppose that for each
`t ∈ [0, 1]` the shifted estimate

`μ ‖u‖ + √μ ‖∇u‖ + ‖D²u‖ ≤ C ‖T t (D²u) - μ u‖`

holds on `W^{2,p}(ℝ^{n+1})` for every `μ` above a threshold depending on `t`. Then one threshold
serves every `t ∈ [0, 1]`, with the constant `2 C`. -/
private theorem exists_forall_mul_norm_add_le_of_forall_mem_Icc {C K : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K)
    {T : ℝ → Lp (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) →L[ℝ]
        Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hT : ∀ s t G, ‖T s G - T t G‖ ≤ K * |s - t| * ‖G‖)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∃ lam₀ : ℝ, ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
        μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖) :
    ∃ lam₀ : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
        μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.iteratedGradient 1 u‖ ≤
            2 * C * ‖T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖ := by
  refine isCompact_Icc.induction_on (p := fun S => ∃ lam₀ : ℝ, ∀ t ∈ S, ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
        μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.iteratedGradient 1 u‖ ≤
            2 * C * ‖T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖)
    ⟨0, fun _ h => h.elim⟩ (fun _ _ hST ⟨lam₀, h⟩ => ⟨lam₀, fun t ht => h t (hST ht)⟩)
    (fun _ _ ⟨lam₁, h₁⟩ ⟨lam₂, h₂⟩ => ⟨max lam₁ lam₂, fun t ht μ hμ => ht.elim
      (fun ht => h₁ t ht μ ((le_max_left _ _).trans hμ))
      (fun ht => h₂ t ht μ ((le_max_right _ _).trans hμ))⟩) fun t ht => ?_
  obtain ⟨lam₀, hlam₀⟩ := h t ht
  -- Within `1 / (2 (C K + 1))` of `t`, the change of operator is absorbed by the Hessian term.
  set ε := (2 * (C * K + 1))⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hCKε : C * K * ε ≤ 1 / 2 := by
    rw [hε, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hC hK]
  refine ⟨Metric.ball t ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε0), max lam₀ 0,
    fun s hs μ hμ u => ?_⟩
  have hμ0 : 0 ≤ μ := (le_max_right _ _).trans hμ
  set X := μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
    ‖Wkp.iteratedGradient 1 u‖
  have hDX : ‖Wkp.iteratedGradient 1 u‖ ≤ X := by
    have := mul_nonneg hμ0 (norm_nonneg (Wkp.value 2 u))
    have := mul_nonneg (Real.sqrt_nonneg μ)
      (norm_nonneg (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)))
    linarith
  have hst : |t - s| ≤ ε := by
    rw [abs_sub_comm]
    exact (Metric.mem_ball.1 hs).le
  -- `‖T t D²u - μ u‖ ≤ ‖T s D²u - μ u‖ + K |t - s| ‖D²u‖`.
  have htri : ‖T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖ ≤
      ‖T s (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖ +
        K * |t - s| * ‖Wkp.iteratedGradient 1 u‖ := by
    refine (norm_le_norm_add_norm_sub' _ (T s (Wkp.iteratedGradient 1 u) -
      μ • Wkp.value 2 u)).trans ?_
    rw [sub_sub_sub_cancel_right]
    gcongr
    exact hT t s _
  have hX := (hlam₀ μ ((le_max_left _ _).trans hμ) u).trans
    (mul_le_mul_of_nonneg_left htri hC)
  have hsmall : C * (K * |t - s| * ‖Wkp.iteratedGradient 1 u‖) ≤ X / 2 := by
    calc C * (K * |t - s| * ‖Wkp.iteratedGradient 1 u‖)
        ≤ C * (K * ε * X) := by gcongr
      _ = C * K * ε * X := by ring
      _ ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hCKε ((norm_nonneg _).trans hDX)
      _ = X / 2 := by ring
  linarith

/-! ### The method of continuity from `Δ - μ` -/

/-- **`Δ - μ` is onto.** If `T` contracts the `Lᵖ` fields of endomorphisms of `ℝ^{n+1}` with the
identity, that is, takes their trace, then for `μ > 0` every `f ∈ Lᵖ(ℝ^{n+1})` is
`T (D²w) - μ w` for some `w ∈ W^{2,p}(ℝ^{n+1})`. -/
private theorem exists_eq_sub_smul_value_of_contraction_one (hp : 1 < p) (hp_top : p ≠ ⊤)
    {T : Lp (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) →L[ℝ]
        Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hT : ∀ G, ∀ᵐ x, T G x = contraction 1 (G x)) {μ : ℝ} (hμ : 0 < μ)
    (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
      (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
      T (Wkp.iteratedGradient 1 w) - μ • Wkp.value 2 w = f := by
  obtain ⟨w, hw⟩ := Wkp.smul_valueL_sub_laplacianL_surjective hp hp_top hμ (-f)
  refine ⟨w, Lp.ext ?_⟩
  have hf := Lp.coeFn_neg f
  rw [← hw] at hf
  have hΔ := Wkp.value_laplacianL_zero_ae_eq_trace (mu := volume) (Omega := ⊤) (p := p) w
  rw [Filter.EventuallyEq, Measure.ae_restrict_coe_opens_top] at hf hΔ ⊢
  filter_upwards [hf, hΔ, hT (Wkp.iteratedGradient 1 w),
    (Lp.coeFn_sub (T (Wkp.iteratedGradient 1 w)) (μ • Wkp.value 2 w)).filter_mono
      Measure.ae_le_ae_restrict_coe_opens_top,
    (Lp.coeFn_smul μ (Wkp.value 2 w)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top,
    (Lp.coeFn_sub (μ • Wkp.valueL 2 w) (Wkp.valueL 0 (Wkp.laplacianL 0 w))).filter_mono
      Measure.ae_le_ae_restrict_coe_opens_top,
    (Lp.coeFn_smul μ (Wkp.valueL 2 w)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [_root_.sub_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, h₆, Pi.sub_apply,
    h₇, Pi.smul_apply, Wkp.valueL_apply, Wkp.valueL_apply, h₂, Pi.neg_apply] at h₁
  rw [h₄, Pi.sub_apply, h₅, Pi.smul_apply, h₃, contraction_one, traceCLM_apply, smul_eq_mul]
  rw [smul_eq_mul] at h₁
  linarith

/-- **The method of continuity from `Δ - μ`.** Let `T t`, `t ∈ [0, 1]`, be operators on the `Lᵖ`
fields of endomorphisms of `ℝ^{n+1}`, continuous in `t`, with `T 0` the contraction with the
identity and `T 1 (D²u) = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Let `μ ≥ 1`, and suppose that

`μ ‖u‖ + √μ ‖∇u‖ + ‖D²u‖ ≤ C ‖T t (D²u) - μ u‖`

for every `t ∈ [0, 1]` and `u ∈ W^{2,p}(ℝ^{n+1})`. Then for every `f ∈ Lᵖ(ℝ^{n+1})` the equation
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u = f` has exactly one solution `u ∈ W^{2,p}(ℝ^{n+1})`. -/
private theorem existsUnique_of_forall_mem_Icc (hp : 1 < p) (hp_top : p ≠ ⊤)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {T : ℝ → Lp (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) →L[ℝ]
        Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hTc : Continuous T) (hT₀ : ∀ G, ∀ᵐ x, T 0 G x = contraction 1 (G x)) {μ C : ℝ}
    (hμ : 1 ≤ μ)
    (hT₁ : ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
      ∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x =
          (T 1 (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u) x)
    (hest : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
        μ * ‖Wkp.value 2 u‖ + √μ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u‖)
    (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
      (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
      ∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x = f x := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2 →L[ℝ]
      Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))),
      L = fun t => (T t).comp (Wkp.iteratedGradientL 1) - μ • Wkp.valueL 2 := ⟨_, rfl⟩
  have hL : ∀ t u, L t u = T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u := fun t u => by
    rw [hLdef, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      Wkp.iteratedGradientL_apply, Wkp.valueL_apply]
  have hLc : Continuous L := by
    rw [hLdef]
    exact (hTc.clm_comp continuous_const).sub continuous_const
  -- For `μ ≥ 1` the estimate bounds the `W^{2,p}` norm, uniformly in `t`.
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ C * ‖L t u‖ := fun t ht u => by
    rw [hL]
    refine le_trans ?_ (hest t ht u)
    have h₁ := Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient 1 u
    have h₂ := Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 (Wkp.lowerOrder 1 u)
    rw [Wkp.lowerOrder_zero, Wkp.value_lowerOrder_one] at h₂
    have h₃ := le_mul_of_one_le_left (norm_nonneg (Wkp.value 2 u)) hμ
    have h₄ := le_mul_of_one_le_left (norm_nonneg (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)))
      (Real.one_le_sqrt.2 hμ)
    linarith
  have hiff : ∀ v, (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 v x
      (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 v x = f x) ↔
        L 1 v = f := fun v => by
    rw [hL, Lp.ext_iff, Filter.EventuallyEq, Measure.ae_restrict_coe_opens_top]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h, hT₁ v] with x hx hx'
    · rw [← hx', hx]
    · rw [hx', hx]
  -- `L 0 = Δ - μ` is onto, hence so is `L 1`.
  obtain ⟨u, hu⟩ := (isPreconnected_Icc.surjective_iff_of_forall_norm_le hLc.continuousOn hnorm
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)).1 (fun g => by
      obtain ⟨w, hw⟩ := exists_eq_sub_smul_value_of_contraction_one hp hp_top hT₀
        (zero_lt_one.trans_le hμ) g
      exact ⟨w, (hL 0 w).trans hw⟩) f
  refine ⟨u, (hiff u).2 hu, fun v hv => ?_⟩
  have h := hnorm 1 (right_mem_Icc.2 zero_le_one) (v - u)
  rw [map_sub, (hiff v).1 hv, hu, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-! ### Solvability -/

/-- **Krylov's shifted whole-space equation is uniquely solvable in `W^{2,p}`.** Let `2 < p < ∞`,
and let `a` be a coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, whose
operators `a(x)` have vanishing mean oscillation. Then there is `λ₀ > 0` such that for every
`μ ≥ λ₀` and every `f ∈ Lᵖ(ℝ^{n+1})` there is exactly one `u ∈ W^{2,p}(ℝ^{n+1})` with

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu - μ u = f` almost everywhere.

The solution satisfies the a priori estimate
`TauCeti.PDE.exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO`
once `μ` is also above the threshold of that estimate. -/
theorem exists_forall_existsUnique_sum_mul_inner_sub_mul_eq_of_memVMO (hp : 2 < p)
    (hp_top : p ≠ ⊤) {lam Lam : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hvmo : MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume)
    (hell : UniformlyEllipticOn univ a lam Lam) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ μ : ℝ, lam₀ ≤ μ →
      ∀ f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))),
        ∃! u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2,
          ∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x = f x := by
  have ha : AEStronglyMeasurable a volume := aestronglyMeasurable_toEuclideanCLM_iff.1
    hvmo.memBMO.locallyIntegrable.aestronglyMeasurable
  obtain ⟨T, K, hK, hTc, hT, hTa⟩ :=
    exists_lipschitz_contraction_smul_add_one_sub_smul_one (p := p) ha hell
  -- `T t (D²u) - μ u` is the shifted operator with the coefficients `t a + (1 - t) I`.
  have hL : ∀ (t μ : ℝ) (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2),
      ∀ᵐ x, ∑ i, ∑ j, (t • a x + (1 - t) • 1) i j * ⟪Wkp.iteratedGradient 1 u x
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ - μ * Wkp.value 2 u x =
          (T t (Wkp.iteratedGradient 1 u) - μ • Wkp.value 2 u) x := fun t μ u => by
    filter_upwards [hTa t (Wkp.iteratedGradient 1 u), (Lp.coeFn_sub (T t (Wkp.iteratedGradient 1 u))
        (μ • Wkp.value 2 u)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top,
      (Lp.coeFn_smul μ (Wkp.value 2 u)).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
      with x h₁ h₂ h₃
    rw [h₂, Pi.sub_apply, h₃, Pi.smul_apply, h₁, contraction_apply, smul_eq_mul]
  -- One threshold and one constant for the whole segment.
  obtain ⟨C, hC⟩ :=
    exists_mul_norm_add_sqrt_mul_norm_add_norm_le_of_sum_mul_inner_sub_mul_eq_of_memVMO (n := n)
      hp hp_top (min lam 1) (max Lam 1)
  obtain ⟨lam₀, hest⟩ := exists_forall_mul_norm_add_le_of_forall_mem_Icc C.coe_nonneg hK hT
    fun t ht => by
      obtain ⟨lam₁, -, h⟩ := hC (memVMO_smul_add_one_sub_smul_one hvmo t)
        (uniformlyEllipticOn_smul_add_one_sub_smul_one hell ht)
      exact ⟨lam₁, fun μ hμ u => h μ hμ u _ (hL t μ u)⟩
  refine ⟨max lam₀ 1, lt_max_of_lt_right one_pos, fun μ hμ f => ?_⟩
  exact existsUnique_of_forall_mem_Icc (ENNReal.one_lt_two.trans hp) hp_top hTc
    (fun G => by simpa only [zero_smul, sub_zero, one_smul, zero_add] using hTa 0 G)
    ((le_max_right _ _).trans hμ)
    (fun u => by simpa only [one_smul, sub_self, zero_smul, add_zero] using hL 1 μ u)
    (fun t ht u => hest t ht μ ((le_max_left _ _).trans hμ) u) f

end PDE

end TauCeti
