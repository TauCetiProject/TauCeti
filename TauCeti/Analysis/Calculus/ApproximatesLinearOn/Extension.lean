/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ApproximatesLinearOn.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Calculus.Hadamard
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Extending local diffeomorphisms to global ones

A map `f` that is `C^k` (`k ≥ 1`) on an open set `U` of a finite-dimensional real normed space
agrees, near any point `x₀ ∈ U`, with a map `g` that is `C^k` on the whole space and whose
derivative stays uniformly close to `f'(x₀)`
(`ContDiffOn.exists_contDiff_eventuallyEq_norm_fderiv_sub_le`). The map `g` is the affine
approximation of `f` at `x₀` plus the deviation `f(x) - f(x₀) - f'(x₀)(x - x₀)` multiplied by a
cutoff supported in a ball of radius `r` around `x₀`. On that ball the deviation has derivative at
most `δ` and size at most `δ r`, while the cutoff has derivative at most a multiple of `r⁻¹`, so
both terms of the derivative of the product are at most a multiple of `δ`, whatever `r` is.

When `f'(x₀)` is invertible and the derivative of `g` stays within `‖f'(x₀)⁻¹‖⁻¹ / 2` of it, `g`
approximates the linear equivalence `f'(x₀)` on the whole space, so it is a homeomorphism
(`ContDiffOn.exists_homeomorph_eventuallyEq_nnNorm_fderiv_sub_le`). Its derivatives and its averaged
derivatives `hadamardFactor` are then all invertible, so an open partial homeomorphism that is `C^k`
with `C^k` inverse agrees near each point of its source with such a global homeomorphism
(`OpenPartialHomeomorph.exists_eqOn_homeomorph_isUnit_hadamardFactor`). This replaces a local
diffeomorphism near a point by a global diffeomorphism all of whose derivatives are invertible, for
instance to apply a change of variables stated for diffeomorphisms of the whole space to the
transition maps of the charts of a manifold. Mathlib's
`ApproximatesLinearOn.exists_homeomorph_extension` extends a map approximating a linear equivalence
to a homeomorphism by a Lipschitz extension; the cutoff construction here keeps the extension `C^k`.
-/

public section

open Set Filter Topology Metric
open scoped NNReal ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The derivative of `χ • h` for a cutoff `χ` supported in a ball around `x₀`, with values in
`[0, 1]` and derivative at most `C`, and a map `h` vanishing at `x₀` whose derivative on the ball
is at most `δ`: on the ball `‖h‖ ≤ δ r`, so the derivative is at most `δ + C δ r`. -/
private theorem norm_fderiv_smul_le {χ : E → ℝ} {χ' : E → E →L[ℝ] ℝ} {h : E → F}
    {h' : E → E →L[ℝ] F} {x₀ : E} {r δ C : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hχd : ∀ x, HasFDerivAt χ (χ' x) x) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ' : ∀ x, ‖χ' x‖ ≤ C)
    (hχs : tsupport χ ⊆ ball x₀ r) (hhd : ∀ x ∈ ball x₀ r, HasFDerivAt h (h' x) x)
    (hh' : ∀ x ∈ ball x₀ r, ‖h' x‖ ≤ δ) (hh0 : h x₀ = 0) (x : E) :
    ‖fderiv ℝ (fun y ↦ χ y • h y) x‖ ≤ δ + C * (δ * r) := by
  by_cases hx : x ∈ ball x₀ r
  · have hhx : ‖h x‖ ≤ δ * r := by
      have hmv := (convex_ball x₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy ↦ (hhd y hy).hasFDerivWithinAt) hh' (mem_ball_self (pos_of_mem_ball hx)) hx
      rw [hh0, sub_zero] at hmv
      exact hmv.trans (mul_le_mul_of_nonneg_left (mem_ball_iff_norm.1 hx).le hδ)
    have hd : HasFDerivAt (fun y ↦ χ y • h y) (χ x • h' x + (χ' x).smulRight (h x)) x :=
      (hχd x).smul (hhd x hx)
    rw [hd.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs,
      abs_of_nonneg (hχ01 x).1]
    gcongr
    · calc χ x * ‖h' x‖ ≤ 1 * δ := mul_le_mul (hχ01 x).2 (hh' x hx) (norm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    · exact hχ' x
  · have h0 : (fun y ↦ χ y • h y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h' ↦ hx (hχs h')] with y hy
      simp [hy]
    rw [h0.fderiv_eq, fderiv_zero, Pi.zero_apply, norm_zero]
    positivity

/-- **Extending a map with almost constant derivative near a point.** A map `f` that is `C^k`
(`k ≥ 1`) on an open set `U` agrees near any point `x₀ ∈ U` with a map `g`, `C^k` on the whole
space, whose derivative stays within `ε` of `f'(x₀)` everywhere. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_norm_fderiv_sub_le {f : E → F} {U : Set E}
    {k : ℕ∞} (hf : ContDiffOn ℝ k f U) (hU : IsOpen U) (hk : 1 ≤ k) {x₀ : E} (hx₀ : x₀ ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ k g ∧ g =ᶠ[𝓝 x₀] f ∧ ∀ x, ‖fderiv ℝ g x - fderiv ℝ f x₀‖ ≤ ε := by
  obtain ⟨C, hC0, hcut⟩ := TauCeti.exists_cutoff_fderiv_bound (E := E)
  set A := fderiv ℝ f x₀
  set δ := ε / (1 + 4 * C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hk' : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hk).ne'
  -- A ball around `x₀` inside `U` on which the derivative of `f` is within `δ` of `A`.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1
    ((hf.continuousOn_fderiv_of_isOpen hU (by exact_mod_cast hk)).isOpen_inter_preimage hU
      (isOpen_lt (continuous_norm.comp (continuous_sub_right A))
        (continuous_const : Continuous fun _ : E →L[ℝ] F ↦ δ))) x₀
    ⟨hx₀, by simp only [mem_preimage, mem_ofPred_eq, Function.comp_apply, A, sub_self, norm_zero]
             exact hδ⟩
  -- A cutoff equal to `1` near `x₀`, supported in that ball, with derivative at most `4 C / r`.
  obtain ⟨χ, χ', hχ, hχ01, hχ1, hχ0, hχd, hχ'b, -, -⟩ := hcut x₀ (r / 4) (by positivity)
  have hχs : tsupport χ ⊆ ball x₀ r := by
    refine (closure_minimal (fun x hx ↦ ?_) isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith : 2 * (r / 4) < r))
    by_contra h
    exact hx (hχ0 x (not_le.1 h))
  -- The deviation `h` of `f` from its affine approximation at `x₀`, cut off by `χ`.
  set h : E → F := fun x ↦ f x - f x₀ - A (x - x₀)
  have hhd : ∀ x ∈ U, HasFDerivAt h (fderiv ℝ f x - A) x := fun x hx ↦
    ((((hf.differentiableOn hk' x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.sub_const
      (f x₀)).sub (A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))).congr_fderiv
      (by simp)
  have hχh : ContDiff ℝ k fun x ↦ χ x • h x :=
    ((hf.sub contDiffOn_const).sub (A.contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffOn).contDiff_smul_of_tsupport_subset hU
      (hχ k).contDiffOn (hχs.trans fun y hy ↦ (hrU hy).1)
  refine ⟨fun x ↦ f x₀ + A (x - x₀) + χ x • h x,
    (contDiff_const.add (A.contDiff.comp (contDiff_id.sub contDiff_const))).add hχh, ?_,
    fun x ↦ ?_⟩
  · filter_upwards [closedBall_mem_nhds x₀ (by positivity : 0 < r / 4)] with x hx
    simp [h, hχ1 x hx]
  -- The derivative of the extension is `A` plus that of `χ • h`.
  have hgd : HasFDerivAt (fun x ↦ f x₀ + A (x - x₀) + χ x • h x)
      (A + fderiv ℝ (fun x ↦ χ x • h x) x) x :=
    (((hasFDerivAt_const (f x₀) x).add (A.hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const x₀))).add (hχh.differentiable hk' x).hasFDerivAt).congr_fderiv
      (by simp)
  rw [hgd.fderiv, add_sub_cancel_left]
  refine (norm_fderiv_smul_le hr.le hδ.le (by positivity) hχd hχ01 hχ'b hχs
    (fun y hy ↦ hhd y (hrU hy).1) (fun y hy ↦ (hrU hy).2.le) (by simp [h]) x).trans_eq ?_
  field_simp
  simp only [δ]
  field_simp

/-- **A local diffeomorphism agrees near a point with a global homeomorphism.** A map `f : E → F`
that is `C^k` (`k ≥ 1`) on an open set `U`, with invertible derivative `A` at `x₀ ∈ U`, agrees near
`x₀` with a homeomorphism `g : E ≃ₜ F` that is `C^k` and whose derivative stays within
`‖A⁻¹‖⁻¹ / 2` of `A` everywhere. In particular every derivative of `g` is invertible
(`ContinuousLinearMap.isInvertible_of_norm_sub_le_half`). -/
theorem ContDiffOn.exists_homeomorph_eventuallyEq_nnNorm_fderiv_sub_le {f : E → F} {U : Set E}
    {k : ℕ∞} (hf : ContDiffOn ℝ k f U) (hU : IsOpen U) (hk : 1 ≤ k) {x₀ : E} (hx₀ : x₀ ∈ U)
    {A : E ≃L[ℝ] F} (hA : fderiv ℝ f x₀ = A) :
    ∃ g : E ≃ₜ F, ContDiff ℝ k g ∧ ⇑g =ᶠ[𝓝 x₀] f ∧
      ∀ x, ‖fderiv ℝ g x - A‖₊ ≤ ‖(A.symm : F →L[ℝ] E)‖₊⁻¹ / 2 := by
  rcases A.subsingleton_or_nnNorm_symm_pos with hE | hpos
  · have : Subsingleton F := A.toEquiv.symm.subsingleton
    refine ⟨A.toHomeomorph, A.contDiff, .of_forall fun x ↦ Subsingleton.elim _ _, fun x ↦ ?_⟩
    rw [Subsingleton.elim (fderiv ℝ _ x - _) 0, nnNorm_zero]
    exact zero_le
  set c : ℝ≥0 := ‖(A.symm : F →L[ℝ] E)‖₊⁻¹ / 2
  obtain ⟨g, hg, hgf, hgd⟩ := hf.exists_contDiff_eventuallyEq_norm_fderiv_sub_le hU hk hx₀
    (ε := c) (NNReal.coe_pos.2 (half_pos (inv_pos.2 hpos)))
  rw [hA] at hgd
  have hk' : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hk).ne'
  have happrox : ApproximatesLinearOn g (A : E →L[ℝ] F) univ c :=
    convex_univ.approximatesLinearOn_of_nnnorm_fderiv_sub_le
      (fun x _ ↦ hg.differentiable hk' x) fun x _ ↦ by exact_mod_cast hgd x
  exact ⟨happrox.toHomeomorph g (.inr (NNReal.half_lt_self (inv_pos.2 hpos).ne')), hg, hgf,
    fun x ↦ by exact_mod_cast hgd x⟩

/-- **A local diffeomorphism agrees near each point with a global diffeomorphism with invertible
averaged derivatives.** Near each point `x₀` of its source, an open partial homeomorphism `κ` of a
finite-dimensional real normed space that is `C^k` (`k ≥ 1`) with `C^k` inverse agrees, on an open
neighbourhood `N` of `x₀` in its source, with a `C^k` homeomorphism `κ'` of the whole space all of
whose derivatives and Hadamard factors `∫₀¹ Dκ'(y + t (x - y)) dt` are invertible. -/
theorem OpenPartialHomeomorph.exists_eqOn_homeomorph_isUnit_hadamardFactor
    (κ : OpenPartialHomeomorph E E) {k : ℕ∞} (hκ : ContDiffOn ℝ k κ κ.source)
    (hκ' : ContDiffOn ℝ k κ.symm κ.target) (hk : 1 ≤ k) {x₀ : E} (hx₀ : x₀ ∈ κ.source) :
    ∃ N : Set E, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ κ.source ∧
      ∃ κ' : E ≃ₜ E, ContDiff ℝ k κ' ∧ (∀ y, IsUnit (fderiv ℝ κ' y)) ∧
        (∀ x y, IsUnit (hadamardFactor κ' y x)) ∧ EqOn κ' κ N := by
  have hk' : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hk).ne'
  obtain ⟨A, hA⟩ := κ.isInvertible_fderiv_of_contDiffOn hκ hκ' hk' hx₀
  obtain ⟨κ', hκ'c, hκ'κ, hκ'd⟩ := hκ.exists_homeomorph_eventuallyEq_nnNorm_fderiv_sub_le
    κ.open_source hk hx₀ hA.symm
  obtain ⟨N, hN, hNo, hx₀N⟩ := _root_.eventually_nhds_iff.1 (hκ'κ.and (κ.open_source.mem_nhds hx₀))
  refine ⟨N, hNo, hx₀N, fun y hy ↦ (hN y hy).2, κ', hκ'c, fun y ↦ ?_, fun x y ↦ ?_,
    fun y hy ↦ (hN y hy).1⟩
  · exact ContinuousLinearMap.isInvertible_iff_isUnit.1
      (ContinuousLinearMap.isInvertible_of_norm_sub_le_half A (hκ'd y))
  · refine ContinuousLinearMap.isInvertible_iff_isUnit.1
      (ContinuousLinearMap.isInvertible_of_norm_sub_le_half A ?_)
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact norm_hadamardFactor_sub_le (hκ'c.continuous_fderiv (by exact_mod_cast hk')).continuousOn
      fun z _ ↦ by exact_mod_cast hκ'd z
