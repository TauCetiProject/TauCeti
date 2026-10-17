/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
public import TauCeti.Analysis.ODE.EnergyEstimate.Global
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Density
public import TauCeti.Analysis.Sobolev.GraphStep.LocalCompactness
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Finite-dimensional kernel and closed range of `d/ds + A(s)`

Let `E` be a finite-dimensional real inner product space and `A : ℝ → E →L[ℝ] E` a `C¹` family of
symmetric operators with invertible limits `A(±∞)` and derivative tending to zero at both ends.
The trajectory operator

`D_A = d/ds + A(s) : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`) satisfies, for a bounded interval `V` and constants
`C₁`, `C₂`,

`‖u‖_{W^{1,2}} ≤ C₁ ‖D_A u‖_{L²} + C₂ ‖u‖_{L²(V)}`

for every Sobolev path `u`. For compactly supported `C¹` paths this is the global energy estimate
`TauCeti.exists_pos_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le`; it passes
to all Sobolev paths because smooth compactly supported paths are dense
(`TauCeti.WeakDerivStep.dense_setOf_contDiff_hasCompactSupport`) and both sides are continuous.
Restriction to the bounded interval is a compact operator
(`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL`), so Peetre's criterion
(`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
`ContinuousLinearMap.isClosed_range_of_compact_estimate`) shows that `D_A` has finite-dimensional
kernel and closed range. These are the kernel and range halves of the Fredholm property of `D_A`;
finite dimensionality of the cokernel is not proved here.

The coefficient enters the operator through its `L∞` class `B`, which exists because a continuous
family with limits at both ends is bounded; the statements take any such class.

## Main declarations

* `TauCeti.WeakDerivStep.exists_norm_le_mul_norm_trajectoryOperator_add_mul_norm_restrictBaseL`:
  the estimate with interior `L²` error on Sobolev paths.
* `TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator`: `ker D_A` is finite
  dimensional.
* `TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator`: `D_A` has closed range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (Peetre's criterion and first-order Fredholm operators).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- The squared energy estimate for a Sobolev path with a compactly supported `C¹`
representative `f`, deduced from the same estimate for `f`. The interior error is measured on
`(-(R + 1), R + 1)`. -/
private theorem norm_sq_le_of_ae_eq_of_contDiff {R C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ)
    (B : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hB : B =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : WeakDerivStep (volume : Measure ℝ) ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (hprev : prev _ u =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f)
    (hderiv : weakFDeriv _ u =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fderiv ℝ f)
    (hest : (∫ s, ‖deriv f s‖ ^ 2) + γ * (∫ s, ‖f s‖ ^ 2) ≤
      (∫ s, ‖deriv f s + A s (f s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖f s‖ ^ 2) :
    ‖u‖ ^ 2 ≤ (1 + γ⁻¹) * ‖trajectoryOperator B u‖ ^ 2 + (1 + γ⁻¹) * C *
      ‖restrictBaseL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
        (le_top : (⟨Ioo (-(R + 1)) (R + 1), isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤) u‖ ^ 2 := by
  let V : Opens ℝ := ⟨Ioo (-(R + 1)) (R + 1), isOpen_Ioo⟩
  -- The whole line carries the restriction of `volume` to `⊤`, which is `volume` itself.
  have hae : ae (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) = ae (volume : Measure ℝ) := by simp
  have hint : ∀ g : ℝ → ℝ, ∫ s, g s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ) = ∫ s, g s :=
    fun g ↦ by simp
  have hcu : HasCompactSupport (fun s ↦ ‖f s‖ ^ 2) :=
    hcf.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hfint : Integrable (fun s ↦ ‖f s‖ ^ 2) :=
    (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
  -- Express the four norms through the representative `f`.
  have hnprev : ‖prev _ u‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine (integral_congr_ae ?_).trans (hint _)
    filter_upwards [hprev] with s hs
    rw [hs]
  have hnderiv : ‖weakFDeriv _ u‖ ^ 2 = ∫ s, ‖deriv f s‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine (integral_congr_ae ?_).trans (hint _)
    filter_upwards [hderiv] with s hs
    rw [hs, ← fderiv_apply_one_eq_deriv, ← ContinuousLinearMap.toSpanSingletonLIE_symm_apply,
      LinearIsometryEquiv.norm_map]
  have hnT : ‖trajectoryOperator B u‖ ^ 2 = ∫ s, ‖deriv f s + A s (f s)‖ ^ 2 := by
    have hT := trajectoryOperator_apply_ae_eq_deriv_add B u hprev
      ((hf.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      fun s _ ↦ (hf.differentiable one_ne_zero).differentiableAt
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine (integral_congr_ae ?_).trans (hint _)
    filter_upwards [hT, hB] with s hs hBs
    rw [hs, hBs]
  have hnK : ∫ s in Icc (-R) R, ‖f s‖ ^ 2 ≤
      ‖restrictBaseL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
        (le_top : V ≤ ⊤) u‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    have hK : ∫ s, ‖restrictBaseL _ (le_top : V ≤ ⊤) u s‖ ^ 2 ∂volume.restrict V =
        ∫ s in V, ‖f s‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [restrictBaseL_apply_ae _ (le_top : V ≤ ⊤) u,
        ae_restrict_of_ae (hae ▸ hprev)] with s hs hps
      rw [hs, ContinuousLinearMap.id_apply, hps]
    rw [hK]
    refine setIntegral_mono_set hfint.integrableOn
      (ae_of_all _ fun s ↦ by positivity) (Eventually.of_forall fun s hs ↦ ?_)
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- Combine with the energy estimate for `f`, using `1 ≤ 1 + γ⁻¹` and `(1 + γ⁻¹) γ = γ + 1`.
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, hnprev, hnderiv, hnT]
  have hI0 : 0 ≤ ∫ s, ‖f s‖ ^ 2 := integral_nonneg fun s ↦ by positivity
  have hd0 : 0 ≤ ∫ s, ‖deriv f s‖ ^ 2 := integral_nonneg fun s ↦ by positivity
  have hcγ : (1 + γ⁻¹) * γ = γ + 1 := by field_simp
  have hc1 : 1 ≤ 1 + γ⁻¹ := le_add_of_nonneg_right (inv_nonneg.2 hγ.le)
  nlinarith [mul_le_mul_of_nonneg_left hnK (mul_nonneg (by positivity : 0 ≤ 1 + γ⁻¹) hC)]

/-- **The trajectory estimate on Sobolev paths.** For a `C¹` family of symmetric operators with
invertible limits at both ends and derivative tending to zero there, there are an open set `V`
with compact closure and constants `C₁`, `C₂` such that every `W^{1,2}` path `u` satisfies
`‖u‖ ≤ C₁ ‖D_A u‖ + C₂ ‖u‖_{L²(V)}`. -/
theorem exists_norm_le_mul_norm_trajectoryOperator_add_mul_norm_restrictBaseL
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (B : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hB : B =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ V : Opens ℝ, IsCompact (closure (V : Set ℝ)) ∧ ∃ C₁ C₂ : ℝ,
      ∀ u : WeakDerivStep (volume : Measure ℝ) ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ‖u‖ ≤ C₁ * ‖trajectoryOperator B u‖ +
        C₂ * ‖restrictBaseL
          (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          (le_top : V ≤ ⊤) u‖ := by
  obtain ⟨R, -, C, hC, hest⟩ :=
    exists_pos_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le hA hsym hα
      hminus hplus hbot htop hdbot hdtop
  let V : Opens ℝ := ⟨Ioo (-(R + 1)) (R + 1), isOpen_Ioo⟩
  let K := restrictBaseL (ContinuousLinearMap.id ℝ
    (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) (le_top : V ≤ ⊤)
  let T := trajectoryOperator (p := 2) B
  set c := 1 + (α ^ 2 / 2)⁻¹
  have hcpos : 0 < c := by positivity
  refine ⟨V, isCompact_Icc.closure_of_subset Ioo_subset_Icc_self, √c, √(c * C), fun u ↦ ?_⟩
  -- Restate the goal through the local names `T` and `K` for the two operators.
  change ‖u‖ ≤ √c * ‖T u‖ + √(c * C) * ‖K u‖
  -- The estimate is a closed condition on `u`, so it suffices to check it on a dense set.
  have hclosed : IsClosed {u | ‖u‖ ≤ √c * ‖T u‖ + √(c * C) * ‖K u‖} :=
    isClosed_le continuous_norm
      ((continuous_const.mul T.continuous.norm).add (continuous_const.mul K.continuous.norm))
  refine hclosed.closure_subset_iff.2 ?_ ((dense_setOf_contDiff_hasCompactSupport
    (mu := (volume : Measure ℝ)) (F := E) (p := 2) (by norm_num)).closure_eq ▸ mem_univ u)
  rintro u ⟨f, hf, hcf, hprev, hderiv⟩
  have hu2 : ‖u‖ ^ 2 ≤ c * ‖T u‖ ^ 2 + c * C * ‖K u‖ ^ 2 :=
    norm_sq_le_of_ae_eq_of_contDiff hC (by positivity) B hB u (hf.of_le (by simp)) hcf hprev
      hderiv (hest f (hf.of_le (by simp)) hcf)
  -- Pass from the squared estimate to the linear one, on real numbers standing for the norms.
  have key (n a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : n ^ 2 ≤ c * a ^ 2 + c * C * b ^ 2) :
      n ≤ √c * a + √(c * C) * b := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [add_sq, mul_pow, mul_pow, Real.sq_sqrt hcpos.le, Real.sq_sqrt (mul_nonneg hcpos.le hC)]
    nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg (c * C)))
      (mul_nonneg ha hb)]
  exact key _ _ _ (norm_nonneg _) (norm_nonneg _) hu2

/-- **Peetre's estimate for `d/ds + A(s)`.** Under the hypotheses of
`exists_norm_le_mul_norm_trajectoryOperator_add_mul_norm_restrictBaseL`, the trajectory operator
on `W^{1,2}(ℝ, E)` is bounded below up to a compact error. -/
theorem exists_isCompactOperator_norm_le_mul_norm_trajectoryOperator_add_norm
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (B : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hB : B =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ (V : Opens ℝ) (C : ℝ) (K : WeakDerivStep (volume : Measure ℝ) ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) →L[ℝ]
          Lp E 2 (volume.restrict (V : Set ℝ))),
      IsCompactOperator K ∧ ∀ u, ‖u‖ ≤ C * ‖trajectoryOperator B u‖ + ‖K u‖ := by
  obtain ⟨V, hV, C₁, C₂, hest⟩ :=
    exists_norm_le_mul_norm_trajectoryOperator_add_mul_norm_restrictBaseL hA hsym hα hminus
      hplus hbot htop hdbot hdtop B hB
  let base := ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
  refine ⟨V, C₁, C₂ • restrictBaseL base (le_top : V ≤ ⊤),
    (isCompactOperator_restrictBaseL base (by norm_num) hV (subset_univ _)).smul C₂,
    fun u ↦ (hest u).trans ?_⟩
  simp only [FunLike.coe_smul, Pi.smul_apply, norm_smul]
  gcongr
  exact Real.le_norm_self C₂

/-- **The kernel of `d/ds + A(s)` is finite dimensional.** For a `C¹` family of symmetric operators
on a finite-dimensional space with invertible limits at both ends and derivative tending to zero
there, the trajectory operator `W^{1,2}(ℝ, E) → L²(ℝ, E)` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (B : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hB : B =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (trajectoryOperator (p := 2) B).ker := by
  obtain ⟨V, C, K, hK, hest⟩ :=
    exists_isCompactOperator_norm_le_mul_norm_trajectoryOperator_add_norm hA hsym hα hminus
      hplus hbot htop hdbot hdtop B hB
  -- Peetre's criterion produces the kernel with the module structure coming from the normed
  -- group structure of the Sobolev space; `convert` identifies it with the submodule structure.
  convert (trajectoryOperator (p := 2) B).finiteDimensional_ker_of_compact_estimate hK hest

/-- **`d/ds + A(s)` has closed range.** Under the hypotheses of
`finiteDimensional_ker_trajectoryOperator`, the range of the trajectory operator
`W^{1,2}(ℝ, E) → L²(ℝ, E)` is closed. -/
theorem isClosed_range_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (B : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hB : B =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    IsClosed ((trajectoryOperator (p := 2) B).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
  obtain ⟨V, C, K, hK, hest⟩ :=
    exists_isCompactOperator_norm_le_mul_norm_trajectoryOperator_add_norm hA hsym hα hminus
      hplus hbot htop hdbot hdtop B hB
  exact (trajectoryOperator B).isClosed_range_of_compact_estimate hK hest

end TauCeti.WeakDerivStep
