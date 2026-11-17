/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# Exponentially weighted trajectory operators

Let `w : ℝ → ℝ` be a weight with derivative `w'`. Multiplication by `exp w` identifies the
weighted space `L²_w = {u | exp w • u ∈ L²}` with `L²`, and it conjugates the trajectory
operator `D_A u = u' + A u` to `D_{A - w'}`:

`exp w • (u' + A u) = (exp w • u)' + (A - w') (exp w • u)`.

So the trajectory operator on exponentially weighted spaces is the unweighted trajectory operator
of the shifted family `A - w' • id`, whose limits at `±∞` are `A± - δ± • id` when `w'` tends to
`δ±`. For the typical weight `w(s) = δ log (cosh s)`, which is `δ |s|` up to a bounded error, the
slopes are `δ± = ±δ`.

This file shows that a weight whose slopes stay *below the spectral gaps* of the limits changes
neither the kernel nor the cokernel. The condition is that `A± - (t δ±) • id` has a Lyapunov form
(`ContinuousLinearMap.HasLyapunovForm`) for every `t ∈ [0, 1]`: shifting the limits by any
fraction of the slopes keeps them hyperbolic, so no eigenvalue of `A±` has real part between `0`
and `δ±`. For a bounded-below weight the conclusions are:

* every square-integrable solution of `v' + A v = 0` lies in the weighted space: the
  square-integrable solutions of `v' + A v = 0` and of `u' + (A - w') u = 0` have the same initial
  values (`TauCeti.squareIntegrableSolutions_sub_smul_id`);
* the same holds for the formal adjoint
  (`TauCeti.squareIntegrableSolutions_neg_adjoint_add_smul_id`);
* square-integrable solutions decay pointwise like `exp (-w)`
  (`TauCeti.exists_forall_norm_le_mul_exp_neg`). For symmetric limits with
  `α ‖v‖ ≤ ‖A± v‖` this gives the decay `‖v s‖ ≤ C exp (-δ |s|)` at every rate `0 ≤ δ < α`
  (`TauCeti.exists_forall_norm_le_mul_exp_neg_mul_abs`).

For these statements the proof compares indices. Multiplying by `exp (w 0 - w)`, which is
bounded, sends weighted solutions to unweighted ones, so the kernel of `D_{A - w'}` is contained in
that of `D_A`; dually, the kernel of the formal adjoint of `D_A` is contained in that of
`D_{A - w'}`. The two operators
are joined through trajectory operators with hyperbolic limits, so they have the same index
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_of_forall_hasLyapunovForm`), and both
inclusions of finite-dimensional spaces are equalities. Pointwise decay then follows because a
square-integrable path whose derivative is bounded by a multiple of its norm is bounded
(`TauCeti.norm_sq_le_exp_mul_integral_norm_sq`).

**Weights beyond the spectral gap.** For symmetric limits the index of the weighted operator is
computed for every weight that is not exceptional, that is, whose slope `δ±` at `±∞` is not an
eigenvalue of `A±`. Since `A± - δ± • id` is then invertible, the Morse-index formula
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`
applies to `A - w' • id`, and the index is `n(A⁻, δ⁻) - n(A⁺, δ⁺)`, with `n(B, δ)` the number of
eigenvalues of `B` below `δ` counted with multiplicity
(`TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id`). So the index depends on the weight
only through the eigenvalues lying between its slopes and those of another weight: as the weight
forces more decay, each eigenvalue of `A⁺` above the old slope `δ⁺` and below the new one, and each
eigenvalue of `A⁻` below `δ⁻` and above the new slope, lowers the index by its multiplicity
(`TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_add_finrank_add_finrank`, with the
single crossings `index_trajectoryOperator_sub_smul_id_add_finrank_eigenspace_of_atTop` and
`index_trajectoryOperator_sub_smul_id_add_finrank_eigenspace_of_atBot`).

The limits may be degenerate. Along a trajectory between critical manifolds of a Morse–Bott
function the limits are Hessians with a kernel, the tangent spaces of the critical manifolds, and
the unweighted operator is not Fredholm. A small decay weight `δ log (cosh s)`, with `δ` below
the nonzero eigenvalues of the limits in absolute value, gives index
`n⁻(A⁻) - n⁻(A⁺) - dim ker A⁺`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_of_neg_of_pos`).

## Main results

* `TauCeti.squareIntegrableSolutions_sub_smul_id`,
  `TauCeti.squareIntegrableSolutions_neg_adjoint_add_smul_id`: weights below the spectral gaps
  change neither kernel nor cokernel.
* `TauCeti.exists_forall_norm_le_mul_exp_neg`, `TauCeti.exists_forall_norm_le_mul_exp_neg_mul_abs`:
  square-integrable solutions decay exponentially.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id`: the index for a non-exceptional
  weight.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_add_finrank_add_finrank`: the index
  drops by the multiplicities of the eigenvalues crossed by the slopes of the weight.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_of_neg_of_pos`: the index for a small
  decay weight at degenerate limits.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (exponentially weighted spaces
  and the dependence of the index on the weight).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (exponential decay of solutions of
  the linearized trajectory equation).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

section Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {Aminus Aplus : E →L[ℝ] E} {w w' : ℝ → ℝ} {δminus δplus : ℝ}

/-- The kernel and cokernel statements below, proved together by comparing indices. -/
private theorem squareIntegrableSolutions_sub_smul_id_and_neg_adjoint (hA : Continuous A)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hbdd : BddBelow (range w))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aminus - (t * δminus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aplus - (t * δplus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm) :
    squareIntegrableSolutions (fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) =
        squareIntegrableSolutions A ∧
      squareIntegrableSolutions
          (fun s ↦ -ContinuousLinearMap.adjoint (A s) + w' s • ContinuousLinearMap.id ℝ E) =
        squareIntegrableSolutions (fun s ↦ -ContinuousLinearMap.adjoint (A s)) := by
  set I := ContinuousLinearMap.id ℝ E
  set B : ℝ → E →L[ℝ] E := fun s ↦ A s - w' s • I
  set C : ℝ → E →L[ℝ] E := fun s ↦ -ContinuousLinearMap.adjoint (A s)
  set C' : ℝ → E →L[ℝ] E := fun s ↦ -ContinuousLinearMap.adjoint (A s) + w' s • I
  have hB : Continuous B := hA.sub (hw'.smul continuous_const)
  have hC : Continuous C :=
    ((ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E)).continuous.comp hA).neg
  have hC' : Continuous C' := hC.add (hw'.smul continuous_const)
  have hBbot : Tendsto B atBot (𝓝 (Aminus - δminus • I)) := hbot.sub (hw'bot.smul_const I)
  have hBtop : Tendsto B atTop (𝓝 (Aplus - δplus • I)) := htop.sub (hw'top.smul_const I)
  -- The limits of `A` and of `B` are the endpoints of the segments in the hypotheses.
  have hAm : Aminus.HasLyapunovForm := by simpa using hminus 0 ⟨le_rfl, zero_le_one⟩
  have hAp : Aplus.HasLyapunovForm := by simpa using hplus 0 ⟨le_rfl, zero_le_one⟩
  have hBm : (Aminus - δminus • I).HasLyapunovForm := by simpa using hminus 1 ⟨zero_le_one, le_rfl⟩
  have hBp : (Aplus - δplus • I).HasLyapunovForm := by simpa using hplus 1 ⟨zero_le_one, le_rfl⟩
  -- `L∞` classes of the coefficients and of their pointwise adjoints.
  obtain ⟨MA, hMA⟩ := exists_forall_norm_le_of_tendsto hA hbot htop
  obtain ⟨MB, hMB⟩ := exists_forall_norm_le_of_tendsto hB hBbot hBtop
  obtain ⟨AL, hAL⟩ : ∃ AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A :=
    ⟨_, MemLp.coeFn_toLp (memLp_top_of_bound hA.aestronglyMeasurable MA (.of_forall hMA))⟩
  obtain ⟨BL, hBL⟩ : ∃ BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B :=
    ⟨_, MemLp.coeFn_toLp (memLp_top_of_bound hB.aestronglyMeasurable MB (.of_forall hMB))⟩
  obtain ⟨AL', hAL'⟩ := WeakDerivStep.exists_ae_eq_adjoint AL hAL
  obtain ⟨BL', hBL'⟩ := WeakDerivStep.exists_ae_eq_adjoint BL hBL
  have hnegAL' : -AL' =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] C := by
    filter_upwards [Lp.coeFn_neg AL', hAL'] with s hs hs'
    rw [hs, Pi.neg_apply, hs']
  have hnegBL' : -BL' =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] C' := by
    filter_upwards [Lp.coeFn_neg BL', hBL'] with s hs hs'
    rw [hs, Pi.neg_apply, hs']
    simp only [B, C', I, map_sub, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.adjoint_id,
      starRingEnd_apply, star_trivial]
    abel
  -- `D_A` and `D_B` are joined through operators with hyperbolic limits, so their indices agree.
  have hindex := WeakDerivStep.index_trajectoryOperator_eq_of_forall_hasLyapunovForm hA hB hbot
    htop hBbot hBtop AL BL hAL hBL
    (fun t ht ↦ by convert hminus t ht using 1; module)
    (fun t ht ↦ by convert hplus t ht using 1; module)
  -- Each index is the dimension of the kernel minus that of the formal adjoint's kernel.
  have i₁ := WeakDerivStep.index_trajectoryOperator_of_hasLyapunovForm hA hAm hAp hbot htop AL AL'
    hAL hAL'
  have i₂ := WeakDerivStep.index_trajectoryOperator_of_hasLyapunovForm hB hBm hBp hBbot hBtop BL
    BL' hBL hBL'
  have k₁ := WeakDerivStep.finrank_ker_trajectoryOperator hA AL hAL
  have k₂ := WeakDerivStep.finrank_ker_trajectoryOperator hB BL hBL
  have k₃ := WeakDerivStep.finrank_ker_trajectoryOperator hC (-AL') hnegAL'
  have k₄ := WeakDerivStep.finrank_ker_trajectoryOperator hC' (-BL') hnegBL'
  -- Weighting gives one inclusion for the kernels and the opposite one for the cokernels.
  have h₁ : squareIntegrableSolutions B ≤ squareIntegrableSolutions A :=
    squareIntegrableSolutions_sub_smul_id_le hw hbdd
  have h₂ : squareIntegrableSolutions C ≤ squareIntegrableSolutions C' := by
    simpa [C', C, I] using squareIntegrableSolutions_sub_smul_id_le (A := C') hw hbdd
  have f₁ := Submodule.finrank_mono h₁
  have f₂ := Submodule.finrank_mono h₂
  exact ⟨Submodule.eq_of_le_of_finrank_eq h₁ (by omega),
    (Submodule.eq_of_le_of_finrank_eq h₂ (by omega)).symm⟩

/-- **Weights below the spectral gap do not change the kernel.** Let `A` be a continuous family
of operators on a finite-dimensional real inner product space with limits `A±` at `±∞`, and let
`w` be a bounded-below weight whose continuous derivative `w'` tends to `δ±` at `±∞`. If
`A± - (t δ±) • id` has a Lyapunov form for every `t ∈ [0, 1]`, then `v' + A v = 0` and
`u' + (A - w') u = 0` have the same initial values of square-integrable solutions. Since
`u = exp (w - w 0) • v` relates their solutions, every square-integrable solution `v` of
`v' + A v = 0` has `exp w • v` square integrable: the kernel of `D_A` on the weighted space
`{u | exp w • u ∈ W^{1,2}}` is its kernel on `W^{1,2}`. -/
theorem squareIntegrableSolutions_sub_smul_id (hA : Continuous A)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hbdd : BddBelow (range w))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aminus - (t * δminus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aplus - (t * δplus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm) :
    squareIntegrableSolutions (fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) =
      squareIntegrableSolutions A :=
  (squareIntegrableSolutions_sub_smul_id_and_neg_adjoint hA hbot htop hw hw' hbdd hw'bot hw'top
    hminus hplus).1

/-- **Weights below the spectral gap do not change the cokernel.** Under the hypotheses of
`TauCeti.squareIntegrableSolutions_sub_smul_id`, the formal adjoint equations
`v' = A† v` and `z' = (A - w')† z` have the same initial values of square-integrable solutions.
These solutions model the cokernels of `D_A` and `D_{A - w'}`, so the cokernel of `D_A` on the
weighted spaces is its cokernel on the unweighted spaces. -/
theorem squareIntegrableSolutions_neg_adjoint_add_smul_id (hA : Continuous A)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hbdd : BddBelow (range w))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aminus - (t * δminus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aplus - (t * δplus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm) :
    squareIntegrableSolutions
        (fun s ↦ -ContinuousLinearMap.adjoint (A s) + w' s • ContinuousLinearMap.id ℝ E) =
      squareIntegrableSolutions (fun s ↦ -ContinuousLinearMap.adjoint (A s)) :=
  (squareIntegrableSolutions_sub_smul_id_and_neg_adjoint hA hbot htop hw hw' hbdd hw'bot hw'top
    hminus hplus).2

/-- **Square-integrable solutions decay like the inverse weight.** Under the hypotheses of
`TauCeti.squareIntegrableSolutions_sub_smul_id`, every square-integrable solution of
`v' + A v = 0` satisfies `‖v s‖ ≤ C exp (-w s)` for some constant `C`. -/
theorem exists_forall_norm_le_mul_exp_neg (hA : Continuous A)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hbdd : BddBelow (range w))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aminus - (t * δminus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aplus - (t * δplus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    {v : ℝ → E} (hv : ∀ s, HasDerivAt v (-A s (v s)) s) (hv2 : MemLp v 2) :
    ∃ C, ∀ s, ‖v s‖ ≤ C * Real.exp (-w s) := by
  set I := ContinuousLinearMap.id ℝ E
  set B : ℝ → E →L[ℝ] E := fun s ↦ A s - w' s • I
  have hB : Continuous B := hA.sub (hw'.smul continuous_const)
  -- The weighted equation has a square-integrable solution `u` with `u 0 = v 0`.
  have hx : v 0 ∈ squareIntegrableSolutions B := by
    rw [squareIntegrableSolutions_sub_smul_id hA hbot htop hw hw' hbdd hw'bot hw'top hminus hplus]
    exact mem_squareIntegrableSolutions.2 ⟨v, rfl, hv, hv2⟩
  obtain ⟨u, hu0, hu, hu2⟩ := mem_squareIntegrableSolutions.1 hx
  -- By uniqueness, `u = exp (w - w 0) • v`.
  have hvw (s : ℝ) : HasDerivAt (fun s ↦ Real.exp (w s - w 0) • v s)
      (-B s (Real.exp (w s - w 0) • v s)) s :=
    hasDerivAt_exp_smul_sub_smul_id ((hw s).sub_const (w 0)) (hv s)
  have heq : u = fun s ↦ Real.exp (w s - w 0) • v s :=
    hB.neg.eq_of_hasDerivAt_clm_apply (fun s ↦ by simpa using hu s) (fun s ↦ by simpa using hvw s)
      (t₀ := 0) (by simp [hu0])
  -- The weighted solution is bounded, since `B` is.
  obtain ⟨K, hK⟩ := exists_forall_norm_le_of_tendsto hB (hbot.sub (hw'bot.smul_const I))
    (htop.sub (hw'top.smul_const I))
  have hK₀ : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hbound := norm_sq_le_exp_mul_integral_norm_sq hK₀ hu
    (fun s ↦ by
      rw [norm_neg]
      exact ((B s).le_opNorm (u s)).trans (by gcongr; exact hK s)) hu2
  refine ⟨Real.exp (w 0) * √(Real.exp (2 * K) * ∫ t, ‖u t‖ ^ 2), fun s ↦ ?_⟩
  have hus : ‖u s‖ ≤ √(Real.exp (2 * K) * ∫ t, ‖u t‖ ^ 2) := by
    simpa using Real.abs_le_sqrt (hbound s)
  have hnorm : ‖u s‖ = Real.exp (w s - w 0) * ‖v s‖ := by
    rw [heq, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hv' : ‖v s‖ = Real.exp (w 0) * Real.exp (-w s) * ‖u s‖ := by
    rw [hnorm, Real.exp_sub, Real.exp_neg]
    field_simp
  rw [hv', mul_right_comm]
  gcongr

/-- **Exponential decay below the spectral gap for symmetric limits.** Let `A` be a continuous
family of operators on a finite-dimensional real inner product space with symmetric limits `A±`
at `±∞` satisfying `α ‖v‖ ≤ ‖A± v‖`. For every `0 ≤ δ < α`, each square-integrable solution of
`v' + A v = 0` satisfies `‖v s‖ ≤ C exp (-δ |s|)` for some constant `C`. -/
theorem exists_forall_norm_le_mul_exp_neg_mul_abs (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    {α : ℝ} (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδα : δ < α)
    {v : ℝ → E} (hv : ∀ s, HasDerivAt v (-A s (v s)) s) (hv2 : MemLp v 2) :
    ∃ C, ∀ s, ‖v s‖ ≤ C * Real.exp (-(δ * |s|)) := by
  -- Use the weight `w s = δ log (cosh s)`, with slope `δ tanh s` and `w s ≥ δ (|s| - log 2)`.
  have hw (s : ℝ) : HasDerivAt (fun s ↦ δ * Real.log (Real.cosh s)) (δ * Real.tanh s) s :=
    (Real.hasDerivAt_log_cosh s).const_mul δ
  have hbdd : BddBelow (range fun s ↦ δ * Real.log (Real.cosh s)) :=
    ⟨0, by
      rintro _ ⟨s, rfl⟩
      exact mul_nonneg hδ (Real.log_nonneg (Real.one_le_cosh s))⟩
  have hgap {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) (hTα : ∀ v, α * ‖v‖ ≤ ‖T v‖)
      {σ : ℝ} (hσ : |σ| = 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (T - (t * (δ * σ)) • ContinuousLinearMap.id ℝ E).HasLyapunovForm := by
    refine ContinuousLinearMap.hasLyapunovForm_sub_smul_id_of_isSymmetric hT hTα ?_
    rw [abs_mul, abs_mul, hσ, abs_of_nonneg ht.1, abs_of_nonneg hδ, mul_one]
    nlinarith [ht.2]
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_exp_neg hA hbot htop hw
    (continuous_const.mul Real.continuous_tanh) hbdd
    (Real.tendsto_tanh_atBot.const_mul δ) (Real.tendsto_tanh_atTop.const_mul δ)
    (hgap hsymminus hminus (σ := -1) (by simp)) (hgap hsymplus hplus (σ := 1) (by simp)) hv hv2
  have hC₀ : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC 0)) (Real.exp_pos _)
  refine ⟨C * Real.exp (δ * Real.log 2), fun s ↦ (hC s).trans ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_left (Real.abs_sub_log_two_le_log_cosh s) hδ]

end Hyperbolic

end TauCeti

namespace TauCeti.WeakDerivStep

/-! ### The index for arbitrary weights and the crossing of exceptional weights -/

section Index

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {Aminus Aplus : E →L[ℝ] E}

/-- **The index of an exponentially weighted trajectory operator.** Let `A` be a continuous
family of operators on a finite-dimensional real inner product space with symmetric limits `A±`
at `±∞`, and let `w'` be a continuous function with limits `δ±` at `±∞`, the slope of a weight
`w`. Multiplication by `exp w` conjugates the trajectory operator `u ↦ u' + A u` on the weighted
spaces `{u | exp w • u ∈ W^{1,2}}` and `{u | exp w • u ∈ L²}` to the trajectory operator of
`A - w' • id` on the unweighted spaces. If the weight is not exceptional, that is, `δ±` is not an
eigenvalue of `A±`, then the index of this operator is `n(A⁻, δ⁻) - n(A⁺, δ⁺)`, where
`n(B, δ)` is the number of eigenvalues of `B` below `δ`, counted with multiplicity.

Nothing is assumed about the spectral gaps of `A±`: the limits may have zero or any other
eigenvalue, as long as it differs from the slope of the weight at that end. -/
theorem index_trajectoryOperator_sub_smul_id (hA : Continuous A) {w' : ℝ → ℝ}
    (hw' : Continuous w') (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {δminus δplus : ℝ}
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio δminus)) :
          ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δplus)) := by
  set I := ContinuousLinearMap.id ℝ E
  -- Away from its eigenvalues, `T - δ • id` is injective, hence bounded below.
  have hbelow {T : E →L[ℝ] E} {δ : ℝ} (h : ¬Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) δ) :
      ∃ α > 0, ∀ v, α * ‖v‖ ≤ ‖(T - δ • I) v‖ := by
    refine antilipschitzWith_iff_exists_mul_le_norm.1
      ((((T - δ • I : E →L[ℝ] E) : E →ₗ[ℝ] E).injective_iff_antilipschitz.1 ?_).imp
        fun _ hK ↦ hK.2)
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have hv' : v ∈ Module.End.eigenspace (T : E →ₗ[ℝ] E) δ := by
      rw [Module.End.mem_eigenspace_iff]
      simpa [I, sub_eq_zero] using hv
    rwa [not_not.mp (mt Module.End.hasEigenvalue_iff.2 h)] at hv'
  have hsym {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) (δ : ℝ) :
      ((T - δ • I : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    simpa [I] using hT.sub (LinearMap.IsSymmetric.id.smul (conj_trivial δ))
  -- Over `ℝ` the coercion `RCLike.ofReal` of the shift lemma is the identity.
  have hshift (T : E →L[ℝ] E) (δ : ℝ) :
      Module.End.pointSpectralSubspace ((T - δ • I : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) =
        Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio δ) := by
    rw [show ((T - δ • I : E →L[ℝ] E) : E →ₗ[ℝ] E) = (T : E →ₗ[ℝ] E) - δ • LinearMap.id by
      ext; simp [I]]
    refine (Module.End.pointSpectralSubspace_sub_smul_id (𝕜 := ℝ) δ).trans ?_
    congr 1
    ext μ
    simp
  obtain ⟨αm, hαm, hm⟩ := hbelow hδminus
  obtain ⟨αp, hαp, hp⟩ := hbelow hδplus
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
      (hA.sub (hw'.smul continuous_const)) (hsym hsymminus δminus) (hsym hsymplus δplus)
      (lt_min hαm hαp)
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hm v))
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hp v))
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) BL hBL,
    hshift, hshift]

/-- **The index jumps at exceptional weights.** Compare two weights whose slopes tend to
`δ±₁` and `δ±₂`, with `δ⁻₂ ≤ δ⁻₁` and `δ⁺₁ ≤ δ⁺₂`, so that the second forces at least as much
decay as the first at both ends, neither of them exceptional. Then the index of the more strongly
weighted trajectory operator is smaller by the number of eigenvalues of `A⁻` in `[δ⁻₂, δ⁻₁)` and
of `A⁺` in `[δ⁺₁, δ⁺₂)`, counted with multiplicity: these are the eigenvalues crossed by the
slopes as the weight increases. -/
theorem index_trajectoryOperator_sub_smul_id_add_finrank_add_finrank (hA : Continuous A)
    {w₁' w₂' : ℝ → ℝ} (hw₁' : Continuous w₁') (hw₂' : Continuous w₂')
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {δminus₁ δplus₁ δminus₂ δplus₂ : ℝ}
    (hw₁'bot : Tendsto w₁' atBot (𝓝 δminus₁)) (hw₁'top : Tendsto w₁' atTop (𝓝 δplus₁))
    (hw₂'bot : Tendsto w₂' atBot (𝓝 δminus₂)) (hw₂'top : Tendsto w₂' atTop (𝓝 δplus₂))
    (hminus : δminus₂ ≤ δminus₁) (hplus : δplus₁ ≤ δplus₂)
    (hδminus₁ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus₁)
    (hδplus₁ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus₁)
    (hδminus₂ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus₂)
    (hδplus₂ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus₂)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₁' s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₂' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Ico δminus₂ δminus₁)) +
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ico δplus₁ δplus₂)) =
      (trajectoryOperator (p := 2) BL₁).index := by
  rw [index_trajectoryOperator_sub_smul_id hA hw₁' hsymminus hsymplus hbot htop hw₁'bot hw₁'top
      hδminus₁ hδplus₁ BL₁ hBL₁,
    index_trajectoryOperator_sub_smul_id hA hw₂' hsymminus hsymplus hbot htop hw₂'bot hw₂'top
      hδminus₂ hδplus₂ BL₂ hBL₂,
    ← Iio_union_Ico_eq_Iio hminus, ← Iio_union_Ico_eq_Iio hplus,
    Module.End.finrank_pointSpectralSubspace_union
      ((Iio_disjoint_Ici le_rfl).mono_right Ico_subset_Ici_self),
    Module.End.finrank_pointSpectralSubspace_union
      ((Iio_disjoint_Ici le_rfl).mono_right Ico_subset_Ici_self)]
  push_cast
  ring

/-- **Crossing one exceptional weight at `+∞`.** If two weights have the same slope at `-∞`,
and their slopes `δ⁺₁ < δ⁺₂` at `+∞` enclose exactly one eigenvalue `μ` of `A⁺`, then the index of
the more strongly weighted trajectory operator is smaller by the multiplicity of `μ`. -/
theorem index_trajectoryOperator_sub_smul_id_add_finrank_eigenspace_of_atTop (hA : Continuous A)
    {w₁' w₂' : ℝ → ℝ} (hw₁' : Continuous w₁') (hw₂' : Continuous w₂')
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {δminus δplus₁ δplus₂ μ : ℝ}
    (hw₁'bot : Tendsto w₁' atBot (𝓝 δminus)) (hw₁'top : Tendsto w₁' atTop (𝓝 δplus₁))
    (hw₂'bot : Tendsto w₂' atBot (𝓝 δminus)) (hw₂'top : Tendsto w₂' atTop (𝓝 δplus₂))
    (hμ : μ ∈ Ioo δplus₁ δplus₂)
    (hcross : ∀ ν ∈ Icc δplus₁ δplus₂, Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) ν → ν = μ)
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₁' s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₂' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ (Module.End.eigenspace (Aplus : E →ₗ[ℝ] E) μ) =
      (trajectoryOperator (p := 2) BL₁).index := by
  have hne (ν : ℝ) (hν : ν ∈ Icc δplus₁ δplus₂) (hνμ : ν ≠ μ) :
      ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) ν :=
    fun h ↦ hνμ (hcross ν hν h)
  rw [← index_trajectoryOperator_sub_smul_id_add_finrank_add_finrank hA hw₁' hw₂' hsymminus
      hsymplus hbot htop hw₁'bot hw₁'top hw₂'bot hw₂'top le_rfl (hμ.1.trans hμ.2).le hδminus
      (hne _ (left_mem_Icc.2 (hμ.1.trans hμ.2).le) hμ.1.ne) hδminus
      (hne _ (right_mem_Icc.2 (hμ.1.trans hμ.2).le) hμ.2.ne') BL₁ BL₂ hBL₁ hBL₂,
    Ico_self, Module.End.pointSpectralSubspace_empty, finrank_bot,
    Module.End.pointSpectralSubspace_eq_eigenspace (Ioo_subset_Ico_self hμ)
      fun ν hν ↦ hcross ν (Ico_subset_Icc_self hν)]
  simp [RCLike.ofReal_real_eq_id]

/-- **Crossing one exceptional weight at `-∞`.** If two weights have the same slope at `+∞`,
and their slopes `δ⁻₂ < δ⁻₁` at `-∞` enclose exactly one eigenvalue `μ` of `A⁻`, then the index of
the more strongly weighted trajectory operator is smaller by the multiplicity of `μ`. -/
theorem index_trajectoryOperator_sub_smul_id_add_finrank_eigenspace_of_atBot (hA : Continuous A)
    {w₁' w₂' : ℝ → ℝ} (hw₁' : Continuous w₁') (hw₂' : Continuous w₂')
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {δminus₁ δminus₂ δplus μ : ℝ}
    (hw₁'bot : Tendsto w₁' atBot (𝓝 δminus₁)) (hw₁'top : Tendsto w₁' atTop (𝓝 δplus))
    (hw₂'bot : Tendsto w₂' atBot (𝓝 δminus₂)) (hw₂'top : Tendsto w₂' atTop (𝓝 δplus))
    (hμ : μ ∈ Ioo δminus₂ δminus₁)
    (hcross : ∀ ν ∈ Icc δminus₂ δminus₁, Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) ν → ν = μ)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₁' s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w₂' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ (Module.End.eigenspace (Aminus : E →ₗ[ℝ] E) μ) =
      (trajectoryOperator (p := 2) BL₁).index := by
  have hne (ν : ℝ) (hν : ν ∈ Icc δminus₂ δminus₁) (hνμ : ν ≠ μ) :
      ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) ν :=
    fun h ↦ hνμ (hcross ν hν h)
  rw [← index_trajectoryOperator_sub_smul_id_add_finrank_add_finrank hA hw₁' hw₂' hsymminus
      hsymplus hbot htop hw₁'bot hw₁'top hw₂'bot hw₂'top (hμ.1.trans hμ.2).le le_rfl
      (hne _ (right_mem_Icc.2 (hμ.1.trans hμ.2).le) hμ.2.ne') hδplus
      (hne _ (left_mem_Icc.2 (hμ.1.trans hμ.2).le) hμ.1.ne) hδplus BL₁ BL₂ hBL₁ hBL₂,
    Ico_self, Module.End.pointSpectralSubspace_empty, finrank_bot,
    Module.End.pointSpectralSubspace_eq_eigenspace (Ioo_subset_Ico_self hμ)
      fun ν hν ↦ hcross ν (Ico_subset_Icc_self hν)]
  simp [RCLike.ofReal_real_eq_id]

/-- **The decay-weighted index at degenerate limits.** Let the limits `A±` be symmetric, possibly
with a kernel, as for the linearized operator along a trajectory between critical manifolds of a
Morse–Bott function. Take a weight whose slope tends to `-δ` at `-∞` and to `δ` at `+∞`, such as
`δ log (cosh s)`, for some `δ > 0` smaller than every nonzero eigenvalue of `A±` in absolute value
on the relevant side: `A⁻` has no eigenvalue in `[-δ, 0)` and `A⁺` none in `(0, δ]`. Then the
weighted trajectory operator has index `n⁻(A⁻) - (n⁻(A⁺) + dim ker A⁺)`: the decay weight
counts the kernel of `A⁺` with the negative eigenvalues, and not that of `A⁻`. -/
theorem index_trajectoryOperator_sub_smul_id_of_neg_of_pos (hA : Continuous A) {w' : ℝ → ℝ}
    (hw' : Continuous w') (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {δ : ℝ} (hδ : 0 < δ)
    (hw'bot : Tendsto w' atBot (𝓝 (-δ))) (hw'top : Tendsto w' atTop (𝓝 δ))
    (hgapminus : ∀ μ ∈ Ico (-δ) 0, ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) μ)
    (hgapplus : ∀ μ ∈ Ioc 0 δ, ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) μ)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iic 0)) := by
  have hminus : Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio (-δ)) =
      Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0) := by
    rw [← Iio_union_Ico_eq_Iio (neg_nonpos.2 hδ.le), Module.End.pointSpectralSubspace_union,
      Module.End.pointSpectralSubspace_eq_bot_iff.2 hgapminus, sup_bot_eq]
  have hplus : Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δ) =
      Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iic 0) := by
    rw [← Iic_union_Ioo_eq_Iio hδ, Module.End.pointSpectralSubspace_union,
      Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hgapplus μ (Ioo_subset_Ioc_self hμ),
      sup_bot_eq]
  rw [index_trajectoryOperator_sub_smul_id hA hw' hsymminus hsymplus hbot htop hw'bot hw'top
      (hgapminus _ ⟨le_rfl, neg_neg_iff_pos.2 hδ⟩) (hgapplus _ ⟨hδ, le_rfl⟩) BL hBL,
    hminus, hplus]

end Index

end TauCeti.WeakDerivStep
