/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.ODE.EnergyEstimate.Weighted
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# The trajectory operator on exponentially weighted spaces

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner
product space, and `w : ℝ → ℝ` a `C¹` *weight* whose derivative `w'` tends to `δ±` at `±∞`. The
weighted spaces `L²_w` and `W^{1,2}_w` consist of the paths `u` with `e^w u` in `L²` and
`W^{1,2}`. Multiplication by `e^w` identifies them with `L²` and `W^{1,2}`, and since
`e^w (u' + A u) = (e^w u)' + (A - w') (e^w u)`, it conjugates `D_A u = u' + A u` on the weighted
spaces to the trajectory operator `D_{A - w'}` on the unweighted ones. This file studies `D_A` on
weighted spaces through this conjugate, the trajectory operator with coefficient
`s ↦ A s - w' s • id`.

Its kernel consists of the solutions of `u' + A u = 0` that lie in `L²_w`
(`TauCeti.squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions`); these are
recorded by `TauCeti.weightedSquareIntegrableSolutions A w`. Its limits are `A± - δ±`, so the
weights move the limiting spectra. For symmetric limits, `D_A` is Fredholm on the weighted spaces
exactly when neither `δ±` is an eigenvalue of `A±`, and its index is then the number of
eigenvalues of `A⁻` below `δ⁻` minus the number of eigenvalues of `A⁺` below `δ⁺`, counted with
multiplicity. A weight can therefore make `D_A` Fredholm when a limit is degenerate, as for
Morse–Bott trajectories: for `A = 0` and a weight with `δ⁻ < 0 < δ⁺`, the index is `-dim E`.

When the weight is bounded below and the limits keep Lyapunov forms along `A± - t δ±` for
`t ∈ [0, 1]`, every square-integrable solution of `u' + A u = 0` already lies in `L²_w`
(`TauCeti.weightedSquareIntegrableSolutions_eq_squareIntegrableSolutions`); this restates
`TauCeti.squareIntegrableSolutions_sub_smul_id` in terms of weighted solutions. For symmetric limits
with spectral gap `α` this says that square-integrable solutions decay exponentially at every rate
`δ < α`: `e^{δ |s|} u ∈ L²` (`TauCeti.memLp_exp_mul_abs_smul_of_hasDerivAt`).

## Main declarations

* `TauCeti.weightedSquareIntegrableSolutions A w`: the initial values of the solutions of
  `u' + A u = 0` with `e^w u` square integrable.
* `TauCeti.squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions`:
  multiplication by `e^w` identifies them with the square-integrable solutions of
  `v' + (A - w') v = 0`.
* `TauCeti.weightedSquareIntegrableSolutions_le_of_le_add`: a larger weight gives fewer
  solutions.
* `TauCeti.WeakDerivStep.finrank_ker_trajectoryOperator_sub_smul_id`: the kernel of the weighted
  operator.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank`: its index,
  for hyperbolic shifted limits, as the difference of the dimensions of the weighted solution
  spaces of `u' + A u = 0` and of the adjoint equation `u' - A† u = 0` with weight `-w`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`: for symmetric limits,
  the weighted operator is Fredholm exactly when `δ±` is not an eigenvalue of `A±`.
* `index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`, in
  `TauCeti.WeakDerivStep`: its index counts the eigenvalues of `A±` below `δ±`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_neg_smul_id`: with decaying weights, `d/ds` is
  Fredholm of index `-dim E`.
* `TauCeti.weightedSquareIntegrableSolutions_eq_squareIntegrableSolutions`: weights below the
  spectral gaps do not change the solutions.
* `TauCeti.memLp_exp_mul_abs_smul_of_hasDerivAt`: square-integrable solutions decay exponentially
  at every rate below the spectral gap of symmetric limits.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Sc. Norm. Sup. Pisa **12** (1985), 409–447 (Fredholm theory in exponentially weighted
  spaces, with index jumps at the weights in the limiting spectra).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator
  and exponential decay of its kernel).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.1 and Chapter 10 (weighted Sobolev spaces and
  exponential decay).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter Real
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

section Solutions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {A : ℝ → F →L[ℝ] F}

/-- The initial values at time `0` of the solutions `u : ℝ → F` of `u' + A(s) u = 0` on the whole
line for which `e^{w(s)} u(s)` is square integrable. For a weight `w` with derivative `w'`, this is
a model of the kernel of the trajectory operator `D_A` on `e^w`-weighted spaces
(`TauCeti.squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions`). -/
def weightedSquareIntegrableSolutions (A : ℝ → F →L[ℝ] F) (w : ℝ → ℝ) : Submodule ℝ F where
  carrier := {x | ∃ u : ℝ → F, u 0 = x ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
    MemLp (fun s ↦ exp (w s) • u s) 2}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, rfl, hu, hu2⟩ ⟨v, rfl, hv, hv2⟩
    refine ⟨u + v, rfl, fun s ↦ by simpa [add_comm] using (hu s).add (hv s), ?_⟩
    convert hu2.add hv2 using 1
    ext s
    simp [smul_add]
  smul_mem' := by
    rintro c _ ⟨u, rfl, hu, hu2⟩
    refine ⟨c • u, rfl, fun s ↦ by simpa using (hu s).const_smul c, ?_⟩
    convert hu2.const_smul c using 1
    ext s
    exact smul_comm _ _ _

/-- A vector lies in `TauCeti.weightedSquareIntegrableSolutions A w` when it is the value at time
`0` of a solution `u` of `u' + A u = 0` with `e^w u` square integrable. -/
theorem mem_weightedSquareIntegrableSolutions {w : ℝ → ℝ} {x : F} :
    x ∈ weightedSquareIntegrableSolutions A w ↔
      ∃ u : ℝ → F, u 0 = x ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
        MemLp (fun s ↦ exp (w s) • u s) 2 :=
  Iff.rfl

/-- With the zero weight, the weighted solutions are the square-integrable solutions. -/
@[simp]
theorem weightedSquareIntegrableSolutions_zero :
    weightedSquareIntegrableSolutions A 0 = squareIntegrableSolutions A := by
  ext x
  simp [mem_weightedSquareIntegrableSolutions, mem_squareIntegrableSolutions]

/-- **A larger weight gives fewer solutions.** If `w₁ ≤ w₂ + C`, a solution with `e^{w₂} u`
square integrable also has `e^{w₁} u` square integrable. -/
theorem weightedSquareIntegrableSolutions_le_of_le_add {w₁ w₂ : ℝ → ℝ} (hw₁ : Measurable w₁)
    {C : ℝ} (h : ∀ s, w₁ s ≤ w₂ s + C) :
    weightedSquareIntegrableSolutions A w₂ ≤ weightedSquareIntegrableSolutions A w₁ := by
  rintro _ ⟨u, rfl, hu, hu2⟩
  have hc : Continuous u := continuous_iff_continuousAt.2 fun s ↦ (hu s).continuousAt
  refine ⟨u, rfl, hu, (hu2.const_smul (exp C)).of_le
    (hw₁.exp.aestronglyMeasurable.smul hc.aestronglyMeasurable) (.of_forall fun s ↦ ?_)⟩
  simp only [Pi.smul_apply, norm_smul, norm_eq_abs, abs_of_pos (exp_pos _)]
  rw [← mul_assoc, ← exp_add]
  gcongr
  linarith [h s]

/-- For a weight bounded below, every weighted solution is square integrable. -/
theorem weightedSquareIntegrableSolutions_le_squareIntegrableSolutions {w : ℝ → ℝ}
    (hw : BddBelow (range w)) :
    weightedSquareIntegrableSolutions A w ≤ squareIntegrableSolutions A := by
  obtain ⟨c, hc⟩ := hw
  rw [← weightedSquareIntegrableSolutions_zero]
  exact weightedSquareIntegrableSolutions_le_of_le_add measurable_const (C := -c)
    fun s ↦ by simpa using hc (mem_range_self s)

/-- For a weight bounded above, every square-integrable solution is a weighted solution. -/
theorem squareIntegrableSolutions_le_weightedSquareIntegrableSolutions {w : ℝ → ℝ}
    (hwm : Measurable w) (hw : BddAbove (range w)) :
    squareIntegrableSolutions A ≤ weightedSquareIntegrableSolutions A w := by
  obtain ⟨c, hc⟩ := hw
  rw [← weightedSquareIntegrableSolutions_zero]
  exact weightedSquareIntegrableSolutions_le_of_le_add hwm (C := c)
    fun s ↦ by simpa using hc (mem_range_self s)

/-- **Weighted solutions are solutions of the conjugate equation.** For a weight `w` with
derivative `w'`, multiplication by `e^w` carries the solutions `u` of `u' + A u = 0` with `e^w u`
square integrable onto the square-integrable solutions of `v' + (A - w') v = 0`. So the kernel of
the trajectory operator with coefficient `A - w'`, which is `D_A` conjugated from the
`e^w`-weighted spaces, consists of the weighted solutions of `u' + A u = 0`. -/
theorem squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions
    {w w' : ℝ → ℝ} (hw : ∀ s, HasDerivAt w (w' s) s) :
    squareIntegrableSolutions (fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) =
      weightedSquareIntegrableSolutions A w := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl, hv, hv2⟩ := mem_squareIntegrableSolutions.1 hx
    have hu (s : ℝ) : HasDerivAt (fun s ↦ exp (-w s) • v s) (-A s (exp (-w s) • v s)) s := by
      convert hasDerivAt_exp_smul_sub_smul_id (hw s).neg (hv s) using 3
      ext y
      simp
    have hx : exp (-w 0) • v 0 ∈ weightedSquareIntegrableSolutions A w :=
      ⟨_, rfl, hu, by simpa [smul_smul, ← exp_add] using hv2⟩
    simpa [smul_smul, ← exp_add] using
      (weightedSquareIntegrableSolutions A w).smul_mem (exp (w 0)) hx
  · rintro ⟨u, rfl, hu, hu2⟩
    have hx : exp (w 0) • u 0 ∈
        squareIntegrableSolutions (fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :=
      mem_squareIntegrableSolutions.2
        ⟨_, rfl, fun s ↦ hasDerivAt_exp_smul_sub_smul_id (hw s) (hu s), hu2⟩
    simpa [smul_smul, ← exp_add] using (squareIntegrableSolutions _).smul_mem (exp (-w 0)) hx

end Solutions

end TauCeti

namespace TauCeti.WeakDerivStep

section Kernel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {A : ℝ → F →L[ℝ] F} {w w' : ℝ → ℝ}

/-- **The kernel of the weighted trajectory operator.** For a continuous family `A` on a real
Banach space and a weight `w` with continuous derivative `w'`, the trajectory operator with
coefficient `A - w'` on `W^{1,2}(ℝ, F)`, which is `D_A` conjugated from the `e^w`-weighted
spaces, has the dimension of the space of solutions of `u' + A u = 0` with `e^w u` square
integrable. -/
theorem finrank_ker_trajectoryOperator_sub_smul_id (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker =
      Module.finrank ℝ (weightedSquareIntegrableSolutions A w) := by
  have hB : Continuous fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F :=
    hA.sub (hw'.smul continuous_const)
  rw [finrank_ker_trajectoryOperator hB AL hAL,
    squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions hw]

end Kernel

section Index

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {w w' : ℝ → ℝ}

/-- **The index of the weighted trajectory operator.** Let `A` be a continuous family of operators
on a finite-dimensional real inner product space with limits `A±`, and `w` a weight whose
continuous derivative `w'` tends to `δ±` at `±∞`. If the shifted limits `A± - δ±` have Lyapunov
forms, then the trajectory operator with coefficient `A - w'`, which is `D_A` conjugated from the
`e^w`-weighted spaces, has index `dim K - dim K†`. Here `K` consists of the solutions of
`u' + A u = 0` with `e^w u` square integrable, and `K†` of the solutions of the adjoint equation
`u' - A† u = 0` with `e^{-w} u` square integrable. -/
theorem index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') {Aminus Aplus : E →L[ℝ] E}
    {δminus δplus : ℝ}
    (hminus : (Aminus - δminus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : (Aplus - δplus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (weightedSquareIntegrableSolutions A w) : ℤ) -
        Module.finrank ℝ (weightedSquareIntegrableSolutions
          (fun s ↦ -ContinuousLinearMap.adjoint (A s)) (-w)) := by
  have hB : Continuous fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E :=
    hA.sub (hw'.smul continuous_const)
  have hadj : Continuous fun s ↦ -ContinuousLinearMap.adjoint (A s) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).neg
  obtain ⟨BL, hBL⟩ := exists_ae_eq_adjoint AL hAL
  have hnegBL : -BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -ContinuousLinearMap.adjoint (A s) - (-w' s) • ContinuousLinearMap.id ℝ E := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with s hs hBs
    rw [hs, Pi.neg_apply, hBs, map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_id]
    simp [sub_eq_add_neg, add_comm]
  rw [index_trajectoryOperator_of_hasLyapunovForm hB hminus hplus
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) AL BL hAL hBL,
    finrank_ker_trajectoryOperator_sub_smul_id hA hw hw' AL hAL,
    finrank_ker_trajectoryOperator_sub_smul_id
      hadj (w := -w) (fun s ↦ (hw s).neg) hw'.neg (-BL) hnegBL]

omit [FiniteDimensional ℝ E] in
/-- A symmetric operator shifted by a real multiple of the identity is symmetric. -/
private theorem isSymmetric_sub_smul_id {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (δ : ℝ) : ((T - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric :=
  by simpa using hT.sub (LinearMap.IsSymmetric.id.smul (c := δ) (by simp))

omit [FiniteDimensional ℝ E] in
/-- A shifted operator `T - δ • id` is injective exactly when `δ` is not an eigenvalue of `T`. -/
private theorem injective_sub_smul_id_iff {T : E →L[ℝ] E} {δ : ℝ} :
    Function.Injective (T - δ • ContinuousLinearMap.id ℝ E) ↔
      ¬ Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) δ := by
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def, not_not, LinearMap.ker_eq_bot]
  rfl

/-- **The weighted Fredholm criterion.** Let `A` be a continuous family of operators on a
finite-dimensional real inner product space with symmetric limits `A±`, and `w` a weight whose
continuous derivative `w'` tends to `δ±` at `±∞`. The trajectory operator with coefficient
`A - w'`, which is `D_A` conjugated from the `e^w`-weighted spaces, is Fredholm exactly when
neither `δ⁻` is an eigenvalue of `A⁻` nor `δ⁺` an eigenvalue of `A⁺`. -/
theorem isFredholm_trajectoryOperator_sub_smul_id_iff (hA : Continuous A) (hw' : Continuous w')
    {Aminus Aplus : E →L[ℝ] E} {δminus δplus : ℝ}
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm ↔
      ¬ Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus ∧
        ¬ Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus := by
  rw [isFredholm_trajectoryOperator_iff (hA.sub (hw'.smul continuous_const))
      (isSymmetric_sub_smul_id hsymminus δminus) (isSymmetric_sub_smul_id hsymplus δplus)
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) AL hAL,
    injective_sub_smul_id_iff, injective_sub_smul_id_iff]

/-- **The weighted index counts eigenvalues below the weights.** Let `A` be a continuous family of
operators on a finite-dimensional real inner product space with symmetric limits `A±`, and `w` a
weight whose continuous derivative `w'` tends to `δ±` at `±∞`, where `δ±` is not an eigenvalue of
`A±`. Then the trajectory operator with coefficient `A - w'`, which is `D_A` conjugated from the
`e^w`-weighted spaces, has index the number of eigenvalues of `A⁻` below `δ⁻` minus the number of
eigenvalues of `A⁺` below `δ⁺`, counted with multiplicity. Moving a weight across an eigenvalue
changes the index by its multiplicity. -/
theorem index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
    (hA : Continuous A) (hw' : Continuous w') {Aminus Aplus : E →L[ℝ] E} {δminus δplus : ℝ}
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hδminus : ¬ Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬ Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio δminus)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δplus)) := by
  -- The shifted limits are injective, hence bounded below by a common constant.
  have hgap (T : E →L[ℝ] E) (δ : ℝ) (hT : ¬ Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) δ) :
      ∃ α > 0, ∀ v, α * ‖v‖ ≤ ‖(T - δ • ContinuousLinearMap.id ℝ E) v‖ := by
    obtain ⟨K, hK, hKT⟩ := LinearMap.exists_antilipschitzWith
      ((T - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E)
      (LinearMap.ker_eq_bot.2 (injective_sub_smul_id_iff.2 hT))
    refine ⟨(K : ℝ)⁻¹, inv_pos.2 (by exact_mod_cast hK), fun v ↦ ?_⟩
    rw [inv_mul_le_iff₀ (by exact_mod_cast hK)]
    exact hKT.le_mul_norm (map_zero _) v
  obtain ⟨αm, hαm, hm⟩ := hgap Aminus δminus hδminus
  obtain ⟨αp, hαp, hp⟩ := hgap Aplus δplus hδplus
  have hshift (T : E →L[ℝ] E) (δ : ℝ) :
      Module.End.pointSpectralSubspace
        ((T - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) =
        Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio δ) := by
    have h : ((T - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        (T : E →ₗ[ℝ] E) - ((δ : ℝ) : ℝ) • 1 := by
      ext v
      simp
    have hsub := Module.End.pointSpectralSubspace_sub_smul_one (A := (T : E →ₗ[ℝ] E))
      (Ω := Iio 0) δ
    rwa [RCLike.ofReal_real_eq_id, id, preimage_sub_const_Iio, zero_add, ← h] at hsub
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
      (hA.sub (hw'.smul continuous_const)) (isSymmetric_sub_smul_id hsymminus δminus)
      (isSymmetric_sub_smul_id hsymplus δplus) (lt_min hαm hαp)
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hm v))
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hp v))
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) AL hAL,
    hshift, hshift]

/-- **A weight makes `d/ds` Fredholm.** For the zero family the trajectory operator is `d/ds`,
which is not Fredholm on `W^{1,2}(ℝ, E)` when `E ≠ 0` since its limits are not injective
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`). With a weight whose continuous
derivative `w'` tends to `δ⁻ < 0` at `-∞` and to `δ⁺ > 0` at `+∞`, so that the weighted paths
decay exponentially at both ends, the conjugated operator `d/ds - w'` has index `-dim E`: no
nonzero constant decays, while every constant pairs with the weighted target. -/
theorem index_trajectoryOperator_neg_smul_id (hw' : Continuous w') {δminus δplus : ℝ}
    (hδminus : δminus < 0) (hδplus : 0 < δplus)
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -(w' s • ContinuousLinearMap.id ℝ E)) :
    (trajectoryOperator (p := 2) AL).index = -(Module.finrank ℝ E : ℤ) := by
  -- The zero operator has the single eigenvalue `0`, with eigenspace everything.
  have heig (μ : ℝ) (hμ : μ ≠ 0) :
      Module.End.eigenspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)) μ = ⊥ := by
    ext x
    simp [eq_comm (a := (0 : E)), hμ]
  have hnot (μ : ℝ) (hμ : μ ≠ 0) :
      ¬ Module.End.HasEigenvalue (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)) μ :=
    fun h ↦ h (heig μ hμ)
  have hsym : (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)).IsSymmetric := fun x y ↦ by simp
  rw [index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
      (A := fun _ ↦ 0) continuous_const hw' hsym hsym (hnot _ hδminus.ne) (hnot _ hδplus.ne')
      tendsto_const_nhds tendsto_const_nhds hw'bot hw'top AL (by simpa using hAL)]
  have hbot : Module.End.pointSpectralSubspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (Iio δminus) = ⊥ :=
    eq_bot_iff.2 <| Module.End.pointSpectralSubspace_le_iff.2 fun μ hμ ↦
      (heig μ (lt_trans (mem_Iio.1 hμ) hδminus).ne).le
  have htop : Module.End.pointSpectralSubspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (Iio δplus) = ⊤ :=
    eq_top_iff.2 fun x _ ↦ Module.End.eigenspace_le_pointSpectralSubspace (μ := 0) hδplus
      (by simp)
  rw [hbot, htop, finrank_bot, finrank_top]
  simp

end Index

end TauCeti.WeakDerivStep

namespace TauCeti

open WeakDerivStep

section Decay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {w w' : ℝ → ℝ}

/-- **Weights below the spectral gaps do not change the solutions.** Let `A` be a continuous family
of operators on a finite-dimensional real inner product space with limits `A±`, and `w` a weight
bounded below whose continuous derivative `w'` tends to `δ±` at `±∞`. If `A± - t δ±` has a
Lyapunov form for every `t ∈ [0, 1]`, then every square-integrable solution `u` of
`u' + A u = 0` has `e^w u` square integrable. This is
`TauCeti.squareIntegrableSolutions_sub_smul_id` transported along the conjugation by `e^w`. -/
theorem weightedSquareIntegrableSolutions_eq_squareIntegrableSolutions (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hwb : BddBelow (range w))
    {Aminus Aplus : E →L[ℝ] E} {δminus δplus : ℝ}
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aminus - (t * δminus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1,
      (Aplus - (t * δplus) • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus)) :
    weightedSquareIntegrableSolutions A w = squareIntegrableSolutions A := by
  rw [← squareIntegrableSolutions_sub_smul_id_eq_weightedSquareIntegrableSolutions hw]
  exact squareIntegrableSolutions_sub_smul_id hA hbot htop hw hw' hwb hw'bot hw'top hminus hplus

/-- **Exponential decay below the spectral gap.** Let `A` be a continuous family of operators on a
finite-dimensional real inner product space whose limits `A±` are symmetric with `α ‖v‖ ≤ ‖A± v‖`.
Then for every `0 ≤ δ < α`, every square-integrable solution `u` of `u' + A u = 0` has
`e^{δ |s|} u(s)` square integrable. -/
theorem memLp_exp_mul_abs_smul_of_hasDerivAt (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    {α : ℝ} (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < α) {u : ℝ → E} (hu : ∀ s, HasDerivAt u (-A s (u s)) s)
    (hu2 : MemLp u 2) :
    MemLp (fun s ↦ exp (δ * |s|) • u s) 2 := by
  -- The weight `δ log cosh s`, with derivative `δ tanh s` tending to `∓δ`.
  have hw (s : ℝ) : HasDerivAt (fun s ↦ δ * log (cosh s)) (δ * tanh s) s :=
    (hasDerivAt_log_cosh s).const_mul δ
  have hwb : BddBelow (range fun s ↦ δ * log (cosh s)) :=
    ⟨0, by
      rintro _ ⟨s, rfl⟩
      exact mul_nonneg hδ0 (log_nonneg (one_le_cosh s))⟩
  -- Shifting a symmetric limit by at most `δ` keeps a Lyapunov form.
  have hlyap (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric) (hgap : ∀ v, α * ‖v‖ ≤ ‖T v‖)
      (c : ℝ) (hc : |c| ≤ δ) : (T - c • ContinuousLinearMap.id ℝ E).HasLyapunovForm :=
    ContinuousLinearMap.hasLyapunovForm_sub_smul_id_of_isSymmetric hT hgap (hc.trans_lt hδ)
  have hmem : u 0 ∈ weightedSquareIntegrableSolutions A fun s ↦ δ * log (cosh s) := by
    rw [weightedSquareIntegrableSolutions_eq_squareIntegrableSolutions hA hw
      (continuous_const.mul continuous_tanh) hwb
      (δminus := -δ) (δplus := δ)
      (fun t ht ↦ hlyap Aminus hsymminus hminus _ (by
        rw [abs_mul, abs_neg, abs_of_nonneg ht.1, abs_of_nonneg hδ0]
        exact mul_le_of_le_one_left hδ0 ht.2))
      (fun t ht ↦ hlyap Aplus hsymplus hplus _ (by
        rw [abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hδ0]
        exact mul_le_of_le_one_left hδ0 ht.2))
      hbot htop (by simpa using tendsto_tanh_atBot.const_mul δ)
      (by simpa using tendsto_tanh_atTop.const_mul δ)]
    exact mem_squareIntegrableSolutions.2 ⟨u, rfl, hu, hu2⟩
  -- `δ |s| ≤ δ log cosh s + δ log 2`, since `|s| - log 2 ≤ log cosh s`.
  have hcmp : ∀ s, δ * |s| ≤ δ * log (cosh s) + δ * log 2 := fun s ↦ by
    nlinarith [mul_le_mul_of_nonneg_left (abs_sub_log_two_le_log_cosh s) hδ0]
  obtain ⟨v, hv0, hv, hv2⟩ := weightedSquareIntegrableSolutions_le_of_le_add
    (measurable_const.mul continuous_abs.measurable) hcmp hmem
  have hcont : Continuous fun s ↦ -A s := hA.neg
  have huv : v = u := hcont.eq_of_hasDerivAt_clm_apply (fun s ↦ by simpa using hv s)
    (fun s ↦ by simpa using hu s) (t₀ := 0) hv0
  rwa [huv] at hv2

end Decay

end TauCeti
