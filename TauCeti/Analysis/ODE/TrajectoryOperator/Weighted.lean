/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index

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
Weights below the spectral gaps do not change the solutions; that case is
`TauCeti.squareIntegrableSolutions_sub_smul_id`.

## Main declarations

* `TauCeti.WeakDerivStep.finrank_ker_trajectoryOperator_sub_smul_id`: the kernel of the weighted
  operator.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank`: its index,
  for hyperbolic shifted limits, as the difference of the dimensions of the weighted solution
  spaces of `u' + A u = 0` and of the adjoint equation `u' - A† u = 0` with weight `-w`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`: for symmetric limits,
  the weighted operator is Fredholm exactly when `δ±` is not an eigenvalue of `A±`.
* `index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`, in
  `TauCeti.WeakDerivStep`: its index counts the eigenvalues of `A±` below `δ±`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_neg_smul_id_eq_neg_finrank`: with decaying
  weights, `d/ds` has index `-dim E`.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Sc. Norm. Sup. Pisa **12** (1985), 409–447 (Fredholm theory in exponentially weighted
  spaces, with index jumps at the weights in the limiting spectra).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.1 and Chapter 10 (weighted Sobolev spaces).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

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
      (ContinuousLinearMap.isSymmetric_sub_smul_id hsymminus δminus)
      (ContinuousLinearMap.isSymmetric_sub_smul_id hsymplus δplus)
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) AL hAL,
    ContinuousLinearMap.injective_sub_smul_id_iff, ContinuousLinearMap.injective_sub_smul_id_iff]

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
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
      (hA.sub (hw'.smul continuous_const))
      (ContinuousLinearMap.isSymmetric_sub_smul_id hsymminus δminus)
      (ContinuousLinearMap.isSymmetric_sub_smul_id hsymplus δplus)
      (ContinuousLinearMap.injective_sub_smul_id_iff.2 hδminus)
      (ContinuousLinearMap.injective_sub_smul_id_iff.2 hδplus)
      (hbot.sub (hw'bot.smul_const _)) (htop.sub (hw'top.smul_const _)) AL hAL,
    ContinuousLinearMap.pointSpectralSubspace_sub_smul_id,
    ContinuousLinearMap.pointSpectralSubspace_sub_smul_id, preimage_sub_const_Iio,
    preimage_sub_const_Iio, zero_add, zero_add]

/-- **The index of `d/ds` with decaying weights.** For the zero family the trajectory operator is
`d/ds`, which is not Fredholm on `W^{1,2}(ℝ, E)` when `E ≠ 0` since its limits are not injective
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`). Take a weight whose continuous
derivative `w'` tends to `δ⁻ < 0` at `-∞` and to `δ⁺ > 0` at `+∞`, so that the weighted paths
decay exponentially at both ends. Then the conjugated operator `d/ds - w'` has index `-dim E`: no
nonzero constant decays, while every constant pairs with the weighted target. Since `δ±` are not
eigenvalues of `0`, this operator is Fredholm by
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`. -/
theorem index_trajectoryOperator_neg_smul_id_eq_neg_finrank (hw' : Continuous w')
    {δminus δplus : ℝ} (hδminus : δminus < 0) (hδplus : 0 < δplus)
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
