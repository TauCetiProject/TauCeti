/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# The index of the trajectory operator as a weight crosses an eigenvalue

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner
product space `E` with symmetric limits `A±` at `±∞`. Multiplication by `exp w` conjugates the
trajectory operator `D_A u = u' + A u` on the weighted spaces `{u | exp w • u ∈ W^{1,2}}` to the
unweighted trajectory operator `D_{A - w'}` (see `TauCeti.Analysis.ODE.EnergyEstimate.Weighted`).
When the slope `w'` tends to `δ±` at `±∞`, the limits of `A - w'` are `A± - δ±`, which are
invertible when `δ±` is not an eigenvalue of `A±`. The weighted operator is Fredholm exactly for
these non-exceptional weights (`isFredholm_trajectoryOperator_sub_smul_id_iff`), and this file
computes its index:

`ind D_{A - w'} = n_{< δ⁻}(A⁻) - n_{< δ⁺}(A⁺)`,

where `n_{< δ}(B)` is the number of eigenvalues of `B` below `δ`, counted with multiplicity
(`index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`).
This is the index formula for invertible symmetric limits
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`)
applied to the shifted limits, since the eigenvalues of `A± - δ±` are those of `A±` shifted by
`-δ±` (`Module.End.pointSpectralSubspace_sub_smul_id`).

Consequently the index depends on the weight only through the position of its slopes relative to
the spectra of the limits, and it changes only when a slope crosses an eigenvalue. A decay weight
`exp (δ |s|)` has slopes `δ⁺ = δ` and `δ⁻ = -δ`; making it stronger moves `δ⁺` up and `δ⁻` down,
and the index decreases by the number of eigenvalues of `A⁺` crossed by `δ⁺` plus the number of
eigenvalues of `A⁻` crossed by `δ⁻`, counted with multiplicity
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_add_finrank_pointSpectralSubspace_Ico`). In
particular, as the weight increases through one exceptional value at either end, the index
decreases by the multiplicity of the crossed eigenvalue
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_add_finrank_eigenspace_atTop` and
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_add_finrank_eigenspace_atBot`).
The weights below the spectral gap of `TauCeti.Analysis.ODE.EnergyEstimate.Weighted` cross no
eigenvalue, and leave the index unchanged. The limits `A±` may have kernels: for small decay
weights, with slopes `δ⁻ < 0 < δ⁺` closer to `0` than every nonzero eigenvalue of the respective
limits, the index is `n⁻(A⁻) - n⁻(A⁺) - dim ker A⁺`, so the kernel of the limit at `+∞` is counted
as negative and that at `-∞` as positive
(`index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker`, in
`TauCeti.WeakDerivStep`).

A weight can therefore make `D_A` Fredholm when a limit is degenerate, as for Morse–Bott
trajectories: for `A = 0`, where `d/ds` itself is not Fredholm, a slope with `δ⁻ < 0 < δ⁺` gives
index `-dim E` (`index_trajectoryOperator_neg_smul_id_eq_neg_finrank`).

For the symmetric weight `w(s) = δ log (cosh s)`, which is `δ |s|` up to a bounded error, the slope
is `δ tanh s` and the index is `n_{< -δ}(A⁻) - n_{< δ}(A⁺)`
(`index_trajectoryOperator_sub_mul_tanh_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`).
For a continuous family `B` with nonzero scalar limits `b± • id` the index is `dim E` when
`b⁻ < 0 < b⁺`, `-dim E` when `b⁺ < 0 < b⁻`, and `0` otherwise
(`TauCeti.WeakDerivStep.index_trajectoryOperator_of_tendsto_smul_id`). In particular, for a
constant scalar coefficient `a • id` on `E` the index is `dim E` when `δ⁺ < a < δ⁻`,
`-dim E` when `δ⁻ < a < δ⁺`, and `0` when `δ⁻` and `δ⁺` lie on the same side of `a`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_smul_id_sub_smul_id`); for `a = 0` the
unweighted operator `d/ds`, which is not Fredholm when `E ≠ 0`, becomes Fredholm of index
`-dim E` for decay weights and of index `dim E` for growth weights.
In the scalar case `E = ℝ` with constant coefficient `a`, the operator `u ↦ u' + (a - δ tanh s) u`
has index `0` for `|δ| < |a|` and index `-1` for `δ > |a|`: as `δ` increases through `|a|`, one
of the two slopes `±δ` crosses the simple eigenvalue `a` of the limits.

## Main results

In the namespace `TauCeti.WeakDerivStep`:

* `isFredholm_trajectoryOperator_sub_smul_id`, `isFredholm_trajectoryOperator_sub_smul_id_iff`:
  `D_{A - c}` is Fredholm exactly for slopes `c` with non-exceptional limits `δ±`.
* `index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`: the index of
  `D_{A - c}` for slopes `c` with non-exceptional limits `δ±` is `n_{< δ⁻}(A⁻) - n_{< δ⁺}(A⁺)`.
* `index_trajectoryOperator_neg_smul_id_eq_neg_finrank`: for `A = 0` and slopes with
  `δ⁻ < 0 < δ⁺`, the weighted operator `d/ds - c` has index `-dim E`.
* `index_trajectoryOperator_eq_add_finrank_pointSpectralSubspace_Ico`: moving the limits of the
  slope outward changes the index by the number of eigenvalues crossed at the two ends.
* `index_trajectoryOperator_eq_add_finrank_eigenspace_atTop`,
  `index_trajectoryOperator_eq_add_finrank_eigenspace_atBot`: crossing one eigenvalue
  at one end changes the index by its multiplicity.
* `index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker`: small decay
  weights give the index `n⁻(A⁻) - n⁻(A⁺) - dim ker A⁺`.
* `index_trajectoryOperator_sub_mul_tanh_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank`:
  the index for the symmetric weight `δ log (cosh s)`.
* `index_trajectoryOperator_of_tendsto_smul_id`: the index for nonzero scalar limits.
* `index_trajectoryOperator_smul_id_sub_smul_id`: the index for a constant scalar coefficient on
  `E`.
* `index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id_eq_zero_of_abs_lt_abs`,
  `index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id_eq_neg_one_of_abs_lt`: the scalar crossing,
  index `0` below `|a|` and `-1` above it.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (the index on weighted spaces
  is locally constant in the weight and jumps at the exceptional weights by the dimension of the
  crossed asymptotic eigenspace).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.1 and Chapter 10 (weighted Sobolev spaces).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace
open ContinuousLinearMap (isSymmetric_sub_smul_id ker_sub_smul_id_eq_bot_iff)

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {Aminus Aplus : E →L[ℝ] E}

/-- **The weighted Fredholm criterion.** Let `A` be a continuous family of operators on a
finite-dimensional real inner product space with symmetric limits `A±`, and let `c` be a
continuous slope tending to `δ±` at `±∞`. The trajectory operator `u ↦ u' + (A - c) u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm exactly when neither `δ⁻` is an eigenvalue of `A⁻` nor
`δ⁺` an eigenvalue of `A⁺`. For `c = w'` this operator is the conjugate of `D_A` on the spaces
weighted by `exp w`. -/
theorem isFredholm_trajectoryOperator_sub_smul_id_iff (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).IsFredholm ↔
      ¬ Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus ∧
        ¬ Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus := by
  rw [isFredholm_trajectoryOperator_iff (hA.sub (hc.smul continuous_const))
      (isSymmetric_sub_smul_id hsymminus (conj_trivial δminus))
      (isSymmetric_sub_smul_id hsymplus (conj_trivial δplus))
      (hbot.sub (hcbot.smul_const _)) (htop.sub (hctop.smul_const _)) BL hBL,
    ← ker_sub_smul_id_eq_bot_iff, ← ker_sub_smul_id_eq_bot_iff, LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]

/-- **The weighted trajectory operator is Fredholm.** Let `A` be a continuous family of operators
on a finite-dimensional real inner product space with symmetric limits `A±` at `±∞`, and let `c`
be a continuous slope tending to `δ±` at `±∞`, where `δ±` is not an eigenvalue of `A±`. Then the
trajectory operator `u ↦ u' + (A - c) u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm. For
`c = w'` this operator is the conjugate of `D_A` on the spaces weighted by `exp w`. -/
theorem isFredholm_trajectoryOperator_sub_smul_id
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).IsFredholm :=
  (isFredholm_trajectoryOperator_sub_smul_id_iff hA hsymminus hsymplus hbot htop hc hcbot hctop
    BL hBL).2 ⟨hδminus, hδplus⟩

/-- **The index on exponentially weighted spaces.** Let `A` be a continuous family of operators on
a finite-dimensional real inner product space with symmetric limits `A±` at `±∞`, and let `c` be
a continuous slope tending to `δ±` at `±∞`, where `δ±` is not an eigenvalue of `A±`. Then the
index of the trajectory operator `u ↦ u' + (A - c) u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is the
number of eigenvalues of `A⁻` below `δ⁻` minus the number of eigenvalues of `A⁺` below `δ⁺`,
counted with multiplicity. For `c = w'` this operator is the conjugate of `D_A` on the spaces
weighted by `exp w`. -/
theorem index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio δminus)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δplus)) := by
  set I := ContinuousLinearMap.id ℝ E
  -- The shifted limits `A± - δ±` are symmetric, and invertible since `δ±` is not an eigenvalue.
  have hbound {T : E →L[ℝ] E} {δ : ℝ} (hT : ¬Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) δ) :
      ∃ α > 0, ∀ v, α * ‖v‖ ≤ ‖(T - δ • I) v‖ := by
    obtain ⟨K, -, hKT⟩ := LinearMap.exists_antilipschitzWith _
      (ker_sub_smul_id_eq_bot_iff.2 hT)
    exact antilipschitzWith_iff_exists_mul_le_norm.1 ⟨K, hKT⟩
  obtain ⟨α₁, hα₁, h₁⟩ := hbound hδminus
  obtain ⟨α₂, hα₂, h₂⟩ := hbound hδplus
  have hshift (T : E →L[ℝ] E) (δ : ℝ) :
      Module.End.pointSpectralSubspace ((T - δ • I : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) =
        Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio δ) := by
    simpa [I] using Module.End.pointSpectralSubspace_sub_smul_id (A := (T : E →ₗ[ℝ] E))
      (Ω := Iio 0) δ
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
      (hA.sub (hc.smul continuous_const)) (isSymmetric_sub_smul_id hsymminus (conj_trivial δminus))
      (isSymmetric_sub_smul_id hsymplus (conj_trivial δplus)) (lt_min hα₁ hα₂)
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (h₁ v))
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (h₂ v))
      (hbot.sub (hcbot.smul_const I)) (htop.sub (hctop.smul_const I)) BL hBL,
    hshift, hshift]

/-- **The index of `d/ds` with decaying weights.** For the zero family the trajectory operator is
`d/ds`, which is not Fredholm on `W^{1,2}(ℝ, E)` when `E ≠ 0` since its limits are not injective
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`). Take a continuous slope `c` tending
to `δ⁻ < 0` at `-∞` and to `δ⁺ > 0` at `+∞`, the derivative of a weight `w` for which the weighted
paths decay exponentially at both ends. Then `u ↦ u' - c u` has index `-dim E`: no nonzero
constant decays, while every constant pairs with the weighted target. Since `δ±` are not
eigenvalues of `0`, this operator is Fredholm by
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`. -/
theorem index_trajectoryOperator_neg_smul_id_eq_neg_finrank {c : ℝ → ℝ} (hc : Continuous c)
    {δminus δplus : ℝ} (hδminus : δminus < 0) (hδplus : 0 < δplus)
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -(c s • ContinuousLinearMap.id ℝ E)) :
    (trajectoryOperator (p := 2) BL).index = -(Module.finrank ℝ E : ℤ) := by
  -- The zero operator has the single eigenvalue `0`, with eigenspace everything.
  have heig (μ : ℝ) (hμ : μ ≠ 0) :
      Module.End.eigenspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)) μ = ⊥ := by
    ext x
    simp [eq_comm (a := (0 : E)), hμ]
  have hnot (μ : ℝ) (hμ : μ ≠ 0) :
      ¬ Module.End.HasEigenvalue (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)) μ :=
    fun h ↦ h (heig μ hμ)
  have hsym : (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E)).IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_zero]
    exact LinearMap.IsSymmetric.zero
  rw [index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
      (A := fun _ ↦ 0) continuous_const hsym hsym tendsto_const_nhds tendsto_const_nhds hc hcbot
      hctop (hnot _ hδminus.ne) (hnot _ hδplus.ne') BL (by simpa using hBL)]
  have hbot : Module.End.pointSpectralSubspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (Iio δminus) = ⊥ := by
    simpa using Module.End.pointSpectralSubspace_smul_id_of_notMem (𝕜 := ℝ) (E := E) (c := 0)
      (notMem_Iio.2 hδminus.le)
  have htop : Module.End.pointSpectralSubspace (((0 : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (Iio δplus) = ⊤ := by
    simpa using Module.End.pointSpectralSubspace_smul_id_of_mem (𝕜 := ℝ) (E := E) (c := 0)
      (mem_Iio.2 hδplus)
  rw [hbot, htop, finrank_bot, finrank_top]
  simp

/-- **The index jumps by the eigenvalues crossed by the weight.** Let `c₁` and `c₂` be continuous
slopes with non-exceptional limits for the symmetric limits `A±` of `A`, such that the limits of
`c₂` lie outside those of `c₁`: `δ₂⁻ ≤ δ₁⁻` at `-∞` and `δ₁⁺ ≤ δ₂⁺` at `+∞`, as for a stronger
decay weight. Then the index of `u ↦ u' + (A - c₁) u` exceeds that of `u ↦ u' + (A - c₂) u` by the
number of eigenvalues of `A⁻` in `[δ₂⁻, δ₁⁻)` plus the number of eigenvalues of `A⁺` in
`[δ₁⁺, δ₂⁺)`, counted with multiplicity. -/
theorem index_trajectoryOperator_eq_add_finrank_pointSpectralSubspace_Ico
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c₁ c₂ : ℝ → ℝ} (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    {δ₁minus δ₁plus δ₂minus δ₂plus : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δ₁minus)) (hc₁top : Tendsto c₁ atTop (𝓝 δ₁plus))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δ₂minus)) (hc₂top : Tendsto c₂ atTop (𝓝 δ₂plus))
    (hminus : δ₂minus ≤ δ₁minus) (hplus : δ₁plus ≤ δ₂plus)
    (hδ₁minus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δ₁minus)
    (hδ₁plus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δ₁plus)
    (hδ₂minus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δ₂minus)
    (hδ₂plus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δ₂plus)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₁ s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₂ s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₁).index =
      (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Ico δ₂minus δ₁minus)) +
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ico δ₁plus δ₂plus)) := by
  rw [index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank hA
      hsymminus hsymplus hbot htop hc₁ hc₁bot hc₁top hδ₁minus hδ₁plus BL₁ hBL₁,
    index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank hA
      hsymminus hsymplus hbot htop hc₂ hc₂bot hc₂top hδ₂minus hδ₂plus BL₂ hBL₂,
    Module.End.finrank_pointSpectralSubspace_Iio_eq_add hminus,
    Module.End.finrank_pointSpectralSubspace_Iio_eq_add (A := (Aplus : E →ₗ[ℝ] E)) hplus]
  push_cast
  ring

/-- **Crossing one exceptional value at `+∞`.** Let `c₁` and `c₂` be continuous slopes with the
same non-exceptional limit at `-∞`, and with limits `δ₁ < ν < δ₂` at `+∞`, where `ν` is the only
eigenvalue of the symmetric limit `A⁺` in `[δ₁, δ₂]`. Then the index of `u ↦ u' + (A - c₁) u`
exceeds that of `u ↦ u' + (A - c₂) u` by the multiplicity of `ν`: as the decay weight at `+∞`
increases through `ν`, the index decreases by the dimension of the eigenspace of `A⁺` at `ν`. -/
theorem index_trajectoryOperator_eq_add_finrank_eigenspace_atTop
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c₁ c₂ : ℝ → ℝ} (hc₁ : Continuous c₁) (hc₂ : Continuous c₂) {δminus δ₁ δ₂ ν : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δminus)) (hc₁top : Tendsto c₁ atTop (𝓝 δ₁))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δminus)) (hc₂top : Tendsto c₂ atTop (𝓝 δ₂))
    (hν : ν ∈ Ioo δ₁ δ₂) (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδ₁ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δ₂)
    (hother : ∀ μ ∈ Ioo δ₁ δ₂, μ ≠ ν → ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) μ)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₁ s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₂ s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₁).index =
      (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ (Module.End.eigenspace (Aplus : E →ₗ[ℝ] E) ν) := by
  rw [index_trajectoryOperator_eq_add_finrank_pointSpectralSubspace_Ico hA hsymminus hsymplus
      hbot htop hc₁ hc₂ hc₁bot hc₁top hc₂bot hc₂top le_rfl (hν.1.trans hν.2).le hδminus hδ₁
      hδminus hδ₂ BL₁ BL₂ hBL₁ hBL₂,
    Ico_self, Module.End.pointSpectralSubspace_empty, finrank_bot, Nat.cast_zero, add_zero,
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₁
      hother,
    RCLike.ofReal_real_eq_id, id_eq]

/-- **Crossing one exceptional value at `-∞`.** Let `c₁` and `c₂` be continuous slopes with the
same non-exceptional limit at `+∞`, and with limits `δ₂ < ν < δ₁` at `-∞`, where `ν` is the only
eigenvalue of the symmetric limit `A⁻` in `[δ₂, δ₁]`. Then the index of `u ↦ u' + (A - c₁) u`
exceeds that of `u ↦ u' + (A - c₂) u` by the multiplicity of `ν`: as the decay weight at `-∞`
strengthens, its slope decreasing through `ν`, the index decreases by the dimension of the
eigenspace of `A⁻` at `ν`. -/
theorem index_trajectoryOperator_eq_add_finrank_eigenspace_atBot
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c₁ c₂ : ℝ → ℝ} (hc₁ : Continuous c₁) (hc₂ : Continuous c₂) {δplus δ₁ δ₂ ν : ℝ}
    (hc₁bot : Tendsto c₁ atBot (𝓝 δ₁)) (hc₁top : Tendsto c₁ atTop (𝓝 δplus))
    (hc₂bot : Tendsto c₂ atBot (𝓝 δ₂)) (hc₂top : Tendsto c₂ atTop (𝓝 δplus))
    (hν : ν ∈ Ioo δ₂ δ₁) (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (hδ₁ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δ₂)
    (hother : ∀ μ ∈ Ioo δ₂ δ₁, μ ≠ ν → ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) μ)
    (BL₁ BL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL₁ : BL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₁ s • ContinuousLinearMap.id ℝ E)
    (hBL₂ : BL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₂ s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL₁).index =
      (trajectoryOperator (p := 2) BL₂).index +
        Module.finrank ℝ (Module.End.eigenspace (Aminus : E →ₗ[ℝ] E) ν) := by
  rw [index_trajectoryOperator_eq_add_finrank_pointSpectralSubspace_Ico hA hsymminus hsymplus
      hbot htop hc₁ hc₂ hc₁bot hc₁top hc₂bot hc₂top (hν.1.trans hν.2).le le_rfl hδ₁ hδplus
      hδ₂ hδplus BL₁ BL₂ hBL₁ hBL₂,
    Ico_self, Module.End.pointSpectralSubspace_empty, finrank_bot, Nat.cast_zero, add_zero,
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₂
      hother,
    RCLike.ofReal_real_eq_id, id_eq]

/-- **The index for small decay weights.** Let `δminus > 0` be smaller than the absolute value of
every negative eigenvalue of `A⁻`, let `δplus > 0` be smaller than every positive eigenvalue of
`A⁺`, and let `c` be a continuous slope with limits `-δminus` at `-∞` and `δplus` at `+∞`, as for
a decay weight equal to `δminus |s|` near `-∞` and to `δplus |s|` near `+∞`. Then the index of
`u ↦ u' + (A - c) u` is the number of negative eigenvalues of `A⁻`, minus the number of negative
eigenvalues of `A⁺`, minus the dimension of the kernel of `A⁺`: the kernel of the limit at `+∞`
is counted as negative, and that at `-∞` as positive. -/
theorem index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ} (hδminus : 0 < δminus)
    (hδplus : 0 < δplus) (hcbot : Tendsto c atBot (𝓝 (-δminus)))
    (hctop : Tendsto c atTop (𝓝 δplus))
    (hgapminus : ∀ μ ∈ Ico (-δminus) 0, ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) μ)
    (hgapplus : ∀ μ ∈ Ioc 0 δplus, ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) μ)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0)) -
          Module.finrank ℝ (LinearMap.ker (Aplus : E →ₗ[ℝ] E)) := by
  rw [index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank hA
      hsymminus hsymplus hbot htop hc hcbot hctop (hgapminus _ ⟨le_rfl, neg_lt_zero.2 hδminus⟩)
      (hgapplus _ ⟨hδplus, le_rfl⟩) BL hBL]
  -- No eigenvalue of `A⁻` lies in `[-δminus, 0)`, and the only one of `A⁺` in `[0, δplus)` is
  -- `0`, whose eigenspace is the kernel.
  have hplus : Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ico 0 δplus) =
      LinearMap.ker (Aplus : E →ₗ[ℝ] E) := by
    rw [Module.End.pointSpectralSubspace_eq_eigenspace (𝕜 := ℝ) (Ω := Ico 0 δplus) (μ := 0)
      ⟨le_rfl, hδplus⟩
      fun ν hν hν0 ↦ not_not.1 (Module.End.hasEigenvalue_iff.not.1
        (hgapplus ν ⟨lt_of_le_of_ne hν.1 hν0.symm, hν.2.le⟩))]
    simp
  rw [Module.End.finrank_pointSpectralSubspace_Iio_eq_add (A := (Aminus : E →ₗ[ℝ] E))
      (neg_nonpos.2 hδminus.le),
    Module.End.finrank_pointSpectralSubspace_Iio_eq_add (A := (Aplus : E →ₗ[ℝ] E)) hδplus.le,
    Module.End.pointSpectralSubspace_eq_bot_iff.2 hgapminus, finrank_bot, hplus]
  push_cast
  ring

/-- **The index for the symmetric weight `δ log (cosh s)`.** Let `A` be a continuous family with
symmetric limits `A±`, and let `δ` be a real number such that `-δ` is not an eigenvalue of `A⁻`
and `δ` is not an eigenvalue of `A⁺`. The weight `δ log (cosh s)`, which is `δ |s|` up to a
bounded error, has slope `δ tanh s`, and the index of `u ↦ u' + (A - δ tanh s) u` is the number of
eigenvalues of `A⁻` below `-δ` minus the number of eigenvalues of `A⁺` below `δ`. -/
theorem index_trajectoryOperator_sub_mul_tanh_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
    (hA : Continuous A) (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {δ : ℝ}
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) (-δ))
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δ)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - (δ * Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio (-δ))) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δ)) :=
  index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank hA hsymminus
    hsymplus hbot htop (c := fun s ↦ δ * Real.tanh s) (continuous_const.mul Real.continuous_tanh)
    (by simpa using Real.tendsto_tanh_atBot.const_mul δ)
    (by simpa using Real.tendsto_tanh_atTop.const_mul δ) hδminus hδplus BL hBL

section Scalar

/-- **The index for scalar limits.** Let `B` be a continuous family of operators on a
finite-dimensional real inner product space `E` whose limits at `±∞` are nonzero scalars
`b± • id`. Then the trajectory operator `u ↦ u' + B u` has index `dim E` when `b⁻ < 0 < b⁺`,
`-dim E` when `b⁺ < 0 < b⁻`, and `0` when `b⁻` and `b⁺` have the same sign: each limit has the
single eigenvalue `b±`, of multiplicity `dim E`. -/
theorem index_trajectoryOperator_of_tendsto_smul_id {B : ℝ → E →L[ℝ] E} (hB : Continuous B)
    {bminus bplus : ℝ} (hbot : Tendsto B atBot (𝓝 (bminus • ContinuousLinearMap.id ℝ E)))
    (htop : Tendsto B atTop (𝓝 (bplus • ContinuousLinearMap.id ℝ E)))
    (hbminus : bminus ≠ 0) (hbplus : bplus ≠ 0)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B) :
    (trajectoryOperator (p := 2) BL).index =
      (if bminus < 0 then (Module.finrank ℝ E : ℤ) else 0) -
        if bplus < 0 then (Module.finrank ℝ E : ℤ) else 0 := by
  have hcoe (b : ℝ) :
      ((b • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) = b • LinearMap.id := by
    rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id]
  have hsym (b : ℝ) : ((b • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    simpa using LinearMap.IsSymmetric.id.smul (conj_trivial b)
  -- The scalar `b` has the single eigenvalue `b`. The lemmas on scalars are stated over `RCLike`;
  -- over `ℝ` the cast `ℝ → ℝ` is the identity.
  have hscalar (b : ℝ) (Ω : Set ℝ) (hb : b ∉ Ω) : Module.End.pointSpectralSubspace
      ((b • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) Ω = ⊥ := by
    have hs := Module.End.pointSpectralSubspace_smul_id_of_notMem (𝕜 := ℝ) (E := E) hb
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hs
    rw [hcoe, hs]
  have hne {b : ℝ} (hb : b ≠ 0) :
      ¬Module.End.HasEigenvalue ((b • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) 0 := by
    simpa using Module.End.pointSpectralSubspace_eq_bot_iff.mp
      (hscalar b {0} (notMem_singleton_iff.2 hb)) 0 (mem_singleton 0)
  have hfinrank (b : ℝ) : (Module.finrank ℝ (Module.End.pointSpectralSubspace
      ((b • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0)) : ℤ) =
        if b < 0 then (Module.finrank ℝ E : ℤ) else 0 := by
    split_ifs with h
    · have hs := Module.End.pointSpectralSubspace_smul_id_of_mem (𝕜 := ℝ) (E := E) (Ω := Iio 0) h
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hs
      rw [hcoe, hs, finrank_top]
    · rw [hscalar b _ h, finrank_bot, Nat.cast_zero]
  rw [index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
      (c := fun _ ↦ 0) hB (hsym bminus) (hsym bplus) hbot htop continuous_const tendsto_const_nhds
      tendsto_const_nhds (hne hbminus) (hne hbplus) BL (by simpa using hBL),
    hfinrank, hfinrank]

/-- **The scalar example.** For the constant coefficient `a • id` on a finite-dimensional real
inner product space `E` and a continuous slope `c` with limits `δ±` different from `a`, the
trajectory operator `u ↦ u' + (a - c) u` has index `dim E` when `δ⁺ < a < δ⁻`, `-dim E` when
`δ⁻ < a < δ⁺`, and `0` when `δ⁻` and `δ⁺` lie on the same side of `a`. This is
`index_trajectoryOperator_of_tendsto_smul_id` for the limits `(a - δ±) • id`. In particular, for
`a = 0` the operator `d/ds`, which is not Fredholm on unweighted spaces when `E ≠ 0`, has index
`-dim E` for decay weights (`δ⁻ < 0 < δ⁺`) and `dim E` for growth weights (`δ⁺ < 0 < δ⁻`). -/
theorem index_trajectoryOperator_smul_id_sub_smul_id (a : ℝ) {c : ℝ → ℝ} (hc : Continuous c)
    {δminus δplus : ℝ} (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hminus : δminus ≠ a) (hplus : δplus ≠ a)
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a • ContinuousLinearMap.id ℝ E - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) BL).index =
      (if a < δminus then (Module.finrank ℝ E : ℤ) else 0) -
        if a < δplus then (Module.finrank ℝ E : ℤ) else 0 := by
  have hlim {l : Filter ℝ} {δ : ℝ} (h : Tendsto c l (𝓝 δ)) :
      Tendsto (fun s ↦ a • ContinuousLinearMap.id ℝ E - c s • ContinuousLinearMap.id ℝ E) l
        (𝓝 ((a - δ) • ContinuousLinearMap.id ℝ E)) := by
    rw [sub_smul]
    exact tendsto_const_nhds.sub (h.smul_const _)
  rw [index_trajectoryOperator_of_tendsto_smul_id (continuous_const.sub (hc.smul continuous_const))
      (hlim hcbot) (hlim hctop) (sub_ne_zero.2 hminus.symm) (sub_ne_zero.2 hplus.symm) BL hBL]
  simp only [sub_neg]

variable {a δ : ℝ}

/-- The index of the scalar operator `u ↦ u' + (a - δ tanh s) u`, by the scalar example
`index_trajectoryOperator_smul_id_sub_smul_id` for the slope `δ tanh s`, whose limits are `∓δ`
at `∓∞`. -/
private theorem index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id (h₁ : a ≠ -δ)
    (h₂ : a ≠ δ) (BL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a • ContinuousLinearMap.id ℝ ℝ - (δ * Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) BL).index =
      (if a < -δ then 1 else 0 : ℤ) - (if a < δ then 1 else 0 : ℤ) := by
  rw [index_trajectoryOperator_smul_id_sub_smul_id a (c := fun s ↦ δ * Real.tanh s)
      (continuous_const.mul Real.continuous_tanh)
      (by simpa using Real.tendsto_tanh_atBot.const_mul δ)
      (by simpa using Real.tendsto_tanh_atTop.const_mul δ) h₁.symm h₂.symm BL hBL,
    Module.finrank_self, Nat.cast_one]

/-- **The scalar crossing below the rate.** For `|δ| < |a|`, the operator
`u ↦ u' + (a - δ tanh s) u` on `W^{1,2}(ℝ)`, the conjugate of `u ↦ u' + a u` on the spaces weighted
by `exp (δ log (cosh s))`, has index `0`. -/
theorem index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id_eq_zero_of_abs_lt_abs
    (hδa : |δ| < |a|) (BL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a • ContinuousLinearMap.id ℝ ℝ - (δ * Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) BL).index = 0 := by
  rw [index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id (by rintro rfl; simp at hδa)
    (by rintro rfl; simp at hδa) BL hBL]
  have hδ₁ := le_abs_self δ
  have hδ₂ := neg_abs_le δ
  rcases lt_abs.mp hδa with h | h
  · simp [show ¬a < -δ by linarith, show ¬a < δ by linarith]
  · simp [show a < -δ by linarith, show a < δ by linarith]

/-- **The scalar crossing above the rate.** For `δ > |a|`, the operator
`u ↦ u' + (a - δ tanh s) u` on `W^{1,2}(ℝ)`, the conjugate of `u ↦ u' + a u` on the spaces weighted
by `exp (δ log (cosh s))`, has index `-1`. -/
theorem index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id_eq_neg_one_of_abs_lt (hδa : |a| < δ)
    (BL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a • ContinuousLinearMap.id ℝ ℝ - (δ * Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) BL).index = -1 := by
  obtain ⟨h₁, h₂⟩ := abs_lt.mp hδa
  rw [index_trajectoryOperator_smul_id_sub_mul_tanh_smul_id h₁.ne' h₂.ne BL hBL]
  simp [show ¬a < -δ by linarith, show a < δ by linarith]

end Scalar

end TauCeti.WeakDerivStep
