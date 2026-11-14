/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.Normed.Module.Homogeneous

/-!
# The index of the trajectory operator on exponentially weighted spaces

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner
product space, with symmetric limits `A±` at `±∞`, and let `w` be a weight whose derivative `w'`
tends to `δ±` at `±∞`. Multiplication by `exp w` conjugates the trajectory operator
`D_A u = u' + A u` on the weighted spaces `{u | exp w • u ∈ W^{1,2}} → {f | exp w • f ∈ L²}` to
the unweighted trajectory operator `D_{A - w'}` of the shifted family `A - w' • id`, whose limits
are `A± - δ± • id`. For the decay weight `w(s) = δ log (cosh s)`, which is `δ |s|` up to a bounded
error, the slopes are `δ± = ±δ`.

This file shows that, for symmetric limits, `D_{A - c}` is Fredholm exactly when the limits `δ±`
at `±∞` of the continuous scalar function `c` are not eigenvalues of `A±`
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`), and computes its index in
that case. Then `A± - δ± • id` are invertible and symmetric, so the index is the number of
negative eigenvalues of `A⁻ - δ⁻` minus that of `A⁺ - δ⁺`, that is,

`ind D_{A - c} = n(A⁻, δ⁻) - n(A⁺, δ⁺)`,

where `n(B, δ)` is the number of eigenvalues of the symmetric operator `B` below `δ`, counted with
multiplicity (`TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id`). The limits `A±` may
have kernels; only the shifted limits must be invertible. So exponential weights turn the
trajectory operator of a family with degenerate limits, such as the linearization along a
trajectory between Morse–Bott critical manifolds, into a Fredholm operator whose index is
computed by the shifted spectra.

As a consequence, the index jumps exactly when a slope crosses an eigenvalue of a limit
(`TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_eq_index_sub_finrank_sub_finrank`).
If the slope at `+∞` increases from `δ₁` to `δ₂`, or the slope at `-∞` decreases from `δ₁` to
`δ₂`, the weight `exp w` grows faster at that end, imposing faster decay on the weighted space,
and the index decreases by the number of eigenvalues
of the limit at that end in `[δ₁, δ₂)` or `[δ₂, δ₁)`, counted with multiplicity. When exactly one
eigenvalue `λ` is crossed, this is the dimension of its eigenspace
(`Module.End.pointSpectralSubspace_eq_eigenspace`). For small decay weights, with slopes
`δ⁻ < 0 < δ⁺` closer to `0` than every nonzero eigenvalue of the respective limits, the index is
`n⁻(A⁻) - n⁻(A⁺) - dim ker A⁺`: the kernel of the limit at `+∞` is counted as negative, and that
at `-∞` as positive
(`index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker`, in
`TauCeti.WeakDerivStep`).

For a constant scalar coefficient `a • id` the index is `dim E` when `δ⁺ < a < δ⁻`, `-dim E` when
`δ⁻ < a < δ⁺`, and `0` when `δ⁻` and `δ⁺` lie on the same side of `a`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_smul_id_sub_smul_id`). For `a = 0`
the unweighted operator `d/ds`, which is not Fredholm when `E ≠ 0`, becomes Fredholm of index
`-dim E` for decay weights and of index `dim E` for growth weights.

## Main results

* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id_iff`:
  `D_{A - c}` is Fredholm exactly when `δ±` are not eigenvalues of `A±`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id`:
  the index of `D_{A - c}` is `n(A⁻, δ⁻) - n(A⁺, δ⁺)`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_sub_smul_id_eq_index_sub_finrank_sub_finrank`:
  raising the slope at `+∞` or lowering it at `-∞` decreases the index by the number of
  eigenvalues crossed.
* `index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker`, in
  `TauCeti.WeakDerivStep`: small decay weights give the index `n⁻(A⁻) - n⁻(A⁺) - dim ker A⁺`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_smul_id_sub_smul_id`: the scalar example.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (the index on exponentially
  weighted spaces and its jumps at exceptional weights).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (the trajectory operator `d/ds + A(s)`).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33 (the index of `d/ds + A(s)` as a count of eigenvalues).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E} {Aminus Aplus : E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- Shifting a symmetric operator by a real scalar keeps it symmetric. -/
private theorem isSymmetric_sub_smul_id {B : E →L[ℝ] E} (hB : (B : E →ₗ[ℝ] E).IsSymmetric)
    (δ : ℝ) : ((B - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
  simpa using hB.sub (LinearMap.IsSymmetric.id.smul (conj_trivial δ))

/-- **The trajectory operator on exponentially weighted spaces is Fredholm exactly when the weight
slopes are not eigenvalues of the limits.** Let `A` be a continuous family of operators on a
finite-dimensional real inner product space with symmetric limits `A±` at `±∞`, and let `c` be a
continuous scalar function with limits `δ±` at `±∞`. Then the trajectory operator
`u ↦ u' + (A - c • id) u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm if and only if `δ⁻` is
not an eigenvalue of `A⁻` and `δ⁺` is not an eigenvalue of `A⁺`. -/
theorem isFredholm_trajectoryOperator_sub_smul_id_iff
    (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {c : ℝ → ℝ}
    {δminus δplus : ℝ} (hc : Continuous c) (hcbot : Tendsto c atBot (𝓝 δminus))
    (hctop : Tendsto c atTop (𝓝 δplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm ↔
      ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus ∧
        ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus := by
  -- `B - δ • id` is injective exactly when its kernel, the eigenspace of `B` at `δ`, vanishes.
  have hinj (B : E →L[ℝ] E) (δ : ℝ) :
      Function.Injective (B - δ • ContinuousLinearMap.id ℝ E) ↔
        ¬Module.End.HasEigenvalue (B : E →ₗ[ℝ] E) δ := by
    rw [Module.End.hasEigenvalue_iff, not_not, Module.End.eigenspace_def, LinearMap.ker_eq_bot]
    rfl
  rw [isFredholm_trajectoryOperator_iff (hA.sub (hc.smul continuous_const))
      (isSymmetric_sub_smul_id hsymminus δminus) (isSymmetric_sub_smul_id hsymplus δplus)
      (hbot.sub (hcbot.smul tendsto_const_nhds)) (htop.sub (hctop.smul tendsto_const_nhds)) AL hAL,
    hinj, hinj]

/-- **The index of the trajectory operator on exponentially weighted spaces.** Let `A` be a
continuous family of operators on a finite-dimensional real inner product space with symmetric
limits `A±` at `±∞`, and let `c` be a continuous scalar function with limits `δ±` at `±∞` which are
not eigenvalues of `A±`. Then the trajectory operator `u ↦ u' + (A - c • id) u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index the number of eigenvalues of `A⁻` below `δ⁻` minus the
number of eigenvalues of `A⁺` below `δ⁺`, counted with multiplicity.

For `c = w'` this operator is conjugate, by multiplication by `exp w`, to `u ↦ u' + A u` on the
spaces weighted by `exp w`. The limits `A±` need not be invertible. -/
theorem index_trajectoryOperator_sub_smul_id
    (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {c : ℝ → ℝ}
    {δminus δplus : ℝ} (hc : Continuous c) (hcbot : Tendsto c atBot (𝓝 δminus))
    (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio δminus)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio δplus)) := by
  -- A shifted limit `B - δ • id`, with `δ` not an eigenvalue of `B`, is injective, so it
  -- stretches norms by at least a fixed positive factor.
  have hbelow (B : E →L[ℝ] E) (δ : ℝ) (hδ : ¬Module.End.HasEigenvalue (B : E →ₗ[ℝ] E) δ) :
      ∃ α > 0, ∀ v, α * ‖v‖ ≤ ‖(B - δ • ContinuousLinearMap.id ℝ E) v‖ := by
    refine (B - δ • ContinuousLinearMap.id ℝ E).continuous.exists_pos_mul_norm_le
      (fun v hv hBv ↦ hδ (Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv⟩))
      (fun c _ v ↦ map_smul _ c v)
    rw [Module.End.mem_eigenspace_iff]
    simpa [sub_eq_zero] using hBv
  -- Its negative eigenvalues are the eigenvalues of `B` below `δ`, shifted by `-δ`.
  have hpss (B : E →L[ℝ] E) (δ : ℝ) :
      Module.End.pointSpectralSubspace
          ((B - δ • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) =
        Module.End.pointSpectralSubspace (B : E →ₗ[ℝ] E) (Iio δ) := by
    have h := Module.End.pointSpectralSubspace_sub_smul_id (A := (B : E →ₗ[ℝ] E))
      (Ω := Iio 0) δ
    rwa [preimage_sub_const_Iio, zero_add] at h
  obtain ⟨αminus, hαminus, hminus⟩ := hbelow Aminus δminus hδminus
  obtain ⟨αplus, hαplus, hplus⟩ := hbelow Aplus δplus hδplus
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
      (hA.sub (hc.smul continuous_const)) (isSymmetric_sub_smul_id hsymminus δminus)
      (isSymmetric_sub_smul_id hsymplus δplus)
      (lt_min hαminus hαplus)
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hminus v))
      (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hplus v))
      (hbot.sub (hcbot.smul tendsto_const_nhds)) (htop.sub (hctop.smul tendsto_const_nhds)) AL hAL,
    hpss, hpss]

/-- **The index jumps when a weight slope crosses an eigenvalue.** Compare two continuous scalar
functions `c₁` and `c₂` with limits `δ₁±` and `δ₂±` at `±∞`, where `δ₂⁻ ≤ δ₁⁻` and `δ₁⁺ ≤ δ₂⁺`, so
that the asymptotic exponential growth rate of the weight `exp w₂` with `w₂' = c₂` is at least that
of `exp w₁` at each end. Then the
index of `D_{A - c₂}` is that of `D_{A - c₁}` minus the number of eigenvalues of `A⁻` in
`[δ₂⁻, δ₁⁻)` and minus the number of eigenvalues of `A⁺` in `[δ₁⁺, δ₂⁺)`, counted with
multiplicity. -/
theorem index_trajectoryOperator_sub_smul_id_eq_index_sub_finrank_sub_finrank
    (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    {c₁ c₂ : ℝ → ℝ} {δminus₁ δplus₁ δminus₂ δplus₂ : ℝ}
    (hc₁ : Continuous c₁) (hcbot₁ : Tendsto c₁ atBot (𝓝 δminus₁))
    (hctop₁ : Tendsto c₁ atTop (𝓝 δplus₁))
    (hc₂ : Continuous c₂) (hcbot₂ : Tendsto c₂ atBot (𝓝 δminus₂))
    (hctop₂ : Tendsto c₂ atTop (𝓝 δplus₂))
    (hδminus₁ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus₁)
    (hδplus₁ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus₁)
    (hδminus₂ : ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) δminus₂)
    (hδplus₂ : ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) δplus₂)
    (hminus : δminus₂ ≤ δminus₁) (hplus : δplus₁ ≤ δplus₂)
    (AL₁ AL₂ : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL₁ : AL₁ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₁ s • ContinuousLinearMap.id ℝ E)
    (hAL₂ : AL₂ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c₂ s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL₂).index =
      (trajectoryOperator (p := 2) AL₁).index -
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Ico δminus₂ δminus₁)) -
        Module.finrank ℝ
          (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ico δplus₁ δplus₂)) := by
  rw [index_trajectoryOperator_sub_smul_id hA hsymminus hsymplus hbot htop hc₁ hcbot₁ hctop₁
      hδminus₁ hδplus₁ AL₁ hAL₁,
    index_trajectoryOperator_sub_smul_id hA hsymminus hsymplus hbot htop hc₂ hcbot₂ hctop₂
      hδminus₂ hδplus₂ AL₂ hAL₂,
    ← Iio_union_Ico_eq_Iio hminus, ← Iio_union_Ico_eq_Iio hplus,
    Module.End.finrank_pointSpectralSubspace_union (Iio_disjoint_Ici le_rfl |>.mono_right
      Ico_subset_Ici_self),
    Module.End.finrank_pointSpectralSubspace_union (Iio_disjoint_Ici le_rfl |>.mono_right
      Ico_subset_Ici_self)]
  push_cast
  ring

/-- **The index for small decay weights.** Let `δminus > 0` be smaller than the absolute value of
every negative eigenvalue of `A⁻`, let `δplus > 0` be smaller than every positive eigenvalue of
`A⁺`, and let `c` be a continuous scalar function with limits `-δminus` at `-∞` and `δplus` at
`+∞`, as for the slope of a decay weight equal to `δminus |s|` near `-∞` and to `δplus |s|` near
`+∞`. Then the index of `D_{A - c}` is the number of negative eigenvalues of `A⁻`, minus the
number of negative eigenvalues of `A⁺`, minus the dimension of the kernel of `A⁺`. -/
theorem index_trajectoryOperator_sub_smul_id_eq_finrank_sub_finrank_sub_finrank_ker
    (hA : Continuous A)
    (hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) {c : ℝ → ℝ}
    {δminus δplus : ℝ} (hδminus : 0 < δminus) (hδplus : 0 < δplus) (hc : Continuous c)
    (hcbot : Tendsto c atBot (𝓝 (-δminus))) (hctop : Tendsto c atTop (𝓝 δplus))
    (hgapminus : ∀ μ ∈ Ico (-δminus) 0, ¬Module.End.HasEigenvalue (Aminus : E →ₗ[ℝ] E) μ)
    (hgapplus : ∀ μ ∈ Ioc 0 δplus, ¬Module.End.HasEigenvalue (Aplus : E →ₗ[ℝ] E) μ)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0)) -
          Module.finrank ℝ (LinearMap.ker (Aplus : E →ₗ[ℝ] E)) := by
  rw [index_trajectoryOperator_sub_smul_id hA hsymminus hsymplus hbot htop hc hcbot hctop
      (hgapminus _ ⟨le_rfl, neg_lt_zero.2 hδminus⟩) (hgapplus _ ⟨hδplus, le_rfl⟩) AL hAL]
  -- At `-∞` no eigenvalue lies in `[-δminus, 0)`, so the count below `-δminus` is the count below
  -- `0`.
  have hminus : Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0) =
      Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio (-δminus)) := by
    rw [← Iio_union_Ico_eq_Iio (neg_nonpos.2 hδminus.le), Module.End.pointSpectralSubspace_union,
      Module.End.pointSpectralSubspace_eq_bot_iff.2 hgapminus, sup_bot_eq]
  -- At `+∞` the eigenvalues below `δplus` are the negative ones and `0`, whose eigenspace is the
  -- kernel.
  have hplus : Iio δplus = (Iio 0 ∪ {0}) ∪ Ioo 0 δplus := by
    rw [Iio_union_right, Iic_union_Ioo_eq_Iio hδplus]
  have hdisj : Disjoint (Iio (0 : ℝ)) {0} := disjoint_singleton_right.2 (lt_irrefl 0)
  have hdisj' : Disjoint (Iio (0 : ℝ) ∪ {0}) (Ioo 0 δplus) := by
    rw [Iio_union_right]
    exact disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx) hx'.1
  rw [hplus, Module.End.finrank_pointSpectralSubspace_union hdisj',
    Module.End.finrank_pointSpectralSubspace_union hdisj,
    Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hgapplus μ (Ioo_subset_Ioc_self hμ),
    hminus]
  rw [Module.End.pointSpectralSubspace_eq_eigenspace (mem_singleton 0) fun ν hν _ ↦ hν,
    RCLike.ofReal_zero, Module.End.eigenspace_zero, finrank_bot]
  push_cast
  ring

/-- **The scalar example.** For the constant coefficient `a • id` on a finite-dimensional real
inner product space `E` and a continuous scalar function `c` with limits `δ±` different from `a`,
the trajectory operator `u ↦ u' + (a - c) u` has index `dim E` when `δ⁺ < a < δ⁻`, `-dim E` when
`δ⁻ < a < δ⁺`, and `0` when `δ⁻` and `δ⁺` lie on the same side of `a`. In particular, for `a = 0`
the operator `d/ds`, which is not Fredholm on unweighted spaces when `E ≠ 0`, has index `-dim E`
for decay weights (`δ⁻ < 0 < δ⁺`) and `dim E` for growth weights (`δ⁺ < 0 < δ⁻`). -/
theorem index_trajectoryOperator_smul_id_sub_smul_id (a : ℝ) {c : ℝ → ℝ} {δminus δplus : ℝ}
    (hc : Continuous c) (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hminus : δminus ≠ a) (hplus : δplus ≠ a)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a • ContinuousLinearMap.id ℝ E - c s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index =
      (if a < δminus then (Module.finrank ℝ E : ℤ) else 0) -
        if a < δplus then (Module.finrank ℝ E : ℤ) else 0 := by
  classical
  have hcoe : ((a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) = a • LinearMap.id := by
    ext v
    simp
  -- `a • id` has the single eigenvalue `a`.
  have hpss (Ω : Set ℝ) : Module.End.pointSpectralSubspace (a • LinearMap.id : E →ₗ[ℝ] E) Ω =
      if a ∈ Ω then ⊤ else ⊥ := by
    exact Module.End.pointSpectralSubspace_smul_id a
  have hfin (δ : ℝ) :
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (a • LinearMap.id : E →ₗ[ℝ] E)
        (Iio δ)) : ℤ) = if a < δ then (Module.finrank ℝ E : ℤ) else 0 := by
    rw [hpss]
    by_cases h : a < δ
    · rw [ite_eq_left (mem_Iio.2 h), ite_eq_left h, finrank_top]
    · rw [ite_eq_right (mt mem_Iio.1 h), ite_eq_right h, finrank_bot, Nat.cast_zero]
  have hsym : ((a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    rw [hcoe]
    exact LinearMap.IsSymmetric.id.smul (conj_trivial a)
  have hev {δ : ℝ} (hδ : δ ≠ a) :
      ¬Module.End.HasEigenvalue ((a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) δ := by
    have hbot := hpss {δ}
    rw [hcoe]
    simp only [mem_singleton_iff, hδ.symm, ↓reduceIte,
      Module.End.pointSpectralSubspace_eq_bot_iff] at hbot
    exact hbot δ rfl
  rw [index_trajectoryOperator_sub_smul_id continuous_const hsym hsym tendsto_const_nhds
      tendsto_const_nhds hc hcbot hctop (hev hminus) (hev hplus) AL hAL,
    hcoe, hfin, hfin]

end TauCeti.WeakDerivStep
