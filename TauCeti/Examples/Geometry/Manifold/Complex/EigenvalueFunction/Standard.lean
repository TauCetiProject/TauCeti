/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction.Standard
public import TauCeti.Analysis.Complex.QuadraticLeviForm

/-!
# Examples: eigenvalue functions and the complex Laplacian of the standard metric

Relative to the standard Hermitian metric `ω` of a complex inner product space, as a Hermitian
metric on the complex manifold modelled on itself:

* `λ_ω[i∂∂bar |z|²] = 2e` and `Δ_ω |z|² = 2n`, and relative to `2ω` the same form has
  `λ_{2ω}[i∂∂bar |z|²] = e`: doubling the metric halves the eigenvalues;
* on `ℂⁿ⁺¹`, `λ_ω[i∂∂bar |z₁|²] = (2, 0, …, 0)`;
* on `ℂⁿ⁺¹`, `Δ_ω (x₁²) = 1` for `x₁ = Re z₁`, half the Euclidean Laplacian `2`;
* the pluriharmonic `Re z₁²` has `λ_ω[i∂∂bar (Re z₁²)] = 0` and `Δ_ω (Re z₁²) = 0`.
-/

public section

open Complex Module TauCeti
open scoped Manifold InnerProductSpace

namespace TauCeti.StandardHermitianMetricExamples

section NormSq

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- `λ_ω[i∂∂bar |z|²] = 2e`. -/
theorem relEigenvalueFunction_norm_sq (x : V) :
    relEigenvalueFunction V (standardHermitianMetric V) 0 (fun z ↦ ‖z‖ ^ 2) x = fun _ ↦ 2 := by
  have hh : (innerₛₗ ℂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ).IsSymm := ⟨fun u v ↦ inner_conj_symm v u⟩
  refine compatible_standardHermitianMetric.relEigenvalueFunction_eq_of_isRelEigenvalueVector
    (fun _ _ ↦ by simp) ?_ antitone_const
  rw [funext₂ (twoFormHermitianForm_standardHermitianMetric x),
    funext₂ (ddbarHermitianForm_zero_form_norm_sq x)]
  exact (isRelEigenvalueVector_smul_self_iff hh
    (fun v hv ↦ by simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv) 2).2 rfl

/-- `Δ_ω |z|² = 2n`. -/
example (x : V) :
    complexLaplacian V (standardHermitianMetric V) (fun z ↦ ‖z‖ ^ 2) x = 2 * finrank ℂ V := by
  have hφ : ContDiffAt ℝ 2 (fun z : V ↦ ‖z‖ ^ 2) x := by
    let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
    exact (contDiff_norm_sq ℝ).contDiffAt
  rw [compatible_standardHermitianMetric.complexLaplacian_eq_two_mul_sum
    (contMDiffAt_iff_contDiffAt.2 hφ) (stdOrthonormalBasis ℂ V)
    fun i j ↦ by simp [orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ V).orthonormal]]
  simp [manifoldLeviForm_eq_leviForm, leviForm_norm_sq]

/-- Doubling the metric halves the eigenvalues: `λ_{2ω}[i∂∂bar |z|²] = e`. -/
example (x : V) :
    relEigenvalueFunction V ((2 : ℝ) • standardHermitianMetric V) 0 (fun z ↦ ‖z‖ ^ 2) x = 1 := by
  rw [compatible_standardHermitianMetric.relEigenvalueFunction_smul_left (fun _ _ ↦ by simp)
    two_pos, relEigenvalueFunction_norm_sq]
  ext
  simp

end NormSq

section Coordinate

variable {n : ℕ}

local notation "ℂⁿ⁺¹" => EuclideanSpace ℂ (Fin (n + 1))

/-- The Levi form of `|z₁|²` on `ℂⁿ⁺¹` is `L(v, w) = conj(v₁)·w₁`. -/
theorem leviForm_norm_sq_coord (x v w : ℂⁿ⁺¹) :
    leviForm (fun z : ℂⁿ⁺¹ ↦ ‖z 0‖ ^ 2) x v w = starRingEnd ℂ (v 0) * w 0 := by
  have hg : ContDiffAt ℝ 2 (fun w : ℂ ↦ ‖w‖ ^ 2) (x 0) := (contDiff_norm_sq ℝ).contDiffAt
  have hp : ContDiffAt ℂ 2 (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) x := by fun_prop
  have := leviForm_comp_apply (g := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) hg hp v w
  refine this.trans ?_
  rw [ContinuousLinearMap.fderiv, leviForm_norm_sq]
  simp [mul_comm]

/-- `λ_ω[i∂∂bar |z₁|²] = (2, 0, …, 0)` on `ℂⁿ⁺¹`. -/
example (x : ℂⁿ⁺¹) :
    relEigenvalueFunction ℂⁿ⁺¹ (standardHermitianMetric ℂⁿ⁺¹) 0 (fun z ↦ ‖z 0‖ ^ 2) x =
      fun i : Fin (finrank ℂ ℂⁿ⁺¹) ↦ if (i : ℕ) = 0 then (2 : ℝ) else 0 := by
  have hn : finrank ℂ ℂⁿ⁺¹ = n + 1 := finrank_euclideanSpace_fin
  refine compatible_standardHermitianMetric.relEigenvalueFunction_eq_of_isRelEigenvalueVector
    ?_ ((isRelEigenvalueVector_def _ _ _).2
      ⟨fun i ↦ EuclideanSpace.single (Fin.cast hn i) 1, fun i j ↦ ?_⟩) fun i j hij ↦ ?_
  · intro u v
    rfl
  · have hij : Fin.cast hn i = Fin.cast hn j ↔ i = j := (Fin.cast_injective hn).eq_iff
    refine ⟨?_, ?_⟩
    · simp only [twoFormHermitianForm_standardHermitianMetric, EuclideanSpace.inner_single_left,
        PiLp.single_apply, map_one, one_mul]
      simp [hij]
    · rw [ddbarHermitianForm_zero_form, manifoldLeviForm_eq_leviForm, leviForm_norm_sq_coord]
      simp only [PiLp.single_apply]
      by_cases h : i = j
      · subst h
        by_cases hi : (i : ℕ) = 0
        · simp [hi, Fin.ext_iff]
        · simp [hi, Fin.ext_iff]
          omega
      · have h' : (i : ℕ) ≠ j := fun e ↦ h (Fin.ext e)
        simp [h, Fin.ext_iff]
        omega
  · by_cases hj : (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by have := Fin.le_iff_val_le_val.1 hij; omega
      simp [hi, hj]
    · by_cases hi : (i : ℕ) = 0 <;> simp [hi, hj]

/-- `Δ_ω (x₁²) = 1` on `ℂⁿ⁺¹`, with `x₁ = Re z₁` the real part of the first coordinate: half the
Euclidean Laplacian `2` of `x₁²`. -/
example (x : ℂⁿ⁺¹) :
    complexLaplacian ℂⁿ⁺¹ (standardHermitianMetric ℂⁿ⁺¹) (fun z ↦ (z 0).re ^ 2) x = 1 := by
  have hg : ContDiffAt ℝ 2 (fun w : ℂ ↦ w.re ^ 2) (x 0) := (reCLM.contDiff.pow 2).contDiffAt
  have hp : ContDiffAt ℂ 2 (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) x := by fun_prop
  -- `(Re w)² = (1/2) |w|² + Re ((1/2) w²)`, a Hermitian plus holomorphic quadratic function.
  have hre : (fun w : ℂ ↦ w.re ^ 2) = fun w ↦
      (1 / 2 : ℝ) * ‖w‖ ^ 2 + (∑ _ : Unit, (1 / 2 : ℂ) * ContinuousLinearMap.id ℂ ℂ w ^ 2).re := by
    funext w
    rw [Complex.sq_norm, normSq_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, ContinuousLinearMap.id_apply, sq, mul_re]
    norm_num
    ring
  have h2 : leviForm (fun w : ℂ ↦ w.re ^ 2) (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1)) x) =
      ((1 / 2 : ℝ) : ℂ) • innerₛₗ ℂ := by
    rw [hre]
    exact leviForm_mul_norm_sq_add_re_sum_mul_sq _ _ _ _
  have hL (v w : ℂⁿ⁺¹) : leviForm (fun z : ℂⁿ⁺¹ ↦ (z 0).re ^ 2) x v w =
      (1 / 2 : ℂ) * (starRingEnd ℂ (v 0) * w 0) := by
    have := leviForm_comp_apply (g := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))) hg hp v w
    rw [h2] at this
    refine this.trans ?_
    rw [ContinuousLinearMap.fderiv]
    simp [mul_comm]
  have hφ : ContDiffAt ℝ 2 (fun z : ℂⁿ⁺¹ ↦ (z 0).re ^ 2) x :=
    show ContDiffAt ℝ 2 ((fun w : ℂ ↦ w.re ^ 2) ∘ EuclideanSpace.proj 0) x from
      hg.comp x (hp.restrict_scalars ℝ)
  have hn : finrank ℂ ℂⁿ⁺¹ = n + 1 := finrank_euclideanSpace_fin
  rw [compatible_standardHermitianMetric.complexLaplacian_eq_two_mul_sum
    (contMDiffAt_iff_contDiffAt.2 hφ) ((EuclideanSpace.basisFun _ ℂ).reindex (finCongr hn.symm))
    fun i j ↦ by
      simp [EuclideanSpace.inner_single_left, PiLp.single_apply]]
  simp only [manifoldLeviForm_eq_leviForm, hL]
  rw [Finset.sum_eq_single (Fin.cast hn.symm 0) (fun j _ hj ↦ ?_) (by simp)]
  · simp
  · have hj' : (0 : Fin (n + 1)) ≠ Fin.cast hn j := fun h ↦ hj (by ext; simp [h])
    simp [hj']

/-- The pluriharmonic `Re z₁²` has `Δ_ω (Re z₁²) = 0`. -/
example (x : ℂⁿ⁺¹) :
    complexLaplacian ℂⁿ⁺¹ (standardHermitianMetric ℂⁿ⁺¹) (fun z ↦ (z 0 ^ 2).re) x = 0 := by
  have hp : ContDiffAt ℂ 2 (fun z : ℂⁿ⁺¹ ↦ z 0 ^ 2) x :=
    ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).contDiff.pow 2).contDiffAt
  have hφ : ContDiffAt ℝ 2 (fun z : ℂⁿ⁺¹ ↦ (z 0 ^ 2).re) x :=
    reCLM.contDiff.contDiffAt.comp x (hp.restrict_scalars ℝ)
  rw [compatible_standardHermitianMetric.complexLaplacian_eq_two_mul_sum
    (contMDiffAt_iff_contDiffAt.2 hφ)
    (stdOrthonormalBasis ℂ ℂⁿ⁺¹)
    fun i j ↦ by simp [orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ ℂⁿ⁺¹).orthonormal]]
  simp [manifoldLeviForm_eq_leviForm, leviForm_re_eq_zero hp]

end Coordinate

end TauCeti.StandardHermitianMetricExamples
