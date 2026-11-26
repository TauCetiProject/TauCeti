/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction.Standard
public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Examples: eigenvalue functions and the complex Laplacian of the standard metric

Relative to the standard Hermitian metric `ω` of a complex inner product space, as a Hermitian
metric on the complex manifold modelled on itself:

* `λ_ω[i∂∂bar |z|²] = 2e` and `Δ_ω |z|² = 2n`, and relative to `2ω` the same form has
  `λ_{2ω}[i∂∂bar |z|²] = e`: doubling the metric halves the eigenvalues;
* on `ℂⁿ⁺¹`, `λ_ω[i∂∂bar |z₁|²] = (2, 0, …, 0)`;
* on `ℂⁿ⁺¹`, `Δ_ω (x₁²) = 1` for `x₁ = Re z₁`, half the Euclidean Laplacian `2`;
* the pluriharmonic `Re z₁²` has `Δ_ω (Re z₁²) = 0`.
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
  have h : ((2 : ℂ) • leviForm (fun z : V ↦ ‖z‖ ^ 2) x).IsSymm := by
    rw [leviForm_norm_sq]
    exact ⟨fun u v ↦ by simp [Complex.conj_ofNat]⟩
  rw [relEigenvalueFunction_standardHermitianMetric h]
  refine h.relEigenvalues_eq_of_orthonormalBasis rfl (stdOrthonormalBasis ℂ V) antitone_const
    fun i j ↦ ?_
  simp only [leviForm_norm_sq, LinearMap.smul_apply, innerₛₗ_apply_apply,
    OrthonormalBasis.inner_eq_ite, smul_eq_mul]
  split_ifs <;> simp

/-- `Δ_ω |z|² = 2n`. -/
example (x : V) :
    complexLaplacian V (standardHermitianMetric V) (fun z ↦ ‖z‖ ^ 2) x = 2 * finrank ℂ V := by
  have hφ : ContDiffAt ℝ 2 (fun z : V ↦ ‖z‖ ^ 2) x := by
    let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
    exact (contDiff_norm_sq ℝ).contDiffAt
  rw [complexLaplacian_standardHermitianMetric_eq_sum hφ (stdOrthonormalBasis ℂ V)]
  simp [leviForm_norm_sq]

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

/-- `λ_ω[i∂∂bar |z₁|²] = (2, 0, …, 0)` on `ℂⁿ⁺¹`. -/
example (x : ℂⁿ⁺¹) :
    relEigenvalueFunction ℂⁿ⁺¹ (standardHermitianMetric ℂⁿ⁺¹) 0 (fun z ↦ ‖z 0‖ ^ 2) x =
      fun i : Fin (finrank ℂ ℂⁿ⁺¹) ↦ if (i : ℕ) = 0 then (2 : ℝ) else 0 := by
  have hn : finrank ℂ ℂⁿ⁺¹ = n + 1 := finrank_euclideanSpace_fin
  refine compatible_standardHermitianMetric.relEigenvalueFunction_eq_of_isRelEigenvalueVector
    ?_ ((isRelEigenvalueVector_def _ _ _).2
      ⟨fun i ↦ EuclideanSpace.single (Fin.cast hn i) 1, fun i j ↦ ?_⟩) fun i j hij ↦ ?_
  · exact fun _ _ ↦ by simp
  · have hij : Fin.cast hn i = Fin.cast hn j ↔ i = j := (Fin.cast_injective hn).eq_iff
    refine ⟨?_, ?_⟩
    · simp only [twoFormHermitianForm_standardHermitianMetric, EuclideanSpace.inner_single_left,
        PiLp.single_apply, map_one, one_mul]
      simp [hij]
    · rw [ddbarHermitianForm_zero_form, manifoldLeviForm_eq_leviForm,
        leviForm_norm_sq_proj_apply]
      simp only [PiLp.single_apply]
      by_cases h : i = j
      · subst h
        by_cases hi : (i : ℕ) = 0
        · simp [hi, Fin.ext_iff]
        · have hi' : 0 ≠ Fin.cast hn i := fun e ↦ hi (by simpa using congrArg Fin.val e.symm)
          simp [hi, hi']
      · have hij' : 0 ≠ Fin.cast hn i ∨ 0 ≠ Fin.cast hn j := by
          by_contra! h'
          exact h (Fin.cast_injective hn (h'.1.symm.trans h'.2))
        rcases hij' with h' | h' <;> simp [h, h']
  · by_cases hj : (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by have := Fin.le_iff_val_le_val.1 hij; omega
      simp [hi, hj]
    · by_cases hi : (i : ℕ) = 0 <;> simp [hi, hj]

/-- `Δ_ω (x₁²) = 1` on `ℂⁿ⁺¹`, with `x₁ = Re z₁` the real part of the first coordinate: half the
Euclidean Laplacian `2` of `x₁²`. -/
example (x : ℂⁿ⁺¹) :
    complexLaplacian ℂⁿ⁺¹ (standardHermitianMetric ℂⁿ⁺¹) (fun z ↦ (z 0).re ^ 2) x = 1 := by
  have hφ : ContDiffAt ℝ 2 (fun z : ℂⁿ⁺¹ ↦ (z 0).re ^ 2) x :=
    ((reCLM.contDiff.comp (contDiff_piLp_apply 2)).pow 2).contDiffAt
  have hn : finrank ℂ ℂⁿ⁺¹ = n + 1 := finrank_euclideanSpace_fin
  rw [complexLaplacian_standardHermitianMetric_eq_sum hφ
    ((EuclideanSpace.basisFun _ ℂ).reindex (finCongr hn.symm))]
  simp only [leviForm_re_sq_proj_apply]
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
  rw [complexLaplacian_standardHermitianMetric_eq_sum hφ (stdOrthonormalBasis ℂ ℂⁿ⁺¹)]
  simp [leviForm_re_eq_zero hp]

end Coordinate

end TauCeti.StandardHermitianMetricExamples
