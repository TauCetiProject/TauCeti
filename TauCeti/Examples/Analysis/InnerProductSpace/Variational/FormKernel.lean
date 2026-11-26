/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormKernel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Checks for the kernel-orthogonal Poincaré connector

Two compact form pairs on `𝕜²` with `V = H` and `j = id`.

* The form `a = diag(1, -1)`, `a(u, v) = conj(u₁) v₁ - conj(u₂) v₂`, is not nonnegative:
  `q(e₂) = -1`. The vector `(1, 1)` has `q(1, 1) = 0` but does not lie in the form kernel `N`, since
  `a((1, 1), e₁) = 1`. So the hypothesis `q ≥ 0` is used in identifying `N` with `{q = 0}`
  (`TauCeti.CompactFormPair.mem_formKernel_iff_energy_eq_zero`).
* The zero form has `N = V`, so `W = (j N)ᗮ = 0` and the constrained sphere `S_W` is empty: the
  best constant `δ`, the minimum of `q` on `S_W`, is not defined. The `W = 0` clause
  (`TauCeti.CompactFormPair.finiteDimensional_of_orthogonal_eq_bot`) gives that `H` is finite
  dimensional, as it is.
-/

public section

noncomputable section

open RCLike ComplexConjugate

namespace TauCeti.FormKernelExamples

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The compact form pair on `𝕜²` with `j = id`, for a Hermitian form `a` with
`‖u‖² ≤ re a(u, u) + ω ‖u‖²`. -/
def idPair (a : EuclideanSpace 𝕜 (Fin 2) →L⋆[𝕜] EuclideanSpace 𝕜 (Fin 2) →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) (ω : ℝ)
    (hω : ∀ u, ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖u‖ ^ 2) :
    CompactFormPair 𝕜 (EuclideanSpace 𝕜 (Fin 2)) (EuclideanSpace 𝕜 (Fin 2)) where
  inclusion := ContinuousLinearMap.id 𝕜 _
  injective := Function.injective_id
  denseRange := Function.Surjective.denseRange Function.surjective_id
  isCompactOperator := (isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜)).2 inferInstance
  form := a
  hermitian := ha
  exists_shifted_coercive := ⟨1, one_pos, ω, fun u ↦ by simpa using hω u⟩

section idPair

variable (a : EuclideanSpace 𝕜 (Fin 2) →L⋆[𝕜] EuclideanSpace 𝕜 (Fin 2) →L[𝕜] 𝕜)
  (ha : ∀ u v, a u v = star (a v u)) (ω : ℝ) (hω : ∀ u, ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖u‖ ^ 2)

/-- The inclusion of `idPair` is the identity. -/
@[simp]
theorem idPair_inclusion : (idPair a ha ω hω).inclusion = ContinuousLinearMap.id 𝕜 _ :=
  (rfl)

/-- The form of `idPair a` is `a`. -/
@[simp]
theorem idPair_form : (idPair a ha ω hω).form = a :=
  (rfl)

end idPair

/-! ### `diag(1, -1)` -/

/-- The form `a(u, v) = ⟪u, diag(1, -1) v⟫ = conj(u₁) v₁ - conj(u₂) v₂` on `𝕜²`. -/
def diagOneNegOneForm : EuclideanSpace 𝕜 (Fin 2) →L⋆[𝕜] EuclideanSpace 𝕜 (Fin 2) →L[𝕜] 𝕜 :=
  ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := 𝕜) (Matrix.diagonal ![1, -1]))

/-- The values of the form `diag(1, -1)`. -/
@[simp]
theorem diagOneNegOneForm_apply (u v : EuclideanSpace 𝕜 (Fin 2)) :
    diagOneNegOneForm u v = conj (u 0) * v 0 - conj (u 1) * v 1 := by
  simp [diagOneNegOneForm, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec_diagonal, mul_comm]
  ring

/-- The compact form pair `(id, diag(1, -1))` on `𝕜²`, with shift `ω = 2`. -/
def diagOneNegOnePair :
    CompactFormPair 𝕜 (EuclideanSpace 𝕜 (Fin 2)) (EuclideanSpace 𝕜 (Fin 2)) :=
  idPair diagOneNegOneForm
    (fun u v ↦ by simp only [diagOneNegOneForm_apply]; simp [mul_comm]) 2 fun u ↦ by
      simp only [diagOneNegOneForm_apply, map_sub, RCLike.conj_mul, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two]
      norm_cast
      nlinarith [sq_nonneg ‖u 0‖, sq_nonneg ‖u 1‖]

/-- The energy of `diag(1, -1)` is `|u₁|² - |u₂|²`. -/
theorem energy_diagOneNegOnePair (u : EuclideanSpace 𝕜 (Fin 2)) :
    diagOneNegOnePair.energy u = ‖u 0‖ ^ 2 - ‖u 1‖ ^ 2 := by
  rw [CompactFormPair.energy_def, diagOneNegOnePair, idPair_form]
  simp only [diagOneNegOneForm_apply, map_sub, RCLike.conj_mul]
  norm_cast

/-- The energy of `diag(1, -1)` is not nonnegative: `q(e₂) = -1`. -/
example : diagOneNegOnePair.energy (EuclideanSpace.single (1 : Fin 2) (1 : 𝕜)) = -1 := by
  simp [energy_diagOneNegOnePair]

/-- `q(1, 1) = 0` for `diag(1, -1)`. -/
example : diagOneNegOnePair.energy (!₂[1, 1] : EuclideanSpace 𝕜 (Fin 2)) = 0 := by
  simp [energy_diagOneNegOnePair]

/-- `(1, 1)` is not in the form kernel of `diag(1, -1)`, although its energy vanishes. -/
example : (!₂[1, 1] : EuclideanSpace 𝕜 (Fin 2)) ∉ diagOneNegOnePair.formKernel := by
  rw [CompactFormPair.mem_formKernel]
  intro h
  have h1 := h (EuclideanSpace.single 0 1)
  simp [diagOneNegOnePair] at h1

/-! ### The zero form -/

/-- The compact form pair `(id, 0)` on `𝕜²`, with shift `ω = 1`. -/
def zeroPair : CompactFormPair 𝕜 (EuclideanSpace 𝕜 (Fin 2)) (EuclideanSpace 𝕜 (Fin 2)) :=
  idPair 0 (fun _ _ ↦ by simp) 1 fun _ ↦ by simp

/-- For the zero form, the form kernel is everything: `N = V`. -/
theorem formKernel_zeroPair : (zeroPair (𝕜 := 𝕜)).formKernel = ⊤ := by
  ext u
  simp only [CompactFormPair.mem_formKernel, Submodule.mem_top, iff_true]
  simp [zeroPair]

/-- For the zero form, `W = (j N)ᗮ = 0`. -/
theorem formKernelImage_orthogonal_zeroPair : (zeroPair (𝕜 := 𝕜)).formKernelImageᗮ = ⊥ := by
  rw [Submodule.orthogonal_eq_bot_iff, eq_top_iff]
  intro x _
  rw [CompactFormPair.mem_formKernelImage, formKernel_zeroPair]
  exact ⟨x, Submodule.mem_top, by simp [zeroPair]⟩

/-- For the zero form, the constrained sphere `S_W` of `W = (j N)ᗮ` is empty, so the best
constant `δ` is not defined. -/
example : (zeroPair (𝕜 := 𝕜)).unitConstraint (zeroPair (𝕜 := 𝕜)).formKernelImageᗮ = ∅ := by
  rw [formKernelImage_orthogonal_zeroPair, Set.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨hu, h1⟩ := CompactFormPair.mem_unitConstraint.1 hu
  rw [Submodule.mem_bot] at hu
  simp [hu] at h1

/-- The `W = 0` clause: `H` is finite dimensional. -/
example : FiniteDimensional 𝕜 (EuclideanSpace 𝕜 (Fin 2)) :=
  zeroPair.finiteDimensional_of_orthogonal_eq_bot formKernelImage_orthogonal_zeroPair

end TauCeti.FormKernelExamples
