/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Riesz isomorphism and the positive dual metric

On a Hilbert space `E`, the Riesz isomorphism `InnerProductSpace.toDual 𝕜 E` is the map
`innerSL 𝕜 : E →L⋆[𝕜] StrongDual 𝕜 E`, upgraded to a conjugate-linear isometric equivalence. So its
inverse undoes `innerSL` on either side.

In finite dimension, `InnerProductSpace.dualMetric` is the positive Hermitian form on the
algebraic dual transported through Riesz duality. Since Riesz duality is conjugate-linear,
its formula reverses the two slots. For these metrics, the adjoint of the transpose
`T.dualMap` is the transpose of the Hermitian adjoint, `T.adjoint.dualMap`.
No inner product instance on the algebraic dual is installed.

## Main results

* `InnerProductSpace.toDual_symm_innerSL`: `(toDual 𝕜 E).symm (innerSL 𝕜 w) = w`.
* `InnerProductSpace.innerSL_toDual_symm`: `innerSL 𝕜 ((toDual 𝕜 E).symm q) = q`.
* `InnerProductSpace.apply_toDual_symm_eq_conj`: `β(α♯) = conj (α(β♯))`, writing `α♯` for
  `(toDual 𝕜 E).symm α`.
* `InnerProductSpace.apply_toDual_symm_self`: `q(q♯) = ‖q‖²`.
* `InnerProductSpace.toDualSymmL`: over `ℝ`, the inverse Riesz map `q ↦ q♯` as a continuous
  linear map.
* `InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner`: over `ℝ`, a bilinear form that is
  a nonzero multiple of the inner product is invertible as a map to the dual.
* `InnerProductSpace.continuousLinearMapOfBilin_innerSL`: the Riesz operator of the real inner
  product is the identity.
* `InnerProductSpace.dualMetric`: the Hermitian form on the algebraic dual transported by Riesz.
* `InnerProductSpace.dualMetric_innerₛₗ`: its value on Riesz functionals is `⟪y, x⟫`.
* `InnerProductSpace.isPosSemidef_dualMetric`: the dual metric is Hermitian and
  positive semidefinite.
* `InnerProductSpace.dualMetric_self_eq_zero_iff`: a functional has zero square norm iff it is zero.
* `LinearMap.dualMetric_dualMap_left`: transposition and Hermitian adjunction commute.
-/

public section

namespace InnerProductSpace

/-- The Riesz operator of the reference inner product is the identity. -/
@[simp]
theorem continuousLinearMapOfBilin_innerSL {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    continuousLinearMapOfBilin (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) = 1 := by
  ext v
  exact ext_inner_right ℝ fun w ↦ by simp

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section Complete

variable [CompleteSpace E]

/-- The inverse Riesz isomorphism sends the functional `innerSL 𝕜 w = ⟪w, ·⟫` back to `w`. -/
@[simp]
theorem toDual_symm_innerSL (w : E) : (toDual 𝕜 E).symm (innerSL 𝕜 w) = w :=
  (toDual 𝕜 E).symm_apply_eq.2 (by ext; simp)

/-- The functional `⟪(toDual 𝕜 E).symm q, ·⟫` represented by the inverse Riesz isomorphism is
`q`. -/
@[simp]
theorem innerSL_toDual_symm (q : StrongDual 𝕜 E) : innerSL 𝕜 ((toDual 𝕜 E).symm q) = q := by
  ext v; simp [toDual_symm_apply]

/-- Evaluating functionals at each other's Riesz representatives is conjugate-symmetric:
`β(α♯) = conj (α(β♯))`. Over `ℝ` this says `β(α♯) = α(β♯)`. -/
theorem apply_toDual_symm_eq_conj (α β : StrongDual 𝕜 E) :
    β ((toDual 𝕜 E).symm α) = starRingEnd 𝕜 (α ((toDual 𝕜 E).symm β)) := by
  rw [← toDual_symm_apply (y := β), ← toDual_symm_apply (y := α), inner_conj_symm]

/-- A functional evaluated at its own Riesz representative is its squared norm. -/
theorem apply_toDual_symm_self (q : StrongDual 𝕜 E) :
    q ((toDual 𝕜 E).symm q) = (‖q‖ : 𝕜) ^ 2 := by
  rw [← toDual_symm_apply, inner_self_eq_norm_sq_to_K, LinearIsometryEquiv.norm_map]

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- On a real Hilbert space the inverse Riesz isomorphism `q ↦ q♯ = (toDual ℝ F).symm q` is
linear; this is it as a continuous linear map. -/
noncomputable def toDualSymmL : StrongDual ℝ F →L[ℝ] F :=
  (toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem toDualSymmL_apply (q : StrongDual ℝ F) : toDualSymmL q = (toDual ℝ F).symm q :=
  (rfl)

/-- On a real Hilbert space, a bounded bilinear form `B(b, a) = c ⟪b, a⟫` with `c ≠ 0`, viewed as
a map to the dual, is invertible: it is `c` times the Riesz isomorphism. -/
theorem isInvertible_of_apply_apply_eq_mul_inner {c : ℝ} (hc : c ≠ 0)
    {B : F →L[ℝ] StrongDual ℝ F} (hB : ∀ b a, B b a = c * inner ℝ b a) : B.IsInvertible := by
  let e : F ≃L[ℝ] StrongDual ℝ F := (toDual ℝ F).toContinuousLinearEquiv
  refine ⟨(Units.mk0 c hc) • e,
    ContinuousLinearMap.ext fun b ↦ ContinuousLinearMap.ext fun a ↦ ?_⟩
  simpa [e] using (hB b a).symm

end Real

end Complete

section FiniteDimensional

variable (𝕜 E) [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The Hermitian metric on the algebraic dual transported through the conjugate-linear Riesz
isomorphism. Its value on `⟪x, ·⟫` and `⟪y, ·⟫` is `⟪y, x⟫`. -/
noncomputable def dualMetric : Module.Dual 𝕜 E →ₗ⋆[𝕜] Module.Dual 𝕜 E →ₗ[𝕜] 𝕜 :=
  let r : Module.Dual 𝕜 E →ₗ⋆[𝕜] E :=
    (toDual 𝕜 E).symm.toLinearEquiv.toLinearMap.comp
      LinearMap.toContinuousLinearMap.toLinearMap
  ((innerₛₗ 𝕜).flip.comp r).compl₂ r

/-- Evaluation of the dual metric in terms of the inverse Riesz isomorphism. -/
theorem dualMetric_apply (φ ψ : Module.Dual 𝕜 E) :
    dualMetric 𝕜 E φ ψ =
      inner 𝕜 ((toDual 𝕜 E).symm (LinearMap.toContinuousLinearMap ψ))
        ((toDual 𝕜 E).symm (LinearMap.toContinuousLinearMap φ)) :=
  (rfl)

/-- Riesz duality is antiunitary for the dual metric. -/
@[simp]
theorem dualMetric_innerₛₗ (x y : E) :
    dualMetric 𝕜 E (innerₛₗ 𝕜 x) (innerₛₗ 𝕜 y) = inner 𝕜 y x := by
  have h (z : E) : LinearMap.toContinuousLinearMap (innerₛₗ 𝕜 z) = toDual 𝕜 E z := by
    ext w
    simp
  simp [dualMetric_apply, h]

variable {𝕜 E}

/-- Every algebraic functional on a finite-dimensional inner product space is represented by
a unique vector. This is the algebraic form of Riesz representation. -/
theorem _root_.Module.Dual.existsUnique_innerₛₗ_eq (φ : Module.Dual 𝕜 E) :
    ∃! x : E, innerₛₗ 𝕜 x = φ := by
  obtain ⟨x, hx⟩ := (toDual 𝕜 E).surjective (LinearMap.toContinuousLinearMap φ)
  have hx' : innerₛₗ 𝕜 x = φ := by
    ext y
    exact DFunLike.congr_fun hx y
  refine ⟨x, hx', fun y hy ↦ ?_⟩
  apply (toDual 𝕜 E).injective
  ext z
  exact LinearMap.congr_fun (hy.trans hx'.symm) z

open scoped ComplexOrder

variable (𝕜 E)

/-- The transported dual metric is Hermitian and positive semidefinite. -/
theorem isPosSemidef_dualMetric : (dualMetric 𝕜 E).IsPosSemidef where
  eq φ ψ := by
    obtain ⟨x, rfl, _⟩ := φ.existsUnique_innerₛₗ_eq
    obtain ⟨y, rfl, _⟩ := ψ.existsUnique_innerₛₗ_eq
    simp [inner_conj_symm]
  nonneg φ := by
    obtain ⟨x, rfl, _⟩ := φ.existsUnique_innerₛₗ_eq
    simp

/-- The dual metric is definite, including on the zero space. -/
@[simp]
theorem dualMetric_self_eq_zero_iff (φ : Module.Dual 𝕜 E) :
    dualMetric 𝕜 E φ φ = 0 ↔ φ = 0 := by
  obtain ⟨x, rfl, _⟩ := φ.existsUnique_innerₛₗ_eq
  rw [dualMetric_innerₛₗ, inner_self_eq_zero]
  constructor
  · rintro rfl
    simp
  · intro h
    apply (toDual 𝕜 E).injective
    ext y
    simpa using LinearMap.congr_fun h y

variable {𝕜 E} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

local instance : CompleteSpace F := FiniteDimensional.complete 𝕜 F

/-- The transpose of an operator acts on Riesz functionals through its Hermitian adjoint. -/
@[simp]
theorem _root_.LinearMap.dualMap_innerₛₗ (T : E →ₗ[𝕜] F) (x : F) :
    T.dualMap (innerₛₗ 𝕜 x) = innerₛₗ 𝕜 (T.adjoint x) := by
  ext y
  exact (LinearMap.adjoint_inner_left T y x).symm

/-- Transposition and Hermitian adjunction commute for the transported dual metrics. -/
theorem _root_.LinearMap.dualMetric_dualMap_left (T : E →ₗ[𝕜] F)
    (φ : Module.Dual 𝕜 F) (ψ : Module.Dual 𝕜 E) :
    dualMetric 𝕜 E (T.dualMap φ) ψ = dualMetric 𝕜 F φ (T.adjoint.dualMap ψ) := by
  obtain ⟨x, rfl, _⟩ := φ.existsUnique_innerₛₗ_eq
  obtain ⟨y, rfl, _⟩ := ψ.existsUnique_innerₛₗ_eq
  simp only [LinearMap.dualMap_innerₛₗ, dualMetric_innerₛₗ, LinearMap.adjoint_adjoint]
  exact LinearMap.adjoint_inner_right T y x

end FiniteDimensional

end InnerProductSpace
