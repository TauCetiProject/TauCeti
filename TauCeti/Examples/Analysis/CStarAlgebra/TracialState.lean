/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.State.Tracial.Kernel
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Concrete examples and counterexamples for tracial states and trace kernels

This file illustrates `PositiveContinuousLinearMap.IsTracialState`, `TauCeti.tracialStateSpace`,
`PositiveContinuousLinearMap.IsFaithful`, and `PositiveContinuousLinearMap.traceKernel` on two
low-dimensional C⋆-algebras:

1. **The commutative two-point C⋆-algebra `Fin 2 → ℂ`:**
   * Coordinate evaluations `evalState i` are tracial states (`isTracialState_evalState`), but are
     not faithful (`not_isFaithful_evalState`): their trace kernels are the coordinate hyperplanes
     `{x | x i = 0}` (`mem_traceKernel_evalState_iff`).
   * The equal-weight average `midpointState` (`x ↦ (x 0 + x 1) / 2`) is a faithful tracial state
     with trivial trace kernel (`isFaithful_midpointState`, `traceKernel_midpointState`).

2. **The noncommutative `2 × 2` matrix C⋆-algebra `CStarMatrix (Fin 2) (Fin 2) ℂ`:**
   * The top-left entry functional `cornerState` (`M ↦ M 0 0`) is a state of operator norm `1`
     (`opNorm_cornerState`) that is not tracial (`not_isTracialState_cornerState`), separating
     `tracialStateSpace` from `stateSpace` (`tracialStateSpace_ne_stateSpace`). Moreover, the matrix
     unit `e01` satisfies `cornerState (star e01 * e01) = 0` while `e01 * e10 = e00` has
     `cornerState (star (e01 * e10) * (e01 * e10)) = 1` (`not_right_ideal_null_cornerState`),
     showing that `{a | φ (star a * a) = 0}` need not be a right ideal without traciality.
   * The unnormalized matrix trace `rawTrace₂` (`M ↦ M 0 0 + M 1 1`) is positive and tracial
     (`rawTrace₂_mul_comm`), yet is not a tracial state because `rawTrace₂ 1 = 2`
     (`not_isTracialState_rawTrace₂`).
   * The normalized matrix trace `normalizedTrace₂` (`M ↦ (M 0 0 + M 1 1) / 2`) is a faithful
     tracial state (`isTracialState_normalizedTrace₂`, `isFaithful_normalizedTrace₂`). Its trace
     kernel is `⊥`, whereas `LinearMap.ker normalizedTrace₂.toLinearMap` contains `e01` and is not
     closed under multiplication (`ker_normalizedTrace₂_not_mul_closed`).
   * Pulling `normalizedTrace₂` back along the nonunital corner embedding
     `cornerHom : ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ` (`z ↦ z • e00`) breaks the state
     normalization (`not_isTracialState_comp_cornerHom`), whereas pulling it back along the unital
     scalar inclusion `scalarHom : ℂ →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ` preserves tracial states
     (`isTracialState_comp_scalarHom`).
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.TracialStateExample

/-! ### Commutative two-point algebra `Fin 2 → ℂ` -/

/-- Evaluation at coordinate `i : Fin 2` as a positive continuous linear functional on
`Fin 2 → ℂ`. -/
def evalState (i : Fin 2) : (Fin 2 → ℂ) →P[ℂ] ℂ :=
  let L : (Fin 2 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i
  .ofClass <| PositiveLinearMap.mk₀ L fun _ hx => by simpa [L] using Pi.le_def.mp hx i

/-- Coordinate evaluation acts by `evalState i x = x i`. -/
@[simp]
theorem evalState_apply (i : Fin 2) (x : Fin 2 → ℂ) : evalState i x = x i := by
  simp [evalState]
  rfl

/-- Every coordinate evaluation on `Fin 2 → ℂ` is a tracial state. -/
theorem isTracialState_evalState (i : Fin 2) : (evalState i).IsTracialState := by
  rw [PositiveContinuousLinearMap.isTracialState_iff_map_one]
  exact ⟨by simp, fun a b => by rw [mul_comm]⟩

/-- The trace kernel of `evalState i` is the coordinate hyperplane `{x | x i = 0}`. -/
theorem mem_traceKernel_evalState_iff (i : Fin 2) (x : Fin 2 → ℂ) :
    x ∈ (evalState i).traceKernel (isTracialState_evalState i).mul_comm ↔ x i = 0 := by
  simp

/-- Coordinate evaluations on `Fin 2 → ℂ` are not faithful: a vector supported on the other
coordinate has zero `star x * x` mass under `evalState i`. -/
theorem not_isFaithful_evalState (i : Fin 2) : ¬ (evalState i).IsFaithful := by
  rw [PositiveContinuousLinearMap.isFaithful_iff]
  intro hf
  have h0 : Pi.single (M := fun _ : Fin 2 => ℂ) (i + 1) 1 = 0 := by
    apply hf
    fin_cases i <;> simp
  have h1 := congrFun h0 (i + 1)
  simp at h1

/-- The equal-weight average `x ↦ (x 0 + x 1) / 2` on `Fin 2 → ℂ`. -/
def midpointState : (Fin 2 → ℂ) →P[ℂ] ℂ :=
  let L : (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => (x 0 + x 1) / 2
      map_add' := fun x y => by simp; ring
      map_smul' := fun c x => by simp; ring }
  .ofClass <| PositiveLinearMap.mk₀ L fun x hx => by
    have hsum : (0 : ℂ) ≤ x 0 + x 1 := add_nonneg (hx 0) (hx 1)
    have hhalf : (0 : ℂ) ≤ (2 : ℂ)⁻¹ := by
      rw [Complex.nonneg_iff]
      norm_num
    simpa [L, div_eq_mul_inv] using mul_nonneg hsum hhalf

/-- `midpointState` evaluates as `(x 0 + x 1) / 2`. -/
@[simp]
theorem midpointState_apply (x : Fin 2 → ℂ) : midpointState x = (x 0 + x 1) / 2 := by
  simp [midpointState]
  rfl

/-- `midpointState` is a tracial state on `Fin 2 → ℂ`. -/
theorem isTracialState_midpointState : midpointState.IsTracialState := by
  rw [PositiveContinuousLinearMap.isTracialState_iff_map_one]
  exact ⟨by norm_num [midpointState_apply], fun a b => by rw [mul_comm]⟩

/-- `midpointState` is faithful on `Fin 2 → ℂ`. -/
theorem isFaithful_midpointState : midpointState.IsFaithful := by
  rw [PositiveContinuousLinearMap.isFaithful_iff]
  intro x hx
  simp only [midpointState_apply, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
    Pi.mul_apply, Pi.star_apply] at hx
  obtain ⟨h0, h1⟩ :=
    add_eq_zero_iff_of_nonneg (star_mul_self_nonneg (x 0)) (star_mul_self_nonneg (x 1)) |>.mp hx
  ext i
  fin_cases i <;> exact star_mul_self_eq_zero.mp ‹_›

/-- The trace kernel of `midpointState` is `⊥`. -/
@[simp]
theorem traceKernel_midpointState :
    midpointState.traceKernel isTracialState_midpointState.mul_comm = ⊥ :=
  (midpointState.traceKernel_eq_bot_iff _).mpr isFaithful_midpointState

/-! ### Noncommutative `2 × 2` matrix algebra `CStarMatrix (Fin 2) (Fin 2) ℂ` -/

/-- Matrix unit `e₀₀ = [[1, 0], [0, 0]]` in `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def e00 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![1, 0; 0, 0]

/-- Off-diagonal matrix unit `e₀₁ = [[0, 1], [0, 0]]` in `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def e01 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]

/-- Off-diagonal matrix unit `e₁₀ = [[0, 0], [1, 0]]` in `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def e10 : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 0; 1, 0]

/-- Diagonal entry functional `M ↦ M i i` on `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def diagFunctional (i : Fin 2) : CStarMatrix (Fin 2) (Fin 2) ℂ →P[ℂ] ℂ :=
  let L : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => by simp }
  .ofClass <| PositiveLinearMap.mk₀ L fun M hM => by
    -- Positivity is the quadratic-form criterion evaluated at the standard basis vector `e_i`.
    have h := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM (Pi.single i (1 : ℂ))
    fin_cases i <;> simpa [L, Fin.sum_univ_two] using h

/-- `diagFunctional i` reads the `(i, i)` entry. -/
@[simp]
theorem diagFunctional_apply (i : Fin 2) (M : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    diagFunctional i M = M i i := by
  simp [diagFunctional]
  rfl

/-- The top-left corner state `M ↦ M 0 0` on `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
abbrev cornerState : CStarMatrix (Fin 2) (Fin 2) ℂ →P[ℂ] ℂ := diagFunctional 0

/-- `cornerState` has operator norm `1`, hence defines a state on `CStarMatrix (Fin 2) (Fin 2) ℂ`.
-/
@[simp]
theorem opNorm_cornerState :
    ‖(cornerState : CStarMatrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ)‖ = 1 := by
  apply Complex.ofReal_injective
  rw [cornerState.ofReal_opNorm_eq_map_one]
  simp [diagFunctional_apply]

/-- `cornerState` belongs to `stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ)`. -/
theorem cornerState_mem_stateSpace :
    StrongDual.toWeakDual (cornerState : CStarMatrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ) ∈
      stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  rw [PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff]
  exact opNorm_cornerState

/-- `cornerState` is not tracial: `cornerState (e01 * e10) = 1 ≠ 0 = cornerState (e10 * e01)`. -/
theorem not_isTracialState_cornerState : ¬ cornerState.IsTracialState := by
  intro h
  have hcomm := h.mul_comm e01 e10
  norm_num [e01, e10, diagFunctional_apply, CStarMatrix.mul_apply, Fin.sum_univ_two] at hcomm

/-- On `CStarMatrix (Fin 2) (Fin 2) ℂ`, the tracial state space is a strict subset of the state
space. -/
theorem tracialStateSpace_ne_stateSpace :
    tracialStateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ) ≠
      stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hmem :
      StrongDual.toWeakDual (cornerState : CStarMatrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ) ∈
        tracialStateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    h ▸ cornerState_mem_stateSpace
  exact not_isTracialState_cornerState
    ((PositiveContinuousLinearMap.toWeakDual_mem_tracialStateSpace_iff cornerState).mp hmem)

/-- Without traciality, the GNS null space `{M | cornerState (star M * M) = 0}` fails to absorb
right multiplication: `e01` lies in it, while `e01 * e10 = e00` does not. -/
theorem not_right_ideal_null_cornerState :
    cornerState (star e01 * e01) = 0 ∧ cornerState (star (e01 * e10) * (e01 * e10)) ≠ 0 := by
  constructor
  · norm_num [e01, diagFunctional_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]
  · norm_num [e01, e10, diagFunctional_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]

/-- The unnormalized matrix trace `M ↦ M 0 0 + M 1 1` on `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def rawTrace₂ : CStarMatrix (Fin 2) (Fin 2) ℂ →P[ℂ] ℂ :=
  diagFunctional 0 + diagFunctional 1

/-- `rawTrace₂` evaluates as `M 0 0 + M 1 1`. -/
@[simp]
theorem rawTrace₂_apply (M : CStarMatrix (Fin 2) (Fin 2) ℂ) : rawTrace₂ M = M 0 0 + M 1 1 := by
  simp [rawTrace₂]

/-- `rawTrace₂` satisfies the trace identity `rawTrace₂ (M * N) = rawTrace₂ (N * M)`. -/
theorem rawTrace₂_mul_comm (M N : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    rawTrace₂ (M * N) = rawTrace₂ (N * M) := by
  simp only [rawTrace₂_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `rawTrace₂` is positive and tracial, yet is not a tracial state because `rawTrace₂ 1 = 2 ≠ 1`.
-/
theorem not_isTracialState_rawTrace₂ : ¬ rawTrace₂.IsTracialState := by
  intro h
  have h1 := h.map_one
  norm_num [rawTrace₂_apply, CStarMatrix.one_apply] at h1

/-- The normalized matrix trace `M ↦ (M 0 0 + M 1 1) / 2` on `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def normalizedTrace₂ : CStarMatrix (Fin 2) (Fin 2) ℂ →P[ℂ] ℂ :=
  let L : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (M 0 0 + M 1 1) / 2
      map_add' := fun M N => by simp; ring
      map_smul' := fun c M => by simp; ring }
  .ofClass <| PositiveLinearMap.mk₀ L fun M hM => by
    have hsum : (0 : ℂ) ≤ M 0 0 + M 1 1 := by simpa [rawTrace₂_apply] using rawTrace₂.map_nonneg hM
    have hhalf : (0 : ℂ) ≤ (2 : ℂ)⁻¹ := by
      rw [Complex.nonneg_iff]
      norm_num
    simpa [L, div_eq_mul_inv] using mul_nonneg hsum hhalf

/-- `normalizedTrace₂` evaluates as `(M 0 0 + M 1 1) / 2`. -/
@[simp]
theorem normalizedTrace₂_apply (M : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    normalizedTrace₂ M = (M 0 0 + M 1 1) / 2 := by
  simp [normalizedTrace₂]
  rfl

/-- `normalizedTrace₂` is a tracial state on `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
theorem isTracialState_normalizedTrace₂ : normalizedTrace₂.IsTracialState := by
  rw [PositiveContinuousLinearMap.isTracialState_iff_map_one]
  refine ⟨by norm_num [normalizedTrace₂_apply, CStarMatrix.one_apply], fun M N => ?_⟩
  have h := rawTrace₂_mul_comm M N
  simp only [rawTrace₂_apply] at h
  simp only [normalizedTrace₂_apply, h]

/-- `normalizedTrace₂` is faithful on `CStarMatrix (Fin 2) (Fin 2) ℂ`: its value on `star M * M` is
half the squared Frobenius norm of `M`. -/
theorem isFaithful_normalizedTrace₂ : normalizedTrace₂.IsFaithful := by
  rw [PositiveContinuousLinearMap.isFaithful_iff]
  intro M hM
  simp only [normalizedTrace₂_apply, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
    CStarMatrix.mul_apply, CStarMatrix.star_apply] at hM
  rw [← Fin.sum_univ_two fun i => ∑ j : Fin 2, star (M j i) * M j i] at hM
  have hcol (i : Fin 2) : ∑ j : Fin 2, star (M j i) * M j i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      Finset.sum_nonneg fun j _ => star_mul_self_nonneg (M j k)).mp hM i (Finset.mem_univ i)
  ext j i
  exact star_mul_self_eq_zero.mp <|
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => star_mul_self_nonneg (M k i)).mp (hcol i) j
      (Finset.mem_univ j)

/-- The trace kernel of `normalizedTrace₂` is `⊥`. -/
@[simp]
theorem traceKernel_normalizedTrace₂ :
    normalizedTrace₂.traceKernel isTracialState_normalizedTrace₂.mul_comm = ⊥ :=
  (normalizedTrace₂.traceKernel_eq_bot_iff _).mpr isFaithful_normalizedTrace₂

/-- Unlike `normalizedTrace₂.traceKernel _ = ⊥`, the linear kernel
`LinearMap.ker normalizedTrace₂.toLinearMap` contains the off-diagonal unit `e01` yet does not
contain `e01 * e10`, so `LinearMap.ker` is not an ideal. -/
theorem ker_normalizedTrace₂_not_mul_closed :
    e01 ∈ LinearMap.ker normalizedTrace₂.toLinearMap ∧
      e01 * e10 ∉ LinearMap.ker normalizedTrace₂.toLinearMap := by
  constructor
  · rw [LinearMap.mem_ker]
    change normalizedTrace₂ e01 = 0
    norm_num [e01, normalizedTrace₂_apply]
  · rw [LinearMap.mem_ker]
    change normalizedTrace₂ (e01 * e10) ≠ 0
    norm_num [e01, e10, normalizedTrace₂_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- Nonunital corner `⋆`-homomorphism `z ↦ z • e₀₀` from `ℂ` into
`CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def cornerHom : ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ where
  toFun z := z • e00
  map_smul' c z := by simp [mul_smul]
  map_zero' := zero_smul _ _
  map_add' z w := add_smul z w e00
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e00, CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e00, CStarMatrix.star_apply]

/-- Pulling `normalizedTrace₂` back along the nonunital corner embedding `cornerHom` yields the
half-norm functional `z ↦ z / 2`, which is tracial and positive but not a state. -/
theorem not_isTracialState_comp_cornerHom :
    ¬ (normalizedTrace₂.comp (.ofClass cornerHom)).IsTracialState := by
  intro h
  have h1 := h.map_one
  have heval : (normalizedTrace₂.comp (.ofClass cornerHom)) 1 = (1 / 2 : ℂ) := by
    simp [cornerHom, e00, normalizedTrace₂_apply]
  rw [heval] at h1
  norm_num at h1

/-- Unital scalar `⋆`-homomorphism `z ↦ algebraMap ℂ _ z` into `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
def scalarHom : ℂ →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ :=
  { Algebra.ofId ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) with
    map_star' := fun z => by
      change algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) (star z) =
        star (algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) z)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one] }

/-- Pulling `normalizedTrace₂` back along the unital scalar embedding `scalarHom` yields the unique
tracial state on `ℂ`. -/
theorem isTracialState_comp_scalarHom :
    (normalizedTrace₂.comp (.ofClass scalarHom)).IsTracialState :=
  isTracialState_normalizedTrace₂.comp_unital scalarHom

end TauCeti.TracialStateExample
