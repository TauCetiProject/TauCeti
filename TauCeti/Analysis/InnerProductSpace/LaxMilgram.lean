/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.InnerProductSpace.Coercive

/-!
# Existence and uniqueness form of Lax--Milgram

Mathlib's Lax--Milgram theorem is packaged over `ℝ` as
`IsCoercive.continuousLinearEquivOfBilin`: a coercive continuous bilinear form
`B : V →L[ℝ] V →L[ℝ] ℝ` induces a continuous linear equivalence `V ≃L[ℝ] V` sending
`u` to the Riesz representative of the functional `v ↦ B u v`.

The variational formulation of coercive equations uses the corresponding solution API:
given a forcing functional `ℓ`, there is a unique `u` satisfying `B u v = ℓ v` for every test
vector `v`. This file records that existence/uniqueness form, both for forcing represented by a
vector `F` (`ℓ = ⟪F, ·⟫`) and for an arbitrary continuous linear functional, first for Mathlib's
real `IsCoercive` predicate and then over any `RCLike` scalar field `𝕜` for bounded sesquilinear
forms `B : V →L⋆[𝕜] V →L[𝕜] 𝕜` satisfying `c * ‖u‖ ^ 2 ≤ re (B u u)` (`0 < c`).

Over `RCLike` scalars, `InnerProductSpace.continuousLinearMapOfBilin B` is invertible by
`ContinuousLinearMap.isUnit_of_coercive`. Inverting it yields:
* `InnerProductSpace.continuousLinearEquivOfBilin`: the Lax--Milgram equivalence `V ≃L[𝕜] V`,
  whose inverse has operator norm at most `c⁻¹`;
* `InnerProductSpace.solutionOfFunctional`: the conjugate-linear dual-forcing solution map
  `StrongDual 𝕜 V →L⋆[𝕜] V` of norm at most `c⁻¹` solving `B u v = ℓ v`;
* `InnerProductSpace.formSolutionMap` and `InnerProductSpace.formSolutionOperator`: for a
  continuous linear map `j : V →L[𝕜] H` into a seminormed inner-product space `H`, the `𝕜`-linear
  `H`-forcing map `H →L[𝕜] V` of norm at most `c⁻¹ * ‖j‖` solving `B u v = ⟪h, j v⟫_𝕜` and the
  induced bounded operator `j ∘ formSolutionMap : H →L[𝕜] H` of norm at most `c⁻¹ * ‖j‖ ^ 2`,
  which is symmetric (and self-adjoint when `H` is complete) whenever `B` is Hermitian.

At `𝕜 = ℝ`, `IsCoercive.continuousLinearEquivOfBilin_eq` and
`IsCoercive.solutionOfFunctional_eq` identify the `RCLike` constructions with their real
counterparts.

## Main declarations

* `IsCoercive.solutionOfInner`, `IsCoercive.solutionOfFunctional`: real Lax--Milgram solution
  maps and uniqueness theorems.
* `InnerProductSpace.continuousLinearEquivOfBilin`: the `RCLike` Lax--Milgram equivalence.
* `InnerProductSpace.solutionOfFunctional`: conjugate-linear dual-forcing solution map over
  `RCLike` scalars, with norm bound `c⁻¹`.
* `InnerProductSpace.formSolutionMap` and `InnerProductSpace.formSolutionOperator`: `𝕜`-linear
  `H`-forcing solution map and induced operator on `H`, with norm bounds, Hermitian symmetry,
  positivity, and injectivity under dense range.

## References

* P. D. Lax and A. N. Milgram, *Parabolic equations*, Contributions to the Theory of Partial
  Differential Equations, Annals of Mathematics Studies **33** (1954), 167--190.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace IsCoercive

section Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A coercive form has nonnegative diagonal. -/
theorem apply_self_nonneg (hB : IsCoercive B) (v : V) : 0 ≤ B v v :=
  let ⟨C, hC, hle⟩ := hB
  (by positivity : 0 ≤ C * ‖v‖ * ‖v‖).trans (hle v)

end Seminormed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The solution supplied by Lax--Milgram for a represented forcing functional.

For `F : V`, `solutionOfInner hB F` is the unique vector `u` satisfying
`B u v = ⟪F, v⟫` for every `v`. -/
def solutionOfInner (hB : IsCoercive B) (F : V) : V :=
  hB.continuousLinearEquivOfBilin.symm F

/-- The represented-forcing solution is the inverse Lax--Milgram operator. -/
theorem solutionOfInner_def (hB : IsCoercive B) (F : V) :
    solutionOfInner hB F = hB.continuousLinearEquivOfBilin.symm F :=
  (rfl)

/-- Applying the Lax--Milgram equivalence to the represented-forcing solution returns the
forcing vector. -/
@[simp]
theorem continuousLinearEquivOfBilin_solutionOfInner (hB : IsCoercive B) (F : V) :
    hB.continuousLinearEquivOfBilin (solutionOfInner hB F) = F := by
  simp [solutionOfInner_def]

/-- Solving against the forcing represented by a Lax--Milgram image recovers the original
vector. -/
@[simp]
theorem solutionOfInner_continuousLinearEquivOfBilin (hB : IsCoercive B) (u : V) :
    solutionOfInner hB (hB.continuousLinearEquivOfBilin u) = u := by
  simp [solutionOfInner_def]

/-- The Lax--Milgram solution satisfies the variational equation. -/
@[simp]
theorem apply_solutionOfInner_eq_inner (hB : IsCoercive B) (F v : V) :
    B (solutionOfInner hB F) v = ⟪F, v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply, continuousLinearEquivOfBilin_solutionOfInner]

/-- A vector satisfying the represented variational equation is the Lax--Milgram solution. -/
theorem eq_solutionOfInner (hB : IsCoercive B) {F u : V} (hu : ∀ v : V, B u v = ⟪F, v⟫_ℝ) :
    u = solutionOfInner hB F := by
  rw [solutionOfInner_def, ContinuousLinearEquiv.eq_symm_apply]
  exact (hB.unique_continuousLinearEquivOfBilin fun v => (hu v).symm).symm

/-- Lax--Milgram as an existence-and-uniqueness theorem for represented functionals.

If `B` is coercive, then for every `F : V` there is a unique `u` such that
`B u v = ⟪F, v⟫` for all test vectors `v`. -/
theorem existsUnique_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃! u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  ⟨solutionOfInner hB F, apply_solutionOfInner_eq_inner hB F,
    fun _ hu => eq_solutionOfInner hB hu⟩

/-- Lax--Milgram as an existence theorem for represented functionals. -/
theorem exists_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃ u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  (existsUnique_forall_eq_inner hB F).exists

/-- The Lax--Milgram solution map on continuous linear functionals, as a continuous linear map.

It sends `ℓ` to the unique vector `u` satisfying `B u v = ℓ v` for every `v`: this is
`solutionOfInner` applied to the Fréchet--Riesz representative of `ℓ`. -/
def solutionOfFunctional (hB : IsCoercive B) : StrongDual ℝ V →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The functional solution is obtained by solving against the Fréchet--Riesz representative. -/
theorem solutionOfFunctional_apply (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    solutionOfFunctional hB ℓ =
      solutionOfInner hB ((InnerProductSpace.toDual ℝ V).symm ℓ) :=
  (rfl)

/-- For represented functionals, the functional solution agrees with `solutionOfInner`. -/
@[simp]
theorem solutionOfFunctional_toDual (hB : IsCoercive B) (F : V) :
    solutionOfFunctional hB ((InnerProductSpace.toDual ℝ V) F) = solutionOfInner hB F := by
  simp [solutionOfFunctional_apply]

/-- The Lax--Milgram solution for a continuous linear functional satisfies the variational
equation. -/
@[simp]
theorem apply_solutionOfFunctional_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (solutionOfFunctional hB ℓ) v = ℓ v := by
  rw [solutionOfFunctional_apply, apply_solutionOfInner_eq_inner,
    InnerProductSpace.toDual_symm_apply]

/-- A vector satisfying the variational equation for a continuous linear functional is the
Lax--Milgram solution for that functional. -/
theorem eq_solutionOfFunctional (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional hB ℓ := by
  rw [solutionOfFunctional_apply]
  exact eq_solutionOfInner hB fun v => by rw [hu, InnerProductSpace.toDual_symm_apply]

/-- Lax--Milgram as an existence-and-uniqueness theorem for arbitrary continuous linear
functionals. -/
theorem existsUnique_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional hB ℓ, apply_solutionOfFunctional_eq hB ℓ,
    fun _ hu => eq_solutionOfFunctional hB hu⟩

/-- Lax--Milgram as an existence theorem for arbitrary continuous linear functionals. -/
theorem exists_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V, B u v = ℓ v :=
  (existsUnique_forall_eq hB ℓ).exists

end IsCoercive

/-! ### Sesquilinear Lax--Milgram over `RCLike` scalars -/

namespace InnerProductSpace

section SeminormedSesq

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A sesquilinear form whose diagonal real part dominates `c * ‖u‖ ^ 2` (`0 ≤ c`) has nonnegative
diagonal real part. -/
theorem re_apply_self_nonneg_of_coercive (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (u : V) :
    0 ≤ RCLike.re (B u u) :=
  (mul_nonneg hc (sq_nonneg ‖u‖)).trans (hB u)

end SeminormedSesq

section Complete

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- A coercive lower bound on `re (B u u)` bounds the Fréchet--Riesz operator of `B` below by
`c * ‖u‖`. -/
theorem mul_norm_le_norm_continuousLinearMapOfBilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (u : V) :
    c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖ :=
  ContinuousLinearMap.mul_norm_le_norm_apply_of_coercive (continuousLinearMapOfBilin B)
    (fun z => by simpa only [continuousLinearMapOfBilin_apply] using hB z) u

/-- **Sesquilinear Lax--Milgram invertibility.** For a bounded sesquilinear form `B` on a Hilbert
space with `c * ‖u‖ ^ 2 ≤ re (B u u)` (`0 < c`), the Fréchet--Riesz operator
`continuousLinearMapOfBilin B` is a unit. -/
theorem isUnit_continuousLinearMapOfBilin_of_coercive (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    IsUnit (continuousLinearMapOfBilin B) :=
  ContinuousLinearMap.isUnit_of_coercive (continuousLinearMapOfBilin B) hc
    fun z => by simpa only [continuousLinearMapOfBilin_apply] using hB z

/-- **The sesquilinear Lax--Milgram equivalence** over an `RCLike` field `𝕜`: a bounded
sesquilinear form `B` with `c * ‖u‖ ^ 2 ≤ re (B u u)` (`0 < c`) upgrades
`continuousLinearMapOfBilin B` to a continuous `𝕜`-linear equivalence `V ≃L[𝕜] V`. -/
def continuousLinearEquivOfBilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) : V ≃L[𝕜] V :=
  let hunit := isUnit_continuousLinearMapOfBilin_of_coercive B hc hB
  ContinuousLinearEquiv.equivOfInverse (continuousLinearMapOfBilin B)
    (↑hunit.unit⁻¹ : V →L[𝕜] V)
    (fun x => ContinuousLinearMap.ext_iff.mp hunit.val_inv_mul x)
    (fun x => ContinuousLinearMap.ext_iff.mp hunit.mul_val_inv x)

/-- The underlying continuous linear map of `continuousLinearEquivOfBilin` is
`continuousLinearMapOfBilin B`. -/
@[simp]
theorem toContinuousLinearMap_continuousLinearEquivOfBilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    (continuousLinearEquivOfBilin B hc hB : V →L[𝕜] V) = continuousLinearMapOfBilin B :=
  (rfl)

/-- The sesquilinear Lax--Milgram equivalence is independent of the choice of coercivity constant
and witness. -/
theorem continuousLinearEquivOfBilin_congr (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hB₁ : ∀ u, c₁ * ‖u‖ ^ 2 ≤ RCLike.re (B u u))
    (hc₂ : 0 < c₂) (hB₂ : ∀ u, c₂ * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    continuousLinearEquivOfBilin B hc₁ hB₁ = continuousLinearEquivOfBilin B hc₂ hB₂ := by
  ext
  rfl

/-- Pairing `continuousLinearEquivOfBilin B hc hB u` against `v` evaluates `B u v`. -/
@[simp]
theorem continuousLinearEquivOfBilin_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (u v : V) :
    ⟪continuousLinearEquivOfBilin B hc hB u, v⟫_𝕜 = B u v :=
  continuousLinearMapOfBilin_apply B u v

/-- The inverse of the Lax--Milgram equivalence solves `B u v = ⟪f, v⟫_𝕜`. -/
@[simp]
theorem apply_continuousLinearEquivOfBilin_symm (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (f v : V) :
    B ((continuousLinearEquivOfBilin B hc hB).symm f) v = ⟪f, v⟫_𝕜 := by
  rw [← continuousLinearEquivOfBilin_apply B hc hB, ContinuousLinearEquiv.apply_symm_apply]

/-- Uniqueness of the solution of `B u v = ⟪f, v⟫_𝕜`. -/
theorem eq_continuousLinearEquivOfBilin_symm (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) {f u : V}
    (hu : ∀ v : V, B u v = ⟪f, v⟫_𝕜) :
    u = (continuousLinearEquivOfBilin B hc hB).symm f := by
  rw [ContinuousLinearEquiv.eq_symm_apply]
  exact ext_inner_right 𝕜 fun v => by rw [continuousLinearEquivOfBilin_apply, hu v]

/-- Pointwise norm bound `‖e.symm f‖ ≤ c⁻¹ * ‖f‖` on the inverse Lax--Milgram equivalence. -/
theorem norm_continuousLinearEquivOfBilin_symm_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (f : V) :
    ‖(continuousLinearEquivOfBilin B hc hB).symm f‖ ≤ c⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ hc]
  have h := mul_norm_le_norm_continuousLinearMapOfBilin B hB
    ((continuousLinearEquivOfBilin B hc hB).symm f)
  rwa [← toContinuousLinearMap_continuousLinearEquivOfBilin B hc hB,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h

/-- Operator-norm bound `‖(e.symm : V →L[𝕜] V)‖ ≤ c⁻¹`. -/
theorem norm_continuousLinearEquivOfBilin_symm_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    ‖((continuousLinearEquivOfBilin B hc hB).symm : V →L[𝕜] V)‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_continuousLinearEquivOfBilin_symm_apply_le B hc hB)

/-- **The sesquilinear dual-forcing solution map.** For a coercive bounded sesquilinear form `B`
(conjugate-linear in the first slot, linear in the second), `solutionOfFunctional B hc hB` is the
continuous conjugate-linear map `StrongDual 𝕜 V →L⋆[𝕜] V` sending `ℓ` to the unique `u` with
`∀ v, B u v = ℓ v`. -/
def solutionOfFunctional (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) : StrongDual 𝕜 V →L⋆[𝕜] V :=
  ((continuousLinearEquivOfBilin B hc hB).symm : V →L[𝕜] V).comp
    ((toDual 𝕜 V).symm : StrongDual 𝕜 V →L⋆[𝕜] V)

/-- `solutionOfFunctional` applies the inverse Lax--Milgram equivalence to the Fréchet--Riesz
representative of `ℓ`. -/
theorem solutionOfFunctional_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (ℓ : StrongDual 𝕜 V) :
    solutionOfFunctional B hc hB ℓ =
      (continuousLinearEquivOfBilin B hc hB).symm ((toDual 𝕜 V).symm ℓ) :=
  (rfl)

/-- `solutionOfFunctional` is independent of the choice of coercivity constant and witness. -/
theorem solutionOfFunctional_congr (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hB₁ : ∀ u, c₁ * ‖u‖ ^ 2 ≤ RCLike.re (B u u))
    (hc₂ : 0 < c₂) (hB₂ : ∀ u, c₂ * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    solutionOfFunctional B hc₁ hB₁ = solutionOfFunctional B hc₂ hB₂ := by
  ext ℓ
  simp only [solutionOfFunctional_apply, continuousLinearEquivOfBilin_congr B hc₁ hB₁ hc₂ hB₂]

/-- On `toDual 𝕜 V f`, `solutionOfFunctional` agrees with the inverse Lax--Milgram equivalence. -/
@[simp]
theorem solutionOfFunctional_toDual (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (f : V) :
    solutionOfFunctional B hc hB (toDual 𝕜 V f) =
      (continuousLinearEquivOfBilin B hc hB).symm f := by
  simp [solutionOfFunctional_apply]

/-- **Variational equation of `solutionOfFunctional`.** -/
@[simp]
theorem apply_solutionOfFunctional_eq (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (ℓ : StrongDual 𝕜 V) (v : V) :
    B (solutionOfFunctional B hc hB ℓ) v = ℓ v := by
  rw [solutionOfFunctional_apply, apply_continuousLinearEquivOfBilin_symm, toDual_symm_apply]

/-- Uniqueness of the solution of `B u v = ℓ v` for a continuous linear functional `ℓ`. -/
theorem eq_solutionOfFunctional (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional B hc hB ℓ := by
  rw [solutionOfFunctional_apply]
  exact eq_continuousLinearEquivOfBilin_symm B hc hB fun v => by rw [hu v, toDual_symm_apply]

/-- **Sesquilinear Lax--Milgram existence and uniqueness** for arbitrary continuous linear
functionals over `RCLike` scalars. -/
theorem existsUnique_forall_apply_eq (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (ℓ : StrongDual 𝕜 V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional B hc hB ℓ, apply_solutionOfFunctional_eq B hc hB ℓ,
    fun _ hu => eq_solutionOfFunctional B hc hB hu⟩

/-- Pointwise norm bound `‖solutionOfFunctional B hc hB ℓ‖ ≤ c⁻¹ * ‖ℓ‖`. -/
theorem norm_solutionOfFunctional_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (ℓ : StrongDual 𝕜 V) :
    ‖solutionOfFunctional B hc hB ℓ‖ ≤ c⁻¹ * ‖ℓ‖ := by
  calc
    ‖solutionOfFunctional B hc hB ℓ‖
        ≤ c⁻¹ * ‖(toDual 𝕜 V).symm ℓ‖ :=
          norm_continuousLinearEquivOfBilin_symm_apply_le B hc hB _
    _ = c⁻¹ * ‖ℓ‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Operator-norm bound `‖solutionOfFunctional B hc hB‖ ≤ c⁻¹`. -/
theorem norm_solutionOfFunctional_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    ‖solutionOfFunctional B hc hB‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_solutionOfFunctional_apply_le B hc hB)

/-! #### `H`-forcing solution map and solution operator -/

section Forcing

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The `H`-forcing Lax--Milgram solution map** along `j : V →L[𝕜] H`: the `𝕜`-linear continuous
map `H →L[𝕜] V` sending `h` to the unique `u : V` with `∀ v, B u v = ⟪h, j v⟫_𝕜`. Both
`solutionOfFunctional` and `toSesqForm j` are conjugate-linear, so their composite is `𝕜`-linear. -/
def formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) : H →L[𝕜] V :=
  (solutionOfFunctional B hc hB).comp (ContinuousLinearMap.toSesqForm j)

/-- `formSolutionMap` evaluates `solutionOfFunctional` on `v ↦ ⟪h, j v⟫_𝕜`. -/
theorem formSolutionMap_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    formSolutionMap B hc hB j h =
      solutionOfFunctional B hc hB (ContinuousLinearMap.toSesqForm j h) :=
  (rfl)

/-- `formSolutionMap` is independent of the choice of coercivity constant and witness. -/
theorem formSolutionMap_congr (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hB₁ : ∀ u, c₁ * ‖u‖ ^ 2 ≤ RCLike.re (B u u))
    (hc₂ : 0 < c₂) (hB₂ : ∀ u, c₂ * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) :
    formSolutionMap B hc₁ hB₁ j = formSolutionMap B hc₂ hB₂ j := by
  ext h
  simp only [formSolutionMap_apply, solutionOfFunctional_congr B hc₁ hB₁ hc₂ hB₂]

/-- **The variational equation solved by `formSolutionMap`.** -/
@[simp]
theorem apply_formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) (v : V) :
    B (formSolutionMap B hc hB j h) v = ⟪h, j v⟫_𝕜 := by
  simp only [formSolutionMap_apply, apply_solutionOfFunctional_eq,
    ContinuousLinearMap.toSesqForm_apply_coe, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

/-- Uniqueness of the solution of `B u v = ⟪h, j v⟫_𝕜`. -/
theorem eq_formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) {h : H} {u : V}
    (hu : ∀ v : V, B u v = ⟪h, j v⟫_𝕜) :
    u = formSolutionMap B hc hB j h := by
  rw [formSolutionMap_apply]
  apply eq_solutionOfFunctional B hc hB
  simpa only [ContinuousLinearMap.toSesqForm_apply_coe, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] using hu

/-- Pointwise norm bound `‖formSolutionMap B hc hB j h‖ ≤ c⁻¹ * ‖j‖ * ‖h‖`. -/
theorem norm_formSolutionMap_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    ‖formSolutionMap B hc hB j h‖ ≤ c⁻¹ * ‖j‖ * ‖h‖ := by
  calc
    ‖formSolutionMap B hc hB j h‖
        ≤ c⁻¹ * ‖ContinuousLinearMap.toSesqForm j h‖ :=
          norm_solutionOfFunctional_apply_le B hc hB _
    _ ≤ c⁻¹ * (‖j‖ * ‖h‖) := by
          gcongr
          exact ContinuousLinearMap.toSesqForm_apply_norm_le
    _ = c⁻¹ * ‖j‖ * ‖h‖ := by ring

/-- Operator-norm bound `‖formSolutionMap B hc hB j‖ ≤ c⁻¹ * ‖j‖`. -/
theorem norm_formSolutionMap_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) :
    ‖formSolutionMap B hc hB j‖ ≤ c⁻¹ * ‖j‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_formSolutionMap_apply_le B hc hB j)

/-- **The `H`-forcing solution operator** `j ∘ formSolutionMap : H →L[𝕜] H`, sending `h` to `j u`
where `u` solves `B u v = ⟪h, j v⟫_𝕜`. -/
def formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) : H →L[𝕜] H :=
  j.comp (formSolutionMap B hc hB j)

/-- `formSolutionOperator` applies `j` to `formSolutionMap`. -/
theorem formSolutionOperator_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    formSolutionOperator B hc hB j h = j (formSolutionMap B hc hB j h) :=
  (rfl)

/-- `formSolutionOperator` factors as `j ∘L formSolutionMap`. -/
theorem formSolutionOperator_eq_comp (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) :
    formSolutionOperator B hc hB j = j.comp (formSolutionMap B hc hB j) :=
  (rfl)

/-- `formSolutionOperator` is independent of the choice of coercivity constant and witness. -/
theorem formSolutionOperator_congr (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hB₁ : ∀ u, c₁ * ‖u‖ ^ 2 ≤ RCLike.re (B u u))
    (hc₂ : 0 < c₂) (hB₂ : ∀ u, c₂ * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) :
    formSolutionOperator B hc₁ hB₁ j = formSolutionOperator B hc₂ hB₂ j := by
  ext h
  simp only [formSolutionOperator_apply, formSolutionMap_congr B hc₁ hB₁ hc₂ hB₂ j]

/-- Operator-norm bound `‖formSolutionOperator B hc hB j‖ ≤ c⁻¹ * ‖j‖ ^ 2`. -/
theorem norm_formSolutionOperator_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) :
    ‖formSolutionOperator B hc hB j‖ ≤ c⁻¹ * ‖j‖ ^ 2 := by
  calc
    ‖formSolutionOperator B hc hB j‖
        ≤ ‖j‖ * ‖formSolutionMap B hc hB j‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖j‖ * (c⁻¹ * ‖j‖) := by
          gcongr
          exact norm_formSolutionMap_le B hc hB j
    _ = c⁻¹ * ‖j‖ ^ 2 := by ring

/-- The quadratic form of `formSolutionOperator` equals the energy of the variational solution. -/
theorem inner_formSolutionOperator_self (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    ⟪h, formSolutionOperator B hc hB j h⟫_𝕜 =
      B (formSolutionMap B hc hB j h) (formSolutionMap B hc hB j h) :=
  (apply_formSolutionMap B hc hB j h _).symm

/-- The real part of `⟪h, formSolutionOperator h⟫` is nonnegative. -/
theorem re_inner_formSolutionOperator_self_nonneg (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    0 ≤ RCLike.re ⟪h, formSolutionOperator B hc hB j h⟫_𝕜 := by
  rw [inner_formSolutionOperator_self]
  exact re_apply_self_nonneg_of_coercive B hc.le hB _

/-- If `B` is Hermitian (`B u v = star (B v u)`), the solution operator on `H` is symmetric. -/
theorem isSymmetric_formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H)
    (hHermitian : ∀ u v : V, B u v = star (B v u)) :
    LinearMap.IsSymmetric (formSolutionOperator B hc hB j : H →ₗ[𝕜] H) := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, formSolutionOperator_apply]
  calc
    ⟪j (formSolutionMap B hc hB j x), y⟫_𝕜
        = star ⟪y, j (formSolutionMap B hc hB j x)⟫_𝕜 := (inner_conj_symm _ _).symm
    _ = star (B (formSolutionMap B hc hB j y) (formSolutionMap B hc hB j x)) := by
          rw [apply_formSolutionMap]
    _ = B (formSolutionMap B hc hB j x) (formSolutionMap B hc hB j y) :=
          (hHermitian _ _).symm
    _ = ⟪x, j (formSolutionMap B hc hB j y)⟫_𝕜 := apply_formSolutionMap B hc hB j x _

/-- The solution operator kills precisely the vectors orthogonal to the range of `j`. -/
theorem formSolutionOperator_apply_eq_zero_iff (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H) (h : H) :
    formSolutionOperator B hc hB j h = 0 ↔ ∀ v : V, ⟪h, j v⟫_𝕜 = 0 := by
  constructor
  · intro hzero v
    have hself : B (formSolutionMap B hc hB j h) (formSolutionMap B hc hB j h) = 0 := by
      rw [← inner_formSolutionOperator_self, hzero, inner_zero_right]
    have hle := hB (formSolutionMap B hc hB j h)
    rw [hself, map_zero] at hle
    have hu0 : formSolutionMap B hc hB j h = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp
        (le_antisymm (nonpos_of_mul_nonpos_right hle hc) (sq_nonneg _)))
    rw [← apply_formSolutionMap B hc hB j h v, hu0, map_zero, zero_apply]
  · intro horth
    have hsol : (0 : V) = formSolutionMap B hc hB j h :=
      eq_formSolutionMap B hc hB j fun v => by rw [horth v, map_zero, zero_apply]
    rw [formSolutionOperator_apply, ← hsol, map_zero]

end Forcing

section NormedTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- When `j` has dense range, `formSolutionOperator` is injective. -/
theorem formSolutionOperator_injective (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) {j : V →L[𝕜] H} (hdense : DenseRange j) :
    Function.Injective (formSolutionOperator B hc hB j) := by
  intro h₁ h₂ hh
  have hsub : formSolutionOperator B hc hB j (h₁ - h₂) = 0 := by rw [map_sub, hh, sub_self]
  exact sub_eq_zero.mp (hdense.eq_zero_of_inner_left 𝕜
    ((formSolutionOperator_apply_eq_zero_iff B hc hB j (h₁ - h₂)).mp hsub))

/-- On a complete Hilbert space `H`, the solution operator of a Hermitian coercive form is
bounded self-adjoint. -/
theorem isSelfAdjoint_formSolutionOperator [CompleteSpace H] (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ}
    (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) (j : V →L[𝕜] H)
    (hHermitian : ∀ u v : V, B u v = star (B v u)) :
    IsSelfAdjoint (formSolutionOperator B hc hB j) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_formSolutionOperator B hc hB j hHermitian)

end NormedTarget

end Complete

end InnerProductSpace

/-! ### Compatibility of the real and `RCLike` Lax--Milgram APIs -/

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Over `ℝ`, Mathlib's `IsCoercive.continuousLinearEquivOfBilin` agrees with
`InnerProductSpace.continuousLinearEquivOfBilin`. -/
theorem continuousLinearEquivOfBilin_eq (hB : IsCoercive B) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    hB.continuousLinearEquivOfBilin = InnerProductSpace.continuousLinearEquivOfBilin B hc hle := by
  ext u
  exact ext_inner_right ℝ fun v => by
    rw [hB.continuousLinearEquivOfBilin_apply,
      InnerProductSpace.continuousLinearEquivOfBilin_apply]

/-- Over `ℝ`, `IsCoercive.solutionOfFunctional` agrees with
`InnerProductSpace.solutionOfFunctional`. -/
theorem solutionOfFunctional_eq (hB : IsCoercive B) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) :
    hB.solutionOfFunctional = InnerProductSpace.solutionOfFunctional B hc hle := by
  ext ℓ
  exact (hB.eq_solutionOfFunctional
    (InnerProductSpace.apply_solutionOfFunctional_eq B hc hle ℓ)).symm

end IsCoercive
