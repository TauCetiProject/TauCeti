/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
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
forms `B : V →L⋆[𝕜] V →L[𝕜] 𝕜` whose Fréchet--Riesz operator `continuousLinearMapOfBilin B` is a
unit (in particular, coercive forms satisfying `c * ‖u‖ ^ 2 ≤ re (B u u)` for `0 < c`, by
`InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive`, and real `IsCoercive` forms via
`IsCoercive.isUnit_continuousLinearMapOfBilin`).

Parameterizing the constructions by the proposition `IsUnit (continuousLinearMapOfBilin B)` keeps
them independent of any coercivity constant and provides a single canonical forcing API shared by
both real variational spectral/semigroup theory and complex/real closed-form representation:
* `InnerProductSpace.continuousLinearEquivOfBilin`: the Lax--Milgram equivalence `V ≃L[𝕜] V`,
  whose inverse has operator norm at most `c⁻¹` whenever
  `c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖`;
* `InnerProductSpace.solutionOfFunctional`: the conjugate-linear dual-forcing solution map
  `StrongDual 𝕜 V →L⋆[𝕜] V` of norm at most `c⁻¹` solving `B u v = ℓ v`;
* `InnerProductSpace.formSolutionMap` and `InnerProductSpace.formSolutionOperator`: for a
  continuous linear map `j : V →L[𝕜] H` into a seminormed inner-product space `H`, the `𝕜`-linear
  `H`-forcing map `H →L[𝕜] V` solving `B u v = ⟪h, j v⟫_𝕜` and the induced bounded operator
  `j ∘ formSolutionMap : H →L[𝕜] H`, which is compact when `j` is compact, symmetric (and
  self-adjoint when `H` is a Hilbert space) when `B` is Hermitian, has nonnegative real quadratic
  form when `0 ≤ re (B u u)` (so `1 + S` is a unit on a Hilbert space `H`), has dense range on a
  Hilbert space `H` whenever `j` is injective with dense range, and under diagonal nondegeneracy
  `∀ u, B u u = 0 → u = 0` has kernel `(range j)ᗮ`, is nonzero when `j ≠ 0` and injective when `j`
  has dense range (on normed `H`), and has dense range on a Hilbert space `H`.

At `𝕜 = ℝ`, `IsCoercive.isUnit_continuousLinearMapOfBilin`,
`IsCoercive.eq_zero_of_apply_self_eq_zero`, `IsCoercive.continuousLinearEquivOfBilin_eq`, and
`IsCoercive.solutionOfFunctional_eq` bridge Mathlib's real `IsCoercive` API with the `RCLike`
constructions.

The same equation restricted to a subspace `S` has a Galerkin solution `w ∈ S`, characterised by
`B (u - w) y = 0` for every `y ∈ S`. Céa's lemma bounds its error by the best approximation error
in `S`, up to the factor `M / C`, where `M` bounds `B` and `C` is its coercivity constant; this is
how solutions of the equation on an increasing family of subspaces with dense union are shown to
converge.

## Main declarations

* `IsCoercive.solutionOfInner`, `IsCoercive.solutionOfFunctional`: real Lax--Milgram solution
  maps and uniqueness theorems.
* `InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive` and
  `InnerProductSpace.mul_norm_le_norm_continuousLinearMapOfBilin`: coercivity yields invertibility
  and a lower norm bound for `continuousLinearMapOfBilin B`.
* `InnerProductSpace.continuousLinearEquivOfBilin`: the `RCLike` Lax--Milgram equivalence for an
  invertible sesquilinear form.
* `InnerProductSpace.solutionOfFunctional`: conjugate-linear dual-forcing solution map over
  `RCLike` scalars, with norm bound `c⁻¹` under a lower norm bound `c * ‖u‖ ≤ ‖B♯ u‖`.
* `InnerProductSpace.formSolutionMap` and `InnerProductSpace.formSolutionOperator`: canonical
  `𝕜`-linear `H`-forcing solution map and induced operator on `H`, with norm bounds, compactness
  under compact `j`, Hermitian symmetry, nonnegativity of the real part of its quadratic form,
  kernel characterization `(range j)ᗮ`, nonvanishing and injectivity on normed `H`, and
  self-adjointness, dense range, and invertibility of `1 + S` on a Hilbert space `H`.
* `LinearMap.norm_sub_le_div_mul_norm_sub`: Céa's lemma, `‖u - w‖ ≤ M / C * ‖u - v‖` for the
  Galerkin solution `w` and every `v` in the subspace, where `M` bounds `B`.

## References

* P. D. Lax and A. N. Milgram, *Parabolic equations*, Contributions to the Theory of Partial
  Differential Equations, Annals of Mathematics Studies **33** (1954), 167--190.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.1.
* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier 14 (1964),
  345–444.
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

end IsCoercive

namespace LinearMap

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Céa's lemma.** Let `B` be a bilinear form with `B x y ≤ M ‖x‖ ‖y‖` and `C ‖x‖² ≤ B x x`
for some `C > 0`, and let `w` be a Galerkin approximation of `u` in a subspace `S`: `w ∈ S` and
`B (u - w) y = 0` for every `y ∈ S`. Then `w` is within the factor `M / C` of the best
approximation of `u` in `S`: `‖u - w‖ ≤ M / C * ‖u - v‖` for every `v ∈ S`. -/
theorem norm_sub_le_div_mul_norm_sub (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {C M : ℝ} (hC : 0 < C)
    (hle : ∀ x, C * ‖x‖ * ‖x‖ ≤ B x x) (hM : ∀ x y, B x y ≤ M * ‖x‖ * ‖y‖)
    {S : Submodule ℝ V} {u w v : V} (hw : w ∈ S) (hv : v ∈ S)
    (horth : ∀ y ∈ S, B (u - w) y = 0) : ‖u - w‖ ≤ M / C * ‖u - v‖ := by
  -- Galerkin orthogonality: `B (u - w) (u - w) = B (u - w) (u - v)`, since `v - w ∈ S`.
  have hsplit : B (u - w) (u - w) = B (u - w) (u - v) := by
    conv_lhs => rw [← sub_add_sub_cancel u v w, map_add]
    rw [sub_add_sub_cancel, horth _ (S.sub_mem hv hw), add_zero]
  have key : C * ‖u - w‖ * ‖u - w‖ ≤ M * ‖u - w‖ * ‖u - v‖ :=
    (hle _).trans (hsplit ▸ hM _ _)
  -- Coercivity and the bound at `u - v` give `C ≤ M` unless `‖u - v‖ = 0`.
  have hd : C * ‖u - v‖ * ‖u - v‖ ≤ M * ‖u - v‖ * ‖u - v‖ := (hle _).trans (hM _ _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hC]
  rcases (norm_nonneg (u - w)).eq_or_lt with h | h
  · rw [← h, zero_mul]
    rcases (norm_nonneg (u - v)).eq_or_lt with h' | h'
    · rw [← h', mul_zero]
    · have hCM : C ≤ M := le_of_mul_le_mul_right (by simpa only [mul_assoc] using hd)
        (mul_pos h' h')
      exact mul_nonneg (hC.le.trans hCM) h'.le
  · nlinarith

end LinearMap

namespace IsCoercive

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

section NormedSesq

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A vector where the diagonal real part of a coercive sesquilinear form (`0 < c`) is
nonpositive is zero. -/
theorem eq_zero_of_re_apply_self_nonpos_of_coercive (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (B u u)) {u : V} (hu : RCLike.re (B u u) ≤ 0) :
    u = 0 :=
  norm_eq_zero.mp <| (pow_eq_zero_iff two_ne_zero).mp <|
    le_antisymm (nonpos_of_mul_nonpos_right ((hB u).trans hu) hc) (sq_nonneg _)

end NormedSesq

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

/-- **The sesquilinear Lax--Milgram equivalence** over an `RCLike` field `𝕜`: an invertible
Fréchet--Riesz operator `continuousLinearMapOfBilin B` upgrades to a continuous `𝕜`-linear
equivalence `V ≃L[𝕜] V`. Because `hB` is a proposition, the equivalence depends only on `B`. -/
def continuousLinearEquivOfBilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) : V ≃L[𝕜] V :=
  ContinuousLinearEquiv.ofUnit hB.unit

/-- The underlying continuous linear map of `continuousLinearEquivOfBilin` is
`continuousLinearMapOfBilin B`. -/
@[simp]
theorem toContinuousLinearMap_continuousLinearEquivOfBilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) :
    (continuousLinearEquivOfBilin B hB : V →L[𝕜] V) = continuousLinearMapOfBilin B :=
  (rfl)

/-- Pairing `continuousLinearEquivOfBilin B hB u` against `v` evaluates `B u v`. -/
@[simp]
theorem continuousLinearEquivOfBilin_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (u v : V) :
    ⟪continuousLinearEquivOfBilin B hB u, v⟫_𝕜 = B u v :=
  continuousLinearMapOfBilin_apply B u v

/-- The inverse of the Lax--Milgram equivalence solves `B u v = ⟪f, v⟫_𝕜`. -/
@[simp]
theorem apply_continuousLinearEquivOfBilin_symm (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (f v : V) :
    B ((continuousLinearEquivOfBilin B hB).symm f) v = ⟪f, v⟫_𝕜 := by
  rw [← continuousLinearEquivOfBilin_apply B hB, ContinuousLinearEquiv.apply_symm_apply]

/-- Uniqueness of the solution of `B u v = ⟪f, v⟫_𝕜`. -/
theorem eq_continuousLinearEquivOfBilin_symm (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {f u : V}
    (hu : ∀ v : V, B u v = ⟪f, v⟫_𝕜) :
    u = (continuousLinearEquivOfBilin B hB).symm f := by
  rw [ContinuousLinearEquiv.eq_symm_apply]
  exact ext_inner_right 𝕜 fun v => by rw [continuousLinearEquivOfBilin_apply, hu v]

/-- Pointwise norm bound `‖e.symm f‖ ≤ c⁻¹ * ‖f‖` on the inverse equivalence from a lower norm
bound `c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖`. -/
theorem norm_continuousLinearEquivOfBilin_symm_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) (f : V) :
    ‖(continuousLinearEquivOfBilin B hB).symm f‖ ≤ c⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ hc]
  have h := hle ((continuousLinearEquivOfBilin B hB).symm f)
  rwa [← toContinuousLinearMap_continuousLinearEquivOfBilin B hB,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h

/-- Operator-norm bound `‖(e.symm : V →L[𝕜] V)‖ ≤ c⁻¹` from a lower norm bound on
`continuousLinearMapOfBilin B`. -/
theorem norm_continuousLinearEquivOfBilin_symm_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) :
    ‖((continuousLinearEquivOfBilin B hB).symm : V →L[𝕜] V)‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_continuousLinearEquivOfBilin_symm_apply_le B hB hc hle)

/-- **The sesquilinear dual-forcing solution map.** For an invertible bounded sesquilinear form `B`
(conjugate-linear in the first slot, linear in the second), `solutionOfFunctional B hB` is the
continuous conjugate-linear map `StrongDual 𝕜 V →L⋆[𝕜] V` sending `ℓ` to the unique `u` with
`∀ v, B u v = ℓ v`. -/
def solutionOfFunctional (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) : StrongDual 𝕜 V →L⋆[𝕜] V :=
  ((continuousLinearEquivOfBilin B hB).symm : V →L[𝕜] V).comp
    ((toDual 𝕜 V).symm : StrongDual 𝕜 V →L⋆[𝕜] V)

/-- `solutionOfFunctional` applies the inverse Lax--Milgram equivalence to the Fréchet--Riesz
representative of `ℓ`. -/
theorem solutionOfFunctional_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (ℓ : StrongDual 𝕜 V) :
    solutionOfFunctional B hB ℓ =
      (continuousLinearEquivOfBilin B hB).symm ((toDual 𝕜 V).symm ℓ) :=
  (rfl)

/-- On `toDual 𝕜 V f`, `solutionOfFunctional` agrees with the inverse Lax--Milgram equivalence. -/
@[simp]
theorem solutionOfFunctional_toDual (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (f : V) :
    solutionOfFunctional B hB (toDual 𝕜 V f) =
      (continuousLinearEquivOfBilin B hB).symm f := by
  simp [solutionOfFunctional_apply]

/-- Applying `B` to `solutionOfFunctional B hB ℓ` recovers the forcing functional `ℓ`. -/
@[simp]
theorem apply_solutionOfFunctional (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (ℓ : StrongDual 𝕜 V) :
    B (solutionOfFunctional B hB ℓ) = ℓ := by
  ext v
  rw [solutionOfFunctional_apply, apply_continuousLinearEquivOfBilin_symm, toDual_symm_apply]

/-- **Variational equation of `solutionOfFunctional`.** -/
theorem apply_solutionOfFunctional_eq (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (ℓ : StrongDual 𝕜 V) (v : V) :
    B (solutionOfFunctional B hB ℓ) v = ℓ v := by
  rw [apply_solutionOfFunctional]

/-- Uniqueness of the solution of `B u v = ℓ v` for a continuous linear functional `ℓ`. -/
theorem eq_solutionOfFunctional (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional B hB ℓ := by
  rw [solutionOfFunctional_apply]
  exact eq_continuousLinearEquivOfBilin_symm B hB fun v => by rw [hu v, toDual_symm_apply]

/-- Solving against the functional `B u` recovers `u`. -/
@[simp]
theorem solutionOfFunctional_bilin (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (u : V) :
    solutionOfFunctional B hB (B u) = u :=
  (eq_solutionOfFunctional B hB fun _ => rfl).symm

/-- **Sesquilinear Lax--Milgram existence and uniqueness** for arbitrary continuous linear
functionals over `RCLike` scalars. -/
theorem existsUnique_forall_apply_eq (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (ℓ : StrongDual 𝕜 V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional B hB ℓ, apply_solutionOfFunctional_eq B hB ℓ,
    fun _ hu => eq_solutionOfFunctional B hB hu⟩

/-- Pointwise norm bound `‖solutionOfFunctional B hB ℓ‖ ≤ c⁻¹ * ‖ℓ‖`. -/
theorem norm_solutionOfFunctional_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) (ℓ : StrongDual 𝕜 V) :
    ‖solutionOfFunctional B hB ℓ‖ ≤ c⁻¹ * ‖ℓ‖ := by
  calc
    ‖solutionOfFunctional B hB ℓ‖
        ≤ c⁻¹ * ‖(toDual 𝕜 V).symm ℓ‖ :=
          norm_continuousLinearEquivOfBilin_symm_apply_le B hB hc hle _
    _ = c⁻¹ * ‖ℓ‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Operator-norm bound `‖solutionOfFunctional B hB‖ ≤ c⁻¹`. -/
theorem norm_solutionOfFunctional_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) :
    ‖solutionOfFunctional B hB‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_solutionOfFunctional_apply_le B hB hc hle)

/-! #### `H`-forcing solution map and solution operator -/

section Forcing

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The `H`-forcing Lax--Milgram solution map** along `j : V →L[𝕜] H`: the `𝕜`-linear continuous
map `H →L[𝕜] V` sending `h` to the unique `u : V` with `∀ v, B u v = ⟪h, j v⟫_𝕜`. Both
`solutionOfFunctional` and `toSesqForm j` are conjugate-linear, so their composite is `𝕜`-linear. -/
def formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hB : IsUnit (continuousLinearMapOfBilin B))
    (j : V →L[𝕜] H) : H →L[𝕜] V :=
  (solutionOfFunctional B hB).comp (ContinuousLinearMap.toSesqForm j)

/-- `formSolutionMap` evaluates `solutionOfFunctional` on `v ↦ ⟪h, j v⟫_𝕜`. -/
theorem formSolutionMap_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hB : IsUnit (continuousLinearMapOfBilin B))
    (j : V →L[𝕜] H) (h : H) :
    formSolutionMap B hB j h = solutionOfFunctional B hB (ContinuousLinearMap.toSesqForm j h) :=
  (rfl)

/-- **The variational equation solved by `formSolutionMap`.** -/
@[simp]
theorem apply_formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hB : IsUnit (continuousLinearMapOfBilin B))
    (j : V →L[𝕜] H) (h : H) (v : V) :
    B (formSolutionMap B hB j h) v = ⟪h, j v⟫_𝕜 := by
  simp only [formSolutionMap_apply, apply_solutionOfFunctional,
    ContinuousLinearMap.toSesqForm_apply_coe, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

/-- Uniqueness of the solution of `B u v = ⟪h, j v⟫_𝕜`. -/
theorem eq_formSolutionMap (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hB : IsUnit (continuousLinearMapOfBilin B))
    (j : V →L[𝕜] H) {h : H} {u : V} (hu : ∀ v : V, B u v = ⟪h, j v⟫_𝕜) :
    u = formSolutionMap B hB j h := by
  rw [formSolutionMap_apply]
  apply eq_solutionOfFunctional B hB
  simpa only [ContinuousLinearMap.toSesqForm_apply_coe, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] using hu

/-- Pointwise norm bound `‖formSolutionMap B hB j h‖ ≤ c⁻¹ * ‖j‖ * ‖h‖`. -/
theorem norm_formSolutionMap_apply_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) (j : V →L[𝕜] H) (h : H) :
    ‖formSolutionMap B hB j h‖ ≤ c⁻¹ * ‖j‖ * ‖h‖ := by
  calc
    ‖formSolutionMap B hB j h‖
        ≤ c⁻¹ * ‖ContinuousLinearMap.toSesqForm j h‖ :=
          norm_solutionOfFunctional_apply_le B hB hc hle _
    _ ≤ c⁻¹ * (‖j‖ * ‖h‖) := by
          gcongr
          exact ContinuousLinearMap.toSesqForm_apply_norm_le
    _ = c⁻¹ * ‖j‖ * ‖h‖ := by ring

/-- Operator-norm bound `‖formSolutionMap B hB j‖ ≤ c⁻¹ * ‖j‖`. -/
theorem norm_formSolutionMap_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) (j : V →L[𝕜] H) :
    ‖formSolutionMap B hB j‖ ≤ c⁻¹ * ‖j‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_formSolutionMap_apply_le B hB hc hle j)

/-- **The `H`-forcing solution operator** `j ∘ formSolutionMap : H →L[𝕜] H`, sending `h` to `j u`
where `u` solves `B u v = ⟪h, j v⟫_𝕜`. -/
def formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hB : IsUnit (continuousLinearMapOfBilin B))
    (j : V →L[𝕜] H) : H →L[𝕜] H :=
  j.comp (formSolutionMap B hB j)

/-- `formSolutionOperator` applies `j` to `formSolutionMap`. -/
theorem formSolutionOperator_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (j : V →L[𝕜] H) (h : H) :
    formSolutionOperator B hB j h = j (formSolutionMap B hB j h) :=
  (rfl)

/-- `formSolutionOperator` factors as `j ∘L formSolutionMap`. -/
theorem formSolutionOperator_eq_comp (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (j : V →L[𝕜] H) :
    formSolutionOperator B hB j = j.comp (formSolutionMap B hB j) :=
  (rfl)

/-- Operator-norm bound `‖formSolutionOperator B hB j‖ ≤ c⁻¹ * ‖j‖ ^ 2`. -/
theorem norm_formSolutionOperator_le (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {c : ℝ} (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖continuousLinearMapOfBilin B u‖) (j : V →L[𝕜] H) :
    ‖formSolutionOperator B hB j‖ ≤ c⁻¹ * ‖j‖ ^ 2 := by
  calc
    ‖formSolutionOperator B hB j‖
        ≤ ‖j‖ * ‖formSolutionMap B hB j‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖j‖ * (c⁻¹ * ‖j‖) := by
          gcongr
          exact norm_formSolutionMap_le B hB hc hle j
    _ = c⁻¹ * ‖j‖ ^ 2 := by ring

/-- When `j : V →L[𝕜] H` is a compact operator, `formSolutionOperator B hB j` is compact. -/
theorem isCompactOperator_formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {j : V →L[𝕜] H} (hj : IsCompactOperator j) :
    IsCompactOperator (formSolutionOperator B hB j) := by
  rw [formSolutionOperator_eq_comp]
  exact hj.comp_clm _

/-- The quadratic form of `formSolutionOperator` equals the energy of the variational solution. -/
theorem inner_formSolutionOperator_self (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (j : V →L[𝕜] H) (h : H) :
    ⟪h, formSolutionOperator B hB j h⟫_𝕜 =
      B (formSolutionMap B hB j h) (formSolutionMap B hB j h) :=
  (apply_formSolutionMap B hB j h _).symm

/-- The real part of `⟪h, formSolutionOperator h⟫` is nonnegative whenever `0 ≤ re (B u u)` for
all `u`. -/
theorem re_inner_formSolutionOperator_self_nonneg (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hpos : ∀ u, 0 ≤ RCLike.re (B u u))
    (j : V →L[𝕜] H) (h : H) :
    0 ≤ RCLike.re ⟪h, formSolutionOperator B hB j h⟫_𝕜 := by
  rw [inner_formSolutionOperator_self]
  exact hpos _

/-- If `B` is Hermitian (`B u v = star (B v u)`), the solution operator on `H` is symmetric. -/
theorem isSymmetric_formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (j : V →L[𝕜] H)
    (hHermitian : ∀ u v : V, B u v = star (B v u)) :
    LinearMap.IsSymmetric (formSolutionOperator B hB j : H →ₗ[𝕜] H) := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, formSolutionOperator_apply]
  calc
    ⟪j (formSolutionMap B hB j x), y⟫_𝕜
        = star ⟪y, j (formSolutionMap B hB j x)⟫_𝕜 := (inner_conj_symm _ _).symm
    _ = star (B (formSolutionMap B hB j y) (formSolutionMap B hB j x)) := by
          rw [apply_formSolutionMap]
    _ = B (formSolutionMap B hB j x) (formSolutionMap B hB j y) :=
          (hHermitian _ _).symm
    _ = ⟪x, j (formSolutionMap B hB j y)⟫_𝕜 := apply_formSolutionMap B hB j x _

/-- When `B` has no nonzero isotropic vectors (`B u u = 0 → u = 0`), the quadratic form of
`formSolutionOperator` vanishes at `h` if and only if `formSolutionOperator` kills `h`. -/
theorem inner_formSolutionOperator_self_eq_zero_iff (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    (j : V →L[𝕜] H) (h : H) :
    ⟪h, formSolutionOperator B hB j h⟫_𝕜 = 0 ↔ formSolutionOperator B hB j h = 0 := by
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, inner_zero_right]⟩
  rw [inner_formSolutionOperator_self] at h0
  rw [formSolutionOperator_apply, hdef _ h0, map_zero]

/-- When `B` has no nonzero isotropic vectors (`B u u = 0 → u = 0`), the solution operator kills
precisely the vectors orthogonal to the range of `j`. -/
theorem formSolutionOperator_apply_eq_zero_iff (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    (j : V →L[𝕜] H) (h : H) :
    formSolutionOperator B hB j h = 0 ↔ ∀ v : V, ⟪h, j v⟫_𝕜 = 0 := by
  constructor
  · intro hzero v
    have hself : B (formSolutionMap B hB j h) (formSolutionMap B hB j h) = 0 := by
      rw [← inner_formSolutionOperator_self, hzero, inner_zero_right]
    rw [← apply_formSolutionMap B hB j h v, hdef _ hself, map_zero, zero_apply]
  · intro horth
    have hsol : (0 : V) = formSolutionMap B hB j h :=
      eq_formSolutionMap B hB j fun v => by rw [horth v, map_zero, zero_apply]
    rw [formSolutionOperator_apply, ← hsol, map_zero]

end Forcing

section NormedTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The solution operator is nonzero whenever `j ≠ 0` and `B` has no nonzero isotropic vectors. -/
theorem formSolutionOperator_ne_zero (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    {j : V →L[𝕜] H} (hj : j ≠ 0) :
    formSolutionOperator B hB j ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : V, j w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hj
  intro hzero
  have hjw : formSolutionOperator B hB j (j w) = 0 := by rw [hzero, zero_apply]
  exact hw (inner_self_eq_zero.mp
    ((formSolutionOperator_apply_eq_zero_iff B hB hdef j (j w)).mp hjw w))

/-- **The kernel of the solution operator** is the orthogonal complement of the range of `j` when
`B` has no nonzero isotropic vectors. -/
theorem ker_formSolutionOperator (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    (j : V →L[𝕜] H) :
    LinearMap.ker (formSolutionOperator B hB j : H →ₗ[𝕜] H) =
      (LinearMap.range (j : V →ₗ[𝕜] H))ᗮ := by
  ext h
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    formSolutionOperator_apply_eq_zero_iff B hB hdef j h, Submodule.mem_orthogonal]
  constructor
  · rintro hh - ⟨v, rfl⟩
    exact inner_eq_zero_symm.mp (hh v)
  · intro hh v
    exact inner_eq_zero_symm.mp (hh (j v) ⟨v, rfl⟩)

/-- When `j` has dense range and `B` has no nonzero isotropic vectors, `formSolutionOperator` is
injective. -/
theorem formSolutionOperator_injective (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    {j : V →L[𝕜] H} (hdense : DenseRange j) :
    Function.Injective (formSolutionOperator B hB j) := by
  intro h₁ h₂ hh
  have hsub : formSolutionOperator B hB j (h₁ - h₂) = 0 := by rw [map_sub, hh, sub_self]
  exact sub_eq_zero.mp (hdense.eq_zero_of_inner_left 𝕜
    ((formSolutionOperator_apply_eq_zero_iff B hB hdef j (h₁ - h₂)).mp hsub))

/-- On a Hilbert space `H`, `formSolutionOperator` has dense range whenever `j` has dense range
and `B` has no nonzero isotropic vectors. -/
theorem denseRange_formSolutionOperator [CompleteSpace H] (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    {j : V →L[𝕜] H} (hdense : DenseRange j) :
    DenseRange (formSolutionOperator B hB j) := by
  rw [DenseRange, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  have h0 : ⟪h, formSolutionOperator B hB j h⟫_𝕜 = 0 :=
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ h) hh
  exact formSolutionOperator_injective B hB hdef hdense <|
    ((inner_formSolutionOperator_self_eq_zero_iff B hB hdef j h).mp h0).trans (map_zero _).symm

/-- On a Hilbert space `H`, `formSolutionOperator` has dense range whenever `j` is injective with
dense range, without requiring diagonal nondegeneracy or Hermiticity of `B`. -/
theorem denseRange_formSolutionOperator_of_injective [CompleteSpace H] (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) {j : V →L[𝕜] H}
    (hj : Function.Injective j) (hdense : DenseRange j) :
    DenseRange (formSolutionOperator B hB j) := by
  rw [DenseRange, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  let e := continuousLinearEquivOfBilin B hB
  have hMap : ∀ g : H, formSolutionMap B hB j g = (e.symm : V →L[𝕜] V) (j.adjoint g) := fun g =>
    (eq_formSolutionMap B hB j fun v => by
      rw [ContinuousLinearEquiv.coe_coe, apply_continuousLinearEquivOfBilin_symm,
        ContinuousLinearMap.adjoint_inner_left]).symm
  have hker : j (((e.symm : V →L[𝕜] V).adjoint) (j.adjoint h)) = 0 := by
    refine ext_inner_left 𝕜 fun g => ?_
    rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, ← hMap g,
      ContinuousLinearMap.adjoint_inner_right, ← formSolutionOperator_apply]
    exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ g) hh
  have hadj : ((e.symm : V →L[𝕜] V).adjoint) (j.adjoint h) = 0 :=
    hj (hker.trans (map_zero j).symm)
  have hjh : j.adjoint h = 0 := by
    have hcomp : ((e : V →L[𝕜] V).adjoint).comp ((e.symm : V →L[𝕜] V).adjoint) =
        ContinuousLinearMap.id 𝕜 V := by
      rw [← ContinuousLinearMap.adjoint_comp, ContinuousLinearEquiv.comp_coe,
        ContinuousLinearEquiv.self_trans_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.adjoint_id]
    have := congrArg (fun f : V →L[𝕜] V => f (j.adjoint h)) hcomp
    simpa only [ContinuousLinearMap.comp_apply, hadj, map_zero,
      ContinuousLinearMap.id_apply] using this.symm
  exact hdense.eq_zero_of_inner_left 𝕜 fun v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, hjh, inner_zero_left]

/-- On a complete Hilbert space `H`, the solution operator of an invertible Hermitian form is
bounded self-adjoint. -/
theorem isSelfAdjoint_formSolutionOperator [CompleteSpace H] (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (j : V →L[𝕜] H)
    (hHermitian : ∀ u v : V, B u v = star (B v u)) :
    IsSelfAdjoint (formSolutionOperator B hB j) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_formSolutionOperator B hB j hHermitian)

/-- On a complete Hilbert space `H`, `1 + formSolutionOperator B hB j` is invertible whenever
`0 ≤ re (B u u)` for all `u`. -/
theorem isUnit_one_add_formSolutionOperator [CompleteSpace H] (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hpos : ∀ u, 0 ≤ RCLike.re (B u u))
    (j : V →L[𝕜] H) :
    IsUnit (1 + formSolutionOperator B hB j) := by
  refine ContinuousLinearMap.isUnit_of_coercive _ one_pos fun h => ?_
  have hS : 0 ≤ RCLike.re ⟪h, formSolutionOperator B hB j h⟫_𝕜 :=
    re_inner_formSolutionOperator_self_nonneg B hB hpos j h
  rw [one_mul, add_apply, one_apply_eq_self, inner_add_left, map_add, inner_self_eq_norm_sq,
    inner_re_symm]
  linarith

end NormedTarget

end Complete

end InnerProductSpace

/-! ### Compatibility of the real and `RCLike` Lax--Milgram APIs -/

namespace IsCoercive

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A coercive real bilinear form has no nonzero isotropic vectors. -/
theorem eq_zero_of_apply_self_eq_zero (hB : IsCoercive B) {u : V} (hu : B u u = 0) : u = 0 :=
  let ⟨c, hc, hle⟩ := hB
  InnerProductSpace.eq_zero_of_re_apply_self_nonpos_of_coercive B hc
    (fun v => by simpa only [RCLike.re_to_real, sq, mul_assoc] using hle v)
    (by rw [RCLike.re_to_real, hu])

end Normed

section Complete

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Over `ℝ`, a coercive bilinear form has invertible Fréchet--Riesz operator
`InnerProductSpace.continuousLinearMapOfBilin B`. -/
theorem isUnit_continuousLinearMapOfBilin (hB : IsCoercive B) :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin B) :=
  let ⟨c, hc, hle⟩ := hB
  InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive B hc fun u => by
    simpa only [RCLike.re_to_real, sq, mul_assoc] using hle u

/-- Over `ℝ`, Mathlib's `IsCoercive.continuousLinearEquivOfBilin` agrees with
`InnerProductSpace.continuousLinearEquivOfBilin`. -/
theorem continuousLinearEquivOfBilin_eq (hB : IsCoercive B) :
    hB.continuousLinearEquivOfBilin =
      InnerProductSpace.continuousLinearEquivOfBilin B hB.isUnit_continuousLinearMapOfBilin := by
  ext u
  exact ext_inner_right ℝ fun v => by
    rw [hB.continuousLinearEquivOfBilin_apply,
      InnerProductSpace.continuousLinearEquivOfBilin_apply]

/-- Over `ℝ`, `IsCoercive.solutionOfFunctional` agrees with
`InnerProductSpace.solutionOfFunctional`. -/
theorem solutionOfFunctional_eq (hB : IsCoercive B) :
    hB.solutionOfFunctional =
      InnerProductSpace.solutionOfFunctional B hB.isUnit_continuousLinearMapOfBilin := by
  ext ℓ
  exact (hB.eq_solutionOfFunctional
    (InnerProductSpace.apply_solutionOfFunctional_eq B hB.isUnit_continuousLinearMapOfBilin
      ℓ)).symm

end Complete

end IsCoercive
