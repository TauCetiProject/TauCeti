/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Trivialization
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Sobolev invertibility of the stationary cylinder operator at a Hamiltonian orbit

Let `(V, ω)` be a finite-dimensional symplectic space, `x` a `1`-periodic orbit of `H`, and
`Φ : ℝ → F →L[ℝ] V` a differentiable symplectic frame from a finite-dimensional complex inner
product space `F` (`ω₀(v, w) = Im ⟪v, w⟫`). Pulling `S_t = dX_{H_t}(x(t))` back along `Φ` via
`TauCeti.trivializedCoeff` (`TauCeti/Analysis/ODE/FrameTrivialization.lean`) and realizing
`∂s + I (∂t - S_Φ)` on `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)` as `CircleSobolev.cylinderOperator 1 S` gives
unconditional injectivity (when each `H t` is `C²` at `x t`), equivalence of cylinder invertibility
and Fredholmness with fixed-point nondegeneracy of the time-one flow, and uniform inverse bounds for
`cylinderOperator 1 (S - δ • Jc)` near a nondegenerate orbit. Specializing to the identity frame on
`(F, ω)` with `ω(v, w) = Im ⟪v, w⟫` gives frame-free corollaries complementing
`isInvertible_loopOperator_iff_isNondegenerateFixedPt` and
`eventually_isInvertible_loopOperator_sub_smul`
(`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator.lean`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
-/

public section

noncomputable section

open TauCeti.CircleSobolev (cylinderOperator)
open Complex ContinuousLinearMap Filter Function Topology
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

section TrivializedOrbit

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- Unconditional injectivity of `cylinderOperator 1 S` along `x` where each `H t` is `C²` at `x t`
and `S` trivializes `dX_{H_t}(x(t))` in a differentiable invertible symplectic frame `Φ`. -/
theorem injective_cylinderOperator_of_trivializedCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {x : ℝ → V} (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t)) {Φ : ℝ → F →L[ℝ] V}
    (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    Function.Injective (cylinderOperator 1 S) :=
  CircleSobolev.injective_cylinderOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff hH hΦd hΦ hω hS)

/-- Along a `1`-periodic orbit `x` of a `1`-periodic, jointly `C²` Hamiltonian `H` with globally
Lipschitz suspended vector field, in a differentiable invertible `1`-periodic symplectic frame `Φ`,
`cylinderOperator 1 S` is invertible iff `x(0)` is a nondegenerate fixed point of the time-one
flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isInvertible_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
      (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- Along a `1`-periodic orbit `x` of a `1`-periodic, jointly `C²` Hamiltonian `H` with globally
Lipschitz suspended vector field, in a differentiable invertible `1`-periodic symplectic frame `Φ`,
`cylinderOperator 1 S` is Fredholm iff `x(0)` is a nondegenerate fixed point of the time-one
flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isFredholm_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
      (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- In a differentiable invertible `1`-periodic symplectic frame along a nondegenerate `1`-periodic
orbit of a `1`-periodic, jointly `C²` Hamiltonian with globally Lipschitz suspended vector field,
`cylinderOperator 1 (S - δ • Jc)` has inverse norm at most `C` for `|δ| ≤ ε`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator 1 (S - δ • Jc)).IsInvertible ∧
        ‖(cylinderOperator 1 (S - δ • Jc)).inverse‖ ≤ C := by
  open CircleSobolev in
  obtain ⟨ε, hε, C, hC, h⟩ :=
    exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isInvertible_loopOperator
      1 (isCompact_singleton (x := ())) (fun _ ↦ S) (fun _ ↦ Jc) continuousOn_const
      continuousOn_const (fun _ _ ↦ ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
        (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)
      (fun _ _ ↦ (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
        hX hH hHp hx hxp hΦd hΦp hΦ hS).2 hnd)
  exact ⟨ε, hε, C, hC, fun δ hδ ↦ h () rfl δ hδ⟩

/-- Filter form of perturbed cylinder invertibility in a differentiable invertible `1`-periodic
symplectic frame along a nondegenerate `1`-periodic orbit. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (cylinderOperator 1 (S - δ • Jc)).IsInvertible := by
  obtain ⟨ε, hε, _, _, h⟩ :=
    ω.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
      hX hH hHp hx hxp hnd hΦd hΦp hΦ hω hS Jc
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hε] with δ hδ
  exact (h δ (by simpa [Real.dist_eq] using hδ)).1

end TrivializedOrbit

section ComplexInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Frame-free unconditional injectivity of `cylinderOperator 1 S` on `(F, ω)` with
`ω(v, w) = Im ⟪v, w⟫` where each `H t` is `C²` at `x t`. -/
theorem injective_cylinderOperator (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {H : ℝ → F → ℝ} {x : ℝ → F} (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    Function.Injective (cylinderOperator 1 S) :=
  ω.injective_cylinderOperator_of_trivializedCoeff (Φ := fun _ ↦ .id ℝ F) hH
    (differentiable_const _) (fun _ ↦ isInvertible_equiv (f := .refl ℝ F)) (fun _ ↦ hω) fun t ↦ by
      simp [hS t]

/-- On `(F, ω)` (`ω(v, w) = Im ⟪v, w⟫`), along a `1`-periodic orbit of a `1`-periodic, jointly `C²`
Hamiltonian with globally Lipschitz suspension, `cylinderOperator 1 S` is invertible iff `x(0)` is
a nondegenerate fixed point of the time-one flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ .id ℝ F) hX hH hHp hx hxp (differentiable_const _) (fun _ ↦ rfl)
    (fun _ ↦ isInvertible_equiv (f := .refl ℝ F)) (fun _ ↦ hω) fun t ↦ by simp [hS t]

/-- On `(F, ω)` (`ω(v, w) = Im ⟪v, w⟫`), along a `1`-periodic orbit of a `1`-periodic, jointly `C²`
Hamiltonian with globally Lipschitz suspension, `cylinderOperator 1 S` is Fredholm iff `x(0)` is a
nondegenerate fixed point of the time-one flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ .id ℝ F) hX hH hHp hx hxp (differentiable_const _) (fun _ ↦ rfl)
    (fun _ ↦ isInvertible_equiv (f := .refl ℝ F)) (fun _ ↦ hω) fun t ↦ by simp [hS t]

/-- On `(F, ω)` (`ω(v, w) = Im ⟪v, w⟫`), along a nondegenerate `1`-periodic orbit of a `1`-periodic,
jointly `C²` Hamiltonian with globally Lipschitz suspension, `cylinderOperator 1 (S - δ • Jc)` has
uniformly bounded inverse for small `|δ|`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isNondegenerateFixedPt
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε → (cylinderOperator 1 (S - δ • Jc)).IsInvertible ∧
      ‖(cylinderOperator 1 (S - δ • Jc)).inverse‖ ≤ C :=
  ω.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
    (Φ := fun _ ↦ .id ℝ F) hX hH hHp hx hxp hnd (differentiable_const _) (fun _ ↦ rfl)
    (fun _ ↦ isInvertible_equiv (f := .refl ℝ F)) (fun _ ↦ hω) (fun t ↦ by simp [hS t]) Jc

/-- Filter form of frame-free perturbed cylinder invertibility on `(F, ω)` (`ω(v, w) = Im ⟪v, w⟫`)
along a nondegenerate `1`-periodic orbit for `δ` near `0`. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (cylinderOperator 1 (S - δ • Jc)).IsInvertible :=
  ω.eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff (Φ := fun _ ↦ .id ℝ F) hX
    hH hHp hx hxp hnd (differentiable_const _) (fun _ ↦ rfl)
    (fun _ ↦ isInvertible_equiv (f := .refl ℝ F)) (fun _ ↦ hω) (fun t ↦ by simp [hS t]) Jc

end ComplexInnerProductSpace

end TauCeti.SymplecticForm
