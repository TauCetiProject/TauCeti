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

Let `(V, ω)` be a finite-dimensional symplectic vector space, `x` a one-periodic orbit of a
time-dependent Hamiltonian `H`, and `Φ : ℝ → F →L[ℝ] V` a differentiable symplectic frame from a
finite-dimensional complex inner product space `F` (with symplectic form `ω₀(v, w) = Im ⟪v, w⟫`).
Pulling back the linearized Floer operator along `Φ` replaces `S_t = dX_{H_t}(x(t))` by the
trivialized loop coefficient `S_Φ(t) = Φ(t)⁻¹ (S_t Φ(t) - Φ'(t))`
(`TauCeti.Floer.trivializedCoeff` in
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Trivialization.lean`).

Realizing `∂s + I (∂t - S_Φ)` on the common-domain Sobolev space `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)` via
`TauCeti.CircleSobolev.cylinderOperator 1 S`:

1. **Unconditional injectivity.** Whenever each `H t` is `C²` at `x t`, `cylinderOperator 1 S` has
   trivial kernel even at a degenerate orbit
   (`TauCeti.SymplecticForm.injective_cylinderOperator_of_trivializedCoeff`,
   `TauCeti.SymplecticForm.injective_cylinderOperator`).
2. **Invertibility and Fredholm equivalences.** Along a one-periodic orbit `x` of a one-periodic,
   jointly `C²` Hamiltonian `H` trivialized by a one-periodic symplectic frame `Φ`,
   `cylinderOperator 1 S` is invertible — and equivalently Fredholm — if and only if `x(0)` is a
   nondegenerate fixed point of the time-one Hamiltonian flow
   (`SymplecticForm.isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`,
   `SymplecticForm.isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`).
3. **Uniform perturbed and weighted cylinder inverses.** At a nondegenerate orbit, for any
   continuous perturbation loop `Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)` (in particular
   `const (I • id)` for exponential weights), the shifted operators
   `cylinderOperator 1 (S - δ • Jc)` are invertible with uniformly bounded inverses for all
   sufficiently small `|δ| ≤ ε`
   (`exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff`,
   `eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff`).

Specializing to the identity frame on `(F, ω)` with `ω(v, w) = Im ⟪v, w⟫` gives the corresponding
frame-free theorems directly in `TauCeti.SymplecticForm`, complementing the 1D loop theorems
`TauCeti.SymplecticForm.isInvertible_loopOperator_of_isNondegenerateFixedPt` and
`TauCeti.SymplecticForm.eventually_isInvertible_loopOperator_sub_smul` in
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator.lean`.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2,
  Section 2.2 (unitary trivializations along periodic orbits and Proposition 2.2).
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter Function Topology
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

section TrivializedOrbit

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Unconditional injectivity of the Sobolev cylinder operator along a curve.** Whenever each
`H t` is `C²` at `x t` and `S` trivializes `dX_{H_t}(x(t))` in a differentiable symplectic frame
`Φ`, `CircleSobolev.cylinderOperator 1 S` is injective on `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)` even when
the orbit is degenerate. -/
theorem injective_cylinderOperator_of_trivializedCoeff (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {x : ℝ → V} (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    Function.Injective (CircleSobolev.cylinderOperator 1 S) :=
  CircleSobolev.injective_cylinderOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff hH hΦd hΦ hω hS)

/-- **Stationary cylinder invertibility equivalence in a unitary frame.** Along a one-periodic
Hamiltonian orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, the
Sobolev stationary cylinder operator `CircleSobolev.cylinderOperator 1 S` is invertible if and only
if `x(0)` is a nondegenerate fixed point of the time-one Hamiltonian flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (CircleSobolev.cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isInvertible_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
      (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- **Stationary cylinder Fredholm equivalence in a unitary frame.** Along a one-periodic
Hamiltonian orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, the
Sobolev stationary cylinder operator is Fredholm if and only if `x(0)` is a nondegenerate fixed
point of the time-one Hamiltonian flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (CircleSobolev.cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isFredholm_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
      (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- **Uniform perturbed cylinder inverses at a nondegenerate orbit.** At a nondegenerate
one-periodic orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, for any
continuous perturbation loop `Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)`, there exist `ε > 0` and
`C ≥ 0` such that for every `|δ| ≤ ε`, the shifted cylinder operator
`CircleSobolev.cylinderOperator 1 (S - δ • Jc)` is invertible with inverse norm at most `C`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε →
      (CircleSobolev.cylinderOperator 1 (S - δ • Jc)).IsInvertible ∧
        ‖(CircleSobolev.cylinderOperator 1 (S - δ • Jc)).inverse‖ ≤ C := by
  open CircleSobolev in
  obtain ⟨ε, hε, C, hC, h⟩ :=
    exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isInvertible_loopOperator
      1 (isCompact_singleton (x := ())) (fun _ ↦ S) (fun _ ↦ Jc)
      continuousOn_const continuousOn_const
      (fun _ _ ↦ ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
        (fun t ↦ (hH.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦ hω hS)
      (fun _ _ ↦ (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
        hX hH hHp hx hxp hΦd hΦp hΦ hS).2 hnd)
  exact ⟨ε, hε, C, hC, fun δ hδ ↦ h () rfl δ hδ⟩

/-- Filter form of
`exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff`: for any
perturbation loop `Jc` and all weights `δ` in a neighborhood of `0`, the shifted cylinder operator
`CircleSobolev.cylinderOperator 1 (S - δ • Jc)` is invertible. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (CircleSobolev.cylinderOperator 1 (S - δ • Jc)).IsInvertible := by
  obtain ⟨ε, hε, _, _, h⟩ :=
    ω.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
      hX hH hHp hx hxp hnd hΦd hΦp hΦ hω hS Jc
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hε] with δ hδ
  exact (h δ (by simpa [Real.dist_eq] using hδ)).1

end TrivializedOrbit

section ComplexInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Frame-free unconditional injectivity of `CircleSobolev.cylinderOperator 1 S` along any curve
`x` on `(F, ω)` with `ω(v, w) = Im ⟪v, w⟫` where each `H t` is `C²` at `x t`. -/
theorem injective_cylinderOperator (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {x : ℝ → F}
    (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t)) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    Function.Injective (CircleSobolev.cylinderOperator 1 S) :=
  ω.injective_cylinderOperator_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hH (differentiable_const _)
    (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω) fun t ↦ by
      simp [hS t]

/-- **Frame-free stationary cylinder invertibility equivalence.** On a finite-dimensional complex
inner product space `F` with symplectic form `ω(v, w) = Im ⟪v, w⟫`, the Sobolev stationary cylinder
operator along a one-periodic orbit `x` is invertible if and only if `x(0)` is a nondegenerate fixed
point of the time-one Hamiltonian flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (CircleSobolev.cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

/-- **Frame-free stationary cylinder Fredholm equivalence.** On `(F, ω)` with
`ω(v, w) = Im ⟪v, w⟫`, the Sobolev stationary cylinder operator along a one-periodic orbit `x` is
Fredholm if and only if `x(0)` is a nondegenerate fixed point of the time-one Hamiltonian flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (CircleSobolev.cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

/-- **Frame-free uniform perturbed cylinder inverses at a nondegenerate orbit.** On `(F, ω)` with
`ω(v, w) = Im ⟪v, w⟫`, for any continuous perturbation loop
`Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)` along a nondegenerate one-periodic orbit `x`, there exist
`ε > 0` and `C ≥ 0` such that for every `|δ| ≤ ε`, `CircleSobolev.cylinderOperator 1 (S - δ • Jc)`
is invertible with inverse norm at most `C`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isNondegenerateFixedPt
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε →
      (CircleSobolev.cylinderOperator 1 (S - δ • Jc)).IsInvertible ∧
        ‖(CircleSobolev.cylinderOperator 1 (S - δ • Jc)).inverse‖ ≤ C :=
  ω.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp hnd (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    (fun t ↦ by simp [hS t]) Jc

/-- Filter form of
`exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isNondegenerateFixedPt`: for
any perturbation loop `Jc` and all weights `δ` in a neighborhood of `0`,
`CircleSobolev.cylinderOperator 1 (S - δ • Jc)` is invertible. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))
    (Jc : C(AddCircle (1 : ℝ), F →L[ℝ] F)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (CircleSobolev.cylinderOperator 1 (S - δ • Jc)).IsInvertible :=
  ω.eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp hnd (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    (fun t ↦ by simp [hS t]) Jc

end ComplexInnerProductSpace

end TauCeti.SymplecticForm
