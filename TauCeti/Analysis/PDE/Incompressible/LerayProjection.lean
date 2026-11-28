/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.PDE.Incompressible.Solenoidal

/-!
# The Leray projection on `L²`

The **Leray projection** `ℙ` is the orthogonal projection of `L²(μ; E)` onto the closed subspace
`L²_σ` of solenoidal fields (`TauCeti.solenoidalLp E 2 μ`), the fields annihilating every test
gradient. It removes from a velocity field its gradient part, and is the operator through which
the pressure is eliminated from the incompressible Navier–Stokes and Euler equations.

The orthogonal complement of `L²_σ` is the closure in `L²(μ; E)` of the gradients of smooth
compactly supported functions, which is `TauCeti.wassersteinTangentSpace μ`. So every
`u ∈ L²(μ; E)` splits uniquely as `u = ℙu + (u - ℙu)`, with `ℙu` solenoidal and `u - ℙu` a limit of
test gradients: this is the abstract form of the **Helmholtz–Weyl decomposition**. For an additive
Haar measure, the limits of test gradients are exactly the square integrable weak gradients
(`TauCeti.mem_orthogonal_solenoidalLp_two_iff` in
`TauCeti.Analysis.PDE.Incompressible.HelmholtzWeyl`).

## Main declarations

* `TauCeti.orthogonal_solenoidalLp_two`: the orthogonal complement of `L²_σ` is the closure of
  the test gradients.
* `TauCeti.lerayProjection`: the Leray projection, as a continuous linear endomorphism of
  `L²(μ; E)`.
* `TauCeti.range_lerayProjection` and `TauCeti.ker_lerayProjection`: its range is `L²_σ` and its
  kernel is the closure of the test gradients; `TauCeti.lerayProjection_eq_self_iff` and
  `TauCeti.lerayProjection_eq_zero_iff` are the pointwise forms.
* `TauCeti.lerayProjection_eq_iff`: the Helmholtz–Weyl decomposition is unique.
* `TauCeti.isStarProjection_lerayProjection` and `TauCeti.norm_lerayProjection_le`: `ℙ` is a
  self-adjoint idempotent of operator norm at most `1`.
* `TauCeti.lerayProjection_toLp_gradient`: `ℙ` annihilates test gradients.
* `TauCeti.norm_sq_eq_norm_lerayProjection_sq_add_norm_sub_sq`: the Pythagorean identity
  `‖u‖² = ‖ℙu‖² + ‖u - ℙu‖²`.

## References

* T. Tao, *254A, Notes 1: Local well-posedness of the Navier–Stokes equations*, 2018,
  Exercise 17.
* W. S. Ozanski, B. C. Pooley, *Leray's fundamental work on the Navier–Stokes equations: a
  modern review of Sur le mouvement d'un liquide visqueux emplissant l'espace*,
  arXiv:1708.09787, §2.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

variable (μ) in
/-- **Helmholtz–Weyl, abstract form.** The orthogonal complement of the solenoidal fields in
`L²(μ; E)` is the closure of the gradients of smooth compactly supported functions. -/
theorem orthogonal_solenoidalLp_two :
    (solenoidalLp E 2 μ).toSubmoduleᗮ = wassersteinTangentSpace μ := by
  rw [solenoidalLp_two_eq_orthogonal_wassersteinTangentSpace, Submodule.orthogonal_orthogonal]

variable (μ) in
/-- The **Leray projection** `ℙ`: the orthogonal projection of `L²(μ; E)` onto the closed
subspace of solenoidal fields. -/
def lerayProjection : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (solenoidalLp E 2 μ).toSubmodule.starProjection

theorem lerayProjection_def :
    lerayProjection μ = (solenoidalLp E 2 μ).toSubmodule.starProjection :=
  (rfl)

/-- The Leray projection of a field is solenoidal. -/
theorem lerayProjection_apply_mem (u : Lp E 2 μ) : lerayProjection μ u ∈ solenoidalLp E 2 μ :=
  Submodule.starProjection_apply_mem _ u

/-- The gradient part `u - ℙu` of a field is a limit of test gradients. -/
theorem sub_lerayProjection_mem_wassersteinTangentSpace (u : Lp E 2 μ) :
    u - lerayProjection μ u ∈ wassersteinTangentSpace μ := by
  rw [← orthogonal_solenoidalLp_two]
  exact Submodule.sub_starProjection_mem_orthogonal u

/-- The range of the Leray projection is the space of solenoidal fields. -/
@[simp]
theorem range_lerayProjection :
    (lerayProjection μ).range = (solenoidalLp E 2 μ).toSubmodule :=
  Submodule.range_starProjection _

/-- The kernel of the Leray projection is the closure of the test gradients. -/
@[simp]
theorem ker_lerayProjection :
    (lerayProjection μ).ker = wassersteinTangentSpace μ := by
  rw [lerayProjection_def, Submodule.ker_starProjection, orthogonal_solenoidalLp_two]

/-- The Leray projection fixes exactly the solenoidal fields. -/
theorem lerayProjection_eq_self_iff {u : Lp E 2 μ} :
    lerayProjection μ u = u ↔ u ∈ solenoidalLp E 2 μ :=
  Submodule.starProjection_eq_self_iff

/-- The Leray projection annihilates exactly the limits of test gradients. -/
theorem lerayProjection_eq_zero_iff {u : Lp E 2 μ} :
    lerayProjection μ u = 0 ↔ u ∈ wassersteinTangentSpace μ := by
  rw [← ker_lerayProjection]
  exact LinearMap.mem_ker.symm

/-- **Uniqueness of the Helmholtz–Weyl decomposition.** A solenoidal field `v` is the Leray
projection of `u` exactly when `u - v` is a limit of test gradients. -/
theorem lerayProjection_eq_iff {u v : Lp E 2 μ} (hv : v ∈ solenoidalLp E 2 μ) :
    lerayProjection μ u = v ↔ u - v ∈ wassersteinTangentSpace μ := by
  refine ⟨fun h ↦ h ▸ sub_lerayProjection_mem_wassersteinTangentSpace u, fun h ↦ ?_⟩
  rw [← orthogonal_solenoidalLp_two] at h
  exact Submodule.eq_starProjection_of_mem_orthogonal' hv h (add_sub_cancel v u).symm

/-- The Leray projection annihilates the gradient of a smooth compactly supported function. -/
@[simp]
theorem lerayProjection_toLp_gradient {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hm : MemLp (∇ φ) 2 μ) : lerayProjection μ (hm.toLp (∇ φ)) = 0 :=
  lerayProjection_eq_zero_iff.2 (toLp_gradient_mem_wassersteinTangentSpace hφ hφc hm)

/-- The Leray projection is idempotent. -/
@[simp]
theorem lerayProjection_lerayProjection (u : Lp E 2 μ) :
    lerayProjection μ (lerayProjection μ u) = lerayProjection μ u :=
  lerayProjection_eq_self_iff.2 (lerayProjection_apply_mem u)

/-- The Leray projection is a self-adjoint idempotent, that is, an orthogonal projection. -/
theorem isStarProjection_lerayProjection : IsStarProjection (lerayProjection μ) :=
  isStarProjection_starProjection

/-- The Leray projection does not increase the `L²` norm. -/
theorem norm_lerayProjection_apply_le (u : Lp E 2 μ) : ‖lerayProjection μ u‖ ≤ ‖u‖ :=
  Submodule.norm_starProjection_apply_le _ u

/-- The Leray projection has operator norm at most `1`. -/
theorem norm_lerayProjection_le : ‖lerayProjection μ‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- **The Pythagorean identity of the Helmholtz–Weyl decomposition**:
`‖u‖² = ‖ℙu‖² + ‖u - ℙu‖²`. -/
theorem norm_sq_eq_norm_lerayProjection_sq_add_norm_sub_sq (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ‖lerayProjection μ u‖ ^ 2 + ‖u - lerayProjection μ u‖ ^ 2 := by
  rw [lerayProjection_def, ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection u _

end TauCeti
