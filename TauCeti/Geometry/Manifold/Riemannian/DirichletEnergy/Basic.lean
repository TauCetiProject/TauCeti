/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# The Dirichlet energy

The Dirichlet energy of a real function `φ` on a Riemannian manifold `M` is
`E(φ) = ∫ ‖grad φ‖² dV`, the integral of the squared length of its Riemannian gradient against
the Riemannian volume. We do not include the factor `1 / 2` used by some authors. The energy on a
subset `s` of `M` is `∫_s ‖grad φ‖² dV`.

The integrand vanishes outside the topological support of `φ`. Hence for a compactly supported
`C¹` function the integrand is integrable, and the energy of `φ` can be computed on any subset
containing its support, in particular on any open subdomain containing it.

## Main definitions

* `TauCeti.Manifold.dirichletEnergy`: the Dirichlet energy `∫ ‖grad φ‖² dV`.
* `TauCeti.Manifold.dirichletEnergyOn`: the Dirichlet energy `∫_s ‖grad φ‖² dV` on a subset `s`.

## Main results

* `TauCeti.Manifold.integrable_norm_sq_mgradient`: the integrand `‖grad φ‖²` of a compactly
  supported `C¹` function is integrable.
* `TauCeti.Manifold.dirichletEnergyOn_eq_of_tsupport_subset`: the energy on a subset containing
  the support of `φ` is the energy of `φ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The Dirichlet energy `∫ ‖grad φ‖² dV` of a real function, without the factor `1 / 2`. -/
def dirichletEnergy (φ : M → ℝ) : ℝ :=
  ∫ x, ‖mgradient I φ x‖ ^ 2 ∂riemannianVolume I M

variable (I) in
/-- The Dirichlet energy `∫_s ‖grad φ‖² dV` of a real function on a subset `s`. -/
def dirichletEnergyOn (φ : M → ℝ) (s : Set M) : ℝ :=
  ∫ x in s, ‖mgradient I φ x‖ ^ 2 ∂riemannianVolume I M

variable (I) in
/-- The Dirichlet energy is the integral of the squared length of the gradient. -/
theorem dirichletEnergy_def (φ : M → ℝ) :
    dirichletEnergy I φ = ∫ x, ‖mgradient I φ x‖ ^ 2 ∂riemannianVolume I M := (rfl)

variable (I) in
/-- The Dirichlet energy on a subset is the integral over that subset of the squared length of
the gradient. -/
theorem dirichletEnergyOn_def (φ : M → ℝ) (s : Set M) :
    dirichletEnergyOn I φ s = ∫ x in s, ‖mgradient I φ x‖ ^ 2 ∂riemannianVolume I M := (rfl)

/-- A constant function has zero Dirichlet energy. -/
@[simp]
theorem dirichletEnergy_const (c : ℝ) : dirichletEnergy I (fun _ : M ↦ c) = 0 := by
  simp [dirichletEnergy_def]

/-- The zero function has zero Dirichlet energy. -/
@[simp]
theorem dirichletEnergy_zero : dirichletEnergy I (0 : M → ℝ) = 0 :=
  dirichletEnergy_const 0

/-- A constant function has zero Dirichlet energy on every subset. -/
@[simp]
theorem dirichletEnergyOn_const (c : ℝ) (s : Set M) :
    dirichletEnergyOn I (fun _ : M ↦ c) s = 0 := by
  simp [dirichletEnergyOn_def]

/-- The zero function has zero Dirichlet energy on every subset. -/
@[simp]
theorem dirichletEnergyOn_zero (s : Set M) : dirichletEnergyOn I (0 : M → ℝ) s = 0 :=
  dirichletEnergyOn_const 0 s

/-- The Dirichlet energy on the empty set vanishes. -/
@[simp]
theorem dirichletEnergyOn_empty (φ : M → ℝ) : dirichletEnergyOn I φ ∅ = 0 := by
  simp [dirichletEnergyOn_def]

/-- The Dirichlet energy on the whole manifold is the Dirichlet energy. -/
@[simp]
theorem dirichletEnergyOn_univ (φ : M → ℝ) :
    dirichletEnergyOn I φ univ = dirichletEnergy I φ := by
  simp [dirichletEnergyOn_def, dirichletEnergy_def]

/-- The Dirichlet energy is nonnegative. -/
theorem dirichletEnergy_nonneg (φ : M → ℝ) : 0 ≤ dirichletEnergy I φ :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- The Dirichlet energy on a subset is nonnegative. -/
theorem dirichletEnergyOn_nonneg (φ : M → ℝ) (s : Set M) : 0 ≤ dirichletEnergyOn I φ s :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- The squared length of the gradient of a compactly supported `C¹` function is integrable. -/
theorem integrable_norm_sq_mgradient {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) 1 φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x ↦ ‖mgradient I φ x‖ ^ 2) (riemannianVolume I M) := by
  refine (continuous_norm_sq_mgradient hφ).integrable_of_hasCompactSupport ?_
  simpa only [real_inner_self_eq_norm_sq] using hc.inner_mgradient (mgradient I φ)

/-- The Dirichlet energy on a subset containing the topological support of `φ` is the Dirichlet
energy of `φ`. -/
theorem dirichletEnergyOn_eq_of_tsupport_subset {φ : M → ℝ} {s : Set M}
    (hs : tsupport φ ⊆ s) : dirichletEnergyOn I φ s = dirichletEnergy I φ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
  rw [mgradient_eq_zero_iff.2 ((notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hs h)).mvfderiv_eq
    |>.trans mvfderiv_zero), norm_zero, zero_pow two_ne_zero]

end TauCeti.Manifold
