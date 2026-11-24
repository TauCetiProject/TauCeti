/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Normal linear functionals and matrix-coefficient functionals on von Neumann algebras

Normal functionals capture the ultraweak/strong-operator continuity of functionals on a concrete
von Neumann algebra `M`, as needed for canonical traces such as `TauCeti.groupVonNeumannTrace`.
This file defines `VonNeumannAlgebra.IsNormalFunctional` (continuity along monotone nets converging
in the strong operator topology `PointwiseConvergenceCLM`) and the matrix-coefficient functional
`VonNeumannAlgebra.innerLinearMap` (`x ↦ ⟪ξ, x η⟫_ℂ`), proving every matrix-coefficient functional
is normal (`VonNeumannAlgebra.isNormalFunctional_innerLinearMap`).

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), §3.2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §2.5.
-/

public section

open Filter Topology
open ContinuousLinearMap (toPointwiseConvergenceCLM)
open scoped InnerProductSpace

universe u

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A linear functional on `M` is **normal** when it preserves limits along increasing nets in `M`
that converge in the strong operator topology. Index types in the universe of `H` suffice because
an increasing net may be replaced by its directed range in `M`. -/
def IsNormalFunctional (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (x : ι → M.toStarSubalgebra) (y : M.toStarSubalgebra),
    Monotone (fun i => (x i : H →L[ℂ] H)) →
    Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (x i : H →L[ℂ] H)) atTop
      (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (y : H →L[ℂ] H))) →
    Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y))

theorem isNormalFunctional_def (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) :
    M.IsNormalFunctional τ ↔
      ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        (x : ι → M.toStarSubalgebra) (y : M.toStarSubalgebra),
        Monotone (fun i => (x i : H →L[ℂ] H)) →
        Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (x i : H →L[ℂ] H)) atTop
          (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (y : H →L[ℂ] H))) →
        Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y)) :=
  Iff.rfl

/-- A normal functional preserves limits along monotone nets converging in the strong operator
topology. -/
theorem IsNormalFunctional.tendsto {M : VonNeumannAlgebra H} {τ : M.toStarSubalgebra →ₗ[ℂ] ℂ}
    (hτ : M.IsNormalFunctional τ) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {x : ι → M.toStarSubalgebra} {y : M.toStarSubalgebra}
    (hmono : Monotone fun i => (x i : H →L[ℂ] H))
    (hlim : Tendsto (fun i => toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (x i : H →L[ℂ] H))
      atTop (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (y : H →L[ℂ] H)))) :
    Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y)) :=
  hτ ι x y hmono hlim

/-- The matrix-coefficient linear functional `x ↦ ⟪ξ, x η⟫_ℂ` on `M.toStarSubalgebra`. -/
noncomputable def innerLinearMap (M : VonNeumannAlgebra H) (ξ η : H) :
    M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun x := ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]

@[simp]
theorem innerLinearMap_apply (M : VonNeumannAlgebra H) (ξ η : H) (x : M.toStarSubalgebra) :
    M.innerLinearMap ξ η x = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ :=
  (rfl)

/-- Evaluating `M.innerLinearMap ξ η` on `star x * y` moves `star x` to the left slot of the inner
product. -/
theorem innerLinearMap_star_mul (M : VonNeumannAlgebra H) (ξ η : H) (x y : M.toStarSubalgebra) :
    M.innerLinearMap ξ η (star x * y) = ⟪(x : H →L[ℂ] H) ξ, (y : H →L[ℂ] H) η⟫_ℂ := by
  rw [innerLinearMap_apply, Subalgebra.coe_mul, StarMemClass.coe_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- Every matrix-coefficient functional `x ↦ ⟪ξ, x η⟫_ℂ` on `M` is normal. -/
theorem isNormalFunctional_innerLinearMap (M : VonNeumannAlgebra H) (ξ η : H) :
    M.IsNormalFunctional (M.innerLinearMap ξ η) := by
  intro ι _ _ _ x y _ hxy
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto] at hxy
  exact tendsto_const_nhds.inner (hxy η)

end VonNeumannAlgebra
