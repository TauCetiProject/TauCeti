/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import TauCeti.Topology.ContinuousMap.Bounded.Nonseparable
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded functions on a discrete space: locally finite-dimensional, not AF

For a discrete space `X`, the C⋆-algebra `X →ᵇ ℂ` (for `X = ℕ`, the algebra `ℓ∞`) satisfies the
local approximation condition for AF algebras: finitely many elements are approximated, to any
tolerance, by finite-valued functions, and the functions constant on the fibres of the joint
finite-valued map form a finite-dimensional C⋆-subalgebra
(`BoundedContinuousFunction.exists_finiteDimensional_approx_of_discrete`). But for infinite `X`,
`X →ᵇ ℂ` is not separable (`BoundedContinuousFunction.not_separableSpace_of_infinite`). So it is
not AF (`TauCeti.not_isAF_boundedContinuousFunction_of_infinite`; for `X = ℕ`, `ℓ∞` is not AF),
and separability is a genuine hypothesis of the local characterization of AF algebras.

## Main statements

* `BoundedContinuousFunction.exists_finiteDimensional_approx_of_discrete`: the local
  approximation condition for `X →ᵇ ℂ`, `X` discrete.
* `TauCeti.not_isAF_boundedContinuousFunction_of_infinite`: `X →ᵇ ℂ` is not AF for `X`
  infinite and discrete; in particular `ℓ∞ = ℕ →ᵇ ℂ` is not AF.
-/

public section

open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

/-- The bounded functions on `X` that are constant on the fibres of `π`, a star subalgebra of
`X →ᵇ ℂ`. -/
private def fibreConstant {X ι : Type*} [TopologicalSpace X] (π : X → ι) :
    NonUnitalStarSubalgebra ℂ (X →ᵇ ℂ) where
  carrier := {b | ∀ x y, π x = π y → b x = b y}
  add_mem' ha hb x y h := by simp [ha x y h, hb x y h]
  zero_mem' _ _ _ := rfl
  mul_mem' ha hb x y h := by simp [ha x y h, hb x y h]
  smul_mem' c _ ha x y h := by simp [ha x y h]
  star_mem' ha x y h := by simp [ha x y h]

private theorem mem_fibreConstant {X ι : Type*} [TopologicalSpace X] {π : X → ι}
    {b : X →ᵇ ℂ} : b ∈ fibreConstant π ↔ ∀ x y, π x = π y → b x = b y :=
  Iff.rfl

/-- If `π` takes finitely many values, the functions constant on its fibres form a
finite-dimensional space: such a function is determined by its values on chosen points of the
fibres. -/
private theorem finiteDimensional_fibreConstant {X ι : Type*} [TopologicalSpace X] (π : X → ι)
    (hπ : (Set.range π).Finite) : FiniteDimensional ℂ (fibreConstant π) := by
  have : Finite (Set.range π) := hπ.to_subtype
  let L : fibreConstant π →ₗ[ℂ] Set.range π → ℂ :=
    { toFun b p := (b : X →ᵇ ℂ) p.property.choose
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  refine Module.Finite.of_injective L fun b c h ↦ Subtype.ext (ext fun x ↦ ?_)
  have hx : π (Set.mem_range_self x : π x ∈ Set.range π).choose = π x :=
    (Set.mem_range_self x : π x ∈ Set.range π).choose_spec
  have := congrFun h ⟨π x, Set.mem_range_self x⟩
  rwa [← mem_fibreConstant.1 b.prop _ _ hx, ← mem_fibreConstant.1 c.prop _ _ hx]

/-- **The local approximation condition for bounded functions on a discrete space**: finitely
many elements of `X →ᵇ ℂ` are approximated, to any tolerance, inside a finite-dimensional
C⋆-subalgebra. -/
theorem exists_finiteDimensional_approx_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] (F : Finset (X →ᵇ ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : NonUnitalStarSubalgebra ℂ (X →ᵇ ℂ), FiniteDimensional ℂ S ∧
      ∀ a ∈ F, ∃ b ∈ S, ‖a - b‖ < ε := by
  -- Approximate each `a ∈ F` within `ε` by a finite-valued function.
  have happrox (a : F) : ∃ g : X →ᵇ ℂ, (Set.range g).Finite ∧ dist (a : X →ᵇ ℂ) g < ε :=
    exists_finite_range_dist_lt _ hε
  choose G hG hGa using happrox
  -- The joint finite-valued map; the approximants are constant on its fibres.
  let π : X → (F → ℂ) := fun x a ↦ G a x
  have hπ : (Set.range π).Finite :=
    (Set.Finite.pi (t := fun a : F ↦ Set.range (G a)) hG).subset
      (by rintro _ ⟨x, rfl⟩ a -; exact ⟨x, rfl⟩)
  refine ⟨fibreConstant π, finiteDimensional_fibreConstant π hπ, fun a ha ↦
    ⟨G ⟨a, ha⟩, mem_fibreConstant.2 fun x y hxy ↦ congrFun hxy ⟨a, ha⟩,
      dist_eq_norm a (G ⟨a, ha⟩) ▸ hGa ⟨a, ha⟩⟩⟩

end BoundedContinuousFunction

namespace TauCeti

/-- **Bounded functions on an infinite discrete space are not AF**: an AF algebra is separable,
and `X →ᵇ ℂ` is not. For `X = ℕ` this says that `ℓ∞` is not AF. -/
theorem not_isAF_boundedContinuousFunction_of_infinite {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [Infinite X] : ¬ IsAF (X →ᵇ ℂ) :=
  fun h ↦ BoundedContinuousFunction.not_separableSpace_of_infinite h.separableSpace

end TauCeti
