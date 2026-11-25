/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.Sheaves.Cech.Cocycle

/-!
# Pointwise holomorphic Čech identities

Holomorphic Čech one-cocycles satisfy the alternating identity pointwise on triple overlaps.
If local potentials differ by the cocycle, subtracting a common function that makes them
complex analytic produces a holomorphic zero-cochain and kills the class in cover cohomology.
These identities apply without choosing a partition of unity.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public noncomputable section

open CategoryTheory Function Opposite Set TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace TauCeti.holomorphicStructureSheafModules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] {ι : Type*}
  {U : ι → Opens (TopCat.of X)}

local notation "𝒪" => holomorphicStructureSheafModules I X

/-- Pointwise evaluation of the alternating cocycle identity on a triple intersection. -/
theorem cocycle_apply_add (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i j k : ι)
    (x : X) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    c.val i j ⟨x, hi, hj⟩ + c.val j k ⟨x, hj, hk⟩ = c.val i k ⟨x, hi, hk⟩ := by
  have h := (Topology.CechOne.mem_cocycles₁_iff (𝒪).obj U).1 c.property i j k
  have he := congrArg (fun g : (𝒪).obj.obj (op (U i ⊓ U j ⊓ U k)) ↦ g ⟨x, ⟨hi, hj⟩, hk⟩) h
  simp only [add_apply, sub_apply, zero_apply, map_apply] at he
  simp only [Opens.inclusion] at he
  linear_combination he

/-- A common correction making the local primitives holomorphic kills the Čech class. -/
theorem toHomology_eq_zero_of_contMDiffOn_sub
    {κ : Type u} {U : κ → Opens (TopCat.of X)}
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U) {g : κ → X → ℂ}
    (hg : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      c.val i j ⟨x, hi, hj⟩ = g j x - g i x)
    (u : X → ℂ) (hu : ∀ i, ContMDiffOn I 𝓘(ℂ) ω (g i - u) (U i)) :
    Topology.CechOne.toHomology (𝒪).obj U c = 0 := by
  let b (i : κ) : (𝒪).obj.obj (op (U i)) :=
    ofContMDiff (fun x : U i ↦ g i x - u x)
      ((hu i).comp_contMDiff contMDiff_subtypeVal
        (fun x ↦ x.property))
  apply (Topology.CechOne.toHomology_eq_zero_iff _ _ _).2
  refine ⟨b, ?_⟩
  funext i j
  apply holomorphicStructureSheafModules.ext
  intro x
  rw [Topology.CechOne.d₀₁_apply, sub_apply, map_apply, map_apply,
    hg i j x x.property.1 x.property.2]
  simp only [b, ofContMDiff_apply]
  abel

/-- On a boundaryless finite-dimensional complex manifold, it suffices that the commonly corrected
potentials be manifold differentiable on the covering opens. -/
theorem toHomology_eq_zero_of_mdifferentiableOn_sub [I.Boundaryless]
    [FiniteDimensional ℂ E] [IsManifold I 1 X]
    {κ : Type u} {U : κ → Opens (TopCat.of X)}
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    {g : κ → X → ℂ}
    (hg : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      c.val i j ⟨x, hi, hj⟩ = g j x - g i x)
    (u : X → ℂ) (hu : ∀ i, MDifferentiableOn I 𝓘(ℂ) (g i - u) (U i)) :
    Topology.CechOne.toHomology (𝒪).obj U c = 0 :=
  toHomology_eq_zero_of_contMDiffOn_sub c hg u fun i ↦ (hu i).contMDiffOn (U i).isOpen

end TauCeti.holomorphicStructureSheafModules
