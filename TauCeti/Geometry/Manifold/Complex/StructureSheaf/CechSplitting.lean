/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.Sheaves.Cech.Cocycle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.PartitionOfUnity.CechSplitting
import TauCeti.Topology.PartitionOfUnity.CechSplitting

/-!
# Smooth splittings of holomorphic Čech cocycles

A smooth partition of unity on a complex manifold writes a holomorphic Čech one-cocycle
as differences of smooth local functions. The splitting is complex-linear in the cocycle.
On Hausdorff σ-compact finite-dimensional complex manifolds every open cover admits such
a partition. If subtracting a common function makes the local potentials holomorphic, the
cocycle represents zero in the cohomology of the cover.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public noncomputable section

open CategoryTheory Function Opposite Set TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace TauCeti.holomorphicStructureSheafModules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type u} [TopologicalSpace X] [ChartedSpace E X] {ι : Type*}
  {U : ι → Opens (TopCat.of X)}

local notation "𝒪" => holomorphicStructureSheafModules 𝓘(ℂ, E) X

/-- Pointwise evaluation of the alternating cocycle identity on a triple intersection. -/
theorem cocycle_apply_add (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i j k : ι)
    (x : X) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    c.val i j ⟨x, hi, hj⟩ + c.val j k ⟨x, hj, hk⟩ = c.val i k ⟨x, hi, hk⟩ := by
  have h := (Topology.CechOne.mem_cocycles₁_iff (𝒪).obj U).1 c.property i j k
  have he := congrArg (fun g : (𝒪).obj.obj (op (U i ⊓ U j ⊓ U k)) ↦ g ⟨x, ⟨hi, hj⟩, hk⟩) h
  simp only [add_apply, sub_apply, zero_apply, map_apply] at he
  change c.val j k ⟨x, hj, hk⟩ - c.val i k ⟨x, hi, hk⟩ + c.val i j ⟨x, hi, hj⟩ = 0 at he
  linear_combination he

private def evalOnOverlap (i j : ι) (x : X) :
    Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] ℂ := by
  classical
  exact if hx : x ∈ U i ⊓ U j then
    { toFun := fun c ↦ c.val i j ⟨x, hx⟩
      map_add' := fun _ _ ↦ add_apply _ _ _
      map_smul' := fun _ _ ↦ smul_apply _ _ _ } else 0

private theorem evalOnOverlap_apply (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    (i j : ι) (x : X) (hx : x ∈ U i ⊓ U j) :
    evalOnOverlap i j x c = c.val i j ⟨x, hx⟩ := by
  classical
  simp only [evalOnOverlap, dite_eq_left hx, LinearMap.coe_mk, AddHom.coe_mk]

private theorem contMDiffOn_evalOnOverlap (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    (i j : ι) : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun x ↦ evalOnOverlap i j x c) (U i ∩ U j) := by
  intro x hx
  have h := (holomorphicStructureSheafModules.contMDiff (c.val i j)).contMDiffAt
    (x := (⟨x, hx⟩ : ↥(U i ⊓ U j)))
  have hs := ((h.of_le (show ∞ ≤ ω by simp)).extend_subtypeVal 0).restrictScalars ℝ
  simp only [modelWithCornersSelf_restrictScalars] at hs
  refine hs.contMDiffWithinAt.congr (fun y hy ↦ ?_) ?_ <;>
    rw [evalOnOverlap_apply c i j _ ‹_›] <;>
    exact (Subtype.val_injective.extend_apply _ _ (⟨_, ‹_›⟩ : ↥(U i ⊓ U j))).symm

/-- On a cover equipped with a subordinate smooth partition of unity, holomorphic Čech
one-cocycles admit a complex-linear choice of smooth local potentials. -/
theorem exists_linear_contMDiffOn_splitting_of_isSubordinate
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) X univ)
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set X)) :
    ∃ S : Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] (ι → X → ℂ),
      (∀ c i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (S c i) (U i)) ∧
      ∀ c i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
        c.val i j ⟨x, hi, hj⟩ = S c j x - S c i x := by
  classical
  let S (i : ι) (x : X) :=
    -∑ k ∈ ρ.finsupport x, (ρ k x : ℝ) • evalOnOverlap (E := E) (U := U) i k x
  have apply_S (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i : ι) (x : X) :
      S i x c = -∑ᶠ k, ρ k x • evalOnOverlap i k x c := by
    simp only [S, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [ρ.sum_finsupport_smul_eq_finsum x (fun k y ↦ evalOnOverlap i k y c)]
  refine ⟨LinearMap.pi fun i ↦ LinearMap.pi (S i), ?_, ?_⟩
  · intro c i
    change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun x ↦ S i x c) _
    simp_rw [apply_S]
    exact (hρ.contMDiffOn_finsum_smul (fun k ↦ (U k).isOpen) fun k ↦
      (contMDiffOn_evalOnOverlap c i k).mono (inter_comm _ _).le).neg
  · intro c i j x hi hj
    change _ = S j x c - S i x c
    rw [apply_S, apply_S, neg_sub_neg]
    have hc (a b d : ι) (y : X) (hy : y ∈ (U a : Set X) ∩ U b ∩ U d) :
        evalOnOverlap a b y c + (1 : ℂ) • evalOnOverlap b d y c = evalOnOverlap a d y c := by
      simpa only [one_smul, evalOnOverlap_apply c a b y hy.1,
        evalOnOverlap_apply c b d y ⟨hy.1.2, hy.2⟩, evalOnOverlap_apply c a d y ⟨hy.1.1, hy.2⟩]
        using cocycle_apply_add c a b d y hy.1.1 hy.1.2 hy.2
    have hw (k : ι) : (ρ.toPartitionOfUnity k) x = ρ k x := by simp
    simpa only [hw, one_smul, evalOnOverlap_apply c i j x ⟨hi, hj⟩] using
      PartitionOfUnity.IsSubordinate.eq_finsum_smul_sub_smul_finsum_smul hρ.toPartitionOfUnity
        (ψ := fun _ _ _ ↦ (1 : ℂ)) (ξ := fun a b y ↦ evalOnOverlap a b y c)
        hc (mem_univ x) (show x ∈ (U i : Set X) ∩ U j from ⟨hi, hj⟩)

variable [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) 1 X]

/-- The smooth splittings of holomorphic cocycles on a cover may be chosen complex linearly. -/
theorem exists_linear_contMDiffOn_splitting [T2Space X] [SigmaCompactSpace X] (hU : IsOpenCover U) :
    ∃ S : Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] (ι → X → ℂ),
      (∀ c i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (S c i) (U i)) ∧
      ∀ c i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
        c.val i j ⟨x, hi, hj⟩ = S c j x - S c i x := by
  have : IsManifold 𝓘(ℝ, E) ∞ X := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ
    (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  exact exists_linear_contMDiffOn_splitting_of_isSubordinate ρ hρ

/-- A holomorphic Čech one-cocycle on a complex manifold is the difference of smooth
potentials on the members of the cover. -/
theorem exists_contMDiffOn_splitting [T2Space X] [SigmaCompactSpace X]
    (hU : IsOpenCover U) (c : Topology.CechOne.cocycles₁ (𝒪).obj U) :
    ∃ g : ι → X → ℂ, (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (g i) (U i)) ∧
      ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), c.val i j ⟨x, hi, hj⟩ = g j x - g i x := by
  obtain ⟨S, hs, hc⟩ := exists_linear_contMDiffOn_splitting (E := E) hU
  exact ⟨S c, hs c, hc c⟩

/-- A common correction making the local primitives holomorphic kills the Čech class. -/
theorem toHomology_eq_zero_of_mdifferentiableOn_sub
    {κ : Type u} {U : κ → Opens (TopCat.of X)}
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U) {g : κ → X → ℂ}
    (hg : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      c.val i j ⟨x, hi, hj⟩ = g j x - g i x)
    (u : X → ℂ) (hu : ∀ i, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ) (g i - u) (U i)) :
    Topology.CechOne.toHomology (𝒪).obj U c = 0 := by
  let b (i : κ) : (𝒪).obj.obj (op (U i)) :=
    ofContMDiff (fun x : U i ↦ g i x - u x)
      (((hu i).contMDiffOn (U i).isOpen).comp_contMDiff contMDiff_subtypeVal
        (fun x ↦ x.property))
  apply (Topology.CechOne.toHomology_eq_zero_iff _ _ _).2
  refine ⟨b, ?_⟩
  funext i j
  apply holomorphicStructureSheafModules.ext
  intro x
  rw [Topology.CechOne.d₀₁_apply, sub_apply, map_apply, map_apply,
    hg i j x x.property.1 x.property.2]
  simp only [b, ofContMDiff_apply]
  change (g j x - u x) - (g i x - u x) = g j x - g i x
  abel

end TauCeti.holomorphicStructureSheafModules
