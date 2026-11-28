/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cech.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Evaluation
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.PartitionOfUnity.CechSplitting
import TauCeti.Logic.Function.Extend
import TauCeti.Topology.PartitionOfUnity.CechSplitting

/-!
# Smooth splittings of holomorphic Čech cocycles

A smooth partition of unity subordinate to an open cover writes a holomorphic Čech one-cocycle
on that cover as differences of smooth local functions. The splitting is complex-linear in the
cocycle, and its weighted-sum formula is available for estimates. On Hausdorff σ-compact
finite-dimensional manifolds with a smooth underlying real atlas every open cover admits such
a partition.

This adapts the untwisted construction of
`TauCeti.exists_contMDiffOn_eq_smul_sub_of_cocycle` to a complex-linear map on native holomorphic
Čech cocycles. The pointwise cocycle and common-correction criteria are in
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cech.Basic`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public noncomputable section

open CategoryTheory Function Opposite Set TopologicalSpace
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheafModules

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] {ι : Type*}
  {U : ι → Opens (TopCat.of X)}

local notation "𝒪" => holomorphicStructureSheafModules I X

private def evalOnOverlap (i j : ι) (x : X) :
    Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] ℂ := by
  classical
  exact if hx : x ∈ U i ⊓ U j then
    holomorphicStructureSheaf.sectionEval I X x (U i ⊓ U j) hx ∘ₗ
      (LinearMap.proj j ∘ₗ LinearMap.proj i) ∘ₗ (Topology.CechOne.cocycles₁ (𝒪).obj U).subtype
    else 0

private theorem evalOnOverlap_apply (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    (i j : ι) (x : X) (hx : x ∈ U i ⊓ U j) :
    evalOnOverlap i j x c = c.val i j ⟨x, hx⟩ := by
  classical
  simp only [evalOnOverlap, dite_eq_left hx, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, holomorphicStructureSheaf.sectionEval_apply I X]

private theorem evalOnOverlap_eq_extend (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    (i j : ι) (x : X) :
    evalOnOverlap i j x c =
      Function.extend (Subtype.val : ↥(U i ⊓ U j) → X) (c.val i j) 0 x := by
  by_cases hx : x ∈ U i ⊓ U j
  · rw [evalOnOverlap_apply c i j x hx]
    exact (Subtype.val_injective.extend_apply _ _ (⟨x, hx⟩ : ↥(U i ⊓ U j))).symm
  · classical
    simp only [evalOnOverlap, dite_eq_right hx, LinearMap.zero_apply]
    exact (Function.extend_subtypeVal_eq (c.val i j) (0 : X → ℂ)
      (x := x) fun h ↦ (hx h).elim).symm

private theorem contMDiffOn_evalOnOverlap [I.Boundaryless]
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i j : ι) :
    ContMDiffOn (I.restrictScalars ℝ) 𝓘(ℝ, ℂ) ∞ (fun x ↦ evalOnOverlap i j x c)
      (U i ∩ U j) := by
  let f : C^ω⟮I, ↥(U i ⊓ U j); 𝓘(ℂ), ℂ⟯ := ⟨c.val i j, contMDiff (c.val i j)⟩
  have hs := ((ContMDiffMap.contMDiffOn_extend (U i ⊓ U j) f 0).of_le
    (by simp : ∞ ≤ ω)).restrictScalars ℝ
  simp only [modelWithCornersSelf_restrictScalars] at hs
  exact hs.congr fun x _ ↦ evalOnOverlap_eq_extend c i j x

namespace SmoothPartitionOfUnity

variable [I.Boundaryless] (ρ : SmoothPartitionOfUnity ι (I.restrictScalars ℝ) X univ)

/-- The complex-linear weighted-sum potentials of a holomorphic Čech cocycle. For a partition
subordinate to its cover these are smooth and their differences recover the cocycle. -/
def holomorphicCechSplitting : Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] (ι → X → ℂ) := by
  classical
  exact LinearMap.pi fun i ↦ LinearMap.pi fun x ↦
    -∑ k ∈ ρ.finsupport x, (ρ k x : ℝ) • evalOnOverlap (I := I) (U := U) i k x

/-- The potentials are the negative weighted sums of the overlap sections extended by zero.
This formula allows the partition-of-unity estimates to be applied to the chosen splitting. -/
@[simp]
theorem holomorphicCechSplitting_apply (c : Topology.CechOne.cocycles₁ (𝒪).obj U)
    (i : ι) (x : X) :
    ρ.holomorphicCechSplitting c i x =
      -∑ᶠ k, ρ k x • Function.extend (Subtype.val : ↥(U i ⊓ U k) → X) (c.val i k) 0 x := by
  classical
  simp only [holomorphicCechSplitting, LinearMap.pi_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, evalOnOverlap_eq_extend]
  rw [ρ.sum_finsupport_smul_eq_finsum x (fun k y ↦
    Function.extend (Subtype.val : ↥(U i ⊓ U k) → X) (c.val i k) 0 y)]

/-- For a subordinate smooth partition, the weighted-sum potentials are smooth on each
member of the cover, for any boundaryless complex model. -/
theorem contMDiffOn_holomorphicCechSplitting
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set X))
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i : ι) :
    ContMDiffOn (I.restrictScalars ℝ) 𝓘(ℝ, ℂ) ∞ (ρ.holomorphicCechSplitting c i) (U i) := by
  have hs : ContMDiffOn (I.restrictScalars ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ -∑ᶠ k, ρ k x • evalOnOverlap i k x c) (U i) :=
    (hρ.contMDiffOn_finsum_smul (fun k ↦ (U k).isOpen) fun k ↦
      (contMDiffOn_evalOnOverlap c i k).mono (inter_comm _ _).le).neg
  refine hs.congr fun x _ ↦ ?_
  rw [holomorphicCechSplitting_apply]
  simp only [evalOnOverlap_eq_extend]

/-- The differences of the weighted-sum potentials recover the holomorphic cocycle on overlaps
when the partition is subordinate to the cover. -/
theorem sub_holomorphicCechSplitting
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set X))
    (c : Topology.CechOne.cocycles₁ (𝒪).obj U) (i j : ι)
    (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    ρ.holomorphicCechSplitting c j x - ρ.holomorphicCechSplitting c i x =
      c.val i j ⟨x, hi, hj⟩ := by
  have hc (a b d : ι) (y : X) (hy : y ∈ (U a : Set X) ∩ U b ∩ U d) :
      evalOnOverlap a b y c + (1 : ℂ) • evalOnOverlap b d y c = evalOnOverlap a d y c := by
    simpa only [one_smul, evalOnOverlap_apply c a b y hy.1,
      evalOnOverlap_apply c b d y ⟨hy.1.2, hy.2⟩, evalOnOverlap_apply c a d y ⟨hy.1.1, hy.2⟩]
      using cocycle_apply_add c a b d y hy.1.1 hy.1.2 hy.2
  have hw (k : ι) : (ρ.toPartitionOfUnity k) x = ρ k x := by simp
  have h := PartitionOfUnity.IsSubordinate.eq_finsum_smul_sub_smul_finsum_smul
    hρ.toPartitionOfUnity
    (ψ := fun _ _ _ ↦ (1 : ℂ)) (ξ := fun a b y ↦ evalOnOverlap a b y c)
    hc (mem_univ x) (Set.mem_inter hi hj)
  have he : c.val i j ⟨x, hi, hj⟩ =
      (∑ᶠ k, ρ k x • evalOnOverlap i k x c) - ∑ᶠ k, ρ k x • evalOnOverlap j k x c := by
    simpa only [hw, one_smul, evalOnOverlap_apply c i j x ⟨hi, hj⟩] using h
  rw [holomorphicCechSplitting_apply, holomorphicCechSplitting_apply, neg_sub_neg]
  simpa only [evalOnOverlap_eq_extend] using he.symm

end SmoothPartitionOfUnity

/-- On an open cover of a Hausdorff σ-compact finite-dimensional manifold with boundaryless
complex model and a smooth underlying real atlas, holomorphic Čech cocycles admit a complex-linear
choice of smooth local potentials. -/
theorem TopologicalSpace.IsOpenCover.exists_linear_contMDiffOn_splitting [I.Boundaryless]
    [FiniteDimensional ℂ E] [IsManifold (I.restrictScalars ℝ) ∞ X]
    [T2Space X] [SigmaCompactSpace X] (hU : IsOpenCover U) :
    ∃ S : Topology.CechOne.cocycles₁ (𝒪).obj U →ₗ[ℂ] (ι → X → ℂ),
      (∀ c i, ContMDiffOn (I.restrictScalars ℝ) 𝓘(ℝ, ℂ) ∞ (S c i) (U i)) ∧
      ∀ c i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
        c.val i j ⟨x, hi, hj⟩ = S c j x - S c i x := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I.restrictScalars ℝ) isClosed_univ
    (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  exact ⟨ρ.holomorphicCechSplitting,
    ρ.contMDiffOn_holomorphicCechSplitting hρ,
    fun c i j x hi hj ↦ (ρ.sub_holomorphicCechSplitting hρ c i j x hi hj).symm⟩
