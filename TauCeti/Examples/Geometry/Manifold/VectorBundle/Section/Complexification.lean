/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Complexification
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Native complexified-section topology examples

Constant sections with values `2 + 3i` compute the real/imaginary product, its inverse, the
quarter-turn and conjugation at finite, smooth, analytic, and zero regularity. A nonzero
coordinate in the infinite fibre `C([0,1], ℝ)` exercises the API without finite-rank or
locally compact fibre hypotheses. Further clients use rank zero, an empty base and frame family, a
disconnected base with distinct component values, and the actual native tangent bundle of `S²`.
-/

public section

noncomputable section
open Bundle TauCeti Set TopologicalSpace
open scoped ContDiff Manifold TensorProduct TauCeti.Complexification

namespace TauCeti.Examples.SectionComplexification

/-- A constant native section of the real trivial bundle, at any regularity order. -/
def constantSection (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞ω) (a : F) : Cₛ^n⟮𝓘(ℝ, ℝ); F, Bundle.Trivial ℝ F⟯ :=
  ⟨fun _ ↦ a, by
    intro x
    rw [Bundle.contMDiffAt_section_iff]
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n (fun _ : ℝ ↦ a) x)⟩

/-- Evaluation of the example constant section. -/
@[simp]
theorem constantSection_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞ω) (a : F) (x : ℝ) : constantSection F n a x = a := by
  rfl

private def realFrames (F : Type*) [TopologicalSpace F] :
    Unit → Trivialization F (π F (Bundle.Trivial ℝ F)) :=
  fun _ ↦ trivializationAt F (Bundle.Trivial ℝ F) 0

private instance realFramesAtlas (F : Type*) [TopologicalSpace F] (i : Unit) :
    MemTrivializationAtlas (realFrames F i) := by
  dsimp only [realFrames]
  infer_instance

private def realDomains : Unit → Opens ℝ := fun _ ↦ ⊤

private theorem realDomains_subset (F : Type*) [TopologicalSpace F] (i : Unit) :
    (realDomains i : Set ℝ) ⊆ (realFrames F i).baseSet := by
  simp [realDomains, realFrames, Bundle.Trivial.fiberBundle_trivializationAt']

/-- For these examples the original sections use the chosen global trivial frame. -/
@[instance_reducible]
private def realSectionTopology (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞ω) : TopologicalSpace Cₛ^n⟮𝓘(ℝ, ℝ); F, Bundle.Trivial ℝ F⟯ :=
  ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℝ)) (n := n)
    (realFrames F) realDomains (realDomains_subset F)

/-- Complexified examples use exactly the matching complexified frame topology. -/
@[instance_reducible]
private def complexSectionTopology (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞ω) : TopologicalSpace
      Cₛ^n⟮𝓘(ℝ, ℝ); Complexification F, fun x ↦ ℂ ⊗[ℝ] Bundle.Trivial ℝ F x⟯ :=
  ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℝ)) (n := n)
    (fun i ↦ (realFrames F i).complexification) realDomains
      (Trivialization.subset_baseSet_complexification (realFrames F) (realDomains_subset F))

attribute [local instance] realSectionTopology complexSectionTopology

/-- The native complexified constant section with real value `a` and imaginary value `b`. -/
def constantPair (n : ℕ∞ω) (a b : ℝ) :
    Cₛ^n⟮𝓘(ℝ, ℝ); Complexification ℝ, fun _ : ℝ ↦ ℂ ⊗[ℝ] ℝ⟯ :=
  ContMDiffSection.oneTmulLinearMap 𝓘(ℝ, ℝ) ℝ n (Bundle.Trivial ℝ ℝ)
      (constantSection ℝ n a) +
    ContMDiffSection.ITmulLinearMap 𝓘(ℝ, ℝ) ℝ n (Bundle.Trivial ℝ ℝ)
      (constantSection ℝ n b)

example :
    (ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (realFrames ℝ) realDomains (realDomains_subset ℝ)) (constantPair ∞ 2 3) =
      (constantSection ℝ ∞ 2, constantSection ℝ ∞ 3) := by
  simp [constantPair]

example :
    (ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := 3)
      (realFrames ℝ) realDomains (realDomains_subset ℝ)).symm
      (constantSection ℝ 3 2, constantSection ℝ 3 3) = constantPair 3 2 3 := by
  simp [constantPair]

example :
    (ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := 0)
      (realFrames ℝ) realDomains (realDomains_subset ℝ)) (Complex.I • constantPair 0 2 3) =
      (-constantSection ℝ 0 3, constantSection ℝ 0 2) := by
  rw [ContMDiffSection.complexificationEquivProdCLE_apply,
    ContMDiffSection.complexificationEquivProd_I_smul]
  simp [constantPair]

example :
    (ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := ω)
      (realFrames ℝ) realDomains (realDomains_subset ℝ))
      (ContMDiffSection.conjCLE (I := 𝓘(ℝ, ℝ)) (n := ω)
        (realFrames ℝ) realDomains (realDomains_subset ℝ) (constantPair ω 2 3)) =
      (constantSection ℝ ω 2, -constantSection ℝ ω 3) := by
  rw [ContMDiffSection.complexificationEquivProdCLE_apply, ContMDiffSection.conjCLE_apply,
    ContMDiffSection.complexificationEquivProd_conjEquiv]
  simp [constantPair]

example :
    ((ContMDiffSection.realPointsConjEquivCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (realFrames ℝ) realDomains (realDomains_subset ℝ)).symm
      ((ContMDiffSection.realPointsConjEquivCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
        (realFrames ℝ) realDomains (realDomains_subset ℝ)) (constantSection ℝ ∞ 2))) 0 = 2 := by
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact constantSection_apply ℝ ∞ 2 0

example :
    (ContMDiffSection.conjCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (realFrames ℝ) realDomains (realDomains_subset ℝ)).symm (constantPair ∞ 2 3) =
      ContMDiffSection.conjEquiv 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial ℝ ℝ) (constantPair ∞ 2 3) := by
  rw [ContMDiffSection.conjCLE_symm_apply]

private abbrev InfiniteF := C(↥(Icc (0 : ℝ) 1), ℝ)

/-- A nonzero vector in the infinite-dimensional example fibre. -/
def intervalCoordinate : C(↥(Icc (0 : ℝ) 1), ℝ) :=
  ⟨Subtype.val, continuous_subtypeVal⟩

private def intervalOne : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

example :
    ((ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (realFrames InfiniteF) realDomains (realDomains_subset InfiniteF))
      (ContMDiffSection.oneTmulLinearMap 𝓘(ℝ, ℝ) InfiniteF ∞ (Bundle.Trivial ℝ InfiniteF)
          (constantSection InfiniteF ∞ intervalCoordinate) +
        ContMDiffSection.ITmulLinearMap 𝓘(ℝ, ℝ) InfiniteF ∞ (Bundle.Trivial ℝ InfiniteF)
          (constantSection InfiniteF ∞ intervalCoordinate))).1 0 intervalOne = 1 := by
  simp [intervalCoordinate, intervalOne]

example :
    ((ContMDiffSection.imaginaryPartCLM (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (realFrames InfiniteF) realDomains (realDomains_subset InfiniteF))
      (ContMDiffSection.conjCLE (I := 𝓘(ℝ, ℝ)) (n := ∞)
        (realFrames InfiniteF) realDomains (realDomains_subset InfiniteF)
        (ContMDiffSection.ITmulLinearMap 𝓘(ℝ, ℝ) InfiniteF ∞ (Bundle.Trivial ℝ InfiniteF)
          (constantSection InfiniteF ∞ intervalCoordinate)))) 0 intervalOne = -1 := by
  simp [intervalCoordinate, intervalOne]

example :
    (ContMDiffSection.realPointsConjEquivCLE (I := 𝓘(ℝ, ℝ)) (n := 0)
      (realFrames (Fin 0 → ℝ)) realDomains (realDomains_subset (Fin 0 → ℝ))).symm
      ((ContMDiffSection.realPointsConjEquivCLE (I := 𝓘(ℝ, ℝ)) (n := 0)
        (realFrames (Fin 0 → ℝ)) realDomains (realDomains_subset (Fin 0 → ℝ)))
          (constantSection (Fin 0 → ℝ) 0 0)) = constantSection (Fin 0 → ℝ) 0 0 := by
  exact ContinuousLinearEquiv.symm_apply_apply _ _

/-- The empty source has its native empty atlas. -/
local instance emptyChartedSpace : ChartedSpace ℝ Empty := ChartedSpace.empty ℝ Empty

private def emptyFrames : Empty → Trivialization ℝ (π ℝ (Bundle.Trivial Empty ℝ)) :=
  fun i ↦ nomatch i

private instance emptyFramesAtlas (i : Empty) : MemTrivializationAtlas (emptyFrames i) :=
  nomatch i

private def emptyDomains : Empty → Opens Empty := fun i ↦ nomatch i

private theorem emptyDomain_subset (i : Empty) :
    (emptyDomains i : Set Empty) ⊆ (emptyFrames i).baseSet := nomatch i

example :
    letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℝ)) (n := ω)
      emptyFrames emptyDomains emptyDomain_subset
    letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℝ)) (n := ω)
      (fun i ↦ (emptyFrames i).complexification) emptyDomains
      (Trivialization.subset_baseSet_complexification emptyFrames emptyDomain_subset)
    Nonempty (Cₛ^ω⟮𝓘(ℝ, ℝ); Complexification ℝ, fun _ : Empty ↦ ℂ ⊗[ℝ] ℝ⟯ ≃L[ℝ]
      Cₛ^ω⟮𝓘(ℝ, ℝ); ℝ, Bundle.Trivial Empty ℝ⟯ × Cₛ^ω⟮𝓘(ℝ, ℝ); ℝ, Bundle.Trivial Empty ℝ⟯) :=
  ⟨ContMDiffSection.complexificationEquivProdCLE (I := 𝓘(ℝ, ℝ)) (n := ω)
    emptyFrames emptyDomains emptyDomain_subset⟩

private def splitFrames : Unit → Trivialization ℝ (π ℝ (Bundle.Trivial (ℝ ⊕ ℝ) ℝ)) :=
  fun _ ↦ trivializationAt ℝ (Bundle.Trivial (ℝ ⊕ ℝ) ℝ) (Sum.inl 0)

private instance splitFramesAtlas (i : Unit) : MemTrivializationAtlas (splitFrames i) := by
  dsimp only [splitFrames]
  infer_instance

private def splitDomains : Unit → Opens (ℝ ⊕ ℝ) := fun _ ↦ ⊤

private theorem splitDomain_subset (i : Unit) :
    (splitDomains i : Set (ℝ ⊕ ℝ)) ⊆ (splitFrames i).baseSet := by
  simp [splitFrames, splitDomains, Bundle.Trivial.fiberBundle_trivializationAt']

/-- A native section whose values distinguish the two connected components. -/
def splitSection : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, Bundle.Trivial (ℝ ⊕ ℝ) ℝ⟯ :=
  ⟨Sum.elim (fun _ : ℝ ↦ (2 : ℝ)) (fun _ : ℝ ↦ 3), by
    intro x
    rw [Bundle.contMDiffAt_section_iff]
    have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (Sum.elim (fun _ : ℝ ↦ (2 : ℝ)) (fun _ : ℝ ↦ 3)) :=
      contMDiff_const.sumElim contMDiff_const
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using h x⟩

example :
    ((ContMDiffSection.imaginaryPartCLM (I := 𝓘(ℝ, ℝ)) (n := ∞)
      splitFrames splitDomains splitDomain_subset)
      (ContMDiffSection.ITmulLinearMap 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial (ℝ ⊕ ℝ) ℝ)
        splitSection)) (Sum.inr 0) = 3 := by
  simp only [ContMDiffSection.imaginaryPartCLM_apply,
    ContMDiffSection.imaginaryPartLinearMap_ITmulLinearMap]
  rfl

private abbrev TwoSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev TwoModel := EuclideanSpace ℝ (Fin 2)

private def tangentFrames (x : TwoSphere) :
    Trivialization TwoModel (π TwoModel (TangentSpace (𝓡 2) : TwoSphere → Type)) :=
  trivializationAt TwoModel (TangentSpace (𝓡 2) : TwoSphere → Type) x

private instance tangentFramesAtlas (x : TwoSphere) : MemTrivializationAtlas (tangentFrames x) := by
  dsimp only [tangentFrames]
  infer_instance

private def tangentDomains (x : TwoSphere) : Opens TwoSphere :=
  ⟨(tangentFrames x).baseSet, (tangentFrames x).open_baseSet⟩

private theorem tangentDomain_subset (x : TwoSphere) :
    (tangentDomains x : Set TwoSphere) ⊆ (tangentFrames x).baseSet := Set.Subset.refl _

example :
    letI := ContMDiffSection.frameTopology (I := 𝓡 2) (n := ∞)
      tangentFrames tangentDomains tangentDomain_subset
    letI := ContMDiffSection.frameTopology (I := 𝓡 2) (n := ∞)
      (fun x ↦ (tangentFrames x).complexification) tangentDomains
      (Trivialization.subset_baseSet_complexification tangentFrames tangentDomain_subset)
    Nonempty (Cₛ^∞⟮𝓡 2; Complexification TwoModel,
        fun x : TwoSphere ↦ ℂ ⊗[ℝ] TangentSpace (𝓡 2) x⟯ ≃L[ℝ]
      Cₛ^∞⟮𝓡 2; TwoModel, (TangentSpace (𝓡 2) : TwoSphere → Type)⟯ ×
      Cₛ^∞⟮𝓡 2; TwoModel, (TangentSpace (𝓡 2) : TwoSphere → Type)⟯) :=
  ⟨ContMDiffSection.complexificationEquivProdCLE (I := 𝓡 2) (n := ∞)
    tangentFrames tangentDomains tangentDomain_subset⟩

end TauCeti.Examples.SectionComplexification
