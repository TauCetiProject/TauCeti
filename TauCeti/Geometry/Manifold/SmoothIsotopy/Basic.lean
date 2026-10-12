/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Smooth isotopies through embeddings

A `SmoothIsotopy f₀ f₁` is a jointly `C^n` map on `unitInterval × M` from `f₀` to
`f₁` whose time slices are smooth embeddings. The endpoints are arbitrary bundled
smooth maps; existence of an isotopy forces them to be embeddings.

The time interval carries Mathlib's manifold-with-boundary structure. Forgetting
smoothness produces the existing continuous `TauCeti.Isotopy`, with exactly the
same time slices. Constant isotopies, smooth changes of time, and time reversal
are provided here. Smooth concatenation is provided in `SmoothIsotopy.Trans`;
isotopy extension is a separate result.

This slice-wise convention does not impose properness on a noncompact source.
Ambient isotopy remains the relation used for knot equivalence; a smooth isotopy
is the input to an isotopy extension theorem, rather than an assertion that such
an extension exists.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1.

The continuous forgetful construction follows Mathlib's `ContinuousMap.HomotopyWith`
and Tau Ceti's `Isotopy`.
-/

public section

noncomputable section

namespace TauCeti

open Topology Manifold
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- A jointly `C^n` homotopy through smooth embeddings, with prescribed endpoints.
The source and target may have boundary or corners. -/
structure SmoothIsotopy (f₀ f₁ : C^n⟮I, M; J, N⟯) where
  /-- The motion, smooth in both time and the source variable. -/
  toContMDiffMap : C^n⟮(𝓡∂ 1).prod I, unitInterval × M; J, N⟯
  /-- The motion starts at `f₀`. -/
  map_zero_left (x : M) : toContMDiffMap (0, x) = f₀ x
  /-- The motion ends at `f₁`. -/
  map_one_left (x : M) : toContMDiffMap (1, x) = f₁ x
  /-- Every time slice is a smooth embedding. -/
  isSmoothEmbedding (t : unitInterval) :
    Manifold.IsSmoothEmbedding I J n (fun x => toContMDiffMap (t, x))

namespace SmoothIsotopy

variable {f₀ f₁ : C^n⟮I, M; J, N⟯}

/-- Evaluate a smooth isotopy at a time and a source point. -/
instance : FunLike (SmoothIsotopy f₀ f₁) (unitInterval × M) N where
  coe F := F.toContMDiffMap
  coe_injective F G h := by
    cases F
    cases G
    have := ContMDiffMap.coe_injective h
    cases this
    rfl

/-- The underlying smooth map evaluates to the motion. -/
@[simp]
theorem toContMDiffMap_apply (F : SmoothIsotopy f₀ f₁) (p : unitInterval × M) :
    F.toContMDiffMap p = F p := (rfl)

/-- The motion starts at its initial endpoint. -/
@[simp]
theorem apply_zero (F : SmoothIsotopy f₀ f₁) (x : M) : F (0, x) = f₀ x :=
  F.map_zero_left x

/-- The motion ends at its final endpoint. -/
@[simp]
theorem apply_one (F : SmoothIsotopy f₀ f₁) (x : M) : F (1, x) = f₁ x :=
  F.map_one_left x

/-- Two smooth isotopies agree when their motions agree pointwise. -/
@[ext]
theorem ext {F G : SmoothIsotopy f₀ f₁} (h : ∀ p, F p = G p) : F = G :=
  DFunLike.ext F G h

/-- A smooth isotopy is jointly smooth in time and space. -/
theorem contMDiff (F : SmoothIsotopy f₀ f₁) :
    ContMDiff ((𝓡∂ 1).prod I) J n F := F.toContMDiffMap.contMDiff

/-- The time-`t` slice, bundled as a smooth embedding. -/
def timeSlice (F : SmoothIsotopy f₀ f₁) (t : unitInterval) :
    SmoothEmbedding I J n M N :=
  SmoothEmbedding.ofIsSmoothEmbedding (fun x => F (t, x)) (F.isSmoothEmbedding t)

/-- Evaluating a time slice is evaluating the isotopy at that time. -/
@[simp]
theorem timeSlice_apply (F : SmoothIsotopy f₀ f₁) (t : unitInterval) (x : M) :
    F.timeSlice t x = F (t, x) := by
  simp only [timeSlice, SmoothEmbedding.ofIsSmoothEmbedding_apply]

/-- The initial endpoint of a smooth isotopy is a smooth embedding. -/
theorem isSmoothEmbedding_left (F : SmoothIsotopy f₀ f₁) :
    Manifold.IsSmoothEmbedding I J n f₀ := by
  have h : (fun x => F.toContMDiffMap (0, x)) = f₀ := funext F.map_zero_left
  simpa only [h] using F.isSmoothEmbedding 0

/-- The final endpoint of a smooth isotopy is a smooth embedding. -/
theorem isSmoothEmbedding_right (F : SmoothIsotopy f₀ f₁) :
    Manifold.IsSmoothEmbedding I J n f₁ := by
  have h : (fun x => F.toContMDiffMap (1, x)) = f₁ := funext F.map_one_left
  simpa only [h] using F.isSmoothEmbedding 1

/-- Forgetting smoothness gives a continuous isotopy through embeddings. -/
def toIsotopy (F : SmoothIsotopy f₀ f₁) :
    Isotopy (_root_.toContinuousMap f₀) (_root_.toContinuousMap f₁) where
  toFun := F
  continuous_toFun := F.contMDiff.continuous
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' t := (F.isSmoothEmbedding t).isEmbedding

/-- Forgetting smoothness preserves the motion. -/
@[simp]
theorem toIsotopy_apply (F : SmoothIsotopy f₀ f₁) (p : unitInterval × M) :
    F.toIsotopy p = F p := (rfl)

/-- Smooth isotopy implies the existing continuous isotopy relation. -/
theorem isotopic (F : SmoothIsotopy f₀ f₁) :
    Isotopic (_root_.toContinuousMap f₀) (_root_.toContinuousMap f₁) :=
  Isotopic.of_isotopy F.toIsotopy

/-- The constant smooth isotopy at a smooth embedding. -/
def _root_.ContMDiffMap.smoothIsotopyRefl (f : C^n⟮I, M; J, N⟯)
    (hf : Manifold.IsSmoothEmbedding I J n f) :
    SmoothIsotopy f f where
  toContMDiffMap := ⟨fun p => f p.2, f.contMDiff.comp contMDiff_snd⟩
  map_zero_left _ := rfl
  map_one_left _ := rfl
  isSmoothEmbedding _ := hf

/-- A constant isotopy keeps its source points stationary. -/
@[simp]
theorem _root_.ContMDiffMap.smoothIsotopyRefl_apply (f : C^n⟮I, M; J, N⟯)
    (hf : Manifold.IsSmoothEmbedding I J n f)
    (p : unitInterval × M) : f.smoothIsotopyRefl hf p = f p.2 := (rfl)

/-- Change time by a smooth map of the unit interval fixing its endpoints.
The time map need not be injective or monotone. -/
def reparam (F : SmoothIsotopy f₀ f₁)
    (ρ : C^n⟮𝓡∂ 1, unitInterval; 𝓡∂ 1, unitInterval⟯) (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) :
    SmoothIsotopy f₀ f₁ where
  toContMDiffMap := ⟨fun p => F (ρ p.1, p.2),
    F.contMDiff.comp ((ρ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)⟩
  map_zero_left x := by
    dsimp
    rw [h₀]
    exact F.map_zero_left x
  map_one_left x := by
    dsimp
    rw [h₁]
    exact F.map_one_left x
  isSmoothEmbedding t := F.isSmoothEmbedding (ρ t)

/-- A time change evaluates the original isotopy at the new time. -/
@[simp]
theorem reparam_apply (F : SmoothIsotopy f₀ f₁)
    (ρ : C^n⟮𝓡∂ 1, unitInterval; 𝓡∂ 1, unitInterval⟯) (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1)
    (p : unitInterval × M) : F.reparam ρ h₀ h₁ p = F (ρ p.1, p.2) := (rfl)

/-- Reverse a smooth isotopy in time. -/
def symm (F : SmoothIsotopy f₀ f₁) : SmoothIsotopy f₁ f₀ where
  toContMDiffMap := ⟨fun p => F (unitInterval.symm p.1, p.2),
    F.contMDiff.comp ((unitInterval.contMDiff_symm.comp contMDiff_fst).prodMk contMDiff_snd)⟩
  map_zero_left x := by
    dsimp
    rw [unitInterval.symm_zero]
    exact F.map_one_left x
  map_one_left x := by
    dsimp
    rw [unitInterval.symm_one]
    exact F.map_zero_left x
  isSmoothEmbedding t := F.isSmoothEmbedding (unitInterval.symm t)

/-- Time reversal evaluates the original isotopy at `1 - t`. -/
@[simp]
theorem symm_apply (F : SmoothIsotopy f₀ f₁) (p : unitInterval × M) :
    F.symm p = F (unitInterval.symm p.1, p.2) := (rfl)

/-- Reversing time twice recovers the original smooth isotopy. -/
@[simp]
theorem symm_symm (F : SmoothIsotopy f₀ f₁) : F.symm.symm = F := by
  ext p
  simp

end SmoothIsotopy

/-- Two bundled smooth maps are smoothly isotopic when a jointly smooth homotopy
through smooth embeddings connects them. This does not assert ambient isotopy. -/
def SmoothIsotopic (f₀ f₁ : C^n⟮I, M; J, N⟯) : Prop :=
  Nonempty (SmoothIsotopy f₀ f₁)

/-- Smooth isotopy is witnessed by a smooth isotopy through embeddings. -/
theorem smoothIsotopic_def {f₀ f₁ : C^n⟮I, M; J, N⟯} :
    SmoothIsotopic f₀ f₁ ↔ Nonempty (SmoothIsotopy f₀ f₁) := (Iff.rfl)

namespace SmoothIsotopic

variable {f₀ f₁ : C^n⟮I, M; J, N⟯}

/-- A smooth embedding is smoothly isotopic to itself. -/
@[refl]
theorem _root_.ContMDiffMap.smoothIsotopic_refl (f : C^n⟮I, M; J, N⟯)
    (hf : Manifold.IsSmoothEmbedding I J n f) :
    SmoothIsotopic f f := smoothIsotopic_def.mpr ⟨f.smoothIsotopyRefl hf⟩

/-- Smooth isotopy is symmetric. -/
@[symm]
theorem symm (h : SmoothIsotopic f₀ f₁) : SmoothIsotopic f₁ f₀ := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp h
  exact smoothIsotopic_def.mpr ⟨F.symm⟩

/-- Smoothly isotopic maps are isotopic after forgetting smoothness. -/
theorem isotopic (h : SmoothIsotopic f₀ f₁) :
    Isotopic (_root_.toContinuousMap f₀) (_root_.toContinuousMap f₁) := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp h
  exact F.isotopic

end SmoothIsotopic

end TauCeti
