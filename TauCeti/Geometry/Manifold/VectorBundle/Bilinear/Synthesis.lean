/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.InnerProductSpace.Frame
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension

/-!
# Fields of bilinear forms read through synthesis maps

Let `Q` be a `C^n` field of bilinear forms on a vector bundle `V` with inner product fibres, and
let `ε₁, …, ε_d` be `C^n` sections of `V` over a set `U`. At each `y ∈ U` the synthesis map
`a ↦ ∑ i, a i • ε i y` reads `Q y` as a bilinear form on the fixed Euclidean space `ℝ^d`, with
matrix entries `Q y (ε i y) (ε j y)`. This file shows that these coordinate forms and their Riesz
operators depend `C^n` on `y`. When the sections form an orthonormal basis at each point, this
turns `Q` into a `C^n` family of operators on a fixed Euclidean space, to which the spectral
calculus of a single space applies.

The same holds when `Q` is read through a trivialization `e` of the atlas: over the base set of
`e`, the forms `(u, v) ↦ Q y (e.symm y u) (e.symm y v)` on the model fibre are a `C^n` family.
Here the fibres need no inner product.

## Main results

* `TauCeti.contMDiffOn_bilinearComp_synthesisMap`: the coordinate bilinear forms are `C^n`.
* `TauCeti.contMDiffOn_continuousLinearMapOfBilin_bilinearComp_synthesisMap`: their Riesz
  operators are `C^n`.
* `TauCeti.contMDiffOn_compl₁₂_symmₗ`: a `C^n` field of bilinear forms read in a
  trivialization is `C^n` on its base set.
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} {Q : Π x, V x →L[ℝ] V x →L[ℝ] ℝ}

/-- Read through the synthesis maps of a `C^n` family of sections, a `C^n` field of bilinear forms
is a `C^n` family of bilinear forms on a fixed Euclidean space. -/
theorem contMDiffOn_bilinearComp_synthesisMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) n
      (fun y ↦ (Q y).bilinearComp (synthesisMap ℝ (ε · y)).toContinuousLinearMap
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap) U := by
  have hc (i j : Fin d) : ContMDiffOn IB 𝓘(ℝ) n (fun y ↦ Q y (ε i y) (ε j y)) U := fun y hy ↦ by
    have h := ContMDiffWithinAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial B ℝ)
      (b := id) (hQ y).contMDiffWithinAt (hε i y hy) (hε j y hy)
    exact (contMDiffWithinAt_totalSpace.mp h).2
  simp_rw [bilinearComp_synthesisMap_eq_sum]
  exact contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
    (hc i j).smul contMDiffOn_const

/-- Read through the synthesis maps of a `C^n` family of sections, a `C^n` field of bilinear forms
has a `C^n` Riesz operator in coordinates. -/
theorem contMDiffOn_continuousLinearMapOfBilin_bilinearComp_synthesisMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ continuousLinearMapOfBilin ((Q y).bilinearComp
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap)) U :=
  contDiff_continuousLinearMapOfBilin.contMDiff.comp_contMDiffOn
    (contMDiffOn_bilinearComp_synthesisMap hQ hε)

section Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

/-- **A `C^n` field of bilinear forms read in a trivialization.** Over the base set of a
trivialization `e` in the atlas of `V`, a `C^n` field `β` of bilinear forms on the fibres reads as
the `C^n` family `y ↦ β y (e.symm y ·) (e.symm y ·)` of bilinear forms on the model fibre. -/
theorem contMDiffOn_compl₁₂_symmₗ {β : ∀ x, V x →L[𝕜] V x →L[𝕜] G}
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] V y →L[𝕜] G) x (β x)))
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G) n
      (fun y ↦ ((β y).toLinearMap₁₂.compl₁₂ (e.symmₗ 𝕜 y)
        (e.symmₗ 𝕜 y)).toContinuousBilinearMap) e.baseSet := by
  intro y hy
  -- Each fixed vector of the model fibre reads as a `C^n` section over the base set.
  have hs (u : F) : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n
      (fun z ↦ TotalSpace.mk' F z (e.symm z u)) e.baseSet y :=
    (e.contMDiffWithinAt_iff (by simpa [e.mem_source] using hy)).mpr
      ⟨contMDiffWithinAt_id, (contMDiffWithinAt_const (c := u)).congr (fun z hz ↦ by
        simp [e.apply_mk_symm hz]) (by simp [e.apply_mk_symm hy])⟩
  refine TauCeti.contMDiffWithinAt_clm_apply.mpr fun v ↦
    TauCeti.contMDiffWithinAt_clm_apply.mpr fun w ↦ ?_
  have h := ContMDiffWithinAt.clm_bundle_apply₂ (F₃ := G) (E₃ := Bundle.Trivial B G)
    (b := id) (hβ y).contMDiffWithinAt (hs v) (hs w)
  exact (contMDiffWithinAt_totalSpace.mp h).2.congr
    (fun z hz ↦ by simp [e.symmₗ_apply hz]) (by simp [e.symmₗ_apply hy])

end Trivialization

end TauCeti
