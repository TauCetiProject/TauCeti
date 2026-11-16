/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.InnerProductSpace.Frame
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Fields of bilinear forms read through synthesis maps

Let `Q` be a `C^n` field of bilinear forms on a vector bundle `V` with inner product fibres, and
let `ε₁, …, ε_d` be `C^n` sections of `V` over a set `U`. At each `y ∈ U` the synthesis map
`a ↦ ∑ i, a i • ε i y` reads `Q y` as a bilinear form on the fixed Euclidean space `ℝ^d`, with
matrix entries `Q y (ε i y) (ε j y)`. This file shows that these coordinate forms and their Riesz
operators depend `C^n` on `y`. When the sections form an orthonormal basis at each point, this
turns `Q` into a `C^n` family of operators on a fixed Euclidean space, to which the spectral
calculus of a single space applies.

## Main results

* `TauCeti.contMDiffOn_bilinearComp_synthesisMap`: the coordinate bilinear forms are `C^n`.
* `TauCeti.contMDiffOn_continuousLinearMapOfBilin_bilinearComp_synthesisMap`: their Riesz
  operators are `C^n`.
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
    exact (contMDiffWithinAt_totalSpace_iff.mp h).2
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

end TauCeti
