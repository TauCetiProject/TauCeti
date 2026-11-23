/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.InnerProductSpace.Frame.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
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
* `TauCeti.contMDiffOn_overlapOperator`: on a `C^n` Riemannian bundle, the overlap operators
  `analysisMap ε ∘ synthesisMap X` of two families of `C^n` sections are `C^n`.
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
  have hc (i j : Fin d) : ContMDiffOn IB 𝓘(ℝ) n (fun y ↦ Q y (ε i y) (ε j y)) U :=
    hQ.contMDiffOn.clm_bundle_apply₂_trivial (hε i) (hε j)
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

/-- The overlap operators of `C^n` sections `ε` and `X` of a `C^n` Riemannian bundle, reading `X`
in the coordinates of `ε`, depend `C^n` on the base point. -/
theorem contMDiffOn_overlapOperator [IsContMDiffRiemannianBundle IB n F V] {d k : ℕ}
    {ε : Fin d → Π x, V x} {X : Fin k → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i)))
    (hX : ∀ j, CMDiff[U] n (T% (X j))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ (overlapOperator ℝ (ε · y) (X · y)).toContinuousLinearMap) U := by
  -- The coordinates `⟪ε i y, X j y⟫` are `C^n`.
  have hw (j : Fin k) : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ analysisMap ℝ (ε · y) (X j y)) U := by
    have hcoord : ContMDiffOn IB 𝓘(ℝ, Fin d → ℝ) n (fun y i ↦ ⟪ε i y, X j y⟫_ℝ) U :=
      contMDiffOn_pi_module_iff.2 fun i ↦ (hε i).inner_bundle (hX j)
    refine (((EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff (n := n)).contMDiff.comp_contMDiffOn
      hcoord).congr fun y _ ↦ ?_
    ext i
    simp
  -- The overlap operator is the sum of the rank-one maps `a ↦ a j • w j y`.
  have hsum : (fun y ↦ (overlapOperator ℝ (ε · y) (X · y)).toContinuousLinearMap) = fun y ↦
      ∑ j, (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
        (analysisMap ℝ (ε · y) (X j y)) := by
    ext y a : 2
    simp [overlapOperator_def, map_sum, map_smul]
  rw [hsum]
  exact contMDiffOn_finsetSum fun j _ ↦
    ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace.proj j)).contDiff (n := n)).contMDiff.comp_contMDiffOn (hw j)

end TauCeti
