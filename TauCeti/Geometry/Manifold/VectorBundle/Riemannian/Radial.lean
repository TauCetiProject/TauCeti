/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Topology.VectorBundle.Ball
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Radial compression of Riemannian vector bundles

A real vector bundle with a smoothly varying fibre inner product admits a smooth radial
identification of its entire total space with its open unit ball bundle. The identification
preserves the base point and fixes the zero section. Composing with positive smooth scalar
rescaling gives variable-radius coordinates, as used in whole-normal-bundle parametrizations
of tubular neighbourhoods.

The fibre maps are Mathlib's `OpenPartialHomeomorph.univUnitBall`, by Yury Kudryashov and
Oliver Nash. Smoothness on the total space uses the smooth fibre inner product; no
orthonormal trivialization or global frame is needed. The rescaling assembly follows
`normalBundleRadialPartialDiffeomorphOfRadius`, now for arbitrary Riemannian vector bundles.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3 (tubular neighbourhoods).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {B : Type*} {V : B → Type*} {F : Type*}
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V]

/-- A smooth fibre metric makes radial compression a partial diffeomorphism from the whole
total space onto the open unit ball bundle. The smooth structure is the original bundle
structure in both directions. -/
def vectorBundleRadialPartialDiffeomorph :
    PartialDiffeomorph (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F))
      (TotalSpace F V) (TotalSpace F V) n := by
  have hsq : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) n
      (fun p : TotalSpace F V => ‖p.2‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contMDiff_id (I := I.prod 𝓘(ℝ, F)) (n := n)).inner_bundle contMDiff_id
  have hforward : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) n
      (fun p : TotalSpace F V => Real.sqrt (1 + ‖p.2‖ ^ 2)) := by
    intro p
    exact (Real.contDiffAt_sqrt (by positivity : 1 + ‖p.2‖ ^ 2 ≠ 0)).comp_contMDiffAt
      (f := fun q : TotalSpace F V => 1 + ‖q.2‖ ^ 2)
      ((contMDiff_const (c := (1 : ℝ))).add hsq).contMDiffAt
  have hinverse : ContMDiffOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) n
      (fun p : TotalSpace F V => Real.sqrt (1 - ‖p.2‖ ^ 2)) {p | ‖p.2‖ < 1} := by
    intro p hp
    have hpos : 0 < 1 - ‖p.2‖ ^ 2 := by nlinarith [norm_nonneg p.2, show ‖p.2‖ < 1 from hp]
    exact (Real.contDiffAt_sqrt hpos.ne').comp_contMDiffWithinAt
      (f := fun q : TotalSpace F V => 1 - ‖q.2‖ ^ 2)
      ((contMDiff_const (c := (1 : ℝ))).sub hsq).contMDiffAt.contMDiffWithinAt
  refine
    { toFun := TotalSpace.radialMap
      invFun := TotalSpace.radialInverse
      source := univ
      target := {p | ‖p.2‖ < 1}
      map_source' := fun p _ => p.norm_radialMap_lt_one
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun p _ => TotalSpace.radialInverse_map p
      right_inv' := fun p hp => TotalSpace.radialMap_inverse p hp
      open_source := isOpen_univ
      open_target := ?_
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · have hnorm : Continuous (fun p : TotalSpace F V => ‖p.2‖) :=
      hsq.continuous.sqrt.congr (fun p => Real.sqrt_sq (norm_nonneg p.2))
    exact isOpen_lt hnorm continuous_const
  · exact ((hforward.inv₀ (fun p => Real.sqrt_ne_zero'.mpr (by positivity))).smul_totalSpace
      contMDiff_id).contMDiffOn.congr (fun p _ => TotalSpace.radialMap_apply p)
  · exact ((hinverse.inv₀ (fun p hp => Real.sqrt_ne_zero'.mpr
      (by nlinarith [norm_nonneg p.2, show ‖p.2‖ < 1 from hp]))).smul_totalSpace
      contMDiff_id.contMDiffOn).congr
      (fun p _ => TotalSpace.radialInverse_apply p)

/-- The source of radial compression is the entire total space. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorph_source :
    (vectorBundleRadialPartialDiffeomorph (I := I) (F := F) (V := V) (n := n)).source =
      univ := (rfl)

/-- The target of radial compression is exactly the open unit ball bundle. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorph_target :
    (vectorBundleRadialPartialDiffeomorph (I := I) (F := F) (V := V) (n := n)).target =
      {p | ‖p.2‖ < 1} := (rfl)

/-- The partial diffeomorphism acts by fibrewise radial compression. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorph_apply (p : TotalSpace F V) :
    vectorBundleRadialPartialDiffeomorph (I := I) (n := n) p =
      TotalSpace.radialMap p := (rfl)

/-- The inverse partial diffeomorphism acts by fibrewise radial expansion. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorph_symm_apply (p : TotalSpace F V) :
    (vectorBundleRadialPartialDiffeomorph (I := I) (n := n)).toPartialEquiv.symm p =
      TotalSpace.radialInverse p := (rfl)

/-- Radial compression followed by positive smooth rescaling identifies the entire total
space with its variable-radius open ball bundle. -/
def vectorBundleRadialPartialDiffeomorphOfRadius {r : B → ℝ}
    (hr : ContMDiff I 𝓘(ℝ) n r) (hrpos : ∀ b, 0 < r b) :
    PartialDiffeomorph (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F))
      (TotalSpace F V) (TotalSpace F V) n :=
  (vectorBundleRadialPartialDiffeomorph (V := V)).trans
    (vectorBundleScalarDiffeomorph r hr (fun b => (hrpos b).ne')).toPartialDiffeomorph

variable {r : B → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r) (hrpos : ∀ b, 0 < r b)

private theorem vectorBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv :
    (vectorBundleRadialPartialDiffeomorphOfRadius (F := F) (V := V) hr hrpos).toPartialEquiv =
      (vectorBundleRadialPartialDiffeomorph (I := I) (F := F) (V := V)
        (n := n)).toPartialEquiv.trans
        (vectorBundleScalarDiffeomorph r hr (fun b => (hrpos b).ne')).toEquiv.toPartialEquiv := by
  unfold vectorBundleRadialPartialDiffeomorphOfRadius
  rw [PartialDiffeomorph.trans_toPartialEquiv]
  exact congrArg
    ((vectorBundleRadialPartialDiffeomorph (I := I) (F := F) (V := V)
      (n := n)).toPartialEquiv.trans)
    (Diffeomorph.toPartialDiffeomorph_toPartialEquiv _)

/-- Variable-radius compression is defined on the entire total space. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorphOfRadius_source :
    (vectorBundleRadialPartialDiffeomorphOfRadius (F := F) (V := V) hr hrpos).source =
      univ := by
  rw [vectorBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv]
  simp [PartialEquiv.trans_source]

/-- The target consists exactly of vectors shorter than the prescribed positive radius. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorphOfRadius_target :
    (vectorBundleRadialPartialDiffeomorphOfRadius (F := F) (V := V) hr hrpos).target =
      {p | ‖p.2‖ < r p.proj} := by
  rw [vectorBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv,
    PartialEquiv.trans_target'']
  simpa [fun b => Real.norm_of_nonneg (hrpos b).le] using
    (vectorBundleScalarDiffeomorph_image_setOf_norm_lt (F := F) (V := V)
      r hr (fun b => (hrpos b).ne') (fun _ => 1))

/-- Variable-radius compression first compresses into the unit ball, then rescales. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorphOfRadius_apply (p : TotalSpace F V) :
    vectorBundleRadialPartialDiffeomorphOfRadius hr hrpos p =
      vectorBundleScalarDiffeomorph r hr (fun b => (hrpos b).ne')
        (TotalSpace.radialMap p) := by
  exact congrArg (fun e : PartialEquiv (TotalSpace F V) (TotalSpace F V) => e p)
    (vectorBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv hr hrpos)

/-- The inverse first divides by the radius, then expands the unit ball. -/
@[simp] theorem vectorBundleRadialPartialDiffeomorphOfRadius_symm_apply (p : TotalSpace F V) :
    (vectorBundleRadialPartialDiffeomorphOfRadius hr hrpos).toPartialEquiv.symm p =
      TotalSpace.radialInverse
        ((vectorBundleScalarDiffeomorph r hr (fun b => (hrpos b).ne')).symm p) := by
  exact congrArg (fun e : PartialEquiv (TotalSpace F V) (TotalSpace F V) => e.symm p)
    (vectorBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv hr hrpos)

end TauCeti
