/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar

/-!
# Top-form Hodge density on an oriented Riemannian manifold

On an oriented Riemannian `k`-manifold `(N, o)`, every rough top form `η` decomposes in all
dimensions (including `k = 0`) as `η x = topFormDensity o η x • riemannianVolumeForm o x`
(`TauCeti.eq_topFormDensity_smul_riemannianVolumeForm`), where `topFormDensity o η x = (⋆η)_x ![]`
has `|topFormDensity o η x| = ‖η x‖` (`TauCeti.abs_topFormDensity`) and inherits `C^n` regularity
from `η` (`TauCeti.IsSmoothForm.contMDiff_topFormDensity`).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N] [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] {k : ℕ}

/-- The scalar density `x ↦ (⋆η)_x ![]` of a rough top form `η` with respect to an orientation `o`
and Riemannian metric on `N`, satisfying `η x = topFormDensity o η x • riemannianVolumeForm o x` in
every dimension `k ≥ 0`. -/
def topFormDensity (o : Manifold.Orientation I' N (Fin k)) (η : RoughForm I' N ℝ k) : N → ℝ :=
  fun x ↦ RoughForm.hodgeStar o (Nat.add_zero k) η x ![]

/-- `RoughForm.hodgeStar` in top degree is `RoughForm.ofFunction` of `topFormDensity`. -/
theorem hodgeStar_eq_ofFunction_topFormDensity (o : Manifold.Orientation I' N (Fin k))
    (η : RoughForm I' N ℝ k) :
    RoughForm.hodgeStar o (Nat.add_zero k) η = RoughForm.ofFunction I' (topFormDensity o η) := by
  refine (RoughForm.eq_ofFunction _).trans ?_
  congr with x
  exact congrArg (RoughForm.hodgeStar o (Nat.add_zero k) η x) (Subsingleton.elim 0 ![])

/-- Every rough top form decomposes as `topFormDensity o η` times `riemannianVolumeForm o` in all
dimensions `k ≥ 0` (including `k = 0`). -/
theorem eq_topFormDensity_smul_riemannianVolumeForm (o : Manifold.Orientation I' N (Fin k))
    (η : RoughForm I' N ℝ k) :
    η = fun x ↦ topFormDensity o η x • riemannianVolumeForm o x := by
  have h := RoughForm.hodgeStar_hodgeStar o (Nat.add_zero k) (Nat.zero_add k) η
  rw [Nat.mul_zero, pow_zero, one_smul, hodgeStar_eq_ofFunction_topFormDensity,
    RoughForm.hodgeStar_ofFunction] at h
  exact h.symm

/-- Reversing the orientation negates `topFormDensity`. -/
@[simp]
theorem topFormDensity_neg_orientation (o : Manifold.Orientation I' N (Fin k))
    (η : RoughForm I' N ℝ k) : topFormDensity (-o) η = -topFormDensity o η := by
  funext x; simp [topFormDensity]

/-- Negating the top form negates `topFormDensity`. -/
@[simp]
theorem topFormDensity_neg (o : Manifold.Orientation I' N (Fin k)) (η : RoughForm I' N ℝ k) :
    topFormDensity o (-η) = -topFormDensity o η := by
  funext x; simp [topFormDensity]

/-- The density of `riemannianVolumeForm o` with respect to `o` is identically `1`. -/
@[simp]
theorem topFormDensity_riemannianVolumeForm (o : Manifold.Orientation I' N (Fin k)) :
    topFormDensity o (riemannianVolumeForm o) = fun _ ↦ 1 := by
  funext x
  have h := congrFun
    (RoughForm.hodgeStar_smul_riemannianVolumeForm o (Nat.add_zero k) (fun _ : N ↦ (1 : ℝ))) x
  simpa [topFormDensity] using congrArg (fun α : TangentSpace I' x [⋀^Fin 0]→L[ℝ] ℝ ↦ α ![]) h

/-- At every point `x`, `|topFormDensity o η x|` equals the operator norm (comass) `‖η x‖`, in all
dimensions `k ≥ 0` (including `k = 0`). -/
@[simp]
theorem abs_topFormDensity (o : Manifold.Orientation I' N (Fin k)) (η : RoughForm I' N ℝ k)
    (x : N) : |topFormDensity o η x| = ‖η x‖ := by
  let := o.fact_finrank_tangentSpace x
  have hnorm : ‖η x‖ = ‖topFormDensity o η x • (o.orientationAt x).volumeFormL‖ :=
    congrArg Norm.norm <| (congrFun (eq_topFormDensity_smul_riemannianVolumeForm o η) x).trans
      (congrArg (topFormDensity o η x • ·) (riemannianVolumeForm_def o x))
  rw [hnorm, norm_smul, Real.norm_eq_abs, (o.orientationAt x).norm_volumeFormL, mul_one]

/-- A rough top form `η` equals `riemannianVolumeForm o` if and only if `topFormDensity o η x = 1`
at every point `x`. -/
theorem eq_riemannianVolumeForm_iff_topFormDensity_eq_one (o : Manifold.Orientation I' N (Fin k))
    (η : RoughForm I' N ℝ k) : η = riemannianVolumeForm o ↔ ∀ x, topFormDensity o η x = 1 := by
  refine ⟨fun h x ↦ by simp [h], fun h ↦ ?_⟩
  rw [eq_topFormDensity_smul_riemannianVolumeForm o η]; funext x; rw [h x, one_smul]

/-- For a `C^n` top form on a `C^(n+1)` Riemannian manifold, `topFormDensity o η` is `C^n`. -/
theorem IsSmoothForm.contMDiff_topFormDensity {n : WithTop ℕ∞} [IsManifold I' (n + 1) N]
    [IsContMDiffRiemannianBundle I' n E' (fun x : N ↦ TangentSpace I' x)]
    (o : Manifold.Orientation I' N (Fin k)) {η : RoughForm I' N ℝ k} (hη : IsSmoothForm I' n η) :
    ContMDiff I' 𝓘(ℝ) n (topFormDensity o η) :=
  isSmoothForm_ofFunction_iff.1 <| hodgeStar_eq_ofFunction_topFormDensity o η ▸
    hη.hodgeStar o (Nat.add_zero k)

end TauCeti

end
