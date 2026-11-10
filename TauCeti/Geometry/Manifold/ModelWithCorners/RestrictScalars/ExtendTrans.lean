/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Real loci in holomorphic charts after restriction of scalars

In a holomorphic chart, a subset cut out by the real locus `star z = z` of complex coordinates has
real coordinates, for the model with restricted scalars, given by the image of that locus under the
induced real linear equivalence (`OpenPartialHomeomorph.image_inter_setOf_star_eq_image_inter`).
This is the chart identity behind the realification of complex analytic submanifolds.

This file is separate from `RestrictScalars.Chart` so that the many importers of that module do not
import `TauCeti.Geometry.Manifold.ExtChartAt`, whose `TauCeti.Manifold` namespace makes
`open scoped Manifold` ambiguous.
-/

public section

open Set

namespace OpenPartialHomeomorph

/-- In a holomorphic chart `φ`, if a subset `s` agrees on `W` with the locus `star z = z` of the
complex coordinates `e_ℂ`, then the real coordinates `e_ℝ` of `s` near `W` are the image of that
locus under the real linear equivalence `(e_ℂ.restrictScalars ℝ).symm.trans e_ℝ`. -/
theorem image_inter_setOf_star_eq_image_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] {n m : ℕ} {s : Set M}
    (e_ℂ : E ≃L[ℂ] Fin n → ℂ) (e_ℝ : E ≃L[ℝ] Fin m → ℝ) (φ : OpenPartialHomeomorph M H)
    {W : Set M}
    (hWs : ∀ y ∈ W, y ∈ s ↔ star (e_ℂ (φ.extend I y)) = e_ℂ (φ.extend I y)) :
    ((e_ℂ.restrictScalars' ℝ).symm.trans e_ℝ) ''
        ((φ.extendTrans I e_ℂ.toHomeomorph).target ∩
          (φ.extendTrans I e_ℂ.toHomeomorph).symm ⁻¹' W ∩ {z : Fin n → ℂ | star z = z}) =
      ((φ.extendTrans (I.restrictScalars ℝ) e_ℝ.toHomeomorph).target ∩
        (φ.extendTrans (I.restrictScalars ℝ) e_ℝ.toHomeomorph).symm ⁻¹' W) ∩
        (e_ℝ ∘ φ.extend (I.restrictScalars ℝ)) '' (s ∩ φ.source) := by
  set Φ_ℂ := φ.extendTrans I e_ℂ.toHomeomorph
  set Φ_ℝ := φ.extendTrans (I.restrictScalars ℝ) e_ℝ.toHomeomorph
  let e_ℂ' : E ≃L[ℝ] Fin n → ℂ := e_ℂ.restrictScalars' ℝ
  let L : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ := e_ℂ'.symm.trans e_ℝ
  ext u
  constructor
  · rintro ⟨z, ⟨⟨hzt, hzW⟩, hzstar⟩, rfl⟩
    set y := Φ_ℂ.symm z
    have hyΦ_ℂ : y ∈ Φ_ℂ.source := Φ_ℂ.map_target hzt
    have hyφ : y ∈ φ.source := by simpa [Φ_ℂ] using hyΦ_ℂ
    have hyW : y ∈ W := hzW
    have hzy : Φ_ℂ y = z := Φ_ℂ.right_inv hzt
    have hys : y ∈ s := (hWs y hyW).2 (by simpa [Φ_ℂ, ← hzy] using hzstar)
    have hLy : L z = e_ℝ (φ.extend (I.restrictScalars ℝ) y) := by
      rw [← hzy]
      simp [L, e_ℂ', Φ_ℂ]
    rw [hLy]
    have hyΦ_ℝ : y ∈ Φ_ℝ.source := by simpa [Φ_ℝ] using hyφ
    have h1 : Φ_ℝ y = e_ℝ (φ.extend (I.restrictScalars ℝ) y) := by simp [Φ_ℝ]
    refine ⟨?_, y, ⟨hys, hyφ⟩, rfl⟩
    rw [← h1]
    exact ⟨Φ_ℝ.map_source hyΦ_ℝ, by simpa [Φ_ℝ.left_inv hyΦ_ℝ] using hyW⟩
  · rintro ⟨huU, y, ⟨hys, hyφ⟩, rfl⟩
    have hyΦ_ℝ : y ∈ Φ_ℝ.source := by simpa [Φ_ℝ] using hyφ
    have h1 : Φ_ℝ y = e_ℝ (φ.extend (I.restrictScalars ℝ) y) := by simp [Φ_ℝ]
    have hw : Φ_ℝ.symm (e_ℝ (φ.extend (I.restrictScalars ℝ) y)) ∈ W := huU.2
    have hyW : y ∈ W := by rwa [← h1, Φ_ℝ.left_inv hyΦ_ℝ] at hw
    have hyΦ_ℂ : y ∈ Φ_ℂ.source := by simpa [Φ_ℂ] using hyφ
    refine ⟨Φ_ℂ y, ⟨⟨Φ_ℂ.map_source hyΦ_ℂ, by simpa [Φ_ℂ.left_inv hyΦ_ℂ] using hyW⟩, ?_⟩, ?_⟩
    · simpa [Φ_ℂ] using (hWs y hyW).1 hys
    · simp [Φ_ℂ]

end OpenPartialHomeomorph
