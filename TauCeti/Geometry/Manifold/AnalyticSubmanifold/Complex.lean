/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Complex
public import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Basic
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.Euclidean
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Complex analytic submanifolds and realification on complex manifolds

This file connects complex and real analytic submanifolds on manifolds:

* **Realification of complex analytic submanifolds**
  (`TauCeti.IsMAnalyticSubmanifold.restrictScalars_complex`,
  `TauCeti.IsMAnalyticSubmanifold.real_of_complex`,
  `TauCeti.IsMAnalyticSubmanifold.complexEuclideanRealModel`): every `d`-dimensional complex
  analytic submanifold of a boundaryless charted space modelled on `I : ModelWithCorners ℂ E H` is a
  `(2 * d)`-dimensional real analytic submanifold for `I.restrictScalars ℝ` (in particular for
  `𝓘(ℝ, E)` when `I = 𝓘(ℂ, E)`, and for `TauCeti.complexEuclideanRealModel n` on complex Euclidean
  manifolds) and any real coordinate equivalence into `Fin m → ℝ`.
* **Conjugation-fixed real loci in holomorphic charts**
  (`TauCeti.isMAnalyticSubmanifold_restrictScalars_of_holomorphicChart_star_eq`,
  `TauCeti.isMAnalyticSubmanifold_of_holomorphicChart_star_eq`,
  `TauCeti.isMAnalyticSubmanifold_complexEuclideanRealModel_of_holomorphicChart_star_eq`): on a
  boundaryless complex `C^r` manifold (`r ≠ 0`) with complex coordinates `e_ℂ : E ≃L[ℂ] Fin n → ℂ`,
  any nonempty subset locally cut out in holomorphic charts by coordinatewise conjugation invariance
  is an `n`-dimensional real analytic submanifold of the underlying real-analytic manifold.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §1.2–1.3.
* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
* H. Whitney and F. Bruhat, *Quelques propriétés fondamentales des ensembles analytiques-réels*,
  Commentarii Mathematici Helvetici 33 (1959), 132–160.
-/

public section

noncomputable section

open Set Topology IsManifold
open scoped Manifold ContDiff

namespace TauCeti

section RestrictScalars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n m d : ℕ} {s : Set M}

/-- Every `d`-dimensional complex analytic submanifold of a boundaryless charted space modelled on
`I : ModelWithCorners ℂ E H` is a `(2 * d)`-dimensional real analytic submanifold for the scalar
restriction `I.restrictScalars ℝ` and any real continuous linear equivalence
`e_ℝ : E ≃L[ℝ] Fin m → ℝ`. -/
theorem IsMAnalyticSubmanifold.restrictScalars_complex {e_ℂ : E ≃L[ℂ] Fin n → ℂ}
    (hs : IsMAnalyticSubmanifold I e_ℂ d s) (e_ℝ : E ≃L[ℝ] Fin m → ℝ) :
    IsMAnalyticSubmanifold (I.restrictScalars ℝ) e_ℝ (2 * d) s := by
  let e_ℂ' : E ≃L[ℝ] Fin n → ℂ := e_ℂ.restrictScalars' ℝ
  let L : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ := e_ℂ'.symm.trans e_ℝ
  rw [isMAnalyticSubmanifold_iff]
  refine ⟨hs.nonempty, fun x hx ↦ ?_⟩
  rw [ModelWithCorners.extChartAt_restrictScalars]
  have himg := (hs.image_extChartAt hx).image_realContinuousLinearEquiv L
  have heq : L '' ((e_ℂ ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) =
      (e_ℝ ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) := by
    rw [← image_comp]
    refine image_congr fun y _ ↦ ?_
    simp [L, e_ℂ']
  rwa [heq] at himg

/-- Every `d`-dimensional complex analytic submanifold of a charted space modelled on `𝓘(ℂ, E)` is
a `(2 * d)`-dimensional real analytic submanifold for `𝓘(ℝ, E)` and any real coordinate equivalence
`e_ℝ : E ≃L[ℝ] Fin m → ℝ`. -/
theorem IsMAnalyticSubmanifold.real_of_complex {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {s : Set M} {e_ℂ : E ≃L[ℂ] Fin n → ℂ}
    (hs : IsMAnalyticSubmanifold 𝓘(ℂ, E) e_ℂ d s) (e_ℝ : E ≃L[ℝ] Fin m → ℝ) :
    IsMAnalyticSubmanifold 𝓘(ℝ, E) e_ℝ (2 * d) s := by
  simpa only [modelWithCornersSelf_restrictScalars] using hs.restrictScalars_complex e_ℝ

/-- Every `d`-dimensional complex analytic submanifold of a charted space modelled on
`𝓘(ℂ, EuclideanSpace ℂ (Fin n))` is a `(2 * d)`-dimensional real analytic submanifold for
`TauCeti.complexEuclideanRealModel n` and any real coordinate equivalence
`e_ℝ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ] Fin m → ℝ`. -/
theorem IsMAnalyticSubmanifold.complexEuclideanRealModel
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    {s : Set M} {k : ℕ} {e_ℂ : EuclideanSpace ℂ (Fin n) ≃L[ℂ] Fin k → ℂ}
    (hs : IsMAnalyticSubmanifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) e_ℂ d s)
    (e_ℝ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ] Fin m → ℝ) :
    IsMAnalyticSubmanifold (TauCeti.complexEuclideanRealModel n) e_ℝ (2 * d) s := by
  rw [complexEuclideanRealModel_def, isMAnalyticSubmanifold_transContinuousLinearEquiv_iff]
  exact hs.real_of_complex _

end RestrictScalars

section RealLocus

/-- In a holomorphic chart `φ`, if a subset `s` agrees on `W` with the locus `star z = z` of the
complex coordinates `e_ℂ`, then the real coordinates `e_ℝ` of `s` near `W` are the image of that
locus under the real linear equivalence `(e_ℂ.restrictScalars ℝ).symm.trans e_ℝ`. -/
private theorem image_inter_setOf_star_eq_image_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n m : ℕ} {s : Set M}
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

/-- On a boundaryless complex `C^r` manifold (`r ≠ 0`) modelled on `I : ModelWithCorners ℂ E H` with
complex coordinates `e_ℂ : E ≃L[ℂ] Fin n → ℂ`, any nonempty subset `s ⊆ M` locally cut out in
holomorphic charts by `star (e_ℂ (φ.extend I y)) = e_ℂ (φ.extend I y)` is an `n`-dimensional real
analytic submanifold of `M` for `I.restrictScalars ℝ` and any `e_ℝ : E ≃L[ℝ] Fin m → ℝ`. -/
theorem isMAnalyticSubmanifold_restrictScalars_of_holomorphicChart_star_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {r : ℕ∞ω} {n m : ℕ} {s : Set M}
    [IsManifold I r M] (hr : r ≠ 0) (e_ℂ : E ≃L[ℂ] Fin n → ℂ) (e_ℝ : E ≃L[ℝ] Fin m → ℝ)
    (hne : s.Nonempty)
    (hloc : ∀ x ∈ s, ∃ φ ∈ maximalAtlas I r M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ φ.source ∧
      ∀ y ∈ W, y ∈ s ↔ star (e_ℂ (φ.extend I y)) = e_ℂ (φ.extend I y)) :
    IsMAnalyticSubmanifold (I.restrictScalars ℝ) e_ℝ n s := by
  have : FiniteDimensional ℂ E := e_ℂ.symm.toLinearEquiv.finiteDimensional
  have : IsManifold (I.restrictScalars ℝ) ω M :=
    I.isManifold_restrictScalars ℝ (‹IsManifold I r M›.of_ne_zero ω hr)
  rw [isMAnalyticSubmanifold_iff_exists_mem_maximalAtlas]
  refine ⟨hne, fun x hxs ↦ ?_⟩
  obtain ⟨φ, hφ, W, hW, hxW, hWsrc, hWs⟩ := hloc x hxs
  have hφ_real : φ ∈ maximalAtlas (I.restrictScalars ℝ) ω M :=
    I.maximalAtlas_subset_restrictScalars ℝ
      ((IsManifold.maximalAtlas_eq_of_ne_zero hr (by simp)).subset hφ)
  set Φ_ℂ := φ.extendTrans I e_ℂ.toHomeomorph
  set Φ_ℝ := φ.extendTrans (I.restrictScalars ℝ) e_ℝ.toHomeomorph
  let e_ℂ' : E ≃L[ℝ] Fin n → ℂ := e_ℂ.restrictScalars' ℝ
  let L : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ := e_ℂ'.symm.trans e_ℝ
  let V : Set (Fin n → ℂ) := Φ_ℂ.target ∩ Φ_ℂ.symm ⁻¹' W
  have hV : IsOpen V := Φ_ℂ.continuousOn_symm.isOpen_inter_preimage Φ_ℂ.open_target hW
  let U : Set (Fin m → ℝ) := Φ_ℝ.target ∩ Φ_ℝ.symm ⁻¹' W
  have hU : IsOpen U := Φ_ℝ.continuousOn_symm.isOpen_inter_preimage Φ_ℝ.open_target hW
  have hxφ : x ∈ φ.source := hWsrc hxW
  have hxΦ_ℝ : x ∈ Φ_ℝ.source := by simpa [Φ_ℝ] using hxφ
  have hxU : e_ℝ (φ.extend (I.restrictScalars ℝ) x) ∈ U := by
    have h1 : Φ_ℝ x = e_ℝ (φ.extend (I.restrictScalars ℝ) x) := by simp [Φ_ℝ]
    rw [← h1]
    exact ⟨Φ_ℝ.map_source hxΦ_ℝ, by simpa [Φ_ℝ.left_inv hxΦ_ℝ] using hxW⟩
  have hxΦ_ℂ : x ∈ Φ_ℂ.source := by simpa [Φ_ℂ] using hxφ
  have hxV : Φ_ℂ x ∈ V ∩ {z : Fin n → ℂ | star z = z} := by
    refine ⟨⟨Φ_ℂ.map_source hxΦ_ℂ, by simpa [Φ_ℂ.left_inv hxΦ_ℂ] using hxW⟩, ?_⟩
    simpa [Φ_ℂ] using (hWs x hxW).1 hxs
  have himg := IsOpen.isAnalyticSubmanifold_image_inter_setOf_star_eq hV ⟨Φ_ℂ x, hxV⟩ L
  refine ⟨φ, hφ_real, hxφ, U, hU, hxU, ?_⟩
  have heq : L '' (V ∩ {z : Fin n → ℂ | star z = z}) =
      U ∩ (e_ℝ ∘ φ.extend (I.restrictScalars ℝ)) '' (s ∩ φ.source) :=
    image_inter_setOf_star_eq_image_inter e_ℂ e_ℝ φ hWs
  rwa [heq] at himg

/-- On a complex `C^r` manifold (`r ≠ 0`) modelled on `𝓘(ℂ, E)` with complex coordinates
`e_ℂ : E ≃L[ℂ] Fin n → ℂ`, any nonempty subset `s ⊆ M` locally cut out in holomorphic charts by
`star (e_ℂ (φ y)) = e_ℂ (φ y)` is an `n`-dimensional real analytic submanifold of `M` for `𝓘(ℝ, E)`
and any real coordinate equivalence `e_ℝ : E ≃L[ℝ] Fin m → ℝ`. -/
theorem isMAnalyticSubmanifold_of_holomorphicChart_star_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} {n m : ℕ} {s : Set M}
    [IsManifold 𝓘(ℂ, E) r M] (hr : r ≠ 0) (e_ℂ : E ≃L[ℂ] Fin n → ℂ) (e_ℝ : E ≃L[ℝ] Fin m → ℝ)
    (hne : s.Nonempty)
    (hloc : ∀ x ∈ s, ∃ φ ∈ maximalAtlas 𝓘(ℂ, E) r M, ∃ W : Set M,
      IsOpen W ∧ x ∈ W ∧ W ⊆ φ.source ∧ ∀ y ∈ W, y ∈ s ↔ star (e_ℂ (φ y)) = e_ℂ (φ y)) :
    IsMAnalyticSubmanifold 𝓘(ℝ, E) e_ℝ n s := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    isMAnalyticSubmanifold_restrictScalars_of_holomorphicChart_star_eq (I := 𝓘(ℂ, E)) hr e_ℂ e_ℝ
      hne (by simpa using hloc)

/-- On a complex `C^r` manifold (`r ≠ 0`) modelled on `𝓘(ℂ, EuclideanSpace ℂ (Fin n))`, any
nonempty subset `s ⊆ M` locally cut out in holomorphic charts by `star (e_ℂ (φ y)) = e_ℂ (φ y)` is
a `k`-dimensional real analytic submanifold for `TauCeti.complexEuclideanRealModel n`. -/
theorem isMAnalyticSubmanifold_complexEuclideanRealModel_of_holomorphicChart_star_eq
    {n m k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    {r : ℕ∞ω} {s : Set M} [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) r M] (hr : r ≠ 0)
    (e_ℂ : EuclideanSpace ℂ (Fin n) ≃L[ℂ] Fin k → ℂ)
    (e_ℝ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ] Fin m → ℝ) (hne : s.Nonempty)
    (hloc : ∀ x ∈ s, ∃ φ ∈ maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) r M, ∃ W : Set M,
      IsOpen W ∧ x ∈ W ∧ W ⊆ φ.source ∧ ∀ y ∈ W, y ∈ s ↔ star (e_ℂ (φ y)) = e_ℂ (φ y)) :
    IsMAnalyticSubmanifold (TauCeti.complexEuclideanRealModel n) e_ℝ k s := by
  rw [complexEuclideanRealModel_def, isMAnalyticSubmanifold_transContinuousLinearEquiv_iff]
  exact isMAnalyticSubmanifold_of_holomorphicChart_star_eq hr e_ℂ _ hne hloc

end RealLocus

end TauCeti

end
