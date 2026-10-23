/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Basis

/-!
# Smooth dependence of the period frame

Let `P : Y → (Λ →ₗ[ℤ] E)` be a family of full lattices in a finite-dimensional real normed space
`E`, as in `TauCeti.Algebra.Module.ZLattice.Family.Basic`, now parametrized by a real manifold `Y`,
and let `b` be a `ℤ`-basis of `Λ` indexed by `ι`. If every period `y ↦ P y l` is `C^n`, then so
are the period frame `F_y : ℝ^ι → E`, `x ↦ ∑ i, x i • P y (b i)`, and its inverse, the coordinate
map `F_y⁻¹ : E → ℝ^ι` of the period basis `TauCeti.periodBasis P b hinj y`, both in the operator
norm. Consequently the maps `(y, v) ↦ (y, F_y⁻¹ v)` and `(y, x) ↦ (y, F_y x)`, which descend to
the global trivialization `TauCeti.torusFamilyHomeomorphProd` of the family of tori and to its
inverse, are `C^n` on `Y × E` and `Y × ℝ^ι`.

The frame is real-linear, so its smoothness is a statement about the real manifold `Y`. A complex
manifold modelled on `𝓘(ℂ, F)` with holomorphic periods is covered through
`ContMDiff.restrictScalars`, which makes the periods `C^n` for the real model `𝓘(ℝ, F)`. The
inverse frame is in general not holomorphic in `y`, even when the periods are: for
`E = ℂ` and periods `1, τ(y)` its coordinates involve `Im τ(y)`.

## Main results

* `TauCeti.contMDiff_periodBasis_equivFunL_symm`, `TauCeti.contMDiff_periodBasis_equivFunL`: the
  period frame `F_y` and its inverse depend `C^n` on `y`.
* `TauCeti.contMDiff_uncurry_periodBasis_equivFun`,
  `TauCeti.contMDiff_uncurry_periodBasis_equivFun_symm`: the period coordinates `(y, v) ↦ F_y⁻¹ v`
  and their inverse `(y, x) ↦ F_y x` are `C^n`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Function
open scoped Manifold ContDiff

namespace TauCeti

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ Λ) (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞}

/-- **Smoothness of the period frame.** If every period depends `C^n` on the parameter, then so
does the real linear isomorphism `F_y : ℝ^ι → E`, `x ↦ ∑ i, x i • P y (b i)`, in the operator
norm. -/
theorem contMDiff_periodBasis_equivFunL_symm
    (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l) :
    ContMDiff I 𝓘(ℝ, (ι → ℝ) →L[ℝ] E) n
      fun y ↦ ((periodBasis P b hinj y).equivFunL.symm : (ι → ℝ) →L[ℝ] E) :=
  Basis.contMDiff_equivFunL_symm_of_contMDiff fun i ↦ by simpa using hP (b i)

/-- **Smoothness of the inverse period frame.** If every period depends `C^n` on the parameter,
then so does the coordinate map `F_y⁻¹ : E → ℝ^ι` of the period basis, in the operator norm. -/
theorem contMDiff_periodBasis_equivFunL
    (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l) :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] ι → ℝ) n
      fun y ↦ ((periodBasis P b hinj y).equivFunL : E →L[ℝ] ι → ℝ) :=
  Basis.contMDiff_equivFunL_of_contMDiff fun i ↦ by simpa using hP (b i)

/-- **Smoothness of the period coordinates.** If every period depends `C^n` on the parameter, then
the coordinates `(y, v) ↦ F_y⁻¹ v` of `v` in the period basis at `y` are `C^n` on `Y × E`. They
induce the global trivialization `TauCeti.torusFamilyHomeomorphProd` on orbit spaces. -/
theorem contMDiff_uncurry_periodBasis_equivFun
    (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l) :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ι → ℝ) n
      (uncurry fun y v ↦ (periodBasis P b hinj y).equivFun v) := by
  have h : (uncurry fun y v ↦ (periodBasis P b hinj y).equivFun v) =
      fun p : Y × E ↦ ((periodBasis P b hinj p.1).equivFunL : E →L[ℝ] ι → ℝ) p.2 := by
    ext ⟨y, v⟩ i
    simp
  rw [h]
  exact ((contMDiff_periodBasis_equivFunL P b hinj hP).comp contMDiff_fst).clm_apply contMDiff_snd

/-- **Smoothness of the inverse period coordinates.** If every period depends `C^n` on the
parameter, then `(y, x) ↦ F_y x = ∑ i, x i • P y (b i)` is `C^n` on `Y × ℝ^ι`. It induces the
inverse of the global trivialization `TauCeti.torusFamilyHomeomorphProd` on orbit spaces. -/
theorem contMDiff_uncurry_periodBasis_equivFun_symm
    (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l) :
    ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ, E) n
      (uncurry fun y x ↦ (periodBasis P b hinj y).equivFun.symm x) := by
  have h : (uncurry fun y x ↦ (periodBasis P b hinj y).equivFun.symm x) =
      fun p : Y × (ι → ℝ) ↦ ((periodBasis P b hinj p.1).equivFunL.symm : (ι → ℝ) →L[ℝ] E) p.2 := by
    funext ⟨y, x⟩
    simp
  rw [h]
  exact ((contMDiff_periodBasis_equivFunL_symm P b hinj hP).comp contMDiff_fst).clm_apply
    contMDiff_snd

end TauCeti
