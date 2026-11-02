/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.BasisChange
public import TauCeti.Algebra.Module.ZLattice.Family.DiffeomorphProd

/-!
# Basis independence of the smooth trivialization of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a `C^n` family of full lattices, parametrized by a real manifold `Y`.
Each `ℤ`-basis `b` of `Λ` gives a smooth global trivialization
`TauCeti.torusFamilyDiffeomorphProd P b : (Y × E)/Λ ≃ Y × ℝ^ι/ℤ^ι` over `Y`, sending `[y, v]` to
`y` and the class of the coordinates of `v` in the period basis `P y (b i)`.

This file proves that the trivializations for two `ℤ`-bases `b` and `c` of `Λ` differ by one fixed
change of coordinates of the standard torus, the diffeomorphism `Module.Basis.torusCoordChange b c`
induced by the integral change-of-basis matrix `c.toMatrix b`: the transition map
`(Y × ℝ^ι/ℤ^ι) ≃ (Y × ℝ^κ/ℤ^κ)` is the identity on `Y` times this diffeomorphism, independently of
the parameter `y` and of the periods. The reason is that the period coordinates at `y` in the two
bases differ by the real coordinate change `Module.Basis.realCoordChange b c`, which does not
involve `P` (`TauCeti.realCoordChange_periodBasis_equivFun`).

On the torus factor, the transition map is induced by the real-linear map
`Module.Basis.realCoordChange b c` of the covering vector spaces. Nothing here says that a
complex family is holomorphically trivial.

## Main results

* `TauCeti.realCoordChange_periodBasis_equivFun`: the period coordinates in the bases `b` and `c`
  differ by the integral change of coordinates.
* `TauCeti.torusFamilyDiffeomorphProd_eq_prodMap_torusCoordChange`: the trivialization for `c`
  is the trivialization for `b` followed by `Module.Basis.torusCoordChange b c` on the torus factor.
* `TauCeti.coe_torusFamilyDiffeomorphProd_symm_trans`: the transition diffeomorphism between the
  two trivializations is `Prod.map id (Module.Basis.torusCoordChange b c)`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
* Tau Ceti PR [#21079](https://github.com/TauCetiProject/TauCeti/pull/21079) (closed, unmerged)
  proved basis independence for the topological trivialization of a family of tori;
  `TauCeti.torusFamilyDiffeomorphProd_eq_prodMap_torusCoordChange` and
  `TauCeti.coe_torusFamilyDiffeomorphProd_symm_trans` move that result to the smooth
  trivialization.
-/

public section

open Module Set Function Submodule
open scoped Manifold ContDiff

namespace TauCeti

section Coordinates

variable {Y : Type*} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
  (hinj : ∀ y, Injective (P y))

/-- **Change of basis for period coordinates.** The coordinates of `v` in the period basis
`P y (c j)` are obtained from its coordinates in the period basis `P y (b i)` by the integral
change of coordinates from `b` to `c`, which depends neither on `y` nor on the periods. -/
theorem realCoordChange_periodBasis_equivFun (y : Y) (v : E) :
    b.realCoordChange c ((periodBasis P b hinj y).equivFun v) =
      (periodBasis P c hinj y).equivFun v := by
  -- Both sides are real linear in `v`, so it suffices to compare them on the period basis at `y`
  -- for `b`, whose vectors are the periods `P y (b i)`.
  have h : (b.realCoordChange c).toLinearMap ∘ₗ (periodBasis P b hinj y).equivFun.toLinearMap =
      (periodBasis P c hinj y).equivFun.toLinearMap := by
    refine (periodBasis P b hinj y).ext fun i ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, periodBasis_apply,
      periodBasis_equivFun_period, Basis.realCoordChange_intCast]
  exact LinearMap.congr_fun h v

end Coordinates

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
  (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l)

/-- **Basis independence of the smooth trivialization.** The smooth trivialization of a family of
tori for the `ℤ`-basis `c` is the trivialization for the `ℤ`-basis `b` followed, on the standard
torus factor, by the fixed change of coordinates `Module.Basis.torusCoordChange b c`. -/
theorem torusFamilyDiffeomorphProd_eq_prodMap_torusCoordChange
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    torusFamilyDiffeomorphProd P c hinj hP z =
      Prod.map id (b.torusCoordChange c (n := n)) (torusFamilyDiffeomorphProd P b hinj hP z) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  induction z using Quotient.inductionOn with | h p => ?_
  rw [torusFamilyDiffeomorphProd_mk, torusFamilyDiffeomorphProd_mk, Prod.map_apply, id_eq,
    Basis.torusCoordChange_mk, realCoordChange_periodBasis_equivFun]

/-- **The transition between two smooth trivializations.** For two `ℤ`-bases `b` and `c` of `Λ`,
the transition diffeomorphism from the smooth trivialization of the family for `b` to the one for
`c` is the identity of `Y` times the fixed change of coordinates `Module.Basis.torusCoordChange b c`
of the standard torus. -/
theorem coe_torusFamilyDiffeomorphProd_symm_trans :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ⇑((torusFamilyDiffeomorphProd P b hinj hP).symm.trans
        (torusFamilyDiffeomorphProd P c hinj hP)) =
      Prod.map id (b.torusCoordChange c (n := n)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  ext q : 1
  rw [Diffeomorph.coe_trans, comp_apply,
    torusFamilyDiffeomorphProd_eq_prodMap_torusCoordChange P b c hinj hP,
    Diffeomorph.apply_symm_apply]

end TauCeti
