/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.BasisChange
public import TauCeti.Algebra.Module.ZLattice.Family.DiffeomorphProd

/-!
# Basis independence of the trivializations of a family of tori

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
involve `P` (`TauCeti.realCoordChange_periodBasis_equivFun`). The same holds for the topological
trivialization `TauCeti.torusFamilyHomeomorphProd` of a continuous family, with the induced
equivalence of quotient groups `ℝ^ι/ℤ^ι ≃ ℝ^κ/ℤ^κ` on the torus factor.

On the torus factor, the transition map is induced by the real-linear map
`Module.Basis.realCoordChange b c` of the covering vector spaces. Nothing here says that a
complex family is holomorphically trivial.

## Main results

* `TauCeti.periodBasis_toMatrix_periodBasis`: at every `y`, the change-of-basis matrix between
  the period bases for `b` and `c` is the integral matrix `c.toMatrix b`.
* `TauCeti.realCoordChange_periodBasis_equivFun`: the period coordinates in the bases `b` and `c`
  differ by the integral change of coordinates.
* `TauCeti.torusFamilyHomeomorphProd_eq_prodMap_quotientEquiv`: the topological trivialization
  for `c` is the trivialization for `b` followed by the equivalence of standard tori induced by
  `Module.Basis.realCoordChange b c` on the torus factor.
* `TauCeti.coe_torusFamilyHomeomorphProd_symm_trans`: the transition homeomorphism between the two
  topological trivializations is the identity of `Y` times that equivalence of standard tori.
* `TauCeti.torusFamilyDiffeomorphProd_eq_prodMap_torusCoordChange`: the trivialization for `c`
  is the trivialization for `b` followed by `Module.Basis.torusCoordChange b c` on the torus factor.
* `TauCeti.coe_torusFamilyDiffeomorphProd_symm_trans`: the transition diffeomorphism between the
  two trivializations is `Prod.map id (Module.Basis.torusCoordChange b c)`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
* The basis independence of the topological trivialization follows Tau Ceti
  PR [#21079](https://github.com/TauCetiProject/TauCeti/pull/21079).
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

omit [Fintype ι] [Fintype κ] in
/-- **The period change-of-basis matrix is constant.** At every `y`, the matrix expressing the
period basis for `b` in the period basis for `c` is the integral change-of-basis matrix
`c.toMatrix b`, independently of `y` and of the periods. -/
@[simp] theorem periodBasis_toMatrix_periodBasis (y : Y) :
    (periodBasis P c hinj y).toMatrix (periodBasis P b hinj y) =
      (c.toMatrix b).map ((↑) : ℤ → ℝ) := by
  ext j i
  simp [Basis.toMatrix_apply]

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

section Topology

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
  (hinj : ∀ y, Injective (P y)) (hcont : ∀ l, Continuous fun y ↦ P y l)

/-- **Basis independence of the topological trivialization.** The global trivialization of a
continuous family of tori for the `ℤ`-basis `c` is the trivialization for the `ℤ`-basis `b`
followed, on the standard torus factor, by the fixed equivalence `ℝ^ι/ℤ^ι ≃ ℝ^κ/ℤ^κ` induced by
the real coordinate change `Module.Basis.realCoordChange b c`. -/
theorem torusFamilyHomeomorphProd_eq_prodMap_quotientEquiv
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyHomeomorphProd P c hinj hcont z =
      Prod.map id (Quotient.equiv (span ℤ (range (Pi.basisFun ℝ ι)))
        (span ℤ (range (Pi.basisFun ℝ κ))) ((b.realCoordChange c).restrictScalars ℤ)
        (b.map_realCoordChange_span_basisFun c))
        (torusFamilyHomeomorphProd P b hinj hcont z) := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn with | h p => ?_
  rw [torusFamilyHomeomorphProd_mk, torusFamilyHomeomorphProd_mk, Prod.map_apply, id_eq,
    Quotient.equiv_apply, mapQ_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    realCoordChange_periodBasis_equivFun]

/-- **The transition between two topological trivializations.** For two `ℤ`-bases `b` and `c` of
`Λ`, the transition homeomorphism from the topological trivialization of the family for `b` to the
one for `c` is the identity of `Y` times the fixed equivalence `ℝ^ι/ℤ^ι ≃ ℝ^κ/ℤ^κ` induced by
`Module.Basis.realCoordChange b c`. -/
theorem coe_torusFamilyHomeomorphProd_symm_trans :
    ⇑((torusFamilyHomeomorphProd P b hinj hcont).symm.trans
        (torusFamilyHomeomorphProd P c hinj hcont)) =
      Prod.map id (Quotient.equiv (span ℤ (range (Pi.basisFun ℝ ι)))
        (span ℤ (range (Pi.basisFun ℝ κ))) ((b.realCoordChange c).restrictScalars ℤ)
        (b.map_realCoordChange_span_basisFun c)) := by
  ext q : 1
  rw [Homeomorph.trans_apply, torusFamilyHomeomorphProd_eq_prodMap_quotientEquiv P b c hinj hcont,
    Homeomorph.apply_symm_apply]

end Topology

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
