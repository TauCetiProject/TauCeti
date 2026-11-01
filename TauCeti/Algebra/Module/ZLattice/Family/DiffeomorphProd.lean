/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.ContMDiff
public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold

/-!
# The smooth global trivialization of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a `C^n` family of full lattices in a finite-dimensional real normed
space `E`, parametrized by a real manifold `Y`, and let `b` be a `ℤ`-basis of `Λ` indexed by `ι`.
The orbit space `(Y × E)/Λ` of the period translation action is a `C^n` manifold
(`TauCeti.isManifold_torusFamily`), and so is the standard torus
`T = ℝ^ι/ℤ^ι`, the orbit space `AddAction.orbitRel.Quotient ℤ^ι (ι → ℝ)` of translation by the
standard lattice `ℤ^ι = span ℤ (range (Pi.basisFun ℝ ι))`
(`Submodule.instLieAddGroupOrbitRelQuotient`).

This file proves that the global trivialization `[y, v] ↦ (y, [F_y⁻¹ v])` of
`TauCeti.torusFamilyHomeomorphProd`, with `F_y⁻¹` the coordinate map of the period basis at `y`,
is a `C^n` diffeomorphism `(Y × E)/Λ ≃ Y × T` over `Y` (`TauCeti.torusFamilyDiffeomorphProd`).
Upstairs, `(y, v) ↦ (y, F_y⁻¹ v)` and its inverse `(y, x) ↦ (y, F_y x)` are `C^n` because the
period frame and its inverse depend `C^n` on `y`
(`TauCeti.contMDiff_uncurry_periodBasis_equivFun`). Both orbit maps
`Y × E → (Y × E)/Λ` and `Y × ℝ^ι → Y × T` are surjective `C^n` local diffeomorphisms, so
smoothness descends to the quotients.

The diffeomorphism is real-linear on fibres and depends on the basis `b`. Only a real `C^n`
trivialization is constructed: no complex structure is supplied on `T`, and no holomorphic
triviality of a complex family is claimed.

## Main definitions

* `TauCeti.torusFamilyDiffeomorphProd`: the `C^n` diffeomorphism `(Y × E)/Λ ≃ Y × ℝ^ι/ℤ^ι` over
  `Y`.

## Main results

* `TauCeti.torusFamilyDiffeomorphProd_mk`, `TauCeti.torusFamilyDiffeomorphProd_symm_mk`: the
  diffeomorphism and its inverse on representatives.
* `TauCeti.fst_torusFamilyDiffeomorphProd`: the diffeomorphism lies over `Y`.
* `TauCeti.orbitRelQuotientAddEquiv_snd_torusFamilyDiffeomorphProd`: it is the homeomorphism
  `TauCeti.torusFamilyHomeomorphProd`, read on the orbit-space model of the standard torus.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Set Function Submodule
open scoped Manifold ContDiff

namespace TauCeti

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ Λ) (hinj : ∀ y, Injective (P y)) {n : WithTop ℕ∞}
  [IsManifold I n Y] (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l)

/-- **The smooth global trivialization** of a `C^n` family of full lattices. For a `ℤ`-basis `b`
of `Λ` indexed by `ι`, the map `[y, v] ↦ (y, [F_y⁻¹ v])`, with `F_y⁻¹` the coordinate map of the
period basis at `y`, is a `C^n` diffeomorphism from the orbit space `(Y × E)/Λ` of the period
translation action to the product of `Y` with the standard torus `ℝ^ι/ℤ^ι`, the orbit space of
translation by `span ℤ (range (Pi.basisFun ℝ ι))`. It lies over `Y`
(`TauCeti.fst_torusFamilyDiffeomorphProd`), and as a map it is the homeomorphism
`TauCeti.torusFamilyHomeomorphProd`
(`TauCeti.orbitRelQuotientAddEquiv_snd_torusFamilyDiffeomorphProd`). -/
noncomputable def torusFamilyDiffeomorphProd :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Diffeomorph (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ι → ℝ)) (AddAction.orbitRel.Quotient Λ (Y × E))
      (Y × AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ)) n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let e := (torusFamilyHomeomorphProd P b hinj fun l ↦ (hP l).continuous).toEquiv.trans
    ((Equiv.refl Y).prodCongr (span ℤ (range (Pi.basisFun ℝ ι))).orbitRelQuotientAddEquiv.symm)
  { toEquiv := e
    contMDiff_toFun := by
      -- Upstairs the map is `(y, v) ↦ (y, [F_y⁻¹ v])`; the orbit map of `Y × E` is a surjective
      -- local diffeomorphism.
      have h : ⇑e ∘ Quotient.mk (AddAction.orbitRel Λ (Y × E)) = fun p : Y × E ↦
          (p.1, Quotient.mk _ ((periodBasis P b hinj p.1).equivFun p.2)) :=
        funext fun p ↦ by simp [e]
      rw [← (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff_comp_iff
        Quotient.mk_surjective le_rfl, h]
      exact contMDiff_fst.prodMk (isLocalDiffeomorph_addQuotientMk.contMDiff.comp
        (contMDiff_uncurry_periodBasis_equivFun P b hinj hP))
    contMDiff_invFun := by
      -- Upstairs the inverse is `(y, x) ↦ [y, F_y x]`; the orbit map of the standard torus is a
      -- surjective local diffeomorphism.
      have h : ⇑e.symm ∘ Prod.map id (Quotient.mk _) =
          Quotient.mk (AddAction.orbitRel Λ (Y × E)) ∘ fun p : Y × (ι → ℝ) ↦
            (p.1, (periodBasis P b hinj p.1).equivFun.symm p.2) :=
        funext fun ⟨y, x⟩ ↦ by simp [e]
      rw [← (isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℝ, ι → ℝ))).contMDiff_comp_prodMap_iff
        Quotient.mk_surjective le_rfl, h]
      exact (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.comp
        (contMDiff_fst.prodMk (contMDiff_uncurry_periodBasis_equivFun_symm P b hinj hP)) }

/-- The smooth trivialization sends the class of `(y, v)` to `y` and the class of the period
coordinates of `v` at `y`. -/
@[simp] theorem torusFamilyDiffeomorphProd_mk (p : Y × E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    torusFamilyDiffeomorphProd P b hinj hP (Quotient.mk _ p) =
      (p.1, Quotient.mk _ ((periodBasis P b hinj p.1).equivFun p.2)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  rw [← Diffeomorph.coe_toEquiv]
  simp [torusFamilyDiffeomorphProd]

/-- The inverse of the smooth trivialization sends `y` and the class of `x` to the class of
`(y, ∑ i, x i • P y (b i))`. -/
@[simp] theorem torusFamilyDiffeomorphProd_symm_mk (y : Y) (x : ι → ℝ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyDiffeomorphProd P b hinj hP).symm (y, Quotient.mk _ x) =
      Quotient.mk _ (y, (periodBasis P b hinj y).equivFun.symm x) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  rw [← Diffeomorph.toEquiv_coe_symm]
  simp [torusFamilyDiffeomorphProd]

/-- The smooth trivialization lies over the parameter space. -/
@[simp] theorem fst_torusFamilyDiffeomorphProd
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyDiffeomorphProd P b hinj hP z).1 = torusFamilyProjection P z := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

/-- The smooth trivialization is the homeomorphism `TauCeti.torusFamilyHomeomorphProd`, whose
fibre is the quotient module `ℝ^ι ⧸ ℤ^ι`, read on the orbit space of translation by `ℤ^ι` through
`Submodule.orbitRelQuotientAddEquiv`. -/
theorem orbitRelQuotientAddEquiv_snd_torusFamilyDiffeomorphProd
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (span ℤ (range (Pi.basisFun ℝ ι))).orbitRelQuotientAddEquiv
        (torusFamilyDiffeomorphProd P b hinj hP z).2 =
      (torusFamilyHomeomorphProd P b hinj (fun l ↦ (hP l).continuous) z).2 := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn
  simp

end TauCeti
