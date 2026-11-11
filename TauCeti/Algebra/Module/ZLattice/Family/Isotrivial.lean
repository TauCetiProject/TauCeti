/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LinearEquivProd
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousLinearEquiv

/-!
# Trivializing a torus family by linear identifications of its lattices

A family of linear equivalences carrying the period lattices onto one fixed lattice induces
an equivalence from the varying torus family to a product with the fixed torus.
If the linear equivalences depend `C^n` on the parameter, this is a `C^n` diffeomorphism.
In particular, complex-linear identifications depending holomorphically on the parameter give
a holomorphic product trivialization. The inverse identifications are automatically `C^n`.

This is an explicit sufficient isotriviality hypothesis, not a conclusion about arbitrary
holomorphic period families. Real-linear period frames provide smooth trivializations but do
not generally provide holomorphic ones. No choice of a lattice basis is needed here.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori and period data).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section Regularity

variable {Y Λ 𝕜 E F : Type*} [AddCommGroup Λ] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (P : Y → Λ →ₗ[ℤ] E) (L : Submodule ℤ F) (A : Y → E ≃L[𝕜] F)
  (hL : ∀ y, (LinearMap.range (P y)).map
    ((A y).toLinearEquiv.restrictScalars ℤ).toLinearMap = L)
  [TopologicalSpace Y] {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H} [ChartedSpace H Y]
  [T2Space Y] [LocallyCompactSpace Y] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] [DiscreteTopology L] [LocallyCompactSpace F]
  {n : WithTop ℕ∞} [IsManifold I n Y]
  (hinj : ∀ y, Function.Injective (P y))
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
  (hA : ContMDiff I 𝓘(𝕜, E →L[𝕜] F) n fun y ↦ (A y : E →L[𝕜] F))

/-- A `C^n` family of linear identifications of the period lattices with one fixed lattice
induces a product diffeomorphism. For complex-linear holomorphic identifications this is a
biholomorphic trivialization with fixed complex-torus fibre. Only the forward linear family
is assumed `C^n`; regularity of its inverse follows from smooth inversion of operators. -/
noncomputable def torusFamilyLinearDiffeomorphProd :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Diffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, F))
      (AddAction.orbitRel.Quotient Λ (Y × E)) (Y × AddAction.orbitRel.Quotient L F) n := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  refine
    { toEquiv := torusFamilyLinearEquivProd P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have heq : torusFamilyLinearEquivProd P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL ∘ Quotient.mk _ =
        fun p : Y × E ↦ (p.1, Quotient.mk (AddAction.orbitRel L F) (A p.1 p.2)) :=
      funext fun p ↦ torusFamilyLinearEquivProd_mk P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL p.1 p.2
    rw [← (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff_comp_iff
      Quotient.mk_surjective le_rfl, heq]
    exact contMDiff_fst.prodMk (isLocalDiffeomorph_addQuotientMk.contMDiff.comp
      ((hA.comp contMDiff_fst).clm_apply contMDiff_snd))
  · have heq : (torusFamilyLinearEquivProd P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL).symm ∘
        Prod.map id (Quotient.mk _) =
        fun p : Y × F ↦ Quotient.mk _ (p.1, (A p.1).symm p.2) :=
      funext fun p ↦ torusFamilyLinearEquivProd_symm_mk P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL p.1 p.2
    rw [← (isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, F))).contMDiff_comp_prodMap_iff
      Quotient.mk_surjective le_rfl, heq]
    exact (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.comp
      (contMDiff_fst.prodMk
        ((hA.continuousLinearEquiv_symm.comp contMDiff_fst).clm_apply contMDiff_snd))

/-- The product diffeomorphism is the equivalence induced by the linear identifications. -/
@[simp] theorem torusFamilyLinearDiffeomorphProd_toEquiv :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyLinearDiffeomorphProd P L A hL hinj hP hA).toEquiv =
      torusFamilyLinearEquivProd P L
        (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL := (rfl)

/-- The product diffeomorphism sends `[y,v]` to `(y,[A y v])`. -/
@[simp] theorem torusFamilyLinearDiffeomorphProd_mk (y : Y) (v : E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    torusFamilyLinearDiffeomorphProd P L A hL hinj hP hA (Quotient.mk _ (y, v)) =
      (y, Quotient.mk _ (A y v)) :=
  torusFamilyLinearEquivProd_mk P L
    (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL y v

/-- The inverse product diffeomorphism sends `(y,[v])` to `[y,(A y)⁻¹ v]`. -/
@[simp] theorem torusFamilyLinearDiffeomorphProd_symm_mk (y : Y) (v : F) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyLinearDiffeomorphProd P L A hL hinj hP hA).symm (y, Quotient.mk _ v) =
      Quotient.mk _ (y, (A y).symm v) :=
  torusFamilyLinearEquivProd_symm_mk P L
    (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL y v

/-- The product diffeomorphism preserves the base point. -/
@[simp] theorem fst_torusFamilyLinearDiffeomorphProd
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyLinearDiffeomorphProd P L A hL hinj hP hA x).1 =
      torusFamilyProjection P x :=
  fst_torusFamilyLinearEquivProd P L
    (fun y ↦ (A y).toLinearEquiv.restrictScalars ℤ) hL x

end Regularity

end TauCeti
