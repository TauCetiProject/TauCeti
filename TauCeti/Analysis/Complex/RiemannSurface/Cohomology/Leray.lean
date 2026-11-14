/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Leray
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Sphere
public import TauCeti.Topology.Sheaves.Leray.CechCohomology

/-!
# Finite Leray covers compute `H¹` on a compact Riemann surface

On a compact Riemann surface `X`, every open cover is refined by a finite cover by coordinate
discs whose members have vanishing `H¹` for the structure sheaf, and for every divisor sheaf
`𝒪(D)` (`TauCeti.exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules`,
`TauCeti.RiemannSurface.exists_finite_cover_subsingleton_H'_one_divisorSheaf`). Hence every finite
open cover whose members have vanishing `H¹` computes the degree one Čech cohomology
(`CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'`), and dimension counts of
`H¹(X, 𝒪)` and `H¹(X, 𝒪(D))` may be done on any such cover.

## Main results

* `TauCeti.RiemannSurface.finrank_cechCohomology_one_holomorphicStructureSheafModules` and
  `TauCeti.RiemannSurface.finrank_cechCohomology_one_divisorSheaf`: `dim H¹` is the dimension of the
  Čech `H¹` of any finite cover whose members have vanishing `H¹`, and similarly for
  finite-dimensionality.
* `TauCeti.RiemannSurface.finrank_cechCohomology_one_holomorphicStructureSheafModules_sphere`:
  **Check.** `dim H¹(ℙ¹, 𝒪) = 0`, computed on the two-disc cover of the Riemann sphere.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 12.8 (Leray's theorem) and §§13-14.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  {ι : Type} [Finite ι] (U : ι → Opens (TopCat.of X)) (hU : ⨆ i, U i = ⊤)

section StructureSheaf

variable (hFU : ∀ i, Subsingleton (Sheaf.H'
  ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X)) 1 (U i)))

include hU hFU in
/-- On a compact Riemann surface, a finite open cover whose members have vanishing `H¹` for the
structure sheaf computes its degree one Čech cohomology. -/
theorem isIso_toCechCohomology_one_holomorphicStructureSheafModules :
    IsIso ((toCechCohomology (ModuleCat.{0} ℂ) 1 U (IsOpenCover.mk hU)).app
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) :=
  Sheaf.isIso_toCechCohomology_one_of_subsingleton_H' _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules V hV)
    U hU hFU

include hU hFU in
/-- `H¹(X, 𝒪)` is finite-dimensional exactly when the Čech `H¹` of a finite open cover whose
members have vanishing `H¹` is. -/
theorem finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules_iff :
    FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) ↔
      FiniteDimensional ℂ (((cechComplexFunctor U).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj).homology 1) :=
  Sheaf.finiteDimensional_cechCohomology_one_iff _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules V hV)
    U hU hFU

include hU hFU in
/-- `dim H¹(X, 𝒪)` is the dimension of the Čech `H¹` of any finite open cover whose members have
vanishing `H¹`. -/
theorem finrank_cechCohomology_one_holomorphicStructureSheafModules :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) =
      Module.finrank ℂ (((cechComplexFunctor U).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj).homology 1) :=
  Sheaf.finrank_cechCohomology_one _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules V hV)
    U hU hFU

end StructureSheaf

section Divisor

variable (D : WeilDivisor X) (hFU : ∀ i, Subsingleton (Sheaf.H'
  ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (divisorSheaf D)) 1 (U i)))

include hU hFU in
/-- On a compact Riemann surface, a finite open cover whose members have vanishing `H¹` for the
divisor sheaf `𝒪(D)` computes its degree one Čech cohomology. -/
theorem isIso_toCechCohomology_one_divisorSheaf :
    IsIso ((toCechCohomology (ModuleCat.{0} ℂ) 1 U (IsOpenCover.mk hU)).app
      (divisorSheaf D).obj) :=
  Sheaf.isIso_toCechCohomology_one_of_subsingleton_H' _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_divisorSheaf D V hV) U hU hFU

include hU hFU in
/-- `H¹(X, 𝒪(D))` is finite-dimensional exactly when the Čech `H¹` of a finite open cover whose
members have vanishing `H¹` for `𝒪(D)` is. -/
theorem finiteDimensional_cechCohomology_one_divisorSheaf_iff :
    FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (divisorSheaf D).obj) ↔
      FiniteDimensional ℂ (((cechComplexFunctor U).obj (divisorSheaf D).obj).homology 1) :=
  Sheaf.finiteDimensional_cechCohomology_one_iff _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_divisorSheaf D V hV) U hU hFU

include hU hFU in
/-- `dim H¹(X, 𝒪(D))` is the dimension of the Čech `H¹` of any finite open cover whose members
have vanishing `H¹` for `𝒪(D)`. -/
theorem finrank_cechCohomology_one_divisorSheaf :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (divisorSheaf D).obj) =
      Module.finrank ℂ (((cechComplexFunctor U).obj (divisorSheaf D).obj).homology 1) :=
  Sheaf.finrank_cechCohomology_one _
    (fun V hV ↦ exists_finite_cover_subsingleton_H'_one_divisorSheaf D V hV) U hU hFU

end Divisor

/-- **Check.** `dim H¹(ℙ¹, 𝒪) = 0`: the two-disc cover of the Riemann sphere computes `H¹`, and
its Čech `H¹` vanishes by the Laurent splitting. -/
theorem finrank_cechCohomology_one_holomorphicStructureSheafModules_sphere :
    Module.finrank ℂ ((cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj) = 0 := by
  rw [finrank_cechCohomology_one_holomorphicStructureSheafModules sphereDiscCover
    iSup_sphereDiscCover subsingleton_H'_one_holomorphicStructureSheafModules_sphereDiscCover]
  have h := (Sheaf.isZero_homology_cechComplex_iff _ sphereDiscCover 1).2
    isZero_homology_one_cechComplex_sphereDiscCover
  have := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_zero_of_subsingleton (M := ((cechComplexFunctor sphereDiscCover).obj
    ((sheafToPresheaf _ _).obj (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)))).homology 1)

end TauCeti.RiemannSurface
