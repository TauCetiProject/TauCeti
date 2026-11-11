/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology

/-!
# Checks for the Čech cohomology of the structure sheaf, a point skyscraper and the zero sheaf

This file records the boundary cases of the Čech cohomology of sheaves of complex vector spaces
on a complex curve that test the hypotheses of the cohomology layer.

* **The structure sheaf.** On a nonempty compact connected complex curve the degree-zero Čech
  cohomology of the holomorphic structure sheaf `𝒪` is one-dimensional, since global holomorphic
  functions are constant. On the empty curve every Čech cohomology group of `𝒪` (indeed of every
  presheaf, and of every divisor sheaf) vanishes, so `H⁰(𝒪) = 0 ≠ ℂ`: nonemptiness is essential.
* **The point skyscraper.** For the skyscraper sheaf `ℂ_x` with stalk `ℂ` at a point `x`, which
  is the cokernel sheaf in the point-twist sequence `0 → 𝒪(D) → 𝒪(D + x) → ℂ_x → 0`, the
  degree-zero Čech cohomology is one-dimensional and every positive-degree group vanishes. In
  particular `H⁰(ℂ_x)` is not zero.
* **The zero sheaf.** A sheaf all of whose sections are zero has vanishing Čech cohomology in
  every degree. This is what treating the support of `ℂ_x` as empty would produce, and it
  disagrees with `H⁰(ℂ_x) = ℂ`.

No compactness, connectedness or separation is used for the skyscraper and zero-sheaf
statements.

## Main results

* `TauCeti.RiemannSurface.finrank_cechCohomology_zero_holomorphicStructureSheafModules`:
  `dim H⁰(X, 𝒪) = 1` on a nonempty compact connected complex curve.
* `TauCeti.RiemannSurface.isZero_cechCohomology_holomorphicStructureSheafModules_of_isEmpty`
  and
  `TauCeti.RiemannSurface.finrank_cechCohomology_zero_holomorphicStructureSheafModules_of_isEmpty`:
  on the empty curve `Hⁿ(X, 𝒪) = 0` for every `n`, so `dim H⁰(X, 𝒪) = 0`.
* `TauCeti.RiemannSurface.finrank_cechCohomology_zero_pointSkyscraper`: `dim H⁰(X, ℂ_x) = 1`.
* `TauCeti.RiemannSurface.isZero_cechCohomology_pointSkyscraper`: `Hⁿ⁺¹(X, ℂ_x) = 0`.
* `TauCeti.RiemannSurface.isZero_cechCohomology_of_isZero_sections`: a sheaf with zero sections
  has `Hⁿ = 0` for every `n`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§12, 16.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type} [TopologicalSpace X]

/-- A complex vector space in `ModuleCat` that is a zero object has dimension zero. -/
private theorem finrank_moduleCat_eq_zero_of_isZero {M : ModuleCat.{0} ℂ} (hM : IsZero M) :
    Module.finrank ℂ M = 0 :=
  have := (ModuleCat.isZero_iff_subsingleton (M := M)).mp hM
  Module.finrank_zero_of_subsingleton

/-! ### The structure sheaf -/

section StructureSheaf

variable [ChartedSpace ℂ X]

/-- On a nonempty compact connected complex curve the degree-zero Čech cohomology of the
holomorphic structure sheaf is one-dimensional: it is identified with the global holomorphic
functions, which are the constants. -/
theorem finrank_cechCohomology_zero_holomorphicStructureSheafModules [IsManifold 𝓘(ℂ) 1 X]
    [CompactSpace X] [PreconnectedSpace X] [Nonempty X] :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) = 1 := by
  rw [← (cechCohomologyZeroIso (holomorphicStructureSheafModules 𝓘(ℂ) X)).toLinearEquiv.finrank_eq]
  exact holomorphicStructureSheafModules.finrank_globalSections 𝓘(ℂ) X

/-- **The empty curve.** On an empty complex curve every Čech cohomology group of the holomorphic
structure sheaf vanishes. -/
theorem isZero_cechCohomology_holomorphicStructureSheafModules_of_isEmpty [IsEmpty X] (n : ℕ) :
    IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) :=
  have : IsEmpty (TopCat.of X) := inferInstanceAs (IsEmpty X)
  isZero_cechCohomology_obj_of_isEmpty _ _ n _

/-- **Nonemptiness is essential for `H⁰(𝒪) = ℂ`.** On an empty complex curve the degree-zero
Čech cohomology of the holomorphic structure sheaf has dimension zero, not one, although the
curve is compact and connected. Compare
`finrank_cechCohomology_zero_holomorphicStructureSheafModules`. -/
theorem finrank_cechCohomology_zero_holomorphicStructureSheafModules_of_isEmpty [IsEmpty X] :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) = 0 :=
  finrank_moduleCat_eq_zero_of_isZero
    (isZero_cechCohomology_holomorphicStructureSheafModules_of_isEmpty 0)

/-- On an empty complex curve every Čech cohomology group of every divisor sheaf vanishes. -/
theorem isZero_divisorCechCohomology_of_isEmpty [IsEmpty X] (D : WeilDivisor X) (n : ℕ) :
    IsZero (divisorCechCohomology D n) :=
  have : IsEmpty (TopCat.of X) := inferInstanceAs (IsEmpty X)
  isZero_cechCohomology_obj_of_isEmpty _ _ n _

end StructureSheaf

/-! ### The point skyscraper -/

variable (x : X)

open Classical in
/-- **The point skyscraper has `H⁰ = ℂ`.** The degree-zero Čech cohomology of the skyscraper
sheaf with stalk `ℂ` at `x`, the cokernel of the point twist `𝒪(D) → 𝒪(D + x)`, is
one-dimensional. -/
theorem finrank_cechCohomology_zero_pointSkyscraper :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) = 1 := by
  rw [← (pointTwistCoefficientCechIso x).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

open Classical in
/-- The degree-zero Čech cohomology of the point skyscraper is not zero. -/
theorem not_isZero_cechCohomology_zero_pointSkyscraper :
    ¬ IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) := fun h ↦ by
  simpa [finrank_moduleCat_eq_zero_of_isZero h] using finrank_cechCohomology_zero_pointSkyscraper x

open Classical in
/-- **The point skyscraper is acyclic.** Every positive-degree Čech cohomology group of the
skyscraper sheaf with stalk `ℂ` at `x` vanishes. -/
theorem isZero_cechCohomology_pointSkyscraper (n : ℕ) :
    IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) (n + 1)).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) :=
  isZero_cechCohomology_skyscraperPresheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ)) n

open Classical in
/-- Every positive-degree Čech cohomology group of the point skyscraper has dimension zero. -/
theorem finrank_cechCohomology_pointSkyscraper (n : ℕ) :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) (n + 1)).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) = 0 :=
  finrank_moduleCat_eq_zero_of_isZero (isZero_cechCohomology_pointSkyscraper x n)

/-! ### The zero sheaf -/

/-- **The zero sheaf has no cohomology.** If every section of `F` is zero, every Čech
cohomology group of `F` vanishes. This is the answer that treating the support of the point
skyscraper as empty would give, which `not_isZero_cechCohomology_zero_pointSkyscraper` rules
out in degree zero. -/
theorem isZero_cechCohomology_of_isZero_sections (F : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X))
    (hF : ∀ U, IsZero (F.obj.obj U)) (n : ℕ) :
    IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj F.obj) :=
  Functor.map_isZero _ (Functor.isZero _ hF)

/-- If every section of `F` is zero, every Čech cohomology group of `F` has dimension zero. -/
theorem finrank_cechCohomology_of_isZero_sections
    (F : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X)) (hF : ∀ U, IsZero (F.obj.obj U)) (n : ℕ) :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj F.obj) = 0 :=
  finrank_moduleCat_eq_zero_of_isZero (isZero_cechCohomology_of_isZero_sections F hF n)

end TauCeti.RiemannSurface
