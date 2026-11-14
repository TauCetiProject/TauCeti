/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic

/-!
# Čech cohomology of the structure sheaf, a point skyscraper and the zero sheaf

This file computes the Čech cohomology of three basic sheaves of complex vector spaces on a
complex curve. The computations show that the curve must be nonempty for `H⁰(𝒪) = ℂ`, and that
the skyscraper `ℂ_x` cannot be replaced by the zero sheaf, as it would be if its support were
empty.

* **The structure sheaf.** On a nonempty compact connected complex curve the degree-zero Čech
  cohomology of the holomorphic structure sheaf `𝒪` is one-dimensional, since global holomorphic
  functions are constant. On the empty curve every Čech cohomology group of every presheaf
  vanishes (`TauCeti.Topology.isZero_cechCohomology_obj_of_isEmpty`), so `H⁰(𝒪) = 0 ≠ ℂ`:
  nonemptiness is essential.
* **The point skyscraper.** For the skyscraper sheaf `ℂ_x` with stalk `ℂ` at a point `x`, which
  is the cokernel sheaf in the point-twist sequence `0 → 𝒪(D) → 𝒪(D + x) → ℂ_x → 0`, the
  degree-zero Čech cohomology is one-dimensional and every positive-degree group vanishes
  (`TauCeti.Topology.isZero_cechCohomology_skyscraperPresheaf`). In particular `H⁰(ℂ_x)` is not
  zero.
* **The zero sheaf.** A presheaf all of whose sections are zero has vanishing Čech cohomology in
  every degree (`TauCeti.Topology.isZero_cechCohomology_obj_of_isZero`). This is what treating
  the support of `ℂ_x` as empty would produce, and it disagrees with `H⁰(ℂ_x) = ℂ`.

No compactness, connectedness or separation is used for the skyscraper and zero-sheaf
statements.

## Main results

* `TauCeti.RiemannSurface.finrank_cechCohomology_zero_holomorphicStructureSheafModules`:
  `dim H⁰(X, 𝒪) = 1` on a nonempty compact connected complex curve.
* `TauCeti.RiemannSurface.finrank_cechCohomology_holomorphicStructureSheafModules_of_isEmpty`:
  on the empty curve `dim Hⁿ(X, 𝒪) = 0` for every `n`, in particular `dim H⁰(X, 𝒪) = 0`. The
  vanishing itself is `TauCeti.Topology.isZero_cechCohomology_obj_of_isEmpty`.
* `TauCeti.RiemannSurface.finrank_cechCohomology_zero_skyscraperSheaf`: `dim H⁰(X, ℂ_x) = 1`.
* `TauCeti.RiemannSurface.finrank_cechCohomology_succ_skyscraperSheaf`: `dim Hⁿ⁺¹(X, ℂ_x) = 0`.
  The vanishing itself is `TauCeti.Topology.isZero_cechCohomology_skyscraperPresheaf`.
* `TauCeti.RiemannSurface.finrank_cechCohomology_of_isZero_sections`: a presheaf with zero
  sections has `dim Hⁿ = 0` for every `n`. The vanishing itself is
  `TauCeti.Topology.isZero_cechCohomology_obj_of_isZero`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§12, 16.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type} [TopologicalSpace X]

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

/-- **Nonemptiness is essential for `H⁰(𝒪) = ℂ`.** On an empty complex curve every Čech
cohomology group of the holomorphic structure sheaf has dimension zero. In degree zero this gives
dimension zero, not one, although the curve is compact and preconnected. Nonemptiness is the extra
condition that makes a preconnected space connected. Compare
`finrank_cechCohomology_zero_holomorphicStructureSheafModules`. The groups themselves vanish by
`TauCeti.Topology.isZero_cechCohomology_obj_of_isEmpty`, which applies to every presheaf on the
empty space; this statement records the dimension. -/
theorem finrank_cechCohomology_holomorphicStructureSheafModules_of_isEmpty [IsEmpty X] (n : ℕ) :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) = 0 :=
  have : IsEmpty (TopCat.of X) := inferInstanceAs (IsEmpty X)
  ModuleCat.finrank_eq_zero_of_isZero (isZero_cechCohomology_obj_of_isEmpty _ _ n _)

end StructureSheaf

/-! ### The point skyscraper -/

variable (x : X)

open Classical in
/-- **The point skyscraper has `H⁰ = ℂ`.** The degree-zero Čech cohomology of the skyscraper
sheaf with stalk `ℂ` at `x`, the cokernel of the point twist `𝒪(D) → 𝒪(D + x)`, is
one-dimensional. -/
theorem finrank_cechCohomology_zero_skyscraperSheaf :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) = 1 := by
  rw [← (pointTwistCoefficientCechIso x).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

open Classical in
/-- The degree-zero Čech cohomology of the point skyscraper is not zero. -/
theorem not_isZero_cechCohomology_zero_skyscraperSheaf :
    ¬ IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) := fun h ↦ by
  simpa [ModuleCat.finrank_eq_zero_of_isZero h] using finrank_cechCohomology_zero_skyscraperSheaf x

open Classical in
/-- Every positive-degree Čech cohomology group of the skyscraper sheaf with stalk `ℂ` at `x`
has dimension zero. The acyclicity of the skyscraper, that is the vanishing of these groups, is
`TauCeti.Topology.isZero_cechCohomology_skyscraperPresheaf`, for any coefficient object; this
statement records the dimension. -/
theorem finrank_cechCohomology_succ_skyscraperSheaf (n : ℕ) :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) (n + 1)).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj) = 0 :=
  ModuleCat.finrank_eq_zero_of_isZero
    (isZero_cechCohomology_skyscraperPresheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ)) n)

/-! ### The zero sheaf -/

/-- If every section of `P` is zero, every Čech cohomology group of `P` has dimension zero. This
is the answer that treating the support of the point skyscraper as empty would give, which
`not_isZero_cechCohomology_zero_skyscraperSheaf` rules out in degree zero. The vanishing of these
groups is `TauCeti.Topology.isZero_cechCohomology_obj_of_isZero`; this statement records the
dimension. -/
theorem finrank_cechCohomology_of_isZero_sections
    (P : (Opens (TopCat.of X))ᵒᵖ ⥤ ModuleCat.{0} ℂ) (hP : ∀ U, IsZero (P.obj U)) (n : ℕ) :
    Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj P) = 0 :=
  ModuleCat.finrank_eq_zero_of_isZero (isZero_cechCohomology_obj_of_isZero _ _ n _ hP)

end TauCeti.RiemannSurface
