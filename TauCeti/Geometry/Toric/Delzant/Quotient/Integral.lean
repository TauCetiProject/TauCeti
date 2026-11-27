/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Toric.Delzant.Quotient.Betti
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.IntegralHomology
import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Toric.Delzant.Quotient.Topology
import TauCeti.Topology.Connected.TypeTags

/-!
# The integral homology and cohomology of a Delzant toric manifold

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ ⊆ V*`, with Delzant quotient `M_Δ` (`TauCeti.Toric.DelzantQuotient i u c`). The torus
`T = (ℝ / 2πℤ)^ι` acts on `M_Δ` by symplectomorphisms with a moment map
(`TauCeti.Toric.IsDelzant.hamiltonianTorusData_delzantQuotientSymplecticForm`), and its fixed
points, one over each vertex of `Δ`, are isolated
(`TauCeti.Toric.DelzantQuotient.eventually_eq_of_mem_fixedPoints_multiplicative`). A generic
component of the moment map is therefore a Morse function all of whose critical points have even
index, and the integral homology and cohomology of a compact Hamiltonian torus manifold with
isolated fixed points are those of a complex with only even cells
(`TauCeti.SmoothTwoForm.IsMomentMap.free_singularHomology_int`,
`TauCeti.SmoothTwoForm.IsMomentMap.free_singularCohomology_int` and their companions). This file
specializes these results to `M_Δ`:

* the integral homology `Hⱼ(M_Δ; ℤ)` and cohomology `Hʲ(M_Δ; ℤ)` are free abelian groups in
  every degree, so `M_Δ` has no torsion
  (`TauCeti.Toric.IsDelzant.free_singularHomology_int_delzantQuotient`,
  `TauCeti.Toric.IsDelzant.free_singularCohomology_int_delzantQuotient`);
* they vanish in odd degrees
  (`TauCeti.Toric.IsDelzant.isZero_singularHomology_int_delzantQuotient_of_odd`,
  `TauCeti.Toric.IsDelzant.isZero_singularCohomology_int_delzantQuotient_of_odd`);
* for `x ∈ V` on which no edge vector at any vertex of `Δ` vanishes, their rank in degree `j` is
  the number of vertices of `Δ` at which twice the number of edges along which `⟨·, x⟩` decreases
  is `j` (`TauCeti.Toric.IsDelzant.finrank_singularHomology_int_delzantQuotient_eq_ncard`,
  `TauCeti.Toric.IsDelzant.finrank_singularCohomology_int_delzantQuotient_eq_ncard`), the count
  of the Betti numbers of `M_Δ` in
  `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_ncard`.

The integral coefficients are the integers lifted to the universe of `M_Δ`. Only the additive
structure of the cohomology is computed here, not its ring structure.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1, Theorem 3.2
  (the universal coefficient theorem).
-/

public section

open CategoryTheory Limits AlgebraicTopology Module Real Topology
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance delzantQuotientIntegralTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

universe w

variable {ι : Type w} {N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- The integral (co)homology of a generic component of the moment map of a Delzant toric
manifold, done once: in every degree the integral homology and cohomology are free, they vanish in
odd degrees, and their ranks are the Betti numbers over every division ring. -/
private theorem free_and_isZero_and_finrank_delzantQuotient :
    (∀ n, Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{w} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) ∧
      Module.Free ℤ ((TopCat.of (DelzantQuotient i u c)).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) n)) ∧
    (∀ n, Odd n → IsZero (((singularHomologyFunctor (ModuleCat.{w} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) ∧
      IsZero ((TopCat.of (DelzantQuotient i u c)).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) n)) ∧
    ∀ (k : Type w) [DivisionRing k] (n : ℕ),
      finrank ℤ (((singularHomologyFunctor (ModuleCat.{w} ℤ) n).obj
          (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) =
          bettiNumber k (DelzantQuotient i u c) n ∧
        finrank ℤ ((TopCat.of (DelzantQuotient i u c)).singularCohomology
          (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) n) =
          bettiNumber k (DelzantQuotient i u c) n := by
  have := hi.finiteDimensional
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  have := hi.t2Space_delzantQuotient (u := u) (c := c)
  have := compactSpace_delzantQuotient (c := c) hΔ.isBounded
  have h := (hΔ.hamiltonianTorusData_delzantQuotientSymplecticForm hi hβ).toIsMomentMap
  have hσ := (hΔ.isSymplectic_delzantQuotientSymplecticForm hi).isNondegenerate
  have hσG := fun g ↦ ((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq _).2
    ((hΔ.hamiltonianTorusData_delzantQuotientSymplecticForm hi hβ).mpullback_smul g)).apply
  have hiso (p) (hp : p ∈ MulAction.fixedPoints (Multiplicative (ι → AddCircle (2 * π)))
      (DelzantQuotient i u c)) :=
    DelzantQuotient.eventually_eq_of_mem_fixedPoints_multiplicative hβ hi hp
  exact ⟨fun n ↦ ⟨h.free_singularHomology_int hσ hσG hiso n,
      h.free_singularCohomology_int hσ hσG hiso _ n⟩,
    fun _ hn ↦ ⟨h.isZero_singularHomology_of_odd hσ hσG hiso _ hn,
      h.isZero_singularCohomology_int_of_odd hσ hσG hiso _ hn⟩,
    fun k _ n ↦ ⟨h.finrank_singularHomology_int_eq_bettiNumber hσ hσG hiso k n,
      h.finrank_singularCohomology_int_eq_bettiNumber hσ hσG hiso k n⟩⟩

/-- **The integral homology of a Delzant toric manifold is free** in every degree. -/
theorem free_singularHomology_int_delzantQuotient (n : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{w} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) :=
  ((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).1 n).1

/-- **The integral cohomology of a Delzant toric manifold is free** in every degree. -/
theorem free_singularCohomology_int_delzantQuotient (n : ℕ) :
    Module.Free ℤ ((TopCat.of (DelzantQuotient i u c)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) n) :=
  ((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).1 n).2

/-- **The odd integral homology of a Delzant toric manifold vanishes.** -/
theorem isZero_singularHomology_int_delzantQuotient_of_odd {n : ℕ} (hn : Odd n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) :=
  ((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).2.1 n hn).1

/-- **The odd integral cohomology of a Delzant toric manifold vanishes.** -/
theorem isZero_singularCohomology_int_delzantQuotient_of_odd {n : ℕ} (hn : Odd n) :
    IsZero ((TopCat.of (DelzantQuotient i u c)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) n) :=
  ((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).2.1 n hn).2

/-- **The ranks of the integral homology of a Delzant toric manifold.** For `x ∈ V` on which no
edge vector at any vertex of `Δ` vanishes, the rank of `Hⱼ(M_Δ; ℤ)` is the number of vertices of
`Δ` at which twice the number of edges along which `⟨·, x⟩` decreases is `j`. -/
theorem finrank_singularHomology_int_delzantQuotient_eq_ncard {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) e,
      (hΔ.isSmoothVertex v hv).edgeBasis hi e x ≠ 0) (j : ℕ) :
    finrank ℤ (((singularHomologyFunctor (ModuleCat.{w} ℤ) j).obj
        (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of (DelzantQuotient i u c))) =
      {v | ∃ hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ,
        2 * {e | (hΔ.isSmoothVertex v hv).edgeBasis hi e x < 0}.ncard = j}.ncard := by
  rw [((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).2.2 (ULift.{w} ℚ) j).1,
    hΔ.bettiNumber_delzantQuotient_eq_ncard hi _ hx]

/-- **The ranks of the integral cohomology of a Delzant toric manifold.** For `x ∈ V` on which no
edge vector at any vertex of `Δ` vanishes, the rank of `Hʲ(M_Δ; ℤ)` is the number of vertices of
`Δ` at which twice the number of edges along which `⟨·, x⟩` decreases is `j`. -/
theorem finrank_singularCohomology_int_delzantQuotient_eq_ncard {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) e,
      (hΔ.isSmoothVertex v hv).edgeBasis hi e x ≠ 0) (j : ℕ) :
    finrank ℤ ((TopCat.of (DelzantQuotient i u c)).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) j) =
      {v | ∃ hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ,
        2 * {e | (hΔ.isSmoothVertex v hv).edgeBasis hi e x < 0}.ncard = j}.ncard := by
  rw [((hΔ.free_and_isZero_and_finrank_delzantQuotient hi).2.2 (ULift.{w} ℚ) j).2,
    hΔ.bettiNumber_delzantQuotient_eq_ncard hi _ hx]

end IsDelzant

end TauCeti.Toric
