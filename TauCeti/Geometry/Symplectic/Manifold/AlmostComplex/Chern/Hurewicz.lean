/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern

/-!
# The first Chern number on the second homology of a simply connected manifold

Let `σ` be a fiberwise nondegenerate two-form on a simply connected Hausdorff σ-compact manifold
`M`, for instance a symplectic form. Its first Chern number
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`) is defined on the second homotopy group
`π₂(M, x)` by clutching. The Hurewicz map `π₂(M, x) → H₂(M; ℤ)` is an isomorphism at every base
point (`HomotopyGroup.hurewiczAddEquiv`), so the first Chern number descends to a homomorphism
`TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom : H₂(M; ℤ) →+ ℤ`. Since both the
first Chern number and the Hurewicz map are invariant under base-point change, it agrees with the
first Chern number on the Hurewicz class of every sphere, at every base point
(`TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom_hurewiczIntHom`).

Together with the symplectic area on `H₂(M; ℤ)` (`TauCeti.homologySphereIntegralHom`), this is the
pair of homomorphisms `ω` and `c` from which capped Hamiltonian Floer theory builds its period
group `TauCeti.Floer.SphericalPeriodGroup ω c`. No comparison with a cohomological first Chern
class is made, and manifolds that are not simply connected are not treated.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom`: the first Chern number of a
  fiberwise nondegenerate two-form on `H₂(M; ℤ)`, for a simply connected `M`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom_hurewiczIntHom`: it agrees with
  the first Chern number on Hurewicz classes, at every base point.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the first Chern class on spherical classes and the Novikov ring).
* A. Hatcher, *Algebraic Topology*, Section 4.2 (the Hurewicz theorem).
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
  [SimplyConnectedSpace M] {σ : SmoothTwoForm I M}

/-- **The first Chern number on `H₂(M; ℤ)`** of a fiberwise nondegenerate two-form on a simply
connected manifold `M`: the first Chern number at a base point, transported along the Hurewicz
isomorphism `π₂(M, x) ≅ H₂(M; ℤ)`. It does not depend on the base point: it agrees with the first
Chern number on the Hurewicz class of every sphere, at every base point
(`TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom_hurewiczIntHom`). -/
def homologyFirstChernHom (h : σ.IsNondegenerate) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+
      ℤ :=
  (h.firstChernHom (Classical.arbitrary M)).comp
    (hurewiczAddEquiv (n := 0) fun _ ↦ subsingleton_homotopyGroup_of_lt_two _).symm.toAddMonoidHom

/-- **The first Chern number on `H₂(M; ℤ)` is the first Chern number on Hurewicz classes**, at
every base point. -/
@[simp]
theorem homologyFirstChernHom_hurewiczIntHom (h : σ.IsNondegenerate) (x : M)
    (a : Additive (π_ 2 M x)) :
    h.homologyFirstChernHom (hurewiczIntHom M x 1 a) = h.firstChernHom x a := by
  -- Transport the class to the base point of the definition; both sides are invariant.
  let γ : Path x (Classical.arbitrary M) := PathConnectedSpace.somePath _ _
  rw [← ofMul_toMul a, ← hurewiczIntHom_homotopyGroupTransport γ a.toMul,
    ← hurewiczAddEquiv_apply_eq_hurewiczIntHom (n := 0)
      fun _ ↦ subsingleton_homotopyGroup_of_lt_two _]
  -- Keep `hurewiczAddEquiv` folded, so that it cancels against its inverse.
  simp [homologyFirstChernHom, -hurewiczAddEquiv_apply]

end TauCeti.SmoothTwoForm.IsNondegenerate
