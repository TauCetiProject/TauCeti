/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.KnotTheory.Grid.Chain.Complex
public import TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# Simply blocked grid homology

This file defines the simply blocked grid homology of a knot grid as the homology of the
one-variable specialization of its unblocked grid complex.  Concretely, after choosing an
`O`-marking in column `i` to block, the coefficient ring is the polynomial ring in the remaining
columns and the differential counts empty rectangles avoiding all `X`-markings and the blocked
`O`-marking.

The public cycle-class API presents Mathlib's categorical homology as the explicit quotient of
the kernel of the differential by its image.  Every homology class has a cycle representative,
and two representatives determine the same class exactly when their difference is a boundary.

For a multi-component link, the standard simply blocked theory blocks one `O`-marking on every
component.  The construction here is therefore named simply blocked homology only under the
`GridDiagram.IsKnot` hypothesis; the underlying one-variable specialization remains available for
every grid diagram as `GridDiagram.simplyBlockedComplex`.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomology`: the simply blocked homology `G-hat`.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedCycles`: its cycles as a kernel.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyQuotient`: the concrete cycles-modulo-boundaries
  model.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyIsoQuotient`: its canonical identification with
  Mathlib's categorical homology.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyClass`: the linear map taking a cycle to its
  homology class.

## Main results

* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyClass_surjective`: every class has a cycle
  representative.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyClass_eq_iff`: two cycles represent the same
  class exactly when their difference is in the range of the differential.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyClass_eq_zero_iff`: a cycle represents zero
  exactly when it is a boundary.

## References

The construction and coefficient convention follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Section 4.6.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n}
variable (R : Type*) [CommRing R] [CharP R 2]

/-- The simply blocked grid homology `G-hat` obtained by setting the variable of column `i` to
zero.

The knot hypothesis records when the one-variable specialization has its standard topological
meaning: a knot has one component, so blocking one `O`-marking blocks one marking on every
component. -/
noncomputable abbrev simplyBlockedHomology (hG : G.IsKnot) (i : Fin n) :
    ModuleCat (MvPolynomial {c : Fin n // c ≠ i} R) :=
  (fun _ : G.IsKnot => (G.simplyBlockedComplex R i).homology ()) hG

/-- The cycles of the simply blocked differential, as an explicit submodule of the chain module. -/
noncomputable abbrev simplyBlockedCycles (hG : G.IsKnot) (i : Fin n) :
    Submodule (MvPolynomial {c : Fin n // c ≠ i} R)
      ((G.simplyBlockedComplex R i).X ()) :=
  (fun _ : G.IsKnot => LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) hG

/-- The boundary map into the cycles of the simply blocked complex.  Its image is contained in the
cycles because the differential squares to zero. -/
noncomputable abbrev simplyBlockedBoundaryMap (hG : G.IsKnot) (i : Fin n) :
      (G.simplyBlockedComplex R i).X ()
      →ₗ[MvPolynomial {c : Fin n // c ≠ i} R]
      hG.simplyBlockedCycles R i :=
  ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles

/-- Membership in the cycle module means that the explicit differential vanishes. -/
theorem mem_simplyBlockedCycles (hG : G.IsKnot) (i : Fin n)
    (c : (G.simplyBlockedComplex R i).X ()) :
    c ∈ hG.simplyBlockedCycles R i ↔
      G.simplyBlockedDifferential R i (G.simplyBlockedChainEquiv R i c) = 0 := by
  rw [← G.simplyBlockedChainEquiv_d, ← map_zero (G.simplyBlockedChainEquiv R i),
    (G.simplyBlockedChainEquiv R i).injective.eq_iff]
  rfl

/-- The boundaries of the simply blocked complex, regarded as a submodule of its cycles. -/
noncomputable abbrev simplyBlockedBoundaries (hG : G.IsKnot) (i : Fin n) :
    Submodule (MvPolynomial {c : Fin n // c ≠ i} R)
      (hG.simplyBlockedCycles R i) :=
  LinearMap.range (hG.simplyBlockedBoundaryMap R i)

/-- The concrete cycles-modulo-boundaries model of simply blocked grid homology. -/
noncomputable abbrev simplyBlockedHomologyQuotient (hG : G.IsKnot) (i : Fin n) : Type _ :=
  let C := hG.simplyBlockedCycles R i
  let B : Submodule (MvPolynomial {c : Fin n // c ≠ i} R) C :=
    hG.simplyBlockedBoundaries R i
  C ⧸ B

/-- Mathlib's categorical homology of the simply blocked complex is canonically isomorphic to the
concrete quotient of cycles by boundaries. -/
noncomputable def simplyBlockedHomologyIsoQuotient (hG : G.IsKnot) (i : Fin n) :
    hG.simplyBlockedHomology R i ≅
      ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R)
        (hG.simplyBlockedHomologyQuotient R i) :=
  (G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl ≪≫
    ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso

/-- The linear map sending a simply blocked cycle to its homology class. -/
noncomputable def simplyBlockedHomologyClass (hG : G.IsKnot) (i : Fin n)
    : hG.simplyBlockedCycles R i
      →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] hG.simplyBlockedHomology R i :=
  (hG.simplyBlockedHomologyIsoQuotient R i).inv.hom.comp
    (hG.simplyBlockedBoundaries R i).mkQ

/-- Under the concrete cycles-modulo-boundaries identification, the class of a cycle is its
quotient class. -/
@[simp]
theorem simplyBlockedHomologyIsoQuotient_hom_class (hG : G.IsKnot) (i : Fin n)
    (c : hG.simplyBlockedCycles R i) :
    (hG.simplyBlockedHomologyIsoQuotient R i).hom (hG.simplyBlockedHomologyClass R i c) =
      Submodule.Quotient.mk c := by
  simp [simplyBlockedHomologyClass]

/-- Every simply blocked homology class has a cycle representative. -/
theorem simplyBlockedHomologyClass_surjective (hG : G.IsKnot) (i : Fin n) :
    Function.Surjective (hG.simplyBlockedHomologyClass R i) := by
  intro x
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective
    (p := hG.simplyBlockedBoundaries R i)
    ((hG.simplyBlockedHomologyIsoQuotient R i).hom x)
  refine ⟨c, ?_⟩
  apply (ModuleCat.mono_iff_injective (hG.simplyBlockedHomologyIsoQuotient R i).hom).1
    inferInstance
  simpa [simplyBlockedHomologyClass] using hc

/-- Two cycles represent the same simply blocked homology class exactly when their difference is
a boundary. -/
theorem simplyBlockedHomologyClass_eq_iff (hG : G.IsKnot) (i : Fin n)
    (c c' : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyClass R i c = hG.simplyBlockedHomologyClass R i c' ↔
      c - c' ∈ hG.simplyBlockedBoundaries R i := by
  constructor
  · intro h
    rw [← Submodule.Quotient.eq]
    simpa [simplyBlockedHomologyClass] using congrArg
      (fun x => (hG.simplyBlockedHomologyIsoQuotient R i).hom x) h
  · intro h
    have h' : (Submodule.Quotient.mk c : hG.simplyBlockedHomologyQuotient R i) =
        Submodule.Quotient.mk c' := by
      rw [Submodule.Quotient.eq]
      exact h
    simpa [simplyBlockedHomologyClass] using congrArg
      (fun x => (hG.simplyBlockedHomologyIsoQuotient R i).inv x) h'

/-- A cycle represents zero in simply blocked homology exactly when it is a boundary. -/
@[simp]
theorem simplyBlockedHomologyClass_eq_zero_iff (hG : G.IsKnot) (i : Fin n)
    (c : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyClass R i c = 0 ↔ c ∈ hG.simplyBlockedBoundaries R i := by
  simpa [simplyBlockedHomologyClass] using
    simplyBlockedHomologyClass_eq_iff (G := G) R hG i c 0

/-- The kernel of the cycle-class map is exactly the submodule of boundaries. -/
@[simp]
theorem ker_simplyBlockedHomologyClass (hG : G.IsKnot) (i : Fin n) :
    LinearMap.ker (hG.simplyBlockedHomologyClass R i) = hG.simplyBlockedBoundaries R i := by
  ext c
  rw [LinearMap.mem_ker, simplyBlockedHomologyClass_eq_zero_iff]

end TauCeti.GridDiagram.IsKnot
