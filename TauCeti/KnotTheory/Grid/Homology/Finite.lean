/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Unblocked
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite generation of unblocked grid homology

The unblocked grid chain module has one generator for each grid state. Over a Noetherian
coefficient ring, its cycles and homology are therefore finitely generated over the multivariate
polynomial ring of grid variables. For a knot grid, the variables act identically on homology, so
the same finite set generates over the single-variable polynomial ring. This finite generation is
needed to bound the Alexander degrees used in the definition of the grid concordance invariant.

The argument uses the Noetherian property of a polynomial ring in finitely many variables and the
surjective cycle-class map. It applies to any Noetherian coefficient ring of characteristic two;
in particular it applies over `ZMod 2`.

## References

The use of a finitely generated `𝔽[U]`-module for knot grid homology follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 4 and 6.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]
  [IsNoetherianRing R]

/-- Unblocked grid homology is finitely generated over the polynomial ring in all grid
variables when the coefficient ring is Noetherian. -/
theorem finite_unblockedHomology :
    Module.Finite (MvPolynomial (Fin n) R) (G.unblockedHomology R) := by
  let A := MvPolynomial (Fin n) R
  have : IsNoetherianRing A := inferInstance
  have : Module.Finite A (GridChainMinus R n) := inferInstance
  have : IsNoetherian A (GridChainMinus R n) := inferInstance
  have : Module.Finite A (LinearMap.ker (G.unblockedDifferential R)) := inferInstance
  have : Module.Finite A
      ((G.unblockedDifferential R).homology
        (G.unblockedDifferential_comp_self_eq_zero R)) :=
    Module.Finite.of_surjective
      ((G.unblockedDifferential R).homologyπ
        (G.unblockedDifferential_comp_self_eq_zero R))
      ((G.unblockedDifferential R).homologyπ_surjective
        (G.unblockedDifferential_comp_self_eq_zero R))
  exact Module.Finite.equiv (G.unblockedHomologyIso R).symm.toLinearEquiv

namespace IsKnot

/-- The unblocked homology of a knot grid is finitely generated over `R[U]`: every grid
variable acts as `U` on homology. -/
theorem finite_unblockedHomology (hG : G.IsKnot) :
    letI := hG.unblockedHomologyModule R
    Module.Finite (Polynomial R) (G.unblockedHomology R) := by
  let _ := hG.unblockedHomologyModule R
  let π : MvPolynomial (Fin n) R →+* Polynomial R :=
    (MvPolynomial.aeval fun _ => (Polynomial.X : Polynomial R)).toRingHom
  have : Module.Finite (MvPolynomial (Fin n) R) (G.unblockedHomology R) :=
    G.finite_unblockedHomology R
  let f : G.unblockedHomology R →ₛₗ[π] G.unblockedHomology R := {
    toFun := id
    map_add' _ _ := rfl
    map_smul' p x := (hG.aeval_smul_unblockedHomology p x).symm }
  exact Module.Finite.of_surjective f (fun x => ⟨x, rfl⟩)

end IsKnot

end TauCeti.GridDiagram
