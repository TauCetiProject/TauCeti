/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import TauCeti.Algebra.Ring.Action.End
public import TauCeti.RingTheory.Invariant.Basic

/-!
# The orbit polynomial of an algebra generator

For a faithful finite group action with invariant ring `R`, the orbit polynomial of a generator
of the `R`-algebra is its minimal polynomial, mapped to the algebra. Its derivative is therefore
the product of the nonidentity displacements. This connects the different of a monogenic
extension with its ramification filtration.

The orbit polynomial and its derivative are those of `MulSemiringAction.charpoly` and
`TauCeti.MulSemiringAction.eval_derivative_charpoly`.
-/

public section

open Polynomial

namespace TauCeti.MulSemiringAction

variable {R S G : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
  [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsInvariant R S G] [FaithfulSMul G S]

/-- The minimal polynomial of an algebra generator is the orbit polynomial of a faithful
finite group action with invariant ring `R`. -/
theorem map_minpoly_eq_charpoly_of_adjoin_eq_top {x : S}
    (hx : Algebra.adjoin R {x} = ⊤) :
    (minpoly R x).map (algebraMap R S) = MulSemiringAction.charpoly G x := by
  have hint : IsIntegral R x := (Algebra.IsInvariant.isIntegral R S G).isIntegral x
  obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts R S G x
  simp only [coe_mapRingHom] at hp
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hint).map _)
    (MulSemiringAction.monic_charpoly G x)
  · have hroot : aeval x p = 0 := by
      rw [← eval_map_algebraMap, hp, MulSemiringAction.eval_charpoly]
    rw [← hp]
    exact Polynomial.map_dvd _ (minpoly.isIntegrallyClosed_dvd hint hroot)
  · exact Polynomial.natDegree_le_of_dvd
      (TauCeti.MulSemiringAction.charpoly_dvd
        (smul_left_injective_of_adjoin_singleton_eq_top hx)
        (fun g ↦ by simp only [eval_map_algebraMap, aeval_smul, minpoly.aeval, smul_zero]))
      ((minpoly.monic hint).map _).ne_zero

/-- At an algebra generator, the derivative of the minimal polynomial is the product of the
nonidentity displacements under the group action. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq G] {x : S}
    (hx : Algebra.adjoin R {x} = ⊤) :
    aeval x (derivative (minpoly R x)) =
      ∏ g ∈ (Finset.univ : Finset G).erase 1, (x - g • x) := by
  rw [← eval_map_algebraMap, ← derivative_map,
    map_minpoly_eq_charpoly_of_adjoin_eq_top (G := G) hx,
    TauCeti.MulSemiringAction.eval_derivative_charpoly]

end TauCeti.MulSemiringAction
