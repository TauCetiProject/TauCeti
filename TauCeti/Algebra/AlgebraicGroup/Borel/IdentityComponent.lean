/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent

/-!
# Borel subgroups and the identity component

Over an algebraically closed field, an affine group of finite type and its identity
component have the same Borel subgroups. More generally, a Borel subgroup contained in a
closed subgroup is Borel in that subgroup's identity component. These comparisons allow
conjugacy arguments to pass to connected ambient groups.

Containment in the identity component follows from
`CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected` and
`HopfIdeal.identityComponent_le_of_le`. Borel maximality is transported by the
closed-subgroup comparison in `Borel.Subgroup`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), §§2.a and 17.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A closed subgroup of the identity component is Borel there exactly when it is Borel
in the whole group. No smoothness hypothesis on the ambient group is needed. -/
theorem isBorelOverAlgClosed_comap_identityComponent_iff
    (J : HopfIdeal k (FiniteTypeCommHopfAlgCat.identityComponent H)) :
    IsBorelOverAlgClosed k H
      (J.comapOfSurjective
        (Bialgebra.Quotient.mkBialgHom
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal)
        (Bialgebra.Quotient.mkBialgHom_surjective _)) ↔
      IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.identityComponent H) J := by
  apply isBorelOverAlgClosed_comapOfSurjective_iff
    (FiniteTypeCommHopfAlgCat.mkQuotient H
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)))
  intro I hI
  let _ : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I)) :=
    hI.geometricallyConnected.connectedSpace k _
  have hCI : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) ≤ I := by
    intro x hx
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x).mp
    exact CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
      (CommHopfAlgCat.mkQuotient H.obj I) (mem_toIdeal.mpr hx)
  apply (toIdeal_le_toIdeal).mp
  exact (kerOfSurjective_toIdeal _ _).le.trans
    ((FiniteTypeCommHopfAlgCat.mkQuotient_ker _ _).le.trans
      ((toIdeal_le_toIdeal).mpr hCI))

/-- A Borel subgroup contained in `P` remains Borel when the ambient group is restricted
to the identity component of `P`. -/
theorem IsBorelOverAlgClosed.map_identityComponent_of_le {P I : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k H I) (hPI : P ≤ I) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient H P.identityComponent)
      (I.map (Bialgebra.Quotient.mkBialgHom P.identityComponent.toIdeal)) := by
  have hc := ((isBorelOverAlgClosed_iff k H I).mp hI).2.prop.geometricallyConnected
  exact hI.map_of_le (identityComponent_le_of_le hPI hc)

end TauCeti.HopfIdeal
