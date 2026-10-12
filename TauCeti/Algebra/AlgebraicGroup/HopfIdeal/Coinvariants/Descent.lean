/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.BaseChange
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.TensorProduct.Descent
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent of faithful flatness over coinvariants

Faithful flatness of an affine group's coordinate algebra over the functions invariant under
a closed subgroup can be checked after a faithfully flat extension of the base ring.
In particular, over a field the quotient-flatness problem reduces to an algebraic closure.
This does not require normality, finite type, or smoothness of either group.

The coinvariant base-change equivalence identifies the inclusion of invariant functions
after scalar extension with the scalar extension of the original inclusion. Faithfully flat
descent then applies to that inclusion, without first equipping the coinvariants with a
Hopf algebra structure. The common universe for the base rings and the coordinate algebra
is required by the ring-map descent API; algebraic closure preserves that universe.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* `TauCeti.CommHopfAlgCat.coinvariantsBaseChangeEquiv` for the comparison of invariant rings.
* `RingHom.CodescendsAlong.of_tensorProduct_map` for descent of properties of coordinate maps.
-/

public section

namespace TauCeti.CommHopfAlgCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S] {H : _root_.CommHopfAlgCat.{u} R}

/-- Faithful flatness over the coinvariant algebra descends along a faithfully flat extension
of scalars. -/
private theorem faithfullyFlat_coinvariants_of_baseChange (I : HopfIdeal R H)
    (h : (baseChangeHopfIdeal (K := S) I).coinvariants.val.toRingHom.FaithfullyFlat) :
    I.coinvariants.val.toRingHom.FaithfullyFlat := by
  apply RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat.of_tensorProduct_map (S := S)
    I.coinvariants.val
  have he : (Algebra.TensorProduct.map (AlgHom.id R S) I.coinvariants.val).toRingHom =
      (baseChangeHopfIdeal (K := S) I).coinvariants.val.toRingHom.comp
        (coinvariantsBaseChangeEquiv (S := S) I).toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro z
    exact (coe_coinvariantsBaseChangeEquiv I z).symm
  rw [he]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (coinvariantsBaseChangeEquiv I).bijective) h

/-- Faithfully flat extension of scalars preserves and reflects faithful flatness of the
coordinate algebra over its coinvariants. Thus the quotient-flatness problem over a field
can be checked over an algebraic closure. -/
@[simp]
theorem faithfullyFlat_coinvariants_baseChange_iff (I : HopfIdeal R H) :
    ((baseChangeHopfIdeal (K := S) I).coinvariants.val :
      (baseChangeHopfIdeal (K := S) I).coinvariants →+* baseChange (K := S) H).FaithfullyFlat ↔
      (I.coinvariants.val : I.coinvariants →+* H).FaithfullyFlat := by
  refine ⟨faithfullyFlat_coinvariants_of_baseChange I, fun h ↦ ?_⟩
  have he : (baseChangeHopfIdeal (K := S) I).coinvariants.val.toRingHom =
      (Algebra.TensorProduct.lTensor (S := S) S I.coinvariants.val).toRingHom.comp
        (coinvariantsBaseChangeEquiv (S := S) I).symm.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro z
    exact (map_coinvariantsBaseChangeEquiv_symm I z).symm
  simp only [AlgHom.toRingHom_eq_coe] at he
  rw [he]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (coinvariantsBaseChangeEquiv I).symm.bijective)
    (h.lTensor S)

end TauCeti.CommHopfAlgCat
