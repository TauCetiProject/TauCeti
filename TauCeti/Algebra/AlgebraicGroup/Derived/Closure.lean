/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import TauCeti.RingTheory.TensorProduct.PointSeparation

/-!
# Derived subgroups of closures of point subgroups

The derived closed subgroup of the reduced closure of a rational-point subgroup `S` is the
reduced closure of `⁅S, S⁆`. This holds over any field: the points of `S` separate functions
on their own closure, and their pairs therefore separate its tensor square. In particular,
this comparison can be iterated along the abstract derived series.

## References

* A. Borel, *Linear Algebraic Groups*, §2.3 and §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.CommHopfAlgCat

noncomputable section

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

private theorem map_vanishingIdeal_commutator_le_derivedDefiningIdeal
    (S : Subgroup (WithConv (H →ₐ[k] k))) :
    (HopfIdeal.vanishingIdeal ⁅S, S⁆).map
        (mkQuotient (_root_.CommHopfAlgCat.of k H) (HopfIdeal.vanishingIdeal S)).hom ≤
      derivedDefiningIdeal (quotient (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.vanishingIdeal S)) := by
  let A := _root_.CommHopfAlgCat.of k H
  let I := HopfIdeal.vanishingIdeal S
  let q := (mkQuotient A I).hom
  let lift (g : S) := liftQuotientPoint A I (CommAlgCat.of k k) g.val
    (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx g)
  have hlift (g : S) (x : H) : (lift g).ofConv (q x) = g.val.ofConv x := by
    rw [mkQuotient_apply, liftQuotientPoint_mk]
  have hsep (x : quotient A I) (hx : ∀ g, (lift g).ofConv x = 0) : x = 0 := by
    obtain ⟨x, rfl⟩ := mkQuotient_surjective A I x
    apply (mkQuotient_eq_zero_iff A I x).mpr
    exact (HopfIdeal.mem_vanishingIdeal S x).mpr fun g ↦ (hlift g x).symm.trans (hx g)
  rw [le_derivedDefiningIdeal_iff]
  intro x hx
  obtain ⟨x, hmem, rfl⟩ :=
    (HopfIdeal.mem_map_iff_of_surjective (mkQuotient_surjective A I)).mp hx
  apply RingHom.mem_ker.mpr
  apply tensor_eq_zero_of_forall_productMap_eq_zero
    (fun g : S ↦ (lift g).ofConv) (fun g : S ↦ (lift g).ofConv) hsep hsep
  intro g h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AlgHom.comp_apply, HopfAlgebra.productMap_comp_commutatorAlgHom]
  have heval := quotientPointsHom_apply_apply A I (CommAlgCat.of k k)
    ⁅lift g, lift h⁆ x
  rw [map_commutatorElement, quotientPointsHom_liftQuotientPoint,
    quotientPointsHom_liftQuotientPoint] at heval
  rw [mkQuotient_apply]
  exact heval.symm.trans ((HopfIdeal.mem_vanishingIdeal ⁅S, S⁆ x).mp hmem
    ⟨⁅g.val, h.val⁆, Subgroup.commutator_mem_commutator g.2 h.2⟩)

/-- Taking the derived closed subgroup commutes with taking the reduced closure of a
rational-point subgroup. The equality is stated as equality of defining ideals in the
ambient coordinate algebra. -/
theorem comapOfSurjective_derivedDefiningIdeal_vanishingIdeal
    (S : Subgroup (WithConv (H →ₐ[k] k))) :
    (derivedDefiningIdeal (quotient (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.vanishingIdeal S))).comapOfSurjective
        (mkQuotient (_root_.CommHopfAlgCat.of k H) (HopfIdeal.vanishingIdeal S)).hom
        (mkQuotient_surjective _ _) = HopfIdeal.vanishingIdeal ⁅S, S⁆ := by
  let A := _root_.CommHopfAlgCat.of k H
  let I := HopfIdeal.vanishingIdeal S
  let q := (mkQuotient A I).hom
  apply le_antisymm
  · apply (HopfIdeal.le_vanishingIdeal_iff _ _).mpr
    apply Subgroup.commutator_le.mpr
    intro g hg h hh
    let g' := liftQuotientPoint A I (CommAlgCat.of k k) g
      (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨g, hg⟩)
    let h' := liftQuotientPoint A I (CommAlgCat.of k k) h
      (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨h, hh⟩)
    apply (mem_quotientPointsSubgroup_iff A _ _ _).mpr
    intro x hx
    have hzero := (mem_quotientPointsSubgroup_iff (quotient A I) _ _ _).mp
      (commutator_mem_derivedPointsSubgroup (quotient A I) (CommAlgCat.of k k) g' h')
      (q x) (HopfIdeal.mem_comapOfSurjective.mp hx)
    have heval := quotientPointsHom_apply_apply A I (CommAlgCat.of k k) ⁅g', h'⁆ x
    rw [map_commutatorElement, quotientPointsHom_liftQuotientPoint,
      quotientPointsHom_liftQuotientPoint] at heval
    exact heval.trans hzero
  · exact (HopfIdeal.map_le_iff_le_comapOfSurjective (mkQuotient_surjective A I)).mp
      (map_vanishingIdeal_commutator_le_derivedDefiningIdeal S)

end

end TauCeti.CommHopfAlgCat
