/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient

/-!
# The affine abelianization

The quotient of an affine group by its derived closed subgroup is commutative. Its coordinate
Hopf algebra is the coinvariants of the derived defining ideal, and every homomorphism to a
commutative affine group factors uniquely through the quotient projection.

More generally, for an injective coordinate morphism between flat commutative Hopf algebras,
the target group is commutative exactly when the scheme-theoretic kernel contains the derived
subgroup of the source group. In defining ideals, this containment reverses direction. This
criterion does not replace the scheme-theoretic kernel by the kernel on rational points, and
requires neither smoothness nor finite type.

The construction uses `TauCeti.CommHopfAlgCat.coinvariants` and its universal property
`TauCeti.CommHopfAlgCat.liftCoinvariants`, together with
`CommHopfAlgCat.Hom.kernelHopfIdeal_le_derivedDefiningIdeal`.
Over a field all required flatness assumptions
are automatic. Over a general base the coinvariant construction needs the explicitly stated
flatness assumptions below.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10 and §16.3.
-/

public section

open CategoryTheory

universe u v

namespace CommHopfAlgCat.Hom

open TauCeti TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R] {Q H : CommHopfAlgCat.{v} R}

/-- For an injective coordinate morphism between flat Hopf algebras, the target affine group
is commutative exactly when its scheme-theoretic kernel contains the source's derived subgroup.
The inclusion of Hopf ideals is reversed relative to the inclusion of subgroups. -/
theorem isCocomm_iff_kernelHopfIdeal_le_derivedDefiningIdeal
    (f : Q ⟶ H) [Module.Flat R Q] [Module.Flat R H]
    (hf : Function.Injective f.hom) :
    Coalgebra.IsCocomm R Q ↔ kernelHopfIdeal f ≤ derivedDefiningIdeal H := by
  constructor
  · intro hQ
    let := hQ
    exact f.kernelHopfIdeal_le_derivedDefiningIdeal
  · intro hker
    apply (derivedDefiningIdeal_eq_augmentation_iff_isCocomm Q).mp
    apply le_antisymm (HopfIdeal.le_augmentation R Q _)
    rw [le_derivedDefiningIdeal_iff]
    intro x hx
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hx' : f.hom x ∈ derivedDefiningIdeal H :=
      hker (mem_kernelHopfIdeal_of_mem_augmentation f
        ((HopfIdeal.mem_augmentation R Q).mp (HopfIdeal.mem_toIdeal.mp hx)))
    exact f.hom.commutatorAlgHom_eq_zero_of_map_mem_derivedDefiningIdeal hf hx'

end CommHopfAlgCat.Hom

namespace TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}
variable {I : HopfIdeal R H}
variable [Module.Flat R H] [Module.Flat R I.coinvariants]
  [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)]

/-- The affine quotient by a normal closed subgroup containing the derived subgroup is
commutative. No reducedness, smoothness, or finite-type hypothesis is needed. -/
theorem isCocomm_coinvariants_of_le_derivedDefiningIdeal (hI : I.IsNormal)
    (hID : I ≤ derivedDefiningIdeal H) :
    letI := (coinvariants hI).hopfAlgebra
    Coalgebra.IsCocomm R (coinvariants hI) := by
  let := (coinvariants hI).hopfAlgebra
  exact ((coinvariantsι hI).isCocomm_iff_kernelHopfIdeal_le_derivedDefiningIdeal
    (hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants)).mpr
      ((kernelHopfIdeal_coinvariantsι_le hI).trans hID)

end TauCeti.CommHopfAlgCat

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : CommHopfAlgCat.{v} R}
variable [Module.Flat R H]
variable [Module.Flat R (derivedDefiningIdeal (R := R) H).coinvariants]
  [Module.Flat R (H ⧸ Subalgebra.toSubmodule (derivedDefiningIdeal (R := R) H).coinvariants)]

/-- The affine quotient by the derived closed subgroup is commutative.
The Hopf structure is the bundled coinvariant structure; it depends on the normality proof
and is not an instance on the unbundled subtype independently of that proof. -/
instance isCocomm_coinvariants_derivedDefiningIdeal (H : CommHopfAlgCat.{v} R)
    [Module.Flat R H] [Module.Flat R (derivedDefiningIdeal (R := R) H).coinvariants]
    [Module.Flat R (H ⧸ Subalgebra.toSubmodule (derivedDefiningIdeal (R := R) H).coinvariants)] :
    letI := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    Coalgebra.IsCocomm R (coinvariants (isNormal_derivedDefiningIdeal H)) :=
  isCocomm_coinvariants_of_le_derivedDefiningIdeal (isNormal_derivedDefiningIdeal H) le_rfl

/-- Every homomorphism from an affine group to a commutative affine group factors uniquely
through its affine quotient by the derived closed subgroup. In coordinates, a morphism from
a cocommutative Hopf algebra factors uniquely through the derived coinvariants. -/
theorem Hom.existsUnique_comp_coinvariantsι_derivedDefiningIdeal
    [Coalgebra.IsCocomm R K] (f : K ⟶ H) :
    ∃! g : K ⟶ coinvariants (isNormal_derivedDefiningIdeal H),
      g ≫ coinvariantsι (isNormal_derivedDefiningIdeal H) = f := by
  have hf := f.kernelHopfIdeal_le_derivedDefiningIdeal
  exact ⟨liftCoinvariants (isNormal_derivedDefiningIdeal H) f hf,
    liftCoinvariants_comp_coinvariantsι _ f hf,
    fun g hg ↦ liftCoinvariants_unique _ f hf g hg⟩

end CommHopfAlgCat
