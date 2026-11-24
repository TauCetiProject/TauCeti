/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike

import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
import TauCeti.Algebra.Bialgebra.GroupLike.Map
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Regular
import TauCeti.GroupTheory.Finiteness

/-!
# Finite generation of group-like elements

If a finite-type Hopf algebra over a commutative ring is spanned by linearly independent
group-like elements, then its group of group-like elements is finitely generated. Indeed,
evaluation identifies the group algebra on the group-like elements with the original Hopf algebra.
Finite type transports across this equivalence, and a group algebra over a nontrivial commutative
ring is of finite type exactly when its indexing group is finitely generated. Over the trivial ring
the Hopf algebra is trivial, so the group of group-like elements is trivial.

The result does not require the Hopf algebra to be commutative. Over a domain, linear independence
is automatic when the carrier is torsion-free.

Conversely, a bialgebra spanned by a finitely generated monoid of group-like elements is of
finite type, being a quotient of a finitely generated monoid algebra. Over a field this gives the
finiteness half of the statement that a quotient group of a diagonalizable group is
diagonalizable: a Hopf algebra `H` that embeds in a finite-type commutative Hopf algebra `K`
spanned by its group-like elements is spanned by its own group-like elements, which form a
subgroup of the finitely generated commutative group of group-like elements of `K`, so `H` is of
finite type. No reducedness of `K` is needed.

## Main declarations

* `TauCeti.GroupLike.fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top`: finite
  generation when the group-like elements are linearly independent and span.
* `TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top`: the domain specialization for
  a torsion-free carrier.
* `TauCeti.GroupLike.finiteType_of_fg_of_groupLikeSetSpan_eq_top`: a bialgebra spanned by a
  finitely generated monoid of group-like elements is of finite type.
* `BialgHom.finiteType_of_injective_of_groupLikeSetSpan_eq_top`: over a field, a Hopf algebra
  embedding in a finite-type commutative Hopf algebra spanned by its group-like elements is of
  finite type.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Theorems 12.8--12.9.
-/

public section

namespace TauCeti

universe u v

namespace GroupLike

/-- The linearly independent group-like elements spanning a finite-type Hopf algebra over a
commutative ring form a finitely generated group.

The spanning hypothesis is expressed intrinsically through the subcoalgebra spanned by all
group-like elements. -/
theorem fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [Semiring H] [HopfAlgebra R H]
    (hfinite : Algebra.FiniteType R H)
    (hlinear : LinearIndependent R (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton H := Module.subsingleton R H
    have : Subsingleton (_root_.GroupLike R H) :=
      (_root_.GroupLike.val_injective (R := R) (A := H)).subsingleton
    infer_instance
  have hlinearSpan :
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ :=
    (liftGroupLikeBialgHom_surjective_iff_span_eq_top R H).1
      ((liftGroupLikeBialgHom_surjective_iff_groupLikeSetSpan_eq_top R H).2 hspan)
  apply (MonoidAlgebra.finiteType_iff_group_fg
    (R := R) (G := _root_.GroupLike R H)).1
  exact Algebra.FiniteType.equiv hfinite
    (evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H
      hlinear hlinearSpan).toAlgEquiv.symm

/-- The group-like elements spanning a finite-type Hopf algebra over a domain form a finitely
generated group, provided the carrier is torsion-free over the base. -/
theorem fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [IsDomain R] [Ring H] [HopfAlgebra R H]
    [Module.IsTorsionFree R H] (hfinite : Algebra.FiniteType R H)
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) :=
  fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top R H hfinite
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

/-- A bialgebra spanned by its group-like elements is of finite type as soon as they form a
finitely generated monoid. For a Hopf algebra the group-like elements form a group, and it
suffices that this group be finitely generated. This is the converse of
`fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top`, and needs no linear
independence. -/
theorem finiteType_of_fg_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [Bialgebra R H]
    [Monoid.FG (_root_.GroupLike R H)]
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Algebra.FiniteType R H := by
  -- Mathlib's finite-type instance for monoid algebras assumes a base ring, so compose the
  -- evaluation with the presentation of the monoid algebra by a free algebra directly.
  obtain ⟨S, hS, hfinite⟩ := Monoid.fg_iff.mp ‹Monoid.FG (_root_.GroupLike R H)›
  have : Finite S := hfinite.to_subtype
  exact .of_surjective
    ((MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)).toAlgHom.comp
      (FreeAlgebra.lift R fun s : S => MonoidAlgebra.of R (_root_.GroupLike R H) ↑s))
    (((liftGroupLikeBialgHom_surjective_iff_groupLikeSetSpan_eq_top R H).mpr hspan).comp
      (MonoidAlgebra.freeAlgebra_lift_of_surjective_of_closure hS))

end GroupLike

end TauCeti

namespace BialgHom

variable {k H K : Type*} [Field k] [Ring H] [HopfAlgebra k H] [CommRing K] [HopfAlgebra k K]

/-- **Over a field, a Hopf algebra that embeds in a finite-type commutative Hopf algebra spanned
by its group-like elements is of finite type.** Contravariantly, a quotient group of a
diagonalizable group of finite type is of finite type. The ambient Hopf algebra need not be
reduced. -/
theorem finiteType_of_injective_of_groupLikeSetSpan_eq_top [Algebra.FiniteType k K]
    (f : H →ₐc[k] K) (hf : Function.Injective f)
    (hK : TauCeti.Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤) :
    Algebra.FiniteType k H := by
  have : Group.FG (GroupLike k K) :=
    TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k K inferInstance hK
  have hinj := mapGroupLike_injective hf
  have : Group.FG (GroupLike k H) :=
    Group.fg_of_surjective (f := (MonoidHom.ofInjective hinj).symm.toMonoidHom)
      (MonoidHom.ofInjective hinj).symm.surjective
  exact TauCeti.GroupLike.finiteType_of_fg_of_groupLikeSetSpan_eq_top k H
    (CoalgHom.groupLikeSetSpan_eq_top_of_injective f.toCoalgHom hf hK)

end BialgHom
