/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Hom
public import TauCeti.RingTheory.Idempotents.Corner.Jacobson
public import TauCeti.RingTheory.Jacobson.Basic
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Local corners

The corner `eAe` of an idempotent `e` is the opposite of the endomorphism ring of the left ideal
`Ae` (`IsIdempotentElem.endSpanSingletonRingEquiv`), so it is local exactly when that endomorphism
ring is. For a primitive idempotent of an Artinian ring, `Ae` is indecomposable of finite length,
and its endomorphism ring is local by Fitting's lemma. More generally, an idempotent whose image
modulo the Jacobson radical is primitive has a local corner when the radical quotient is
semisimple: the radical quotient of `eAe` is the corner of that image
(`IsIdempotentElem.cornerQuotientJacobsonEquiv`), and a ring is local when its radical quotient is,
since units lift modulo the radical (`TauCeti.Ring.isLocalHom_mk_jacobson`).

## Main results

* `IsIdempotentElem.isLocalRing_corner_of_isLocalRing_end` and
  `IsIdempotentElem.isLocalRing_end_of_isLocalRing_corner`: the corner `eAe` is local exactly when
  the endomorphism ring of `Ae` is.
* `TauCeti.IsPrimitiveIdempotent.isLocalRing_corner`: a primitive idempotent of an Artinian ring
  has a local corner.
* `IsIdempotentElem.isLocalRing_corner_of_isPrimitiveIdempotent_mk`: an idempotent that is
  primitive modulo the Jacobson radical has a local corner, when the radical quotient is
  semisimple.
-/

public section

namespace IsIdempotentElem

variable {A : Type*} [Ring A] {e : A}

/-- The corner `eAe` is local when the endomorphism ring of the left ideal `Ae` is. -/
theorem isLocalRing_corner_of_isLocalRing_end (he : IsIdempotentElem e)
    [IsLocalRing (Module.End A (Ideal.span {e} : Ideal A))] : IsLocalRing he.Corner :=
  have : Nontrivial he.Corner := he.endSpanSingletonRingEquiv.injective.nontrivial
  IsLocalRing.of_surjective' he.endSpanSingletonRingEquiv.toRingHom
    he.endSpanSingletonRingEquiv.surjective

/-- The endomorphism ring of the left ideal `Ae` is local when the corner `eAe` is. -/
theorem isLocalRing_end_of_isLocalRing_corner (he : IsIdempotentElem e) [IsLocalRing he.Corner] :
    IsLocalRing (Module.End A (Ideal.span {e} : Ideal A)) :=
  have : Nontrivial (Module.End A (Ideal.span {e} : Ideal A))ᵐᵒᵖ :=
    he.endSpanSingletonRingEquiv.symm.injective.nontrivial
  have : IsLocalRing (Module.End A (Ideal.span {e} : Ideal A))ᵐᵒᵖ :=
    IsLocalRing.of_surjective' he.endSpanSingletonRingEquiv.symm.toRingHom
      he.endSpanSingletonRingEquiv.symm.surjective
  have : Nontrivial (Module.End A (Ideal.span {e} : Ideal A)) :=
    MulOpposite.unop_injective.nontrivial
  let σ := (RingEquiv.opOp (Module.End A (Ideal.span {e} : Ideal A))).symm
  IsLocalRing.of_surjective' σ.toRingHom σ.surjective

end IsIdempotentElem

namespace TauCeti

variable {A : Type*} [Ring A] {e : A}

/-- **A primitive idempotent of an Artinian ring has a local corner**, by Fitting's lemma for the
left ideal `Ae`, which has finite length. -/
theorem IsPrimitiveIdempotent.isLocalRing_corner [IsArtinianRing A] (he : IsPrimitiveIdempotent e) :
    IsLocalRing he.isIdempotentElem.Corner := by
  have hfin : IsFiniteLength A (Ideal.span {e} : Ideal A) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have := (isPrimitiveIdempotent_iff_isLocalRing_end he.isIdempotentElem hfin).1 he
  exact he.isIdempotentElem.isLocalRing_corner_of_isLocalRing_end

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [Ring A] {e : A}

/-- **An idempotent that is primitive modulo the Jacobson radical has a local corner**, when the
radical quotient is semisimple. -/
theorem isLocalRing_corner_of_isPrimitiveIdempotent_mk [IsSemisimpleRing (A ⧸ Ring.jacobson A)]
    (he : IsIdempotentElem e)
    (hp : IsPrimitiveIdempotent (Ideal.Quotient.mk (Ring.jacobson A) e)) :
    IsLocalRing he.Corner := by
  have : IsLocalRing (he.map (Ideal.Quotient.mk (Ring.jacobson A))).Corner := hp.isLocalRing_corner
  have : Nontrivial (he.Corner ⧸ Ring.jacobson he.Corner) :=
    he.cornerQuotientJacobsonEquiv.symm.injective.nontrivial
  have : IsLocalRing (he.Corner ⧸ Ring.jacobson he.Corner) := IsLocalRing.of_surjective'
    he.cornerQuotientJacobsonEquiv.symm.toRingHom he.cornerQuotientJacobsonEquiv.symm.surjective
  exact (Ideal.Quotient.mk (Ring.jacobson he.Corner)).domain_isLocalRing

end IsIdempotentElem
