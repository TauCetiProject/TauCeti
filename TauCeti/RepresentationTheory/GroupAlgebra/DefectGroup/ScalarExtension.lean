/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Center
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Scalar extension of Brauer projections, defect groups and the principal block

Let `f : R →+* S` be a homomorphism of commutative semirings, for instance a field extension
`k ⊆ k'`, and `mapRingHom G f : R[G] → S[G]` the induced map of group algebras. It acts on
coefficients, so it commutes with the Brauer projection `Br_P`, which keeps the coefficients on the
centralizer of `P`. When `f` is injective, `Br_P(f x) = 0` exactly when `Br_P(x) = 0`, so `x` and
`f x` have the same defect groups: the defect groups of `e ∈ R[G]` do not change under scalar
extension. In particular a block idempotent of `k[G]` whose image in `k'[G]` is still a block
idempotent has the same defect groups over `k` and over `k'`.

The augmentation also commutes with `f`, so for a field extension `k ⊆ k'` and a finite `G`, the
principal block of `k[G]`, if it stays a block of `k'[G]`, is the principal block of `k'[G]`.

This is part of the scalar extension of ModularCharactersAndBlocks §6.2. Over a field `k` that
splits `G`, the blocks of `k[G]` stay blocks over every extension; that statement needs the
central characters of §6.2 and is not proved here. Without splitting a block can split
(`TauCeti.exists_centerMapRingHom_eq_sum`).

## Main results

* `TauCeti.brauerProjection_mapRingHom`: `Br_P(f x) = f(Br_P(x))`.
* `TauCeti.brauerProjection_mapRingHom_eq_zero_iff`: for injective `f`,
  `Br_P(f x) = 0 ↔ Br_P(x) = 0`.
* `TauCeti.isDefectGroup_mapRingHom_iff`, `TauCeti.isDefectGroup_centerMapRingHom_iff`: for
  injective `f`, `P` is a defect group of `f e` exactly when it is one of `e`.
* `TauCeti.centerAugmentation_centerMapRingHom`: the augmentation of `f b` is `f` of that of `b`.
* `TauCeti.centerMapRingHom_principalBlockIdempotent_of_isBlockIdempotent`: for a field
  extension, if the image of the principal block idempotent of `k[G]` is a block idempotent of
  `k'[G]`, it is the principal block idempotent of `k'[G]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243.
-/

public section

namespace TauCeti

open MonoidAlgebra

section BrauerProjection

variable {R S G : Type*} [CommSemiring R] [CommSemiring S] [Group G] (f : R →+* S)

/-- The Brauer projection commutes with a change of coefficients: `Br_P(f x) = f(Br_P(x))`. -/
theorem brauerProjection_mapRingHom (P : Subgroup G) (x : MonoidAlgebra R G) :
    brauerProjection P (mapRingHom G f x) = mapRingHom _ f (brauerProjection P x) := by
  ext c
  simp

variable {f}

/-- For injective `f`, `Br_P(f x) = 0` exactly when `Br_P(x) = 0`. -/
theorem brauerProjection_mapRingHom_eq_zero_iff (hf : Function.Injective f) {P : Subgroup G}
    {x : MonoidAlgebra R G} :
    brauerProjection P (mapRingHom G f x) = 0 ↔ brauerProjection P x = 0 := by
  simp only [brauerProjection_eq_zero_iff, coeff_mapRingHom, map_eq_zero_iff f hf]

/-- **Defect groups are invariant under scalar extension.** For injective `f : R →+* S`, a
subgroup `P` is a defect group of `f e ∈ S[G]` exactly when it is a defect group of `e ∈ R[G]`. -/
theorem isDefectGroup_mapRingHom_iff (hf : Function.Injective f) {p : ℕ}
    {e : MonoidAlgebra R G} {P : Subgroup G} :
    IsDefectGroup S p (mapRingHom G f e) P ↔ IsDefectGroup R p e P := by
  simp only [isDefectGroup_iff, ne_eq, brauerProjection_mapRingHom_eq_zero_iff hf]

/-- **Defect groups of central elements are invariant under scalar extension.** For injective
`f : R →+* S` and `b ∈ Z(R[G])`, for instance a block idempotent whose image is again a block
idempotent, `P` is a defect group of the image of `b` in `Z(S[G])` exactly when it is a defect
group of `b`. -/
theorem isDefectGroup_centerMapRingHom_iff (hf : Function.Injective f) {p : ℕ}
    {b : Subalgebra.center R (MonoidAlgebra R G)} {P : Subgroup G} :
    IsDefectGroup S p (centerMapRingHom G f b : MonoidAlgebra S G) P ↔
      IsDefectGroup R p (b : MonoidAlgebra R G) P := by
  rw [coe_centerMapRingHom, isDefectGroup_mapRingHom_iff hf]

end BrauerProjection

section Augmentation

variable {R S G : Type*} [CommRing R] [CommRing S] [Monoid G]

/-- The augmentation commutes with a change of coefficients on the centre:
`ε(f b) = f(ε(b))`. -/
theorem centerAugmentation_centerMapRingHom (f : R →+* S)
    (b : Subalgebra.center R (MonoidAlgebra R G)) :
    centerAugmentation S G (centerMapRingHom G f b) = f (centerAugmentation R G b) := by
  rw [centerAugmentation_apply, centerAugmentation_apply, coe_centerMapRingHom,
    augmentation_mapRingHom]

variable {k k' : Type*} [Field k] [Field k'] [Finite G]

/-- **The principal block under scalar extension.** For a field extension `f : k →+* k'`, if the
image of the principal block idempotent of `k[G]` is a block idempotent of `k'[G]`, then it is
the principal block idempotent of `k'[G]`: its augmentation is `f 1 = 1`. -/
theorem centerMapRingHom_principalBlockIdempotent_of_isBlockIdempotent (f : k →+* k')
    (h : IsBlockIdempotent (centerMapRingHom G f (principalBlockIdempotent k G))) :
    centerMapRingHom G f (principalBlockIdempotent k G) = principalBlockIdempotent k' G := by
  rw [h.eq_principalBlockIdempotent_iff, centerAugmentation_centerMapRingHom,
    centerAugmentation_principalBlockIdempotent, map_one]
  exact one_ne_zero

/-- **Non-principal blocks under scalar extension.** For a ring homomorphism `f : k →+* k'`, the
image of a block idempotent of `k[G]` other than the principal one has augmentation `0`, so it
is a sum of non-principal blocks of `k'[G]`. -/
theorem centerAugmentation_centerMapRingHom_eq_zero (f : k →+* k')
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (hne : b ≠ principalBlockIdempotent k G) :
    centerAugmentation k' G (centerMapRingHom G f b) = 0 := by
  rw [centerAugmentation_centerMapRingHom, hb.centerAugmentation_eq_zero hne, map_zero]

end Augmentation

end TauCeti
