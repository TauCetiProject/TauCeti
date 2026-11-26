/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Center
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Scalar extension of defect groups

Let `f : R →+* S` be an injective homomorphism of commutative semirings, for instance a field
extension `k ⊆ k'`, and `mapRingHom G f : R[G] → S[G]` the induced map of group algebras. It
commutes with the Brauer projection (`TauCeti.brauerProjection_mapRingHom`), and
`Br_P(f x) = 0` exactly when `Br_P(x) = 0` (`TauCeti.brauerProjection_mapRingHom_eq_zero_iff`), so
`x` and `f x` have the same defect groups: the defect groups of `e ∈ R[G]` do not change under
scalar extension. In particular a block idempotent of `k[G]` whose image in `k'[G]` is still a
block idempotent has the same defect groups over `k` and over `k'`.

Over a field `k` that splits `G`, the blocks of `k[G]` stay blocks over every extension; this
needs central characters and is not proved here. In general the image of a block is only a sum of
blocks (`TauCeti.exists_centerMapRingHom_eq_sum`).

## Main results

* `TauCeti.isDefectGroup_mapRingHom_iff`, `TauCeti.isDefectGroup_centerMapRingHom_iff`: for
  injective `f`, `P` is a defect group of `f e` exactly when it is one of `e`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R S G : Type*} [CommSemiring R] [CommSemiring S] [Group G] {f : R →+* S}

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

end TauCeti
