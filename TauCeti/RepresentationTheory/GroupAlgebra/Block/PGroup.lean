/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.LocalRing
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The single block of a `p`-group

Let `R` be a local ring in which the prime `p` is not a unit, for instance a field of
characteristic `p`, and `G` a finite `p`-group. The group algebra `R[G]` is then a local ring
(`TauCeti.MonoidAlgebra.isLocalRing_iff_isPGroup`), so its only idempotents are `0` and `1`, and
`1` is its only block idempotent.

## Main results

* `TauCeti.isBlockIdempotent_one_of_isPGroup`: `1` is a block idempotent of `R[G]`.
* `TauCeti.isBlockIdempotent_iff_eq_one_of_isPGroup`: it is the only one.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
  [Finite G]

/-- **The group algebra of a `p`-group has the single block `1`**: for a local ring `R` in which
`p` is not a unit and a finite `p`-group `G`, `1` is a block idempotent of `R[G]`. -/
theorem isBlockIdempotent_one_of_isPGroup (hp : ¬IsUnit (p : R)) (hG : IsPGroup p G) :
    IsBlockIdempotent (1 : Subalgebra.center R (MonoidAlgebra R G)) := by
  have := (MonoidAlgebra.isLocalRing_iff_isPGroup hp).2 hG
  refine isPrimitiveIdempotent_one_iff.2 fun f hf ↦ ?_
  rcases (hf.map (Subalgebra.center R (MonoidAlgebra R G)).val).eq_zero_or_eq_one_of_isLocalRing
    with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- **`1` is the only block idempotent of the group algebra of a `p`-group**, for a local ring `R`
in which `p` is not a unit and a finite `p`-group `G`. -/
theorem isBlockIdempotent_iff_eq_one_of_isPGroup (hp : ¬IsUnit (p : R)) (hG : IsPGroup p G)
    {b : Subalgebra.center R (MonoidAlgebra R G)} : IsBlockIdempotent b ↔ b = 1 := by
  refine ⟨fun hb ↦ ?_, fun h ↦ h ▸ isBlockIdempotent_one_of_isPGroup hp hG⟩
  exact (isBlockIdempotent_one_of_isPGroup hp hG).eq_zero_or_eq hb.isIdempotentElem (one_mul b)
    (mul_one b) |>.resolve_left hb.ne_zero

end TauCeti
