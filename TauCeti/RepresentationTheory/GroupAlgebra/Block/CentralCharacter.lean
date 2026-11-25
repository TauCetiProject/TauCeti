/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.Idempotents.Primitive.AlgHom

/-!
# Central characters of blocks

Let `k` be a field, `G` a finite group (or monoid) and `e_B` a block idempotent of `k[G]`, a
primitive idempotent of the centre `Z(k[G])`. The centre is a finite-dimensional commutative
`k`-algebra, hence Artinian (`TauCeti.isArtinianRing_center_monoidAlgebra`), so the block's part
`Z(k[G]) e_B` of the centre is a local ring (`TauCeti.IsPrimitiveIdempotent.exists_mul_mul_eq_or`).

A **central character** of `B` is a `k`-algebra homomorphism `λ_B : Z(k[G]) → k` with
`λ_B(e_B) = 1`. A block has at most one, over every field
(`TauCeti.IsPrimitiveIdempotent.algHom_ext`, applied to `e_B`). Over an algebraically closed
field a central character exists (`IsIdempotentElem.exists_algHom_apply_eq_one`); this file names
it `TauCeti.IsBlockIdempotent.centralCharacter`. It vanishes on every central element orthogonal to
`e_B`, in particular on the other block idempotents. The augmentation is the central character of
the principal block, over every field (`TauCeti.eq_centerAugmentation`).

## Main definitions

* `TauCeti.IsBlockIdempotent.centralCharacter`: over an algebraically closed field, the central
  character `λ_B : Z(k[G]) →ₐ[k] k` of a block.

## Main results

* `TauCeti.IsBlockIdempotent.centralCharacter_self`,
  `TauCeti.IsBlockIdempotent.centralCharacter_eq_zero_of_mul_eq_zero`: `λ_B(e_B) = 1`, and
  `λ_B(e) = 0` for every `e` with `e_B e = 0`.
* `TauCeti.IsBlockIdempotent.eq_centralCharacter_iff`: `λ_B` is the only `k`-algebra
  homomorphism `Z(k[G]) → k` taking the value `1` at `e_B`.
* `TauCeti.eq_centerAugmentation`: a `k`-algebra homomorphism `Z(k[G]) → k` taking the value `1`
  at the principal block idempotent is the augmentation.
* `TauCeti.IsBlockIdempotent.centralCharacter_principalBlockIdempotent`: over an algebraically
  closed field, the central character of the principal block is the augmentation.

## References

* A. Martínez, *Modular representation theory of finite groups*, pp. 9–10.
* B. Sambale, *Blocks of Finite Groups and Their Invariants*, Lecture Notes in Mathematics 2127,
  Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

variable {k G : Type*} [Field k] [Monoid G] [Finite G]

/-- **The augmentation is the central character of the principal block.** Over every field, a
`k`-algebra homomorphism `Z(k[G]) → k` taking the value `1` at the principal block idempotent is
the augmentation. -/
theorem eq_centerAugmentation {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    (hφ : φ (principalBlockIdempotent k G) = 1) : φ = centerAugmentation k G :=
  (isBlockIdempotent_principalBlockIdempotent k G).algHom_ext hφ
    (centerAugmentation_principalBlockIdempotent k G)

namespace IsBlockIdempotent

variable [IsAlgClosed k] {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- The **central character** `λ_B : Z(k[G]) → k` of a block `B` of `k[G]`, over an
algebraically closed field `k`: the unique `k`-algebra homomorphism with `λ_B(e_B) = 1`. -/
noncomputable def centralCharacter (hb : IsBlockIdempotent b) :
    Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  (hb.isIdempotentElem.exists_algHom_apply_eq_one (K := k) hb.ne_zero).choose

/-- The central character of `B` takes the value `1` at `e_B`. -/
@[simp]
theorem centralCharacter_self (hb : IsBlockIdempotent b) : hb.centralCharacter b = 1 :=
  (hb.isIdempotentElem.exists_algHom_apply_eq_one (K := k) hb.ne_zero).choose_spec

/-- **Characterization of the central character.** Over an algebraically closed field, the
central character of `B` is the only `k`-algebra homomorphism `Z(k[G]) → k` taking the value `1`
at `e_B`. -/
theorem eq_centralCharacter_iff (hb : IsBlockIdempotent b)
    (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    φ = hb.centralCharacter ↔ φ b = 1 :=
  ⟨fun h ↦ h ▸ hb.centralCharacter_self, fun h ↦ hb.algHom_ext h hb.centralCharacter_self⟩

/-- The central character of `B` vanishes at every central `e` with `e_B e = 0`, in particular
at the block idempotents of the other blocks. -/
theorem centralCharacter_eq_zero_of_mul_eq_zero (hb : IsBlockIdempotent b)
    {e : Subalgebra.center k (MonoidAlgebra k G)} (h : b * e = 0) :
    hb.centralCharacter e = 0 := by
  have := congrArg hb.centralCharacter h
  rwa [map_mul, centralCharacter_self, one_mul, map_zero] at this

/-- Over an algebraically closed field, the central character of the principal block is the
augmentation. -/
@[simp]
theorem centralCharacter_principalBlockIdempotent :
    (isBlockIdempotent_principalBlockIdempotent k G).centralCharacter = centerAugmentation k G :=
  eq_centerAugmentation (centralCharacter_self _)

end IsBlockIdempotent

end TauCeti
