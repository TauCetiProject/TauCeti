/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Sz.-Nagy's projection intertwiner and unitization partial-isometry transfer

For idempotents `p` and `q` in a ring `R`, Sz.-Nagy's intertwiner
`projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` satisfies `z * p = q * z`, and
`1 - (p - q) ^ 2` commutes with both `p` and `q`. When `R` is a star ring and `p`, `q` are star
projections, `star z * z = z * star z = 1 - (p - q) ^ 2` and `z + star z = 2 * (1 - (p - q) ^ 2)`.

For a non-unital star `R`-algebra `B`, when `u` is unitary in `Unitization R B` and conjugates a
star projection `p : B` to `q : B`, `u.mulInr p = u.fst • p + u.snd * p` is a partial isometry in
`B` with initial projection `p` and final projection `q`.

## Main declarations

* `TauCeti.projectionIntertwiner`: the intertwiner `q * p + (1 - q) * (1 - p)`.
* `TauCeti.projectionIntertwiner_mul_eq_mul`, `TauCeti.star_projectionIntertwiner_mul_self`,
  `TauCeti.projectionIntertwiner_mul_star_self`, `TauCeti.projectionIntertwiner_add_star`:
  intertwining and star-ring identities.
* `Unitization.star_mulInr_mul_self`, `Unitization.mulInr_mul_star_self`,
  `Unitization.isPartialIsometry_mulInr`,
  `IsStarProjection.exists_isPartialIsometry_of_unitization_unitary_conj`: partial-isometry transfer
  from `Unitization R B` to `B`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Proposition 4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Propositions 2.2.4 and
  2.2.6.
-/

public section

namespace TauCeti

section IntertwinerAlgebra

variable {R : Type*} [Ring R]

/-- Sz.-Nagy's intertwiner `q * p + (1 - q) * (1 - p)` between idempotents `p` and `q`. -/
def projectionIntertwiner (p q : R) : R :=
  q * p + (1 - q) * (1 - p)

/-- Unfold `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_def (p q : R) :
    projectionIntertwiner p q = q * p + (1 - q) * (1 - p) := (rfl)

/-- At equal idempotents `p = q`, the intertwiner is `1`. -/
@[simp]
theorem projectionIntertwiner_self {p : R} (hp : IsIdempotentElem p) :
    projectionIntertwiner p p = 1 := by
  rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]

/-- Right multiplication by an idempotent `p` reduces `projectionIntertwiner p q * p` to `q * p`. -/
theorem projectionIntertwiner_mul_right {p q : R} (hp : IsIdempotentElem p) :
    projectionIntertwiner p q * p = q * p := by
  rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]

/-- Left multiplication by an idempotent `q` reduces `q * projectionIntertwiner p q` to `q * p`. -/
theorem mul_projectionIntertwiner_left {p q : R} (hq : IsIdempotentElem q) :
    q * projectionIntertwiner p q = q * p := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.eq]
  rw [projectionIntertwiner_def]; noncomm_ring [hq.eq, hqqp]

/-- `projectionIntertwiner p q` intertwines idempotents `p` and `q`: `z * p = q * z`. -/
theorem projectionIntertwiner_mul_eq_mul {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) :
    projectionIntertwiner p q * p = q * projectionIntertwiner p q := by
  rw [projectionIntertwiner_mul_right hp, mul_projectionIntertwiner_left hq]

/-- For idempotents `p` and `q`, `1 - (p - q) ^ 2` commutes with `p`. -/
theorem commute_one_sub_sub_mul_self_left {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : Commute (1 - (p - q) * (p - q)) p := by
  have hppq : p * (p * q) = p * q := by rw [← mul_assoc, hp.eq]
  rw [commute_iff_eq]; noncomm_ring [hp.eq, hq.eq, hppq]

/-- For idempotents `p` and `q`, `1 - (p - q) ^ 2` commutes with `q`. -/
theorem commute_one_sub_sub_mul_self_right {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : Commute (1 - (p - q) * (p - q)) q := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.eq]
  rw [commute_iff_eq]; noncomm_ring [hp.eq, hq.eq, hqqp]

section Star

variable [StarRing R]

/-- Taking `star` of `projectionIntertwiner p q` for self-adjoint `p`, `q` swaps `p` and `q`. -/
theorem star_projectionIntertwiner {p q : R} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def, star_add, star_mul, star_mul,
    star_sub, star_sub, star_one, hp.star_eq, hq.star_eq]

/-- For star projections `p` and `q`, `star z * z = 1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) * (p - q) := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.isIdempotentElem.eq]
  have hpqqp : p * (q * (q * p)) = p * (q * p) := by rw [hqqp]
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint, projectionIntertwiner_def,
    projectionIntertwiner_def]
  noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hqqp, hpqqp]

/-- For star projections `p` and `q`, `z * star z = 1 - (p - q) ^ 2`, so `z` is normal. -/
theorem projectionIntertwiner_mul_star_self {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) * (p - q) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint]
  have h := star_projectionIntertwiner_mul_self hq hp
  rw [star_projectionIntertwiner hq.isSelfAdjoint hp.isSelfAdjoint] at h
  rw [h]; noncomm_ring

/-- Twice `1 - (p - q) ^ 2` equals `z + star z` for `z = projectionIntertwiner p q`. -/
theorem projectionIntertwiner_add_star {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) =
      2 * (1 - (p - q) * (p - q)) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint, projectionIntertwiner_def,
    projectionIntertwiner_def]
  noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]

end Star

end IntertwinerAlgebra

end TauCeti

namespace Unitization

variable {R B : Type*} [CommSemiring R] [NonUnitalSemiring B] [Module R B]
  [StarRing R] [IsScalarTower R B B] [SMulCommClass R B B] [StarRing B] [StarModule R B]

/-- If `u` is unitary in `Unitization R B` and `p` is a star projection in `B`, the initial
projection `star v * v` of `v = u.mulInr p` in `B` is `p`. -/
theorem star_mulInr_mul_self {u : Unitization R B}
    (hu : u ∈ unitary (Unitization R B)) {p : B} (hp : IsStarProjection p) :
    star (u.mulInr p) * u.mulInr p = p := by
  apply Unitization.inr_injective (R := R)
  rw [Unitization.inr_mul, Unitization.inr_star, inr_mulInr, star_mul,
    ← Unitization.inr_star, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star u),
    Unitary.star_mul_self_of_mem hu, one_mul, ← Unitization.inr_mul, hp.isIdempotentElem.eq]

/-- If `u` in `Unitization R B` conjugates a star projection `p : B` to `q : B`, the final
projection `v * star v` of `v = u.mulInr p` in `B` is `q`. -/
theorem mulInr_mul_star_self {u : Unitization R B} {p q : B} (hp : IsStarProjection p)
    (hconj : u * (p : Unitization R B) * star u = (q : Unitization R B)) :
    u.mulInr p * star (u.mulInr p) = q := by
  apply Unitization.inr_injective (R := R)
  rw [Unitization.inr_mul, Unitization.inr_star, inr_mulInr, star_mul,
    ← Unitization.inr_star, hp.isSelfAdjoint.star_eq, mul_assoc,
    ← mul_assoc (p : Unitization R B), ← Unitization.inr_mul, hp.isIdempotentElem.eq,
    ← mul_assoc, hconj]

/-- If `u` is unitary in `Unitization R B` and `p` is a star projection in `B`, `u.mulInr p` is a
partial isometry in `B`. -/
theorem isPartialIsometry_mulInr {u : Unitization R B}
    (hu : u ∈ unitary (Unitization R B)) {p : B} (hp : IsStarProjection p) :
    TauCeti.IsPartialIsometry (u.mulInr p) := by
  rw [TauCeti.isPartialIsometry_iff, mul_assoc, star_mulInr_mul_self hu hp,
    mulInr_def, add_mul, smul_mul_assoc, mul_assoc, hp.isIdempotentElem.eq]

end Unitization

namespace IsStarProjection

/-- If a unitary `u` of `Unitization R B` conjugates a star projection `p : B` to `q : B`, then
`v = (u : Unitization R B).mulInr p` is a partial isometry in `B` with `star v * v = p` and
`v * star v = q`. -/
theorem exists_isPartialIsometry_of_unitization_unitary_conj {R B : Type*}
    [CommSemiring R] [StarRing R] [NonUnitalSemiring B] [StarRing B]
    [Module R B] [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    {p q : B} (hp : IsStarProjection p) (u : unitary (Unitization R B))
    (h : (u : Unitization R B) * (p : Unitization R B) * star (u : Unitization R B) =
      (q : Unitization R B)) :
    ∃ v : B, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q :=
  ⟨(u : Unitization R B).mulInr p, Unitization.isPartialIsometry_mulInr u.property hp,
    Unitization.star_mulInr_mul_self u.property hp, Unitization.mulInr_mul_star_self hp h⟩

end IsStarProjection
