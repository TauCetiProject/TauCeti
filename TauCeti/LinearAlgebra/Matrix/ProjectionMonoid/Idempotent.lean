/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Basic

/-!
# From projections to idempotents

A rectangular matrix `v` with `vᴴ * v = p` and `v * vᴴ = q` exhibits the matrix projections `p` and
`q` as equivalent idempotents, through `x = vᴴ` and `y = v`
(`Matrix.IsMurrayVonNeumannEquivalent.idempotentEquivalent`). So the class of a projection in the
projection monoid `V(R)` determines its class in the idempotent monoid of `R`, which for a ring `R`
is the monoid of isomorphism classes of finitely generated projective `R`-modules. This gives a
monoid homomorphism `TauCeti.ProjectionMonoid.toIdempotentMonoid : V(R) →+ IdempotentMonoid R`,
natural for star ring homomorphisms. Over a unital C⋆-algebra it is an isomorphism; see
`TauCeti/Analysis/CStarAlgebra/Projection/ProjectiveModule.lean`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Propositions 4.6.2 and 4.6.4.
-/

public section

open Matrix

namespace Matrix

variable {R m n : Type*} [Fintype m] [Fintype n] [NonUnitalSemiring R] [StarRing R]

/-- **Murray–von Neumann equivalence implies algebraic equivalence.** If `v` implements `p ∼ q`,
then `p = vᴴ * v` and `q = v * vᴴ` are equivalent idempotents. -/
theorem IsMurrayVonNeumannEquivalent.idempotentEquivalent {p : Matrix m m R} {q : Matrix n n R}
    (h : IsMurrayVonNeumannEquivalent p q) : IdempotentEquivalent p q := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  exact (idempotentEquivalent_iff_exists_mul_eq hp.isIdempotentElem hq.isIdempotentElem).2
    ⟨vᴴ, v, hvp, hvq⟩

end Matrix

namespace TauCeti

namespace ProjectionMonoid

variable {R S : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]
  {m : Type*} [Fintype m]

/-- The function `V(R) → IdempotentMonoid R` sending the class of a projection to its class as an
idempotent. -/
private noncomputable def toIdempotentMonoidFun : ProjectionMonoid R → IdempotentMonoid R :=
  lift (fun p hp ↦ IdempotentMonoid.mk p hp.isIdempotentElem) fun _ _ h ↦
    IdempotentMonoid.mk_eq_mk h.idempotentEquivalent

private theorem toIdempotentMonoidFun_mk {p : Matrix m m R} (hp : IsStarProjection p) :
    toIdempotentMonoidFun (mk p hp) = IdempotentMonoid.mk p hp.isIdempotentElem := by
  rw [toIdempotentMonoidFun, ← mk_reindex hp (Fintype.equivFin m), lift_mk]
  exact IdempotentMonoid.mk_eq_mk
    (hp.isMurrayVonNeumannEquivalent_reindex _).symm.idempotentEquivalent

/-- **Projections as idempotents.** The monoid homomorphism `V(R) →+ IdempotentMonoid R` sending
the class of a matrix projection to its class as an idempotent matrix. -/
noncomputable def toIdempotentMonoid : ProjectionMonoid R →+ IdempotentMonoid R where
  toFun := toIdempotentMonoidFun
  map_zero' := by
    rw [← mk_zero (m := Fin 0), toIdempotentMonoidFun_mk, IdempotentMonoid.mk_zero]
  map_add' x y := by
    induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [← mk_fromBlocks, toIdempotentMonoidFun_mk, toIdempotentMonoidFun_mk,
      toIdempotentMonoidFun_mk, IdempotentMonoid.mk_add_mk]

/-- `TauCeti.ProjectionMonoid.toIdempotentMonoid` sends the class of a projection to its class as
an idempotent. -/
@[simp]
theorem toIdempotentMonoid_mk {p : Matrix m m R} (hp : IsStarProjection p) :
    toIdempotentMonoid (mk p hp) = IdempotentMonoid.mk p hp.isIdempotentElem :=
  toIdempotentMonoidFun_mk hp

/-- An idempotent matrix `e` and a projection `p` with `e * p = p` and `p * e = e` have the same
class as idempotents: `e = p * e` and `p = e * p`. -/
theorem toIdempotentMonoid_mk_eq_mk {e p : Matrix m m R} (he : IsIdempotentElem e)
    (hp : IsStarProjection p) (hep : e * p = p) (hpe : p * e = e) :
    toIdempotentMonoid (mk p hp) = IdempotentMonoid.mk e he := by
  rw [toIdempotentMonoid_mk, IdempotentMonoid.mk_eq_mk_iff,
    idempotentEquivalent_iff_exists_mul_eq hp.isIdempotentElem he]
  exact ⟨e, p, hep, hpe⟩

/-- **Naturality.** Passing from projections to idempotents commutes with the maps induced by a
star ring homomorphism. -/
@[simp]
theorem map_toIdempotentMonoid (f : R →⋆ₙ+* S) (x : ProjectionMonoid R) :
    IdempotentMonoid.map f.toNonUnitalRingHom (toIdempotentMonoid x) =
      toIdempotentMonoid (map f x) := by
  induction x using ind with
  | mk _ p hp => simp [IdempotentMonoid.map_mk]

/-- **Naturality**, as an equality of monoid homomorphisms. -/
theorem toIdempotentMonoid_comp_map (f : R →⋆ₙ+* S) :
    toIdempotentMonoid.comp (map f) =
      (IdempotentMonoid.map f.toNonUnitalRingHom).comp toIdempotentMonoid :=
  AddMonoidHom.ext fun x ↦ (map_toIdempotentMonoid f x).symm

end ProjectionMonoid

end TauCeti
