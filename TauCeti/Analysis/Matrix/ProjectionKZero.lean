/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.MurrayVonNeumann
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

import TauCeti.RingTheory.GrothendieckRing

/-!
# The projection monoid and `K₀` of `ℝ` and `ℂ`

Over `𝕜 = ℝ` or `ℂ`, matrix projections of any sizes are Murray–von Neumann equivalent exactly
when they have the same rank (`Matrix.isMurrayVonNeumannEquivalent_iff_rank_eq`). The rank
therefore identifies the projection monoid `V(𝕜)` with `ℕ`, and its Grothendieck group, the
projection `K₀`-group of `𝕜`, with `ℤ`. Under these identifications the class of the identity
matrix of size `n` is `n`.

## Main definitions

* `TauCeti.ProjectionMonoid.rankAddEquiv`: `V(𝕜) ≃+ ℕ`, sending the class of a matrix projection
  to its rank, with inverse `n ↦ [1ₙ]`.
* `TauCeti.ProjectionKZero.rankAddEquiv`: `K₀(𝕜) ≃+ ℤ`, the induced isomorphism of Grothendieck
  groups.

## Main statements

* `TauCeti.ProjectionMonoid.rankAddEquiv_mk` and `TauCeti.ProjectionKZero.rankAddEquiv_of_mk`: the
  isomorphisms send the class of `p` to the rank of `p`.
* `TauCeti.ProjectionKZero.rankAddEquiv_of_mk_one` and
  `TauCeti.ProjectionKZero.rankAddEquiv_symm_natCast`: the class of the identity matrix of size `n`
  corresponds to `n`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definitions 5.1.1, 5.1.2 and 5.3.1.
-/

public section

open Matrix Algebra

namespace TauCeti

variable (𝕜 : Type*) [RCLike 𝕜] {m : Type*} [Fintype m]

namespace ProjectionMonoid

/-- The rank of a representative, as a function on `V(𝕜)`. -/
private noncomputable def rankFun : ProjectionMonoid 𝕜 → ℕ :=
  lift (fun p _ ↦ p.rank) fun _ _ h ↦ h.rank_eq

private theorem rankFun_mk {p : Matrix m m 𝕜} (hp : IsStarProjection p) :
    rankFun 𝕜 (mk p hp) = p.rank := by
  rw [rankFun, lift_mk_of_equiv _ _ hp (Fintype.equivFin m)]
  exact (hp.isMurrayVonNeumannEquivalent_reindex _).rank_eq.symm

/-- **The projection monoid of `ℝ` or `ℂ` is `ℕ`.** Sending the class of a matrix projection to its
rank is an isomorphism `V(𝕜) ≃+ ℕ`, with inverse `n ↦ [1ₙ]`. -/
noncomputable def rankAddEquiv : ProjectionMonoid 𝕜 ≃+ ℕ where
  toFun := rankFun 𝕜
  invFun n := mk (1 : Matrix (Fin n) (Fin n) 𝕜) (.one _)
  left_inv x := by
    induction x using ind with
    | mk n p hp =>
      rw [rankFun_mk, mk_eq_mk_iff]
      exact (hp.isMurrayVonNeumannEquivalent_one rfl).symm
  right_inv n := by
    rw [rankFun_mk, rank_one, Fintype.card_fin]
  map_add' x y := by
    induction x using ind with | mk k p hp => ?_
    induction y using ind with | mk l q hq => ?_
    rw [← mk_fromBlocks, rankFun_mk, rankFun_mk, rankFun_mk,
      ((hp.isMurrayVonNeumannEquivalent_one rfl).fromBlocks
        (hq.isMurrayVonNeumannEquivalent_one rfl)).rank_eq]
    simp [fromBlocks_one, rank_one]

/-- The isomorphism `V(𝕜) ≃+ ℕ` sends the class of a matrix projection to its rank. -/
@[simp]
theorem rankAddEquiv_mk {p : Matrix m m 𝕜} (hp : IsStarProjection p) :
    rankAddEquiv 𝕜 (mk p hp) = p.rank :=
  rankFun_mk 𝕜 hp

/-- The inverse of `V(𝕜) ≃+ ℕ` sends `n` to the class of the identity matrix of size `n`. -/
@[simp]
theorem rankAddEquiv_symm_apply (n : ℕ) :
    (rankAddEquiv 𝕜).symm n = mk (1 : Matrix (Fin n) (Fin n) 𝕜) (.one _) :=
  (rfl)

end ProjectionMonoid

namespace ProjectionKZero

/-- **The projection `K₀`-group of `ℝ` or `ℂ` is `ℤ`.** The Grothendieck group of
`TauCeti.ProjectionMonoid.rankAddEquiv`, sending `[p] - [q]` to `rank p - rank q`. -/
noncomputable def rankAddEquiv : ProjectionKZero 𝕜 ≃+ ℤ :=
  GrothendieckAddGroup.addEquivInt (ProjectionMonoid.rankAddEquiv 𝕜)

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, so the left-hand side is not in simp normal form.
/-- The isomorphism `K₀(𝕜) ≃+ ℤ` sends the class of a matrix projection to its rank. -/
theorem rankAddEquiv_of_mk {p : Matrix m m 𝕜} (hp : IsStarProjection p) :
    rankAddEquiv 𝕜 (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = p.rank := by
  rw [rankAddEquiv, GrothendieckAddGroup.addEquivInt_of, ProjectionMonoid.rankAddEquiv_mk]

/-- The isomorphism `K₀(𝕜) ≃+ ℤ` sends the class of the identity matrix of size `n` to `n`. -/
theorem rankAddEquiv_of_mk_one (n : ℕ) :
    rankAddEquiv 𝕜 (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin n) (Fin n) 𝕜) (.one _))) = n := by
  rw [rankAddEquiv_of_mk, rank_one, Fintype.card_fin]

/-- The inverse of `K₀(𝕜) ≃+ ℤ` sends `n` to the class of the identity matrix of size `n`. -/
@[simp]
theorem rankAddEquiv_symm_natCast (n : ℕ) :
    (rankAddEquiv 𝕜).symm n =
      GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin n) (Fin n) 𝕜) (.one _)) :=
  GrothendieckAddGroup.addEquivInt_symm_natCast _ n

end ProjectionKZero

end TauCeti
