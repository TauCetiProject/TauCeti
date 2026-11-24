/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability
public import TauCeti.RingTheory.StableRange.Commutative

/-!
# Elementary reduction over commutative rings of stable range one

Let `R` be a commutative ring of Bass stable range at most `1`
(`TauCeti.HasStableRangeLE R 1`), for instance a commutative semilocal or local ring. Surjective
stability makes every class of `K₁(R)` the class of a `1 × 1` matrix, so a class of determinant
one is trivial: `SK₁(R) = 1` and the determinant is an isomorphism `K₁(R) ≃* Rˣ`. Injective
stability then identifies the elementary subgroup in every size `n ≥ 2` with the kernel of
`GLₙ(R) → K₁(R)`, so

  `Eₙ(R) = SLₙ(R)`, the invertible matrices of determinant one,

for every finite index type. In sizes `0` and `1` both groups are trivial.

## Main results

* `TauCeti.specialAlgebraicK1_eq_bot_of_hasStableRangeLE_one`: `SK₁(R) = 1` for a commutative
  ring of stable range at most `1`.
* `TauCeti.AlgebraicK1.mk_eq_one_iff_det_eq_one_of_hasStableRangeLE_one`: over such a ring the
  class of an invertible matrix in `K₁(R)` is trivial exactly when its determinant is one.
* `TauCeti.elementarySubgroup_eq_ker_det_of_hasStableRangeLE_one`: over such a ring an invertible
  matrix is a product of elementary matrices exactly when its determinant is one.
* `TauCeti.specialAlgebraicK1_eq_bot_of_finite_maximalSpectrum` and
  `TauCeti.elementarySubgroup_eq_ker_det_of_finite_maximalSpectrum`: the same for commutative
  semilocal rings, in particular for commutative local rings.

## References

* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §4.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Lemma 1.4 and Example 1.1.1.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **`SK₁` vanishes in stable range one.** Over a commutative ring of Bass stable range at most
`1`, every class of `K₁(R)` is represented by a `1 × 1` matrix, so the determinant
`K₁(R) →* Rˣ` is injective and `SK₁(R)` is trivial. -/
theorem specialAlgebraicK1_eq_bot_of_hasStableRangeLE_one (hR : HasStableRangeLE R 1) :
    specialAlgebraicK1 R = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  obtain ⟨g, rfl⟩ := AlgebraicK1.mk_surjective hR le_rfl x
  have hg : g ∈ (GeneralLinearGroup.det : GL (Fin 1) R →* Rˣ).ker :=
    AlgebraicK1.mk_mem_specialAlgebraicK1_iff.1 hx
  rw [GeneralLinearGroup.ker_det_eq_bot_of_subsingleton, Subgroup.mem_bot] at hg
  rw [hg, map_one]

/-- In stable range one, the class of an invertible matrix in `K₁(R)` is trivial exactly when its
determinant is one, since `SK₁(R)` vanishes. -/
theorem AlgebraicK1.mk_eq_one_iff_det_eq_one_of_hasStableRangeLE_one (hR : HasStableRangeLE R 1)
    {n : ℕ} {u : GL (Fin n) R} :
    AlgebraicK1.mk R n u = 1 ↔ GeneralLinearGroup.det u = 1 := by
  rw [← AlgebraicK1.mk_mem_specialAlgebraicK1_iff,
    specialAlgebraicK1_eq_bot_of_hasStableRangeLE_one hR, Subgroup.mem_bot]

/-- **Elementary reduction in stable range one.** Over a commutative ring of Bass stable range at
most `1`, an invertible matrix of any finite size is a product of elementary matrices exactly when
its determinant is one: `E n R = SL n R`. -/
theorem elementarySubgroup_eq_ker_det_of_hasStableRangeLE_one (hR : HasStableRangeLE R 1)
    (n : Type*) [Fintype n] [DecidableEq n] :
    elementarySubgroup n R = GeneralLinearGroup.det.ker := by
  refine le_antisymm elementarySubgroup_le_ker_det fun g hg ↦ ?_
  rcases le_or_gt (Fintype.card n) 1 with hn | hn
  · -- In size at most one both groups are trivial.
    have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp hn
    rw [GeneralLinearGroup.ker_det_eq_bot_of_subsingleton, Subgroup.mem_bot] at hg
    exact hg ▸ (elementarySubgroup n R).one_mem
  · -- In size at least two, injective stability identifies `E n R` with the kernel of `GLₙ → K₁`.
    rw [← (Fintype.equivFin n).symm.map_reindexGL_elementarySubgroup]
    refine ⟨(Fintype.equivFin n).reindexGL R g, ?_, by simp⟩
    rw [← AlgebraicK1.ker_mk_eq_elementarySubgroup hR hn, SetLike.mem_coe, MonoidHom.mem_ker,
      AlgebraicK1.mk_eq_one_iff_det_eq_one_of_hasStableRangeLE_one hR, Equiv.det_reindexGL]
    exact hg

/-- **`SK₁` of a semilocal ring vanishes.** For a commutative ring with finitely many maximal
ideals, in particular a commutative local ring, `SK₁(R)` is trivial, so the determinant is an
isomorphism `K₁(R) ≃* Rˣ`. -/
theorem specialAlgebraicK1_eq_bot_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    specialAlgebraicK1 R = ⊥ :=
  specialAlgebraicK1_eq_bot_of_hasStableRangeLE_one
    (hasStableRangeLE_one_of_finite_maximalSpectrum R)

/-- Over a commutative ring with finitely many maximal ideals, in particular a commutative local
ring, an invertible matrix is a product of elementary matrices exactly when its determinant is
one. -/
theorem elementarySubgroup_eq_ker_det_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    (n : Type*) [Fintype n] [DecidableEq n] :
    elementarySubgroup n R = GeneralLinearGroup.det.ker :=
  elementarySubgroup_eq_ker_det_of_hasStableRangeLE_one
    (hasStableRangeLE_one_of_finite_maximalSpectrum R) n

end TauCeti
