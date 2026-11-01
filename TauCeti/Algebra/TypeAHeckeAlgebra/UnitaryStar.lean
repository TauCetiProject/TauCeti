/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import TauCeti.Algebra.Star.Unitary
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement

/-!
# The unit-circle involution on the infinite type-A Hecke algebra

For a unitary unit parameter `q` in a commutative star ring, so `star q = q⁻¹` (for example a
complex number of modulus one), the type-A Hecke algebra has an involution sending every
generator `T i` to its inverse `T i - (q - q⁻¹)` and conjugating scalars. The construction
descends to the relation quotient: the inverses satisfy the quadratic relation with the
conjugated parameter `q⁻¹ - q`, and the reversed braid and distant-commutation relations, in
the opposite algebra.

In this fiber every generator, every rescaled generator `q • T i`, and the image of every braid
are unitary. Finite stages are invariant under the involution, and strand shifts, the
complement automorphism and the index/sign characters commute with it. This is the algebraic
star structure on which positive traces at unit-circle parameters are stated; no positivity or
C*-completion is asserted.

The real-parameter involution of `TauCeti.Algebra.TypeAHeckeAlgebra.Star`, in which the
generators are self-adjoint, is a different structure on a different parameter fiber. The two
fibers meet only where `q = q⁻¹`; there `T i⁻¹ = T i`, so both involutions fix the generators
and agree. To keep the two APIs apart, the declarations here live in the namespace
`TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle`.

## Main definitions and results

* `UnitCircle.instStarRing`: the unit-circle star ring structure, for `Fact (q ∈ unitary R)`.
* `UnitCircle.star_T`: the involution sends `T i` to its inverse.
* `UnitCircle.T_mem_unitary`, `UnitCircle.braidHom_mem_unitary`: generators and braid images
  are unitary.
* `UnitCircle.map_star_iff`: the star-algebra universal property, in terms of unitary images
  of the generators.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4 and 11.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988),
  349–383, Section 3 (the unit-circle parameters).
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle

open MulOpposite

variable {R : Type*} [CommRing R] {q : Rˣ} [StarRing R] [hq : Fact ((q : R) ∈ unitary R)]

/-- The conjugate-linear map sending each generator to its inverse, bundled as a ring
homomorphism into the opposite algebra. The target algebra structure is twisted by scalar
conjugation only during construction. -/
private def conjugateInverse :
    InfiniteTypeAHeckeAlgebra R q →+* (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ := by
  letI : Algebra R (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
    Algebra.compHom _ (starRingEnd R)
  exact (lift (fun i ↦ op (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q))
    (fun i ↦ unop_injective <| by
      simp only [unop_mul, unop_op, unop_add, unop_one, Algebra.smul_def,
        Algebra.compHom_algebraMap_apply, starRingEnd_apply, MulOpposite.algebraMap_apply,
        Units.star_sub_inv_of_mem_unitary hq.out]
      rw [val_inv_unitT_mul_self, neg_sub, Algebra.smul_def, Algebra.commutes])
    (fun i ↦ unop_injective <| by
      simpa only [unop_mul, unop_op, map_mul, complementEquiv_T_eq_neg_inv, neg_mul, mul_neg,
        neg_neg, neg_inj, mul_assoc] using congrArg (complementEquiv q) (T_braid (q := q) i))
    (fun h ↦ unop_injective <| by
      simpa only [unop_mul, unop_op, complementEquiv_T_eq_neg_inv, neg_mul_neg] using
        ((commute_T (q := q) (Or.inl h)).map (complementEquiv q)).eq.symm)).toRingHom

private theorem conjugateInverse_T (i : ℕ) :
    conjugateInverse (T q i) = op (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) := by
  simp [conjugateInverse]

private theorem conjugateInverse_algebraMap (r : R) :
    conjugateInverse (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) =
      op (algebraMap R _ (star r)) := by
  simp [conjugateInverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateInverse_involutive (x : InfiniteTypeAHeckeAlgebra R q) :
    unop (conjugateInverse (unop (conjugateInverse x))) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T q)) := by simp [adjoin_range_T]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [conjugateInverse_T, conjugateInverse_algebraMap,
      Units.star_eq_inv_of_mem_unitary hq.out, Units.star_inv_eq_of_mem_unitary hq.out]
    abel
  | algebraMap r => simp [conjugateInverse_algebraMap]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy => simp [map_mul, hx, hy]

/-- The unit-circle star ring structure: each generator is sent to its inverse and scalars are
conjugated. Requires `Fact (q ∈ unitary R)`, i.e. a unitary (e.g. modulus-one) parameter. -/
@[no_expose]
instance instStarRing : StarRing (InfiniteTypeAHeckeAlgebra R q) where
  star x := unop (conjugateInverse x)
  star_involutive := conjugateInverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- In the unit-circle convention the adjoint of a generator is its inverse. -/
@[simp]
theorem star_T (i : ℕ) :
    star (T q i) = (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) :=
  congrArg unop (conjugateInverse_T (q := q) i)

private theorem star_algebraMap (r : R) :
    star (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) = algebraMap R _ (star r) :=
  congrArg unop (conjugateInverse_algebraMap r)

/-- The unit-circle involution is conjugate-linear over the coefficient ring. -/
instance instStarModule : StarModule R (InfiniteTypeAHeckeAlgebra R q) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

/-- The adjoint of the inverse of a generator is the generator. -/
theorem star_val_inv_unitT (i : ℕ) :
    star (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) = T q i := by
  rw [← star_T, star_star]

/-- Every generator is unitary in the unit-circle convention. -/
theorem T_mem_unitary (i : ℕ) : T q i ∈ unitary (InfiniteTypeAHeckeAlgebra R q) :=
  Unitary.mem_iff.mpr ⟨by rw [star_T, ← val_unitT (q := q) i, Units.inv_mul],
    by rw [star_T, ← val_unitT (q := q) i, Units.mul_inv]⟩

/-- In the `g i = q • T i` convention, the rescaled generators are unitary as well. -/
theorem smul_T_mem_unitary (i : ℕ) :
    (q : R) • T q i ∈ unitary (InfiniteTypeAHeckeAlgebra R q) :=
  Unitary.smul_mem_of_mem hq.out (T_mem_unitary i)

/-- The braid representation is unitary in the unit-circle convention: every braid on `n`
strands is sent to a unitary element. -/
theorem braidHom_mem_unitary {n : ℕ} (b : BraidGroup n) :
    (braidHom R q n b : InfiniteTypeAHeckeAlgebra R q) ∈
      unitary (InfiniteTypeAHeckeAlgebra R q) := by
  have h : braidHom R q n b ∈ (unitarySubgroup (InfiniteTypeAHeckeAlgebra R q)ˣ) := by
    induction b using BraidGroup.sigma_induction_on with
    | sigma i =>
      rw [braidHom_sigma, mem_unitarySubgroup_iff, Units.unitary_eq, Submonoid.mem_comap,
        Units.coeHom_apply, val_unitT]
      exact T_mem_unitary (i : ℕ)
    | one => simp [one_mem]
    | mul b b' hb hb' => simpa only [map_mul] using mul_mem hb hb'
    | inv b hb => simpa only [map_inv] using inv_mem hb
  rw [mem_unitarySubgroup_iff, Units.unitary_eq] at h
  exact h

/-- The adjoint of the image of a braid is its inverse, the image of the inverse braid. -/
@[simp]
theorem star_braidHom {n : ℕ} (b : BraidGroup n) :
    star (braidHom R q n b : InfiniteTypeAHeckeAlgebra R q) = ↑(braidHom R q n b)⁻¹ :=
  Units.star_eq_inv_of_mem_unitary (braidHom_mem_unitary b)

section UniversalProperty

variable {A : Type*} [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map out of the unit-circle Hecke algebra preserves star exactly when its
generator images are unitary. Thus its presentation also has the expected universal property
as a star algebra. -/
theorem map_star_iff {F : InfiniteTypeAHeckeAlgebra R q →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, F (T q i) ∈ unitary A := by
  constructor
  · intro h i
    exact Unitary.map_mem (F := InfiniteTypeAHeckeAlgebra R q →⋆ₐ[R] A)
      { F with map_star' := h } (T_mem_unitary i)
  · intro h x
    have hx : x ∈ Algebra.adjoin R (Set.range (T q)) := by simp [adjoin_range_T]
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hu := Units.inv_eq_of_mul_eq_one_left
        (u := Units.map (F : InfiniteTypeAHeckeAlgebra R q →* A) (unitT q i))
        (a := star (F (T q i))) (by simpa using Unitary.star_mul_self_of_mem (h i))
      simpa using hu
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y _ _ hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [star_mul, map_mul, hx, hy]

end UniversalProperty

/-- Every finite stage is invariant under the unit-circle involution. -/
@[simp]
theorem star_mem_stage_iff {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} :
    star x ∈ stage R q n ↔ x ∈ stage R q n := by
  have h : stage R q n ≤ star (stage R q n) := stage_le_iff.mpr fun i hi ↦ by
    rw [Subalgebra.mem_star_iff, star_T, val_inv_unitT]
    exact sub_mem (T_mem_stage hi) (Subalgebra.algebraMap_mem _ _)
  exact ⟨fun hx ↦ by simpa only [Subalgebra.mem_star_iff, star_star] using h hx,
    fun hx ↦ (Subalgebra.mem_star_iff _ _).mp (h hx)⟩

/-- Shifting all generator labels commutes with the unit-circle involution. -/
@[simp]
theorem shift_star (k : ℕ) (x : InfiniteTypeAHeckeAlgebra R q) :
    shift R q k (star x) = star (shift R q k x) :=
  map_star_iff.mpr (fun i ↦ by simpa using T_mem_unitary (i + k)) x

/-- The complement automorphism `T i ↦ -T i⁻¹` commutes with the unit-circle involution. -/
@[simp]
theorem complementEquiv_star (x : InfiniteTypeAHeckeAlgebra R q) :
    complementEquiv q (star x) = star (complementEquiv q x) :=
  map_star_iff (F := (complementEquiv q).toAlgHom) |>.mpr (fun i ↦ by
    simpa only [AlgEquiv.toAlgHom_apply, complementEquiv_T_eq_neg_inv, ← star_T,
      Unitary.coe_neg, Unitary.coe_star] using
      (-star ⟨T q i, T_mem_unitary i⟩ : unitary (InfiniteTypeAHeckeAlgebra R q)).prop) x

/-- The scalar character sending every generator to `q` preserves the unit-circle involution. -/
@[simp]
theorem indexCharacter_star (x : InfiniteTypeAHeckeAlgebra R q) :
    indexCharacter R q (star x) = star (indexCharacter R q x) :=
  map_star_iff.mpr (fun i ↦ by simpa using hq.out) x

/-- The scalar character sending every generator to `-q⁻¹` preserves the unit-circle
involution. -/
@[simp]
theorem signCharacter_star (x : InfiniteTypeAHeckeAlgebra R q) :
    signCharacter R q (star x) = star (signCharacter R q x) :=
  map_star_iff.mpr (fun i ↦ by
    simpa only [signCharacter_T, ← Units.star_eq_inv_of_mem_unitary hq.out, Unitary.coe_neg,
      Unitary.coe_star] using
      (-star ⟨(q : R), hq.out⟩ : unitary R).prop) x

end TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle
