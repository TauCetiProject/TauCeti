/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.SelfAdjoint
public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# The real-parameter involution on the infinite type-A Hecke algebra

For a star-fixed unit parameter in a commutative star ring, the type-A Hecke algebra has an
involution fixing every generator and conjugating scalars. In particular, real nonzero parameters
give complex star algebras. The construction descends to the relation quotient by checking the
quadratic relation and the reversed braid and distant-commutation relations in the opposite
algebra. It does not put a star operation on the free generators' inverses.

The finite stages are invariant under this involution, as are strand shifts. This supplies the
algebraic star structure needed to discuss positive traces and self-adjoint elements; no positivity
or C*-completion is asserted. The unit-circle convention, in which the generators are unitary
rather than self-adjoint, is a different involution and is not constructed here.

The conjugate-opposite construction follows the same `Algebra.compHom` strategy as
`TauCeti.QuantumGroups.UqSl2.Star`, without importing its quantum-group presentation.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4 and 11.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open MulOpposite

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
variable [hq : Fact (IsSelfAdjoint (q : R))]

private theorem star_inv_parameter : star (↑q⁻¹ : R) = (↑q⁻¹ : R) := by
  have hu : star q = q := Units.ext hq.out.star_eq
  rw [← Units.coe_star_inv, hu]

private theorem star_parameter_sub_inv :
    star ((q : R) - ↑q⁻¹) = (q : R) - ↑q⁻¹ := by
  simp [star_sub, hq.out.star_eq, star_inv_parameter]

/-- The conjugate-linear reversal map, bundled as a ring homomorphism into the opposite algebra.
The target algebra structure is twisted by scalar conjugation only during construction. -/
private def conjugateReverse :
    InfiniteTypeAHeckeAlgebra R q →+* (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ := by
  letI : Algebra R (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
    Algebra.compHom _ (starRingEnd R)
  exact (lift (fun i ↦ op (T q i))
    (fun i ↦ unop_injective <| by
      simp only [unop_mul, unop_op, unop_add, unop_one, Algebra.smul_def,
        Algebra.compHom_algebraMap_apply, starRingEnd_apply, MulOpposite.algebraMap_apply,
        star_parameter_sub_inv]
      rw [T_mul_self, Algebra.smul_def, Algebra.commutes])
    (fun i ↦ unop_injective <| by simpa [mul_assoc] using T_braid (q := q) i)
    (fun {_ _} h ↦ unop_injective <| (commute_T (q := q) (.inl h)).eq.symm)).toRingHom

private theorem conjugateReverse_T (i : ℕ) :
    conjugateReverse (T q i) = op (T q i) := by
  simp [conjugateReverse]

private theorem conjugateReverse_algebraMap (r : R) :
    conjugateReverse (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) =
      op (algebraMap R _ (star r)) := by
  simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateReverse_involutive (x : InfiniteTypeAHeckeAlgebra R q) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T q)) := by simp [adjoin_range_T]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [conjugateReverse_T]
  | algebraMap r => simp [conjugateReverse_algebraMap]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy => simp [map_mul, hx, hy]

/-- The real-parameter star ring structure: generators are self-adjoint and scalars are
conjugated. The `Fact` hypothesis specifies the parameter fiber. -/
@[no_expose]
instance instStarRing : StarRing (InfiniteTypeAHeckeAlgebra R q) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- Every generator is self-adjoint in the real-parameter convention. -/
@[simp]
theorem star_T (i : ℕ) : star (T q i) = T q i :=
  congrArg unop (conjugateReverse_T (q := q) i)

private theorem star_algebraMap (r : R) :
    star (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) = algebraMap R _ (star r) :=
  congrArg unop (conjugateReverse_algebraMap r)

/-- The real-parameter involution is conjugate-linear over the coefficient ring. -/
instance instStarModule : StarModule R (InfiniteTypeAHeckeAlgebra R q) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

section UniversalProperty

variable {A : Type*} [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map out of the real-parameter Hecke algebra preserves star exactly when its
generator images are self-adjoint. Thus its presentation also has the expected universal
property as a star algebra. -/
theorem map_star_iff {F : InfiniteTypeAHeckeAlgebra R q →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, IsSelfAdjoint (F (T q i)) := by
  constructor
  · intro h i
    simpa only [IsSelfAdjoint, star_T] using (h (T q i)).symm
  · intro h x
    have hx : x ∈ Algebra.adjoin R (Set.range (T q)) := by simp [adjoin_range_T]
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [star_T, (h i).star_eq]
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y _ _ hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [star_mul, map_mul, hx, hy]

end UniversalProperty

/-- Every finite stage is invariant under the real-parameter involution. -/
@[simp]
theorem star_mem_stage_iff {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} :
    star x ∈ stage R q n ↔ x ∈ stage R q n := by
  have h : stage R q n ≤ star (stage R q n) := stage_le_iff.mpr fun i hi ↦ by
    simpa only [Subalgebra.mem_star_iff, star_T] using T_mem_stage (q := q) hi
  exact ⟨fun hx ↦ by simpa only [Subalgebra.mem_star_iff, star_star] using h hx,
    fun hx ↦ (Subalgebra.mem_star_iff _ _).mp (h hx)⟩

/-- Shifting all generator labels preserves the involution, so the shifted tail is a star
subalgebra with its actual generator labels. -/
@[simp]
theorem shift_star (k : ℕ) (x : InfiniteTypeAHeckeAlgebra R q) :
    shift R q k (star x) = star (shift R q k x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint]) x

/-- The scalar character sending every generator to `q` preserves the involution. -/
@[simp]
theorem indexCharacter_star (x : InfiniteTypeAHeckeAlgebra R q) :
    indexCharacter R q (star x) = star (indexCharacter R q x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint, hq.out.star_eq]) x

/-- The scalar character sending every generator to `-q⁻¹` preserves the involution. -/
@[simp]
theorem signCharacter_star (x : InfiniteTypeAHeckeAlgebra R q) :
    signCharacter R q (star x) = star (signCharacter R q x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint, star_inv_parameter]) x

end TauCeti.InfiniteTypeAHeckeAlgebra
