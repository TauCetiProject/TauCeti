/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# The reversal anti-automorphism

The defining relations of the infinite type-A Hecke algebra are invariant under reading words
backwards, so there is an `R`-linear anti-automorphism
`TauCeti.InfiniteTypeAHeckeAlgebra.reverse` fixing every generator `T i`, which sends
`T i₁ * ⋯ * T iₖ` to `T iₖ * ⋯ * T i₁`. It is involutive, it preserves every stage, and it is
defined over every commutative ring and for every unit `q`, with no star structure on the
coefficients. On the basis `T_w` of a stage it is the classical anti-involution `T_w ↦ T_(w⁻¹)`,
although that description is not needed here.

Reversal turns left modules into right modules; it is used to obtain the right coset basis
`TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv` from the left one.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverseOp`: reversal as an algebra map to the opposite
  algebra.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverseOpEquiv`: reversal as an algebra isomorphism with the
  opposite algebra.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse`: reversal as an `R`-linear anti-automorphism.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mul` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_reverse`: reversal is an involutive
  anti-automorphism.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_prod_map_T`: reversal reverses every word in the
  generators.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mem_stage_iff`: reversal preserves every stage.

## Implementation notes

The reversal follows the pattern of `CliffordAlgebra.reverseOp`,
`CliffordAlgebra.reverseOpEquiv` and `CliffordAlgebra.reverse`: an algebra map to the opposite
algebra built from the universal property, its bundling as an isomorphism, and the underlying
linear map.

## References

* A. Mathas, *Iwahori-Hecke algebras and Schur algebras of the symmetric group*, University
  Lecture Series 15, AMS (1999), Section 1.1, for the anti-involution `T_w ↦ T_(w⁻¹)`.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

open MulOpposite

variable {R : Type*} [CommRing R] {q : Rˣ}

/-- Reversal of words in the generators, as an algebra map to the opposite algebra: it sends each
generator `T i` to `op (T i)`. -/
def reverseOp : InfiniteTypeAHeckeAlgebra R q →ₐ[R] (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
  lift (fun i ↦ op (T q i))
    (fun i ↦ unop_injective <| by simp)
    (fun i ↦ unop_injective <| by simpa [mul_assoc] using T_braid (q := q) i)
    (fun {_ _} h ↦ unop_injective <| (commute_T (q := q) (.inl h)).eq.symm)

/-- Reversal sends each generator to itself in the opposite algebra. -/
@[simp]
theorem reverseOp_T (i : ℕ) : reverseOp (T q i) = op (T q i) :=
  lift_T _ _ _ _ i

/-- Reversal of words in the generators, `T i₁ * ⋯ * T iₖ ↦ T iₖ * ⋯ * T i₁`: the `R`-linear
anti-automorphism of the infinite type-A Hecke algebra fixing every generator. -/
def reverse : InfiniteTypeAHeckeAlgebra R q →ₗ[R] InfiniteTypeAHeckeAlgebra R q :=
  (opLinearEquiv R).symm.toLinearMap ∘ₗ reverseOp.toLinearMap

@[simp]
theorem unop_reverseOp (x : InfiniteTypeAHeckeAlgebra R q) : unop (reverseOp x) = reverse x :=
  (rfl)

@[simp]
theorem op_reverse (x : InfiniteTypeAHeckeAlgebra R q) : op (reverse x) = reverseOp x :=
  (rfl)

/-- Reversal fixes every generator. -/
@[simp]
theorem reverse_T (i : ℕ) : reverse (T q i) = T q i := by
  rw [← unop_reverseOp, reverseOp_T, unop_op]

/-- Reversal fixes the scalars. -/
@[simp]
theorem reverse_algebraMap (r : R) :
    reverse (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) = algebraMap R _ r := by
  rw [← unop_reverseOp, AlgHom.commutes, MulOpposite.algebraMap_apply, unop_op]

/-- Reversal fixes `1`. -/
@[simp]
theorem reverse_one : reverse (1 : InfiniteTypeAHeckeAlgebra R q) = 1 := by
  rw [← unop_reverseOp, map_one, unop_one]

/-- Reversal is an anti-homomorphism. -/
@[simp]
theorem reverse_mul (x y : InfiniteTypeAHeckeAlgebra R q) :
    reverse (x * y) = reverse y * reverse x := by
  simp only [← unop_reverseOp, map_mul, unop_mul]

/-- Reversal reverses every word in the generators:
`T i₁ * ⋯ * T iₖ ↦ T iₖ * ⋯ * T i₁`. -/
theorem reverse_prod_map_T (l : List ℕ) :
    reverse (l.map (T q)).prod = (l.map (T q)).reverse.prod := by
  rw [← unop_reverseOp, unop_map_list_prod, List.map_map]
  simp [Function.comp_def]

/-- Reversal is an involution. -/
@[simp]
theorem reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q) : reverse (reverse x) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T q)) := by simp [adjoin_range_T]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp
  | algebraMap r => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | mul x y _ _ hx hy => simp only [reverse_mul, hx, hy]

/-- Reversal is an involution, as a function. -/
theorem reverse_involutive : Function.Involutive (reverse (R := R) (q := q)) :=
  reverse_reverse

/-- Reversal is an involution, as a linear map. -/
@[simp]
theorem reverse_comp_reverse :
    reverse ∘ₗ reverse = (LinearMap.id : InfiniteTypeAHeckeAlgebra R q →ₗ[R] _) :=
  LinearMap.ext reverse_reverse

/-- Reversal, as an algebra isomorphism of the infinite type-A Hecke algebra with its opposite
algebra. -/
def reverseOpEquiv : InfiniteTypeAHeckeAlgebra R q ≃ₐ[R] (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.ext fun x ↦ unop_injective <| by simp)
    (AlgHom.ext fun x ↦ by simp)

@[simp]
theorem reverseOpEquiv_apply (x : InfiniteTypeAHeckeAlgebra R q) :
    reverseOpEquiv x = reverseOp x :=
  (rfl)

/-- The inverse of `reverseOpEquiv` is reversal read in the opposite algebra. -/
@[simp]
theorem reverseOpEquiv_symm_apply (x : (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ) :
    reverseOpEquiv.symm x = reverse (unop x) :=
  (rfl)

/-- Reversal maps the stage of the first `n` strands into itself. -/
theorem reverse_mem_stage {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q n) :
    reverse x ∈ stage R q n := by
  have h : stage R q n ≤ (stage R q n).op.comap reverseOp :=
    stage_le_iff.2 fun i hi ↦ by simpa using T_mem_stage (q := q) hi
  simpa using h hx

/-- Reversal preserves the stage of the first `n` strands. -/
@[simp]
theorem reverse_mem_stage_iff {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} :
    reverse x ∈ stage R q n ↔ x ∈ stage R q n :=
  ⟨fun h ↦ by simpa using reverse_mem_stage h, reverse_mem_stage⟩

end InfiniteTypeAHeckeAlgebra

end TauCeti
