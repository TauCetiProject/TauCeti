/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.GroupTheory.Coxeter.Hecke.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import TauCeti.GroupTheory.Coxeter.Basic

/-!
# The reversal anti-involution of an Iwahori–Hecke algebra

The defining relations of the Iwahori–Hecke algebra `M.HeckeAlgebra c` of a Coxeter matrix `M`
are invariant under reading words backwards: the quadratic relation involves a single generator,
and reversing an alternating word of length `M i j` in `i` and `j` gives an alternating word of
the same length, so the reversed braid relation is again a braid relation. Hence there is an
`R`-linear anti-automorphism `CoxeterMatrix.HeckeAlgebra.reverse` fixing every generator `T i`
and reversing the order of products. It is an involution, and for a Coxeter system `cs` with
Coxeter matrix `M` it sends `T_w` to `T_(w⁻¹)`, since a reduced expression of `w` read backwards
is a reduced expression of `w⁻¹`.

This is the anti-involution `*` of the cellular structures on Hecke algebras: for instance
Murphy's basis of the type-A Hecke algebra is transposed by it.

## Main definitions

* `CoxeterMatrix.HeckeAlgebra.reverseOp`: the reversal as an algebra homomorphism to the opposite
  algebra.
* `CoxeterMatrix.HeckeAlgebra.reverse`: the reversal as a linear map.
* `CoxeterMatrix.HeckeAlgebra.reverseOpEquiv`: the reversal as an algebra isomorphism with the
  opposite algebra.

## Main results

* `CoxeterMatrix.HeckeAlgebra.reverse_T` and `CoxeterMatrix.HeckeAlgebra.reverse_mul`: the
  reversal fixes the generators and reverses products.
* `CoxeterMatrix.HeckeAlgebra.reverse_reverse`: the reversal is an involution.
* `CoxeterMatrix.HeckeAlgebra.reverse_Tw`: the reversal sends `T_w` to `T_(w⁻¹)`.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Chapter 4, for the anti-involution `T_w ↦ T_(w⁻¹)`.
* The bundling through the opposite algebra follows `CliffordAlgebra.reverseOp` and
  `CliffordAlgebra.reverse` in `Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation`, as does
  `TauCeti.InfiniteTypeAHeckeAlgebra.reverse`.
-/

public section

open MulOpposite CoxeterSystem

namespace CoxeterMatrix.HeckeAlgebra

variable {B : Type*} (M : CoxeterMatrix B) {R : Type*} [CommSemiring R] (c : R)

/-- Reading an alternating word backwards does not change the product of the Hecke generators
along the two sides of a braid relation: the reversed braid relation is again a braid relation. -/
private theorem prod_map_T_reverse_braidWord (i j : B) :
    ((braidWord M i j).reverse.map (T M c)).prod =
      ((braidWord M j i).reverse.map (T M c)).prod := by
  rw [braidWord, braidWord, TauCeti.reverse_alternatingWord, TauCeti.reverse_alternatingWord,
    M.symmetric j i]
  have h := prod_map_T_braidWord M c j i
  rw [braidWord, braidWord, M.symmetric j i] at h
  split_ifs
  · exact h
  · exact h.symm

/-- The reversal, as an algebra homomorphism to the opposite algebra: it sends each generator
`T i` to `op (T i)`. -/
def reverseOp : M.HeckeAlgebra c →ₐ[R] (M.HeckeAlgebra c)ᵐᵒᵖ :=
  lift (fun i ↦ op (T M c i))
    (fun i ↦ unop_injective <| by simp [T_mul_self])
    (fun i j ↦ unop_injective <| by
      simpa [unop_list_prod, Function.comp_def] using prod_map_T_reverse_braidWord M c i j)

/-- The reversal fixes every generator. -/
@[simp]
theorem reverseOp_T (i : B) : reverseOp M c (T M c i) = op (T M c i) :=
  lift_T ..

/-- The reversal anti-automorphism of the Hecke algebra: the `R`-linear map fixing every
generator `T i` and reversing the order of products. -/
def reverse : M.HeckeAlgebra c →ₗ[R] M.HeckeAlgebra c :=
  (opLinearEquiv R).symm.toLinearMap ∘ₗ (reverseOp M c).toLinearMap

variable {M c}

@[simp]
theorem unop_reverseOp (x : M.HeckeAlgebra c) : unop (reverseOp M c x) = reverse M c x :=
  (rfl)

@[simp]
theorem op_reverse (x : M.HeckeAlgebra c) : op (reverse M c x) = reverseOp M c x :=
  (rfl)

/-- The reversal fixes every generator. -/
@[simp]
theorem reverse_T (i : B) : reverse M c (T M c i) = T M c i :=
  op_injective (reverseOp_T M c i)

/-- The reversal fixes the scalars. -/
@[simp]
theorem reverse_algebraMap (r : R) :
    reverse M c (algebraMap R (M.HeckeAlgebra c) r) = algebraMap R _ r :=
  op_injective ((reverseOp M c).commutes r)

@[simp]
theorem reverse_one : reverse M c (1 : M.HeckeAlgebra c) = 1 :=
  op_injective (map_one (reverseOp M c))

/-- The reversal reverses the order of products. -/
@[simp]
theorem reverse_mul (x y : M.HeckeAlgebra c) :
    reverse M c (x * y) = reverse M c y * reverse M c x :=
  op_injective (map_mul (reverseOp M c) x y)

/-- The reversal of a product of a list is the product of the reversals in the opposite order. -/
theorem reverse_list_prod (l : List (M.HeckeAlgebra c)) :
    reverse M c l.prod = (l.map (reverse M c)).reverse.prod := by
  rw [← unop_reverseOp, map_list_prod, unop_list_prod, List.map_map]
  simp only [Function.comp_def, unop_reverseOp]

/-- The reversal is an involution. -/
@[simp]
theorem reverse_reverse (x : M.HeckeAlgebra c) : reverse M c (reverse M c x) = x := by
  have h : (AlgHom.opComm (reverseOp M c)).comp (reverseOp M c) = AlgHom.id R _ :=
    hom_ext fun i ↦ by simp [AlgHom.opComm]
  simpa [AlgHom.opComm] using AlgHom.congr_fun h x

theorem reverse_involutive : Function.Involutive (reverse M c) :=
  reverse_reverse

/-- The reversal is an involution, as a linear map. -/
@[simp]
theorem reverse_comp_reverse :
    reverse M c ∘ₗ reverse M c = (LinearMap.id : M.HeckeAlgebra c →ₗ[R] _) :=
  LinearMap.ext reverse_reverse

variable (M c) in
/-- The reversal, as an algebra isomorphism of the Hecke algebra with its opposite algebra. -/
def reverseOpEquiv : M.HeckeAlgebra c ≃ₐ[R] (M.HeckeAlgebra c)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverseOp M c) (AlgHom.opComm (reverseOp M c))
    (AlgHom.ext fun x ↦ unop_injective <| by simp)
    (AlgHom.ext fun x ↦ by simp)

@[simp]
theorem reverseOpEquiv_apply (x : M.HeckeAlgebra c) :
    reverseOpEquiv M c x = reverseOp M c x :=
  (rfl)

/-- The inverse of `reverseOpEquiv` is the reversal read in the opposite algebra. -/
@[simp]
theorem reverseOpEquiv_symm_apply (x : (M.HeckeAlgebra c)ᵐᵒᵖ) :
    (reverseOpEquiv M c).symm x = reverse M c (unop x) :=
  (rfl)

/-- The reversal sends `T_w` to `T_(w⁻¹)`: a reduced expression of `w` read backwards is a
reduced expression of `w⁻¹`. -/
@[simp]
theorem reverse_Tw {W : Type*} [Group W] (cs : CoxeterSystem M W) (w : W) :
    reverse M c (Tw c cs w) = Tw c cs w⁻¹ := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [Tw_wordProd hω, ← cs.wordProd_reverse, Tw_wordProd hω.reverse, reverse_list_prod,
    List.map_map, List.map_reverse]
  simp only [Function.comp_def, reverse_T]

end CoxeterMatrix.HeckeAlgebra
