/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite
public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.GroupTheory.Coxeter.Hecke.Reverse

/-!
# The reversal anti-automorphisms of the type-A Hecke algebras

The defining relations of the infinite type-A Hecke algebra are invariant under reading words
backwards: the quadratic relation involves a single generator, and the braid and
distant-commutation relations are palindromic or symmetric. So there is an `R`-linear
anti-automorphism `TauCeti.InfiniteTypeAHeckeAlgebra.reverse` fixing every generator `T i` and
reversing the order of products, `reverse (x * y) = reverse y * reverse x`. It is an involution
and preserves every finite stage. On the reduced-word elements `T_w` it is the anti-involution
`T_w ↦ T_(w⁻¹)`, since a reduced word for `w` read backwards is a reduced word for `w⁻¹`; that
identification is not needed here.

This anti-automorphism exchanges left and right multiplication, so it transports statements about
left modules over the stages into statements about right modules. Unlike the real-parameter
involution of `TauCeti.Algebra.TypeAHeckeAlgebra.Star`, it is linear over the coefficients and
needs no star structure or hypothesis on `q`.

The finite type-A Hecke algebra on `n` strands carries the same anti-involution
`TauCeti.TypeAHeckeAlgebra.reverse`, the reversal `CoxeterMatrix.HeckeAlgebra.reverse` of the
Hecke algebra of the type-A Coxeter matrix transported along
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`. It sends `T_w` to `T_(w⁻¹)`
(`TauCeti.TypeAHeckeAlgebra.reverse_Tw`), and it is the anti-involution `*` that transposes
Murphy's elements `m_st` (`TauCeti.TypeAHeckeAlgebra.reverse_murphyElement`).

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverseOp`: the reversal as an algebra homomorphism to the
  opposite algebra.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse`: the reversal as a linear map.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverseOpEquiv`: the reversal as an algebra isomorphism with
  the opposite algebra.
* `TauCeti.InfiniteTypeAHeckeAlgebra.stageReverse`: its restriction to the stage of the first `n`
  strands, as a linear isomorphism.
* `TauCeti.TypeAHeckeAlgebra.reverseOpEquiv` and `TauCeti.TypeAHeckeAlgebra.reverse`: the
  reversal of the finite type-A Hecke algebra, as an algebra isomorphism with the opposite algebra
  and as a linear map.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_T` and `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mul`:
  the reversal fixes the generators and reverses products.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_reverse`: the reversal is an involution.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mem_stage_iff`: it preserves the finite stages.
* `TauCeti.TypeAHeckeAlgebra.reverse_T`, `TauCeti.TypeAHeckeAlgebra.reverse_mul`,
  `TauCeti.TypeAHeckeAlgebra.reverse_reverse` and `TauCeti.TypeAHeckeAlgebra.reverse_Tw`: the
  finite reversal fixes the generators, reverses products, is an involution and sends `T_w` to
  `T_(w⁻¹)`.
* `TauCeti.TypeAHeckeAlgebra.toInfinite_reverse`: the embedding into the infinite algebra
  intertwines the two reversals.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Chapter 4, for the anti-involution `T_w ↦ T_(w⁻¹)`.
* The bundling through the opposite algebra follows `CliffordAlgebra.reverseOp` and
  `CliffordAlgebra.reverse` in `Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation`.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open MulOpposite

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The reversal, as an algebra homomorphism to the opposite algebra: it sends each generator
`T i` to `op (T i)`. -/
def reverseOp : InfiniteTypeAHeckeAlgebra R q →ₐ[R] (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
  lift (fun i ↦ op (T q i))
    (fun i ↦ unop_injective <| by simp)
    (fun i ↦ unop_injective <| by simpa [mul_assoc] using T_braid (q := q) i)
    (fun h ↦ unop_injective (commute_T (q := q) (.inl h)).eq.symm)

/-- The reversal fixes every generator. -/
@[simp]
theorem reverseOp_T (i : ℕ) : reverseOp q (T q i) = op (T q i) :=
  lift_T ..

/-- The reversal anti-automorphism of the infinite type-A Hecke algebra: the `R`-linear map
fixing every generator `T i` and reversing the order of products. -/
def reverse : InfiniteTypeAHeckeAlgebra R q →ₗ[R] InfiniteTypeAHeckeAlgebra R q :=
  (opLinearEquiv R).symm.toLinearMap ∘ₗ (reverseOp q).toLinearMap

variable {q}

@[simp]
theorem unop_reverseOp (x : InfiniteTypeAHeckeAlgebra R q) : unop (reverseOp q x) = reverse q x :=
  (rfl)

@[simp]
theorem op_reverse (x : InfiniteTypeAHeckeAlgebra R q) : op (reverse q x) = reverseOp q x :=
  (rfl)

/-- The reversal fixes every generator. -/
@[simp]
theorem reverse_T (i : ℕ) : reverse q (T q i) = T q i :=
  op_injective (reverseOp_T q i)

/-- The reversal fixes the scalars. -/
@[simp]
theorem reverse_algebraMap (r : R) :
    reverse q (algebraMap R (InfiniteTypeAHeckeAlgebra R q) r) = algebraMap R _ r :=
  op_injective ((reverseOp q).commutes r)

@[simp]
theorem reverse_one : reverse q (1 : InfiniteTypeAHeckeAlgebra R q) = 1 :=
  op_injective (map_one (reverseOp q))

/-- The reversal reverses the order of products. -/
@[simp]
theorem reverse_mul (x y : InfiniteTypeAHeckeAlgebra R q) :
    reverse q (x * y) = reverse q y * reverse q x :=
  op_injective (map_mul (reverseOp q) x y)

/-- The reversal of a product of a list is the product of the reversals in the opposite order. -/
theorem reverse_list_prod (l : List (InfiniteTypeAHeckeAlgebra R q)) :
    reverse q l.prod = (l.map (reverse q)).reverse.prod := by
  rw [← unop_reverseOp, unop_map_list_prod]
  simp only [Function.comp_def, unop_reverseOp]

/-- The reversal is an involution. -/
@[simp]
theorem reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q) : reverse q (reverse q x) = x := by
  have h : (AlgHom.opComm (reverseOp q)).comp (reverseOp q) = AlgHom.id R _ :=
    hom_ext fun i ↦ by simp [AlgHom.opComm]
  simpa [AlgHom.opComm] using AlgHom.congr_fun h x

theorem reverse_involutive : Function.Involutive (reverse q) :=
  reverse_reverse

/-- The reversal is an involution, as a linear map. -/
@[simp]
theorem reverse_comp_reverse :
    reverse q ∘ₗ reverse q = (LinearMap.id : InfiniteTypeAHeckeAlgebra R q →ₗ[R] _) :=
  LinearMap.ext reverse_reverse

variable (q) in
/-- The reversal, as an algebra isomorphism of the infinite type-A Hecke algebra with its opposite
algebra. -/
def reverseOpEquiv : InfiniteTypeAHeckeAlgebra R q ≃ₐ[R] (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverseOp q) (AlgHom.opComm (reverseOp q))
    (AlgHom.ext fun x ↦ unop_injective <| by simp)
    (AlgHom.ext fun x ↦ by simp)

@[simp]
theorem reverseOpEquiv_apply (x : InfiniteTypeAHeckeAlgebra R q) :
    reverseOpEquiv q x = reverseOp q x :=
  (rfl)

/-- The inverse of `reverseOpEquiv` is the reversal read in the opposite algebra. -/
@[simp]
theorem reverseOpEquiv_symm_apply (x : (InfiniteTypeAHeckeAlgebra R q)ᵐᵒᵖ) :
    (reverseOpEquiv q).symm x = reverse q (unop x) :=
  (rfl)

/-- The reversal preserves the stage of the first `n` strands. -/
@[simp]
theorem reverse_mem_stage_iff {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} :
    reverse q x ∈ stage R q n ↔ x ∈ stage R q n := by
  have h : stage R q n ≤ (stage R q n).op.comap (reverseOp q) :=
    stage_le_iff.2 fun i hi ↦ by
      simpa [Subalgebra.mem_comap, Subalgebra.mem_op] using T_mem_stage (q := q) hi
  refine ⟨fun hx ↦ ?_, fun hx ↦ h hx⟩
  simpa using h hx

variable (q) in
/-- The reversal restricted to the stage of the first `n` strands, as a linear isomorphism. -/
def stageReverse (n : ℕ) : stage R q n ≃ₗ[R] stage R q n where
  toFun x := ⟨reverse q x, reverse_mem_stage_iff.2 x.property⟩
  invFun x := ⟨reverse q x, reverse_mem_stage_iff.2 x.property⟩
  left_inv x := Subtype.ext (reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q))
  right_inv x := Subtype.ext (reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q))
  map_add' x y := Subtype.ext (map_add (reverse q) (x : InfiniteTypeAHeckeAlgebra R q) y)
  map_smul' r x := Subtype.ext (map_smul (reverse q) r (x : InfiniteTypeAHeckeAlgebra R q))

/-- Restriction to a stage agrees with the ambient reversal. -/
@[simp]
theorem coe_stageReverse (n : ℕ) (x : stage R q n) :
    (stageReverse q n x : InfiniteTypeAHeckeAlgebra R q) = reverse q x :=
  (rfl)

/-- The reversal on a stage is its own inverse. -/
@[simp]
theorem stageReverse_symm (n : ℕ) : (stageReverse q n).symm = stageReverse q n :=
  (rfl)

end TauCeti.InfiniteTypeAHeckeAlgebra

namespace TauCeti.TypeAHeckeAlgebra

open MulOpposite

variable {R : Type*} [CommRing R] (q : Rˣ) {n : ℕ}

/-- The reversal of the type-A Hecke algebra on `n` strands, as an algebra isomorphism with its
opposite algebra. It fixes every generator `T i` (`TauCeti.TypeAHeckeAlgebra.reverse_T`); it is the
reversal of the Hecke algebra of the type-A Coxeter matrix, transported along
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`. -/
noncomputable def reverseOpEquiv : TypeAHeckeAlgebra R q n ≃ₐ[R] (TypeAHeckeAlgebra R q n)ᵐᵒᵖ :=
  ((algEquivHeckeAlgebra R q n).trans (CoxeterMatrix.HeckeAlgebra.reverseOpEquiv _ _)).trans
    (AlgEquiv.op (algEquivHeckeAlgebra R q n)).symm

/-- The reversal anti-automorphism of the type-A Hecke algebra on `n` strands: the `R`-linear map
fixing every generator `T i` and reversing the order of products. It sends `T_w` to `T_(w⁻¹)`. -/
noncomputable def reverse : TypeAHeckeAlgebra R q n →ₗ[R] TypeAHeckeAlgebra R q n :=
  (opLinearEquiv R).symm.toLinearMap ∘ₗ (reverseOpEquiv q).toLinearMap

variable {q}

@[simp]
theorem unop_reverseOpEquiv (x : TypeAHeckeAlgebra R q n) :
    unop (reverseOpEquiv q x) = reverse q x :=
  (rfl)

@[simp]
theorem op_reverse (x : TypeAHeckeAlgebra R q n) : op (reverse q x) = reverseOpEquiv q x :=
  (rfl)

/-- The reversal corresponds to the reversal of the Hecke algebra of the type-A Coxeter matrix
under `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`. -/
theorem algEquivHeckeAlgebra_reverse (x : TypeAHeckeAlgebra R q n) :
    algEquivHeckeAlgebra R q n (reverse q x) =
      CoxeterMatrix.HeckeAlgebra.reverse _ _ (algEquivHeckeAlgebra R q n x) := by
  simp [reverse, reverseOpEquiv, ← CoxeterMatrix.HeckeAlgebra.op_reverse]

/-- The reversal reverses the order of products. -/
@[simp]
theorem reverse_mul (x y : TypeAHeckeAlgebra R q n) :
    reverse q (x * y) = reverse q y * reverse q x :=
  op_injective (map_mul (reverseOpEquiv q) x y)

@[simp]
theorem reverse_one : reverse q (1 : TypeAHeckeAlgebra R q n) = 1 :=
  op_injective (map_one (reverseOpEquiv q))

/-- The reversal fixes the scalars. -/
@[simp]
theorem reverse_algebraMap (r : R) :
    reverse q (algebraMap R (TypeAHeckeAlgebra R q n) r) = algebraMap R _ r :=
  op_injective ((reverseOpEquiv q).commutes r)

/-- The reversal fixes every generator. -/
@[simp]
theorem reverse_T (i : Fin (n - 1)) : reverse q (T q i) = T (R := R) q i :=
  (algEquivHeckeAlgebra R q n).injective <| by
    rw [algEquivHeckeAlgebra_reverse, algEquivHeckeAlgebra_T,
      CoxeterMatrix.HeckeAlgebra.reverse_T]

/-- The reversal sends `T_w` to `T_(w⁻¹)`. -/
@[simp]
theorem reverse_Tw {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    (w : W) : reverse q (Tw (R := R) q cs w) = Tw q cs w⁻¹ :=
  (algEquivHeckeAlgebra R q n).injective <| by
    rw [algEquivHeckeAlgebra_reverse, algEquivHeckeAlgebra_Tw, algEquivHeckeAlgebra_Tw,
      CoxeterMatrix.HeckeAlgebra.reverse_Tw]

/-- The reversal is an involution. -/
@[simp]
theorem reverse_reverse (x : TypeAHeckeAlgebra R q n) : reverse q (reverse q x) = x :=
  (algEquivHeckeAlgebra R q n).injective <| by
    rw [algEquivHeckeAlgebra_reverse, algEquivHeckeAlgebra_reverse,
      CoxeterMatrix.HeckeAlgebra.reverse_reverse]

theorem reverse_involutive : Function.Involutive (reverse (R := R) q (n := n)) :=
  reverse_reverse

/-- The reversal is an involution, as a linear map. -/
@[simp]
theorem reverse_comp_reverse :
    reverse q ∘ₗ reverse q = (LinearMap.id : TypeAHeckeAlgebra R q n →ₗ[R] _) :=
  LinearMap.ext reverse_reverse

/-- The map to the infinite type-A Hecke algebra intertwines the two reversals. -/
theorem toInfinite_reverse (x : TypeAHeckeAlgebra R q n) :
    toInfinite R q n (reverse q x) = InfiniteTypeAHeckeAlgebra.reverse q (toInfinite R q n x) := by
  have h : (AlgHom.op (toInfinite R q n)).comp (reverseOpEquiv q).toAlgHom =
      (InfiniteTypeAHeckeAlgebra.reverseOp q).comp (toInfinite R q n) :=
    hom_ext fun i ↦ by simp [← op_reverse]
  simpa [← op_reverse] using congrArg unop (AlgHom.congr_fun h x)

/-- The inverse of `reverseOpEquiv` is the reversal read in the opposite algebra. -/
@[simp]
theorem reverseOpEquiv_symm_apply (x : (TypeAHeckeAlgebra R q n)ᵐᵒᵖ) :
    (reverseOpEquiv q).symm x = reverse q (unop x) := by
  rw [AlgEquiv.symm_apply_eq, ← op_reverse, reverse_reverse, op_unop]

end TauCeti.TypeAHeckeAlgebra
