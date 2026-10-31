/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis

/-!
# The reversal anti-automorphism and the right coset basis

The defining relations of the infinite type-A Hecke algebra are invariant under reading words
backwards, so there is an `R`-linear anti-automorphism
`TauCeti.InfiniteTypeAHeckeAlgebra.reverse` fixing every generator `T i`, which sends
`T i₁ * ⋯ * T iₖ` to `T iₖ * ⋯ * T i₁`. It is involutive, it preserves every stage, and it is
defined over every commutative ring and for every unit `q`, with no star structure on the
coefficients. On the basis `T_w` of a stage it is the classical anti-involution `T_w ↦ T_(w⁻¹)`,
although that description is not needed here.

Reversal turns left modules into right modules. Applied to the coset basis
`TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv`, which makes the stage `Hₙ₊₁` of the first
`n + 1` strands a free left module over the stage `Hₙ` with basis the descending products
`T (n - 1) * ⋯ * T m`, it makes `Hₙ₊₁` a free right `Hₙ`-module of rank `n + 1` with basis the
ascending products

`rightCosetRep q n m = T m * T (m + 1) * ⋯ * T (n - 1)`, for `m = 0, …, n`.

Concretely, every element of `Hₙ₊₁` is uniquely a sum `∑ m, rightCosetRep q n m * a m` with
coefficients `a m` in `Hₙ` (`TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv`), and the
coefficients depend `Hₙ`-linearly on the element for right multiplication
(`TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv_symm_mul`). These are the elements `T_w` for
the minimal-length representatives `w = s m ⋯ s (n - 1)` of the right cosets of the symmetric
group on `n` letters in the symmetric group on `n + 1` letters.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverseOp`: reversal as an algebra map to the opposite
  algebra.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse`: reversal as an `R`-linear anti-automorphism.
* `TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetRep`: the ascending product `T m * ⋯ * T (n - 1)`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv`: the `R`-linear isomorphism from
  `Fin (n + 1) → Hₙ` to `Hₙ₊₁` sending `a` to `∑ m, rightCosetRep q n m * a m`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mul` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_reverse`: reversal is an involutive
  anti-automorphism.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_mem_stage_iff`: reversal preserves every stage.
* `TauCeti.InfiniteTypeAHeckeAlgebra.reverse_cosetRep`: reversal exchanges the descending and
  ascending coset representatives.
* `TauCeti.InfiniteTypeAHeckeAlgebra.coe_rightCosetEquiv_apply`: the formula for
  `rightCosetEquiv`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv_op_smul` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv_symm_mul`: `rightCosetEquiv` is `Hₙ`-linear
  for right multiplication, so the ascending representatives form a basis of `Hₙ₊₁` as a right
  `Hₙ`-module.
* `TauCeti.InfiniteTypeAHeckeAlgebra.rightCosetEquiv_symm_inclusion`: an element `b` of `Hₙ` has
  coordinate `b` at the representative `rightCosetRep q n n = 1`, and coordinate zero at every
  other index.

## Implementation notes

The reversal follows the pattern of `CliffordAlgebra.reverseOp` and `CliffordAlgebra.reverse`: an
algebra map to the opposite algebra built from the universal property, and the underlying linear
map.

## References

* A. Mathas, *Iwahori-Hecke algebras and Schur algebras of the symmetric group*, University
  Lecture Series 15, AMS (1999), Section 1.1, for the anti-involution `T_w ↦ T_(w⁻¹)`.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

open MulOpposite

variable {R : Type*} [CommRing R] {q : Rˣ}

section Reverse

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

variable (R q) in
/-- Reversal, restricted to the stage of the first `n` strands. -/
private def stageReverse (n : ℕ) : stage R q n ≃ₗ[R] stage R q n where
  toFun x := ⟨reverse (x : InfiniteTypeAHeckeAlgebra R q), reverse_mem_stage x.2⟩
  invFun x := ⟨reverse (x : InfiniteTypeAHeckeAlgebra R q), reverse_mem_stage x.2⟩
  map_add' x y := Subtype.ext (map_add reverse (x : InfiniteTypeAHeckeAlgebra R q) y)
  map_smul' r x := Subtype.ext (map_smul reverse r (x : InfiniteTypeAHeckeAlgebra R q))
  left_inv x := Subtype.ext (reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q))
  right_inv x := Subtype.ext (reverse_reverse (x : InfiniteTypeAHeckeAlgebra R q))

private theorem coe_stageReverse {n : ℕ} (x : stage R q n) :
    (stageReverse R q n x : InfiniteTypeAHeckeAlgebra R q) = reverse x :=
  (rfl)

end Reverse

section RightCosetRep

variable (q) in
/-- The ascending product `T m * T (m + 1) * ⋯ * T (n - 1)` of the generators from `T m` up to
`T (n - 1)`, which is `1` when `n ≤ m`. It is the reversal of `cosetRep q n m`; for `m ≤ n` it is
the element `T_w` of the minimal-length representative `w = s m ⋯ s (n - 1)` of a right coset of
the symmetric group on `n` letters in the symmetric group on `n + 1` letters. -/
def rightCosetRep (n m : ℕ) : InfiniteTypeAHeckeAlgebra R q :=
  ((List.Ico m n).map (T q)).prod

/-- The ascending product from `T m` up to `T (n - 1)` is empty when `n ≤ m`. -/
theorem rightCosetRep_of_le {n m : ℕ} (h : n ≤ m) : rightCosetRep q n m = 1 := by
  rw [rightCosetRep, List.Ico.eq_nil_of_le h, List.map_nil, List.prod_nil]

/-- The trivial ascending representative is `1`. -/
@[simp]
theorem rightCosetRep_self (n : ℕ) : rightCosetRep q n n = 1 :=
  rightCosetRep_of_le le_rfl

/-- Raising the top of the ascending product adds a generator on the right. -/
theorem rightCosetRep_succ {n m : ℕ} (h : m ≤ n) :
    rightCosetRep q (n + 1) m = rightCosetRep q n m * T q n := by
  simp only [rightCosetRep, List.Ico.succ_top h, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

/-- Reversal turns the descending coset representatives into the ascending ones. -/
@[simp]
theorem reverse_cosetRep (n m : ℕ) : reverse (cosetRep q n m) = rightCosetRep q n m := by
  induction n with
  | zero => rw [cosetRep_of_le m.zero_le, rightCosetRep_of_le m.zero_le, reverse_one]
  | succ n ih =>
    obtain h | h := le_or_gt m n
    · rw [cosetRep_succ h, reverse_mul, ih, reverse_T, rightCosetRep_succ h]
    · rw [cosetRep_of_le h, rightCosetRep_of_le h, reverse_one]

/-- Reversal turns the ascending coset representatives into the descending ones. -/
@[simp]
theorem reverse_rightCosetRep (n m : ℕ) : reverse (rightCosetRep q n m) = cosetRep q n m := by
  rw [← reverse_cosetRep, reverse_reverse]

/-- Lowering the bottom of the ascending product adds a generator on the left. -/
theorem T_mul_rightCosetRep_succ {n m : ℕ} (h : m < n) :
    T q m * rightCosetRep q n (m + 1) = rightCosetRep q n m := by
  rw [← reverse_cosetRep n m, ← cosetRep_succ_mul_T h, reverse_mul, reverse_T, reverse_cosetRep]

/-- The ascending product up to `T (n - 1)` lies in the stage of the first `n + 1` strands. -/
theorem rightCosetRep_mem_stage (n m : ℕ) : rightCosetRep q n m ∈ stage R q (n + 1) := by
  rw [← reverse_cosetRep]
  exact reverse_mem_stage (cosetRep_mem_stage n m)

end RightCosetRep

section RightCosetEquiv

variable (R q) in
/-- **The right coset basis.** The stage of the first `n + 1` strands is a free right module over
the stage of the first `n` strands with basis the ascending products `rightCosetRep q n m`,
`m = 0, …, n`: the `R`-linear map sending coefficients `a : Fin (n + 1) → Hₙ` to
`∑ m, rightCosetRep q n m * a m` is an isomorphism onto `Hₙ₊₁`. It is the reversal of the left
coset basis `TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv`. -/
noncomputable def rightCosetEquiv (n : ℕ) :
    (Fin (n + 1) → stage R q n) ≃ₗ[R] stage R q (n + 1) :=
  (LinearEquiv.piCongrRight fun _ ↦ stageReverse R q n) ≪≫ₗ cosetEquiv R q n ≪≫ₗ
    stageReverse R q (n + 1)

/-- The right coset isomorphism sends coefficients `a` to `∑ m, rightCosetRep q n m * a m`. -/
@[simp]
theorem coe_rightCosetEquiv_apply {n : ℕ} (a : Fin (n + 1) → stage R q n) :
    (rightCosetEquiv R q n a : InfiniteTypeAHeckeAlgebra R q) =
      ∑ m : Fin (n + 1), rightCosetRep q n m * (a m : InfiniteTypeAHeckeAlgebra R q) := by
  simp [rightCosetEquiv, coe_stageReverse, map_sum]

/-- The right coset isomorphism is linear for right multiplication by the stage of the first `n`
strands, which acts on the coefficients through the opposite ring. -/
theorem rightCosetEquiv_op_smul {n : ℕ} (b : stage R q n) (a : Fin (n + 1) → stage R q n) :
    rightCosetEquiv R q n (op b • a) =
      rightCosetEquiv R q n a * Subalgebra.inclusion (stage_mono n.le_succ) b :=
  Subtype.ext <| by
    simp only [coe_rightCosetEquiv_apply, Pi.smul_apply, op_smul_eq_mul, Subalgebra.coe_mul,
      Subalgebra.coe_inclusion, Finset.sum_mul, mul_assoc]

/-- The coefficients of an element of the stage `n + 1` along the representatives
`rightCosetRep q n m` are linear for right multiplication by the stage `n`. -/
theorem rightCosetEquiv_symm_mul {n : ℕ} (b : stage R q n) (x : stage R q (n + 1)) :
    (rightCosetEquiv R q n).symm (x * Subalgebra.inclusion (stage_mono n.le_succ) b) =
      op b • (rightCosetEquiv R q n).symm x := by
  rw [LinearEquiv.symm_apply_eq, rightCosetEquiv_op_smul, LinearEquiv.apply_symm_apply]

/-- An element of the stage `n` is its own coefficient at the trivial representative
`rightCosetRep q n n = 1`, and has no other coefficients. -/
@[simp]
theorem rightCosetEquiv_symm_inclusion {n : ℕ} (b : stage R q n) :
    (rightCosetEquiv R q n).symm (Subalgebra.inclusion (stage_mono n.le_succ) b) =
      Pi.single (Fin.last n) b := by
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [coe_rightCosetEquiv_apply, Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro m _ hm
    simp [Pi.single_eq_of_ne hm]
  · simp

end RightCosetEquiv

end InfiniteTypeAHeckeAlgebra

end TauCeti
