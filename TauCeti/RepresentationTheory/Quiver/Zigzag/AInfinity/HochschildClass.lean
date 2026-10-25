/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import TauCeti.Algebra.Homology.AInfinity.Algebra.IntrinsicFormality.Criterion
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Backtrack
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Trace

/-!
# Nonzero quartic Hochschild classes of zigzag algebras

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). Its Hochschild cohomology `HH^{4, -2}(Z, Z)` is the
obstruction group for the quartic operations of minimal `A∞` structures on `Z`
(`TauCeti.AInfinityAlgebra.HochschildVanishesAt`). This file shows that it is nonzero, over every
nontrivial commutative ring, as soon as some vertex `v` of `G` has four distinct neighbours, for
example the centre of the affine `D₄` graph. The class is that of the loop operation
`TauCeti.zigzagLoopOperation` of a single closed walk which goes from a neighbour of `v` to `v`,
makes a detour to another neighbour and back, and returns.

## The detecting cycle

Since `Z` is a symmetric algebra, a Hochschild cochain can be paired with a Hochschild chain by
means of the trace `TauCeti.zigzagTrace`. Fix darts `δ i`, pairwise distinct, all with head `v`,
and a symmetric matrix `a` with zero diagonal and zero row sums. Write `B i j` for the backtrack
walk `TauCeti.zigzagBacktrackWalk G (δ j).symm (δ i)`, that is the darts
`δ j, (δ j).symm, δ i, (δ i).symm` in product order, and `B' i j` for its rotation
`(δ j).symm, δ i, (δ i).symm, δ j`. The functional

```text
Λ(F) = ∑ i j, a i j (tr F(B' i j) - tr F(B i j)),
```

evaluated on the words of the corresponding arrows (`TauCeti.zigzagBacktrackPairing`), vanishes on
every Hochschild coboundary of degree zero
(`TauCeti.zigzagBacktrackPairing_hochschildDifferential_eq_zero`).
On a word of four arrows the Hochschild differential of a suspended cochain `φ` is

```text
δφ(x₀, x₁, x₂, x₃) = φ(x₀x₁, x₂, x₃) + φ(x₀, x₁x₂, x₃) + φ(x₀, x₁, x₂x₃)
                       - φ(x₀, x₁, x₂) x₃ - x₀ φ(x₁, x₂, x₃)
```

(`TauCeti.zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod`), and on the words
above the only nonzero products of consecutive arrows are the backtracks at `v`, all equal to the
volume class `x_v`. The outer terms of `B' i j` cancel against those of `B i j` and `B j i` by the
trace property `tr(xy) = tr(yx)` and the symmetry of `a`, and the terms containing `x_v` cancel
because the rows of `a` sum to zero. Such a matrix exists for four darts:

```text
a = [ 0 -1  0  1]
    [-1  0  1  0]
    [ 0  1  0 -1]
    [ 1  0 -1  0].
```

On the other hand `Λ` pairs the obstruction of the loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` with coefficients `c`, its operation `m₄`, to
`∑ i j, a i j (c (B' i j) - c (B i j))` (`TauCeti.zigzagBacktrackPairing_obstruction`). For the
single walk `B' 0 3` with coefficient one this is `a 0 3 = 1`, so its loop operation, a
Hochschild cocycle (`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`), is
not a coboundary
(`TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single`),
and `HH^{4, -2}(Z, Z) ≠ 0`
(`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra`).

This is consistent with `TauCeti.zigzagBacktrackOperation_coboundary`, by which the sum of the loop
operations of a backtrack walk `B i j` and of its rotation `B' i j` is a coboundary: `Λ` takes
opposite values on them. In particular the four rotations of one such walk with equal coefficients,
as in Liu--Wang's affine `D₄` example, have a coboundary as their sum, while a single rotation does
not.

Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` therefore does not
apply to such zigzag algebras. That the corresponding loop deformation is not `A∞` isomorphic to
the strict zigzag algebra, when `2` is invertible, is proved in
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal`.

## Main definitions

* `TauCeti.zigzagBacktrackPairing`: the functional `Λ` on suspended Hochschild cochains.

## Main results

* `TauCeti.zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod`: the Hochschild
  differential of a degree-zero suspended cochain on a word of four letters of path length one.
* `TauCeti.zigzagBacktrackPairing_hochschildDifferential_eq_zero`: `Λ` vanishes on coboundaries.
* `TauCeti.zigzagBacktrackPairing_obstruction`: the value of `Λ` on the quartic operation of a loop
  deformation.
* `TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`: the quartic operation of
  a loop deformation is a Hochschild cocycle.
* `TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra` and
  `TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single`:
  quartic loop operations which are not Hochschild coboundaries.
* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra`: `HH^{4, -2}(Z, Z) ≠ 0`
  when a vertex of `G` has four distinct neighbours.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras and their Hochschild cohomology.
* J.-L. Loday, *Cyclic Homology*, Chapter 1, for Hochschild chains and cochains and their duality.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

/-! ### The Hochschild differential on words of four arrows -/

section Differential

/-- The Taylor map of the strict zigzag algebra vanishes on spliced words of length other than
two. -/
private theorem taylor_splice_of_ne {n : ℕ} (z : Fin n → nonisolatedZigzagQuotient k G)
    (p d : ℕ) (e : nonisolatedZigzagQuotient k G) (h : n + 1 - d ≠ 2) :
    (𝒵).taylor (splice k z 0 n p d e) = 0 := by
  by_cases hfit : 0 < d ∧ p + d ≤ n
  · rw [splice_eq_of_tprod k z e hfit.1 hfit.2 (by omega), AInfinityAlgebra.taylor_of_tprod,
      zigzagStrictAInfinityAlgebra_m_eq_zero h, _root_.zero_apply]
  · rw [splice_eq_zero_of_not_fits k z e hfit, map_zero]

/-- The Taylor map of the strict zigzag algebra vanishes on blocks of length other than two. -/
private theorem taylor_subword_of_ne {n : ℕ} (x : Fin n → nonisolatedZigzagQuotient k G)
    (p d : ℕ) (h : d ≠ 2) : (𝒵).taylor (subword k x p d) = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [subword_length_zero, map_zero]
  by_cases hpd : p + d ≤ n
  · rw [subword_eq_of_tprod k x hd hpd, AInfinityAlgebra.taylor_of_tprod,
      zigzagStrictAInfinityAlgebra_m_eq_zero h, _root_.zero_apply]
  · rw [subword_eq_zero_of_lt_add k x (by omega), map_zero]

/-- The Taylor map of the strict zigzag algebra on a block of length two is the twisted product. -/
private theorem taylor_subword_two {n : ℕ} (x : Fin n → nonisolatedZigzagQuotient k G)
    (p : ℕ) (h : p + 2 ≤ n) :
    (𝒵).taylor (subword k x p 2) =
      (𝒵).grading.koszulTwist 1 (x ⟨p, by omega⟩) * x ⟨p + 1, by omega⟩ := by
  rw [subword_eq_of_tprod k x (by norm_num) h, AInfinityAlgebra.taylor_of_tprod,
    zigzagStrictAInfinityAlgebra_m_two_apply]
  norm_num

/-- The Taylor map of the strict zigzag algebra on the word collapsing the first three letters of
a word of length four. -/
private theorem taylor_splice_four_zero (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    (𝒵).taylor (splice k z 0 4 0 3 e) = (𝒵).grading.koszulTwist 1 e * z 3 := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num),
    AInfinityAlgebra.taylor_of_tprod, zigzagStrictAInfinityAlgebra_m_two_apply]
  norm_num

/-- The Taylor map of the strict zigzag algebra on the word collapsing the last three letters of
a word of length four. -/
private theorem taylor_splice_four_one (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    (𝒵).taylor (splice k z 0 4 1 3 e) = (𝒵).grading.koszulTwist 1 (z 0) * e := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num),
    AInfinityAlgebra.taylor_of_tprod, zigzagStrictAInfinityAlgebra_m_two_apply]
  norm_num

/-- Collapsing the first two letters of a word of length four. -/
private theorem splice_four_two_zero (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    splice k z 0 4 0 2 e = of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![e, z 2, z 3]) := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num)]
  refine of_tprod_congr k _ _ (by norm_num) fun j ↦ ?_
  fin_cases j <;> simp

/-- Collapsing the middle two letters of a word of length four. -/
private theorem splice_four_two_one (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    splice k z 0 4 1 2 e = of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![z 0, e, z 3]) := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num)]
  refine of_tprod_congr k _ _ (by norm_num) fun j ↦ ?_
  fin_cases j <;> simp

/-- Collapsing the last two letters of a word of length four. -/
private theorem splice_four_two_two (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    splice k z 0 4 2 2 e = of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![z 0, z 1, e]) := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num)]
  refine of_tprod_congr k _ _ (by norm_num) fun j ↦ ?_
  fin_cases j <;> simp

/-- The first three letters of a word of length four. -/
private theorem subword_four_three_zero (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    subword k x 0 3 = of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1, x 2]) := by
  rw [subword_eq_of_tprod k x (by norm_num) (by norm_num)]
  refine of_tprod_congr k _ _ (by norm_num) fun j ↦ ?_
  fin_cases j <;> simp

/-- The last three letters of a word of length four. -/
private theorem subword_four_three_one (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    subword k x 1 3 = of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 1, x 2, x 3]) := by
  rw [subword_eq_of_tprod k x (by norm_num) (by norm_num)]
  refine of_tprod_congr k _ _ (by norm_num) fun j ↦ ?_
  fin_cases j <;> simp

/-- The Hochschild differential of the strict zigzag algebra on a word of four letters, with the
Koszul twists of the suspension. -/
private theorem hochschildDifferential_apply_of_tprod_koszulTwist
    (φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G)
    (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    (𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k x)) =
      (𝒵).grading.koszulTwist 1
          (φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1, x 2]))) * x 3 +
        (𝒵).grading.koszulTwist 1 (x 0) *
          φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 1, x 2, x 3])) -
      (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![(𝒵).grading.koszulTwist 1 (x 0) * x 1, x 2, x 3])) +
        φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k
          ![-(𝒵).grading.koszulTwist 1 (x 0), (𝒵).grading.koszulTwist 1 (x 1) * x 2, x 3])) +
        φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k
          ![-(𝒵).grading.koszulTwist 1 (x 0), -(𝒵).grading.koszulTwist 1 (x 1),
            (𝒵).grading.koszulTwist 1 (x 2) * x 3]))) := by
  simp only [AInfinityAlgebra.hochschildDifferential_eq_brace_sub, LinearMap.sub_apply,
    LinearMap.smul_apply, brace_def, LinearMap.comp_apply]
  rw [gradedCoderiv_of_tprod, gradedCoderiv_of_tprod, map_sum]
  -- In `φ{m}` only the collapses of two letters survive, since `m` is concentrated in arity two;
  -- in `m{φ}` only the collapses of three letters at the two ends do.
  rw [Finset.sum_congr rfl fun p _ ↦ Finset.sum_eq_single 2
    (fun d _ hd ↦ by simp [taylor_subword_of_ne x p d hd]) (by simp)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add]
  simp (disch := norm_num) only [taylor_splice_of_ne, taylor_splice_four_zero,
    taylor_splice_four_one, splice_eq_zero_of_block_lt_add, map_zero, add_zero, zero_add,
    taylor_subword_two, InternalGrading.twistedTuple_zero_twist]
  simp only [splice_four_two_zero, splice_four_two_one, splice_four_two_two,
    subword_four_three_zero, subword_four_three_one, negOnePowCast_zero, one_smul,
    InternalGrading.twistedTuple_apply, InternalGrading.koszulTwist_one_shift_one]
  norm_num

private theorem tprod_three_neg_zero (a b c : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![-a, b, c] = -PiTensorProduct.tprod k ![a, b, c] := by
  have h := (PiTensorProduct.tprod k).map_update_neg ![a, b, c] 0 a
  convert h using 3 <;> · funext j; fin_cases j <;> rfl

private theorem tprod_three_neg_one (a b c : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![a, -b, c] = -PiTensorProduct.tprod k ![a, b, c] := by
  have h := (PiTensorProduct.tprod k).map_update_neg ![a, b, c] 1 b
  convert h using 3 <;> · funext j; fin_cases j <;> rfl

private theorem tprod_three_neg_two (a b c : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![a, b, -c] = -PiTensorProduct.tprod k ![a, b, c] := by
  have h := (PiTensorProduct.tprod k).map_update_neg ![a, b, c] 2 c
  convert h using 3 <;> · funext j; fin_cases j <;> rfl

/-- **The Hochschild differential on words of four letters of path length one.** For a suspended
cochain `φ` of degree zero and letters `x₀, x₁, x₂, x₃` of path length one, such as arrows,

```text
δφ(x₀, x₁, x₂, x₃) = φ(x₀x₁, x₂, x₃) + φ(x₀, x₁x₂, x₃) + φ(x₀, x₁, x₂x₃)
                       - φ(x₀, x₁, x₂) x₃ - x₀ φ(x₁, x₂, x₃).
``` -/
theorem zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0)
    (x : Fin 4 → nonisolatedZigzagQuotient k G) (hx : ∀ i, x i ∈ zigzagIntegerGrade k G 1) :
    (𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k x)) =
      φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0 * x 1, x 2, x 3])) +
        φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1 * x 2, x 3])) +
        φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1, x 2 * x 3])) -
        φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1, x 2])) * x 3 -
        x 0 * φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 1, x 2, x 3])) := by
  have htw (y : nonisolatedZigzagQuotient k G) (hy : y ∈ zigzagIntegerGrade k G 1) :
      (𝒵).grading.koszulTwist 1 y = -y := by
    rw [(𝒵).grading.koszulTwist_one_apply_of_mem (e := 1)
      (by rwa [zigzagStrictAInfinityAlgebra_grading_piece])]
    simp
  -- `φ` sends a word of three letters of path length one to path length one.
  have hφx : φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![x 0, x 1, x 2])) ∈
      zigzagIntegerGrade k G 1 := by
    have h := hφ.map_mem (mem_gradedPiece_of_tprod ((𝒵).grading.shift 1) (by norm_num)
      ![x 0, x 1, x 2] (fun _ ↦ 0) fun i ↦ by
        rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece, zero_add]
        fin_cases i <;> exact hx _)
    simpa [InternalGrading.shift_piece] using h
  rw [hochschildDifferential_apply_of_tprod_koszulTwist, htw _ hφx, htw _ (hx 0), htw _ (hx 1),
    htw _ (hx 2)]
  simp only [neg_neg, neg_mul, tprod_three_neg_zero, tprod_three_neg_one, tprod_three_neg_two,
    map_neg]
  abel

end Differential

/-! ### The pairing with a Hochschild cycle -/

section Pairing

variable {ι : Type*} [Fintype ι]

variable (hns) in
/-- **The backtrack pairing** of darts `δ i` with weights `a i j`: the linear functional on
suspended Hochschild cochains `F` of the zigzag algebra

```text
Λ(F) = ∑ i j, a i j (tr F(B' i j) - tr F(B i j)),
```

where `B i j` is the word of the arrows of the backtrack walk
`TauCeti.zigzagBacktrackWalk G (δ j).symm (δ i)`, namely `δ j, (δ j).symm, δ i, (δ i).symm`, and
`B' i j` that of its rotation by one step. It is the pairing, through the trace, with the
Hochschild chain `∑ i j, a i j (1 ⊗ B' i j - 1 ⊗ B i j)`. -/
noncomputable def zigzagBacktrackPairing (δ : ι → G.Dart) (a : Matrix ι ι k) :
    (ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G)
      →ₗ[k] k :=
  ∑ i, ∑ j, a i j • (zigzagTrace k G hns ∘ₗ
    (LinearMap.applyₗ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
        𝔞 (zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1)))) -
      LinearMap.applyₗ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
        𝔞 (zigzagBacktrackWalk G (δ j).symm (δ i) t)))))

/-- Unfolding the backtrack pairing. -/
theorem zigzagBacktrackPairing_apply (δ : ι → G.Dart) (a : Matrix ι ι k)
    (F : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) :
    zigzagBacktrackPairing hns δ a F = ∑ i, ∑ j, a i j *
      (zigzagTrace k G hns (F (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
          𝔞 (zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1))))) -
        zigzagTrace k G hns (F (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
          𝔞 (zigzagBacktrackWalk G (δ j).symm (δ i) t))))) := by
  simp [zigzagBacktrackPairing, LinearMap.sum_apply]

private theorem tprod_three_zero_left (b c : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![0, b, c] = 0 :=
  (PiTensorProduct.tprod k).map_coord_zero (m := ![0, b, c]) 0 rfl

private theorem tprod_three_zero_mid (a c : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![a, 0, c] = 0 :=
  (PiTensorProduct.tprod k).map_coord_zero (m := ![a, 0, c]) 1 rfl

private theorem tprod_three_zero_right (a b : nonisolatedZigzagQuotient k G) :
    PiTensorProduct.tprod k ![a, b, 0] = 0 :=
  (PiTensorProduct.tprod k).map_coord_zero (m := ![a, b, 0]) 2 rfl

private theorem arrows_mem (d₀ d₁ d₂ d₃ : G.Dart) :
    ∀ i, ![𝔞 d₀, 𝔞 d₁, 𝔞 d₂, 𝔞 d₃] i ∈ zigzagIntegerGrade k G 1 := by
  intro i
  fin_cases i <;> exact zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _

/-- The trace of a Hochschild coboundary on the rotated backtrack word
`e.symm, d, d.symm, e`, for distinct darts `d` and `e` with head `v`. -/
private theorem trace_hochschildDifferential_rotate
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) {d e : G.Dart} (hde : d ≠ e) {v : V} (hd : d.snd = v) :
    zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm, 𝔞 e]))) =
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e.symm, zigzagVolume k G v, 𝔞 e]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm])) * 𝔞 e) -
        zigzagTrace k G hns (𝔞 e.symm * φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 e]))) := by
  rw [zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod hφ _
    (arrows_mem e.symm d d.symm e)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hdd : 𝔞 d * 𝔞 d.symm = zigzagVolume k G v := by
    rw [zigzagMk_ofArrow_mul_ofArrow_symm, hd]
  rw [zigzagMk_ofArrow_mul_ofArrow_of_ne k G (d := e.symm) (e := d) (by simpa using hde), hdd,
    zigzagMk_ofArrow_mul_ofArrow_of_ne k G (d := d.symm) (e := e) (by simpa using hde.symm),
    tprod_three_zero_left, tprod_three_zero_right]
  simp only [map_zero, zero_add, add_zero, map_sub]

/-- The trace of a Hochschild coboundary on the backtrack word `e, e.symm, d, d.symm`, for
distinct darts `d` and `e` with head `v`. -/
private theorem trace_hochschildDifferential_backtrack
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) {d e : G.Dart} (hde : d ≠ e) {v : V} (hd : d.snd = v)
    (he : e.snd = v) :
    zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, 𝔞 d, 𝔞 d.symm]))) =
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![zigzagVolume k G v, 𝔞 d, 𝔞 d.symm]))) +
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, zigzagVolume k G v]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, 𝔞 d])) * 𝔞 d.symm) -
        zigzagTrace k G hns (𝔞 e * φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm]))) := by
  rw [zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod hφ _
    (arrows_mem e e.symm d d.symm)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hdd : 𝔞 d * 𝔞 d.symm = zigzagVolume k G v := by
    rw [zigzagMk_ofArrow_mul_ofArrow_symm, hd]
  have hee : 𝔞 e * 𝔞 e.symm = zigzagVolume k G v := by
    rw [zigzagMk_ofArrow_mul_ofArrow_symm, he]
  rw [hee, zigzagMk_ofArrow_mul_ofArrow_of_ne k G (d := e.symm) (e := d) (by simpa using hde), hdd,
    tprod_three_zero_mid]
  simp only [map_zero, add_zero, map_sub, map_add]

/-- The arrows of a rotated backtrack walk. -/
private theorem arrows_zigzagBacktrackWalk_rotate (d e : G.Dart) :
    (fun t ↦ 𝔞 (zigzagBacktrackWalk G e.symm d (t + 1))) = ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm, 𝔞 e] := by
  funext t
  fin_cases t <;> exact congrArg (fun d : G.Dart ↦ 𝔞 d) (by simp [zigzagBacktrackWalk_def])

/-- The arrows of a backtrack walk. -/
private theorem arrows_zigzagBacktrackWalk (d e : G.Dart) :
    (fun t ↦ 𝔞 (zigzagBacktrackWalk G e.symm d t)) = ![𝔞 e, 𝔞 e.symm, 𝔞 d, 𝔞 d.symm] := by
  funext t
  fin_cases t <;> exact congrArg (fun d : G.Dart ↦ 𝔞 d) (by simp [zigzagBacktrackWalk_def])

/-- **The backtrack pairing vanishes on Hochschild coboundaries.** Let `δ i` be pairwise distinct
darts with a common head, and let `a` be a symmetric matrix with zero diagonal whose rows sum to
zero. Then the backtrack pairing vanishes on the Hochschild differential of every suspended cochain
of degree zero. -/
theorem zigzagBacktrackPairing_hochschildDifferential_eq_zero {δ : ι → G.Dart}
    (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) {a : Matrix ι ι k}
    (ha : a.IsSymm) (ha₀ : ∀ i, a i i = 0) (ha₁ : ∀ i, ∑ j, a i j = 0)
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    zigzagBacktrackPairing hns δ a ((𝒵).hochschildDifferential 0 φ) = 0 := by
  rw [zigzagBacktrackPairing_apply]
  simp only [arrows_zigzagBacktrackWalk_rotate, arrows_zigzagBacktrackWalk]
  set tr := zigzagTrace k G hns
  set x := zigzagVolume k G v
  -- The terms which survive once the trace has been used to move the outer arrows across:
  -- `A j` and `B i` contain the volume class, `C i j` comes from an end of a word.
  set A : ι → k := fun j ↦ tr (φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![𝔞 (δ j).symm, x, 𝔞 (δ j)]))) -
    tr (φ (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k ![𝔞 (δ j), 𝔞 (δ j).symm, x])))
  set B : ι → k := fun i ↦ tr (φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![x, 𝔞 (δ i), 𝔞 (δ i).symm])))
  set C : ι → ι → k := fun i j ↦ tr (𝔞 (δ j).symm * φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![𝔞 (δ i), 𝔞 (δ i).symm, 𝔞 (δ j)])))
  have key (i j : ι) :
      a i j * (tr ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 (δ j).symm, 𝔞 (δ i), 𝔞 (δ i).symm, 𝔞 (δ j)]))) -
        tr ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 (δ j), 𝔞 (δ j).symm, 𝔞 (δ i), 𝔞 (δ i).symm])))) =
        a i j * (A j - B i - C i j + C j i) := by
    rcases eq_or_ne i j with rfl | hij
    · rw [ha₀, zero_mul, zero_mul]
    rw [trace_hochschildDifferential_rotate hφ (hδ.ne hij) (hv i),
      trace_hochschildDifferential_backtrack hφ (hδ.ne hij) (hv i) (hv j),
      zigzagTrace_mul_comm k G hns _ (𝔞 (δ j)),
      zigzagTrace_mul_comm k G hns _ (𝔞 (δ i).symm)]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ key i j]
  -- The columns, equivalently the rows, of `a` sum to zero, and `a` is symmetric.
  have hA : ∑ i, ∑ j, a i j * A j = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, fun j i ↦ ha.apply j i, ha₁, zero_mul, Finset.sum_const_zero]
  have hB : ∑ i, ∑ j, a i j * B i = 0 := by
    simp_rw [mul_comm (a _ _), ← Finset.mul_sum, ha₁, mul_zero, Finset.sum_const_zero]
  have hC : ∑ i, ∑ j, a i j * C j i = ∑ i, ∑ j, a i j * C i j := by
    rw [Finset.sum_comm]
    simp_rw [fun j i ↦ ha.apply j i]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hB, hC]
  ring

/-- The trace of the quartic operation of a loop deformation on the arrows of four darts `w` is
the coefficient of `w`. -/
private theorem trace_obstruction_ofArrow (c : (Fin 4 → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) (w : Fin 4 → G.Dart) :
    zigzagTrace k G hns ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩
      (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t)))) = c w := by
  simp only [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [lengthProj_of_self, AInfinityAlgebra.taylor_of_tprod, AInfinityAlgebra.taylor_of_tprod,
    zigzagStrictAInfinityAlgebra_m_eq_zero (by norm_num), _root_.zero_apply, sub_zero]
  -- The suspension twists the first and third arrows, each by a sign.
  have htw : (fun i : Fin 4 ↦ (zigzagLoopAInfinityAlgebra hns c hc).grading.koszulTwist
      (((⟨4, by norm_num⟩ : {n : ℕ // 0 < n}) : ℕ) - 1 - (i : ℕ)) (𝔞 (w i))) =
      fun i ↦ (![-1, 1, -1, 1] i : k) • 𝔞 (w i) := by
    funext i
    rw [InternalGrading.koszulTwist_apply_of_mem _ (e := 1) (by
      rw [zigzagLoopAInfinityAlgebra_grading_piece]
      exact zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _)]
    fin_cases i <;> norm_num
  rw [htw, MultilinearMap.map_smul_univ, zigzagLoopAInfinityAlgebra_m_four_ofArrow,
    Fin.prod_univ_four]
  simp

/-- **The backtrack pairing of a quartic loop operation.** On the obstruction of the loop
deformation with coefficients `c`, that is on its quartic operation, the backtrack pairing is
`∑ i j, a i j (c (B' i j) - c (B i j))`, for `B i j` the backtrack walk of `(δ j).symm` and `δ i`
and `B' i j` its rotation by one step. -/
theorem zigzagBacktrackPairing_obstruction (δ : ι → G.Dart) (a : Matrix ι ι k)
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    zigzagBacktrackPairing hns δ a
        ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) =
      ∑ i, ∑ j, a i j * (c (fun t ↦ zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1)) -
        c (zigzagBacktrackWalk G (δ j).symm (δ i))) := by
  rw [zigzagBacktrackPairing_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [trace_obstruction_ofArrow c hc fun t ↦ zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1),
    trace_obstruction_ofArrow c hc (zigzagBacktrackWalk G (δ j).symm (δ i))]

omit [Fintype ι] in
/-- **Quartic loop operations are Hochschild cocycles.** The obstruction of the loop deformation
with coefficients `c`, that is its quartic operation, is a Hochschild cocycle of the strict zigzag
algebra, since the two agree up to arity three. -/
theorem hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (𝒵).hochschildDifferential 1
      ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) = 0 := by
  have hG :=
    zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading (hns := hns) c hc
  -- The loop deformation agrees with the strict zigzag algebra up to arity three.
  have hm : ∀ n, 0 < n → n ≤ 3 → (zigzagLoopAInfinityAlgebra hns c hc).m n = (𝒵).m n := by
    intro n hn hn3
    rcases eq_or_ne n 2 with rfl | h₂
    · exact zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc
    · rw [zigzagLoopAInfinityAlgebra_m_eq_zero _ _ h₂ (by omega),
        zigzagStrictAInfinityAlgebra_m_eq_zero h₂]
  exact AInfinityAlgebra.hochschildDifferential_obstruction isMinimal_zigzagStrictAInfinityAlgebra
    (fun n hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)) hG (n := 3) (by norm_num)
    fun z hz ↦ AInfinityAlgebra.taylor_apply_eq_of_forall_m_eq hG hm hz

/-- **Quartic loop operations which are not Hochschild coboundaries.** Let `δ i` be pairwise
distinct darts with a common head and `a` a symmetric matrix with zero diagonal whose rows sum to
zero. If the backtrack pairing of the coefficients `c` of a loop deformation is nonzero, its
quartic operation, a Hochschild cocycle of the strict zigzag algebra by
`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`, is not the Hochschild
differential of any suspended cochain of degree zero. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra
    {δ : ι → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v)
    {a : Matrix ι ι k} (ha : a.IsSymm) (ha₀ : ∀ i, a i i = 0) (ha₁ : ∀ i, ∑ j, a i j = 0)
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (h : ∑ i, ∑ j, a i j * (c (fun t ↦ zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1)) -
        c (zigzagBacktrackWalk G (δ j).symm (δ i))) ≠ 0) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩ := by
  rintro ⟨φ, hφ, hφc⟩
  have h0 :=
    zigzagBacktrackPairing_hochschildDifferential_eq_zero (hns := hns) hδ hv ha ha₀ ha₁ hφ
  rw [hφc, zigzagBacktrackPairing_obstruction] at h0
  exact h h0

end Pairing

/-! ### Four darts with a common head -/

section Four

/-- Weights on four darts which are symmetric, vanish on the diagonal and have zero row sums. -/
private def fourWeights : Matrix (Fin 4) (Fin 4) k :=
  !![0, -1, 0, 1; -1, 0, 1, 0; 0, 1, 0, -1; 1, 0, -1, 0]

private theorem fourWeights_isSymm : (fourWeights : Matrix (Fin 4) (Fin 4) k).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> rfl

private theorem fourWeights_diag (i : Fin 4) :
    (fourWeights : Matrix (Fin 4) (Fin 4) k) i i = 0 := by
  fin_cases i <;> rfl

private theorem fourWeights_sum (i : Fin 4) :
    ∑ j, (fourWeights : Matrix (Fin 4) (Fin 4) k) i j = 0 := by
  fin_cases i <;> simp [fourWeights, Fin.sum_univ_four]

omit [Finite V] in
/-- The rotation by one step of the backtrack walk of `e.symm` and `d`, for darts `d` and `e` with
a common head, is a closed walk: a single coefficient on it is supported on closed walks. -/
theorem fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk {d e : G.Dart}
    (h : e.snd = d.snd) (r : k) :
    ∀ w ∈ (Finsupp.single (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) r).support, ∀ i,
      (w i).fst = (w (i + 1)).snd := by
  intro w hw i
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hw)]
  simpa [add_assoc] using zigzagBacktrackWalk_fst_eq_snd (by simpa using h) 1 i

/-- **A quartic loop operation which is not a Hochschild coboundary.** Let `δ 0, …, δ 3` be four
distinct darts with a common head `v`, for instance the darts into `v` from four distinct
neighbours. The loop operation of the closed walk `(δ 3).symm, δ 0, (δ 0).symm, δ 3` (in product
order), the rotation of the backtrack walk of `(δ 3).symm` and `δ 0`, is a Hochschild cocycle of
the strict zigzag algebra
(`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`), and it is not the
Hochschild differential of any suspended cochain of degree zero. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single
    [Nontrivial k] {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V}
    (hv : ∀ i, (δ i).snd = v) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns _
            (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk
              ((hv 3).trans (hv 0).symm) (1 : k))).obstruction 𝒵 ⟨4, by norm_num⟩ := by
  classical
  refine not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra hδ hv
    fourWeights_isSymm fourWeights_diag fourWeights_sum _ _ ?_
  -- The rotated walk of `(i, j)` is that of `(0, 3)` only for `(i, j) = (0, 3)`, by comparing the
  -- second and fourth darts; no backtrack walk is, since its first dart has head `v`.
  have h₀ (i j : Fin 4) :
      Finsupp.single (fun t ↦ zigzagBacktrackWalk G (δ 3).symm (δ 0) (t + 1)) (1 : k)
        (fun t ↦ zigzagBacktrackWalk G (δ j).symm (δ i) (t + 1)) =
        if i = 0 ∧ j = 3 then 1 else 0 := by
    rw [Finsupp.single_apply]
    refine if_congr ⟨fun h ↦ ⟨hδ ?_, hδ ?_⟩, ?_⟩ rfl rfl
    · simpa [zigzagBacktrackWalk_def] using (congrFun h 1).symm
    · simpa [zigzagBacktrackWalk_def] using (congrFun h 3).symm
    · rintro ⟨rfl, rfl⟩
      rfl
  have h₁ (i j : Fin 4) :
      Finsupp.single (fun t ↦ zigzagBacktrackWalk G (δ 3).symm (δ 0) (t + 1)) (1 : k)
        (zigzagBacktrackWalk G (δ j).symm (δ i)) = 0 := by
    rw [Finsupp.single_apply, ite_eq_right_iff]
    intro h
    have h0 : (δ 3).fst = v := by
      simpa [zigzagBacktrackWalk_def, hv] using
        congrArg (fun d : G.Dart ↦ d.toProd.2) (congrFun h 0)
    exact ((δ 3).adj.ne (h0.trans (hv 3).symm)).elim
  simp [h₀, h₁, Fin.sum_univ_four, fourWeights]

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of a zigzag algebra is nonzero** when four
distinct darts of `G` have a common head, that is when some vertex has four distinct neighbours,
over every nontrivial commutative ring: some Hochschild cocycle of the strict zigzag algebra of
suspended degree one, concentrated on words of length four, is not the Hochschild differential of
a cochain of degree zero. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra [Nontrivial k]
    {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  intro hvan
  have hc := fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk
    ((hv 3).trans (hv 0).symm) (1 : k)
  obtain ⟨φ, hφ, -, hφc⟩ := AInfinityAlgebra.hochschildVanishesAt_iff.mp hvan _
    (AInfinityAlgebra.isHomogeneous_obstruction
      (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ hc) _)
    (AInfinityAlgebra.obstruction_comp_lengthProj _ _ _)
    (hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra _ hc)
  exact not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single hδ hv
    ⟨φ, hφ, hφc⟩

end Four

end TauCeti
