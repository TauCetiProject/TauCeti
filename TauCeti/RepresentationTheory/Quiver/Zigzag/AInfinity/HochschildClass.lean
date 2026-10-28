/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import TauCeti.Algebra.Homology.AInfinity.Algebra.IntrinsicFormality.Criterion
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
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
example the centre of the affine `D₄` graph, or two vertices of `G` with three distinct neighbours
each are joined by a walk of a suitable shape, for example the two branch vertices of the affine
`Dₙ` graphs for `n ≥ 5`. The class is that of the loop operation `TauCeti.zigzagLoopOperation` of
a single closed walk which goes from a neighbour of `v` to `v`, makes a detour to another neighbour
and back, and returns.

## The detecting cycle

Since `Z` is a symmetric algebra, a Hochschild cochain can be paired with a Hochschild chain by
means of the trace `TauCeti.zigzagTrace`. Fix a symmetric matrix `a` of weights on pairs of darts
which vanishes on the pairs of darts with distinct heads. Write `B d e` for the backtrack walk
`TauCeti.zigzagBacktrackWalk G e.symm d`, that is the darts `e, e.symm, d, d.symm` in product
order, and `B' d e` for its rotation `e.symm, d, d.symm, e`. The functional

```text
Λ(F) = ∑ d e, a d e (tr F(B' d e) - tr F(B d e)),
```

evaluated on the words of the corresponding arrows (`TauCeti.zigzagBacktrackPairing`), vanishes on
every Hochschild coboundary of degree zero as soon as the weights satisfy the balance condition

```text
∑ d, a d e = a e.symm e.symm    for every dart e
```

(`TauCeti.zigzagBacktrackPairing_hochschildDifferential_eq_zero`).
On a word of four arrows the Hochschild differential of a suspended cochain `φ` is

```text
δφ(x₀, x₁, x₂, x₃) = φ(x₀x₁, x₂, x₃) + φ(x₀, x₁x₂, x₃) + φ(x₀, x₁, x₂x₃)
                       - φ(x₀, x₁, x₂) x₃ - x₀ φ(x₁, x₂, x₃)
```

(`TauCeti.zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod`), and on the words
above the only nonzero products of consecutive arrows are backtracks, which are volume classes. For
distinct darts `d` and `e` with head `v`, the outer terms of `B' d e` cancel against those of
`B d e` and `B e d` by the trace property `tr(xy) = tr(yx)` and the symmetry of `a`, leaving terms
containing the volume class `x_v`. For `d = e` the two words are the double backtracks
`d.symm, d, d.symm, d` and `d, d.symm, d, d.symm`, which leave terms containing the volume classes
at both ends of `d`; this is why the diagonal weight of `e.symm` enters the balance condition at
`e`. The terms containing volume classes then cancel by the balance condition.

The balance condition holds in two situations.

* Four distinct darts `δ i` with a common head, with the weights

  ```text
  a = [ 0 -1  0  1]
      [-1  0  1  0]
      [ 0  1  0 -1]
      [ 1  0 -1  0]
  ```

  on the pairs `(δ i, δ j)`, which have zero diagonal and zero row sums.
* Distinct darts `d` and `e` with a common head `v`, joined by a non-backtracking walk of darts
  `f 0, …, f n` to distinct darts `d'` and `e'` with a common head `w`. The weights are `1` on the
  pair `{d, e}` and `-1` on the pairs `{d, (f 0).symm}` and `{e, (f 0).symm}`, then `2 (-1)^t` on
  the diagonal entry of `(f t).symm` and on the pair `{f t, (f (t + 1)).symm}`, and finally
  `(-1)^(n + 1)` times the weights `1, -1, -1` on the pairs `{d', e'}`, `{d', f n}`, `{e', f n}`.
  The balance condition along the walk is a telescoping identity.

On the other hand `Λ` pairs the obstruction of the loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` with coefficients `c`, its operation `m₄`, to
`∑ d e, a d e (c (B' d e) - c (B d e))` (`TauCeti.zigzagBacktrackPairing_obstruction`). For the
single walk `B' d e` with coefficient one, for distinct darts `d` and `e`, this is `a d e`, which
is `1` for the pair `(δ 0, δ 3)` in the first situation and the pair `(d, e)` in the second. So its
loop operation, a Hochschild cocycle
(`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`), is not a coboundary
(`TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single` and
`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk`),
and `HH^{4, -2}(Z, Z) ≠ 0`. In particular this holds for the affine `Dₙ` graphs with `n ≥ 5`
(`TauCeti.not_hochschildVanishesAt_four_affineD`), as it does for the affine `D₄` graph.

This is consistent with `TauCeti.zigzagBacktrackOperation_coboundary`, by which the sum of the loop
operations of a backtrack walk `B d e` and of its rotation `B' d e` is a coboundary: `Λ` takes
opposite values on them. In particular the four rotations of one such walk with equal coefficients,
as in Liu--Wang's affine `D₄` example, have a coboundary as their sum, while a single rotation does
not.

Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` therefore does not
apply to such zigzag algebras. That a nonzero obstruction class gives a minimal
`A∞` structure which is not `A∞` isomorphic to the strict one is not addressed here: an `A∞`
isomorphism may have a nonzero quadratic component, which changes the quartic operation by more
than a coboundary.

## Main definitions

* `TauCeti.zigzagBacktrackPairing`: the functional `Λ` on suspended Hochschild cochains.

## Main results

* `TauCeti.zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod`: the Hochschild
  differential of a degree-zero suspended cochain on a word of four letters of path length one.
* `TauCeti.zigzagBacktrackPairing_hochschildDifferential_eq_zero`: `Λ` vanishes on coboundaries
  when its weights satisfy the balance condition.
* `TauCeti.zigzagBacktrackPairing_obstruction`: the value of `Λ` on the quartic operation of a loop
  deformation.
* `TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`: the quartic operation of
  a loop deformation is a Hochschild cocycle.
* `TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra` and
  `TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single`:
  quartic loop operations which are not Hochschild coboundaries.
* `not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk`:
  the same at a vertex joined by a walk to another vertex, both with three distinct neighbours.
* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra` and
  `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_walk`:
  `HH^{4, -2}(Z, Z) ≠ 0` when a vertex of `G` has four distinct neighbours, or two vertices with
  three distinct neighbours each are joined by a suitable walk.
* `TauCeti.not_hochschildVanishesAt_four_affineD`: `HH^{4, -2}(Z, Z) ≠ 0` for the affine `Dₙ`
  graphs with `n ≥ 5`.

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

variable [Fintype G.Dart]

variable (hns) in
/-- **The backtrack pairing** with weights `a d e` on pairs of darts: the linear functional on
suspended Hochschild cochains `F` of the zigzag algebra

```text
Λ(F) = ∑ d e, a d e (tr F(B' d e) - tr F(B d e)),
```

where `B d e` is the word of the arrows of the backtrack walk
`TauCeti.zigzagBacktrackWalk G e.symm d`, namely `e, e.symm, d, d.symm`, and `B' d e` that of its
rotation by one step, namely `e.symm, d, d.symm, e`. It is the pairing, through the trace, with the
Hochschild chain `∑ d e, a d e (1 ⊗ B' d e - 1 ⊗ B d e)`. -/
noncomputable def zigzagBacktrackPairing (a : Matrix G.Dart G.Dart k) :
    (ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G)
      →ₗ[k] k :=
  ∑ d, ∑ e, a d e • (zigzagTrace k G hns ∘ₗ
    (LinearMap.applyₗ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
        𝔞 (zigzagBacktrackWalk G e.symm d (t + 1)))) -
      LinearMap.applyₗ (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
        𝔞 (zigzagBacktrackWalk G e.symm d t)))))

/-- Unfolding the backtrack pairing. -/
theorem zigzagBacktrackPairing_apply (a : Matrix G.Dart G.Dart k)
    (F : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) :
    zigzagBacktrackPairing hns a F = ∑ d, ∑ e, a d e *
      (zigzagTrace k G hns (F (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
          𝔞 (zigzagBacktrackWalk G e.symm d (t + 1))))) -
        zigzagTrace k G hns (F (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦
          𝔞 (zigzagBacktrackWalk G e.symm d t))))) := by
  simp [zigzagBacktrackPairing, LinearMap.sum_apply]

end Pairing

section Coboundary

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

/-- The arrow of the reverse of the reverse of a dart. -/
private theorem arrow_symm_symm (d : G.Dart) : 𝔞 d.symm.symm = 𝔞 d :=
  congrArg (fun d : G.Dart ↦ 𝔞 d) d.symm_symm

/-- The trace of a Hochschild coboundary on the double backtrack word `d, d.symm, d, d.symm`,
whose products of consecutive arrows are the volume classes at the head and at the tail of `d`. -/
private theorem trace_hochschildDifferential_double
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) (d : G.Dart) :
    zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 d, 𝔞 d.symm]))) =
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![zigzagVolume k G d.snd, 𝔞 d, 𝔞 d.symm]))) +
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, zigzagVolume k G d.fst, 𝔞 d.symm]))) +
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, zigzagVolume k G d.snd]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 d])) * 𝔞 d.symm) -
        zigzagTrace k G hns (𝔞 d * φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d.symm, 𝔞 d, 𝔞 d.symm]))) := by
  rw [zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod hφ _
    (arrows_mem d d.symm d d.symm)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hd : 𝔞 d * 𝔞 d.symm = zigzagVolume k G d.snd := zigzagMk_ofArrow_mul_ofArrow_symm k G d
  have hd' : 𝔞 d.symm * 𝔞 d = zigzagVolume k G d.fst := by
    have h := zigzagMk_ofArrow_mul_ofArrow_symm k G d.symm
    rw [arrow_symm_symm] at h
    rw [h]
    simp
  rw [hd, hd']
  simp only [map_add, map_sub]

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

/-- The difference of the traces of a Hochschild coboundary on the rotated backtrack word of
`d` and `e` and on the backtrack word, for distinct darts with a common head. -/
private theorem trace_hochschildDifferential_rotate_sub_backtrack
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) {d e : G.Dart} (hde : d ≠ e) (h : d.snd = e.snd) :
    zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm, 𝔞 e]))) -
      zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, 𝔞 d, 𝔞 d.symm]))) =
      (zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e.symm, zigzagVolume k G e.snd, 𝔞 e]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, zigzagVolume k G e.snd])))) -
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![zigzagVolume k G d.snd, 𝔞 d, 𝔞 d.symm]))) -
      zigzagTrace k G hns (𝔞 e.symm * φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 e]))) +
      zigzagTrace k G hns (𝔞 d.symm * φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, 𝔞 d]))) := by
  have hvol : zigzagVolume k G e.snd = zigzagVolume k G d.snd := by rw [h]
  rw [trace_hochschildDifferential_rotate hφ hde h,
    trace_hochschildDifferential_backtrack hφ hde rfl h.symm, hvol,
    zigzagTrace_mul_comm k G hns _ (𝔞 e), zigzagTrace_mul_comm k G hns _ (𝔞 d.symm)]
  ring

/-- The difference of the traces of a Hochschild coboundary on the double backtrack words of
`d.symm` and of `d`. -/
private theorem trace_hochschildDifferential_double_symm_sub
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) (d : G.Dart) :
    zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 d.symm, 𝔞 d, 𝔞 d.symm, 𝔞 d]))) -
      zigzagTrace k G hns ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
        (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 d, 𝔞 d.symm]))) =
      (zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d.symm, zigzagVolume k G d.snd, 𝔞 d]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, zigzagVolume k G d.snd])))) -
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![zigzagVolume k G d.snd, 𝔞 d, 𝔞 d.symm]))) +
      zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![zigzagVolume k G d.symm.snd, 𝔞 d.symm, 𝔞 d.symm.symm]))) -
      (zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d.symm.symm, zigzagVolume k G d.symm.snd, 𝔞 d.symm]))) -
        zigzagTrace k G hns (φ (of k _ ⟨3, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 d.symm, 𝔞 d.symm.symm, zigzagVolume k G d.symm.snd])))) := by
  have hsnd : zigzagVolume k G d.symm.snd = zigzagVolume k G d.fst := by simp
  have hfst : zigzagVolume k G d.symm.fst = zigzagVolume k G d.snd := by simp
  have h := trace_hochschildDifferential_double hφ d.symm
  rw [arrow_symm_symm] at h
  rw [h, trace_hochschildDifferential_double hφ d, arrow_symm_symm, hsnd, hfst,
    zigzagTrace_mul_comm k G hns _ (𝔞 d), zigzagTrace_mul_comm k G hns _ (𝔞 d.symm)]
  ring

end Coboundary

section Vanishing

variable [Fintype G.Dart]

/-- **The backtrack pairing vanishes on Hochschild coboundaries.** Let `a` be a symmetric matrix of
weights on pairs of darts which vanishes on pairs of darts with distinct heads, and whose column
sums satisfy the balance condition `∑ d, a d e = a e.symm e.symm` at every dart `e`. Then the
backtrack pairing with weights `a` vanishes on the Hochschild differential of every suspended
cochain of degree zero. -/
theorem zigzagBacktrackPairing_hochschildDifferential_eq_zero {a : Matrix G.Dart G.Dart k}
    (ha : a.IsSymm) (hhead : ∀ d e, d.snd ≠ e.snd → a d e = 0)
    (hbal : ∀ e, ∑ d, a d e = a e.symm e.symm)
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    zigzagBacktrackPairing hns a ((𝒵).hochschildDifferential 0 φ) = 0 := by
  classical
  rw [zigzagBacktrackPairing_apply]
  simp only [arrows_zigzagBacktrackWalk_rotate, arrows_zigzagBacktrackWalk]
  set tr := zigzagTrace k G hns
  -- The terms which survive once the trace has been used to move the outer arrows across:
  -- `A e` and `B d` contain a volume class, `C d e` comes from an end of a word.
  set A : G.Dart → k := fun e ↦ tr (φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![𝔞 e.symm, zigzagVolume k G e.snd, 𝔞 e]))) -
    tr (φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, zigzagVolume k G e.snd])))
  set B : G.Dart → k := fun d ↦ tr (φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![zigzagVolume k G d.snd, 𝔞 d, 𝔞 d.symm])))
  set C : G.Dart → G.Dart → k := fun d e ↦ tr (𝔞 e.symm * φ (of k _ ⟨3, by norm_num⟩
      (PiTensorProduct.tprod k ![𝔞 d, 𝔞 d.symm, 𝔞 e])))
  have key (d e : G.Dart) :
      a d e * (tr ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e.symm, 𝔞 d, 𝔞 d.symm, 𝔞 e]))) -
        tr ((𝒵).hochschildDifferential 0 φ (of k _ ⟨4, by norm_num⟩
          (PiTensorProduct.tprod k ![𝔞 e, 𝔞 e.symm, 𝔞 d, 𝔞 d.symm])))) =
        a d e * (A e - B d - C d e + C e d) +
          if d = e then a d d * (B d.symm - A d.symm) else 0 := by
    rcases eq_or_ne d e with rfl | hde
    · simp only [↓reduceIte]
      rw [trace_hochschildDifferential_double_symm_sub hφ d]
      ring
    simp only [hde, ↓reduceIte, add_zero]
    by_cases h : d.snd = e.snd
    · rw [trace_hochschildDifferential_rotate_sub_backtrack hφ hde h]
    · rw [hhead d e h, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ key d e]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Reversing darts permutes them.
  have hrev (g : G.Dart → k) : ∑ d : G.Dart, g d.symm = ∑ d, g d :=
    Equiv.sum_comp (Function.Involutive.toPerm (SimpleGraph.Dart.symm (G := G))
      SimpleGraph.Dart.symm_involutive) g
  -- The balance condition, on columns and, by symmetry, on rows.
  have hA : ∑ d, ∑ e, a d e * A e = ∑ d, a d d * A d.symm := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hbal]
    rw [← hrev fun e ↦ a e.symm e.symm * A e]
    simp only [SimpleGraph.Dart.symm_symm]
  have hB : ∑ d, ∑ e, a d e * B d = ∑ d, a d d * B d.symm := by
    simp_rw [← Finset.sum_mul]
    have hrow (d : G.Dart) : ∑ e, a d e = a d.symm d.symm := by
      rw [← hbal]
      exact Finset.sum_congr rfl fun e _ ↦ (ha.apply d e).symm
    simp_rw [hrow]
    rw [← hrev fun e ↦ a e.symm e.symm * B e]
    simp only [SimpleGraph.Dart.symm_symm]
  have hC : ∑ d, ∑ e, a d e * C e d = ∑ d, ∑ e, a d e * C d e := by
    rw [Finset.sum_comm]
    simp_rw [fun d e ↦ ha.apply d e]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hB, hC]
  ring

omit [Fintype G.Dart] in
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
`∑ d e, a d e (c (B' d e) - c (B d e))`, for `B d e` the backtrack walk of `e.symm` and `d` and
`B' d e` its rotation by one step. -/
theorem zigzagBacktrackPairing_obstruction (a : Matrix G.Dart G.Dart k)
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    zigzagBacktrackPairing hns a
        ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) =
      ∑ d, ∑ e, a d e * (c (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) -
        c (zigzagBacktrackWalk G e.symm d)) := by
  rw [zigzagBacktrackPairing_apply]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  rw [trace_obstruction_ofArrow c hc fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1),
    trace_obstruction_ofArrow c hc (zigzagBacktrackWalk G e.symm d)]

omit [Fintype G.Dart] in
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
    · ext x
      rw [zigzagLoopAInfinityAlgebra_m_two_apply, zigzagStrictAInfinityAlgebra_m_two_apply]
    · rw [zigzagLoopAInfinityAlgebra_m_eq_zero _ _ h₂ (by omega),
        zigzagStrictAInfinityAlgebra_m_eq_zero h₂]
  exact AInfinityAlgebra.hochschildDifferential_obstruction isMinimal_zigzagStrictAInfinityAlgebra
    (fun n hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)) hG (n := 3) (by norm_num)
    fun z hz ↦ AInfinityAlgebra.taylor_apply_eq_of_forall_m_eq hG hm hz

/-- **Quartic loop operations which are not Hochschild coboundaries.** Let `a` be a symmetric
matrix of weights on pairs of darts which vanishes on pairs of darts with distinct heads and
satisfies the balance condition `∑ d, a d e = a e.symm e.symm`. If the backtrack pairing of the
coefficients `c` of a loop deformation is nonzero, its quartic operation, a Hochschild cocycle of
the strict zigzag algebra by
`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`, is not the Hochschild
differential of any suspended cochain of degree zero. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra
    {a : Matrix G.Dart G.Dart k} (ha : a.IsSymm) (hhead : ∀ d e, d.snd ≠ e.snd → a d e = 0)
    (hbal : ∀ e, ∑ d, a d e = a e.symm e.symm)
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (h : ∑ d, ∑ e, a d e * (c (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) -
        c (zigzagBacktrackWalk G e.symm d)) ≠ 0) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩ := by
  rintro ⟨φ, hφ, hφc⟩
  have h0 := zigzagBacktrackPairing_hochschildDifferential_eq_zero (hns := hns) ha hhead hbal hφ
  rw [hφc, zigzagBacktrackPairing_obstruction] at h0
  exact h h0

omit [Finite V] [Fintype G.Dart] in
/-- The rotation by one step of the backtrack walk of `e.symm` and `d`, for darts `d` and `e` with
a common head, is a closed walk: a single coefficient on it is supported on closed walks. -/
theorem fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk {d e : G.Dart}
    (h : e.snd = d.snd) (r : k) :
    ∀ w ∈ (Finsupp.single (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) r).support, ∀ i,
      (w i).fst = (w (i + 1)).snd := by
  intro w hw i
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hw)]
  simpa [add_assoc] using zigzagBacktrackWalk_fst_eq_snd (by simpa using h) 1 i

omit [Finite V] in
/-- On the coefficient one on the rotated backtrack walk of `e₀.symm` and `d₀`, for distinct
darts, the sum computing the backtrack pairing of a quartic loop operation is the weight
`a d₀ e₀`: no other rotated backtrack walk, and no backtrack walk, is this walk. -/
private theorem sum_mul_single_rotate_zigzagBacktrackWalk (a : Matrix G.Dart G.Dart k)
    {d₀ e₀ : G.Dart} (h : d₀ ≠ e₀) :
    ∑ d, ∑ e, a d e *
      (Finsupp.single (fun t ↦ zigzagBacktrackWalk G e₀.symm d₀ (t + 1)) (1 : k)
          (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) -
        Finsupp.single (fun t ↦ zigzagBacktrackWalk G e₀.symm d₀ (t + 1)) (1 : k)
          (zigzagBacktrackWalk G e.symm d)) = a d₀ e₀ := by
  classical
  -- The rotated walk of `(d, e)` is that of `(d₀, e₀)` only for `(d, e) = (d₀, e₀)`, by comparing
  -- the second and fourth darts; no backtrack walk is, since its first two darts are reverse.
  have h₀ (d e : G.Dart) :
      Finsupp.single (fun t ↦ zigzagBacktrackWalk G e₀.symm d₀ (t + 1)) (1 : k)
        (fun t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) = if d = d₀ ∧ e = e₀ then 1 else 0 := by
    rw [Finsupp.single_apply]
    refine if_congr ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩ rfl rfl
    · simpa [zigzagBacktrackWalk_def] using (congrFun h 1).symm
    · simpa [zigzagBacktrackWalk_def] using (congrFun h 3).symm
    · rintro ⟨rfl, rfl⟩
      rfl
  have h₁ (d e : G.Dart) :
      Finsupp.single (fun t ↦ zigzagBacktrackWalk G e₀.symm d₀ (t + 1)) (1 : k)
        (zigzagBacktrackWalk G e.symm d) = 0 := by
    rw [Finsupp.single_apply, ite_eq_right_iff]
    intro h'
    have h0 : e₀.symm = e := by simpa [zigzagBacktrackWalk_def] using congrFun h' 0
    have h1 : d₀ = e.symm := by simpa [zigzagBacktrackWalk_def] using congrFun h' 1
    exact (h (by rw [h1, ← h0, SimpleGraph.Dart.symm_symm])).elim
  simp [h₀, h₁, ite_and]

end Vanishing

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

private theorem fourWeights_sum (j : Fin 4) :
    ∑ i, (fourWeights : Matrix (Fin 4) (Fin 4) k) i j = 0 := by
  fin_cases j <;> simp [fourWeights, Fin.sum_univ_four]

/-- The weights `fourWeights` on four darts `δ i`. -/
private def fourDartWeights [DecidableEq V] (δ : Fin 4 → G.Dart) : Matrix G.Dart G.Dart k :=
  ∑ i, ∑ j, Matrix.single (δ i) (δ j) (fourWeights i j)

omit [Finite V] in
private theorem fourDartWeights_apply [DecidableEq V] {δ : Fin 4 → G.Dart}
    (hδ : Function.Injective δ) (i j : Fin 4) :
    (fourDartWeights δ : Matrix G.Dart G.Dart k) (δ i) (δ j) = fourWeights i j := by
  simp [fourDartWeights, Matrix.sum_apply, Matrix.single_apply, hδ.eq_iff, ite_and]

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
  have := Fintype.ofFinite V
  refine not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra
    (a := fourDartWeights δ) ?_ ?_ ?_ _ _ ?_
  · simp only [Matrix.IsSymm, fourDartWeights, Matrix.transpose_sum, Matrix.transpose_single]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [(fourWeights_isSymm (k := k)).apply]
  · intro d e hde
    simp only [fourDartWeights, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦
      Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, rfl⟩
    exact hde ((hv i).trans (hv j).symm)
  · -- Both sides vanish: the columns of the weights sum to zero, and their diagonal vanishes.
    intro e
    have hL : ∑ d, (fourDartWeights δ : Matrix G.Dart G.Dart k) d e = 0 := by
      simp only [fourDartWeights, Matrix.sum_apply]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := Finset.univ (α := G.Dart)), Matrix.single_apply, ite_and,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases h : δ j = e
      · simp only [h, ite_true, fourWeights_sum]
      · simp only [h, ite_false, Finset.sum_const_zero]
    rw [hL]
    simp only [fourDartWeights, Matrix.sum_apply]
    refine (Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_).symm
    rw [Matrix.single_apply]
    split_ifs with h
    · rw [hδ (h.1.trans h.2.symm), fourWeights_diag]
    · rfl
  · rw [sum_mul_single_rotate_zigzagBacktrackWalk _ (hδ.ne (by decide)),
      fourDartWeights_apply hδ]
    simp [fourWeights]

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

/-! ### Two branch vertices joined by a walk -/

section Branch

variable [DecidableEq V]

omit [Finite V] in
/-- A matrix with a single nonzero entry, on a pair of darts with a common head, vanishes on the
pairs of darts with distinct heads. -/
private theorem single_apply_eq_zero_of_snd_ne {x y : G.Dart} (h : x.snd = y.snd) (r : k)
    {d e : G.Dart} (hde : d.snd ≠ e.snd) : Matrix.single x y r d e = 0 :=
  Matrix.single_apply_of_ne _ _ _ _ _ fun ⟨hx, hy⟩ ↦ hde (by rw [← hx, ← hy, h])

/-- The symmetric weight one on a pair of darts. -/
private def pairWeights (x y : G.Dart) : Matrix G.Dart G.Dart k :=
  Matrix.single x y 1 + Matrix.single y x 1

omit [Finite V] in
private theorem pairWeights_isSymm (x y : G.Dart) :
    (pairWeights x y : Matrix G.Dart G.Dart k).IsSymm := by
  simp only [Matrix.IsSymm, pairWeights, Matrix.transpose_add, Matrix.transpose_single, add_comm]

omit [Finite V] in
private theorem pairWeights_apply_eq_zero_of_snd_ne {x y : G.Dart} (h : x.snd = y.snd)
    {d e : G.Dart} (hde : d.snd ≠ e.snd) : (pairWeights x y : Matrix G.Dart G.Dart k) d e = 0 := by
  rw [pairWeights, Matrix.add_apply, single_apply_eq_zero_of_snd_ne h _ hde,
    single_apply_eq_zero_of_snd_ne h.symm _ hde, add_zero]

variable [Fintype G.Dart]

omit [Finite V] in
/-- The failure of the balance condition `∑ d, a d e = a e.symm e.symm` at each dart `e`. -/
private def balanceDefect : Matrix G.Dart G.Dart k →ₗ[k] G.Dart → k where
  toFun a e := ∑ d, a d e - a e.symm e.symm
  map_add' a b := by
    ext e
    simp only [Matrix.add_apply, Finset.sum_add_distrib, Pi.add_apply]
    ring
  map_smul' r a := by
    ext e
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply, Pi.smul_apply]
    ring

omit [Finite V] [DecidableEq V] in
private theorem balanceDefect_apply (a : Matrix G.Dart G.Dart k) (e : G.Dart) :
    balanceDefect a e = ∑ d, a d e - a e.symm e.symm :=
  rfl

omit [Finite V] in
private theorem balanceDefect_single_of_ne {x y : G.Dart} (h : x ≠ y) (r : k) :
    balanceDefect (Matrix.single x y r) = Pi.single y r := by
  ext e
  rw [balanceDefect_apply,
    Matrix.single_apply_of_ne _ _ _ _ _ fun h' ↦ h (h'.1.trans h'.2.symm), sub_zero]
  simp [Matrix.single_apply, ite_and, Pi.single_apply, eq_comm]

omit [Finite V] in
private theorem balanceDefect_single_self (x : G.Dart) (r : k) :
    balanceDefect (Matrix.single x x r) = Pi.single x r - Pi.single x.symm r := by
  ext e
  have h : x = e.symm ↔ e = x.symm := by
    constructor <;> rintro rfl <;> simp
  simp only [balanceDefect_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, and_self, h, Pi.sub_apply, Pi.single_apply, @eq_comm _ x e]

omit [Finite V] in
private theorem balanceDefect_pairWeights {x y : G.Dart} (h : x ≠ y) :
    balanceDefect (pairWeights x y : Matrix G.Dart G.Dart k) = Pi.single x 1 + Pi.single y 1 := by
  rw [pairWeights, map_add, balanceDefect_single_of_ne h, balanceDefect_single_of_ne h.symm,
    add_comm]

/-- The weights detecting a quartic Hochschild class at a vertex `d.snd` with three distinct
neighbours, joined by the walk of darts `f` to another vertex with three distinct neighbours: the
backtracks at the two ends, and alternating weights along the walk. -/
private def branchWeights (d e d' e' : G.Dart) {n : ℕ} (f : Fin (n + 1) → G.Dart) :
    Matrix G.Dart G.Dart k :=
  pairWeights d e - pairWeights d (f 0).symm - pairWeights e (f 0).symm +
    ∑ t : Fin (n + 1), (2 * (-1) ^ (t : ℕ) : k) • Matrix.single (f t).symm (f t).symm 1 +
    ∑ t : Fin n, (2 * (-1) ^ (t : ℕ) : k) • pairWeights (f t.castSucc) (f t.succ).symm +
    ((-1) ^ (n + 1) : k) • (pairWeights d' e' - pairWeights d' (f (Fin.last n)) -
      pairWeights e' (f (Fin.last n)))

variable {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart}

omit [Finite V] [Fintype G.Dart] in
private theorem branchWeights_isSymm :
    (branchWeights d e d' e' f : Matrix G.Dart G.Dart k).IsSymm :=
  Matrix.IsSymm.ext fun x y ↦ by
    simp only [branchWeights, pairWeights, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.single_apply, and_comm, smul_add, Finset.sum_add_distrib]
    ring

omit [Finite V] [Fintype G.Dart] in
private theorem branchWeights_apply_eq_zero_of_snd_ne (hed : e.snd = d.snd)
    (hf₀ : (f 0).fst = d.snd) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    {x y : G.Dart} (hxy : x.snd ≠ y.snd) :
    (branchWeights d e d' e' f : Matrix G.Dart G.Dart k) x y = 0 := by
  simp only [branchWeights, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply]
  rw [pairWeights_apply_eq_zero_of_snd_ne hed.symm hxy,
    pairWeights_apply_eq_zero_of_snd_ne hf₀.symm hxy, pairWeights_apply_eq_zero_of_snd_ne
      (hed.trans hf₀.symm) hxy,
    Finset.sum_eq_zero fun t _ ↦ by rw [single_apply_eq_zero_of_snd_ne rfl _ hxy, smul_zero],
    Finset.sum_eq_zero fun t _ ↦ by
      rw [pairWeights_apply_eq_zero_of_snd_ne ((hf t).trans (by simp)) hxy, smul_zero],
    pairWeights_apply_eq_zero_of_snd_ne (hd'.trans he'.symm) hxy,
    pairWeights_apply_eq_zero_of_snd_ne hd' hxy, pairWeights_apply_eq_zero_of_snd_ne he' hxy]
  simp

omit [Finite V] in
private theorem balanceDefect_branchWeights (hde : d ≠ e) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hde' : d' ≠ e')
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    balanceDefect (branchWeights d e d' e' f : Matrix G.Dart G.Dart k) = 0 := by
  simp only [branchWeights, map_add, map_sub, map_sum, map_smul, balanceDefect_pairWeights hde,
    balanceDefect_pairWeights hdf, balanceDefect_pairWeights hef, balanceDefect_single_self,
    balanceDefect_pairWeights (hf' _), balanceDefect_pairWeights hde',
    balanceDefect_pairWeights hdf', balanceDefect_pairWeights hef', smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (f := fun t : Fin (n + 1) ↦
      (2 * (-1) ^ (t : ℕ) : k) • (Pi.single (f t).symm 1 : G.Dart → k)),
    Fin.sum_univ_castSucc (f := fun t : Fin (n + 1) ↦
      (2 * (-1) ^ (t : ℕ) : k) • (Pi.single (f t).symm.symm 1 : G.Dart → k))]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, SimpleGraph.Dart.symm_symm,
    pow_succ, pow_zero]
  -- The weights along the walk alternate in sign.
  have h (g : Fin n → G.Dart → k) : ∑ t : Fin n, (2 * ((-1) ^ (t : ℕ) * -1) : k) • g t =
      -∑ t : Fin n, (2 * (-1) ^ (t : ℕ) : k) • g t := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ ↦ by rw [← neg_smul]; ring_nf
  rw [h]
  module

omit [Finite V] [Fintype G.Dart] in
private theorem branchWeights_apply_self (hde : d ≠ e) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hfd : ∀ t, (f t).snd ≠ d.snd) (hd' : d'.snd = (f (Fin.last n)).snd)
    (he' : e'.snd = (f (Fin.last n)).snd) :
    (branchWeights d e d' e' f : Matrix G.Dart G.Dart k) d e = 1 := by
  -- Only the backtrack weight at `d.snd` sees the pair `(d, e)`; every other weight lives at
  -- another vertex or on another pair.
  have h₁ (t : Fin (n + 1)) : f t ≠ d := fun h ↦ hfd t (congrArg (·.snd) h)
  have h₂ (t : Fin n) : (f t.succ).symm ≠ d := fun h ↦
    hfd t.castSucc ((hf t).trans (by rw [← h]; simp))
  have h₃ (t : Fin (n + 1)) : ¬((f t).symm = d ∧ (f t).symm = e) := fun h ↦
    hde (h.1.symm.trans h.2)
  have h₄ : d' ≠ d := fun h ↦ hfd (Fin.last n) (hd'.symm.trans (congrArg (·.snd) h))
  have h₅ : e' ≠ d := fun h ↦ hfd (Fin.last n) (he'.symm.trans (congrArg (·.snd) h))
  simp [branchWeights, pairWeights, Matrix.sum_apply, hde.symm, hdf.symm, hef.symm, h₁, h₂, h₃,
    h₄, h₅]

end Branch

/-- **A quartic loop operation at a vertex joined by a walk to another branch vertex which is not a
Hochschild coboundary.** Let `d` and `e` be distinct darts with a common head `v`, and let the
non-backtracking walk of darts `f 0, …, f n` lead from `v`, along neither `d.symm` nor `e.symm`,
to a vertex `w` without returning to `v`. Let `d'` and `e'` be distinct darts with head `w`, both
distinct from the last dart `f n` of the walk. Thus `v` and `w` each have three distinct neighbours,
as do the two branch vertices of the affine `Dₙ` graphs for `n ≥ 5`. The loop operation of the
closed walk `e.symm, d, d.symm, e` (in product order), the rotation of the backtrack walk of
`e.symm` and `d`, is a Hochschild cocycle of the strict zigzag algebra
(`TauCeti.hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra`), and it is not the
Hochschild differential of any suspended cochain of degree zero. -/
theorem not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk
    [Nontrivial k] {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns _
            (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk hed (1 : k))).obstruction
            𝒵 ⟨4, by norm_num⟩ := by
  classical
  have := Fintype.ofFinite V
  refine not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra
    (a := branchWeights d e d' e' f) branchWeights_isSymm
    (fun x y hxy ↦ branchWeights_apply_eq_zero_of_snd_ne hed hf₀ hf hd' he' hxy)
    (fun x ↦ sub_eq_zero.mp
      (congrFun (balanceDefect_branchWeights hde hdf hef hf' hde' hdf' hef') x)) _ _ ?_
  rw [sum_mul_single_rotate_zigzagBacktrackWalk _ hde,
    branchWeights_apply_self hde hdf hef hf hfd hd' he']
  exact one_ne_zero

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of a zigzag algebra is nonzero** when `G` has
two vertices with three distinct neighbours each, joined by a non-backtracking walk which leaves
the first through its third neighbour, enters the second through its third neighbour, and does not
return to the first, over every nontrivial commutative ring. The hypotheses are those of the
previous theorem, which shows that the loop operation of the walk `e.symm, d, d.symm, e` is not a
Hochschild coboundary. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_walk [Nontrivial k]
    {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  intro hvan
  have hc := fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk hed (1 : k)
  obtain ⟨φ, hφ, -, hφc⟩ := AInfinityAlgebra.hochschildVanishesAt_iff.mp hvan _
    (AInfinityAlgebra.isHomogeneous_obstruction
      (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ hc) _)
    (AInfinityAlgebra.obstruction_comp_lengthProj _ _ _)
    (hochschildDifferential_obstruction_zigzagLoopAInfinityAlgebra _ hc)
  exact not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk
    hde hed hf₀ hdf hef hf hf' hfd hde' hd' he' hdf' hef' ⟨φ, hφ, hφc⟩

/-! ### The affine `Dₙ` graphs -/

section AffineD

variable {m : ℕ}

/-- The dart from node `i` to node `j` of the affine `D_{m+5}` graph, for adjacent nodes: the
hypothesis is the adjacency condition of `TauCeti.AffineDynkinType.graph_D_adj`. -/
private def affineDDart (i j : ℕ)
    (h : (i + 1 = j ∧ j ≤ m + 3) ∨ (j + 1 = i ∧ i ≤ m + 3) ∨ (i = 1 ∧ j = m + 4) ∨
      (j = 1 ∧ i = m + 4) ∨ (i = m + 2 ∧ j = m + 5) ∨ (j = m + 2 ∧ i = m + 5)) :
    (AffineDynkinType.D (m + 5)).graph.Dart :=
  ⟨(⟨i, by simp; omega⟩, ⟨j, by simp; omega⟩),
    (AffineDynkinType.graph_D_adj (by omega)).2 (by simp only; omega)⟩

private theorem affineDDart_ne {i j i' j' : ℕ} {h h'} (hii' : i ≠ i' ∨ j ≠ j') :
    affineDDart (m := m) i j h ≠ affineDDart i' j' h' := by
  intro heq
  rw [SimpleGraph.Dart.ext_iff] at heq
  simp only [affineDDart, Prod.mk.injEq, Fin.mk.injEq] at heq
  omega

private theorem affineDDart_ne_symm {i j i' j' : ℕ} {h h'} (hii' : i ≠ j' ∨ j ≠ i') :
    affineDDart (m := m) i j h ≠ (affineDDart i' j' h').symm := by
  intro heq
  rw [SimpleGraph.Dart.ext_iff, SimpleGraph.Dart.symm_toProd] at heq
  simp only [affineDDart, Prod.swap_prod_mk, Prod.mk.injEq, Fin.mk.injEq] at heq
  omega

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero**
for `n ≥ 5`, over every nontrivial commutative ring: the two branch nodes `1` and `n - 3` have
three neighbours each and are joined by the path `1 - 2 - ⋯ - (n - 3)`. For `n = 4` see
`TauCeti.not_hochschildVanishesAt_four_affineD4`. -/
theorem not_hochschildVanishesAt_four_affineD [Nontrivial k] {n : ℕ} (hn : 5 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 (by omega)))).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  -- The walk `1 → 2 → ⋯ → m + 2` from the branch node `1` to the branch node `m + 2 = n - 3`,
  -- whose other neighbours are `0, m + 4` and `m + 3, m + 5`.
  let f : Fin (m + 1) → (AffineDynkinType.D (m + 5)).graph.Dart := fun t ↦
    affineDDart (t + 1) (t + 2) (by omega)
  refine not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_walk
    (d := affineDDart 0 1 (by omega)) (e := affineDDart (m + 4) 1 (by omega))
    (d' := affineDDart (m + 3) (m + 2) (by omega)) (e' := affineDDart (m + 5) (m + 2) (by omega))
    (f := f) (affineDDart_ne (by omega)) rfl rfl (affineDDart_ne_symm (by omega))
    (affineDDart_ne_symm (by omega)) (fun _ ↦ rfl) (fun t ↦ affineDDart_ne_symm (by simp))
    (fun t h ↦ ?_) (affineDDart_ne (by omega)) rfl rfl (affineDDart_ne (by simp))
    (affineDDart_ne (by simp))
  have h' := congrArg Fin.val h
  simp [f, affineDDart] at h'

end AffineD

end TauCeti
