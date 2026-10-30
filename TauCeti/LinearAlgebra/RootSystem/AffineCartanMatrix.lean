/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot

/-!
# The untwisted affine Cartan matrix of a base

Let `b` be a base of a finite crystallographic root pairing `P`, with simple roots `αᵢ` and highest
root `θ` (`RootPairing.Base.highestRoot`; when `P` is not reduced and irreducible this is only a
root of maximal height, and the construction below is the affine Cartan matrix only in the reduced
irreducible case). Adjoining the *affine simple root* `α₀ = -θ`, with
coroot `α₀^∨ = -θ^∨`, to the simple roots gives the *untwisted affine Cartan matrix*
`A = (⟨αₖ, αₗ^∨⟩)` indexed by `Option b.support`, where `none` is the affine node `0`:

* `A 0 0 = 2`, `A 0 j = -⟨θ, αⱼ^∨⟩`, `A i 0 = -⟨αᵢ, θ^∨⟩`, and `A i j = ⟨αᵢ, αⱼ^∨⟩` is the finite
  Cartan matrix `RootPairing.Base.cartanMatrix`.

This is the matrix of the extended Dynkin diagram; it governs the affine Weyl group, whose simple
reflections are the reflections in the walls of the fundamental alcove, and the walls of the
alcove `{x | αᵢ(x) > 0, θ(x) < 1}` are the zero sets of the affine functions `αᵢ` and `1 - θ`.

Writing `θ = ∑ mᵢ αᵢ` and setting `m₀ = 1`, the *marks* `mₖ` (`RootPairing.Base.affineMarks`)
satisfy `∑ₖ mₖ αₖ = 0` with `α₀ = -θ`. This is the finite projection of the affine *null-root
relation*: in an affine realization `α₀ = δ - θ`, the null root `δ = ∑ₖ mₖ αₖ` pairs to zero with
every coroot. This file proves that `A` is a generalized Cartan matrix (diagonal `2`, nonpositive
off-diagonal entries, symmetric zero pattern) and that it is singular. For a root system its left
kernel is exactly the line spanned by the marks, so `A` has corank one, and the marks are positive
when the root system is reduced and irreducible. The nodes with mark `1` are the special nodes,
among them the affine node.

## Main definitions

* `RootPairing.Base.affineCartanMatrix`: the untwisted affine Cartan matrix.
* `RootPairing.Base.affineMarks`: the marks, the coefficients of the null-root relation.

## Main results

* `RootPairing.Base.submatrix_affineCartanMatrix_some`: deleting the affine node recovers the
  finite Cartan matrix.
* `RootPairing.Base.affineCartanMatrix_apply_same`,
  `RootPairing.Base.affineCartanMatrix_le_zero_of_ne` and
  `RootPairing.Base.affineCartanMatrix_apply_eq_zero_iff_symm`: `A` is a generalized Cartan matrix.
* `RootPairing.Base.root_highestRoot_eq_sum_affineMarks` and
  `RootPairing.Base.affineMarks_some_eq_of_root_highestRoot_eq_sum`: the marks are the
  coefficients of the highest root in the simple roots.
* `RootPairing.Base.affineMarks_vecMul_affineCartanMatrix`: the marks are a left null vector of
  `A`.
* `RootPairing.Base.vecMul_affineCartanMatrix_eq_zero_iff`: for a root system, every left null
  vector of `A` is a multiple of the marks.
* `RootPairing.Base.det_affineCartanMatrix`: `A` is singular.
* `RootPairing.Base.affineMarks_pos`: for a reduced irreducible root pairing, all marks are
  positive.

## References

* V. G. Kac, *Infinite Dimensional Lie Algebras*, third edition, Cambridge University Press, 1990,
  §6.1 and Chapter 4 (Tables Aff 1).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §4.3 and Plates I–IX.
-/

public section

open Matrix

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [CharZero R] [Finite ι] [Nonempty ι] (b : P.Base)

/-! ### The marks -/

/-- **The marks** of the affine Cartan matrix: `1` at the affine node and, at a simple root `αᵢ`,
the coefficient of `αᵢ` in the expansion `θ = ∑ mᵢ αᵢ` of the highest root. These are the
coefficients of the relation `∑ₖ mₖ αₖ = 0` with `α₀ = -θ`, the finite projection of the affine
null-root relation `δ = ∑ₖ mₖ αₖ`. -/
noncomputable def affineMarks : Option b.support → ℤ
  | none => 1
  | some i => b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) i

@[simp]
theorem affineMarks_none : b.affineMarks none = 1 := (rfl)

/-- The highest root is the combination of the simple roots with the marks as coefficients. -/
theorem root_highestRoot_eq_sum_affineMarks :
    P.root b.highestRoot = ∑ i : b.support, b.affineMarks (some i) • P.root i := by
  have h := congrArg Subtype.val (b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ b.highestRoot))
  simpa [affineMarks, eq_comm] using h

/-- The marks are the *only* coefficients expressing the highest root in the simple roots. -/
theorem affineMarks_some_eq_of_root_highestRoot_eq_sum {f : b.support → ℤ}
    (hf : P.root b.highestRoot = ∑ i : b.support, f i • P.root i) (i : b.support) :
    b.affineMarks (some i) = f i := by
  have h : P.rootSpanMem ℤ b.highestRoot = ∑ i, f i • b.toWeightBasisInt i :=
    Subtype.ext <| by simpa using hf
  rw [affineMarks, h, b.toWeightBasisInt.repr_sum_self]

/-- **The marks are positive** for a reduced irreducible crystallographic root pairing: the highest
root has a positive coefficient along every simple root, and the affine node has mark `1`. -/
theorem affineMarks_pos [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (k : Option b.support) : 0 < b.affineMarks k := by
  rcases k with _ | i
  · simp
  obtain ⟨f, hf, hθ⟩ := b.exists_root_highestRoot_eq_sum_nat
  rw [b.affineMarks_some_eq_of_root_highestRoot_eq_sum (f := fun j ↦ (f j : ℤ)) ?_ i]
  · exact_mod_cast hf i i.2
  · rw [hθ, ← Finset.sum_coe_sort b.support]
    simp

/-! ### The affine Cartan matrix -/

variable [P.IsCrystallographic]

/-- **The untwisted affine Cartan matrix** of a base `b`: the matrix `(⟨αₖ, αₗ^∨⟩)` of the simple
roots together with the affine simple root `α₀ = -θ`, where `θ = b.highestRoot` and the affine
node `0` is `none`.

For a reduced irreducible root pairing `θ` is the highest root and this is the untwisted affine
Cartan matrix of the extended Dynkin diagram. For a reducible one `θ` is only a root of maximal
height, lying in a single irreducible component, and the matrix adjoins one affine node to that
component alone. -/
noncomputable def affineCartanMatrix : Matrix (Option b.support) (Option b.support) ℤ :=
  .of fun
    | none, none => 2
    | none, some j => -P.pairingIn ℤ b.highestRoot j
    | some i, none => -P.pairingIn ℤ i b.highestRoot
    | some i, some j => P.pairingIn ℤ i j

@[simp]
theorem affineCartanMatrix_none_some (j : b.support) :
    b.affineCartanMatrix none (some j) = -P.pairingIn ℤ b.highestRoot j := (rfl)

@[simp]
theorem affineCartanMatrix_some_none (i : b.support) :
    b.affineCartanMatrix (some i) none = -P.pairingIn ℤ i b.highestRoot := (rfl)

@[simp]
theorem affineCartanMatrix_some_some (i j : b.support) :
    b.affineCartanMatrix (some i) (some j) = P.pairingIn ℤ i j := (rfl)

/-- Deleting the affine node from the affine Cartan matrix recovers the finite Cartan matrix. -/
@[simp]
theorem submatrix_affineCartanMatrix_some :
    b.affineCartanMatrix.submatrix some some = b.cartanMatrix := by
  ext i j
  simp [cartanMatrixIn_def]

/-- The diagonal entries of the affine Cartan matrix are `2`. -/
@[simp]
theorem affineCartanMatrix_apply_same (k : Option b.support) : b.affineCartanMatrix k k = 2 := by
  cases k with
  | none => rfl
  | some i => simp

section IsDomain

variable [IsDomain R]

/-- The off-diagonal entries of the affine Cartan matrix are nonpositive. For the entries in the
row and the column of the affine node this is the dominance of the highest root. -/
theorem affineCartanMatrix_le_zero_of_ne {k l : Option b.support} (hkl : k ≠ l) :
    b.affineCartanMatrix k l ≤ 0 := by
  rcases k with _ | i <;> rcases l with _ | j
  · exact absurd rfl hkl
  · simpa using b.pairingIn_highestRoot_nonneg j.2
  · -- the simple roots pair nonnegatively with `θ^∨` because `θ` pairs nonnegatively with them
    simpa using (P.pairingIn_lt_zero_iff ℤ (i := i) (j := b.highestRoot)).not.mpr
      (b.pairingIn_highestRoot_nonneg i.2).not_gt
  · simpa [cartanMatrixIn_def] using
      b.cartanMatrix_le_zero_of_ne i j fun h ↦ hkl (congrArg some h)

/-- An entry of the affine Cartan matrix vanishes exactly when the transposed entry does. -/
theorem affineCartanMatrix_apply_eq_zero_iff_symm {k l : Option b.support} :
    b.affineCartanMatrix k l = 0 ↔ b.affineCartanMatrix l k = 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases k with _ | i <;> rcases l with _ | j <;> simp [P.pairingIn_eq_zero_iff (S := ℤ)]

end IsDomain

/-! ### The null-root relation and the kernel -/

/-- Pairing the highest root with a coroot expands along the marks. -/
private theorem pairingIn_highestRoot_eq_sum_affineMarks (l : ι) :
    P.pairingIn ℤ b.highestRoot l =
      ∑ i : b.support, b.affineMarks (some i) * P.pairingIn ℤ i l := by
  classical
  -- extend the marks by zero off the support to apply the expansion over `b.support`
  let f : ι → ℤ := fun k ↦ if h : k ∈ b.support then b.affineMarks (some ⟨k, h⟩) else 0
  have hf : P.root b.highestRoot = ∑ k ∈ b.support, f k • P.root k := by
    rw [b.root_highestRoot_eq_sum_affineMarks, ← Finset.sum_coe_sort b.support]
    simp [f]
  rw [RootPairing.pairingIn_eq_sum_of_root_eq_sum hf, ← Finset.sum_coe_sort b.support]
  simp [f]

/-- **The null-root relation**: the marks are a left null vector of the affine Cartan matrix,
since `∑ₖ mₖ αₖ = 0` with `α₀ = -θ`. In an affine realization, where `α₀ = δ - θ`, this says that
the null root `δ = ∑ₖ mₖ αₖ` pairs to zero with every coroot. -/
@[simp]
theorem affineMarks_vecMul_affineCartanMatrix :
    b.affineMarks ᵥ* b.affineCartanMatrix = 0 := by
  ext l
  rcases l with _ | j <;>
    simp only [vecMul, dotProduct, Fintype.sum_option, affineMarks_none, one_mul,
      affineCartanMatrix_apply_same, affineCartanMatrix_some_none, affineCartanMatrix_none_some,
      affineCartanMatrix_some_some, mul_neg, Finset.sum_neg_distrib, Pi.zero_apply,
      ← pairingIn_highestRoot_eq_sum_affineMarks, pairingIn_same]
  · norm_num
  · simp

/-- **The affine Cartan matrix is singular**: its marks are a nonzero left null vector. -/
@[simp]
theorem det_affineCartanMatrix [DecidableEq ι] : b.affineCartanMatrix.det = 0 :=
  exists_vecMul_eq_zero_iff.mp
    ⟨b.affineMarks, fun h ↦ by simpa using congrFun h none,
      b.affineMarks_vecMul_affineCartanMatrix⟩

/-- **The left kernel of the affine Cartan matrix is spanned by the marks**: for a root system, a
vector `v` with `v ᵥ* A = 0` is `v 0` times the marks. Together with
`RootPairing.Base.affineMarks_vecMul_affineCartanMatrix`, the affine Cartan matrix has corank
one. -/
theorem vecMul_affineCartanMatrix_eq_zero_iff [IsDomain R] [P.IsRootSystem]
    {v : Option b.support → ℤ} :
    v ᵥ* b.affineCartanMatrix = 0 ↔ v = v none • b.affineMarks := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ by rw [hv, smul_vecMul, affineMarks_vecMul_affineCartanMatrix,
    smul_zero]⟩
  -- `w = v - v 0 • m` is a left null vector vanishing at the affine node, so its restriction to
  -- the simple nodes is a left null vector of the nondegenerate finite Cartan matrix
  set w := v - v none • b.affineMarks with hw
  have hw0 : w none = 0 := by simp [hw]
  have hwA : w ᵥ* b.affineCartanMatrix = 0 := by
    rw [hw, sub_vecMul, smul_vecMul, affineMarks_vecMul_affineCartanMatrix, hv, smul_zero,
      sub_zero]
  have hfin : (w ∘ some) ᵥ* b.cartanMatrix = 0 := by
    ext j
    have := congrFun hwA (some j)
    simpa [vecMul, dotProduct, Fintype.sum_option, hw0, cartanMatrixIn_def] using this
  have hsome := b.cartanMatrix_nondegenerate.separatingLeft.eq_zero_of_vecMul_eq_zero hfin
  rw [← sub_eq_zero]
  ext k
  rcases k with _ | i
  · exact hw0
  · exact congrFun hsome i

end RootPairing.Base
