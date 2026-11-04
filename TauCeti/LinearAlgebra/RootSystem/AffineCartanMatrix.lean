/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.Matrix.Submatrix
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Isomorphism

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
when the root system is reduced and irreducible. The nodes with mark `1` are the *special nodes*
(`RootPairing.Base.specialNodes`), among them the affine node.

A *symmetry* of `A` is a permutation `σ` of the nodes with `A (σ k) (σ l) = A k l`, an element of
`TauCeti.matrixSymmetryGroup A`; these are the automorphisms of the extended Dynkin diagram, and
they may move the affine node. Such a `σ` carries the left null vector `m` to the left null vector
`m ∘ σ`, which is therefore `c • m` for a scalar `c`. Summing over the nodes, `∑ₖ mₖ` is
`ht(θ) + 1` (`RootPairing.Base.sum_affineMarks`), which is positive, and it is unchanged by `σ`,
so `c = 1`: every symmetry of `A` preserves the marks, and hence permutes the special nodes. In
particular a symmetry sends the affine node to a special node. Classically, the stabilizer of the
fundamental alcove in the extended affine Weyl group acts simply transitively on the special
nodes, so composing with one of its elements turns any symmetry of `A` into one fixing the affine
node, that is, into a symmetry of the finite Dynkin diagram.

Conversely, every symmetry `τ` of the finite Cartan matrix extends to a symmetry of `A` fixing the
affine node. The symmetries of the finite Cartan matrix are the automorphisms of the based root
system as a diagram: permutations of the simple roots preserving every oriented Cartan integer,
hence the root lengths, without reference to a weight lattice. Since a root system is determined
by its Cartan matrix (Mathlib's `RootPairing.Base.equivOfCartanMatrixEq`), `τ` lifts to an
automorphism of the root system permuting the simple roots as `τ` does. Such an automorphism
preserves heights, so it fixes the highest root, the only root of maximal height, and with it every
Cartan integer `⟨θ, αⱼ^∨⟩` and `⟨αᵢ, θ^∨⟩` of the row and the column of the affine node. This
needs the root system to be reduced and irreducible: for `A₁ × A₁` the swap of the two simple roots
moves the only simple root joined to the affine node. Thus the stabilizer of the affine node in the
symmetry group of `A` is identified with the symmetry group of the finite Cartan matrix, by
restriction to the simple nodes and extension by fixing the affine node.

## Main definitions

* `RootPairing.Base.affineCartanMatrix`: the untwisted affine Cartan matrix.
* `RootPairing.Base.affineSimpleRootIndex`: the root index of the simple root at each node, with
  `α₀ = -θ` at the affine node.
* `RootPairing.Base.affineMarks`: the marks, the coefficients of the null-root relation.
* `RootPairing.Base.specialNodes`: the special nodes, those with mark `1`.
* `RootPairing.Base.affineExtension`: the extension of the symmetries of the finite Cartan matrix
  to symmetries of `A` fixing the affine node.
* `RootPairing.Base.affineNodeStabilizerEquiv`: the stabilizer of the affine node in the symmetry
  group of `A` is the symmetry group of the finite Cartan matrix.

## Main results

* `RootPairing.Base.affineCartanMatrix_apply`: `A k l = ⟨αₖ, αₗ^∨⟩` for the simple roots at the
  nodes, with `α₀ = -θ`.
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
* `RootPairing.Base.sum_affineMarks`: the marks sum to `ht(θ) + 1`.
* `RootPairing.Base.affineMarks_apply_of_mem_matrixSymmetryGroup`: **for a root system, every
  symmetry of `A` preserves the marks**, and `RootPairing.Base.apply_mem_specialNodes_iff`: it
  permutes the special nodes.
* `RootPairing.Base.pairingIn_highestRoot_apply_of_mem_matrixSymmetryGroup` and
  `RootPairing.Base.pairingIn_apply_highestRoot_of_mem_matrixSymmetryGroup`: for a reduced
  irreducible root system, a symmetry of the finite Cartan matrix preserves the Cartan integers
  involving the highest root, and
  `RootPairing.Base.affineMarks_some_apply_of_mem_matrixSymmetryGroup`: it preserves the marks.
* `RootPairing.Base.optionCongr_mem_matrixSymmetryGroup_affineCartanMatrix`: **a symmetry of the
  finite Cartan matrix extends to a symmetry of `A` fixing the affine node**, and
  `RootPairing.Base.range_affineExtension`: these are all the symmetries of `A` fixing it.

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

open scoped Classical in
/-- The expansion `RootPairing.Base.root_highestRoot_eq_sum_affineMarks` as a sum over the simple
roots indexed in `ι`, with the marks extended by zero off the base: the shape consumed by
`RootPairing.Base.height_eq_sum` and `RootPairing.pairingIn_eq_sum_of_root_eq_sum`. -/
private theorem root_highestRoot_eq_sum_dite :
    P.root b.highestRoot = ∑ k ∈ b.support,
      (if h : k ∈ b.support then b.affineMarks (some ⟨k, h⟩) else 0) • P.root k := by
  rw [b.root_highestRoot_eq_sum_affineMarks, ← Finset.sum_coe_sort b.support]
  simp

/-- **The sum of the marks** is one more than the height of the highest root. For a reduced
irreducible root system this is the Coxeter number. -/
theorem sum_affineMarks : ∑ k, b.affineMarks k = b.height b.highestRoot + 1 := by
  classical
  rw [Fintype.sum_option, affineMarks_none, height_eq_sum b.root_highestRoot_eq_sum_dite,
    ← Finset.sum_coe_sort b.support, add_comm]
  simp

/-- The marks have positive sum, since the highest root is a positive root. -/
theorem sum_affineMarks_pos : 0 < ∑ k, b.affineMarks k := by
  have := b.isPos_iff.mp b.isPos_highestRoot
  rw [sum_affineMarks]
  omega

/-- The **special nodes** of the affine Dynkin diagram: the nodes whose mark is `1`, that is, the
affine node together with the simple roots whose coefficient in the highest root is `1`. -/
def specialNodes : Set (Option b.support) :=
  {k | b.affineMarks k = 1}

@[simp]
theorem mem_specialNodes {k : Option b.support} : k ∈ b.specialNodes ↔ b.affineMarks k = 1 :=
  Iff.rfl

/-- The affine node is special. -/
theorem none_mem_specialNodes : none ∈ b.specialNodes :=
  b.affineMarks_none

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

/-- The root index of the simple root at a node of the affine Dynkin diagram: the simple root `αᵢ`
at a node `i`, and the affine simple root `α₀ = -θ`, the root of index
`P.reflectionPerm θ θ`, at the affine node. -/
noncomputable def affineSimpleRootIndex : Option b.support → ι
  | none => P.reflectionPerm b.highestRoot b.highestRoot
  | some i => i

@[simp]
theorem affineSimpleRootIndex_none :
    b.affineSimpleRootIndex none = P.reflectionPerm b.highestRoot b.highestRoot := (rfl)

@[simp]
theorem affineSimpleRootIndex_some (i : b.support) : b.affineSimpleRootIndex (some i) = i := (rfl)

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

/-- **The affine Cartan matrix is the matrix of Cartan integers of the affine simple roots**:
`A k l = ⟨αₖ, αₗ^∨⟩`, with `α₀ = -θ` at the affine node. -/
theorem affineCartanMatrix_apply (k l : Option b.support) :
    b.affineCartanMatrix k l =
      P.pairingIn ℤ (b.affineSimpleRootIndex k) (b.affineSimpleRootIndex l) := by
  rcases k with _ | i <;> rcases l with _ | j <;> simp

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
  rw [RootPairing.pairingIn_eq_sum_of_root_eq_sum b.root_highestRoot_eq_sum_dite,
    ← Finset.sum_coe_sort b.support]
  simp

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

/-! ### Symmetries of the affine Cartan matrix -/

/-- **A symmetry of the affine Cartan matrix preserves the marks**: if a permutation `σ` of the
nodes satisfies `A (σ k) (σ l) = A k l`, then `m (σ k) = m k` for every node `k`. Here `σ` may
move the affine node, and the root system need not be reduced or irreducible. -/
theorem affineMarks_apply_of_mem_matrixSymmetryGroup [IsDomain R] [P.IsRootSystem]
    {σ : Equiv.Perm (Option b.support)}
    (hσ : σ ∈ TauCeti.matrixSymmetryGroup b.affineCartanMatrix) (k : Option b.support) :
    b.affineMarks (σ k) = b.affineMarks k := by
  -- `m ∘ σ` is again a left null vector, so it is `c • m` with `c = m (σ 0)`
  have hnull : (b.affineMarks ∘ σ) ᵥ* b.affineCartanMatrix = 0 := by
    conv_lhs => rw [← TauCeti.mem_matrixSymmetryGroup_iff.mp hσ]
    rw [submatrix_vecMul_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      affineMarks_vecMul_affineCartanMatrix, Pi.zero_comp]
  have hc (k : Option b.support) : b.affineMarks (σ k) = b.affineMarks (σ none) * b.affineMarks k :=
    congrFun (b.vecMul_affineCartanMatrix_eq_zero_iff.mp hnull) k
  -- summing over the nodes gives `∑ m = c * ∑ m`, and `∑ m > 0`, so `c = 1`
  have hsum : b.affineMarks (σ none) * ∑ k, b.affineMarks k = 1 * ∑ k, b.affineMarks k := by
    rw [one_mul, Finset.mul_sum]
    conv_rhs => rw [← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl fun k _ ↦ (hc k).symm
  rw [hc, mul_right_cancel₀ b.sum_affineMarks_pos.ne' hsum, one_mul]

/-- **A symmetry of the affine Cartan matrix permutes the special nodes.** In particular it sends
the affine node to a special node. -/
theorem apply_mem_specialNodes_iff [IsDomain R] [P.IsRootSystem]
    {σ : Equiv.Perm (Option b.support)}
    (hσ : σ ∈ TauCeti.matrixSymmetryGroup b.affineCartanMatrix) {k : Option b.support} :
    σ k ∈ b.specialNodes ↔ k ∈ b.specialNodes := by
  rw [mem_specialNodes, mem_specialNodes, b.affineMarks_apply_of_mem_matrixSymmetryGroup hσ]

/-! ### Extending symmetries of the finite Cartan matrix to the affine node -/

section Extension

variable [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible]
  {τ : Equiv.Perm b.support}

/-- A symmetry `τ` of the finite Cartan matrix lifts to an automorphism of the root system
carrying each simple root `αᵢ` to `α_{τ i}` (Mathlib's `RootPairing.Base.equivOfCartanMatrixEq`).
That automorphism permutes the simple roots, so it fixes the highest root. -/
private theorem exists_aut_of_mem_matrixSymmetryGroup
    (hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix) :
    ∃ u : P.Aut, u.indexEquiv b.highestRoot = b.highestRoot ∧
      ∀ k : b.support, u.indexEquiv k = τ k := by
  have he (k l : b.support) : b.cartanMatrix (τ k) (τ l) = b.cartanMatrix k l :=
    congrFun₂ (TauCeti.mem_matrixSymmetryGroup_iff.mp hτ) k l
  let u : P.Aut := b.equivOfCartanMatrixEq b τ he
  have hu (k : b.support) : u.indexEquiv k = τ k :=
    TauCeti.equivOfCartanMatrixEq_indexEquiv_apply b b τ he k
  exact ⟨u, b.indexEquiv_highestRoot u fun k hk ↦ hu ⟨k, hk⟩ ▸ (τ ⟨k, hk⟩).2, hu⟩

/-- **A symmetry of the finite Cartan matrix preserves the pairings of the highest root with the
simple coroots**, `⟨θ, α_{τ j}^∨⟩ = ⟨θ, αⱼ^∨⟩`. -/
theorem pairingIn_highestRoot_apply_of_mem_matrixSymmetryGroup
    (hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix)
    (j : b.support) :
    P.pairingIn ℤ b.highestRoot (τ j) = P.pairingIn ℤ b.highestRoot j := by
  obtain ⟨u, hθ, hu⟩ := b.exists_aut_of_mem_matrixSymmetryGroup hτ
  simpa [hθ, hu] using u.toHom.pairingIn_indexEquiv ℤ b.highestRoot j

/-- **A symmetry of the finite Cartan matrix preserves the pairings of the simple roots with the
coroot of the highest root**, `⟨α_{τ i}, θ^∨⟩ = ⟨αᵢ, θ^∨⟩`. -/
theorem pairingIn_apply_highestRoot_of_mem_matrixSymmetryGroup
    (hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix)
    (i : b.support) :
    P.pairingIn ℤ (τ i) b.highestRoot = P.pairingIn ℤ i b.highestRoot := by
  obtain ⟨u, hθ, hu⟩ := b.exists_aut_of_mem_matrixSymmetryGroup hτ
  simpa [hθ, hu] using u.toHom.pairingIn_indexEquiv ℤ i b.highestRoot

/-- **A symmetry of the finite Cartan matrix extends to the affine node**: fixing the affine node,
it is a symmetry of the affine Cartan matrix. -/
theorem optionCongr_mem_matrixSymmetryGroup_affineCartanMatrix
    (hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix) :
    τ.optionCongr ∈ TauCeti.matrixSymmetryGroup b.affineCartanMatrix := by
  refine TauCeti.mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun k l ↦ ?_)
  rcases k with _ | i <;> rcases l with _ | j
  · rfl
  · simp [b.pairingIn_highestRoot_apply_of_mem_matrixSymmetryGroup hτ j]
  · simp [b.pairingIn_apply_highestRoot_of_mem_matrixSymmetryGroup hτ i]
  · simpa [cartanMatrixIn_def] using congrFun₂ (TauCeti.mem_matrixSymmetryGroup_iff.mp hτ) i j

/-- **A symmetry of the finite Cartan matrix preserves the marks**: the coefficients of the highest
root in the simple roots are constant along the orbits of every diagram symmetry. -/
theorem affineMarks_some_apply_of_mem_matrixSymmetryGroup
    (hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix)
    (i : b.support) : b.affineMarks (some (τ i)) = b.affineMarks (some i) := by
  simpa using b.affineMarks_apply_of_mem_matrixSymmetryGroup
    (b.optionCongr_mem_matrixSymmetryGroup_affineCartanMatrix hτ) (some i)

/-- **The extension of the symmetries of the finite Cartan matrix to the affine Cartan matrix.**
The symmetry group of the finite Cartan matrix is the group `Γ` of automorphisms of the based root
system as a diagram: the permutations of the simple roots preserving every oriented Cartan integer,
hence the root lengths, with no reference to a weight lattice. Each of them extends to a symmetry
of the affine Cartan matrix by fixing the affine node. -/
def affineExtension :
    TauCeti.matrixSymmetryGroup b.cartanMatrix →* TauCeti.matrixSymmetryGroup b.affineCartanMatrix
    where
  toFun τ := ⟨(τ : Equiv.Perm b.support).optionCongr,
    b.optionCongr_mem_matrixSymmetryGroup_affineCartanMatrix τ.2⟩
  map_one' := Subtype.ext Equiv.optionCongr_one
  map_mul' σ τ := Subtype.ext <| by simp [Equiv.Perm.mul_def, Equiv.optionCongr_trans]

@[simp]
theorem coe_affineExtension (τ : TauCeti.matrixSymmetryGroup b.cartanMatrix) :
    (b.affineExtension τ : Equiv.Perm (Option b.support)) =
      (τ : Equiv.Perm b.support).optionCongr :=
  (rfl)

theorem affineExtension_injective : Function.Injective b.affineExtension := fun _ _ h ↦
  Subtype.ext <| Equiv.optionCongr_injective congr(($h : Equiv.Perm (Option b.support)))

/-- **The extended symmetries are exactly the symmetries of the affine Cartan matrix fixing the
affine node.** A symmetry of the affine Cartan matrix fixing the affine node restricts to a
symmetry of the finite Cartan matrix, since deleting the affine node recovers it. -/
theorem range_affineExtension :
    b.affineExtension.range =
      MulAction.stabilizer (TauCeti.matrixSymmetryGroup b.affineCartanMatrix)
        (none : Option b.support) := by
  ext σ
  rw [MonoidHom.mem_range, MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
  refine ⟨fun ⟨τ, hτ⟩ ↦ by simp [← hτ], fun hσ ↦ ?_⟩
  -- the restriction of `σ` to the simple nodes, which `σ` does not move to the affine node
  set τ := Equiv.removeNone (σ : Equiv.Perm (Option b.support))
  have hσ' : τ.optionCongr = σ := by
    classical
    rw [map_equiv_removeNone, hσ, Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]
  have hsome (i : b.support) : some (τ i) = (σ : Equiv.Perm (Option b.support)) (some i) :=
    congr($hσ' (some i))
  have hτ : τ ∈ TauCeti.matrixSymmetryGroup b.cartanMatrix := by
    refine TauCeti.mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun i j ↦ ?_)
    have h := congrFun₂ (TauCeti.mem_matrixSymmetryGroup_iff.mp σ.2) (some i) (some j)
    simp only [Matrix.submatrix_apply, ← hsome, affineCartanMatrix_some_some] at h
    simpa [cartanMatrixIn_def] using h
  exact ⟨⟨τ, hτ⟩, Subtype.ext hσ'⟩

/-- **The stabilizer of the affine node in the symmetry group of the affine Cartan matrix is the
symmetry group of the finite Cartan matrix**, by restriction to the simple nodes. Its inverse is
`RootPairing.Base.affineExtension`. -/
noncomputable def affineNodeStabilizerEquiv :
    MulAction.stabilizer (TauCeti.matrixSymmetryGroup b.affineCartanMatrix)
        (none : Option b.support) ≃*
      TauCeti.matrixSymmetryGroup b.cartanMatrix :=
  ((MonoidHom.ofInjective b.affineExtension_injective).trans
    (MulEquiv.subgroupCongr b.range_affineExtension)).symm

@[simp]
theorem coe_affineNodeStabilizerEquiv_symm_apply (τ : TauCeti.matrixSymmetryGroup b.cartanMatrix) :
    ((b.affineNodeStabilizerEquiv.symm τ : TauCeti.matrixSymmetryGroup b.affineCartanMatrix) :
      Equiv.Perm (Option b.support)) = (τ : Equiv.Perm b.support).optionCongr :=
  (rfl)

/-- The symmetry of the finite Cartan matrix attached to a symmetry `σ` of the affine Cartan matrix
fixing the affine node is the restriction of `σ` to the simple nodes. -/
theorem some_affineNodeStabilizerEquiv_apply
    (σ : MulAction.stabilizer (TauCeti.matrixSymmetryGroup b.affineCartanMatrix)
        (none : Option b.support))
    (i : b.support) :
    some ((b.affineNodeStabilizerEquiv σ : Equiv.Perm b.support) i) =
      ((σ : TauCeti.matrixSymmetryGroup b.affineCartanMatrix) : Equiv.Perm (Option b.support))
        (some i) := by
  obtain ⟨τ, rfl⟩ := b.affineNodeStabilizerEquiv.symm.surjective σ
  simp

end Extension

end RootPairing.Base
