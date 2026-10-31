/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.End.JordanChain.Partition

/-!
# Nilpotent Jordan forms with prescribed block sizes

For a basis `b` of `V` indexed by `Σ i, Fin (len i)`, the *chain shift* `b.chainShift` sends
`b ⟨i, j⟩` to `b ⟨i, j + 1⟩` and the last vector of each chain to zero. Its matrix in `b` is the
block-diagonal matrix of nilpotent Jordan blocks of sizes `len i`, with ones just below the
diagonal (`Module.Basis.toMatrix_chainShift`). When every `len i` is positive, the first vectors
`b ⟨i, 0⟩` are the heads of a Jordan-chain basis of `b.chainShift`
(`Module.Basis.jordanChainBasis`), so the Jordan partition of `b.chainShift` consists of the
lengths `len i` (`Module.Basis.jordanPartition_chainShift_parts`). Conversely, an endomorphism
with a Jordan-chain basis `c` is the chain shift of `c.basis`
(`Module.End.JordanChainBasis.chainShift_basis`).

Consequently every partition of `finrank K V` is the Jordan partition of a nilpotent endomorphism
of `V` (`Module.End.exists_jordanPartition_eq`). Together with
`Module.End.exists_linearEquiv_conj_eq_iff_jordanPartition_parts_eq`, the Jordan partition is a
bijection from conjugacy classes of nilpotent endomorphisms of `V` onto the partitions of
`finrank K V`, and each class contains a chain shift.

## References

* P. R. Halmos, *Finite-Dimensional Vector Spaces*, §57.
-/

public section

open Module

namespace Module.Basis

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {len : ι → ℕ}

/-- The chain shift of a basis indexed by chains: it sends `b ⟨i, j⟩` to `b ⟨i, j + 1⟩`, and the
last vector of each chain to zero. It is the direct sum of nilpotent Jordan blocks of sizes
`len i`. -/
noncomputable def chainShift (b : Basis (Σ i, Fin (len i)) R M) : Module.End R M :=
  b.constr ℕ fun p => if h : (p.2 : ℕ) + 1 < len p.1 then b ⟨p.1, ⟨p.2 + 1, h⟩⟩ else 0

/-- The chain shift moves a basis vector one step along its chain, or kills it at the end of the
chain. -/
@[simp]
theorem chainShift_basis (b : Basis (Σ i, Fin (len i)) R M) (i : ι) (j : Fin (len i)) :
    b.chainShift (b ⟨i, j⟩) = if h : (j : ℕ) + 1 < len i then b ⟨i, ⟨j + 1, h⟩⟩ else 0 :=
  b.constr_basis ℕ _ _

/-- A power of the chain shift moves a basis vector along its chain, or kills it once it reaches
the end of the chain. -/
@[simp]
theorem pow_chainShift_basis (b : Basis (Σ i, Fin (len i)) R M) (k : ℕ) (i : ι)
    (j : Fin (len i)) :
    (b.chainShift ^ k) (b ⟨i, j⟩) = if h : (j : ℕ) + k < len i then b ⟨i, ⟨j + k, h⟩⟩ else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    split_ifs with h₁ h₂ h₂
    · simp [add_assoc, h₂]
    · simp [add_assoc, h₂]
    · omega
    · exact map_zero _

/-- Each basis vector is a power of the chain shift applied to the first vector of its chain. -/
theorem pow_chainShift_basis_zero (b : Basis (Σ i, Fin (len i)) R M) (i : ι) (j : Fin (len i)) :
    (b.chainShift ^ (j : ℕ)) (b ⟨i, ⟨0, j.pos⟩⟩) = b ⟨i, j⟩ := by
  simp

/-- The first vectors `b ⟨i, 0⟩` of the chains of a basis are the heads of a Jordan-chain basis
of its chain shift, provided every chain is nonempty. Its underlying basis is `b`
(`Module.Basis.basis_jordanChainBasis`). The body is exposed so that the type of the underlying
basis, which is indexed by the chain lengths, reduces to the index type of `b`. -/
@[expose] noncomputable def jordanChainBasis (b : Basis (Σ i, Fin (len i)) R M)
    (hlen : ∀ i, 0 < len i) : b.chainShift.JordanChainBasis ι where
  len := len
  head i := b ⟨i, ⟨0, hlen i⟩⟩
  len_pos := hlen
  pow_len_apply_head i := by simp
  linearIndependent := by
    convert b.linearIndependent with p
    exact b.pow_chainShift_basis_zero p.1 p.2
  span_eq_top := by
    convert b.span_eq with p
    exact b.pow_chainShift_basis_zero p.1 p.2

/-- The chains of the Jordan-chain basis of a chain shift have the prescribed lengths. -/
@[simp]
theorem jordanChainBasis_len (b : Basis (Σ i, Fin (len i)) R M) (hlen : ∀ i, 0 < len i) :
    (b.jordanChainBasis hlen).len = len := (rfl)

/-- The heads of the Jordan-chain basis of a chain shift are the first vectors of the chains. -/
@[simp]
theorem jordanChainBasis_head (b : Basis (Σ i, Fin (len i)) R M) (hlen : ∀ i, 0 < len i)
    (i : ι) : (b.jordanChainBasis hlen).head i = b ⟨i, ⟨0, hlen i⟩⟩ := (rfl)

/-- The Jordan-chain basis of a chain shift recovers the original basis. -/
@[simp]
theorem basis_jordanChainBasis (b : Basis (Σ i, Fin (len i)) R M) (hlen : ∀ i, 0 < len i) :
    (b.jordanChainBasis hlen).basis = b :=
  Basis.eq_of_apply_eq fun p => by
    rw [Module.End.JordanChainBasis.basis_apply]
    exact b.pow_chainShift_basis_zero p.1 p.2

/-- A chain shift with finitely many chains is nilpotent. -/
theorem isNilpotent_chainShift [Finite ι] (b : Basis (Σ i, Fin (len i)) R M) :
    IsNilpotent b.chainShift := by
  cases nonempty_fintype ι
  refine ⟨∑ i, len i, b.ext fun ⟨i, j⟩ => ?_⟩
  have := Finset.single_le_sum (fun i _ => Nat.zero_le (len i)) (Finset.mem_univ i)
  simp only [pow_chainShift_basis, LinearMap.zero_apply, dite_eq_right_iff]
  omega

end Module.Basis

namespace Module.End.JordanChainBasis

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : End R M}

/-- An endomorphism with a Jordan-chain basis `c` is the chain shift of `c.basis`. -/
@[simp]
theorem chainShift_basis (c : f.JordanChainBasis ι) : c.basis.chainShift = f :=
  c.basis.ext fun ⟨i, j⟩ => by rw [Basis.chainShift_basis, c.apply_basis]

end Module.End.JordanChainBasis

namespace Module.Basis

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {len : ι → ℕ}
  [Fintype ι] [DecidableEq ι]

/-- The matrix of a chain shift in its basis is block diagonal, with a nilpotent Jordan block of
size `len i` for each chain: its only nonzero entries are ones just below the diagonal of each
block. -/
theorem toMatrix_chainShift (b : Basis (Σ i, Fin (len i)) R M) :
    LinearMap.toMatrix b b b.chainShift =
      Matrix.of fun p q => if p.1 = q.1 ∧ (p.2 : ℕ) = q.2 + 1 then 1 else 0 := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [LinearMap.toMatrix_apply, chainShift_basis, Matrix.of_apply]
  split_ifs with h₁ h₂ h₂
  · obtain ⟨rfl, h₂⟩ := h₂
    have hj : (⟨j' + 1, h₁⟩ : Fin (len i)) = j := Fin.ext h₂.symm
    rw [b.repr_self, hj, Finsupp.single_eq_same]
  · rw [b.repr_self, Finsupp.single_apply, ite_eq_right_iff]
    rintro ⟨⟩
    exact absurd ⟨rfl, rfl⟩ h₂
  · obtain ⟨rfl, h₂⟩ := h₂
    exact absurd (h₂ ▸ j.isLt) h₁
  · simp

end Module.Basis

namespace Module.Basis

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι] {len : ι → ℕ}

/-- The Jordan partition of a chain shift consists of the chain lengths. -/
theorem jordanPartition_chainShift_parts (b : Basis (Σ i, Fin (len i)) K V)
    (hlen : ∀ i, 0 < len i) :
    (b.chainShift.jordanPartition b.isNilpotent_chainShift).parts = Finset.univ.val.map len := by
  rw [(b.jordanChainBasis hlen).jordanPartition_eq,
    Module.End.JordanChainBasis.partition_parts, jordanChainBasis_len]

end Module.Basis

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Every partition of `finrank K V` is the Jordan partition of a nilpotent endomorphism of `V`.
This includes the empty partition of the zero space. -/
theorem exists_jordanPartition_eq (μ : Nat.Partition (finrank K V)) :
    ∃ (f : End K V) (hf : IsNilpotent f), f.jordanPartition hf = μ := by
  let l := μ.parts.toList
  have hlen (i : Fin l.length) : 0 < l[i] :=
    μ.parts_pos (Multiset.mem_toList.mp (List.getElem_mem _))
  have hsum : ∑ i : Fin l.length, l[i] = finrank K V := by
    simp only [Fin.getElem_fin]
    rw [Fin.sum_univ_getElem, ← Multiset.sum_coe, Multiset.coe_toList, μ.parts_sum]
  let b := (Module.finBasis K V).reindex (finSigmaFinEquiv.trans (finCongr hsum)).symm
  refine ⟨b.chainShift, b.isNilpotent_chainShift, Nat.Partition.ext ?_⟩
  rw [b.jordanPartition_chainShift_parts hlen, Fin.univ_val_map]
  simp only [Fin.getElem_fin]
  rw [List.ofFn_getElem, Multiset.coe_toList]

end Module.End
