/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Jordan chains of nilpotent endomorphisms

A *Jordan-chain basis* of an endomorphism `f` of a vector space `V` is a basis of the form
`f ^ j (v i)`, `j < len i`, where `f ^ len i` kills the chain head `v i`. In such a basis `f` is
a direct sum of nilpotent Jordan blocks of the sizes `len i`.

This file proves that every nilpotent endomorphism of a finite-dimensional vector space over a
field has a Jordan-chain basis, and that the multiset of chain lengths (the partition of
`finrank K V` given by the Jordan block sizes) is recovered from the dimensions of the kernels of
the powers of `f`. Consequently two nilpotent endomorphisms are conjugate exactly when their
powers have kernels of the same dimensions. The basic API of Jordan-chain bases and the
conjugator between Jordan-chain bases with matching lengths only need a semiring of scalars, and
the kernel-dimension formulas only need a division ring.

## Main definitions and results

* `Module.End.JordanChainBasis f ι`: Jordan chains for `f`, indexed by `ι`, forming a basis.
* `Module.End.exists_jordanChainBasis`: a nilpotent endomorphism of a finite-dimensional vector
  space has a Jordan-chain basis.
* `Module.End.JordanChainBasis.finrank_ker_pow`: `dim ker f ^ k = ∑ i, min k (len i)`.
* `Module.End.JordanChainBasis.card_len_eq_add_one`: the number of chains of length `k + 1` in
  terms of the dimensions of the kernels of `f ^ k`, `f ^ (k + 1)` and `f ^ (k + 2)`.
* `Module.End.JordanChainBasis.exists_equiv_len_eq`: chain lengths are unique up to reindexing.
* `Module.End.JordanChainBasis.equiv`: the conjugator between Jordan-chain bases with matching
  lengths, see `Module.End.JordanChainBasis.apply_equiv`.
* `Module.End.exists_linearEquiv_conj_eq_iff`: two nilpotent endomorphisms of finite-dimensional
  vector spaces are conjugate if and only if `dim ker f ^ k = dim ker g ^ k` for every `k`.
* `Module.End.JordanChainBasis.joinEnds`: the rank-one endomorphism sending the last vector of one
  chain to the last vector of another.
* `Module.End.JordanChainBasis.finrank_range_add_smul_joinEnds_pow` and
  `Module.End.JordanChainBasis.exists_linearEquiv_conj_add_smul_joinEnds`: for `t ≠ 0` the
  endomorphisms `f + t • joinEnds i j` are conjugate to one another, and the rank of the `k`-th
  power exceeds that of `f ^ k` by one exactly when `len j ≤ k ≤ len i`.

## Elementary degenerations

For chains `i ≠ j` of lengths `m = len i` and `r = len j`, adding `t • joinEnds i j` to `f` links
the end of chain `i` to the end of chain `j`. When `r ≤ m` and `t ≠ 0` the result has Jordan chains
of lengths `m + 1` and `r - 1` in place of `m` and `r` (the second one disappearing when `r = 1`),
as the rank formula shows, and at `t = 0` it is `f` again. So, over a topological field in which `0`
is not isolated, `f` is a limit of conjugates of an endomorphism whose Jordan type is obtained from
that of `f` by moving one box from a shorter part to a longer one. These moves generate the
dominance order on partitions, and this family is the degeneration behind the description of
nilpotent orbit closures by dominance. Over an infinite field the same family puts `f` in the
Zariski closure of that conjugacy class. When `m < r` the rank formula shows that the perturbation
does not change the Jordan type.

## Implementation notes

Existence is proved by splitting off one chain of maximal length together with an invariant
complement. If `f ^ m` kills the invariant subspace `Z` but `f ^ (m - 1) v ≠ 0` for some `v ∈ Z`,
choose a linear form `φ` with `φ (f ^ (m - 1) v) ≠ 0`. The common kernel in `Z` of the forms
`φ ∘ f ^ j`, `j < m`, is invariant and complementary in `Z` to the span of the chain of `v`.

## References

* P. R. Halmos, *Finite-Dimensional Vector Spaces*, §57.
* M. Gerstenhaber, *On dominance and varieties of commuting matrices*, Ann. of Math. **73**
  (1961), 324–348.
-/

public section

open Module Submodule Finset

namespace Module.End

variable {K V W : Type*}

section Semiring

variable [Semiring K] [AddCommMonoid V] [AddCommMonoid W] [Module K V] [Module K W]

/-- A Jordan-chain basis of `f` indexed by `ι`: chain `i` has head `head i` and positive length
`len i`, the power `f ^ len i` kills `head i`, and the vectors `f ^ j (head i)`, `j < len i`,
form a basis of `V`. In this basis `f` is the direct sum of nilpotent Jordan blocks of sizes
`len i`. -/
@[ext]
structure JordanChainBasis (f : End K V) (ι : Type*) where
  /-- The length of each chain. -/
  len : ι → ℕ
  /-- The head of each chain. -/
  head : ι → V
  len_pos (i : ι) : 0 < len i
  pow_len_apply_head (i : ι) : (f ^ len i) (head i) = 0
  linearIndependent :
    LinearIndependent K fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)
  span_eq_top : span K (Set.range fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)) = ⊤

namespace JordanChainBasis

variable {f : End K V} {g : End K W} {ι κ : Type*}

/-- The basis `f ^ j (head i)`, `j < len i`, of a Jordan-chain basis. -/
noncomputable def basis (c : f.JordanChainBasis ι) : Basis (Σ i, Fin (c.len i)) K V :=
  .mk c.linearIndependent c.span_eq_top.ge

@[simp]
theorem basis_apply (c : f.JordanChainBasis ι) (p : Σ i, Fin (c.len i)) :
    c.basis p = (f ^ (p.2 : ℕ)) (c.head p.1) :=
  Basis.mk_apply _ _ _

/-- A power of `f` moves a vector of a Jordan-chain basis along its chain, or kills it once it
reaches the end of the chain. -/
theorem pow_apply_basis (c : f.JordanChainBasis ι) (k : ℕ) (i : ι) (j : Fin (c.len i)) :
    (f ^ k) (c.basis ⟨i, j⟩) =
      if h : (j : ℕ) + k < c.len i then c.basis ⟨i, ⟨j + k, h⟩⟩ else 0 := by
  simp only [basis_apply, ← mul_apply, ← pow_add]
  split_ifs with h
  · rw [add_comm]
  · exact pow_map_zero_of_le (by omega) (c.pow_len_apply_head i)

/-- The endomorphism `f` moves a vector of a Jordan-chain basis one step along its chain, or kills
it at the end of the chain. -/
theorem apply_basis (c : f.JordanChainBasis ι) (i : ι) (j : Fin (c.len i)) :
    f (c.basis ⟨i, j⟩) = if h : (j : ℕ) + 1 < c.len i then c.basis ⟨i, ⟨j + 1, h⟩⟩ else 0 := by
  rw [← c.pow_apply_basis 1, pow_one]

/-- An endomorphism with a finite Jordan-chain basis is nilpotent. -/
theorem isNilpotent [Finite ι] (c : f.JordanChainBasis ι) : IsNilpotent f := by
  cases nonempty_fintype ι
  refine ⟨∑ i, c.len i, c.basis.ext fun ⟨i, j⟩ => ?_⟩
  have := Finset.single_le_sum (fun i _ => Nat.zero_le (c.len i)) (Finset.mem_univ i)
  simp only [c.pow_apply_basis, LinearMap.zero_apply, dite_eq_right_iff]
  omega

/-- The range of `f ^ k` is spanned by the vectors of a Jordan-chain basis at depth at least `k`
in their chains. -/
theorem range_pow (c : f.JordanChainBasis ι) (k : ℕ) :
    LinearMap.range (f ^ k) = span K (Set.range fun p : Σ i, Fin (c.len i - k) =>
      c.basis ⟨p.1, ⟨p.2 + k, by omega⟩⟩) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← c.basis.span_eq, map_span, span_le]
    rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    rw [c.pow_apply_basis]
    split_ifs with h
    · exact subset_span ⟨⟨i, ⟨j, by omega⟩⟩, rfl⟩
    · exact zero_mem _
  · rw [span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨c.basis ⟨i, ⟨j, by omega⟩⟩, by simp [← mul_apply, ← pow_add, add_comm]⟩

/-- The linear equivalence between the spaces of two Jordan-chain bases whose lengths agree under
the reindexing `σ`, matching chain vectors at equal depths in corresponding chains. It conjugates
one endomorphism to the other, see `apply_equiv`. -/
noncomputable def equiv (c : f.JordanChainBasis ι) (d : g.JordanChainBasis κ) (σ : ι ≃ κ)
    (hσ : ∀ i, d.len (σ i) = c.len i) : V ≃ₗ[K] W :=
  c.basis.equiv d.basis (.sigmaCongr σ fun i => finCongr (hσ i).symm)

/-- The conjugator of two Jordan-chain bases with matching lengths sends `f ^ j` of a chain head
to `g ^ j` of the corresponding head; past the end of the chains both sides vanish. -/
@[simp]
theorem equiv_pow_apply_head (c : f.JordanChainBasis ι) (d : g.JordanChainBasis κ) (σ : ι ≃ κ)
    (hσ : ∀ i, d.len (σ i) = c.len i) (i : ι) (j : ℕ) :
    c.equiv d σ hσ ((f ^ j) (c.head i)) = (g ^ j) (d.head (σ i)) := by
  by_cases hj : j < c.len i
  · -- `Equiv.sigmaCongr` acts on a pair componentwise by definition.
    have h : c.equiv d σ hσ (c.basis ⟨i, ⟨j, hj⟩⟩) = d.basis ⟨σ i, finCongr (hσ i).symm ⟨j, hj⟩⟩ :=
      Basis.equiv_apply ..
    simpa using h
  · rw [pow_map_zero_of_le (not_lt.1 hj) (c.pow_len_apply_head i), map_zero,
      pow_map_zero_of_le (by rw [hσ]; omega) (d.pow_len_apply_head (σ i))]

/-- The inverse of the conjugator of two Jordan-chain bases with matching lengths is the conjugator
in the opposite direction. -/
@[simp]
theorem equiv_symm (c : f.JordanChainBasis ι) (d : g.JordanChainBasis κ) (σ : ι ≃ κ)
    (hσ : ∀ i, d.len (σ i) = c.len i) :
    (c.equiv d σ hσ).symm = d.equiv c σ.symm fun j => by rw [← hσ, Equiv.apply_symm_apply] := by
  refine LinearEquiv.toLinearMap_injective (d.basis.ext fun ⟨i, j⟩ => ?_)
  simp [LinearEquiv.symm_apply_eq]

/-- The conjugator of two Jordan-chain bases with matching lengths intertwines the two
endomorphisms. -/
@[simp]
theorem apply_equiv (c : f.JordanChainBasis ι) (d : g.JordanChainBasis κ) (σ : ι ≃ κ)
    (hσ : ∀ i, d.len (σ i) = c.len i) (x : V) : g (c.equiv d σ hσ x) = c.equiv d σ hσ (f x) := by
  have h : g ∘ₗ (c.equiv d σ hσ).toLinearMap = (c.equiv d σ hσ).toLinearMap ∘ₗ f := by
    refine c.basis.ext fun ⟨i, j⟩ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, basis_apply, equiv_pow_apply_head]
    rw [← mul_apply, ← pow_succ', ← mul_apply, ← pow_succ', equiv_pow_apply_head]
  exact LinearMap.congr_fun h x

/-- The dimension of `V` is the sum of the lengths of the chains. -/
theorem finrank_eq_sum_len [StrongRankCondition K] [Fintype ι] (c : f.JordanChainBasis ι) :
    finrank K V = ∑ i, c.len i := by
  simp [finrank_eq_card_basis c.basis]

/-- The rank of `f ^ k` is `∑ i, (len i - k)`. -/
theorem finrank_range_pow [StrongRankCondition K] [Fintype ι] (c : f.JordanChainBasis ι)
    (k : ℕ) : finrank K (LinearMap.range (f ^ k)) = ∑ i, (c.len i - k) := by
  have hinj : Function.Injective fun p : Σ i, Fin (c.len i - k) =>
      (⟨p.1, ⟨p.2 + k, by omega⟩⟩ : Σ i, Fin (c.len i)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_iff_eq, Fin.ext_iff] at h
    obtain rfl : j = j' := Fin.ext (by omega)
    rfl
  rw [c.range_pow]
  exact (finrank_span_eq_card (c.basis.linearIndependent.comp _ hinj)).trans (by simp)

end JordanChainBasis

end Semiring

section CommSemiring

variable [CommSemiring K] [AddCommMonoid V] [AddCommMonoid W] [Module K V] [Module K W]
  {f : End K V} {g : End K W} {ι κ : Type*}

/-- Two endomorphisms are conjugate by the conjugator of Jordan-chain bases with matching
lengths. -/
@[simp]
theorem JordanChainBasis.conj_equiv (c : f.JordanChainBasis ι) (d : g.JordanChainBasis κ)
    (σ : ι ≃ κ) (hσ : ∀ i, d.len (σ i) = c.len i) : (c.equiv d σ hσ).conj f = g := by
  ext x
  rw [LinearEquiv.conj_apply_apply, ← apply_equiv, LinearEquiv.apply_symm_apply]

end CommSemiring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

namespace JordanChainBasis

variable {f : End K V} {g : End K W} {ι κ : Type*}

/-- The dimension of the kernel of `f ^ k` is `∑ i, min k (len i)`. -/
theorem finrank_ker_pow [Fintype ι] (c : f.JordanChainBasis ι) (k : ℕ) :
    finrank K (LinearMap.ker (f ^ k)) = ∑ i, min k (c.len i) := by
  have : FiniteDimensional K V := .of_basis c.basis
  have h := (f ^ k).finrank_range_add_finrank_ker
  rw [c.finrank_range_pow, c.finrank_eq_sum_len] at h
  have h' : ∑ i, c.len i = ∑ i, (c.len i - k) + ∑ i, min k (c.len i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  omega

/-- Passing from `f ^ k` to `f ^ (k + 1)`, the kernel grows by one dimension for each chain of
length greater than `k`. -/
theorem finrank_ker_pow_succ [Fintype ι] (c : f.JordanChainBasis ι) (k : ℕ) :
    finrank K (LinearMap.ker (f ^ (k + 1))) =
      finrank K (LinearMap.ker (f ^ k)) + #{i | k < c.len i} := by
  rw [c.finrank_ker_pow, c.finrank_ker_pow, Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> omega

/-- The number of Jordan chains of length `k + 1` is determined by the dimensions of the kernels
of `f ^ k`, `f ^ (k + 1)` and `f ^ (k + 2)`. -/
theorem card_len_eq_add_one [Fintype ι] (c : f.JordanChainBasis ι) (k : ℕ) :
    #{i | c.len i = k + 1} =
      (finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k))) -
        (finrank K (LinearMap.ker (f ^ (k + 2))) - finrank K (LinearMap.ker (f ^ (k + 1)))) := by
  have h : #{i | k < c.len i} = #{i | c.len i = k + 1} + #{i | k + 1 < c.len i} := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> omega
  rw [c.finrank_ker_pow_succ (k + 1), c.finrank_ker_pow_succ k]
  omega

/-- The lengths of two Jordan-chain bases agree up to reindexing as soon as the kernels of the
powers of the two endomorphisms have the same dimensions. For `g = f` this is the uniqueness of
the Jordan block sizes of `f`. -/
theorem exists_equiv_len_eq [Finite ι] [Finite κ] (c : f.JordanChainBasis ι)
    (d : g.JordanChainBasis κ)
    (h : ∀ k, finrank K (LinearMap.ker (f ^ k)) = finrank K (LinearMap.ker (g ^ k))) :
    ∃ σ : ι ≃ κ, ∀ i, d.len (σ i) = c.len i := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  have hcard (a : ℕ) : Fintype.card {i // c.len i = a} = Fintype.card {i // d.len i = a} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases a with _ | a
    · simp [(c.len_pos _).ne', (d.len_pos _).ne']
    · rw [c.card_len_eq_add_one, d.card_len_eq_add_one, h, h, h]
  exact ⟨.ofFiberEquiv fun a => Fintype.equivOfCardEq (hcard a), Equiv.ofFiberEquiv_map _⟩

end JordanChainBasis

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W] {f : End K V}
  {g : End K W}

/-- If `f ^ m` kills `v` and the linear form `φ` does not vanish at `f ^ (m - 1) v`, then the
vectors `j ↦ φ (f ^ j (f ^ i v))` of `Fin m → K`, for `i < m`, are linearly independent: they form
an anti-triangular system with nonzero antidiagonal. -/
private theorem linearIndependent_dual_pow_apply {m : ℕ} {v : V} (φ : Dual K V)
    (hv : (f ^ m) v = 0) (hφ : φ ((f ^ (m - 1)) v) ≠ 0) :
    LinearIndependent K fun i : Fin m => fun j : Fin m => φ ((f ^ (j : ℕ)) ((f ^ (i : ℕ)) v)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  suffices ∀ n, ∀ i : Fin m, (i : ℕ) = n → a i = 0 from fun i => this i i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro i rfl
    have hsum := congrFun ha ⟨m - 1 - i, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
    rw [Finset.sum_eq_single i] at hsum
    · rw [← mul_apply, ← pow_add, show m - 1 - i + i = m - 1 by omega] at hsum
      exact (mul_eq_zero.1 hsum).resolve_right hφ
    · intro i' _ hi'
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hi') with h | h
      · rw [ih i' h i' rfl, zero_mul]
      · rw [← mul_apply, ← pow_add, pow_map_zero_of_le (by omega) hv, map_zero, mul_zero]
    · simp

/-- Jordan chains for `f`, indexed by `ι`, whose vectors are linearly independent and span the
subspace `Z`. For `Z = ⊤` these are the data of a `JordanChainBasis`. -/
private structure JordanChains (f : End K V) (Z : Submodule K V) (ι : Type*) where
  /-- The length of each chain. -/
  len : ι → ℕ
  /-- The head of each chain. -/
  head : ι → V
  len_pos (i : ι) : 0 < len i
  pow_len_apply_head (i : ι) : (f ^ len i) (head i) = 0
  linearIndependent :
    LinearIndependent K fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)
  span_eq : span K (Set.range fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)) = Z

/-- Adding one more chain, of length `m` with head `v`, to Jordan chains spanning a subspace `Z`
disjoint from the span of the new chain. -/
private theorem exists_jordanChains_sup {m : ℕ} {v : V} (hm : 0 < m) (hv : (f ^ m) v = 0)
    (hu : LinearIndependent K fun i : Fin m => (f ^ (i : ℕ)) v) {Z : Submodule K V} {ι : Type}
    [Finite ι] (c : JordanChains f Z ι)
    (hdisj : Disjoint (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v)) Z) :
    ∃ (ι' : Type) (_ : Finite ι'),
      Nonempty (JordanChains f (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v) ⊔ Z) ι') := by
  rw [← c.span_eq] at hdisj ⊢
  let len₁ : Unit ⊕ ι → ℕ := Sum.elim (fun _ => m) c.len
  let head₁ : Unit ⊕ ι → V := Sum.elim (fun _ => v) c.head
  let F₁ (p : Σ i : Unit, Fin (len₁ (.inl i))) : V := (f ^ (p.2 : ℕ)) v
  let F₂ (p : Σ i : ι, Fin (len₁ (.inr i))) : V := (f ^ (p.2 : ℕ)) (c.head p.1)
  have hF : (fun p : Σ s, Fin (len₁ s) => (f ^ (p.2 : ℕ)) (head₁ p.1)) =
      Sum.elim F₁ F₂ ∘ Equiv.sumSigmaDistrib fun s => Fin (len₁ s) := by
    funext p
    rcases p with ⟨s | i, j⟩ <;> simp [F₁, F₂, head₁]
  -- `F₁` reparametrizes the chain of `v` by `Equiv.uniqueSigma`, whose inverse is `j ↦ ⟨(), j⟩`.
  let e := (Equiv.uniqueSigma fun i : Unit => Fin (len₁ (.inl i))).symm
  have h₁ : LinearIndependent K F₁ := (linearIndependent_equiv e).1 hu
  have hr₁ : Set.range F₁ = Set.range fun i : Fin m => (f ^ (i : ℕ)) v :=
    (EquivLike.range_comp F₁ e).symm
  refine ⟨Unit ⊕ ι, inferInstance, ⟨⟨len₁, head₁, ?_, ?_, ?_, ?_⟩⟩⟩
  · rintro (_ | i)
    exacts [hm, c.len_pos i]
  · rintro (_ | i)
    exacts [hv, c.pow_len_apply_head i]
  · rw [hF, linearIndependent_equiv]
    refine h₁.sum_type c.linearIndependent ?_
    rwa [hr₁]
  · rw [hF, EquivLike.range_comp, Set.Sum.elim_range, span_union, hr₁]
    -- `F₂` is the family of the given chains, with `len₁ (.inr i)` unfolding to `len i`.
    rfl

/-- The invariant complement of Halmos §57: if `f ^ m` kills the `f`-invariant subspace `Z`,
`v ∈ Z`, and the linear form `φ` does not vanish at `f ^ (m - 1) v`, then the chain of `v` is
linearly independent, and `Z` has an `f`-invariant subspace `Z'` of dimension `finrank K Z - m`
that meets the span of the chain trivially and together with it spans `Z`. The subspace `Z'` is
the common kernel in `Z` of the forms `φ ∘ f ^ j`, `j < m`. -/
private theorem invariant_complement [FiniteDimensional K V] {m : ℕ} {Z : Submodule K V}
    (hZ : ∀ x ∈ Z, f x ∈ Z) (hfm : ∀ x ∈ Z, (f ^ m) x = 0) {v : V} (hvZ : v ∈ Z) (φ : Dual K V)
    (hφ : φ ((f ^ (m - 1)) v) ≠ 0) :
    LinearIndependent K (fun i : Fin m => (f ^ (i : ℕ)) v) ∧
    ∃ Z' : Submodule K V, (∀ x ∈ Z', f x ∈ Z') ∧
      Disjoint (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v)) Z' ∧
      span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v) ⊔ Z' = Z ∧
      finrank K Z' + m = finrank K Z := by
  set u : Fin m → V := fun i => (f ^ (i : ℕ)) v
  set Φ : V →ₗ[K] Fin m → K := LinearMap.pi fun j => φ ∘ₗ f ^ (j : ℕ) with hΦ
  have hΦu : LinearIndependent K (Φ ∘ u) := linearIndependent_dual_pow_apply φ (hfm v hvZ) hφ
  have hu : LinearIndependent K u := hΦu.of_comp Φ
  -- The span `C` of the chain of `v` meets the common kernel of the `φ ∘ f ^ j` trivially.
  have hdisj : Disjoint (span K (Set.range u)) (LinearMap.ker Φ) :=
    Submodule.range_ker_disjoint hΦu
  -- Dimension count for `Z' = Z ⊓ ker Φ`: `C ⊔ Z' ≤ Z` and `dim C + dim Z' ≥ dim Z`.
  have hC : finrank K (span K (Set.range u)) = m := by
    rw [finrank_span_eq_card hu, Fintype.card_fin]
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (span K (Set.range u)) (Z ⊓ LinearMap.ker Φ)
  rw [(hdisj.mono_right inf_le_right).eq_bot, finrank_bot] at h4
  have hsup : span K (Set.range u) ⊔ Z ⊓ LinearMap.ker Φ = Z := by
    have hCZ : span K (Set.range u) ≤ Z := by
      refine span_le.2 (Set.range_subset_iff.2 fun i => ?_)
      simp only [u, SetLike.mem_coe, pow_apply]
      exact Set.MapsTo.iterate hZ i hvZ
    have hrange : finrank K (LinearMap.range Φ) ≤ m := (Submodule.finrank_le _).trans (by simp)
    have h1 := Φ.finrank_range_add_finrank_ker
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq Z (LinearMap.ker Φ)
    have h3 := Submodule.finrank_le (Z ⊔ LinearMap.ker Φ)
    exact Submodule.eq_of_le_of_finrank_le (sup_le hCZ inf_le_left) (by omega)
  refine ⟨hu, Z ⊓ LinearMap.ker Φ, ?_, hdisj.mono_right inf_le_right, hsup, by
    rw [hsup] at h4; omega⟩
  -- The complement `Z'` is `f`-invariant.
  intro x hx
  rw [Submodule.mem_inf, LinearMap.mem_ker] at hx ⊢
  refine ⟨hZ x hx.1, funext fun j => ?_⟩
  simp only [hΦ, LinearMap.pi_apply, LinearMap.comp_apply, Pi.zero_apply]
  rw [← mul_apply, ← pow_succ]
  by_cases hj : (j : ℕ) + 1 < m
  · exact congrFun hx.2 ⟨j + 1, hj⟩
  · rw [show (j : ℕ) + 1 = m by omega, hfm x hx.1, map_zero]

/-- Every `f`-invariant subspace `Z` on which `f` is nilpotent is spanned by Jordan chains whose
vectors are linearly independent. The proof splits off a chain of maximal length together with an
invariant complement, and recurses on the dimension of `Z`. -/
private theorem exists_jordanChains [FiniteDimensional K V] (hf : IsNilpotent f)
    (Z : Submodule K V) (hZ : ∀ x ∈ Z, f x ∈ Z) :
    ∃ (ι : Type) (_ : Finite ι), Nonempty (JordanChains f Z ι) := by
  classical
  induction hd : finrank K Z using Nat.strong_induction_on generalizing Z with
  | _ d ih =>
  have hex : ∃ k, Z ≤ LinearMap.ker (f ^ k) := by
    obtain ⟨n, hn⟩ := hf
    exact ⟨n, by simp [hn]⟩
  -- `m` is the nilpotency index of `f` on `Z`.
  set m := Nat.find hex
  have hfm (x : V) (hx : x ∈ Z) : (f ^ m) x = 0 := Nat.find_spec hex hx
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · refine ⟨Empty, inferInstance, ⟨⟨Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
      linearIndependent_empty_type, ?_⟩⟩⟩
    rw [Set.range_eq_empty, span_empty, eq_comm, eq_bot_iff]
    intro x hx
    simpa [h0] using hfm x hx
  -- A vector `v` with a chain of maximal length `m`, and a form `φ` detecting its last vector.
  obtain ⟨v, hvZ, hv⟩ : ∃ v ∈ Z, (f ^ (m - 1)) v ≠ 0 := by
    simpa [IsConcreteLE.not_le_iff_exists] using Nat.find_min hex (show m - 1 < m by omega)
  obtain ⟨φ, hφ⟩ : ∃ φ : Dual K V, φ ((f ^ (m - 1)) v) ≠ 0 := by
    simpa using (Module.forall_dual_apply_eq_zero_iff K _).not.2 hv
  obtain ⟨hu, Z', hZ', hdisj, hsup, hdim⟩ := invariant_complement hZ hfm hvZ φ hφ
  -- The complement is smaller than `Z`, since the chain of `v` has length `m > 0`.
  obtain ⟨ι, _, ⟨c⟩⟩ := ih _ (by omega) Z' hZ' rfl
  obtain ⟨ι', _, ⟨c'⟩⟩ := exists_jordanChains_sup hpos (hfm v hvZ) hu c hdisj
  exact ⟨ι', inferInstance, ⟨{ c' with span_eq := c'.span_eq.trans hsup }⟩⟩

/-- A nilpotent endomorphism of a finite-dimensional vector space has a Jordan-chain basis. -/
theorem exists_jordanChainBasis [FiniteDimensional K V] (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (f.JordanChainBasis ι) := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChains hf ⊤ fun _ _ => mem_top
  exact ⟨ι, .ofFinite ι, ⟨⟨c.len, c.head, c.len_pos, c.pow_len_apply_head, c.linearIndependent,
    c.span_eq⟩⟩⟩

/-- An endomorphism of a finite-dimensional vector space is nilpotent if and only if it has a
Jordan-chain basis. -/
theorem isNilpotent_iff_exists_jordanChainBasis [FiniteDimensional K V] :
    IsNilpotent f ↔ ∃ (ι : Type) (_ : Fintype ι), Nonempty (f.JordanChainBasis ι) :=
  ⟨exists_jordanChainBasis, fun ⟨_, _, ⟨c⟩⟩ => c.isNilpotent⟩

/-- Two nilpotent endomorphisms of finite-dimensional vector spaces are conjugate if and only if
the kernels of their powers have the same dimensions. -/
theorem exists_linearEquiv_conj_eq_iff [FiniteDimensional K V] [FiniteDimensional K W]
    (hf : IsNilpotent f) (hg : IsNilpotent g) :
    (∃ e : V ≃ₗ[K] W, e.conj f = g) ↔
      ∀ k, finrank K (LinearMap.ker (f ^ k)) = finrank K (LinearMap.ker (g ^ k)) := by
  constructor
  · rintro ⟨e, rfl⟩ k
    rw [← LinearEquiv.conj_pow, LinearEquiv.finrank_ker_conj]
  · intro h
    obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hf
    obtain ⟨κ, _, ⟨d⟩⟩ := exists_jordanChainBasis hg
    obtain ⟨σ, hσ⟩ := c.exists_equiv_len_eq d h
    exact ⟨c.equiv d σ hσ, c.conj_equiv d σ hσ⟩

end Field

section Degeneration

namespace JordanChainBasis

section Semiring

variable [Semiring K] [AddCommMonoid V] [Module K V] {f : End K V} {ι : Type*}

/-- The coordinate of depth `b` in a Jordan-chain basis vanishes on the range of `f ^ k` when
`b < k`. -/
@[simp]
theorem basis_coord_comp_pow_eq_zero (c : f.JordanChainBasis ι) {p : Σ i, Fin (c.len i)}
    {k : ℕ} (hk : (p.2 : ℕ) < k) : c.basis.coord p ∘ₗ f ^ k = 0 := by
  refine c.basis.ext fun q => ?_
  rw [LinearMap.comp_apply, c.pow_apply_basis k q.1 q.2]
  split_ifs with h
  · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne, LinearMap.zero_apply]
    intro hq
    have := congrArg (fun r : Σ i, Fin (c.len i) => (r.2 : ℕ)) hq
    simp only at this
    omega
  · simp

/-- The last vector `f ^ (len j - 1) (head j)` of chain `j` lies in the range of `f ^ k` exactly
when `k < len j`. -/
theorem pow_apply_head_mem_range_pow_iff [Nontrivial K] (c : f.JordanChainBasis ι) (j : ι)
    (k : ℕ) : (f ^ (c.len j - 1)) (c.head j) ∈ LinearMap.range (f ^ k) ↔ k < c.len j := by
  refine ⟨fun ⟨y, hy⟩ => ?_, fun hk => ⟨(f ^ (c.len j - 1 - k)) (c.head j), ?_⟩⟩
  · by_contra! hk
    have h := LinearMap.congr_fun (c.basis_coord_comp_pow_eq_zero
      (p := ⟨j, ⟨c.len j - 1, by have := c.len_pos j; omega⟩⟩) (k := k)
      (by dsimp only; have := c.len_pos j; omega)) y
    rw [LinearMap.comp_apply, hy,
      ← basis_apply c ⟨j, ⟨c.len j - 1, by have := c.len_pos j; omega⟩⟩, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_eq_same, LinearMap.zero_apply] at h
    exact one_ne_zero h
  · rw [← mul_apply, ← pow_add]
    congr 2
    omega

end Semiring

section CommSemiring

variable [CommSemiring K] [AddCommMonoid V] [Module K V] {f : End K V} {ι : Type*}

/-- The rank-one endomorphism sending the last vector `f ^ (len i - 1) (head i)` of chain `i` to
the last vector of chain `j`, and every other vector of the Jordan-chain basis to `0`. -/
noncomputable def joinEnds (c : f.JordanChainBasis ι) (i j : ι) : End K V :=
  (c.basis.coord ⟨i, ⟨c.len i - 1, by have := c.len_pos i; omega⟩⟩).smulRight
    ((f ^ (c.len j - 1)) (c.head j))

/-- The endomorphism `joinEnds i j` multiplies the last vector of chain `j` by the coordinate of
the last vector of chain `i`. -/
theorem joinEnds_apply (c : f.JordanChainBasis ι) (i j : ι) (x : V) :
    c.joinEnds i j x =
      c.basis.repr x ⟨i, ⟨c.len i - 1, by have := c.len_pos i; omega⟩⟩ •
        (f ^ (c.len j - 1)) (c.head j) := by
  simp only [joinEnds, LinearMap.smulRight_apply, Basis.coord_apply]

/-- The endomorphism `joinEnds i j` sends the last vector of chain `i` to the last vector of
chain `j`. -/
@[simp]
theorem joinEnds_pow_apply_head (c : f.JordanChainBasis ι) (i j : ι) :
    c.joinEnds i j ((f ^ (c.len i - 1)) (c.head i)) = (f ^ (c.len j - 1)) (c.head j) := by
  rw [joinEnds_apply, ← basis_apply c ⟨i, ⟨c.len i - 1, by have := c.len_pos i; omega⟩⟩,
    Basis.repr_self, Finsupp.single_eq_same, one_smul]

/-- The image of `joinEnds i j` is killed by `f`, being spanned by the end of a chain. -/
@[simp]
theorem mul_joinEnds (c : f.JordanChainBasis ι) (i j : ι) : f * c.joinEnds i j = 0 := by
  ext x
  rw [mul_apply, joinEnds_apply, map_smul, ← mul_apply, ← pow_succ',
    Nat.sub_add_cancel (c.len_pos j), c.pow_len_apply_head, smul_zero, LinearMap.zero_apply]

/-- For distinct chains `i ≠ j`, the endomorphism `joinEnds i j` squares to zero. -/
@[simp]
theorem joinEnds_mul_joinEnds (c : f.JordanChainBasis ι) {i j : ι} (hij : i ≠ j) :
    c.joinEnds i j * c.joinEnds i j = 0 := by
  ext x
  rw [mul_apply, joinEnds_apply (x := x), map_smul, joinEnds_apply,
    ← basis_apply c ⟨j, ⟨c.len j - 1, by have := c.len_pos j; omega⟩⟩, Basis.repr_self,
    Finsupp.single_eq_of_ne, zero_smul, smul_zero, LinearMap.zero_apply]
  intro h
  exact hij (congrArg Sigma.fst h)

/-- The endomorphism `joinEnds i j` vanishes on the range of `f ^ k` once `len i ≤ k`. -/
@[simp]
theorem joinEnds_mul_pow_of_le (c : f.JordanChainBasis ι) (i j : ι) {k : ℕ} (hk : c.len i ≤ k) :
    c.joinEnds i j * f ^ k = 0 := by
  ext x
  have h := LinearMap.congr_fun (c.basis_coord_comp_pow_eq_zero
    (p := ⟨i, ⟨c.len i - 1, by have := c.len_pos i; omega⟩⟩) (k := k)
    (by dsimp only; have := c.len_pos i; omega)) x
  rw [LinearMap.comp_apply, Basis.coord_apply, LinearMap.zero_apply] at h
  rw [mul_apply, joinEnds_apply, h, zero_smul, LinearMap.zero_apply]

/-- For distinct chains `i ≠ j`, the powers of `f + t • joinEnds i j` are
`f ^ (k + 1) + t • joinEnds i j * f ^ k`, since `f * joinEnds i j` and `joinEnds i j ^ 2`
vanish. -/
theorem add_smul_joinEnds_pow_succ (c : f.JordanChainBasis ι) {i j : ι} (hij : i ≠ j) (t : K)
    (k : ℕ) :
    (f + t • c.joinEnds i j) ^ (k + 1) = f ^ (k + 1) + t • (c.joinEnds i j * f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, pow_succ' f (k + 1)]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ← mul_assoc, c.mul_joinEnds,
      c.joinEnds_mul_joinEnds hij, zero_mul, smul_zero, add_zero]

/-- For distinct chains `i ≠ j` of a finite Jordan-chain basis, `f + t • joinEnds i j` is
nilpotent. -/
theorem isNilpotent_add_smul_joinEnds [Finite ι] (c : f.JordanChainBasis ι) {i j : ι}
    (hij : i ≠ j) (t : K) : IsNilpotent (f + t • c.joinEnds i j) := by
  obtain ⟨N, hN⟩ := c.isNilpotent
  exact ⟨N + 1, by rw [c.add_smul_joinEnds_pow_succ hij, hN, mul_zero, smul_zero, pow_succ, hN,
    zero_mul, add_zero]⟩

end CommSemiring

section Field

variable [Field K] [AddCommGroup V] [Module K V] {f : End K V} {ι : Type*}

/-- For `t ≠ 0` and `0 < k ≤ len i`, the range of `(f + t • joinEnds i j) ^ k` is spanned by the
range of `f ^ k` together with the last vector of chain `j`. -/
theorem range_add_smul_joinEnds_pow (c : f.JordanChainBasis ι) {i j : ι} (hij : i ≠ j) {t : K}
    (ht : t ≠ 0) {k : ℕ} (hk₀ : 0 < k) (hk : k ≤ c.len i) :
    LinearMap.range ((f + t • c.joinEnds i j) ^ k) =
      LinearMap.range (f ^ k) ⊔ K ∙ (f ^ (c.len j - 1)) (c.head j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk₀
  rw [zero_add] at hk ⊢
  set d := (f ^ (c.len j - 1)) (c.head j)
  have hE (x : V) : (t • (c.joinEnds i j * f ^ k)) x ∈ K ∙ d := by
    rw [LinearMap.smul_apply, mul_apply, joinEnds_apply]
    exact smul_mem _ _ (smul_mem _ _ (mem_span_singleton_self d))
  -- The vector `f ^ (len i - k - 1) (head i)` is sent to `t • d`.
  have hd : d ∈ LinearMap.range ((f + t • c.joinEnds i j) ^ (k + 1)) := by
    refine ⟨t⁻¹ • (f ^ (c.len i - (k + 1))) (c.head i), ?_⟩
    rw [map_smul, c.add_smul_joinEnds_pow_succ hij, LinearMap.add_apply, LinearMap.smul_apply,
      mul_apply, ← mul_apply (f ^ (k + 1)), ← pow_add, ← mul_apply (f ^ k), ← pow_add,
      Nat.add_sub_cancel' hk, show k + (c.len i - (k + 1)) = c.len i - 1 by omega,
      c.pow_len_apply_head, joinEnds_pow_apply_head, zero_add, smul_smul, inv_mul_cancel₀ ht,
      one_smul]
  have hspan := (span_singleton_le_iff_mem _ _).2 hd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [c.add_smul_joinEnds_pow_succ hij, LinearMap.add_apply]
    exact add_mem (mem_sup_left ⟨x, rfl⟩) (mem_sup_right (hE x))
  · refine sup_le ?_ hspan
    rintro _ ⟨x, rfl⟩
    have h := congrArg (· - (t • (c.joinEnds i j * f ^ k)) x)
      (LinearMap.congr_fun (c.add_smul_joinEnds_pow_succ hij t k) x)
    simp only [LinearMap.add_apply, add_sub_cancel_right] at h
    rw [← h]
    exact sub_mem ⟨x, rfl⟩ (hspan (hE x))

/-- **Ranks along an elementary degeneration.** For distinct chains `i ≠ j` and `t ≠ 0`, the rank
of `(f + t • joinEnds i j) ^ k` exceeds the rank of `f ^ k` by one when `len j ≤ k ≤ len i`, and
equals it otherwise. -/
theorem finrank_range_add_smul_joinEnds_pow [Finite ι] (c : f.JordanChainBasis ι) {i j : ι}
    (hij : i ≠ j) {t : K} (ht : t ≠ 0) (k : ℕ) :
    finrank K (LinearMap.range ((f + t • c.joinEnds i j) ^ k)) =
      finrank K (LinearMap.range (f ^ k)) + if c.len j ≤ k ∧ k ≤ c.len i then 1 else 0 := by
  cases nonempty_fintype ι
  have : FiniteDimensional K V := .of_basis c.basis
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · rw [pow_zero, pow_zero, left_eq_add, ite_eq_right_iff]
    have := c.len_pos j
    omega
  by_cases hk : k ≤ c.len i
  · rw [c.range_add_smul_joinEnds_pow hij ht hk₀ hk]
    split_ifs with hj
    · rw [finrank_sup_span_singleton]
      rw [c.pow_apply_head_mem_range_pow_iff]
      omega
    · rw [add_zero, sup_eq_left.2]
      rw [span_singleton_le_iff_mem, c.pow_apply_head_mem_range_pow_iff]
      omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk₀
    rw [zero_add] at hk ⊢
    rw [c.add_smul_joinEnds_pow_succ hij, c.joinEnds_mul_pow_of_le i j (by omega), smul_zero,
      add_zero, left_eq_add, ite_eq_right_iff]
    omega

/-- **The elementary degeneration has a single orbit away from `t = 0`.** For distinct chains
`i ≠ j` and `s, t ≠ 0`, the endomorphisms `f + s • joinEnds i j` and `f + t • joinEnds i j` are
conjugate. -/
theorem exists_linearEquiv_conj_add_smul_joinEnds [Finite ι] (c : f.JordanChainBasis ι)
    {i j : ι} (hij : i ≠ j) {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e.conj (f + s • c.joinEnds i j) = f + t • c.joinEnds i j := by
  cases nonempty_fintype ι
  have : FiniteDimensional K V := .of_basis c.basis
  refine (exists_linearEquiv_conj_eq_iff (c.isNilpotent_add_smul_joinEnds hij s)
    (c.isNilpotent_add_smul_joinEnds hij t)).2 fun k => ?_
  have hs' := LinearMap.finrank_range_add_finrank_ker ((f + s • c.joinEnds i j) ^ k)
  have ht' := LinearMap.finrank_range_add_finrank_ker ((f + t • c.joinEnds i j) ^ k)
  rw [c.finrank_range_add_smul_joinEnds_pow hij hs] at hs'
  rw [c.finrank_range_add_smul_joinEnds_pow hij ht] at ht'
  omega

end Field

end JordanChainBasis

end Degeneration

end Module.End
