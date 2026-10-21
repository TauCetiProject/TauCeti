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

## Implementation notes

Existence is proved by splitting off one chain of maximal length together with an invariant
complement. If `f ^ m` kills the invariant subspace `Z` but `f ^ (m - 1) v ≠ 0` for some `v ∈ Z`,
choose a linear form `φ` with `φ (f ^ (m - 1) v) ≠ 0`. The common kernel in `Z` of the forms
`φ ∘ f ^ j`, `j < m`, is invariant and complementary in `Z` to the span of the chain of `v`.

## References

* P. R. Halmos, *Finite-Dimensional Vector Spaces*, §57.
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

/-- The conjugator of two Jordan-chain bases with matching lengths intertwines the two
endomorphisms. -/
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

/-- Adding one more chain, of length `m` with head `v`, to a linearly independent family of Jordan
chains whose span is disjoint from the span of the new chain. -/
private theorem exists_jordanChains_sup {m : ℕ} {v : V} (hm : 0 < m) (hv : (f ^ m) v = 0)
    (hu : LinearIndependent K fun i : Fin m => (f ^ (i : ℕ)) v) {ι : Type} [Finite ι]
    {len : ι → ℕ} {head : ι → V} (hpos : ∀ i, 0 < len i) (hpow : ∀ i, (f ^ len i) (head i) = 0)
    (hli : LinearIndependent K fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1))
    (hdisj : Disjoint (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v))
      (span K (Set.range fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)))) :
    ∃ (ι' : Type) (_ : Finite ι') (len' : ι' → ℕ) (head' : ι' → V), (∀ i, 0 < len' i) ∧
      (∀ i, (f ^ len' i) (head' i) = 0) ∧
      LinearIndependent K (fun p : Σ i, Fin (len' i) => (f ^ (p.2 : ℕ)) (head' p.1)) ∧
      span K (Set.range fun p : Σ i, Fin (len' i) => (f ^ (p.2 : ℕ)) (head' p.1)) =
        span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v) ⊔
          span K (Set.range fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)) := by
  let len₁ : Unit ⊕ ι → ℕ := Sum.elim (fun _ => m) len
  let head₁ : Unit ⊕ ι → V := Sum.elim (fun _ => v) head
  let F₁ (p : Σ i : Unit, Fin (len₁ (.inl i))) : V := (f ^ (p.2 : ℕ)) v
  let F₂ (p : Σ i : ι, Fin (len₁ (.inr i))) : V := (f ^ (p.2 : ℕ)) (head p.1)
  have hF : (fun p : Σ s, Fin (len₁ s) => (f ^ (p.2 : ℕ)) (head₁ p.1)) =
      Sum.elim F₁ F₂ ∘ Equiv.sumSigmaDistrib fun s => Fin (len₁ s) := by
    funext p
    rcases p with ⟨s | i, j⟩ <;> rfl
  -- `F₁` reparametrizes the chain of `v` by `Equiv.uniqueSigma`, whose inverse is `j ↦ ⟨(), j⟩`.
  let e := (Equiv.uniqueSigma fun i : Unit => Fin (len₁ (.inl i))).symm
  have h₁ : LinearIndependent K F₁ := (linearIndependent_equiv e).1 hu
  have hr₁ : Set.range F₁ = Set.range fun i : Fin m => (f ^ (i : ℕ)) v :=
    (EquivLike.range_comp F₁ e).symm
  refine ⟨Unit ⊕ ι, inferInstance, len₁, head₁, ?_, ?_, ?_, ?_⟩
  · rintro (_ | i)
    exacts [hm, hpos i]
  · rintro (_ | i)
    exacts [hv, hpow i]
  · rw [hF, linearIndependent_equiv]
    refine h₁.sum_type hli ?_
    rwa [hr₁]
  · rw [hF, EquivLike.range_comp, Set.Sum.elim_range, span_union, hr₁]
    -- `F₂` is the family of the given chains, with `len₁ (.inr i)` unfolding to `len i`.
    rfl

/-- The invariant complement of Halmos §57: if `f ^ m` kills the `f`-invariant subspace `Z`,
`v ∈ Z`, and the linear form `φ` does not vanish at `f ^ (m - 1) v`, then the common kernel in
`Z` of the forms `φ ∘ f ^ j`, `j < m`, is `f`-invariant, meets the span of the chain of `v`
trivially, and together with it spans `Z`. -/
private theorem invariant_complement [FiniteDimensional K V] {m : ℕ} {Z : Submodule K V}
    (hZ : ∀ x ∈ Z, f x ∈ Z) (hfm : ∀ x ∈ Z, (f ^ m) x = 0) {v : V} (hvZ : v ∈ Z) (φ : Dual K V)
    (hφ : φ ((f ^ (m - 1)) v) ≠ 0) :
    (∀ x ∈ Z ⊓ LinearMap.ker (LinearMap.pi fun j : Fin m => φ ∘ₗ f ^ (j : ℕ)),
      f x ∈ Z ⊓ LinearMap.ker (LinearMap.pi fun j : Fin m => φ ∘ₗ f ^ (j : ℕ))) ∧
    Disjoint (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v))
      (Z ⊓ LinearMap.ker (LinearMap.pi fun j : Fin m => φ ∘ₗ f ^ (j : ℕ))) ∧
    span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v) ⊔
      Z ⊓ LinearMap.ker (LinearMap.pi fun j : Fin m => φ ∘ₗ f ^ (j : ℕ)) = Z := by
  set u : Fin m → V := fun i => (f ^ (i : ℕ)) v
  set Φ : V →ₗ[K] Fin m → K := LinearMap.pi fun j => φ ∘ₗ f ^ (j : ℕ) with hΦ
  have hΦu : LinearIndependent K (Φ ∘ u) := linearIndependent_dual_pow_apply φ (hfm v hvZ) hφ
  have hu : LinearIndependent K u := hΦu.of_comp Φ
  -- The span `C` of the chain of `v` meets the common kernel of the `φ ∘ f ^ j` trivially.
  have hdisj : Disjoint (span K (Set.range u)) (LinearMap.ker Φ) := by
    rw [Submodule.disjoint_def]
    intro x hxC hxΦ
    obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun K).1 hxC
    rw [LinearMap.mem_ker, map_sum] at hxΦ
    simp only [map_smul] at hxΦ
    simp [Fintype.linearIndependent_iff.1 hΦu a hxΦ]
  refine ⟨?_, hdisj.mono_right inf_le_right, ?_⟩
  · -- The complement `Z'` is `f`-invariant.
    intro x hx
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hx ⊢
    refine ⟨hZ x hx.1, funext fun j => ?_⟩
    simp only [hΦ, LinearMap.pi_apply, LinearMap.comp_apply, Pi.zero_apply]
    rw [← mul_apply, ← pow_succ]
    by_cases hj : (j : ℕ) + 1 < m
    · exact congrFun hx.2 ⟨j + 1, hj⟩
    · rw [show (j : ℕ) + 1 = m by omega, hfm x hx.1, map_zero]
  · -- Dimension count: `C ⊔ Z' ≤ Z` and `dim C + dim Z' ≥ dim Z`.
    have hCZ : span K (Set.range u) ≤ Z := by
      refine span_le.2 (Set.range_subset_iff.2 fun i => ?_)
      simp only [u, SetLike.mem_coe, pow_apply]
      exact Set.MapsTo.iterate hZ i hvZ
    have hC : finrank K (span K (Set.range u)) = m := by
      rw [finrank_span_eq_card hu, Fintype.card_fin]
    have hrange : finrank K (LinearMap.range Φ) ≤ m := (Submodule.finrank_le _).trans (by simp)
    have h1 := Φ.finrank_range_add_finrank_ker
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq Z (LinearMap.ker Φ)
    have h3 := Submodule.finrank_le (Z ⊔ LinearMap.ker Φ)
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq (span K (Set.range u))
      (Z ⊓ LinearMap.ker Φ)
    rw [(hdisj.mono_right inf_le_right).eq_bot, finrank_bot] at h4
    exact Submodule.eq_of_le_of_finrank_le (sup_le hCZ inf_le_left) (by omega)

/-- Every `f`-invariant subspace `Z` on which `f` is nilpotent is spanned by Jordan chains whose
vectors are linearly independent. The proof splits off a chain of maximal length together with an
invariant complement, and recurses on the dimension of `Z`. -/
private theorem exists_jordanChains [FiniteDimensional K V] (hf : IsNilpotent f)
    (Z : Submodule K V) (hZ : ∀ x ∈ Z, f x ∈ Z) :
    ∃ (ι : Type) (_ : Finite ι) (len : ι → ℕ) (head : ι → V), (∀ i, 0 < len i) ∧
      (∀ i, (f ^ len i) (head i) = 0) ∧
      LinearIndependent K (fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)) ∧
      span K (Set.range fun p : Σ i, Fin (len i) => (f ^ (p.2 : ℕ)) (head p.1)) = Z := by
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
  · refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
      linearIndependent_empty_type, ?_⟩
    rw [Set.range_eq_empty, span_empty, eq_comm, eq_bot_iff]
    intro x hx
    simpa [h0] using hfm x hx
  -- A vector `v` with a chain of maximal length `m`, and a form `φ` detecting its last vector.
  obtain ⟨v, hvZ, hv⟩ : ∃ v ∈ Z, (f ^ (m - 1)) v ≠ 0 := by
    simpa [IsConcreteLE.not_le_iff_exists] using Nat.find_min hex (show m - 1 < m by omega)
  obtain ⟨φ, hφ⟩ : ∃ φ : Dual K V, φ ((f ^ (m - 1)) v) ≠ 0 := by
    simpa using (Module.forall_dual_apply_eq_zero_iff K _).not.2 hv
  obtain ⟨hZ', hdisj, hsup⟩ := invariant_complement hZ hfm hvZ φ hφ
  let Φ : V →ₗ[K] Fin m → K := LinearMap.pi fun j => φ ∘ₗ f ^ (j : ℕ)
  have hu : LinearIndependent K fun i : Fin m => (f ^ (i : ℕ)) v :=
    (linearIndependent_dual_pow_apply φ (hfm v hvZ) hφ).of_comp Φ
  -- The complement is smaller than `Z`, since the chain of `v` spans an `m`-dimensional subspace.
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (span K (Set.range fun i : Fin m => (f ^ (i : ℕ)) v)) (Z ⊓ LinearMap.ker Φ)
  rw [hdisj.eq_bot, finrank_bot, hsup, finrank_span_eq_card hu, Fintype.card_fin] at h
  obtain ⟨ι, _, len, head, hpos', hpow', hli', hspan'⟩ :=
    ih _ (by omega) (Z ⊓ LinearMap.ker Φ) hZ' rfl
  obtain ⟨ι', _, len', head', h₁, h₂, h₃, h₄⟩ := exists_jordanChains_sup hpos (hfm v hvZ) hu
    hpos' hpow' hli' (hspan' ▸ hdisj)
  exact ⟨ι', inferInstance, len', head', h₁, h₂, h₃, by rw [h₄, hspan', hsup]⟩

/-- A nilpotent endomorphism of a finite-dimensional vector space has a Jordan-chain basis. -/
theorem exists_jordanChainBasis [FiniteDimensional K V] (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (f.JordanChainBasis ι) := by
  obtain ⟨ι, _, len, head, h₁, h₂, h₃, h₄⟩ := exists_jordanChains hf ⊤ fun _ _ => mem_top
  exact ⟨ι, .ofFinite ι, ⟨⟨len, head, h₁, h₂, h₃, h₄⟩⟩⟩

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

end Module.End
