/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis

/-!
# The coordinates of a pure symmetric tensor

`TauCeti/LinearAlgebra/SymmetricPower/Basis.lean` builds the basis `Module.Basis.symmetricPower`
of `Sym[R]^n M` induced by a basis `b : Basis κ R M`, and reads off the coordinates of a pure
symmetric tensor whose factors are *basis vectors*: it is a basis vector.  This file reads off the
coordinates of a pure symmetric tensor `⨂ₛ v` whose factors are arbitrary.

Expanding each factor in the basis and using multilinearity writes `⨂ₛ v` as a sum, over the
ordered tuples `p : Fin n → κ`, of the pure tensors `⨂ₛ i, b (p i)`, each scaled by
`∏ i, b.repr (v i) (p i)`.  Collecting the terms by the unordered tuple `TauCeti.Sym.ofFn p`
underlying `p` gives the coordinate at `s` as a sum over the orderings of `s`.

Two consequences are what the file exists for.

* **At a constant index the sum has one term.**  Only the constant tuple orders the unordered
  tuple `(k, …, k)`, so the coordinate of `⨂ₛ v` there is the plain product `∏ i, b.repr (v i) k`
  of one coordinate of each factor.
* **A pure power has no vanishing coordinate.**  The product `∏ i, b.repr (v i) (p i)` depends
  only on `TauCeti.Sym.ofFn p` when all the factors `v i` are equal, so the sum over the orderings
  of `s` has all its terms equal and no cancellation is possible: over a characteristic-zero
  commutative semiring with no zero divisors, `⨂ₛ (u, …, u)` has a nonzero coordinate at `s`
  whenever the coordinates of `u` indexed by the members of `s` are nonzero. For a general pure
  tensor this fails, the terms attached to different orderings being unrelated.

The basis index type may be infinite in every result below.

## Main results

* `Module.Basis.symmetricPower_repr_tprod_apply`: the coordinate of a pure symmetric tensor at
  `s` is the sum, over the orderings of `s`, of the products of the corresponding coordinates of
  the factors.
* `Module.Basis.symmetricPower_repr_tprod_apply_ofFn_const`: its value at a constant unordered
  tuple is a single product.
* `Module.Basis.symmetricPower_repr_tprod_const_apply_ne_zero`: a pure power has a nonzero
  coordinate at any unordered tuple of indices where the original vector has nonzero coordinates.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Appendix B, for the monomial basis of a symmetric power.
-/

public section

open Finset Module

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis κ R M)

/-- The single expansion step behind everything below: the coordinate at `s` of a pure symmetric
tensor of *scaled* basis vectors is the product of the scalars when the indices order `s`, and
zero otherwise. -/
private theorem symmetricPower_repr_tprod_apply_smul_basis [DecidableEq κ] (c : Fin n → R)
    (p : Fin n → κ) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, c i • b (p i)) s =
      if TauCeti.Sym.ofFn p = s then ∏ i, c i else 0 := by
  have hbasis : (tprod R fun i => b (p i)) = b.symmetricPower n (TauCeti.Sym.ofFn p) := by
    rw [Basis.symmetricPower_apply, tprodOfSym_ofFn]
  rw [(tprod R).map_smul_univ c fun i => b (p i), hbasis, map_smul, Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]

/-- **The coordinates of a pure symmetric tensor.**  Expanding each factor of `⨂ₛ v` in the basis
`b` and collecting the resulting pure tensors of basis vectors by the unordered tuple of indices
they use, the coordinate at `s` is the sum, over the ordered tuples `p` underlying `s`, of the
products of the corresponding coordinates of the factors.

For factors that are themselves basis vectors this recovers `Module.Basis.symmetricPower_apply`;
the content here is the general case. The basis index type may be infinite: the sum is finite
because a nonzero summand uses only the finite supports of the coordinates of the factors. -/
-- The constant-index formula below should simplify directly to a product.
@[simp low]
theorem _root_.Module.Basis.symmetricPower_repr_tprod_apply (v : Fin n → M) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) s =
      ∑ᶠ p ∈ {p : Fin n → κ | TauCeti.Sym.ofFn p = s}, ∏ i, b.repr (v i) (p i) := by
  classical
  have hv : (⨂ₛ[R] i, v i) =
      ⨂ₛ[R] i, ∑ j ∈ (b.repr (v i)).support, b.repr (v i) j • b j := by
    congr 1
    funext i
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (b.linearCombination_repr (v i)).symm
  rw [hv, (tprod R).map_sum_finset (fun (i : Fin n) (j : κ) => b.repr (v i) j • b j)
      fun i => (b.repr (v i)).support, map_sum, Finsupp.finsetSum_apply]
  simp_rw [symmetricPower_repr_tprod_apply_smul_basis]
  rw [finsum_mem_def]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  symm
  apply finsum_eq_sum_of_support_subset
  intro p hp
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff] at hp
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finsupp.mem_support_iff]
  intro i
  by_contra hi
  exact hp fun _ => Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- **The coordinates of a pure symmetric tensor at a constant unordered tuple.**  The only
ordering of `(k, …, k)` is the constant tuple, so the sum of
`Module.Basis.symmetricPower_repr_tprod_apply` collapses to a single product: one coordinate of
each factor.

This holds for arbitrary basis index types. -/
@[simp]
theorem _root_.Module.Basis.symmetricPower_repr_tprod_apply_ofFn_const (v : Fin n → M) (k : κ) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) (TauCeti.Sym.ofFn fun _ => k) =
      ∏ i, b.repr (v i) k := by
  classical
  rw [Basis.symmetricPower_repr_tprod_apply]
  have hconst {p : Fin n → κ}
      (h : TauCeti.Sym.ofFn p = TauCeti.Sym.ofFn fun _ => k) : p = fun _ => k := by
    obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 h
    exact funext fun i => by simpa using congrFun hσ (σ.symm i)
  have hindex : {p : Fin n → κ | TauCeti.Sym.ofFn p = TauCeti.Sym.ofFn fun _ => k} =
      {fun _ => k} := by
    ext p
    exact ⟨hconst, fun h => by simp [Set.mem_singleton_iff.mp h]⟩
  rw [hindex, finsum_mem_singleton]

end CommSemiring

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R] [CharZero R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)

/-- **Nonvanishing coordinates of a pure power.** Over a characteristic-zero commutative semiring
with no zero divisors, the coordinate of the pure power of `u` at `s` is nonzero whenever every
coordinate of `u` indexed by a member of `s` is nonzero. No conditions are imposed on the other
coordinates of `u`, and the basis index type may be infinite.

Nothing like this holds for a general pure tensor: the terms attached to different orderings of
`s` can cancel. -/
theorem _root_.Module.Basis.symmetricPower_repr_tprod_const_apply_ne_zero {u : M}
    (s : Sym κ n) (hu : ∀ k ∈ s, b.repr u k ≠ 0) :
    (b.symmetricPower n).repr (⨂ₛ[R] (_ : Fin n), u) s ≠ 0 := by
  classical
  obtain ⟨p₀, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  let orderings : Finset (Fin n → κ) := Finset.univ.image fun σ : Equiv.Perm (Fin n) => p₀ ∘ σ
  have horderings (p : Fin n → κ) : p ∈ orderings ↔ TauCeti.Sym.ofFn p = TauCeti.Sym.ofFn p₀ := by
    simp only [orderings, Finset.mem_image, Finset.mem_univ, true_and,
      ← TauCeti.Sym.ofFn_eq_ofFn_iff]
    exact eq_comm
  rw [Basis.symmetricPower_repr_tprod_apply]
  simp only [Set.mem_ofPred_eq]
  rw [finsum_cond_eq_sum_of_cond_iff _ (t := orderings) (fun _ => (horderings _).symm),
    Finset.sum_congr rfl (g := fun _ => ∏ i, b.repr u (p₀ i)) fun p hp => ?_]
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨p₀, (horderings p₀).2 rfl⟩).ne')
      (Finset.prod_ne_zero_iff.2 fun i _ => hu _ (TauCeti.Sym.mem_ofFn.2 ⟨i, rfl⟩))
  · obtain ⟨σ, rfl⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 ((horderings p).1 hp).symm
    exact Equiv.prod_comp σ fun i => b.repr u (p₀ i)

end NoZeroDivisors

end SymmetricPower
