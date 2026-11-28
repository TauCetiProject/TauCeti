/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Binomial.FilteredSpan

/-!
# Integral spans of finitely supported binomial products

`prodRingChooseSpan` is the integral additive span of finite products of binomial
coefficients in an arbitrary family in a commutative binomial ring. It is closed under
multiplication. The finite multiplication calculation is shared with the bounded ordered
spans in `TauCeti.RingTheory.Binomial.FilteredSpan`, by enumerating the union of the two
supports and extending the output exponents by zero.

Under linear independence, membership is equivalent to a unique finite integral expansion.
-/

public section

namespace TauCeti

open Finset

variable {R : Type*}

section ProductSpan

variable {σ : Type*} [CommRing R] [BinomialRing R]

/-- The additive subgroup spanned by finite products of binomial coefficients in a family. -/
noncomputable def prodRingChooseSpan (r : σ → R) : AddSubgroup R :=
  AddSubgroup.closure (Set.range fun n : σ →₀ ℕ =>
    n.prod (fun i k => Ring.choose (r i) k))

/-- The integral product span is the additive closure of the binomial products. -/
theorem prodRingChooseSpan_def (r : σ → R) :
    prodRingChooseSpan r = AddSubgroup.closure (Set.range fun n : σ →₀ ℕ =>
      n.prod (fun i k => Ring.choose (r i) k)) := (rfl)

/-- Every finite product of binomial coefficients belongs to the integral product span. -/
@[simp]
theorem prod_ringChoose_mem_prodRingChooseSpan (r : σ → R) (n : σ →₀ ℕ) :
    n.prod (fun i k => Ring.choose (r i) k) ∈ prodRingChooseSpan r :=
  AddSubgroup.subset_closure ⟨n, rfl⟩

/-- An additive subgroup contains the integral product span exactly when it contains each
binomial product. -/
@[simp]
theorem prodRingChooseSpan_le_iff {r : σ → R} {S : AddSubgroup R} :
    prodRingChooseSpan r ≤ S ↔
      ∀ n : σ →₀ ℕ, n.prod (fun i k => Ring.choose (r i) k) ∈ S := by
  rw [prodRingChooseSpan_def, AddSubgroup.closure_le, Set.range_subset_iff]
  rfl

/-- The `ℤ`-linear span of the binomial products is the integral submodule associated to
`prodRingChooseSpan r`. -/
@[simp]
theorem span_int_range_prod_ringChoose (r : σ → R) :
    Submodule.span ℤ (Set.range fun n : σ →₀ ℕ =>
      n.prod (fun i k => Ring.choose (r i) k)) =
      (prodRingChooseSpan r).toIntSubmodule := by
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.span_int_eq_addSubgroupClosure,
    AddSubgroup.toIntSubmodule_toAddSubgroup, prodRingChooseSpan_def]

/-- The integral product span contains one, the product indexed by the zero multi-index. -/
@[simp]
theorem one_mem_prodRingChooseSpan (r : σ → R) : 1 ∈ prodRingChooseSpan r := by
  simpa using prod_ringChoose_mem_prodRingChooseSpan r 0

/-- A bounded ordered span on a finite subfamily is contained in the full product span.
The exponents outside the subfamily are extended by zero. -/
theorem ringChooseFilteredSpan_le_prodRingChooseSpan (r : σ → R) {k : ℕ}
    (e : Fin k ↪ σ) (n : ℕ) :
    ringChooseFilteredSpan (r ∘ e) n ≤ (prodRingChooseSpan r).toIntSubmodule := by
  classical
  rw [ringChooseFilteredSpan_le_iff]
  intro a _
  have h := prod_ringChoose_mem_prodRingChooseSpan r
    ((Finsupp.equivFunOnFinite.symm a).embDomain e)
  rw [Finsupp.prod_embDomain,
    Finsupp.prod_fintype _ _ (fun _ => Ring.choose_zero_right _)] at h
  rw [← Submodule.mem_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]
  simpa only [Finsupp.coe_equivFunOnFinite_symm, List.prod_ofFn, Function.comp_apply] using h

/-- The integral product span is closed under multiplication. -/
theorem mul_mem_prodRingChooseSpan (r : σ → R) {x y : R}
    (hx : x ∈ prodRingChooseSpan r) (hy : y ∈ prodRingChooseSpan r) :
    x * y ∈ prodRingChooseSpan r := by
  classical
  rw [prodRingChooseSpan_def] at hx hy ⊢
  refine AddSubgroup.mul_mem_closure_of_mul_mem ?_ hx hy
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  dsimp only
  let s := m.support ∪ n.support
  let e : Fin s.card ≃ s := s.equivFin.symm
  have hprod (v : σ →₀ ℕ) (hv : v.support ⊆ s) :
      v.prod (fun i k => Ring.choose (r i) k) =
        (List.ofFn fun i => Ring.choose (r (e i)) (v (e i))).prod := by
    rw [List.prod_ofFn,
      e.prod_comp (fun i : s => Ring.choose (r i) (v i)),
      v.prod_of_support_subset hv _ (by simp),
      Finset.prod_coe_sort s (fun i => Ring.choose (r i) (v i))]
  rw [hprod m Finset.subset_union_left, hprod n Finset.subset_union_right]
  have hm := prod_ofFn_ringChoose_mem_ringChooseFilteredSpan
    (fun i => r (e i)) (fun i => m (e i)) le_rfl
  have hn := prod_ofFn_ringChoose_mem_ringChooseFilteredSpan
    (fun i => r (e i)) (fun i => n (e i)) le_rfl
  exact ringChooseFilteredSpan_le_prodRingChooseSpan r
    (e.toEmbedding.trans (Function.Embedding.subtype _)) _
    (mul_le_ringChooseFilteredSpan (fun i => r (e i))
      (fun _ _ => Commute.all _ _) _ _ (Submodule.mul_mem_mul hm hn))

/-- Membership in the integral product span is equivalent to a unique finite integral
expansion, provided the binomial products are linearly independent over the integers. -/
theorem mem_prodRingChooseSpan_iff_existsUnique {r : σ → R}
    (h : LinearIndependent ℤ (fun n : σ →₀ ℕ =>
      n.prod (fun i k => Ring.choose (r i) k))) (x : R) :
    x ∈ prodRingChooseSpan r ↔
      ∃! a : (σ →₀ ℕ) →₀ ℤ,
        a.sum (fun n z => z • n.prod (fun i k => Ring.choose (r i) k)) = x := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (prodRingChooseSpan r),
    Submodule.mem_toAddSubgroup, ← span_int_range_prod_ringChoose r]
  exact LinearIndependent.mem_span_range_iff_existsUnique h x

end ProductSpan

end TauCeti
