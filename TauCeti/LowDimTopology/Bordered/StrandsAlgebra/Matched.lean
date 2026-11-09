/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.MoveHorizontal

/-!
# The algebra of a matching

Let `Z` be a pointed matched circle with `4k` points, matched in pairs. Lipshitz, Ozsváth and
Thurston define the algebra `A(Z)` as a subalgebra of the strands algebra `A(4k)`: its elements
are the sums of strand diagrams over all ways of placing horizontal strands on given matched pairs,
each horizontal strand sitting at either point of its pair, and restricted to diagrams in which no
two starting points and no two ending points are matched. This file constructs this subalgebra for
an arbitrary matching `m : α → β` of a finite linear order `α`, two points being matched when they
have the same image, and over any commutative semiring.

The subalgebra `TauCeti.StrandsAlgebra.matchedSubalgebra R m` consists of the elements whose
coefficients vanish off the diagrams with pairwise unmatched starting points and pairwise unmatched
ending points, and are unchanged by moving a horizontal strand to a point matched with it
(`TauCeti.StrandDiagram.moveHorizontal`). It is closed under products and under the differential:
in the coefficient of a diagram `χ` with a horizontal strand at `p`, every term comes from a
factorization of `χ`, or a resolution giving `χ`, in which that strand is horizontal throughout.
Moving it to a point `q` matched with `p` in each piece matches these terms bijectively with those
of the moved diagram, and preserves the conditions for a nonzero product and for a term of the
differential.

The subalgebra is not unital in the strands algebra: its own unit
`TauCeti.StrandsAlgebra.matchedOne` sums the idempotents `I(s)` of the sets `s` with pairwise
unmatched points. It splits into the orthogonal idempotents `I(t)`
(`TauCeti.StrandsAlgebra.matchedIdem`) indexed by the sets `t` of occupied matched classes, each
the sum of the `I(s)` over the sets `s` containing one point of each class in `t`. With this unit
the subalgebra is an `R`-algebra, and over a ring of characteristic two the restricted differential
makes it an ungraded differential algebra, over which type `D` structures are defined.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R m`: the algebra `A(m)` of the matching `m`.
* `TauCeti.StrandsAlgebra.matchedIdem R m t`, `TauCeti.StrandsAlgebra.matchedOne R m`: its
  idempotents `I(t)` and its unit.
* `TauCeti.StrandsAlgebra.matchedDifferential R m`: the differential restricted to `A(m)`.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: membership in `A(m)`.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: `A(m)` is closed under the
  differential.
* `TauCeti.StrandsAlgebra.matchedOne_mul`, `TauCeti.StrandsAlgebra.mul_matchedOne`: the unit.
* `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`, `TauCeti.StrandsAlgebra.sum_matchedIdem`:
  the `I(t)` are orthogonal idempotents summing to the unit.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_matchedDifferential`: over a ring of characteristic
  two, `A(m)` is an ungraded differential algebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (pointed matched circles, the idempotents `I(s)` and the algebra `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

open scoped Classical in
/-- The coefficients of a product in the basis of strand diagrams. -/
private theorem repr_mul_apply [Fintype (StrandDiagram α)] (x y : StrandsAlgebra R α)
    (χ : StrandDiagram α) :
    (basis R α).repr (x * y) χ = ∑ π ∈ {π : StrandDiagram α × StrandDiagram α |
      π.1.Composable π.2 ∧ π.1.trans π.2 = χ},
        (basis R α).repr x π.1 * (basis R α).repr y π.2 := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp [add_mul, hx, hx', Finset.sum_add_distrib]
  | smul_of r φ =>
    induction y using induction_on with
    | zero => simp
    | add y y' hy hy' =>
      rw [mul_add, map_add, Finsupp.add_apply, hy, hy', ← Finset.sum_add_distrib]
      simp [mul_add]
    | smul_of s ψ =>
      rw [smul_mul_smul_comm, of_mul_of, Finset.sum_filter, Finset.sum_eq_single (φ, ψ)]
      · by_cases h : φ.Composable ψ
        · by_cases h' : φ.trans ψ = χ <;> simp [h, h']
        · simp [h]
      · rintro ⟨φ', ψ'⟩ - hne
        simp only [map_smul, basis_repr_of, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases h₁ : φ = φ' <;> by_cases h₂ : ψ = ψ' <;> simp_all
      · simp

/-- The defining property of the elements of the matched subalgebra: their coefficients vanish
off the diagrams whose starting and ending points are pairwise unmatched, and are unchanged by
moving a horizontal strand to a point matched with it. -/
private def IsMatched (m : α → β) (x : StrandsAlgebra R α) : Prop :=
  (∀ φ, (basis R α).repr x φ ≠ 0 → Set.InjOn m φ.source ∧ Set.InjOn m φ.target) ∧
    ∀ φ : StrandDiagram α, Set.InjOn m φ.source → Set.InjOn m φ.target → ∀ ⦃p q : α⦄,
      p ∈ φ p → p ≠ q → m p = m q →
        (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ

variable {m : α → β}

omit [LinearOrder α] [Fintype α] in
/-- A point matched with a point of a set on which the matching is injective lies outside it. -/
private theorem notMem_of_injOn {s : Finset α} (hs : Set.InjOn m s) {p q : α} (hp : p ∈ s)
    (hpq : p ≠ q) (hm : m p = m q) : q ∉ s :=
  fun hq ↦ hs.ne hp hq hpq hm

/-- In a factorization of `χ` with nonzero coefficients, a horizontal strand of `χ` is
horizontal in both factors, and a point matched with it is free in both. -/
private theorem isMatched_factor_horizontal {x y : StrandsAlgebra R α} (hx : IsMatched m x)
    (hy : IsMatched m y) {φ ψ : StrandDiagram α} (hφ : (basis R α).repr x φ ≠ 0)
    (hψ : (basis R α).repr y ψ ≠ 0) {p q : α} (hp : p ∈ φ.trans ψ p) (hpq : p ≠ q)
    (hm : m p = m q) :
    (p ∈ φ p ∧ q ∉ φ.source ∧ q ∉ φ.target) ∧ (p ∈ ψ p ∧ q ∉ ψ.source ∧ q ∉ ψ.target) := by
  obtain ⟨hφS, hφT⟩ := hx.1 φ hφ
  obtain ⟨hψS, hψT⟩ := hy.1 ψ hψ
  obtain ⟨hpφ, hpψ⟩ := mem_trans_self_iff.1 hp
  exact ⟨⟨hpφ, notMem_of_injOn hφS (mem_source.2 ⟨p, hpφ⟩) hpq hm,
      notMem_of_injOn hφT (mem_target.2 ⟨p, hpφ⟩) hpq hm⟩,
    ⟨hpψ, notMem_of_injOn hψS (mem_source.2 ⟨p, hpψ⟩) hpq hm,
      notMem_of_injOn hψT (mem_target.2 ⟨p, hpψ⟩) hpq hm⟩⟩

/-- Moving a horizontal strand of `χ` to a matched point, in both factors of a factorization of
`χ` with nonzero coefficients, gives a factorization of the moved diagram with the same
coefficients. -/
private theorem isMatched_factor {x y : StrandsAlgebra R α} (hx : IsMatched m x)
    (hy : IsMatched m y) {φ ψ χ : StrandDiagram α} (h : φ.Composable ψ) (hχ : φ.trans ψ = χ)
    (hφ : (basis R α).repr x φ ≠ 0) (hψ : (basis R α).repr y ψ ≠ 0) {p q : α} (hp : p ∈ χ p)
    (hpq : p ≠ q) (hm : m p = m q) :
    (φ.moveHorizontal p q).Composable (ψ.moveHorizontal p q) ∧
      (φ.moveHorizontal p q).trans (ψ.moveHorizontal p q) = χ.moveHorizontal p q ∧
      (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ ∧
      (basis R α).repr y (ψ.moveHorizontal p q) = (basis R α).repr y ψ := by
  subst hχ
  obtain ⟨⟨hpφ, hsφ, htφ⟩, ⟨hpψ, hsψ, htψ⟩⟩ :=
    isMatched_factor_horizontal hx hy hφ hψ hp hpq hm
  exact ⟨h.moveHorizontal hpφ hsφ htφ hpψ hsψ htψ, moveHorizontal_trans hpφ hsφ htφ hpψ hsψ htψ,
    hx.2 φ (hx.1 φ hφ).1 (hx.1 φ hφ).2 hpφ hpq hm, hy.2 ψ (hy.1 ψ hψ).1 (hy.1 ψ hψ).2 hpψ hpq hm⟩

/-- **The matched subalgebra is closed under products.** -/
private theorem isMatched_mul {x y : StrandsAlgebra R α} (hx : IsMatched m x)
    (hy : IsMatched m y) : IsMatched m (x * y) := by
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  refine ⟨fun χ hχ ↦ ?_, fun χ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_mul_apply] at hχ
    obtain ⟨π, hπ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    obtain ⟨h, rfl⟩ := hπ
    rw [source_trans_of_target_eq h.target_eq, target_trans_of_target_eq h.target_eq]
    exact ⟨(hx.1 _ (left_ne_zero_of_mul hne)).1, (hy.1 _ (right_ne_zero_of_mul hne)).2⟩
  have hsχ := notMem_of_injOn hS (mem_source.2 ⟨p, hp⟩) hpq hm
  have htχ := notMem_of_injOn hT (mem_target.2 ⟨p, hp⟩) hpq hm
  have hq : q ∈ χ.moveHorizontal p q q := mem_moveHorizontal_self hp hsχ htχ
  rw [repr_mul_apply, repr_mul_apply]
  -- Moving the horizontal strand back from `q` to `p` in both factors matches the factorizations
  -- of the two diagrams with nonzero coefficients.
  refine Finset.sum_bij_ne_zero (fun π _ _ ↦ (π.1.moveHorizontal q p, π.2.moveHorizontal q p))
    ?_ ?_ ?_ ?_
  · intro π hπ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    obtain ⟨h₁, h₂, -⟩ := isMatched_factor hx hy hπ.1 hπ.2 (left_ne_zero_of_mul hne)
      (right_ne_zero_of_mul hne) hq hpq.symm hm.symm
    exact ⟨h₁, by rw [h₂, moveHorizontal_moveHorizontal hp hsχ htχ]⟩
  · intro π hπ hne π' hπ' hne' he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ hπ'
    obtain ⟨⟨hp₁, hs₁, ht₁⟩, ⟨hp₂, hs₂, ht₂⟩⟩ := isMatched_factor_horizontal hx hy
      (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne) (hπ.2 ▸ hq) hpq.symm hm.symm
    obtain ⟨⟨hp₁', hs₁', ht₁'⟩, ⟨hp₂', hs₂', ht₂'⟩⟩ := isMatched_factor_horizontal hx hy
      (left_ne_zero_of_mul hne') (right_ne_zero_of_mul hne') (hπ'.2 ▸ hq) hpq.symm hm.symm
    obtain ⟨he₁, he₂⟩ := Prod.mk.inj he
    refine Prod.ext ?_ ?_
    · rw [← moveHorizontal_moveHorizontal hp₁ hs₁ ht₁, he₁,
        moveHorizontal_moveHorizontal hp₁' hs₁' ht₁']
    · rw [← moveHorizontal_moveHorizontal hp₂ hs₂ ht₂, he₂,
        moveHorizontal_moveHorizontal hp₂' hs₂' ht₂']
  · intro ρ hρ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨⟨hp₁, hs₁, ht₁⟩, ⟨hp₂, hs₂, ht₂⟩⟩ := isMatched_factor_horizontal hx hy
      (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne) (hρ.2 ▸ hp) hpq hm
    obtain ⟨h₁, h₂, h₃, h₄⟩ := isMatched_factor hx hy hρ.1 hρ.2 (left_ne_zero_of_mul hne)
      (right_ne_zero_of_mul hne) hp hpq hm
    refine ⟨(ρ.1.moveHorizontal p q, ρ.2.moveHorizontal p q), ?_, by rwa [h₃, h₄], ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h₁, h₂⟩
    · rw [moveHorizontal_moveHorizontal hp₁ hs₁ ht₁, moveHorizontal_moveHorizontal hp₂ hs₂ ht₂]
  · intro π hπ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    obtain ⟨-, -, h₃, h₄⟩ := isMatched_factor hx hy hπ.1 hπ.2 (left_ne_zero_of_mul hne)
      (right_ne_zero_of_mul hne) hq hpq.symm hm.symm
    rw [h₃, h₄]

open scoped Classical in
/-- The coefficients of the differential in the basis of strand diagrams. -/
private theorem repr_differential_apply [Fintype (StrandDiagram α)] (x : StrandsAlgebra R α)
    (χ : StrandDiagram α) :
    (basis R α).repr (differential R α x) χ = ∑ π ∈ {π : StrandDiagram α × (α × α) |
      π.2 ∈ π.1.resolvableInversions ∧ π.1.resolve π.2 = χ}, (basis R α).repr x π.1 := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx', Finset.sum_add_distrib]
  | smul_of r φ =>
    rw [map_smul, differential_of, Finset.sum_filter, Fintype.sum_prod_type,
      Finset.sum_eq_single φ]
    · simp only [map_smul, map_sum, basis_repr_of, Finsupp.smul_apply, Finset.sum_apply',
        Finsupp.single_apply, smul_eq_mul, ite_true, ite_and]
      rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.mul_sum, Finset.sum_filter]
    · rintro φ' - hne
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      simp [Ne.symm hne]
    · simp

/-- Moving a horizontal strand of a resolution `χ` of `φ`, where `φ` has a nonzero coefficient, to
a matched point: the moved diagram is the resolution of the moved `φ` at the same crossing. -/
private theorem isMatched_resolve {x : StrandsAlgebra R α} (hx : IsMatched m x)
    {φ χ : StrandDiagram α} {r : α × α} (hr : r ∈ φ.resolvableInversions) (hχ : φ.resolve r = χ)
    (hφ : (basis R α).repr x φ ≠ 0) {p q : α} (hp : p ∈ χ p) (hpq : p ≠ q) (hm : m p = m q) :
    (p ∈ φ p ∧ q ∉ φ.source ∧ q ∉ φ.target) ∧ r ∈ (φ.moveHorizontal p q).resolvableInversions ∧
      (φ.moveHorizontal p q).resolve r = χ.moveHorizontal p q ∧
      (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ := by
  subst hχ
  obtain ⟨hS, hT⟩ := hx.1 φ hφ
  have hr' := (mem_resolvableInversions.1 hr).1
  obtain ⟨hpφ, h₁, h₂⟩ := mem_resolve_self hr' hp
  have hs := notMem_of_injOn hS (mem_source.2 ⟨p, hpφ⟩) hpq hm
  have ht := notMem_of_injOn hT (mem_target.2 ⟨p, hpφ⟩) hpq hm
  exact ⟨⟨hpφ, hs, ht⟩, mem_resolvableInversions_moveHorizontal hr hp hs ht,
    (moveHorizontal_resolve hpφ hs ht hr' h₁ h₂).symm, hx.2 φ hS hT hpφ hpq hm⟩

/-- **The matched subalgebra is closed under the differential.** -/
private theorem isMatched_differential {x : StrandsAlgebra R α} (hx : IsMatched m x) :
    IsMatched m (differential R α x) := by
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  refine ⟨fun χ hχ ↦ ?_, fun χ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_differential_apply] at hχ
    obtain ⟨π, hπ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    obtain ⟨-, rfl⟩ := hπ
    rw [source_resolve, target_resolve]
    exact hx.1 _ hne
  have hsχ := notMem_of_injOn hS (mem_source.2 ⟨p, hp⟩) hpq hm
  have htχ := notMem_of_injOn hT (mem_target.2 ⟨p, hp⟩) hpq hm
  have hq : q ∈ χ.moveHorizontal p q q := mem_moveHorizontal_self hp hsχ htχ
  rw [repr_differential_apply, repr_differential_apply]
  -- Moving the horizontal strand back from `q` to `p` matches the resolutions giving the two
  -- diagrams from diagrams with nonzero coefficients.
  refine Finset.sum_bij_ne_zero (fun π _ _ ↦ (π.1.moveHorizontal q p, π.2)) ?_ ?_ ?_ ?_
  · intro π hπ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    obtain ⟨-, h₁, h₂, -⟩ := isMatched_resolve hx hπ.1 hπ.2 hne hq hpq.symm hm.symm
    exact ⟨h₁, by rw [h₂, moveHorizontal_moveHorizontal hp hsχ htχ]⟩
  · intro π hπ hne π' hπ' hne' he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ hπ'
    obtain ⟨⟨hp₁, hs₁, ht₁⟩, -⟩ := isMatched_resolve hx hπ.1 hπ.2 hne hq hpq.symm hm.symm
    obtain ⟨⟨hp₁', hs₁', ht₁'⟩, -⟩ := isMatched_resolve hx hπ'.1 hπ'.2 hne' hq hpq.symm hm.symm
    obtain ⟨he₁, he₂⟩ := Prod.mk.inj he
    refine Prod.ext ?_ he₂
    rw [← moveHorizontal_moveHorizontal hp₁ hs₁ ht₁, he₁,
      moveHorizontal_moveHorizontal hp₁' hs₁' ht₁']
  · intro ρ hρ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨⟨hp₁, hs₁, ht₁⟩, h₁, h₂, h₃⟩ := isMatched_resolve hx hρ.1 hρ.2 hne hp hpq hm
    refine ⟨(ρ.1.moveHorizontal p q, ρ.2), ?_, by rwa [h₃], ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h₁, h₂⟩
    · rw [moveHorizontal_moveHorizontal hp₁ hs₁ ht₁]
  · intro π hπ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    exact (isMatched_resolve hx hπ.1 hπ.2 hne hq hpq.symm hm.symm).2.2.2.symm


omit [Fintype α] in
/-- Moving a point of a set on which the matching is injective to a point matched with it and
outside the set keeps the matching injective. -/
private theorem injOn_insert_erase {s : Finset α} (hs : Set.InjOn m s) {p q : α} (hp : p ∈ s)
    (hq : q ∉ s) (hm : m p = m q) : Set.InjOn m ↑(insert q (s.erase p)) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_sdiff,
    Finset.mem_coe, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | ⟨ha, hap⟩ <;> rcases hb with rfl | ⟨hb, hbp⟩
  · rfl
  · exact absurd (hs hb hp (hab.symm.trans hm.symm)) hbp
  · exact absurd (hs ha hp (hab.trans hm.symm)) hap
  · exact hs ha hb hab

open scoped Classical in
/-- The coefficients of a sum of idempotents `I(s)`. -/
private theorem repr_sum_idem_apply (F : Finset (Finset α)) (ψ : StrandDiagram α) :
    (basis R α).repr (∑ s ∈ F, idem s) ψ = if ψ = idOn ψ.source ∧ ψ.source ∈ F then 1 else 0 := by
  simp only [map_sum, idem_def, basis_repr_of, Finset.sum_apply', Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem _ h.2 fun s _ hs ↦ ?_]
    · simp [← h.1]
    · rw [ite_eq_right]
      rintro rfl
      exact hs (source_idOn s).symm
  · refine Finset.sum_eq_zero fun s hs ↦ ite_eq_right ?_
    rintro rfl
    exact h ⟨by rw [source_idOn], by rwa [source_idOn]⟩

/-- A sum of idempotents `I(s)` over a family of sets on which the matching is injective, closed
under moving a point to a point matched with it, lies in the matched subalgebra. -/
private theorem isMatched_sum_idem (F : Finset (Finset α)) (hF : ∀ s ∈ F, Set.InjOn m s)
    (hmove : ∀ s ∈ F, ∀ ⦃p q⦄, p ∈ s → q ∉ s → m p = m q → insert q (s.erase p) ∈ F) :
    IsMatched m (∑ s ∈ F, idem s : StrandsAlgebra R α) := by
  classical
  refine ⟨fun ψ hψ ↦ ?_, fun φ hS hT p q hp hpq hm ↦ ?_⟩
  · rw [repr_sum_idem_apply] at hψ
    obtain ⟨h₁, h₂⟩ := (ite_ne_right_iff.1 hψ).1
    rw [h₁, source_idOn, target_idOn]
    exact ⟨hF _ h₂, hF _ h₂⟩
  have hs := notMem_of_injOn hS (mem_source.2 ⟨p, hp⟩) hpq hm
  have ht := notMem_of_injOn hT (mem_target.2 ⟨p, hp⟩) hpq hm
  have hpS : p ∈ φ.source := mem_source.2 ⟨p, hp⟩
  rw [repr_sum_idem_apply, repr_sum_idem_apply, source_moveHorizontal hp hs ht]
  congr 1
  refine propext ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have hq' : q ∈ insert q (φ.source.erase p) := mem_insert_self q _
    have hp' : p ∉ insert q (φ.source.erase p) := by simp [hpq]
    have he : insert p ((insert q (φ.source.erase p)).erase q) = φ.source := by
      rw [erase_insert (by simp [hs]), insert_erase hpS]
    refine ⟨?_, he ▸ hmove _ h₂ hq' hp' hm.symm⟩
    rw [← moveHorizontal_moveHorizontal hp hs ht, h₁, moveHorizontal_idOn hq' hp', he, source_idOn]
  · refine ⟨?_, hmove _ h₂ hpS hs hm⟩
    conv_lhs => rw [h₁]
    rw [moveHorizontal_idOn hpS hs]


variable (R m) in
/-- The **matched subalgebra** `A(m)` of the strands algebra for a matching `m : α → β`, two points
being matched when they have the same image. It consists of the elements whose coefficients vanish
off the diagrams with pairwise unmatched starting points and pairwise unmatched ending points, and
are unchanged by moving a horizontal strand to a point matched with it. Equivalently it is spanned
by the sums of all diagrams with given moving strands and given matched pairs carrying a
horizontal strand, the horizontal strand of each pair placed at either of its points. For the
matching of the `4k` points of a pointed matched circle `Z` this is the algebra `A(Z)` of
Lipshitz, Ozsváth and Thurston. -/
def matchedSubalgebra : NonUnitalSubalgebra R (StrandsAlgebra R α) where
  carrier := {x | IsMatched m x}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {x y} hx hy := by
    refine ⟨fun φ hφ ↦ ?_, fun φ hS hT p q hp hpq hm ↦ ?_⟩
    · rw [map_add, Finsupp.add_apply] at hφ
      by_cases h : (basis R α).repr x φ = 0
      · exact hy.1 φ (by simpa [h] using hφ)
      · exact hx.1 φ h
    · simp [hx.2 φ hS hT hp hpq hm, hy.2 φ hS hT hp hpq hm]
  smul_mem' r x hx := by
    refine ⟨fun φ hφ ↦ hx.1 φ fun h ↦ hφ (by simp [h]), fun φ hS hT p q hp hpq hm ↦ ?_⟩
    simp [hx.2 φ hS hT hp hpq hm]
  mul_mem' := isMatched_mul

/-- Membership in the matched subalgebra. -/
theorem mem_matchedSubalgebra {x : StrandsAlgebra R α} :
    x ∈ matchedSubalgebra R m ↔
      (∀ φ, (basis R α).repr x φ ≠ 0 → Set.InjOn m φ.source ∧ Set.InjOn m φ.target) ∧
        ∀ φ : StrandDiagram α, Set.InjOn m φ.source → Set.InjOn m φ.target → ∀ ⦃p q : α⦄,
          p ∈ φ p → p ≠ q → m p = m q →
            (basis R α).repr x (φ.moveHorizontal p q) = (basis R α).repr x φ :=
  Iff.rfl

/-- **The matched subalgebra is closed under the differential.** -/
theorem differential_mem_matchedSubalgebra {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R m) : differential R α x ∈ matchedSubalgebra R m :=
  isMatched_differential hx

open scoped Classical in
variable (R m) in
/-- The idempotent `I(t)` of the matched subalgebra for a set `t` of matched classes: the sum of
the idempotents `I(s)` over the sets `s` containing exactly one point of each class in `t`. -/
def matchedIdem (t : Finset β) : StrandsAlgebra R α :=
  ∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α) ∧ s.image m = t, idem s

open scoped Classical in
variable (R m) in
/-- The unit of the matched subalgebra: the sum of the idempotents `I(s)` over the sets `s` on
which the matching is injective. -/
def matchedOne : StrandsAlgebra R α :=
  ∑ s ∈ univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α), idem s

theorem matchedIdem_mem (t : Finset β) : matchedIdem R m t ∈ matchedSubalgebra R m := by
  classical
  rw [matchedIdem]
  refine isMatched_sum_idem _ (fun s hs ↦ (Finset.mem_filter.1 hs).2.1) fun s hs p q hp hq hm ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  refine ⟨injOn_insert_erase hs.1 hp hq hm, ?_⟩
  rw [Finset.image_insert, ← hm, ← Finset.image_insert, Finset.insert_erase hp, hs.2]

theorem matchedOne_mem : matchedOne R m ∈ matchedSubalgebra R m := by
  classical
  rw [matchedOne]
  refine isMatched_sum_idem _ (fun s hs ↦ (Finset.mem_filter.1 hs).2) fun s hs p q hp hq hm ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact injOn_insert_erase hs hp hq hm

/-- The unit of the matched subalgebra fixes a diagram whose starting points are pairwise
unmatched. -/
theorem matchedOne_mul_of {φ : StrandDiagram α} (h : Set.InjOn m φ.source) :
    matchedOne R m * of φ = of φ := by
  classical
  simp [matchedOne, Finset.sum_mul, idem_mul_of, h]

/-- The unit of the matched subalgebra fixes a diagram whose ending points are pairwise
unmatched. -/
theorem of_mul_matchedOne {φ : StrandDiagram α} (h : Set.InjOn m φ.target) :
    of φ * matchedOne R m = of φ := by
  classical
  simp [matchedOne, Finset.mul_sum, of_mul_idem, h]

theorem matchedOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R m) :
    matchedOne R m * x = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [mul_smul_comm, basis_apply, matchedOne_mul_of (hx.1 φ hφ).1]

theorem mul_matchedOne {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R m) :
    x * matchedOne R m = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [smul_mul_assoc, basis_apply, of_mul_matchedOne (hx.1 φ hφ).2]

/-- The idempotents `I(t)` are orthogonal: `I(t) I(t')` is `I(t)` when `t = t'` and zero
otherwise. -/
@[simp]
theorem matchedIdem_mul_matchedIdem [DecidableEq β] (t t' : Finset β) :
    matchedIdem R m t * matchedIdem R m t' = if t = t' then matchedIdem R m t else 0 := by
  classical
  rw [matchedIdem, matchedIdem, Finset.sum_mul_sum]
  simp only [idem_mul_idem, Finset.sum_ite_eq]
  split_ifs with h
  · subst h
    exact Finset.sum_congr rfl fun s hs ↦ ite_eq_left hs
  · refine Finset.sum_eq_zero fun s hs ↦ ite_eq_right fun hs' ↦ ?_
    simp only [Finset.mem_filter] at hs hs'
    exact absurd (hs.2.2.symm.trans hs'.2.2) h

theorem isIdempotentElem_matchedIdem (t : Finset β) :
    IsIdempotentElem (matchedIdem R m t) := by
  classical
  rw [IsIdempotentElem, matchedIdem_mul_matchedIdem, ite_eq_left rfl]

/-- Multiplying a diagram with pairwise unmatched starting points on the left by `I(t)` keeps it
when its starting points occupy the classes `t`, and gives zero otherwise. -/
theorem matchedIdem_mul_of [DecidableEq β] (t : Finset β) {φ : StrandDiagram α}
    (h : Set.InjOn m φ.source) :
    matchedIdem R m t * of φ = if φ.source.image m = t then of φ else 0 := by
  classical
  simp only [matchedIdem, Finset.sum_mul, idem_mul_of, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, h, true_and]
  -- The two sides decide equality of images with different instances.
  congr
  exact Subsingleton.elim _ _

/-- Multiplying a diagram with pairwise unmatched ending points on the right by `I(t)` keeps it
when its ending points occupy the classes `t`, and gives zero otherwise. -/
theorem of_mul_matchedIdem [DecidableEq β] (t : Finset β) {φ : StrandDiagram α}
    (h : Set.InjOn m φ.target) :
    of φ * matchedIdem R m t = if φ.target.image m = t then of φ else 0 := by
  classical
  simp only [matchedIdem, Finset.mul_sum, of_mul_idem, Finset.sum_ite_eq, Finset.mem_filter,
    Finset.mem_univ, h, true_and]
  -- The two sides decide equality of images with different instances.
  congr
  exact Subsingleton.elim _ _

/-- The idempotents `I(t)` sum to the unit of the matched subalgebra. -/
theorem sum_matchedIdem [Fintype β] : ∑ t : Finset β, matchedIdem R m t = matchedOne R m := by
  classical
  simp only [matchedIdem, matchedOne]
  rw [← Finset.sum_fiberwise (univ.filter fun s : Finset α ↦ Set.InjOn m (s : Set α))
    (fun s ↦ s.image m)]
  simp only [Finset.filter_filter]

/-- The idempotents `I(t)` are cycles. -/
@[simp]
theorem differential_matchedIdem (t : Finset β) : differential R α (matchedIdem R m t) = 0 := by
  simp [matchedIdem]

instance : One (matchedSubalgebra R m) :=
  ⟨⟨matchedOne R m, matchedOne_mem⟩⟩

@[simp]
theorem coe_one : ((1 : matchedSubalgebra R m) : StrandsAlgebra R α) = matchedOne R m :=
  (rfl)

/-- The matched subalgebra is a unital algebra, with unit `TauCeti.StrandsAlgebra.matchedOne`. -/
instance : Semiring (matchedSubalgebra R m) where
  __ := (matchedSubalgebra R m).toNonUnitalSemiring
  one_mul x := Subtype.ext (matchedOne_mul x.2)
  mul_one x := Subtype.ext (mul_matchedOne x.2)

instance {R : Type*} [CommRing R] : Ring (matchedSubalgebra R m) where
  __ := (inferInstance : Semiring (matchedSubalgebra R m))
  __ := (matchedSubalgebra R m).toNonUnitalRing

instance : Algebra R (matchedSubalgebra R m) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

variable (R m) in
/-- The differential of the strands algebra restricted to the matched subalgebra. -/
def matchedDifferential : matchedSubalgebra R m →ₗ[R] matchedSubalgebra R m where
  toFun x := ⟨differential R α x, differential_mem_matchedSubalgebra x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp]
theorem coe_matchedDifferential (x : matchedSubalgebra R m) :
    (matchedDifferential R m x : StrandsAlgebra R α) = differential R α x :=
  (rfl)

/-- Over a ring of characteristic two, such as `𝔽₂`, the matched subalgebra with the restricted
differential is an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_matchedDifferential {R : Type*} [CommRing R] [CharP R 2] :
    IsUngradedDGAlgebra (matchedDifferential R m) where
  map_mul a b := Subtype.ext (by simp [differential_mul])
  map_map a := Subtype.ext (by simp [differential_differential])

end StrandsAlgebra

end TauCeti
