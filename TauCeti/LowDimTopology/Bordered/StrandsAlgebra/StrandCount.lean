/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched

/-!
# The parts of the strands algebra with a given number of strands

Lipshitz, Ozsváth and Thurston define the strands algebra `A(n, k)` on `k` strands, spanned by the
strand diagrams `φ : S → T` with `#S = k`; the strands algebra `TauCeti.StrandsAlgebra R α` is
their direct sum over `k`. This file defines the part `A(n, k)`
(`TauCeti.StrandsAlgebra.strandCountPart R k`) as a submodule, the elements supported on the
diagrams with `k` strands, in the same way as the graded parts
`TauCeti.StrandsAlgebra.gradedPart`. Concatenation keeps the number of strands, so the part with
`k` strands is a two-sided ideal and the product of elements with different numbers of strands is
zero; resolving a crossing keeps the number of strands too, so the differential preserves each
part. A diagram with at most one strand has no crossing, so the differential vanishes on the
parts with at most one strand.

For a matching `M : α → β`, the elements of the matched subalgebra with `k` strands form the
summand of `A(Z)` that Lipshitz, Ozsváth and Thurston write `A(Z, i)`, with `i = k - g` for a
pointed matched circle `Z` of genus `g`. The summand with one strand has an explicit basis
(`TauCeti.StrandsAlgebra.oneStrandBasis`): the idempotent `I({b})` of each matched pair `b`, and
the single strand of each chord `i < j` of `α`, which has no horizontal strand to complete. For
the genus-one pointed matched circle this is the eight-dimensional torus algebra, with the
idempotents `ι₀, ι₁` and the six chords `ρ₁, ρ₂, ρ₃, ρ₁₂, ρ₂₃, ρ₁₂₃`
(`TauCeti.StrandsAlgebra.finrank_genusOne`, in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Torus`).

## Main definitions

* `TauCeti.StrandsAlgebra.strandCountPart R k`: the part `A(n, k)` with `k` strands.
* `TauCeti.StrandsAlgebra.oneStrandFamily R M`: the idempotents `I({b})` of the matched pairs and
  the chords, and `TauCeti.StrandsAlgebra.oneStrandBasis R M`, the basis they form of the
  one-strand part of the matched subalgebra.

## Main results

* `TauCeti.StrandsAlgebra.mul_mem_strandCountPart_left`,
  `TauCeti.StrandsAlgebra.mul_mem_strandCountPart_right`: each part is a two-sided ideal.
* `TauCeti.StrandsAlgebra.mul_eq_zero_of_mem_strandCountPart`: parts with different numbers of
  strands multiply to zero.
* `TauCeti.StrandsAlgebra.differential_mem_strandCountPart`: the differential preserves each part,
  and `TauCeti.StrandsAlgebra.differential_eq_zero_of_mem_strandCountPart` it vanishes on the parts
  with at most one strand.
* `TauCeti.StrandsAlgebra.iSupIndep_strandCountPart`, `TauCeti.StrandsAlgebra.iSup_strandCountPart`,
  `TauCeti.StrandsAlgebra.isInternal_strandCountPart`: over a ring, the strands algebra is the
  internal direct sum of the parts.
* `TauCeti.StrandsAlgebra.finrank_oneStrand`: the one-strand part of the matched subalgebra has
  dimension the number of matched pairs plus the number of chords.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the strands algebra `A(n, k)`), and §3.2 (the summands `A(Z, i)` and the
  torus algebra).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable (R : Type*) {α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-! ### The parts `A(n, k)` -/

/-- The part `A(n, k)` of the strands algebra with `k` strands: the elements supported on the
strand diagrams with `k` starting points, that is, the image of `Finsupp.supported` under the basis
of strand diagrams. -/
def strandCountPart (k : ℕ) : Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R {φ : StrandDiagram α | #φ.source = k}).map
    ((basis R α).repr.symm : (StrandDiagram α →₀ R) →ₗ[R] StrandsAlgebra R α)

variable {R}

/-- An element has `k` strands exactly when every strand diagram in its support has `k`
strands. -/
theorem mem_strandCountPart {k : ℕ} {x : StrandsAlgebra R α} :
    x ∈ strandCountPart R k ↔ ∀ φ ∈ ((basis R α).repr x).support, #φ.source = k := by
  rw [strandCountPart, Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_supported]
  rfl

/-- An element with `k` strands has coefficient zero on every diagram with a different number of
strands. -/
theorem repr_apply_eq_zero_of_mem_strandCountPart {k : ℕ} {x : StrandsAlgebra R α}
    (hx : x ∈ strandCountPart R k) {φ : StrandDiagram α} (hφ : #φ.source ≠ k) :
    (basis R α).repr x φ = 0 :=
  Finsupp.notMem_support_iff.1 fun h ↦ hφ (mem_strandCountPart.1 hx φ h)

/-- The part with `k` strands is the span of the strand diagrams with `k` strands. -/
theorem strandCountPart_eq_span (k : ℕ) :
    strandCountPart R k = Submodule.span R (of '' {φ : StrandDiagram α | #φ.source = k}) := by
  rw [strandCountPart, Finsupp.supported_eq_span_single, Submodule.map_span, ← Set.image_comp]
  congr 2
  ext φ
  simp [← basis_apply]

theorem of_mem_strandCountPart (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ strandCountPart R #φ.source :=
  mem_strandCountPart.2 fun ψ hψ ↦ by
    rw [← basis_apply, Module.Basis.repr_self] at hψ
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hψ)]

/-- A strand diagram lies in the part with `k` strands exactly when it has `k` strands. -/
@[simp]
theorem of_mem_strandCountPart_iff [Nontrivial R] {φ : StrandDiagram α} {k : ℕ} :
    (of φ : StrandsAlgebra R α) ∈ strandCountPart R k ↔ #φ.source = k := by
  rw [mem_strandCountPart, ← basis_apply, Module.Basis.repr_self,
    Finsupp.support_single _ one_ne_zero]
  simp

theorem idem_mem_strandCountPart (s : Finset α) :
    (idem s : StrandsAlgebra R α) ∈ strandCountPart R #s := by
  simpa [idem_def] using of_mem_strandCountPart (R := R) (idOn s)

/-- **The parts are right ideals**: concatenating a diagram with another keeps its number of
strands. -/
theorem mul_mem_strandCountPart_right {k : ℕ} {x : StrandsAlgebra R α} (y : StrandsAlgebra R α)
    (hx : x ∈ strandCountPart R k) : x * y ∈ strandCountPart R k := by
  rw [strandCountPart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    induction y using induction_on with
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul_of r ψ =>
      rw [mul_smul_comm, of_mul_of]
      refine Submodule.smul_mem _ r ?_
      split_ifs with h
      · have := of_mem_strandCountPart (R := R) (φ.trans ψ)
        rwa [source_trans_of_target_eq h.target_eq, (hφ : #φ.source = k)] at this
      · exact zero_mem _
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- **The parts are left ideals**: concatenating a diagram with another keeps its number of
strands. -/
theorem mul_mem_strandCountPart_left {k : ℕ} (x : StrandsAlgebra R α) {y : StrandsAlgebra R α}
    (hy : y ∈ strandCountPart R k) : x * y ∈ strandCountPart R k := by
  rw [strandCountPart_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ψ, hψ, rfl⟩ := hy
    induction x using induction_on with
    | zero => rw [zero_mul]; exact zero_mem _
    | add x x' hx hx' => rw [add_mul]; exact add_mem hx hx'
    | smul_of r φ =>
      rw [smul_mul_assoc, of_mul_of]
      refine Submodule.smul_mem _ r ?_
      split_ifs with h
      · have := of_mem_strandCountPart (R := R) (φ.trans ψ)
        rwa [source_trans_of_target_eq h.target_eq, ← card_target, h.target_eq,
          (hψ : #ψ.source = k)] at this
      · exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

/-- Every element of the strands algebra is a sum of elements with fixed numbers of strands. -/
theorem iSup_strandCountPart :
    ⨆ k, strandCountPart R k = (⊤ : Submodule R (StrandsAlgebra R α)) := by
  have h : ⋃ k, {φ : StrandDiagram α | #φ.source = k} = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun φ ↦ ⟨#φ.source, rfl⟩
  simp only [strandCountPart, ← Submodule.map_iSup, ← Finsupp.supported_iUnion, h,
    Finsupp.supported_univ, Submodule.map_top, LinearEquiv.range]

/-- The parts with different numbers of strands are independent. -/
theorem iSupIndep_strandCountPart :
    iSupIndep (strandCountPart R : ℕ → Submodule R (StrandsAlgebra R α)) := by
  refine LinearMap.iSupIndep_map _ (basis R α).repr.symm.injective fun k ↦
    (Finsupp.disjoint_supported_supported (s := {φ : StrandDiagram α | #φ.source = k})
      (t := {φ | #φ.source ≠ k}) (Set.disjoint_left.2 fun _ hφ hφ' ↦ hφ' hφ)).mono_right ?_
  exact iSup₂_le fun l hne ↦ Finsupp.supported_mono fun φ (hφ : #φ.source = l) ↦ hφ.trans_ne hne

/-- Over a ring, the strands algebra is the internal direct sum of its parts `A(n, k)`. -/
theorem isInternal_strandCountPart {R : Type*} [CommRing R] :
    DirectSum.IsInternal (strandCountPart R : ℕ → Submodule R (StrandsAlgebra R α)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_strandCountPart
    iSup_strandCountPart

/-- **Parts with different numbers of strands multiply to zero.** -/
theorem mul_eq_zero_of_mem_strandCountPart {k l : ℕ} {x y : StrandsAlgebra R α}
    (hx : x ∈ strandCountPart R k) (hy : y ∈ strandCountPart R l) (hkl : k ≠ l) : x * y = 0 :=
  (Submodule.disjoint_def.1 (iSupIndep_strandCountPart.pairwiseDisjoint hkl)) _
    (mul_mem_strandCountPart_right y hx) (mul_mem_strandCountPart_left x hy)

/-- **The differential preserves the number of strands**, since resolving a crossing does. -/
theorem differential_mem_strandCountPart {k : ℕ} {x : StrandsAlgebra R α}
    (hx : x ∈ strandCountPart R k) : differential R α x ∈ strandCountPart R k := by
  rw [strandCountPart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    rw [differential_of]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    have := of_mem_strandCountPart (R := R) (φ.resolve p)
    rwa [source_resolve, (hφ : #φ.source = k)] at this
  | zero => rw [map_zero]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **The differential vanishes on the parts with at most one strand**, whose diagrams have no
crossing to resolve. -/
theorem differential_eq_zero_of_mem_strandCountPart {k : ℕ} (hk : k ≤ 1) {x : StrandsAlgebra R α}
    (hx : x ∈ strandCountPart R k) : differential R α x = 0 := by
  rw [strandCountPart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    have h := resolvableInversions_subset_inversions φ
    rw [inversions_eq_empty_of_card_source_le_one ((hφ : #φ.source = k).trans_le hk),
      Finset.subset_empty] at h
    rw [differential_of, h, Finset.sum_empty]
  | zero => exact map_zero _
  | add x x' _ _ hx hx' => rw [map_add, hx, hx', add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-! ### The one-strand part of the matched subalgebra -/

section OneStrand

variable {β : Type*} [DecidableEq β] (M : α → β)

variable (R) in
/-- The spanning family of the one-strand part of the matched subalgebra for a matching `M`: the
idempotent `I({b})` of each matched pair `b` in the range of `M`, and the single strand of each
chord `i < j`. -/
def oneStrandFamily : Set.range M ⊕ {p : α × α // p.1 < p.2} → StrandsAlgebra R α :=
  Sum.elim (fun b ↦ matchedIdem R M {b.1}) fun p ↦ of (single p.1.1 p.1.2 p.2.le)

@[simp]
theorem oneStrandFamily_inl (b : Set.range M) :
    oneStrandFamily R M (.inl b) = matchedIdem R M {b.1} :=
  (rfl)

@[simp]
theorem oneStrandFamily_inr (p : {p : α × α // p.1 < p.2}) :
    oneStrandFamily R M (.inr p) = of (single p.1.1 p.1.2 p.2.le) :=
  (rfl)

/-- The coefficient of the identity diagram on `{a}` in a combination of the family is the
coefficient of the idempotent of the pair of `a`. -/
private theorem repr_sum_smul_oneStrandFamily_idOn
    (c : Set.range M ⊕ {p : α × α // p.1 < p.2} → R) (a : α) :
    (basis R α).repr (∑ i, c i • oneStrandFamily R M i) (idOn {a}) = c (.inl ⟨M a, a, rfl⟩) := by
  rw [repr_sum_smul_apply, Fintype.sum_sum_type, Fintype.sum_eq_single ⟨M a, a, rfl⟩ ?_,
    Finset.sum_eq_zero ?_, add_zero]
  · simp [repr_matchedIdem_apply]
  · intro p _
    simp [single_ne_idOn p.2]
  · intro b hb
    have hb' : M a ≠ b.1 := fun h ↦ hb (Subtype.ext h.symm)
    simp [repr_matchedIdem_apply, hb']

/-- The coefficient of the single strand of a chord in a combination of the family is the
coefficient of that chord. -/
private theorem repr_sum_smul_oneStrandFamily_single
    (c : Set.range M ⊕ {p : α × α // p.1 < p.2} → R) {i j : α} (h : i < j) :
    (basis R α).repr (∑ i, c i • oneStrandFamily R M i) (single i j h.le) =
      c (.inr ⟨(i, j), h⟩) := by
  rw [repr_sum_smul_apply, Fintype.sum_sum_type, Finset.sum_eq_zero ?_, zero_add,
    Fintype.sum_eq_single ⟨(i, j), h⟩ ?_]
  · simp
  · intro p hp
    have hp' : ¬(p.1.1 = i ∧ p.1.2 = j) := fun h' ↦ hp (Subtype.ext (Prod.ext h'.1 h'.2))
    simp [hp']
  · intro b _
    simp [repr_matchedIdem_apply, single_ne_idOn h]

/-- The idempotents of the matched pairs and the single strands of the chords are linearly
independent. -/
theorem linearIndependent_oneStrandFamily : LinearIndependent R (oneStrandFamily R M) := by
  refine Fintype.linearIndependent_iffₛ.2 fun f g hfg i ↦ ?_
  rcases i with ⟨_, a, rfl⟩ | ⟨⟨i, j⟩, h⟩
  · have := congrArg (fun x ↦ (basis R α).repr x (idOn {a})) hfg
    simpa only [repr_sum_smul_oneStrandFamily_idOn] using this
  · have h' : i < j := h
    have := congrArg (fun x ↦ (basis R α).repr x (single i j h'.le)) hfg
    rwa [repr_sum_smul_oneStrandFamily_single M f h', repr_sum_smul_oneStrandFamily_single M g h']
      at this

theorem oneStrandFamily_mem_strandCountPart (i : Set.range M ⊕ {p : α × α // p.1 < p.2}) :
    oneStrandFamily R M i ∈ strandCountPart R 1 := by
  rcases i with ⟨b, -⟩ | p
  · rw [oneStrandFamily_inl, matchedIdem_def]
    exact Submodule.sum_mem _ fun S hS ↦ by
      simpa [(mem_filter.1 hS).2.2] using idem_mem_strandCountPart (R := R) S
  · simpa using of_mem_strandCountPart (R := R) (single p.1.1 p.1.2 p.2.le)

theorem oneStrandFamily_mem_matchedSubalgebra (i : Set.range M ⊕ {p : α × α // p.1 < p.2}) :
    oneStrandFamily R M i ∈ matchedSubalgebra R M := by
  rcases i with b | ⟨⟨i, j⟩, h⟩
  · exact matchedIdem_mem_matchedSubalgebra M _
  · rw [oneStrandFamily_inr, mem_matchedSubalgebra]
    refine ⟨fun φ hφ ↦ ?_, fun φ a b _ ↦ ?_⟩
    · rw [basis_repr_of, Finsupp.single_apply, ne_eq, ite_eq_right_iff, not_imp] at hφ
      rw [← hφ.1, source_single, target_single, coe_singleton, coe_singleton]
      exact ⟨Set.injOn_singleton _ _, Set.injOn_singleton _ _⟩
    · -- A single moving strand is fixed by moving horizontal strands, so moving them permutes the
      -- other diagrams.
      rw [basis_repr_of, Finsupp.single_apply, Finsupp.single_apply]
      refine if_congr ⟨fun he ↦ ?_, fun he ↦ ?_⟩ rfl rfl
      · rw [← swapHorizontal_swapHorizontal φ a b, ← he, swapHorizontal_single h]
      · rw [← he, swapHorizontal_single h]

omit [DecidableEq β] in
/-- In the matched subalgebra, the identity diagrams on matched points have the same
coefficient. -/
private theorem repr_idOn_singleton_eq {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M)
    {a a' : α} (h : M a = M a') :
    (basis R α).repr x (idOn {a'}) = (basis R α).repr x (idOn {a}) := by
  rcases eq_or_ne a a' with rfl | hne
  · rfl
  have hs := swapHorizontal_idOn (s := {a}) (mem_singleton_self a) (by simpa using hne.symm)
  rw [erase_singleton, insert_empty] at hs
  rw [← hs, (mem_matchedSubalgebra.1 hx).2 _ a a' h]

/-- **The one-strand part of the matched subalgebra** is spanned by the idempotents `I({b})` of the
matched pairs and the single strands of the chords. -/
theorem span_oneStrandFamily :
    Submodule.span R (Set.range (oneStrandFamily R M)) =
      (matchedSubalgebra R M).toSubmodule ⊓ strandCountPart R 1 := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x ⟨hxM, hx⟩ ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨oneStrandFamily_mem_matchedSubalgebra M i, oneStrandFamily_mem_strandCountPart M i⟩
  -- Write `x` as the combination of the family with its coefficients on the identity diagram of
  -- a chosen point of each pair and on the chords.
  let c : Set.range M ⊕ {p : α × α // p.1 < p.2} → R :=
    Sum.elim (fun b ↦ (basis R α).repr x (idOn {b.2.choose}))
      fun p ↦ (basis R α).repr x (single p.1.1 p.1.2 p.2.le)
  have hsum : ∑ i, c i • oneStrandFamily R M i ∈ strandCountPart R 1 :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (oneStrandFamily_mem_strandCountPart M i)
  suffices hx' : x = ∑ i, c i • oneStrandFamily R M i by
    rw [hx']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (basis R α).repr.injective (Finsupp.ext fun φ ↦ ?_)
  by_cases hφ : #φ.source = 1
  · obtain ⟨i, j, hij, rfl⟩ := exists_eq_single_of_card_source_eq_one hφ
    rcases hij.lt_or_eq with hij | rfl
    · rw [repr_sum_smul_oneStrandFamily_single M c hij]
      rfl
    · rw [single_self, repr_sum_smul_oneStrandFamily_idOn]
      exact repr_idOn_singleton_eq M hxM (⟨i, rfl⟩ : ∃ a, M a = M i).choose_spec
  · rw [repr_apply_eq_zero_of_mem_strandCountPart hx hφ,
      repr_apply_eq_zero_of_mem_strandCountPart hsum hφ]

variable (R) in
/-- The basis of the one-strand part of the matched subalgebra for a matching `M`, given by the
idempotent `I({b})` of each matched pair `b` and the single strand of each chord `i < j`. -/
def oneStrandBasis : Module.Basis (Set.range M ⊕ {p : α × α // p.1 < p.2}) R
    ((matchedSubalgebra R M).toSubmodule ⊓ strandCountPart R 1 :
      Submodule R (StrandsAlgebra R α)) :=
  (Module.Basis.span (linearIndependent_oneStrandFamily M)).map
    (LinearEquiv.ofEq _ _ (span_oneStrandFamily M))

@[simp]
theorem coe_oneStrandBasis (i : Set.range M ⊕ {p : α × α // p.1 < p.2}) :
    (oneStrandBasis R M i : StrandsAlgebra R α) = oneStrandFamily R M i := by
  simp [oneStrandBasis]

/-- **The dimension of the one-strand part of the matched subalgebra** is the number of matched
pairs plus the number of chords. -/
theorem finrank_oneStrand [StrongRankCondition R] :
    Module.finrank R ((matchedSubalgebra R M).toSubmodule ⊓ strandCountPart R 1 :
      Submodule R (StrandsAlgebra R α)) =
      Fintype.card (Set.range M) + Fintype.card {p : α × α // p.1 < p.2} := by
  rw [Module.finrank_eq_card_basis (oneStrandBasis R M), Fintype.card_sum]

end OneStrand

end StrandsAlgebra

end TauCeti
