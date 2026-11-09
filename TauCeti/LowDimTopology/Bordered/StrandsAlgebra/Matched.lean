/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import TauCeti.Data.Finset.Image
public import TauCeti.Data.Set.Function
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.AddHorizontal
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal
import TauCeti.Data.Finset.Basic

/-!
# The matched subalgebra of the strands algebra

A pointed matched circle `Z` has `4k` points on an oriented circle cut open at a basepoint, matched
in pairs. Lipshitz, Ozsváth and Thurston define the algebra `A(Z)` of bordered Heegaard Floer
homology as a subalgebra of the strands algebra `A(4k)`: it is spanned by the sums of strand
diagrams over all ways of placing each horizontal strand at one of the two points of a matched
pair, the diagrams having no two matched starting points and no two matched end points. Its
idempotents are the sums `I(s)` of the idempotents `I(S)` over the sets `S` containing one point
of each matched pair in `s`.

This file describes this subalgebra intrinsically for an arbitrary matching, a map `M : α → β`
whose fibres are the matched sets (`TauCeti.StrandsAlgebra.matchedSubalgebra`): an element belongs
to it when its diagrams have no two matched starting or end points and its coefficients do not
change when a horizontal strand moves to a matched point
(`TauCeti.StrandDiagram.swapHorizontal`). It is closed under the product, and it is closed under
the differential, so that it is a differential subalgebra. Both closure properties come down to the
behaviour of crossings when a horizontal strand moves, developed in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal`: moving a strand identifies the
factorizations of a diagram, and the diagrams resolving to it, with those of the moved diagram.

The file also describes the spanning sums explicitly. A generator `a(ρ, h)`
(`TauCeti.StrandsAlgebra.horizontalCompletion`) is obtained from a diagram `ρ` without horizontal
strands and a set `h` of pairs by summing over all ways of adding one horizontal strand at a point
of each pair in `h`. The product of two generators is again a generator or zero
(`TauCeti.StrandsAlgebra.horizontalCompletion_mul_horizontalCompletion`), so their span
`TauCeti.StrandsAlgebra.matchedAlgebra` is a non-unital subalgebra, and `∑ₛ I(s)` is a two-sided
unit for it. A horizontal strand of the first factor over a pair in `M(σ⁻)` must sit where a strand
of `σ` starts, and one of the second factor over a pair in `M(ρ⁺)` must sit where a strand of `ρ`
ends; over a pair in `h ∩ k` both factors have a horizontal strand at the same freely chosen point.
Common horizontal strands do not affect composability
(`TauCeti.StrandDiagram.composable_addHorizontal_iff`), so the nonzero products are indexed by the
choices over `h ∩ k` and sum to a single generator.

Two diagrams are related by `TauCeti.StrandDiagram.matchedSetoid M` when they differ only in the
positions of their horizontal strands within matched classes. The coefficients of an element of
the matched subalgebra are constant on these classes, so the subalgebra is also spanned by the
matched completion sums `TauCeti.StrandsAlgebra.matchedSum`, the sums over the classes of diagrams
with no two matched starting points and no two matched end points.

The unit `∑ₛ I(s)` is also the sum of the idempotents `I(S)` of the sets `S` with no two matched
points, and it is a unit for the matched subalgebra too. When `R` is nontrivial and `M` identifies
two points it differs from the unit of the strands algebra. With this unit the matched subalgebra
is an `R`-algebra, and over a ring of characteristic two the restricted differential makes it an
ungraded differential algebra, over which type `D` structures are defined.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R M`: the matched subalgebra, a non-unital subalgebra
  of the strands algebra.
* `TauCeti.StrandsAlgebra.matchedIdem R M s`: the idempotent `I(s)`.
* `TauCeti.StrandsAlgebra.IsMatchedGenerator M ρ h`: `ρ` has no horizontal strands, `M` is
  injective on its starting points and on its end points, and `h` avoids their images.
* `TauCeti.StrandsAlgebra.matchedChoices M h`: the choices of one point of each pair in `h`.
* `TauCeti.StrandsAlgebra.horizontalCompletion M ρ h`: the generator `a(ρ, h)`.
* `TauCeti.StrandsAlgebra.matchedAlgebra R M`: the span of the `a(ρ, h)`, a non-unital subalgebra
  of the strands algebra.
* `TauCeti.StrandsAlgebra.matchedOne R M`: the unit `∑ₛ I(s)` of `matchedAlgebra R M` and of
  `matchedSubalgebra R M`.
* `TauCeti.StrandDiagram.matchedSetoid M`: diagrams differing by moving horizontal strands within
  matched classes.
* `TauCeti.StrandsAlgebra.matchedSum R M φ`: the matched completion sum of a diagram.
* `TauCeti.StrandsAlgebra.matchedDifferential R M`: the differential restricted to the matched
  subalgebra.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: the characterization of the matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: the matched subalgebra is closed
  under the differential.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`: the `I(s)` are orthogonal idempotents of the
  matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_matchedIdem`: the `I(s)` are cycles.
* `TauCeti.StrandsAlgebra.horizontalCompletion_mul_horizontalCompletion`: the product of two
  generators.
* `TauCeti.StrandsAlgebra.matchedOne_mul`, `TauCeti.StrandsAlgebra.mul_matchedOne`: `∑ₛ I(s)` is
  a two-sided unit for `matchedAlgebra R M`.
* `TauCeti.StrandsAlgebra.matchedSum_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.span_matchedSum`: the matched completion sums lie in the matched
  subalgebra and span it.
* `TauCeti.StrandsAlgebra.matchedOne_mul_of_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.mul_matchedOne_of_mem_matchedSubalgebra`: `∑ₛ I(s)` is a two-sided unit
  for the matched subalgebra.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_matchedDifferential`: over a ring of characteristic
  two, the matched subalgebra is an ungraded differential algebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (pointed
  matched circles, the idempotents `I(s)`, the elements `a(ρ)` and the algebra `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α β : Type*} [LinearOrder α] [Fintype α] {M : α → β} {φ ψ : StrandDiagram α} {a b : α}

/-- Moving a horizontal strand to a matched point does not change whether the starting points are
pairwise unmatched. -/
theorem injOn_source_swapHorizontal_iff (hab : M a = M b) :
    Set.InjOn M ((φ.swapHorizontal a b).source : Set α) ↔ Set.InjOn M (φ.source : Set α) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this hab.symm h'
    · rw [swapHorizontal_of_not h h']
  rw [source_swapHorizontal h]
  exact Finset.injOn_insert_erase_iff (mem_source.2 ⟨a, h.mem⟩) h.notMem_source hab

/-- Moving a horizontal strand to a matched point does not change whether the end points are
pairwise unmatched. -/
theorem injOn_target_swapHorizontal_iff (hab : M a = M b) :
    Set.InjOn M ((φ.swapHorizontal a b).target : Set α) ↔ Set.InjOn M (φ.target : Set α) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this hab.symm h'
    · rw [swapHorizontal_of_not h h']
  rw [target_swapHorizontal h]
  exact Finset.injOn_insert_erase_iff (mem_target.2 ⟨a, h.mem⟩) h.notMem_target hab

variable (M) in
/-- Two strand diagrams are related for a matching `M : α → β` when one is obtained from the other
by moving horizontal strands to points with the same image under `M`, so that they differ only in
the positions of their horizontal strands within matched classes. -/
def matchedSetoid : Setoid (StrandDiagram α) :=
  Relation.EqvGen.setoid fun φ ψ ↦ ∃ a b, M a = M b ∧ φ.swapHorizontal a b = ψ

/-- Two diagrams are related by `TauCeti.StrandDiagram.matchedSetoid M` exactly when they are
related by the equivalence relation generated by moving a horizontal strand to a point with the
same image under `M`. -/
theorem matchedSetoid_iff : matchedSetoid M φ ψ ↔
    Relation.EqvGen (fun φ ψ ↦ ∃ a b, M a = M b ∧ φ.swapHorizontal a b = ψ) φ ψ :=
  Iff.rfl

/-- Moving a horizontal strand to a point with the same image under `M` gives a diagram related by
`TauCeti.StrandDiagram.matchedSetoid M`. -/
theorem matchedSetoid_swapHorizontal (hab : M a = M b) :
    matchedSetoid M φ (φ.swapHorizontal a b) :=
  matchedSetoid_iff.2 (.rel _ _ ⟨a, b, hab, rfl⟩)

/-- A function on strand diagrams that is unchanged by moving a horizontal strand to a point with
the same image under `M` is constant on the classes of `TauCeti.StrandDiagram.matchedSetoid M`. -/
theorem apply_eq_of_matchedSetoid {γ : Type*} {f : StrandDiagram α → γ}
    (hf : ∀ φ a b, M a = M b → f (φ.swapHorizontal a b) = f φ) (h : matchedSetoid M φ ψ) :
    f φ = f ψ :=
  Setoid.ker_def.1 <| Setoid.le_def.1 (Setoid.eqvGen_le (s := Setoid.ker f)
    fun φ _ ⟨a, b, hab, e⟩ ↦ Setoid.ker_def.2 <| e ▸ (hf φ a b hab).symm) h

/-- Diagrams related by `TauCeti.StrandDiagram.matchedSetoid M` both have, or both fail to have,
pairwise unmatched starting points and pairwise unmatched end points. -/
theorem injOn_source_and_target_iff_of_matchedSetoid (h : matchedSetoid M φ ψ) :
    Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α) ↔
      Set.InjOn M (ψ.source : Set α) ∧ Set.InjOn M (ψ.target : Set α) :=
  (apply_eq_of_matchedSetoid (f := fun φ : StrandDiagram α ↦
    Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α))
      (fun _ _ _ hab ↦ propext (by
        rw [injOn_source_swapHorizontal_iff hab, injOn_target_swapHorizontal_iff hab])) h).to_iff

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-! ### The matched subalgebra -/

variable (R) in
/-- The matched subalgebra of the strands algebra of `α` for a matching `M : α → β`, which pairs
the points of `α` with equal images. It consists of the elements `x` such that

* every diagram with a nonzero coefficient in `x` has no two matched starting points and no two
  matched end points, and
* the coefficient of a diagram in `x` does not change when one of its horizontal strands is moved
  to a matched point at which no strand starts or ends.

The second condition says that the coefficients are constant on each family of diagrams obtained
from one another by moving horizontal strands between matched points, so that `x` is a combination
of the sums of these families. For the matching of a pointed matched circle `Z` with `4k` points,
`α = Fin (4 * k)` and `R = ZMod 2`, these sums span the algebra `A(Z)` of Lipshitz, Ozsváth and
Thurston, which is therefore this subalgebra. The definition uses no property of `M` beyond being
a function. -/
def matchedSubalgebra (M : α → β) : NonUnitalSubalgebra R (StrandsAlgebra R α) where
  carrier := {x | (∀ φ, (basis R α).repr x φ ≠ 0 →
      Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)) ∧
    ∀ φ a b, M a = M b → (basis R α).repr x (φ.swapHorizontal a b) = (basis R α).repr x φ}
  add_mem' {x y} hx hy := by
    refine ⟨fun φ h ↦ ?_, fun φ a b hab ↦ ?_⟩
    · rw [map_add, Finsupp.add_apply] at h
      by_cases hxφ : (basis R α).repr x φ = 0
      · exact hy.1 φ (by simpa [hxφ] using h)
      · exact hx.1 φ hxφ
    · simp only [map_add, Finsupp.add_apply, hx.2 φ a b hab, hy.2 φ a b hab]
  zero_mem' := ⟨fun φ h ↦ absurd (by simp) h, fun φ a b _ ↦ by simp⟩
  smul_mem' r x hx := by
    refine ⟨fun φ h ↦ hx.1 φ fun hxφ ↦ h ?_, fun φ a b hab ↦ ?_⟩
    · simp [hxφ]
    · simp only [map_smul, Finsupp.smul_apply, hx.2 φ a b hab]
  mul_mem' {x y} hx hy := by
    have := Fintype.ofFinite (StrandDiagram α)
    refine ⟨fun χ hχ ↦ ?_, fun χ a b hab ↦ ?_⟩
    · -- A diagram in a product starts where a diagram of `x` starts and ends where one of `y`
      -- ends.
      rw [repr_mul_apply] at hχ
      obtain ⟨φ, -, hφ⟩ := exists_ne_zero_of_sum_ne_zero hχ
      obtain ⟨ψ, -, hψ⟩ := exists_ne_zero_of_sum_ne_zero hφ
      rw [ne_eq, ite_eq_right_iff, not_imp] at hψ
      obtain ⟨⟨hc, rfl⟩, hψ⟩ := hψ
      rw [source_trans_of_target_eq hc.target_eq, target_trans_of_target_eq hc.target_eq]
      exact ⟨(hx.1 φ (left_ne_zero_of_mul hψ)).1, (hy.1 ψ (right_ne_zero_of_mul hψ)).2⟩
    -- Reduce to a diagram `χ` with a horizontal strand at `a` that can move to `b`.
    wlog hχ : χ.CanMoveHorizontal a b generalizing a b
    · by_cases hχ' : χ.CanMoveHorizontal b a
      · rw [swapHorizontal_comm]
        exact this b a hab.symm hχ'
      · rw [swapHorizontal_of_not hχ hχ']
    -- Moving the strand in both factors identifies the factorizations of `χ` with those of `χ`
    -- with the strand moved.
    have key {φ ψ : StrandDiagram α} {χ : StrandDiagram α} {a b : α}
        (hχ : χ.CanMoveHorizontal a b) (hab : M a = M b)
        (hM : Set.InjOn M (φ.target : Set α)) (h : φ.Composable ψ ∧ φ.trans ψ = χ) :
        (φ.swapHorizontal a b).Composable (ψ.swapHorizontal a b) ∧
          (φ.swapHorizontal a b).trans (ψ.swapHorizontal a b) = χ.swapHorizontal a b := by
      obtain ⟨hc, rfl⟩ := h
      have ha : a ∈ (φ.target : Set α) := mem_coe.2 (mem_target.2 ⟨a, hχ.mem_left_of_trans⟩)
      obtain ⟨hφ, hψ⟩ := hχ.of_trans hc.target_eq fun hb ↦ hχ.ne (hM ha hb hab)
      exact ⟨hc.swapHorizontal hφ hψ, swapHorizontal_trans_swapHorizontal hφ hψ⟩
    set e := (swapHorizontal_involutive (α := α) a b).toPerm
    rw [repr_mul_apply, repr_mul_apply, ← Equiv.sum_comp e]
    refine sum_congr rfl fun φ _ ↦ ?_
    rw [← Equiv.sum_comp e]
    refine sum_congr rfl fun ψ _ ↦ ?_
    simp only [e, Function.Involutive.coe_toPerm, hx.2 φ a b hab, hy.2 ψ a b hab]
    by_cases hxy : (basis R α).repr x φ * (basis R α).repr y ψ = 0
    · simp [hxy]
    have hxφ : (basis R α).repr x (φ.swapHorizontal a b) ≠ 0 := by
      rw [hx.2 φ a b hab]
      exact left_ne_zero_of_mul hxy
    refine if_congr ⟨fun h ↦ ?_, key hχ hab (hx.1 φ (left_ne_zero_of_mul hxy)).2⟩ rfl rfl
    simpa [swapHorizontal_comm _ b a] using key hχ.swapHorizontal hab.symm (hx.1 _ hxφ).2 h

/-- An element of the strands algebra lies in the matched subalgebra when every diagram with a
nonzero coefficient has no two matched starting points and no two matched end points, and the
coefficients do not change when a horizontal strand moves to a matched point. -/
theorem mem_matchedSubalgebra {M : α → β} {x : StrandsAlgebra R α} :
    x ∈ matchedSubalgebra R M ↔
      (∀ φ, (basis R α).repr x φ ≠ 0 →
        Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)) ∧
      ∀ φ a b, M a = M b →
        (basis R α).repr x (φ.swapHorizontal a b) = (basis R α).repr x φ :=
  Iff.rfl

/-- **The matched subalgebra is closed under the differential.** -/
theorem differential_mem_matchedSubalgebra {M : α → β} {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : differential R α x ∈ matchedSubalgebra R M := by
  have := Fintype.ofFinite (StrandDiagram α)
  rw [mem_matchedSubalgebra] at hx ⊢
  refine ⟨fun χ hχ ↦ ?_, fun χ a b hab ↦ ?_⟩
  · -- Resolving a crossing keeps the starting and end points.
    rw [repr_differential_apply] at hχ
    obtain ⟨φ, -, hφ⟩ := exists_ne_zero_of_sum_ne_zero hχ
    obtain ⟨q, -, hq⟩ := exists_ne_zero_of_sum_ne_zero hφ
    rw [ne_eq, ite_eq_right_iff, not_imp] at hq
    obtain ⟨⟨-, rfl⟩, hq⟩ := hq
    rw [source_resolve, target_resolve]
    exact hx.1 φ hq
  wlog hχ : χ.CanMoveHorizontal a b generalizing a b
  · by_cases hχ' : χ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this b a hab.symm hχ'
    · rw [swapHorizontal_of_not hχ hχ']
  -- Moving the strand identifies the diagrams resolving to `χ` with those resolving to `χ` with
  -- the strand moved.
  have key {φ χ : StrandDiagram α} {q : α × α} {a b : α} (hχ : χ.CanMoveHorizontal a b)
      (h : q ∈ φ.resolvableInversions ∧ φ.resolve q = χ) :
      q ∈ (φ.swapHorizontal a b).resolvableInversions ∧
        (φ.swapHorizontal a b).resolve q = χ.swapHorizontal a b := by
    obtain ⟨hq, rfl⟩ := h
    have hq' := resolvableInversions_subset_inversions φ hq
    exact ⟨(mem_resolvableInversions_swapHorizontal_iff hq' hχ).2 hq, resolve_swapHorizontal hq' hχ⟩
  set e := (swapHorizontal_involutive (α := α) a b).toPerm
  rw [repr_differential_apply, repr_differential_apply, ← Equiv.sum_comp e]
  refine sum_congr rfl fun φ _ ↦ sum_congr rfl fun q _ ↦ ?_
  simp only [e, Function.Involutive.coe_toPerm, hx.2 φ a b hab]
  refine if_congr ⟨fun h ↦ ?_, key hχ⟩ rfl rfl
  simpa [swapHorizontal_comm _ b a] using key hχ.swapHorizontal h

/-! ### The idempotents of the matched subalgebra -/

section Idempotents

variable [DecidableEq β]

variable (R) in
/-- The idempotent `I(s)` of the matched subalgebra for a finite set `s` of values of the
matching `M`: the sum of the idempotents `I(S)` over the sets `S` of points mapped bijectively
onto `s` by `M`, that is, containing exactly one point over each element of `s`. -/
def matchedIdem (M : α → β) (s : Finset β) : StrandsAlgebra R α :=
  ∑ S with S.image M = s ∧ #S = #s, idem S

theorem matchedIdem_def (M : α → β) (s : Finset β) :
    matchedIdem R M s = ∑ S with S.image M = s ∧ #S = #s, idem S :=
  (rfl)

/-- The idempotents `I(s)` are cycles. -/
@[simp]
theorem differential_matchedIdem (M : α → β) (s : Finset β) :
    differential R α (matchedIdem R M s) = 0 := by
  simp [matchedIdem_def]

/-- The coefficient of a diagram in `I(s)` is `1` when it is the identity diagram on a set mapped
bijectively onto `s` by `M`, and `0` otherwise. -/
theorem repr_matchedIdem_apply (M : α → β) (s : Finset β) (φ : StrandDiagram α) :
    (basis R α).repr (matchedIdem R M s) φ =
      if φ = idOn φ.source ∧ φ.source.image M = s ∧ #φ.source = #s then 1 else 0 := by
  have key (S : Finset α) : idOn S = φ ↔ S = φ.source ∧ φ = idOn φ.source := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨rfl, h⟩
      exact h.symm
  simp only [matchedIdem, idem_def, map_sum, ← basis_apply, Module.Basis.repr_self,
    Finset.sum_apply', Finsupp.single_apply, key, ite_and, sum_ite_eq', mem_filter, mem_univ,
    true_and]
  split_ifs <;> tauto

/-- **The idempotents `I(s)` lie in the matched subalgebra.** -/
theorem matchedIdem_mem_matchedSubalgebra (M : α → β) (s : Finset β) :
    matchedIdem R M s ∈ matchedSubalgebra R M := by
  rw [mem_matchedSubalgebra]
  simp only [repr_matchedIdem_apply]
  refine ⟨fun φ hφ ↦ ?_, fun φ a b hab ↦ ?_⟩
  · obtain ⟨hφ, hM, hcard⟩ := (ite_ne_right_iff.1 hφ).1
    have hinj : Set.InjOn M (φ.source : Set α) := card_image_iff.1 (by rw [hM, hcard])
    rw [hφ, source_idOn, target_idOn]
    exact ⟨hinj, hinj⟩
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this b a hab.symm h'
    · rw [swapHorizontal_of_not h h']
  have ha : a ∈ φ.source := mem_source.2 ⟨a, h.mem⟩
  -- Replacing `a` by `b` changes neither the image under `M` nor the size of the source.
  have himage : (insert b (φ.source.erase a)).image M = φ.source.image M := by
    rw [image_insert, ← hab, ← image_insert, insert_erase ha]
  have hcard : #(insert b (φ.source.erase a)) = #φ.source := by
    rw [card_insert_of_notMem fun h' ↦ h.notMem_source (mem_of_mem_erase h'),
      card_erase_of_mem ha]
    have := card_pos.2 ⟨a, ha⟩
    omega
  rw [source_swapHorizontal h, himage, hcard]
  refine if_congr (and_congr_left fun _ ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩) rfl rfl
  · -- Move the strand back: `φ` is the identity diagram with the strand at `a`.
    have hb : b ∈ insert b (φ.source.erase a) := mem_insert_self b _
    have ha' : a ∉ insert b (φ.source.erase a) := by simp [h.ne]
    conv_lhs => rw [← swapHorizontal_swapHorizontal φ a b, h']
    rw [swapHorizontal_comm, swapHorizontal_idOn hb ha',
      erase_insert fun hb' ↦ h.notMem_source (mem_of_mem_erase hb'), insert_erase ha]
  · conv_lhs => rw [h']
    exact swapHorizontal_idOn ha h.notMem_source

/-- The idempotents `I(s)` are orthogonal: `I(s) I(t)` is `I(s)` when `s = t` and zero
otherwise. -/
@[simp]
theorem matchedIdem_mul_matchedIdem (M : α → β) (s t : Finset β) :
    matchedIdem R M s * matchedIdem R M t = if s = t then matchedIdem R M s else 0 := by
  simp only [matchedIdem, sum_mul_sum, idem_mul_idem, sum_ite_eq, mem_filter, mem_univ, true_and]
  split_ifs with hst
  · subst hst
    exact sum_congr rfl fun S hS ↦ ite_eq_left (mem_filter.1 hS).2
  · refine sum_eq_zero fun S hS ↦ ite_eq_right fun h ↦ hst ?_
    rw [← (mem_filter.1 hS).2.1, h.1]

/-- Each `I(s)` is idempotent. -/
theorem isIdempotentElem_matchedIdem (M : α → β) (s : Finset β) :
    IsIdempotentElem (matchedIdem R M s) := by
  simp [IsIdempotentElem, matchedIdem_mul_matchedIdem]

end Idempotents

/-! ### The matched completion sums -/

section MatchedSum

variable {M : α → β}

/-- The coefficients of an element of the matched subalgebra agree on diagrams related by moving
horizontal strands to matched points. -/
theorem repr_eq_of_matchedSetoid {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M)
    {φ ψ : StrandDiagram α} (h : matchedSetoid M φ ψ) :
    (basis R α).repr x φ = (basis R α).repr x ψ :=
  apply_eq_of_matchedSetoid (mem_matchedSubalgebra.1 hx).2 h

variable (R M) in
/-- The **matched completion sum** of a strand diagram `φ`: the sum of the diagrams obtained from
`φ` by moving horizontal strands to points matched with them. When `φ` has no two matched starting
points and no two matched end points, it is the sum over all ways of placing each horizontal
strand of `φ` at any free point of its matched class, keeping the other strands; these sums span
the matched subalgebra. -/
def matchedSum (φ : StrandDiagram α) : StrandsAlgebra R α :=
  ∑ ψ ∈ (Set.toFinite {ψ | matchedSetoid M φ ψ}).toFinset, of ψ

open scoped Classical in
/-- The coefficients of a matched completion sum: `1` on the diagrams related to `φ` and `0`
elsewhere. -/
theorem repr_matchedSum_apply (φ ψ : StrandDiagram α) :
    (basis R α).repr (matchedSum R M φ) ψ = if matchedSetoid M φ ψ then 1 else 0 := by
  rw [matchedSum, repr_sum_of_apply]
  simp

/-- The matched completion sum of a diagram with no two matched starting points and no two matched
end points lies in the matched subalgebra. -/
theorem matchedSum_mem_matchedSubalgebra {φ : StrandDiagram α}
    (hS : Set.InjOn M (φ.source : Set α)) (hT : Set.InjOn M (φ.target : Set α)) :
    matchedSum R M φ ∈ matchedSubalgebra R M := by
  classical
  refine mem_matchedSubalgebra.2 ⟨fun ψ hψ ↦ ?_, fun ψ a b hab ↦ ?_⟩
  · rw [repr_matchedSum_apply] at hψ
    exact (injOn_source_and_target_iff_of_matchedSetoid (ite_ne_right_iff.1 hψ).1).1 ⟨hS, hT⟩
  · have h : matchedSetoid M ψ (ψ.swapHorizontal a b) := matchedSetoid_swapHorizontal hab
    have h' : matchedSetoid M φ (ψ.swapHorizontal a b) ↔ matchedSetoid M φ ψ :=
      ⟨fun h' ↦ (matchedSetoid M).iseqv.trans h' ((matchedSetoid M).iseqv.symm h),
        fun h' ↦ (matchedSetoid M).iseqv.trans h' h⟩
    simp only [repr_matchedSum_apply, h']

/-- **The matched completion sums span the matched subalgebra.** The sums
`TauCeti.StrandsAlgebra.matchedSum` of the diagrams with no two matched starting points and no two
matched end points span the matched subalgebra as an `R`-module. -/
theorem span_matchedSum :
    Submodule.span R (matchedSum R M ''
      {φ | Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)}) =
      (matchedSubalgebra R M).toSubmodule := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · rintro _ ⟨φ, ⟨hS, hT⟩, rfl⟩
    exact matchedSum_mem_matchedSubalgebra hS hT
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  let := Fintype.ofFinite (Quotient (matchedSetoid M))
  rw [NonUnitalSubalgebra.mem_toSubmodule] at hx
  -- Grouping the basis expansion of `x` by classes of diagrams writes `x` as a combination of
  -- the matched completion sums of class representatives.
  have key : x = ∑ C : Quotient (matchedSetoid M),
      (basis R α).repr x C.out • matchedSum R M C.out := by
    conv_lhs => rw [← (basis R α).sum_repr x]
    rw [← sum_fiberwise univ fun φ ↦ (⟦φ⟧ : Quotient (matchedSetoid M))]
    refine sum_congr rfl fun C _ ↦ ?_
    rw [matchedSum, smul_sum]
    refine sum_congr ?_ fun φ hφ ↦ ?_
    · ext φ
      simp only [mem_filter, mem_univ, true_and, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
        Quotient.mk_eq_iff_out]
      exact ⟨(matchedSetoid M).iseqv.symm, (matchedSetoid M).iseqv.symm⟩
    · rw [Set.Finite.mem_toFinset] at hφ
      rw [basis_apply, repr_eq_of_matchedSetoid hx hφ]
  rw [key]
  refine Submodule.sum_mem _ fun C _ ↦ ?_
  by_cases h : (basis R α).repr x C.out = 0
  · simp [h]
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨C.out, (mem_matchedSubalgebra.1 hx).1 _ h, rfl⟩)

end MatchedSum

/-! ### The generators `a(ρ, h)` and their products -/

section Generators

variable [DecidableEq β] (M : α → β)

/-- The pair `(ρ, h)` indexes a generator of the algebra of the matching `M`: `ρ` has no
horizontal strands, `M` is injective on its starting points and on its end points, and the set `h`
of pairs along which horizontal strands are added avoids the pairs of those points. -/
structure IsMatchedGenerator (ρ : StrandDiagram α) (h : Finset β) : Prop where
  notMem_self : ∀ i, i ∉ ρ i
  injOn_source : Set.InjOn M ρ.source
  injOn_target : Set.InjOn M ρ.target
  disjoint_source : Disjoint (ρ.source.image M) h
  disjoint_target : Disjoint (ρ.target.image M) h

/-- The choices of one point of each pair in `h`: the finite sets `U` with `M(U) = h` and `#U = #h`,
so that `M` is injective on `U` (`mem_matchedChoices`). -/
def matchedChoices (h : Finset β) : Finset (Finset α) :=
  {U | U.image M = h ∧ #U = #h}

variable {M}

omit [LinearOrder α] in
@[simp]
theorem mem_matchedChoices {h : Finset β} {U : Finset α} :
    U ∈ matchedChoices M h ↔ U.image M = h ∧ Set.InjOn M U := by
  simp only [matchedChoices, mem_filter, mem_univ, true_and]
  refine and_congr_right fun hU ↦ ?_
  rw [← card_image_iff, hU, eq_comm]

variable (M) in
/-- The element `a(ρ, h)` of the algebra of the matching `M`: the sum of the diagrams obtained from
`ρ` by adding a horizontal strand at one point of each pair in `h`, over all such choices `U`. When
`IsMatchedGenerator M ρ h` holds, each summand is `ρ` together with these horizontal strands; for
other inputs, the strands of `ρ` starting or ending at a chosen point are dropped. -/
def horizontalCompletion (ρ : StrandDiagram α) (h : Finset β) : StrandsAlgebra R α :=
  ∑ U ∈ matchedChoices M h, of (ρ.addHorizontal U)

theorem horizontalCompletion_def (ρ : StrandDiagram α) (h : Finset β) :
    (horizontalCompletion M ρ h : StrandsAlgebra R α) =
      ∑ U ∈ matchedChoices M h, of (ρ.addHorizontal U) :=
  (rfl)

/-- With no pairs to add horizontal strands along, `a(ρ, ∅)` is the diagram `ρ` itself. -/
@[simp]
theorem horizontalCompletion_empty (ρ : StrandDiagram α) :
    (horizontalCompletion M ρ ∅ : StrandsAlgebra R α) = of ρ := by
  simp [horizontalCompletion_def, matchedChoices, image_eq_empty, filter_eq']

/-- `a(ρ, h)` is zero unless `h` consists of pairs of `M`. -/
theorem horizontalCompletion_eq_zero_of_not_subset (ρ : StrandDiagram α) {h : Finset β}
    (hh : ¬h ⊆ univ.image M) : (horizontalCompletion M ρ h : StrandsAlgebra R α) = 0 :=
  (horizontalCompletion_def ρ h).trans <| sum_eq_zero fun U hU ↦
    absurd ((mem_matchedChoices.1 hU).1 ▸ image_subset_image (subset_univ U)) hh

namespace IsMatchedGenerator

variable {ρ : StrandDiagram α} {h : Finset β}

/-- Horizontal strands over the pairs of `h` avoid the starting points of `ρ`. -/
theorem disjoint_source_of_image_subset (hρ : IsMatchedGenerator M ρ h) {U : Finset α}
    (hU : U.image M ⊆ h) : Disjoint ρ.source U :=
  (disjoint_of_subset_right hU hρ.disjoint_source).of_image_finset

/-- Horizontal strands over the pairs of `h` avoid the end points of `ρ`. -/
theorem disjoint_target_of_image_subset (hρ : IsMatchedGenerator M ρ h) {U : Finset α}
    (hU : U.image M ⊆ h) : Disjoint ρ.target U :=
  (disjoint_of_subset_right hU hρ.disjoint_target).of_image_finset

end IsMatchedGenerator

section Product

variable {ρ σ : StrandDiagram α} {h k : Finset β}

/-- The composable pairs of summands of `a(ρ, h)` and `a(σ, k)`: the horizontal strands of the
first factor over the starting pairs of `σ` sit at the starting points of `σ`, those of the second
factor over the end pairs of `ρ` sit at the end points of `ρ`, and all other horizontal strands
are common to both factors, over the pairs of `h ∩ k`. -/
private theorem eq_union_inter_of_composable (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) {U V : Finset α} (hU : U.image M = h) (hV : V.image M = k)
    (hUV : (ρ.addHorizontal U).Composable (σ.addHorizontal V)) :
    ρ.target.image M ∪ h = σ.source.image M ∪ k ∧ U = {i ∈ σ.source | M i ∈ h} ∪ U ∩ V ∧
      V = {i ∈ ρ.target | M i ∈ k} ∪ U ∩ V ∧ (U ∩ V).image M = h ∩ k := by
  have hX : ρ.target ∪ U = σ.source ∪ V := by
    rw [← StrandDiagram.target_addHorizontal (hρ.disjoint_source_of_image_subset hU.le),
      ← StrandDiagram.source_addHorizontal (hσ.disjoint_target_of_image_subset hV.le)]
    exact hUV.target_eq
  have hmem (x : α) : x ∈ ρ.target ∨ x ∈ U ↔ x ∈ σ.source ∨ x ∈ V := by
    simpa using congrArg (x ∈ ·) hX
  have hUh (x : α) (hx : x ∈ U) : M x ∈ h := hU ▸ mem_image_of_mem M hx
  have hVk (x : α) (hx : x ∈ V) : M x ∈ k := hV ▸ mem_image_of_mem M hx
  have hTh (x : α) (hx : x ∈ ρ.target) : M x ∉ h :=
    disjoint_left.1 hρ.disjoint_target (mem_image_of_mem M hx)
  have hSk (x : α) (hx : x ∈ σ.source) : M x ∉ k :=
    disjoint_left.1 hσ.disjoint_source (mem_image_of_mem M hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hU, ← hV, ← image_union, ← image_union, hX]
  · ext x
    simp only [mem_union, mem_filter, mem_inter]
    grind
  · ext x
    simp only [mem_union, mem_filter, mem_inter]
    grind
  · ext m
    simp only [mem_image, mem_inter]
    constructor
    · rintro ⟨x, ⟨hxU, hxV⟩, rfl⟩
      exact ⟨hUh x hxU, hVk x hxV⟩
    · rintro ⟨hmh, hmk⟩
      obtain ⟨x, hxU, rfl⟩ := mem_image.1 (hU ▸ hmh)
      refine ⟨x, ⟨hxU, ?_⟩, rfl⟩
      exact ((hmem x).1 (Or.inr hxU)).resolve_left fun hxS ↦ hSk x hxS hmk

/-- The horizontal strands of `a(ρ, h)` forced at the points of `A` over `h` avoid the end points
of `ρ`, so they add to its starting points. -/
private theorem source_addHorizontal_filter (hρ : IsMatchedGenerator M ρ h) (A : Finset α) :
    (ρ.addHorizontal {i ∈ A | M i ∈ h}).source = ρ.source ∪ {i ∈ A | M i ∈ h} :=
  StrandDiagram.source_addHorizontal
    (hρ.disjoint_target_of_image_subset (image_filter_mem_subset _ _ _))

/-- The horizontal strands of `a(ρ, h)` forced at the points of `A` over `h` avoid the starting
points of `ρ`, so they add to its end points. -/
private theorem target_addHorizontal_filter (hρ : IsMatchedGenerator M ρ h) (A : Finset α) :
    (ρ.addHorizontal {i ∈ A | M i ∈ h}).target = ρ.target ∪ {i ∈ A | M i ∈ h} :=
  StrandDiagram.target_addHorizontal
    (hρ.disjoint_source_of_image_subset (image_filter_mem_subset _ _ _))

/-- Adding common horizontal strands over `h ∩ k` to the forced parts of two summands does not
change their composability, and commutes with their product. -/
private theorem composable_and_trans_of_image_subset_inter (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) {W : Finset α} (hW : W.image M ⊆ h ∩ k) :
    ((ρ.addHorizontal ({i ∈ σ.source | M i ∈ h} ∪ W)).Composable
        (σ.addHorizontal ({i ∈ ρ.target | M i ∈ k} ∪ W)) ↔
      (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
        (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) ∧
    (ρ.addHorizontal ({i ∈ σ.source | M i ∈ h} ∪ W)).trans
        (σ.addHorizontal ({i ∈ ρ.target | M i ∈ k} ∪ W)) =
      ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
        (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})).addHorizontal W := by
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  have hWh : W.image M ⊆ h := hW.trans inter_subset_left
  have hWk : W.image M ⊆ k := hW.trans inter_subset_right
  -- The forced horizontal strands lie over pairs used by the other factor.
  have hUfW : Disjoint Uf W :=
    (disjoint_of_disjoint_image_of_image_subset hσ.disjoint_source hWk).mono_left
      (filter_subset _ _)
  have hVfW : Disjoint Vf W :=
    (disjoint_of_disjoint_image_of_image_subset hρ.disjoint_target hWh).mono_left
      (filter_subset _ _)
  have h₁s : Disjoint (ρ.addHorizontal Uf).source W := by
    rw [source_addHorizontal_filter hρ]
    exact disjoint_union_left.2 ⟨hρ.disjoint_source_of_image_subset hWh, hUfW⟩
  have h₁t : Disjoint (ρ.addHorizontal Uf).target W := by
    rw [target_addHorizontal_filter hρ]
    exact disjoint_union_left.2 ⟨hρ.disjoint_target_of_image_subset hWh, hUfW⟩
  have h₂s : Disjoint (σ.addHorizontal Vf).source W := by
    rw [source_addHorizontal_filter hσ]
    exact disjoint_union_left.2 ⟨hσ.disjoint_source_of_image_subset hWk, hVfW⟩
  have h₂t : Disjoint (σ.addHorizontal Vf).target W := by
    rw [target_addHorizontal_filter hσ]
    exact disjoint_union_left.2 ⟨hσ.disjoint_target_of_image_subset hWk, hVfW⟩
  rw [← StrandDiagram.addHorizontal_addHorizontal, ← StrandDiagram.addHorizontal_addHorizontal]
  refine ⟨StrandDiagram.composable_addHorizontal_iff h₁s h₁t h₂s h₂t, ?_⟩
  exact StrandDiagram.addHorizontal_trans_addHorizontal fun _ _ ↦
    StrandDiagram.notMem_of_mem_of_disjoint_target h₁t

/-- If every pair of `h` outside `k` is a pair of a point of `A`, the points of `A` over `h`
together with a choice over `h ∩ k` form a choice over `h`. Here `A` is the set of starting points
of the second factor, or that of end points of the first. -/
private theorem filter_union_mem_matchedChoices {A W : Finset α} {h k : Finset β}
    (hA : Set.InjOn M A) (hAk : Disjoint (A.image M) k) (hh : h ⊆ A.image M ∪ k)
    (hW : W ∈ matchedChoices M (h ∩ k)) : {i ∈ A | M i ∈ h} ∪ W ∈ matchedChoices M h := by
  obtain ⟨hWim, hWi⟩ := mem_matchedChoices.1 hW
  refine mem_matchedChoices.2 ⟨image_filter_mem_union_eq hh hWim, ?_⟩
  rw [coe_union]
  refine (hA.mono (coe_subset.2 (filter_subset _ _))).union_of_disjoint_image hWi ?_
  simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_left
    (image_subset_image (filter_subset _ _))
    (disjoint_of_subset_right (hWim.le.trans inter_subset_right) hAk))

/-- Under the pair condition `M(ρ⁺) ∪ h = M(σ⁻) ∪ k`, the pairs of choices over `h` and over `k`
whose summands have a nonzero product are the images of the choices `W` over `h ∩ k` under
`W ↦ (U₀ ∪ W, V₀ ∪ W)`, so the expanded product `a(ρ, h) a(σ, k)` is a sum over `h ∩ k`. -/
private theorem sum_mul_eq_sum_matchedChoices_inter (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) (hC : ρ.target.image M ∪ h = σ.source.image M ∪ k) :
    ∑ p ∈ matchedChoices M h ×ˢ matchedChoices M k,
        (of (ρ.addHorizontal p.1) * of (σ.addHorizontal p.2) : StrandsAlgebra R α) =
      ∑ W ∈ matchedChoices M (h ∩ k), of (ρ.addHorizontal ({i ∈ σ.source | M i ∈ h} ∪ W)) *
        of (σ.addHorizontal ({i ∈ ρ.target | M i ∈ k} ∪ W)) := by
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  set g : Finset α → Finset α × Finset α := fun W ↦ (Uf ∪ W, Vf ∪ W)
  have hUfk : Disjoint (Uf.image M) k :=
    disjoint_of_subset_left (image_subset_image (filter_subset _ _)) hσ.disjoint_source
  -- A choice `W` over `h ∩ k` is recovered from `Uf ∪ W`, as the points over `k`.
  have hrec {W : Finset α} (hW : W ∈ matchedChoices M (h ∩ k)) :
      {x ∈ Uf ∪ W | M x ∈ k} = W := by
    rw [filter_union, filter_false_of_mem fun x hx ↦
        disjoint_left.1 hUfk (mem_image_of_mem M hx),
      filter_true_of_mem fun x hx ↦
        (mem_matchedChoices.1 hW).1.le.trans inter_subset_right (mem_image_of_mem M hx),
      empty_union]
  have hg : Set.InjOn g (matchedChoices M (h ∩ k)) := fun W hW W' hW' hWW' ↦ by
    have hfst : Uf ∪ W = Uf ∪ W' := congrArg Prod.fst hWW'
    rw [← hrec hW, ← hrec hW', hfst]
  refine ((sum_subset ?_ ?_).symm.trans (sum_image hg)).trans (sum_congr rfl fun _ _ ↦ rfl)
  · intro p hp
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hp
    exact mem_product.2 ⟨filter_union_mem_matchedChoices hσ.injOn_source hσ.disjoint_source
      (subset_union_right.trans hC.le) hW, filter_union_mem_matchedChoices hρ.injOn_target
      hρ.disjoint_target (subset_union_right.trans hC.ge) (inter_comm h k ▸ hW)⟩
  · intro p hp hpg
    obtain ⟨hU, hV⟩ := mem_product.1 hp
    refine of_mul_of_of_not_composable fun hUV ↦ hpg (mem_image.2 ⟨p.1 ∩ p.2, ?_⟩)
    obtain ⟨-, h₁, h₂, h₃⟩ := eq_union_inter_of_composable hρ hσ (mem_matchedChoices.1 hU).1
      (mem_matchedChoices.1 hV).1 hUV
    exact ⟨mem_matchedChoices.2 ⟨h₃, (mem_matchedChoices.1 hU).2.mono
      (coe_subset.2 inter_subset_left)⟩, Prod.ext h₁.symm h₂.symm⟩

/-- **The product of two generators of the algebra of a matching.** Let `U₀` be the starting
points of `σ` over the pairs of `h` and `V₀` the end points of `ρ` over the pairs of `k`. The
product `a(ρ, h) a(σ, k)` is zero unless the pairs at the right of the first factor are those at
the left of the second, `M(ρ⁺) ∪ h = M(σ⁻) ∪ k`, and `ρ` with horizontal strands at `U₀` is
composable with `σ` with horizontal strands at `V₀`; then it is the generator of their
composite and of the common pairs `h ∩ k`. -/
theorem horizontalCompletion_mul_horizontalCompletion (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) :
    (horizontalCompletion M ρ h * horizontalCompletion M σ k : StrandsAlgebra R α) =
      if ρ.target.image M ∪ h = σ.source.image M ∪ k ∧
          (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
            (σ.addHorizontal {i ∈ ρ.target | M i ∈ k}) then
        horizontalCompletion M ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
          (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) (h ∩ k)
      else 0 := by
  -- Expand the product as a sum over pairs `(U, V)` of choices over `h` and over `k`.
  have hLHS : (horizontalCompletion M ρ h * horizontalCompletion M σ k : StrandsAlgebra R α) =
      ∑ p ∈ matchedChoices M h ×ˢ matchedChoices M k,
        of (ρ.addHorizontal p.1) * of (σ.addHorizontal p.2) := by
    rw [horizontalCompletion_def, horizontalCompletion_def, sum_mul_sum, sum_product]
  rw [hLHS]
  split_ifs with hC
  · rw [sum_mul_eq_sum_matchedChoices_inter hρ hσ hC.1, horizontalCompletion_def]
    refine sum_congr rfl fun W hW ↦ ?_
    obtain ⟨hcomp, htrans⟩ :=
      composable_and_trans_of_image_subset_inter hρ hσ (mem_matchedChoices.1 hW).1.le
    rw [of_mul_of_of_composable (hcomp.2 hC.2), htrans]
  · -- A nonzero summand has the shape described by `eq_union_inter_of_composable`.
    refine sum_eq_zero fun p hp ↦ of_mul_of_of_not_composable fun hUV ↦ hC ?_
    obtain ⟨hU, hV⟩ := mem_product.1 hp
    obtain ⟨hC', h₁, h₂, h₃⟩ := eq_union_inter_of_composable hρ hσ (mem_matchedChoices.1 hU).1
      (mem_matchedChoices.1 hV).1 hUV
    refine ⟨hC', ?_⟩
    have := (composable_and_trans_of_image_subset_inter hρ hσ h₃.le).1
    rw [← h₁, ← h₂] at this
    exact this.1 hUV

/-- The composite in `horizontalCompletion_mul_horizontalCompletion`, together with the common
pairs `h ∩ k`, again indexes a generator. -/
theorem IsMatchedGenerator.trans (hρ : IsMatchedGenerator M ρ h) (hσ : IsMatchedGenerator M σ k)
    (hτ : (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
      (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) :
    IsMatchedGenerator M ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
      (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) (h ∩ k) := by
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  have hUf : Uf.image M ⊆ h := image_filter_mem_subset _ _ _
  have hVf : Vf.image M ⊆ k := image_filter_mem_subset _ _ _
  have hUfS : Uf.image M ⊆ σ.source.image M := image_subset_image (filter_subset _ _)
  have hVfT : Vf.image M ⊆ ρ.target.image M := image_subset_image (filter_subset _ _)
  have hsource : ((ρ.addHorizontal Uf).trans (σ.addHorizontal Vf)).source = ρ.source ∪ Uf := by
    rw [StrandDiagram.source_trans_of_target_eq hτ.target_eq, source_addHorizontal_filter hρ]
  have htarget : ((ρ.addHorizontal Uf).trans (σ.addHorizontal Vf)).target = σ.target ∪ Vf := by
    rw [StrandDiagram.target_trans_of_target_eq hτ.target_eq, target_addHorizontal_filter hσ]
  -- Pairs over `h` avoid the end points of `ρ`, so no point carries forced strands of both kinds.
  have hUfVf : Disjoint Uf Vf :=
    ((disjoint_of_disjoint_image_of_image_subset hρ.disjoint_target hUf).mono_left
      (filter_subset _ _)).symm
  refine ⟨fun i hi ↦ ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hij, hji⟩ := StrandDiagram.mem_trans.1 hi
    obtain rfl : j = i := le_antisymm ((σ.addHorizontal Vf).le_of_mem hji)
      ((ρ.addHorizontal Uf).le_of_mem hij)
    exact disjoint_left.1 hUfVf ((StrandDiagram.mem_addHorizontal_self hρ.notMem_self).1 hij)
      ((StrandDiagram.mem_addHorizontal_self hσ.notMem_self).1 hji)
  · rw [hsource, coe_union]
    refine hρ.injOn_source.union_of_disjoint_image
      (hσ.injOn_source.mono (coe_subset.2 (filter_subset _ _))) ?_
    simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_right hUf hρ.disjoint_source)
  · rw [htarget, coe_union]
    refine hσ.injOn_target.union_of_disjoint_image
      (hρ.injOn_target.mono (coe_subset.2 (filter_subset _ _))) ?_
    simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_right hVf hσ.disjoint_target)
  · rw [hsource, image_union]
    exact disjoint_union_left.2 ⟨disjoint_of_subset_right inter_subset_left hρ.disjoint_source,
      disjoint_of_subset_left hUfS (disjoint_of_subset_right inter_subset_right
        hσ.disjoint_source)⟩
  · rw [htarget, image_union]
    exact disjoint_union_left.2 ⟨disjoint_of_subset_right inter_subset_right hσ.disjoint_target,
      disjoint_of_subset_left hVfT (disjoint_of_subset_right inter_subset_left
        hρ.disjoint_target)⟩

end Product

/-! ### The algebra of a matching -/

open scoped Pointwise in
variable (R M) in
/-- The algebra of the matching `M`, spanned by the elements `a(ρ, h)`. For the matching of a
pointed matched circle `Z` this is the span description of the algebra `A(Z)` of Lipshitz,
Ozsváth and Thurston, without its differential; `matchedSubalgebra R M` is the intrinsic
description. It is closed under multiplication because the product of two of its
generators is again one or zero (`horizontalCompletion_mul_horizontalCompletion`). It is a
non-unital subalgebra of the strands algebra; its own unit is `matchedOne R M`. -/
def matchedAlgebra : NonUnitalSubalgebra R (StrandsAlgebra R α) :=
  (Submodule.span R {x | ∃ ρ h, IsMatchedGenerator M ρ h ∧ horizontalCompletion M ρ h = x}
    ).toNonUnitalSubalgebra fun x y hx hy ↦ by
      have hxy := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at hxy
      refine Submodule.span_le.2 ?_ hxy
      rintro _ ⟨_, ⟨ρ, h, hρ, rfl⟩, _, ⟨σ, k, hσ, rfl⟩, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, horizontalCompletion_mul_horizontalCompletion hρ hσ]
      split_ifs with hC
      · exact Submodule.subset_span ⟨_, _, hρ.trans hσ hC.2, rfl⟩
      · exact zero_mem _

theorem mem_matchedAlgebra_iff {x : StrandsAlgebra R α} :
    x ∈ matchedAlgebra R M ↔
      x ∈ Submodule.span R {x | ∃ ρ h, IsMatchedGenerator M ρ h ∧ horizontalCompletion M ρ h = x} :=
  Iff.rfl

theorem horizontalCompletion_mem_matchedAlgebra {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) :
    (horizontalCompletion M ρ h : StrandsAlgebra R α) ∈ matchedAlgebra R M :=
  Submodule.subset_span ⟨ρ, h, hρ, rfl⟩

/-- To prove a linear property of the elements of the algebra of a matching, it suffices to prove
it for the generators `a(ρ, h)`. -/
@[elab_as_elim]
theorem matchedAlgebra_induction {p : (x : StrandsAlgebra R α) → x ∈ matchedAlgebra R M → Prop}
    (generator : ∀ ρ h (hρ : IsMatchedGenerator M ρ h),
      p (horizontalCompletion M ρ h) (horizontalCompletion_mem_matchedAlgebra hρ))
    (zero : p 0 (zero_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) : p x hx := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ρ, h, hρ, rfl⟩ := hx
    exact generator ρ h hρ
  | zero => exact zero
  | add x y hx hy px py => exact add x y hx hy px py
  | smul r x hx px => exact smul r x hx px

end Generators

/-! ### Idempotents and the unit -/

section Unit

variable [DecidableEq β] (M : α → β)

/-- The empty diagram, with no horizontal strands added, indexes a generator for every set of
pairs. -/
theorem isMatchedGenerator_idOn_empty (s : Finset β) :
    IsMatchedGenerator M (StrandDiagram.idOn ∅) s where
  notMem_self i := by simp
  injOn_source := by simp
  injOn_target := by simp
  disjoint_source := by simp
  disjoint_target := by simp

/-- The idempotent `I(s)` is the generator `a(∅, s)`: the empty diagram with a horizontal strand
added at one point of each pair in `s`. -/
theorem matchedIdem_eq_horizontalCompletion (s : Finset β) :
    matchedIdem R M s = horizontalCompletion M (StrandDiagram.idOn ∅) s := by
  simp [matchedIdem_def, horizontalCompletion_def, matchedChoices,
    StrandDiagram.idOn_addHorizontal, idem_def]

theorem matchedIdem_mem_matchedAlgebra (s : Finset β) :
    matchedIdem R M s ∈ matchedAlgebra R M :=
  matchedIdem_eq_horizontalCompletion (R := R) M s ▸
    horizontalCompletion_mem_matchedAlgebra (isMatchedGenerator_idOn_empty M s)

variable {M} in
/-- Multiplying `a(ρ, h)` on the left by `I(s)` keeps it exactly when `s` is the set of pairs at
its left, those of the starting points of `ρ` together with `h`. -/
@[simp]
theorem matchedIdem_mul_horizontalCompletion (s : Finset β) {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) :
    (matchedIdem R M s * horizontalCompletion M ρ h : StrandsAlgebra R α) =
      if s = ρ.source.image M ∪ h then horizontalCompletion M ρ h else 0 := by
  rw [matchedIdem_eq_horizontalCompletion, horizontalCompletion_mul_horizontalCompletion
    (isMatchedGenerator_idOn_empty M s) hρ]
  simp only [StrandDiagram.target_idOn, image_empty, empty_union, filter_empty,
    StrandDiagram.addHorizontal_empty, StrandDiagram.idOn_addHorizontal,
    StrandDiagram.composable_idOn_left_iff]
  by_cases hs : s = ρ.source.image M ∪ h
  · subst hs
    have hfilter : {i ∈ ρ.source | M i ∈ ρ.source.image M ∪ h} = ρ.source :=
      filter_true_of_mem fun i hi ↦ mem_union_left _ (mem_image_of_mem M hi)
    simp only [hfilter, and_self, ↓reduceIte, StrandDiagram.idOn_trans_of_eq_source rfl,
      inter_eq_right.2 (subset_union_right (s₁ := ρ.source.image M))]
  · simp only [hs, false_and, ↓reduceIte]

variable {M} in
/-- Multiplying `a(ρ, h)` on the right by `I(t)` keeps it exactly when `t` is the set of pairs at
its right, those of the end points of `ρ` together with `h`. -/
@[simp]
theorem horizontalCompletion_mul_matchedIdem {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) (t : Finset β) :
    (horizontalCompletion M ρ h * matchedIdem R M t : StrandsAlgebra R α) =
      if ρ.target.image M ∪ h = t then horizontalCompletion M ρ h else 0 := by
  rw [matchedIdem_eq_horizontalCompletion, horizontalCompletion_mul_horizontalCompletion hρ
    (isMatchedGenerator_idOn_empty M t)]
  simp only [StrandDiagram.source_idOn, image_empty, empty_union, filter_empty,
    StrandDiagram.addHorizontal_empty, StrandDiagram.idOn_addHorizontal,
    StrandDiagram.composable_idOn_right_iff]
  by_cases ht : ρ.target.image M ∪ h = t
  · subst ht
    have hfilter : {i ∈ ρ.target | M i ∈ ρ.target.image M ∪ h} = ρ.target :=
      filter_true_of_mem fun i hi ↦ mem_union_left _ (mem_image_of_mem M hi)
    simp only [hfilter, and_self, ↓reduceIte, StrandDiagram.trans_idOn_of_target_eq rfl,
      inter_eq_left.2 (subset_union_right (s₁ := ρ.target.image M))]
  · simp only [ht, false_and, ↓reduceIte]

variable (R) in
/-- The unit of the algebra of a matching: the sum of the idempotents `I(s)` over all sets `s` of
pairs, the subsets of the image of `M`. -/
def matchedOne : StrandsAlgebra R α :=
  ∑ s ∈ (univ.image M).powerset, matchedIdem R M s

theorem matchedOne_def :
    matchedOne R M = ∑ s ∈ (univ.image M).powerset, matchedIdem R M s :=
  (rfl)

theorem matchedOne_mem_matchedAlgebra : matchedOne R M ∈ matchedAlgebra R M :=
  sum_mem fun s _ ↦ matchedIdem_mem_matchedAlgebra M s

variable {M} in
/-- `∑ₛ I(s)` is a left unit for the algebra of a matching. -/
@[simp]
theorem matchedOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) :
    matchedOne R M * x = x := by
  induction hx using matchedAlgebra_induction with
  | generator ρ h hρ =>
    simp only [matchedOne_def, sum_mul, matchedIdem_mul_horizontalCompletion _ hρ, sum_ite_eq',
      mem_powerset]
    split_ifs with hS
    · rfl
    · exact (horizontalCompletion_eq_zero_of_not_subset ρ fun hh ↦
        hS (union_subset (image_subset_image (subset_univ _)) hh)).symm
  | zero => exact mul_zero _
  | add x y _ _ hx hy => rw [mul_add, hx, hy]
  | smul r x _ hx => rw [mul_smul_comm, hx]

variable {M} in
/-- `∑ₛ I(s)` is a right unit for the algebra of a matching. -/
@[simp]
theorem mul_matchedOne {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) :
    x * matchedOne R M = x := by
  induction hx using matchedAlgebra_induction with
  | generator ρ h hρ =>
    simp only [matchedOne_def, mul_sum, horizontalCompletion_mul_matchedIdem hρ, sum_ite_eq,
      mem_powerset]
    split_ifs with hS
    · rfl
    · exact (horizontalCompletion_eq_zero_of_not_subset ρ fun hh ↦
        hS (union_subset (image_subset_image (subset_univ _)) hh)).symm
  | zero => exact zero_mul _
  | add x y _ _ hx hy => rw [add_mul, hx, hy]
  | smul r x _ hx => rw [smul_mul_assoc, hx]

end Unit

/-! ### The unit of the matched subalgebra -/

section SubalgebraUnit

variable [DecidableEq β] {M : α → β}

open scoped Classical in
/-- The unit `∑ₛ I(s)` is the sum of the idempotents `I(S)` over the sets `S` with no two matched
points. -/
theorem matchedOne_eq_sum_idem :
    matchedOne R M = ∑ S ∈ univ.filter fun S : Finset α ↦ Set.InjOn M (S : Set α), idem S := by
  symm
  rw [matchedOne_def, ← sum_fiberwise_of_maps_to fun S _ ↦
    mem_powerset.2 (image_subset_image (f := M) (subset_univ S))]
  refine sum_congr rfl fun s _ ↦ sum_congr ?_ fun _ _ ↦ rfl
  ext S
  simp only [mem_filter, mem_univ, true_and, ← card_image_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨rfl, h.symm⟩
  · rintro ⟨rfl, h⟩
    exact ⟨h.symm, rfl⟩

/-- The unit `TauCeti.StrandsAlgebra.matchedOne R M` lies in the matched subalgebra. -/
theorem matchedOne_mem_matchedSubalgebra : matchedOne R M ∈ matchedSubalgebra R M :=
  sum_mem fun s _ ↦ matchedIdem_mem_matchedSubalgebra M s

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem differential_matchedOne : differential R α (matchedOne R M) = 0 := by
  simp [matchedOne_def]

/-- The unit of the matched subalgebra fixes a diagram with no two matched starting points. -/
theorem matchedOne_mul_of {φ : StrandDiagram α} (h : Set.InjOn M (φ.source : Set α)) :
    matchedOne R M * of φ = of φ := by
  classical
  simp [matchedOne_eq_sum_idem, sum_mul, idem_mul_of, h]

/-- The unit of the matched subalgebra fixes a diagram with no two matched end points. -/
theorem of_mul_matchedOne {φ : StrandDiagram α} (h : Set.InjOn M (φ.target : Set α)) :
    of φ * matchedOne R M = of φ := by
  classical
  simp [matchedOne_eq_sum_idem, mul_sum, of_mul_idem, h]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a left identity on the elements of the matched
subalgebra. -/
theorem matchedOne_mul_of_mem_matchedSubalgebra {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : matchedOne R M * x = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [mul_sum]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [mul_smul_comm, basis_apply, matchedOne_mul_of ((mem_matchedSubalgebra.1 hx).1 φ hφ).1]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a right identity on the elements of the matched
subalgebra. -/
theorem mul_matchedOne_of_mem_matchedSubalgebra {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : x * matchedOne R M = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [sum_mul]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [smul_mul_assoc, basis_apply, of_mul_matchedOne ((mem_matchedSubalgebra.1 hx).1 φ hφ).2]

instance : One (matchedSubalgebra R M) :=
  ⟨⟨matchedOne R M, matchedOne_mem_matchedSubalgebra⟩⟩

/-- The unit of the matched subalgebra is `TauCeti.StrandsAlgebra.matchedOne`, which differs from
the unit of the strands algebra when `R` is nontrivial and `M` identifies two points. -/
@[simp]
theorem coe_matchedSubalgebra_one :
    ((1 : matchedSubalgebra R M) : StrandsAlgebra R α) = matchedOne R M :=
  (rfl)

/-- The matched subalgebra is a unital algebra, with unit `TauCeti.StrandsAlgebra.matchedOne`. -/
instance : Semiring (matchedSubalgebra R M) where
  __ := (matchedSubalgebra R M).toNonUnitalSemiring
  one_mul x := Subtype.ext (matchedOne_mul_of_mem_matchedSubalgebra x.2)
  mul_one x := Subtype.ext (mul_matchedOne_of_mem_matchedSubalgebra x.2)

instance {R : Type*} [CommRing R] : Ring (matchedSubalgebra R M) where
  __ := (inferInstance : Semiring (matchedSubalgebra R M))
  __ := (matchedSubalgebra R M).toNonUnitalRing

instance : Algebra R (matchedSubalgebra R M) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

end SubalgebraUnit

/-! ### The differential of the matched subalgebra -/

section Differential

variable {M : α → β}

variable (R M) in
/-- The differential of the strands algebra restricted to the matched subalgebra. -/
def matchedDifferential : matchedSubalgebra R M →ₗ[R] matchedSubalgebra R M :=
  (differential R α).restrict (p := (matchedSubalgebra R M).toSubmodule)
    (q := (matchedSubalgebra R M).toSubmodule) fun _ hx ↦ differential_mem_matchedSubalgebra hx

@[simp]
theorem coe_matchedDifferential (x : matchedSubalgebra R M) :
    (matchedDifferential R M x : StrandsAlgebra R α) = differential R α x :=
  (rfl)

variable [DecidableEq β] in
/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem matchedDifferential_one : matchedDifferential R M 1 = 0 :=
  Subtype.ext (by simp)

/-- Over a ring of characteristic two, such as `𝔽₂`, the matched subalgebra with the restricted
differential is an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_matchedDifferential [DecidableEq β] {R : Type*} [CommRing R]
    [CharP R 2] :
    IsUngradedDGAlgebra (matchedDifferential R M) where
  map_mul a b := Subtype.ext (by simp [differential_mul])
  map_map a := Subtype.ext (by simp [differential_differential])

end Differential

end StrandsAlgebra

end TauCeti
