/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Multiset.EqualPartMerging
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Algebra.Order.Group.Multiset
import TauCeti.GroupTheory.Perm.Semiconj

/-!
# Permutations whose cycle type is a merging of a partition

For a partition `ρ` of `n`, a bound `y`, and a finite carrier `α`, `TauCeti.mergePerms y ρ` is the
set of permutations of `α` whose full cycle type (with fixed points counted as parts `1`) is a
`y`-merging of the parts of `ρ`, in the sense of `TauCeti.EqualPartMerging`. Membership forces
`n` to be the cardinality of `α`, and the set is closed under conjugation and relabelling.

The source of such permutations is `Function.Semiconj.equalPartMerging_replicate_fullCycleType`:
if `r : α → β` intertwines `σ` with a permutation `ψ` consisting of a single cycle of length `d`,
and every fibre of `r` has `m` points, then the cycles of `σ` lying over that cycle have lengths
`d * mᵢ` with `0 < mᵢ ≤ m` and `∑ mᵢ = m`, so the full cycle type of `σ` is an `m`-merging of `m`
copies of `d`. Applied to the reduction of the roots of a polynomial modulo a prime and a
Frobenius element, it compares the cycle type of the Frobenius element with the factor degrees
at a ramified prime (Bary-Soroker, Koukoulopoulos and Kozma, *Irreducibility of random
polynomials: general measures*, Lemma 11.3 and Claim 11.4).

## Main definitions

* `TauCeti.mergePerms y ρ`: the permutations whose full cycle type is a `y`-merging of `ρ.parts`.

## Main results

* `TauCeti.mergePerms_mono`: the set grows with the bound.
* `TauCeti.card_eq_of_mem_mergePerms`: a member forces `Fintype.card α = n`.
* `TauCeti.conj_mem_mergePerms_iff`, `TauCeti.permCongr_mem_mergePerms_iff`: invariance under
  conjugation and under relabelling along `α ≃ β`.
* `TauCeti.mem_mergePerms_iff_of_lt_two`: for `1 ≤ y < 2`, membership says the full cycle type
  is `ρ.parts`.
* `Function.Semiconj.equalPartMerging_replicate_fullCycleType`: cycles lying over a single cycle
  of length `d`, with fibres of `m` points, form an `m`-merging of `m` copies of `d`.
-/

public section

open Equiv Equiv.Perm Function

open scoped Finset

namespace TauCeti

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {n : ℕ} {y z : ℝ} {ρ : n.Partition} {σ : Perm α}

variable (α) in
/-- The permutations of `α` whose full cycle type, fixed points counted as parts `1`, is a
`y`-merging of the parts of the partition `ρ`. -/
def mergePerms (y : ℝ) (ρ : n.Partition) : Set (Perm α) :=
  {σ | EqualPartMerging y ρ.parts σ.fullCycleType}

@[simp]
theorem mem_mergePerms : σ ∈ mergePerms α y ρ ↔ EqualPartMerging y ρ.parts σ.fullCycleType :=
  Iff.rfl

/-- Enlarging the bound enlarges the set of merged permutations. -/
@[gcongr]
theorem mergePerms_mono (hyz : y ≤ z) : mergePerms α y ρ ⊆ mergePerms α z ρ :=
  fun _ hσ => EqualPartMerging.mono hσ hyz

/-- A permutation whose full cycle type is a merging of a partition of `n` acts on a carrier of
cardinality `n`. -/
theorem card_eq_of_mem_mergePerms (hσ : σ ∈ mergePerms α y ρ) : Fintype.card α = n := by
  rw [← sum_fullCycleType σ, ← hσ.sum_eq, ρ.parts_sum]

/-- Conjugation preserves membership in `mergePerms`. -/
theorem conj_mem_mergePerms_iff (g : Perm α) :
    g * σ * g⁻¹ ∈ mergePerms α y ρ ↔ σ ∈ mergePerms α y ρ := by
  simp

/-- Relabelling the carrier along `e : α ≃ β` preserves membership in `mergePerms`. -/
theorem permCongr_mem_mergePerms_iff (e : α ≃ β) :
    e.permCongr σ ∈ mergePerms β y ρ ↔ σ ∈ mergePerms α y ρ := by
  simp

/-- For `1 ≤ y < 2`, a permutation lies in `mergePerms y ρ` exactly when its full cycle type is
the multiset of parts of `ρ`. -/
theorem mem_mergePerms_iff_of_lt_two (hy₁ : 1 ≤ y) (hy₂ : y < 2) :
    σ ∈ mergePerms α y ρ ↔ ρ.parts = σ.fullCycleType := by
  rw [mem_mergePerms, equalPartMerging_iff_eq_of_lt_two hy₁ hy₂]

/-- The identity lies in `mergePerms 1 ρ` exactly when `ρ` consists of `Fintype.card α` parts
equal to `1`; a cycle type omitting fixed points would fail this. -/
example : (1 : Perm α) ∈ mergePerms α 1 ρ ↔ ρ.parts = Multiset.replicate (Fintype.card α) 1 := by
  rw [mem_mergePerms_iff_of_lt_two le_rfl one_lt_two, fullCycleType_one]

end TauCeti

namespace Function.Semiconj

open TauCeti

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- If the cycles `q` of `σ` have lengths `K q * d` with `0 < K q ≤ m` and `∑ q, K q = m`, then
the full cycle type of `σ` is an `m`-merging of `m` copies of `d`, with one block of `K q`
copies of `d` for each cycle. -/
private theorem equalPartMerging_of_cycle_counts {σ : Perm α}
    [Fintype (Quotient (SameCycle.setoid σ))] {d m : ℕ} (K : Quotient (SameCycle.setoid σ) → ℕ)
    (hK : ∀ x, K (Quotient.mk _ x) * d = minimalPeriod σ x) (hKpos : ∀ q, 0 < K q)
    (hKle : ∀ q, K q ≤ m) (hKsum : ∑ q, K q = m) :
    EqualPartMerging m (Multiset.replicate m d) σ.fullCycleType := by
  -- Write both sides as sums over the cycles of `σ`, and merge cycle by cycle.
  have hleft : Multiset.replicate m d = ∑ q, Multiset.replicate (K q) d := by
    rw [eq_comm, Multiset.eq_replicate, Multiset.card_sum]
    simp [hKsum, Multiset.mem_sum, Multiset.mem_replicate]
  have hright : σ.fullCycleType = ∑ q, {K q * d} := by
    rw [fullCycleType_eq_map_univ σ (Equiv.refl _)
      (f := Quotient.lift (minimalPeriod σ) fun _ _ h => h.minimalPeriod_eq) fun _ => rfl,
      ← Multiset.sum_map_singleton (Multiset.map _ _), Multiset.map_map,
      Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
    induction q using Quotient.inductionOn with
    | h x => rw [Function.comp_apply, Quotient.lift_mk, hK]
  rw [hleft, hright]
  exact equalPartMerging_sum _ fun q _ =>
    equalPartMerging_replicate_singleton (hKpos q) (by exact_mod_cast hKle q) d

/-- **Cycles above a single cycle merge equal parts.** Let `r : α → β` intertwine `σ` with a
permutation `ψ` that is a single cycle of length `d`, fixed points included, and let every fibre
of `r` have `m` points. Then each cycle of `σ` has length `d * mᵢ`, where `0 < mᵢ ≤ m` is the
number of its points in any one fibre, and these `mᵢ` sum to `m`. So the full cycle type of `σ` is
an `m`-merging of `m` copies of `d`: one block of `mᵢ` copies of `d` for each cycle. -/
theorem equalPartMerging_replicate_fullCycleType {r : α → β} {σ : Perm α} {ψ : Perm β}
    (h : Semiconj r σ ψ) {d m : ℕ} (hψ : ψ.fullCycleType = {d})
    (hr : ∀ b, Fintype.card {a // r a = b} = m) :
    EqualPartMerging m (Multiset.replicate m d) σ.fullCycleType := by
  classical
  -- Every point of `β` lies on the single cycle of `ψ`, whose length is `d`.
  have hper (b : β) : minimalPeriod ψ b = d := by
    simpa [hψ] using mem_fullCycleType_iff (σ := ψ).2 ⟨b, rfl⟩
  obtain ⟨⟨b₀, hb₀⟩, -⟩ := (fullCycleType_eq_singleton_iff ψ).1 hψ
  -- Every cycle of `σ` meets the fibre over `b₀`.
  have hmeet (x : α) : ∃ x', σ.SameCycle x x' ∧ r x' = b₀ := by
    obtain ⟨i, -, hi⟩ := (hb₀ (r x)).symm.exists_pow_eq'
    exact ⟨(σ ^ i) x, ⟨i, by simp⟩, by rw [coe_pow, h.iterate_right, ← coe_pow, hi]⟩
  -- `K q` is the number of points of the cycle `q` lying over `b₀`.
  let Q := Quotient (SameCycle.setoid σ)
  let K : Q → ℕ := fun q => #{y | r y = b₀ ∧ Quotient.mk _ y = q}
  have hK (x : α) : K (Quotient.mk _ x) * d = minimalPeriod σ x := by
    obtain ⟨x', hxx', hx'⟩ := hmeet x
    rw [hxx'.minimalPeriod_eq, ← h.ncard_sameCycle_and_eq_mul_minimalPeriod x', hper, hx']
    congr 1
    simp only [K]
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [and_comm, Quotient.eq]
    exact and_congr_left fun _ => ⟨fun hy : σ.SameCycle y x => (hy.trans hxx').symm,
      fun hy => (hxx'.trans hy).symm⟩
  have hfibre : #{y | r y = b₀} = m := by
    rw [← hr b₀, Fintype.card_subtype]
  have hKpos (q : Q) : 0 < K q := by
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨x', hxx', hx'⟩ := hmeet x
      exact Finset.card_pos.2 ⟨x', Finset.mem_filter.2 ⟨Finset.mem_univ _, hx',
        Quotient.sound hxx'.symm⟩⟩
  have hKle (q : Q) : K q ≤ m := by
    rw [← hfibre]
    refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.1
  have hKsum : ∑ q, K q = m := by
    rw [← hfibre, Finset.card_eq_sum_card_fiberwise (f := Quotient.mk (SameCycle.setoid σ))
      (t := Finset.univ) fun _ _ => Finset.mem_univ _]
    -- The two sides differ only in the decidability instances of the filters.
    simp only [K, Finset.filter_filter]
    rfl
  exact equalPartMerging_of_cycle_counts K hK hKpos hKle hKsum

end Function.Semiconj
