/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Elementary facts about permutations

This file records general-purpose facts about permutations: an identity between transpositions,
a characterization of permutations with a unique fixed point, functions constant on a permutation
orbit, the orbit relation of an involution, a positive-power representative of a relation inside a
periodic orbit, a permutation transported along an injection, and the combination of two
permutations transported along injections with disjoint ranges.
-/

public section

namespace Equiv.Perm.SameCycle

variable {α : Type*} {β : Sort*} {σ : Equiv.Perm α} {x y : α} {f : α → β}

variable {γ : Type*} {τ : Equiv.Perm γ} {g : α → γ}

private theorem map_zpow_apply (hg : ∀ z, g (σ z) = τ (g z)) (k : ℤ) (z : α) :
    g ((σ ^ k) z) = (τ ^ k) (g z) := by
  have hinv : Function.Semiconj g (σ⁻¹ : Equiv.Perm α) (τ⁻¹ : Equiv.Perm γ) :=
    Function.Semiconj.inverses_right hg σ.right_inv τ.left_inv
  cases k with
  | ofNat m =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hg m z)
  | negSucc m =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hinv (m + 1) z)

/-- A function invariant under one application of a permutation is constant on every orbit of
that permutation. -/
theorem apply_eq_of_apply_eq (hσ : σ.SameCycle x y) (hf : ∀ z, f (σ z) = f z) : f x = f y := by
  obtain ⟨k, rfl⟩ := hσ
  have hmap := map_zpow_apply (τ := 1) (g := fun z => PLift.up (f z))
    (fun z => congrArg PLift.up (hf z)) k x
  exact congrArg PLift.down (by simpa only [one_zpow, Equiv.Perm.one_apply] using hmap.symm)

/-- A map intertwining two permutations carries orbits of the first permutation into orbits of
the second. -/
theorem map (hσ : σ.SameCycle x y) (hg : ∀ z, g (σ z) = τ (g z)) :
    τ.SameCycle (g x) (g y) := by
  obtain ⟨k, rfl⟩ := hσ
  exact ⟨k, (map_zpow_apply hg k x).symm⟩

/-- If a periodic point `x` of `σ` shares its orbit with `y`, some positive natural power of `σ`
carries `x` to `y`. -/
theorem exists_pos_pow_eq_of_mem_periodicPts (h : σ.SameCycle x y)
    (hx : x ∈ Function.periodicPts (σ : α → α)) : ∃ j : ℕ, 0 < j ∧ (σ ^ j) x = y := by
  obtain ⟨k, hk⟩ := h
  have hperiod : MulAction.period σ x = Function.minimalPeriod (σ : α → α) x :=
    MulAction.period_eq_minimalPeriod
  have hpos : 0 < MulAction.period σ x :=
    hperiod ▸ Function.minimalPeriod_pos_of_mem_periodicPts hx
  have hnonneg : 0 ≤ k % (MulAction.period σ x : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hpos.ne')
  refine ⟨(k % (MulAction.period σ x : ℤ)).toNat + MulAction.period σ x, by omega, ?_⟩
  have hred : σ ^ (k % (MulAction.period σ x : ℤ) + (MulAction.period σ x : ℤ)) • x = y := by
    rw [MulAction.zpow_add_period_smul, MulAction.zpow_mod_period_smul]
    exact hk
  rw [Equiv.Perm.smul_def] at hred
  rw [← zpow_natCast, Nat.cast_add, Int.toNat_of_nonneg hnonneg]
  exact hred

end Equiv.Perm.SameCycle

namespace TauCeti

/-- Two points lie in the same orbit of an involution exactly when they are equal or one is the
image of the other. -/
theorem sameCycle_toPerm_iff {α : Type*} (f : α → α) (hf : Function.Involutive f) (a b : α) :
    (hf.toPerm f).SameCycle a b ↔ a = b ∨ a = f b := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.symm
    rcases Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self
      (f := hf.toPerm f) (x := b) (hf b) i with h | h
    · exact Or.inl (hi.symm.trans h)
    · exact Or.inr (hi.symm.trans h)
  · rintro (rfl | h)
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      have : f a = b := by
        calc
          f a = f (f b) := congrArg f h
          _ = b := hf b
      simpa using this

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation moves all but one point exactly when it has a unique fixed point. -/
theorem card_support_add_one_eq_card_iff_existsUnique_fixedPoint (σ : Equiv.Perm α) :
    σ.support.card + 1 = Fintype.card α ↔ ∃! x : α, σ x = x := by
  have hfixed : (∃! x : α, x ∈ σ.supportᶜ) ↔ ∃! x : α, σ x = x := by
    simp only [Finset.mem_compl, Equiv.Perm.notMem_support]
  rw [← hfixed, ← Finset.card_eq_one_iff_existsUnique, Finset.card_compl]
  omega

/-- Whenever `a` and `c` are both distinct from `b`, the transpositions `(a b)` and `(b c)`
satisfy the braid relation. The two points `a` and `c` need not be distinct: for `a = c` both
sides are `(a b)`. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hcb : c ≠ b) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  rcases eq_or_ne a c with rfl | hac
  · rw [Equiv.swap_comm b a]
  · calc Equiv.swap a b * Equiv.swap b c * Equiv.swap a b
        = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
          rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
      _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hcb (Ne.symm hac)
      _ = Equiv.swap c a := Equiv.swap_comm a c
      _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
          (Equiv.swap_mul_swap_mul_swap hab hac).symm

/-- **A permutation along an injection extends to a permutation of the ambient type.** Given an
injection `e : α → γ`, every permutation `σ` of `α` is realized along `e` by some
`ρ : Equiv.Perm γ`. This is `Equiv.Perm.viaEmbedding` stated in terms of the underlying function
of the injection, which is the form a consumer reindexing along `e` needs. -/
theorem exists_perm_apply_eq {α γ : Type*} {e : α → γ} (he : Function.Injective e)
    (σ : Equiv.Perm α) : ∃ ρ : Equiv.Perm γ, ∀ a, ρ (e a) = e (σ a) :=
  ⟨σ.viaEmbedding ⟨e, he⟩, fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a⟩

/-- **Two permutations along disjoint injections extend to one permutation of the ambient type.**
Given injections `e : α → γ` and `f : β → γ` with disjoint ranges, every pair of permutations
`σ` of `α` and `τ` of `β` is realized by a single `ρ : Equiv.Perm γ` which acts as `σ` along `e`
and as `τ` along `f`. -/
theorem exists_perm_apply_eq_of_disjoint_range {α β γ : Type*} {e : α → γ} {f : β → γ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    ∃ ρ : Equiv.Perm γ, (∀ a, ρ (e a) = e (σ a)) ∧ ∀ b, ρ (f b) = f (τ b) := by
  -- `Function.Embedding.coeFn_mk` is what carries a statement about the bundled embedding
  -- `⟨e, he⟩` over to the function `e` it is built from.
  have hrange_e : Set.range (⟨e, he⟩ : α ↪ γ) = Set.range e := by
    rw [Function.Embedding.coeFn_mk]
  have hrange_f : Set.range (⟨f, hf⟩ : β ↪ γ) = Set.range f := by
    rw [Function.Embedding.coeFn_mk]
  have hone : ∀ a, σ.viaEmbedding ⟨e, he⟩ (e a) = e (σ a) :=
    fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a
  have htwo : ∀ b, τ.viaEmbedding ⟨f, hf⟩ (f b) = f (τ b) :=
    fun b => Equiv.Perm.viaEmbedding_apply (ι := ⟨f, hf⟩) τ b
  refine ⟨σ.viaEmbedding ⟨e, he⟩ * τ.viaEmbedding ⟨f, hf⟩, fun a => ?_, fun b => ?_⟩
  · have hmem : e a ∉ Set.range (⟨f, hf⟩ : β ↪ γ) :=
      hrange_f ▸ Set.disjoint_left.mp hd ⟨a, rfl⟩
    rw [Equiv.Perm.mul_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨f, hf⟩) _ _ hmem, hone]
  · have hmem : f (τ b) ∉ Set.range (⟨e, he⟩ : α ↪ γ) :=
      hrange_e ▸ Set.disjoint_right.mp hd ⟨τ b, rfl⟩
    rw [Equiv.Perm.mul_apply, htwo,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨e, he⟩) _ _ hmem]

end TauCeti
