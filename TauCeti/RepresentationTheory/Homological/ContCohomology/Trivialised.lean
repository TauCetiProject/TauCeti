/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

import Mathlib.GroupTheory.Index

/-!
# Cocycles with specified trivialisations on a group action

For a `G`-set `X`, consider a continuous function `z : G → M` together with a function
`f : X → M` satisfying `g • f x = f (g • x) + z g`. The function `z` must vanish on a
specified set `I`. The trivialisation `f` is part of the data, not just an existence
condition. If `X` is nonempty, the compatibility law forces `z` to be a cocycle.

The functor in the coefficient group is left exact. For finite counts, the middle term
is therefore counted by the kernel and the image of the coefficient projection, without
assuming that every trivialised cocycle lifts.

The formulation follows `New.DiscreteModule.trivialisedCocycles` and
`New.DiscreteModule.trivialisedCocycles.card_eq_of_isShortExact` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).
-/

public section

namespace TauCeti.ContCohomology

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- A trivialised cocycle consists of a function on `X` and a continuous function on `G`
vanishing on `I`, related by the trivialisation law. No cocycle condition is imposed when
`X` is empty. -/
def trivialisedCocycles (X : Type*) [MulAction G X] (I : Set G) (M : Type*)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M] :
    AddSubgroup ((X → M) × (G → M)) where
  carrier := {p | Continuous p.2 ∧ (∀ g ∈ I, p.2 g = 0) ∧
    ∀ g x, g • p.1 x = p.1 (g • x) + p.2 g}
  zero_mem' := ⟨continuous_const, by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨hp, hpI, hpX⟩ ⟨hq, hqI, hqX⟩
    refine ⟨hp.add hq, fun g hg ↦ by simp [hpI g hg, hqI g hg], fun g x ↦ ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, smul_add, hpX, hqX]
    abel
  neg_mem' := by
    rintro p ⟨hp, hpI, hpX⟩
    exact ⟨hp.neg, fun g hg ↦ by simp [hpI g hg], fun g x ↦ by simp [hpX, smul_neg, add_comm]⟩

variable {X M N P : Type*} [MulAction G X]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M]
  {I : Set G}

/-- Membership in the group of trivialised cocycles is continuity and vanishing for the
second component, and the trivialisation identity for the two components together. -/
theorem mem_trivialisedCocycles_iff {p : (X → M) × (G → M)} :
    p ∈ trivialisedCocycles X I M ↔ Continuous p.2 ∧ (∀ g ∈ I, p.2 g = 0) ∧
      ∀ g x, g • p.1 x = p.1 (g • x) + p.2 g := (Iff.rfl)

/-- The trivialised cocycles are finite in number, and their count is at most the `k`-th
power of the coefficient group order. This excludes the infinite case of `Nat.card`. -/
def HasFewTrivialisedCocycles (X : Type*) [MulAction G X] (I : Set G) (M : Type*)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M]
    (k : ℕ) : Prop :=
  Nat.card (trivialisedCocycles X I M) ∈ Set.Ioc 0 (Nat.card M ^ k)

/-- A count in the indicated positive interval characterizes having few trivialised cocycles. -/
theorem hasFewTrivialisedCocycles_iff {k : ℕ} : HasFewTrivialisedCocycles X I M k ↔
    0 < Nat.card (trivialisedCocycles X I M) ∧
      Nat.card (trivialisedCocycles X I M) ≤ Nat.card M ^ k := (Iff.rfl)

namespace TrivialisedCocycles

/-- On a nonempty `G`-set, comparing the trivialisation identities for `g`, `h` and `gh`
gives the cocycle identity for the second component. -/
theorem snd_mem_Z1 [Nonempty X] (p : trivialisedCocycles X I M) :
    p.val.2 ∈ Z1 G M := by
  obtain ⟨hc, _, h⟩ := mem_trivialisedCocycles_iff.mp p.property
  obtain ⟨x⟩ := ‹Nonempty X›
  refine mem_Z1_iff.mpr ⟨hc, fun g k ↦ ?_⟩
  have he := (h (g * k) x).symm
  rw [mul_smul g k (p.val.1 x), h k x, smul_add, h g (k • x), add_assoc, mul_smul] at he
  simpa only [add_comm ((p.val.2) g)] using add_left_cancel he

variable [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [DistribMulAction G N]

/-- Apply an equivariant continuous coefficient homomorphism to both components. -/
def map (u : M →+[G] N) (hu : Continuous u) :
    trivialisedCocycles X I M →+ trivialisedCocycles X I N where
  toFun p := ⟨(u ∘ p.val.1, u ∘ p.val.2), mem_trivialisedCocycles_iff.mpr <| by
    obtain ⟨hc, hI, hX⟩ := mem_trivialisedCocycles_iff.mp p.property
    exact ⟨hu.comp hc, fun g hg ↦ by simp [hI g hg],
      fun g x ↦ by simpa only [Function.comp_apply, map_smul, map_add] using congrArg u (hX g x)⟩⟩
  map_zero' := by apply Subtype.ext; ext <;> simp
  map_add' p q := by apply Subtype.ext; ext <;> simp

/-- The coefficient map acts by postcomposition on both components. -/
@[simp] theorem val_map (u : M →+[G] N) (hu : Continuous u) (p : trivialisedCocycles X I M) :
    (map u hu p).val = (u ∘ p.val.1, u ∘ p.val.2) := (rfl)

/-- An injective coefficient map is still injective on trivialised cocycles. -/
theorem map_injective (u : M →+[G] N) (hu : Continuous u) (hi : Function.Injective u) :
    Function.Injective (map (X := X) (I := I) u hu) := by
  intro p q h
  have hv := congrArg Subtype.val h
  rw [val_map, val_map] at hv
  exact Subtype.ext (Prod.ext (funext fun x ↦ hi (congrFun (congrArg Prod.fst hv) x))
    (funext fun g ↦ hi (congrFun (congrArg Prod.snd hv) g)))

/-- The identity coefficient map induces the identity on trivialised cocycles. -/
@[simp] theorem map_id : map (X := X) (I := I) (DistribMulActionHom.id G : M →+[G] M)
    continuous_id = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

variable [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P] [DistribMulAction G P]

/-- Successive changes of coefficients act by the composite coefficient map. -/
@[simp] theorem map_comp (u : M →+[G] N) (v : N →+[G] P) (hu : Continuous u) (hv : Continuous v) :
    map (X := X) (I := I) (v.comp u) (hv.comp hu) = (map v hv).comp (map u hu) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

/-- Trivialised cocycles are left exact in the coefficients: if the first map is a
topological embedding, a pair killed by the second map lifts through the first. -/
theorem map_exact {u : M →+[G] N} {v : N →+[G] P} (hu : Topology.IsEmbedding u)
    (hv : Continuous v) (he : Function.Exact u v) :
    Function.Exact (map (X := X) (I := I) u hu.continuous) (map v hv) := by
  intro p
  constructor
  · intro hp
    have hp' := congrArg Subtype.val hp
    rw [val_map] at hp'
    have h₁ (x : X) : v (p.val.1 x) = 0 := congrFun (congrArg Prod.fst hp') x
    have h₂ (g : G) : v (p.val.2 g) = 0 := congrFun (congrArg Prod.snd hp') g
    choose f hf using fun x ↦ (he (p.val.1 x)).mp (h₁ x)
    choose z hz using fun g ↦ (he (p.val.2 g)).mp (h₂ g)
    obtain ⟨hc, hI, hX⟩ := mem_trivialisedCocycles_iff.mp p.property
    have hcomp : u ∘ z = p.val.2 := funext hz
    refine ⟨⟨(f, z), mem_trivialisedCocycles_iff.mpr ⟨hu.isInducing.continuous_iff.mpr
      (hcomp ▸ hc), fun g hg ↦ hu.injective (by rw [hz, hI g hg, map_zero]), fun g x ↦ ?_⟩⟩, ?_⟩
    · exact hu.injective (by simpa only [map_smul, map_add, hf, hz] using hX g x)
    · exact Subtype.ext ((val_map ..).trans (Prod.ext (funext hf) hcomp))
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    rw [val_map, val_map]
    exact Prod.ext (funext fun _ ↦ (he _).mpr ⟨_, rfl⟩)
      (funext fun _ ↦ (he _).mpr ⟨_, rfl⟩)

/-- The count in the middle term is the count on the left times the order of the image
in the right term. The right coefficient map need not be surjective. -/
theorem natCard_eq_mul_card_range {u : M →+[G] N} {v : N →+[G] P} (hu : Topology.IsEmbedding u)
    (hv : Continuous v) (he : Function.Exact u v) :
    Nat.card (trivialisedCocycles X I N) = Nat.card (trivialisedCocycles X I M) *
      Nat.card (map (X := X) (I := I) v hv).range := by
  have h := map_exact (X := X) (I := I) hu hv he
  have hk : (map (X := X) (I := I) v hv).ker = (map u hu.continuous).range :=
    AddSubgroup.ext fun p ↦ h p
  rw [← AddSubgroup.card_ker_mul_card_range (map v hv), hk,
    Nat.card_congr (AddMonoidHom.ofInjective (map_injective u hu.continuous hu.injective)).toEquiv]

/-- Short exact coefficient sequences preserve upper bounds of the form `|M|^k` on the
number of trivialised cocycles. If the middle bound is attained, both outer bounds are attained
and every pair over the quotient coefficients lifts. -/
theorem few_and_surjective_of_card_eq {u : M →+[G] N} {v : N →+[G] P}
    (hu : Topology.IsEmbedding u) (hv : Continuous v)
    (he : Function.Exact u v) (hs : Function.Surjective v) {k : ℕ}
    (hM : HasFewTrivialisedCocycles X I M k) (hP : HasFewTrivialisedCocycles X I P k) :
    HasFewTrivialisedCocycles X I N k ∧
      (Nat.card (trivialisedCocycles X I N) = Nat.card N ^ k →
        Nat.card (trivialisedCocycles X I M) = Nat.card M ^ k ∧
        Nat.card (trivialisedCocycles X I P) = Nat.card P ^ k ∧
        Function.Surjective (map (X := X) (I := I) v hv)) := by
  obtain ⟨hM₀, hM₁⟩ := hasFewTrivialisedCocycles_iff.mp hM
  obtain ⟨hP₀, hP₁⟩ := hasFewTrivialisedCocycles_iff.mp hP
  have := Nat.finite_of_card_ne_zero hP₀.ne'
  let v' := map (X := X) (I := I) v hv
  have hcount := natCard_eq_mul_card_range (X := X) (I := I) hu hv he
  have hrange := Nat.card_le_card_of_injective (f := v'.range.subtype) Subtype.val_injective
  have hcoeff : Nat.card N = Nat.card M * Nat.card P := by
    have hk : v.toAddMonoidHom.ker = u.toAddMonoidHom.range := AddSubgroup.ext fun n ↦ he n
    rw [← AddSubgroup.card_ker_mul_card_of_surjective (f := v.toAddMonoidHom) hs, hk,
      Nat.card_congr (AddMonoidHom.ofInjective (f := u.toAddMonoidHom) hu.injective).toEquiv]
  have hr₀ : 0 < Nat.card v'.range := Nat.card_pos
  have hbound := hrange.trans hP₁
  refine ⟨hasFewTrivialisedCocycles_iff.mpr ⟨by rw [hcount]; exact Nat.mul_pos hM₀ hr₀, ?_⟩,
    fun hEq ↦ ?_⟩
  · rw [hcoeff, mul_pow, hcount]
    exact Nat.mul_le_mul hM₁ hbound
  · rw [hcoeff, mul_pow, hcount] at hEq
    have hleft : Nat.card (trivialisedCocycles X I M) = Nat.card M ^ k := by
      by_contra! h
      exact ((Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hM₁ h) hr₀).trans_le
        (Nat.mul_le_mul_left _ hbound)).ne hEq
    have hright : Nat.card v'.range = Nat.card P ^ k :=
      Nat.eq_of_mul_eq_mul_left hM₀ (hEq.trans (congrArg (· * Nat.card P ^ k) hleft).symm)
    have hcard : Nat.card v'.range = Nat.card (trivialisedCocycles X I P) := by omega
    refine ⟨hleft, hcard.symm.trans hright, ?_⟩
    have htop : v'.range = ⊤ := v'.range.eq_top_of_card_eq hcard
    exact v'.range_eq_top.mp htop

end TrivialisedCocycles
end TauCeti.ContCohomology
