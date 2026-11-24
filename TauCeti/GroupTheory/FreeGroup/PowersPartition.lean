/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Group
public import TauCeti.GroupTheory.FreeGroup.StartsWith

/-!
# The Powers partition property of free groups

A group `Γ` has the *Powers property* (de la Harpe, Definition 9) when for every finite set `F`
of nontrivial elements and every `N` there are a partition `Γ = C ⊔ D` and elements
`γ₁, …, γ_N` such that `f • C` is disjoint from `C` for every `f ∈ F` and the translates `γⱼ • D`
are pairwise disjoint. It is the combinatorial input to Powers's averaging argument for the
simplicity and the unique trace of the reduced group C⋆-algebra.

This file proves that a free group whose type of generators has two distinct elements `a ≠ b` has
this property, at arbitrary cardinality of the generators, by a direct argument on reduced words.
Let `L` exceed the word length of every element of `F` and put `w = a b^L`. Every element `f` of
`F` factors as `b^k f'` with `f'` not beginning with `b` or `b⁻¹` and `|k| < L`, so the middle
factor of `w f w⁻¹ = a (b^L f b^{-L}) a⁻¹` begins with `b` or `b⁻¹`; so does its inverse, the
middle factor for `f⁻¹`. Let `B` be the set of elements whose reduced word begins with `b` or
`b⁻¹`. Then left multiplication by `w f w⁻¹` maps `B` into the elements beginning with `a`, which
lie outside `B`. For distinct `i, j : ℕ` the sets `b^i • Bᶜ` and `b^j • Bᶜ` are disjoint, since
`b^(j - i)` maps `Bᶜ` into `B`. Transporting along `w`, the sets `C = w⁻¹ • B` and `D = w⁻¹ • Bᶜ`
with `γⱼ = b^j w` form the required partition.

## Main results

* `FreeGroup.exists_powers_partition`: the Powers partition property of a free group on a type of
  generators with two distinct elements.

## References

* R. T. Powers, *Simplicity of the C*-algebra associated with the free group on two generators*,
  Duke Math. J. 42 (1975), 151–156.
* P. de la Harpe, *On simplicity of reduced C*-algebras of groups*, Bull. Lond. Math. Soc. 39
  (2007), 1–26, Definition 9 and Corollary 12(i).
-/

public section

namespace FreeGroup

variable {α : Type*}

section Partition

variable [DecidableEq α] {a b : α}

/-- Conjugating a nontrivial element `f` by a power `b ^ L` with `L` larger than the word length of
`f` gives an element beginning with `b` or `b⁻¹`. -/
private theorem exists_zpow_mul_mul_zpow_mem_startsWith {f : FreeGroup α} (hf : f ≠ 1) {L : ℕ}
    (hL : norm f < L) : ∃ s, of b ^ (L : ℤ) * f * of b ^ (-(L : ℤ)) ∈ startsWith (b, s) := by
  obtain ⟨k, f', hf', rfl⟩ := exists_eq_of_zpow_mul b f
  have hk : k.natAbs < L := by
    rw [norm_of_zpow_mul (hf' _)] at hL
    omega
  by_cases h1 : f' = 1
  · subst h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hf
    have h : of b ^ (L : ℤ) * (of b ^ k * 1) * of b ^ (-(L : ℤ)) = of b ^ k * 1 := by group
    rw [h]
    exact ⟨_, of_zpow_mul_mem_startsWith hk0 fun h => startsWith.ne_one _ h rfl⟩
  · have hpos : 0 < (L : ℤ) + k := by omega
    have h : of b ^ (L : ℤ) * (of b ^ k * f') * of b ^ (-(L : ℤ)) =
        of b ^ ((L : ℤ) + k) * (f' * of b ^ (-(L : ℤ))) := by group
    rw [h]
    refine ⟨_, of_zpow_mul_mem_startsWith hpos.ne' ?_⟩
    -- The first letter of `f'` survives in `f' * b ^ (-L)`, and it is not `b⁻¹`.
    obtain ⟨c, l, hcl⟩ := List.exists_cons_of_ne_nil (mt toWord_eq_nil_iff.1 h1)
    have hc : c.1 ≠ b := fun hc =>
      hf' c.2 (mem_startsWith_iff_exists_toWord_eq_cons.2 ⟨l, by rw [hcl, ← hc]⟩)
    have hpre : ¬invRev f'.toWord <+: (of b ^ (-(L : ℤ))).toWord := by
      intro hp
      have hmem := hp.subset (mem_invRev_iff.2 (by simp [hcl]) : (c.1, !c.2) ∈ invRev f'.toWord)
      rw [toWord_of_zpow] at hmem
      exact hc (congrArg Prod.fst (List.eq_of_mem_replicate hmem))
    exact Set.disjoint_left.1 (startsWith.disjoint_iff_ne.2 fun h => hc (congrArg Prod.fst h))
      (mul_mem_startsWith_of_not_invRev_prefix
        (mem_startsWith_iff_exists_toWord_eq_cons.2 ⟨l, hcl⟩) hpre)

/-- If `u` and `u⁻¹` both begin with `b` or `b⁻¹`, then left multiplication by `a u a⁻¹` maps every
element beginning with `b` or `b⁻¹` to an element beginning with `a`. -/
private theorem of_mul_mul_inv_mul_mem_startsWith (hab : a ≠ b) {u y : FreeGroup α}
    (hu : ∃ s, u ∈ startsWith (b, s)) (hu' : ∃ s, u⁻¹ ∈ startsWith (b, s))
    (hy : ∃ s, y ∈ startsWith (b, s)) :
    of a * u * (of a)⁻¹ * y ∈ startsWith (a, true) := by
  obtain ⟨s, hs⟩ := hy
  obtain ⟨s₁, hs₁⟩ := hu
  obtain ⟨s₂, hs₂⟩ := hu'
  have h₁ : (of a)⁻¹ * y ∈ startsWith (a, false) := by
    have hinv : (of a)⁻¹ = mk [(a, false)] := inv_mk_singleton (a, true)
    rw [hinv, mk_singleton_mul_mem_startsWith_iff]
    exact Set.disjoint_right.1 (startsWith.disjoint_iff_ne.2 (by simp [hab])) hs
  have h₂ : ¬invRev u.toWord <+: ((of a)⁻¹ * y).toWord := by
    obtain ⟨l₁, e₁⟩ := mem_startsWith_iff_exists_toWord_eq_cons.1 hs₂
    obtain ⟨l₂, e₂⟩ := mem_startsWith_iff_exists_toWord_eq_cons.1 h₁
    rw [← toWord_inv, e₁, e₂, List.cons_prefix_cons]
    simp [hab.symm]
  have h₃ : u * ((of a)⁻¹ * y) ∈ startsWith (b, s₁) :=
    mul_mem_startsWith_of_not_invRev_prefix hs₁ h₂
  rw [mul_assoc, mul_assoc, of, mk_singleton_mul_mem_startsWith_iff]
  exact Set.disjoint_left.1 (startsWith.disjoint_iff_ne.2 (by simp [hab.symm])) h₃

end Partition

/-- **The Powers partition property of a free group** (de la Harpe, Definition 9 and
Corollary 12(i)). For a free group on a type of generators with two distinct elements `a ≠ b`, of
arbitrary cardinality, every finite set `F` of nontrivial elements and every `N`, there are a
partition `FreeGroup α = C ⊔ D` and elements `γ_1, …, γ_N` such that `f • C` is disjoint from `C`
for every `f ∈ F` and the translates `γ_j • D` are pairwise disjoint. -/
theorem exists_powers_partition (a b : α) (hab : a ≠ b) (F : Finset (FreeGroup α))
    (hF : ∀ f ∈ F, f ≠ 1) (N : ℕ) :
    ∃ (C D : Set (FreeGroup α)) (γ : Fin N → FreeGroup α),
      Disjoint C D ∧ C ∪ D = Set.univ ∧
      (∀ f ∈ F, Disjoint ((fun x : FreeGroup α => f * x) '' C) C) ∧
      Pairwise (fun i j : Fin N =>
        Disjoint ((fun x : FreeGroup α => γ i * x) '' D)
          ((fun x : FreeGroup α => γ j * x) '' D)) := by
  classical
  -- `B` is the set of elements beginning with `b` or `b⁻¹`; `C` and `D` are its preimage and the
  -- preimage of its complement under left multiplication by `w = a b^L`.
  let L := F.sup norm + 1
  let w := of a * of b ^ (L : ℤ)
  let B : Set (FreeGroup α) := {g | ∃ s, g ∈ startsWith (b, s)}
  refine ⟨{x | w * x ∈ B}, {x | w * x ∉ B}, fun j => of b ^ ((j : ℕ) : ℤ) * w,
    Set.disjoint_left.2 fun x hx hx' => hx' hx, Set.eq_univ_of_forall fun x => em _, ?_, ?_⟩
  · intro f hf
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ hfx
    have hL : norm f < L := Nat.lt_succ_of_le (Finset.le_sup hf)
    have hL' : norm f⁻¹ < L := by rwa [norm_inv_eq]
    have hinv : (of b ^ (L : ℤ) * f * of b ^ (-(L : ℤ)))⁻¹ =
        of b ^ (L : ℤ) * f⁻¹ * of b ^ (-(L : ℤ)) := by group
    have key := of_mul_mul_inv_mul_mem_startsWith hab
      (exists_zpow_mul_mul_zpow_mem_startsWith (hF f hf) hL)
      (hinv ▸ exists_zpow_mul_mul_zpow_mem_startsWith (inv_ne_one.2 (hF f hf)) hL') hx
    have h : w * (f * x) =
        of a * (of b ^ (L : ℤ) * f * of b ^ (-(L : ℤ))) * (of a)⁻¹ * (w * x) := by
      simp only [w]
      group
    obtain ⟨s, hs⟩ := hfx
    rw [h] at hs
    exact Set.disjoint_left.1 (startsWith.disjoint_iff_ne.2 (by simp [hab])) key hs
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    simp only at hxy
    apply hx
    have hk : ((j : ℕ) : ℤ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      omega
    have h : w * x = of b ^ (((j : ℕ) : ℤ) - (i : ℕ)) * (w * y) := by
      calc w * x = of b ^ (-((i : ℕ) : ℤ)) * (of b ^ ((i : ℕ) : ℤ) * w * x) := by group
        _ = of b ^ (-((i : ℕ) : ℤ)) * (of b ^ ((j : ℕ) : ℤ) * w * y) := by rw [← hxy]
        _ = of b ^ (((j : ℕ) : ℤ) - (i : ℕ)) * (w * y) := by group
    rw [h]
    exact ⟨_, of_zpow_mul_mem_startsWith hk fun h => hy ⟨_, h⟩⟩

end FreeGroup
