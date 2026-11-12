/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Stabilizer.Sift

/-!
# Certified membership by sifting

A successful sift already expresses an element as a product of transversal elements. A failed
sift, however, proves nonmembership only when those transversals cover the basic orbits and the
terminal stabilizer is trivial. This file proves both directions for the executable
`TauCeti.sift`, first for complete transversals along a base and then from the finite checks
`TauCeti.transversalCheck` and `TauCeti.siftCheck`.

The finite checks certify completeness, not just soundness: the certified group order equals the
product of the transversal lengths, so every basic-orbit lower bound must be an equality.
Neither finiteness of the ambient group nor faithfulness of its action is required.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Springer, 1996, §1.4.
* Á. Seress, *Permutation Group Algorithms*, Cambridge University Press, 2003, §4.1–§4.2.
-/

public section

open MulAction

namespace Subgroup

variable {G α : Type*} [Group G] [MulAction G α] [DecidableEq G] [DecidableEq α]
  {H : Subgroup G} {b : ℕ → α} {T : ℕ → List G} {k : ℕ}

/-- With complete transversals along a base, a sift starting from a partial product succeeds
exactly when its residue belongs to the corresponding stabilizer. No distinctness assumption
on the transversals is needed. -/
theorem sift_eq_true_iff_inv_mul_mem_stabilizerChain
    (hk : H.stabilizerChain b k = ⊥)
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hcover : ∀ i < k, orbit (H.stabilizerChain b i) (b i) ⊆
      (· • b i) '' {r | r ∈ T i}) {i : ℕ} (hi : i ≤ k) (p g : G) :
    TauCeti.sift b T i (k - i) p g = true ↔ p⁻¹ * g ∈ H.stabilizerChain b i := by
  suffices ∀ n i, i + n = k → ∀ p g : G,
      TauCeti.sift b T i n p g = true ↔ p⁻¹ * g ∈ H.stabilizerChain b i from
    this (k - i) i (by omega) p g
  intro n
  induction n with
  | zero =>
    intro i hik p g
    have hik' : i = k := by omega
    simp [hik', hk, inv_mul_eq_one, eq_comm]
  | succ n ih =>
    intro i hik p g
    have hik' : i < k := by omega
    rw [TauCeti.sift_succ]
    cases hf : (T i).find? (fun r ↦ decide ((p * r) • b i = g • b i)) with
    | some r =>
      have hr := List.mem_of_find?_eq_some hf
      have heq : (p * r) • b i = g • b i := by simpa using List.find?_some hf
      have hrb : r • b i = (p⁻¹ * g) • b i := by
        simpa [mul_smul] using congrArg (p⁻¹ • ·) heq
      simpa only [Option.elim_some, ih (i + 1) (by omega), mul_inv_rev, mul_assoc] using
        (inv_mul_mem_stabilizerChain_succ_iff (hT i hik' r hr) hrb)
    | none =>
      simp only [Option.elim_none, Bool.false_eq_true, false_iff]
      intro hres
      obtain ⟨r, hr, heq⟩ := hcover i hik' (mem_orbit (b i) ⟨_, hres⟩)
      have hmatch : (p * r) • b i = g • b i := by
        simpa [mul_smul] using congrArg (p • ·) heq
      have := List.find?_eq_none.mp hf r hr
      simp [hmatch] at this

/-- Complete transversals along a base make the executable sift an exact membership test. -/
theorem sift_eq_true_iff_mem
    (hk : H.stabilizerChain b k = ⊥)
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hcover : ∀ i < k, orbit (H.stabilizerChain b i) (b i) ⊆
      (· • b i) '' {r | r ∈ T i}) (g : G) :
    TauCeti.sift b T 0 k 1 g = true ↔ g ∈ H := by
  simpa using sift_eq_true_iff_inv_mul_mem_stabilizerChain hk hT hcover (Nat.zero_le k) 1 g

/-- Successful sifts under the structured order hypotheses force each listed transversal to
exhaust its actual basic orbit. -/
theorem orbit_stabilizerChain_eq_image_of_sift
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hne : ∀ i < k, T i ≠ []) (hnodup : ∀ i < k, ((T i).map (· • b i)).Nodup)
    (hH : H ≤ closure {r | ∃ i < k, r ∈ T i})
    (hsift : ∀ i < k, ∀ j < k, i ≤ j → ∀ s ∈ T j, ∀ r ∈ T i,
      TauCeti.sift b T i (k - i) 1 (s * r) = true) {i : ℕ} (hi : i < k) :
    orbit (H.stabilizerChain b i) (b i) = (· • b i) '' {r | r ∈ T i} := by
  have hcard := natCard_eq_prod_length_of_sift hT hne hnodup hH hsift
  obtain ⟨hfin, hle, -⟩ := length_le_ncard_orbit_and_natCard_le_of_sift hT hne hnodup hH hsift
  have hprod : ∏ j ∈ Finset.range k, (orbit (H.stabilizerChain b j) (b j)).ncard =
      ∏ j ∈ Finset.range k, (T j).length := by
    rw [H.prod_ncard_orbit_stabilizerChain_eq_card b
      (stabilizerChain_eq_bot_of_sift hT hne hnodup hH hsift), hcard]
  have hlen : (orbit (H.stabilizerChain b i) (b i)).ncard = (T i).length := by
    by_contra hne'
    have hlt := Finset.prod_lt_prod₀
      (fun j hj ↦ List.length_pos_iff.mpr (hne j (Finset.mem_range.mp hj)))
      (fun j hj ↦ hle j (Finset.mem_range.mp hj))
      ⟨i, Finset.mem_range.mpr hi, lt_of_le_of_ne (hle i hi) (Ne.symm hne')⟩
    omega
  have hsub : (· • b i) '' {r | r ∈ T i} ⊆ orbit (H.stabilizerChain b i) (b i) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_orbit_iff.mpr ⟨⟨r, hT i hi r hr⟩, rfl⟩
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ (Finite.finite_mulAction_orbit _)).symm
  have himage : (fun r : G ↦ r • b i) '' {r | r ∈ T i} =
      {x | x ∈ (T i).map (· • b i)} := by
    ext x
    simp
  rw [hlen, himage, ← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (hnodup i hi), List.length_map]

/-- Accepted order checks force every listed transversal to exhaust its actual basic orbit.
The listed elements must belong to `H`; sifting the generators alone only proves an upper bound
and does not certify this membership. -/
theorem orbit_stabilizerChain_eq_image_of_siftCheck {gens : List G}
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H)
    (hH : H ≤ closure {g | g ∈ gens}) (htrans : TauCeti.transversalCheck b T k = true)
    (hgens : gens.all (TauCeti.sift b T 0 k 1) = true)
    (hsift : ∀ i < k, TauCeti.siftCheck b T k i = true) {i : ℕ} (hi : i < k) :
    orbit (H.stabilizerChain b i) (b i) = (· • b i) '' {r | r ∈ T i} :=
  let ⟨h₁, h₂, h₃, h₄, h₅⟩ := hypotheses_of_siftCheck hT hH htrans hgens hsift
  orbit_stabilizerChain_eq_image_of_sift h₁ h₂ h₃ h₄ h₅ hi

/-- The structured sifting hypotheses certify exact subgroup membership, without assuming
completeness of the listed transversals or triviality of the terminal stabilizer in advance. -/
theorem sift_eq_true_iff_mem_of_sift
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hne : ∀ i < k, T i ≠ []) (hnodup : ∀ i < k, ((T i).map (· • b i)).Nodup)
    (hH : H ≤ closure {r | ∃ i < k, r ∈ T i})
    (hsift : ∀ i < k, ∀ j < k, i ≤ j → ∀ s ∈ T j, ∀ r ∈ T i,
      TauCeti.sift b T i (k - i) 1 (s * r) = true) (g : G) :
    TauCeti.sift b T 0 k 1 g = true ↔ g ∈ H :=
  sift_eq_true_iff_mem (stabilizerChain_eq_bot_of_sift hT hne hnodup hH hsift) hT
    (fun _ hi ↦ (orbit_stabilizerChain_eq_image_of_sift hT hne hnodup hH hsift hi).subset) g

/-- Finite transversal and sifting checks certify both acceptance and rejection of membership
in the actual subgroup, not merely in a permutation image of it. -/
theorem sift_eq_true_iff_mem_of_siftCheck {gens : List G}
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H)
    (hH : H ≤ closure {g | g ∈ gens}) (htrans : TauCeti.transversalCheck b T k = true)
    (hgens : gens.all (TauCeti.sift b T 0 k 1) = true)
    (hsift : ∀ i < k, TauCeti.siftCheck b T k i = true) (g : G) :
    TauCeti.sift b T 0 k 1 g = true ↔ g ∈ H :=
  let ⟨h₁, h₂, h₃, h₄, h₅⟩ := hypotheses_of_siftCheck hT hH htrans hgens hsift
  sift_eq_true_iff_mem_of_sift h₁ h₂ h₃ h₄ h₅ g

end Subgroup
