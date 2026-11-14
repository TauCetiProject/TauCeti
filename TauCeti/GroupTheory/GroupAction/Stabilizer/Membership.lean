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

/-- With complete transversals on the slice `[i, i + n)` and trivial terminal stabilizer,
a sift starting from a partial product succeeds exactly when its residue belongs to the initial
stabilizer. No prefix transversals or distinctness assumption are needed. -/
theorem sift_eq_true_iff_inv_mul_mem_stabilizerChain
    {i n : ℕ} (hn : H.stabilizerChain b (i + n) = ⊥)
    (hT : ∀ j, i ≤ j → j < i + n → ∀ r ∈ T j, r ∈ H.stabilizerChain b j)
    (hcover : ∀ j, i ≤ j → j < i + n → orbit (H.stabilizerChain b j) (b j) ⊆
      (· • b j) '' {r | r ∈ T j}) (p g : G) :
    TauCeti.sift b T i n p g = true ↔ p⁻¹ * g ∈ H.stabilizerChain b i := by
  induction n generalizing i p with
  | zero =>
    rw [Nat.add_zero] at hn
    rw [TauCeti.sift_zero, hn]
    simp [inv_mul_eq_one, eq_comm]
  | succ n ih =>
    have hn' : H.stabilizerChain b (i + 1 + n) = ⊥ := by
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using hn
    have hT' : ∀ j, i + 1 ≤ j → j < i + 1 + n → ∀ r ∈ T j,
        r ∈ H.stabilizerChain b j := fun j hj hj' ↦ hT j (by omega) (by omega)
    have hcover' : ∀ j, i + 1 ≤ j → j < i + 1 + n →
        orbit (H.stabilizerChain b j) (b j) ⊆ (· • b j) '' {r | r ∈ T j} :=
      fun j hj hj' ↦ hcover j (by omega) (by omega)
    rw [TauCeti.sift_succ]
    cases hf : (T i).find? (fun r ↦ decide ((p * r) • b i = g • b i)) with
    | some r =>
      have hr := List.mem_of_find?_eq_some hf
      have heq : (p * r) • b i = g • b i := by simpa using List.find?_some hf
      have hrb : r • b i = (p⁻¹ * g) • b i := by
        simpa [mul_smul] using congrArg (p⁻¹ • ·) heq
      simpa only [Option.elim_some, ih hn' hT' hcover', mul_inv_rev, mul_assoc] using
        (inv_mul_mem_stabilizerChain_succ_iff (hT i le_rfl (by omega) r hr) hrb)
    | none =>
      simp only [Option.elim_none, Bool.false_eq_true, false_iff]
      intro hres
      obtain ⟨r, hr, heq⟩ := hcover i le_rfl (by omega) (mem_orbit (b i) ⟨_, hres⟩)
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
  simpa using sift_eq_true_iff_inv_mul_mem_stabilizerChain (i := 0) (n := k)
    (by simpa using hk) (fun j _ hj ↦ hT j (by simpa using hj))
    (fun j _ hj ↦ hcover j (by simpa using hj)) 1 g

/-- Under the structured sifting hypotheses, each basic orbit has the corresponding
transversal length. -/
theorem ncard_orbit_stabilizerChain_eq_length_of_sift
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hne : ∀ i < k, T i ≠ []) (hnodup : ∀ i < k, ((T i).map (· • b i)).Nodup)
    (hH : H ≤ closure {r | ∃ i < k, r ∈ T i})
    (hsift : ∀ i < k, ∀ j < k, i ≤ j → ∀ s ∈ T j, ∀ r ∈ T i,
      TauCeti.sift b T i (k - i) 1 (s * r) = true) {i : ℕ} (hi : i < k) :
    (orbit (H.stabilizerChain b i) (b i)).ncard = (T i).length := by
  have := finite_of_sift hne hH hsift
  have hcard := natCard_eq_prod_length_of_sift hT hne hnodup hH hsift
  have hle : ∀ j < k, (T j).length ≤ (orbit (H.stabilizerChain b j) (b j)).ncard :=
    fun j hj ↦ length_le_ncard_orbit (hT j hj) (hnodup j hj) (Finite.finite_mulAction_orbit _)
  have hprod : ∏ j ∈ Finset.range k, (orbit (H.stabilizerChain b j) (b j)).ncard =
      ∏ j ∈ Finset.range k, (T j).length := by
    rw [H.prod_ncard_orbit_stabilizerChain_eq_card b
      (stabilizerChain_eq_bot_of_sift hT hne hnodup hH hsift), hcard]
  by_contra hne'
  have hlt := Finset.prod_lt_prod₀
    (fun j hj ↦ List.length_pos_iff.mpr (hne j (Finset.mem_range.mp hj)))
    (fun j hj ↦ hle j (Finset.mem_range.mp hj))
    ⟨i, Finset.mem_range.mpr hi, lt_of_le_of_ne (hle i hi) (Ne.symm hne')⟩
  omega

/-- Successful sifts under the structured order hypotheses force each listed transversal to
exhaust its actual basic orbit. -/
theorem orbit_stabilizerChain_eq_image_of_sift
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H.stabilizerChain b i)
    (hne : ∀ i < k, T i ≠ []) (hnodup : ∀ i < k, ((T i).map (· • b i)).Nodup)
    (hH : H ≤ closure {r | ∃ i < k, r ∈ T i})
    (hsift : ∀ i < k, ∀ j < k, i ≤ j → ∀ s ∈ T j, ∀ r ∈ T i,
      TauCeti.sift b T i (k - i) 1 (s * r) = true) {i : ℕ} (hi : i < k) :
    orbit (H.stabilizerChain b i) (b i) = (· • b i) '' {r | r ∈ T i} := by
  have := finite_of_sift hne hH hsift
  have hlen := ncard_orbit_stabilizerChain_eq_length_of_sift hT hne hnodup hH hsift hi
  have hsub : (· • b i) '' {r | r ∈ T i} ⊆ orbit (H.stabilizerChain b i) (b i) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_orbit_iff.mpr ⟨⟨r, hT i hi r hr⟩, rfl⟩
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ (Finite.finite_mulAction_orbit _)).symm
  simpa [hlen] using (hnodup i hi).length_le_ncard
    ((List.finite_toSet (T i)).image (· • b i)) (by simp)

/-- Accepted order checks force every listed transversal to exhaust its actual basic orbit.
The listed elements must belong to `H`; sifting the generators alone only proves an upper bound
and does not certify this membership. -/
theorem orbit_stabilizerChain_eq_image_of_siftCheck {gens : List G}
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H)
    (hH : H ≤ closure {g | g ∈ gens}) (htrans : TauCeti.transversalCheck b T k = true)
    (hgens : gens.all (TauCeti.sift b T 0 k 1) = true)
    (hsift : ∀ i < k, TauCeti.siftCheck b T k i = true) {i : ℕ} (hi : i < k) :
    orbit (H.stabilizerChain b i) (b i) = (· • b i) '' {r | r ∈ T i} :=
  orbit_stabilizerChain_eq_image_of_sift
    (fun _ hi _ hr ↦ mem_stabilizerChain_of_transversalCheck hT htrans hi hr)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).1)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).2.2)
    (hH.trans (closure_le_closure_of_sift (List.all_eq_true.1 hgens)))
    (fun i hi ↦ TauCeti.siftCheck_eq_true_iff.1 (hsift i hi)) hi

/-- Accepted transversal and sifting checks certify the cardinality of every basic orbit. -/
theorem ncard_orbit_stabilizerChain_eq_length_of_siftCheck {gens : List G}
    (hT : ∀ i < k, ∀ r ∈ T i, r ∈ H)
    (hH : H ≤ closure {g | g ∈ gens}) (htrans : TauCeti.transversalCheck b T k = true)
    (hgens : gens.all (TauCeti.sift b T 0 k 1) = true)
    (hsift : ∀ i < k, TauCeti.siftCheck b T k i = true) {i : ℕ} (hi : i < k) :
    (orbit (H.stabilizerChain b i) (b i)).ncard = (T i).length :=
  ncard_orbit_stabilizerChain_eq_length_of_sift
    (fun _ hi _ hr ↦ mem_stabilizerChain_of_transversalCheck hT htrans hi hr)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).1)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).2.2)
    (hH.trans (closure_le_closure_of_sift (List.all_eq_true.1 hgens)))
    (fun i hi ↦ TauCeti.siftCheck_eq_true_iff.1 (hsift i hi)) hi

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
  sift_eq_true_iff_mem_of_sift
    (fun _ hi _ hr ↦ mem_stabilizerChain_of_transversalCheck hT htrans hi hr)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).1)
    (fun i hi ↦ (TauCeti.transversalCheck_eq_true_iff.1 htrans i hi).2.2)
    (hH.trans (closure_le_closure_of_sift (List.all_eq_true.1 hgens)))
    (fun i hi ↦ TauCeti.siftCheck_eq_true_iff.1 (hsift i hi)) g

end Subgroup
