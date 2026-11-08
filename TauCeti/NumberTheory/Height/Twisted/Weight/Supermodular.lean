/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Weight.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.LinearAlgebra.LinearIndependent.Filtration
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Dimension.Submodule

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort

/-!
# Supermodularity of local subspace weights

The minimum weight of a restricted dual basis can be computed from the dimensions of the
intersections with the common kernels of the low-weight forms. The coefficients of these
dimensions are the nonnegative successive differences of the form weights. Dimension
supermodularity for intersection with a fixed subspace therefore gives supermodularity of
the local weight. The spanning forms may be redundant.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace
  Theorem*, §15, equation (15.4) and Lemma 15.1.
-/

public noncomputable section

open Module Submodule Set

namespace TauCeti

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- There is a restricted dual basis which spans the restrictions of all forms in each
weight sublevel of a finite increasing list of thresholds. -/
theorem exists_localWeightBasis_spanning_sublevels {L : ι → Dual K V}
    (hL : span K (range L) = ⊤) (c : ι → ℝ) (U : Submodule K V)
    {n : ℕ} (a : Fin n → ℝ) (ha : Monotone a) :
    ∃ b ∈ localWeightBases L U, ∀ j,
      span K ((fun i ↦ (L i).comp U.subtype) ''
        {i | i ∈ b ∧ c i ≤ a j}) =
      span K ((fun i ↦ (L i).comp U.subtype) '' {i | c i ≤ a j}) := by
  classical
  let f : ι → Dual K U := fun i ↦ (L i).comp U.subtype
  have hf : span K (range f) = ⊤ := by
    have heq : range f = U.subtype.dualMap '' range L := by
      exact Set.range_comp U.subtype.dualMap L
    rw [heq, ← LinearMap.map_span, hL, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.dualMap_surjective_of_injective U.injective_subtype
  obtain ⟨b, -, hbi, hbsp, hb⟩ := exists_linearIndepOn_inter_span_eq (K := K) f
    (fun j ↦ {i | c i ≤ a j}) (fun j k hjk i hi ↦ hi.trans (ha hjk))
    univ (fun _ ↦ subset_univ _)
  refine ⟨b.toFinset, mem_localWeightBases.mpr ⟨?_, ?_⟩, ?_⟩
  · have hbi' : LinearIndepOn K f (b.toFinset : Set ι) := by
      rwa [Set.coe_toFinset]
    simpa only [Finset.coe_sort_coe, f] using hbi'.linearIndependent
  · have hset : range (fun i : b.toFinset ↦ f i) = f '' (b.toFinset : Set ι) :=
      (Set.image_eq_range _ _).symm
    have hspan : span K (range (fun i : b.toFinset ↦ f i)) = ⊤ := by
      rw [hset, Set.coe_toFinset, hbsp, image_univ, hf]
    exact hspan
  · intro j
    simpa only [Set.mem_toFinset, Set.ofPred_and, Set.ofPred_mem_eq, f] using hb j

private theorem localWeightBasis_card_filter {L : ι → Dual K V} {U : Submodule K V}
    {b : Finset ι} (hb : b ∈ localWeightBases L U) (c : ι → ℝ) (r : ℝ) :
    (b.filter (fun i ↦ r < c i)).card +
      finrank K (span K ((fun i ↦ (L i).comp U.subtype) ''
        {i | i ∈ b ∧ c i ≤ r})) = finrank K U := by
  classical
  let t := b.filter fun i ↦ c i ≤ r
  have ht : t ⊆ b := Finset.filter_subset _ _
  have hli : LinearIndependent K (fun i : t ↦ (L i).comp U.subtype) :=
    (mem_localWeightBases.mp hb).1.comp
      (fun i : t ↦ (⟨i, ht i.2⟩ : b)) (fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
  have heq : {i | i ∈ b ∧ c i ≤ r} = (t : Set ι) := by ext i; simp [t]
  have hset : range (fun i : t ↦ (L i).comp U.subtype) =
      (fun i ↦ (L i).comp U.subtype) '' (t : Set ι) := by
    simpa only [Finset.coe_sort_coe] using
      (Set.image_eq_range (fun i ↦ (L i).comp U.subtype) (t : Set ι)).symm
  rw [heq, ← hset, finrank_span_eq_card hli, Fintype.card_coe]
  have h := Finset.card_filter_add_card_filter_not (s := b) (fun i ↦ c i ≤ r)
  rw [card_eq_finrank_of_mem_localWeightBases hb] at h
  simpa only [not_le, add_comm, t] using h

/-- Every restricted dual basis has at least as many forms of weight above `r` as the dimension
of the intersection of `U` with the common kernel of the forms of weight at most `r`. -/
private theorem finrank_inf_iInf_ker_le_card_filter [Module.Finite K V] {L : ι → Dual K V}
    {U : Submodule K V} {b : Finset ι} (hb : b ∈ localWeightBases L U) (c : ι → ℝ) (r : ℝ) :
    finrank K ↥(U ⊓ ⨅ i ∈ {i | c i ≤ r}, LinearMap.ker (L i)) ≤
      (b.filter fun i ↦ r < c i).card := by
  have hcard := localWeightBasis_card_filter hb c r
  have hsubset : {i | i ∈ b ∧ c i ≤ r} ⊆ {i | c i ≤ r} := fun _ hi ↦ hi.2
  have hspanle : span K ((fun i ↦ (L i).comp U.subtype) '' {i | i ∈ b ∧ c i ≤ r}) ≤
      span K ((fun i ↦ (L i).comp U.subtype) '' {i | c i ≤ r}) :=
    span_mono (image_mono hsubset)
  have hle := Submodule.finrank_mono hspanle
  have hj := Dual.finrank_span_restrict_add_finrank_inf_iInf_ker L U {i | c i ≤ r}
  omega

/-- When a finite strictly increasing list contains all form weights, the local weight is a
linear combination of common-kernel intersection dimensions, with nonnegative successive gaps.
This is equation (15.4) of Evertse--Ferretti, allowing redundant spanning forms. -/
theorem localWeight_eq_sum_finrank_inf_iInf_ker {L : ι → Dual K V}
    (hL : span K (range L) = ⊤) (c : ι → ℝ) (U : Submodule K V)
    {n : ℕ} (a : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (hc : range c ⊆ range a) :
    localWeight L c U = a 0 * finrank K U +
      ∑ j : Fin n, (a j.succ - a j.castSucc) *
        finrank K ↥(U ⊓ ⨅ i ∈ {i | c i ≤ a j.castSucc}, LinearMap.ker (L i)) := by
  classical
  have : Module.Finite K (Dual K V) := Module.Finite.of_fg_top
    ⟨Finset.univ.image L, by simpa using hL⟩
  have : Module.Finite K V := (Module.finite_dual_iff K).mp inferInstance
  have hgap (j : Fin n) : 0 ≤ a j.succ - a j.castSucc :=
    sub_nonneg.mpr (ha.monotone Fin.castSucc_lt_succ.le)
  have hrank (j : Fin n) :=
    Dual.finrank_span_restrict_add_finrank_inf_iInf_ker L U
      {i | c i ≤ a j.castSucc}
  have hsum := fun b ↦
    sum_eq_mul_card_add_sum_gap_mul_card_filter ha b (fun i _ ↦ hc (mem_range_self i))
  apply le_antisymm
  -- A sublevel-adapted basis attains every lower bound simultaneously.
  · obtain ⟨b, hb, hspan⟩ := exists_localWeightBasis_spanning_sublevels hL c U
      (fun j : Fin n ↦ a j.castSucc) (ha.monotone.comp (fun _ _ h ↦ h))
    have hcard (j : Fin n) : (b.filter fun i ↦ a j.castSucc < c i).card =
        finrank K ↥(U ⊓ ⨅ i ∈ {i | c i ≤ a j.castSucc}, LinearMap.ker (L i)) := by
      have h := localWeightBasis_card_filter hb c (a j.castSucc)
      rw [hspan j] at h
      have hj := hrank j
      omega
    calc
      localWeight L c U ≤ ∑ i ∈ b, c i := localWeight_le_sum c hb
      _ = _ := by simp only [hsum, hcard, card_eq_finrank_of_mem_localWeightBases hb]
  · apply (le_localWeight_iff (localWeightBases_nonempty hL U) c _).mpr
    intro b hb
    rw [hsum, card_eq_finrank_of_mem_localWeightBases hb]
    exact add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (finrank_inf_iInf_ker_le_card_filter hb c _)) (hgap j))

/-- Local subspace weight is supermodular for any finite spanning family of forms,
including redundant families and arbitrary real weights. -/
theorem localWeight_inf_add_localWeight_sup {L : ι → Dual K V}
    (hL : span K (range L) = ⊤) (c : ι → ℝ) (U W : Submodule K V) :
    localWeight L c U + localWeight L c W ≤
      localWeight L c (U ⊓ W) + localWeight L c (U ⊔ W) := by
  classical
  have : Module.Finite K (Dual K V) := Module.Finite.of_fg_top
    ⟨Finset.univ.image L, by simpa using hL⟩
  have : Module.Finite K V := (Module.finite_dual_iff K).mp inferInstance
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hc : c = 0 := funext fun i ↦ isEmptyElim i
    simp [hc]
  let s := Finset.univ.image c
  have hs : s.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hs.card_pos)
  let a : Fin (n + 1) → ℝ := s.orderEmbOfFin hn
  have ha : StrictMono a := (s.orderEmbOfFin hn).strictMono
  have hc : range c ⊆ range a := by
    rw [Finset.range_orderEmbOfFin s hn]
    rintro _ ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hdim : (finrank K U : ℝ) + finrank K W =
      finrank K ↥(U ⊓ W) + finrank K ↥(U ⊔ W) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    exact_mod_cast (by omega : finrank K U + finrank K W =
      finrank K ↥(U ⊓ W) + finrank K ↥(U ⊔ W))
  let H (j : Fin n) := ⨅ i ∈ {i | c i ≤ a j.castSucc}, LinearMap.ker (L i)
  have hker (j : Fin n) : (finrank K ↥(U ⊓ H j) : ℝ) + finrank K ↥(W ⊓ H j) ≤
      finrank K ↥((U ⊓ W) ⊓ H j) + finrank K ↥((U ⊔ W) ⊓ H j) := by
    exact_mod_cast Submodule.finrank_inf_add_finrank_inf_le U W (H j)
  have hgap (j : Fin n) : 0 ≤ a j.succ - a j.castSucc :=
    sub_nonneg.mpr (ha.monotone Fin.castSucc_lt_succ.le)
  simp_rw [localWeight_eq_sum_finrank_inf_iInf_ker hL c _ a ha hc]
  calc
    _ = a 0 * ((finrank K U : ℝ) + finrank K W) +
        ∑ j : Fin n, (a j.succ - a j.castSucc) *
          ((finrank K ↥(U ⊓ H j) : ℝ) + finrank K ↥(W ⊓ H j)) := by
      simp only [mul_add, Finset.sum_add_distrib, H]
      ring
    _ ≤ a 0 * ((finrank K ↥(U ⊓ W) : ℝ) + finrank K ↥(U ⊔ W)) +
        ∑ j : Fin n, (a j.succ - a j.castSucc) *
          ((finrank K ↥((U ⊓ W) ⊓ H j) : ℝ) + finrank K ↥((U ⊔ W) ⊓ H j)) := by
      rw [hdim]
      exact add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hker j) (hgap j))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, H]
      ring

end TauCeti
