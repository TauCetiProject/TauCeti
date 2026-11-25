/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
import TauCeti.Combinatorics.Hypergraph.Polyad.Nontransversal
import TauCeti.Combinatorics.Hypergraph.Polyad.Perm
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring.CoarsePassage
import TauCeti.Data.Finset.Piecewise
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Order.Partition.Equipartition

/-!
# Coupled triple recoloring over fine polyads over equitable partitions

Given a coarse triadic complex `C` with at least `48 / ε` equitable vertex cells and a same-cell
fine palette refinement `D` with small polyad energy gap from `C` to `D`, suppose a coloring
`H : Colored3Graph κ V` is `(η, 1)`-top-regular over most polyads of `D`. This file constructs an
`ε`-close recoloring `H'` that is `(δ₁, 1)`-top-regular over most polyads of `C`, coupling directly
on unordered supports over canonical representatives of distinct-cell `S₃`-orbits via
`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`,
`TauCeti.two_mul_add_one_mul_exp_lt_of_le_two_pow`, and
`Finset.exists_piecewise_of_pairwiseDisjoint`, and passing regularity from good fine children via
`TauCeti.Colored3Graph.topRegularOverMostPolyads_of_good_children`.

## Main results

* `TauCeti.Colored3Graph.exists_recoloring_topRegularOverMostPolyads`: coupled recoloring from a
  same-cell fine rank-one top-regular refinement with equitable vertex cells.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V]

section EquipartitionRecoloring

variable [Fintype κ] [DecidableEq κ]

/-- Large, distinct-cell, rank-one top-regular fine polyads recolored in the gluing step. -/
private def IsGoodFinePolyad (H : Colored3Graph κ V) {D : TriadicComplex3 V} (η γ : ℝ) (s : ℕ)
    (Q : Polyad3 D.skeleton) : Prop :=
  Q.HasDistinctCells ∧ γ * (s : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1

omit [Fintype κ] in
private theorem isGoodFinePolyad_perm_iff (H : Colored3Graph κ V) {D : TriadicComplex3 V}
    (η γ : ℝ) (s : ℕ) (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) :
    IsGoodFinePolyad H η γ s (Q.perm σ) ↔ IsGoodFinePolyad H η γ s Q := by
  simp [IsGoodFinePolyad]

/-- Local coupled recoloring on the unordered support of a single good fine polyad `Q`. -/
private theorem exists_local_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s)
    (Q : Polyad3 D.skeleton) (hQ : IsGoodFinePolyad H η γ s Q) :
    ∃ x : Set.powersetCard V 3 → κ,
      (∀ e ∉ Q.unorderedSupport, x e = H.color e) ∧
      (#{e ∈ Q.unorderedSupport | x e ≠ H.color e} : ℝ) ≤
        (∑ c : κ, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support ∧
      ∀ (S : Subpolyad3 Q) (d : κ),
        |(#{e ∈ S.unorderedSupport | x e = d} : ℝ) -
            H.relativeDensity d (Q.coarsen hVeq.le π) * #S.unorderedSupport| ≤
          2 * Fintype.card κ * η * #Q.support := by
  classical
  obtain ⟨hdist, hsize, hreg⟩ := hQ
  have hQpos : (0 : ℝ) < #Q.support := lt_of_lt_of_le (by positivity) hsize
  have hPne : (Q.coarsen hVeq.le π).support.Nonempty :=
    (card_pos.1 (Nat.cast_pos.1 hQpos)).mono
      (Polyad3.support_subset_coarsen hVeq.le π (fun p ↦ (hπ p).symm) Q)
  have hcardΩ : #Q.unorderedSupport = #Q.support := hdist.card_unorderedSupport
  have hIcard : Fintype.card (Subpolyad3 Q) ≤ 2 ^ (12 * s ^ 2) := by
    refine (card_subpolyad3_le_mul_card Q).trans (Nat.pow_le_pow_right two_pos ?_)
    have h0 := hcells Q.c₀ Q.hc₀; have h1 := hcells Q.c₁ Q.hc₁; have h2 := hcells Q.c₂ Q.hc₂
    calc #Q.c₀ * #Q.c₁ + #Q.c₀ * #Q.c₂ + #Q.c₁ * #Q.c₂
        ≤ (2 * s) * (2 * s) + (2 * s) * (2 * s) + (2 * s) * (2 * s) := by gcongr
      _ = 12 * s ^ 2 := by ring
  have hN_bound :
      ((12 * s ^ 2 : ℕ) : ℝ) + Fintype.card κ + 2 ≤ 2 * η ^ 2 * #Q.unorderedSupport := by
    rw [hcardΩ]
    have hs2 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ s := Nat.one_le_cast.2 hs
      nlinarith
    have hreq' : (Fintype.card κ : ℝ) + 14 ≤ 2 * η ^ 2 * γ * s := by
      rwa [div_le_iff₀' (by positivity)] at hs_req
    have h1 : ((12 * s ^ 2 : ℕ) : ℝ) + Fintype.card κ + 2 ≤
        ((Fintype.card κ : ℝ) + 14) * (s : ℝ) ^ 2 := by
      push_cast
      have : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
      nlinarith
    have h2 : ((Fintype.card κ : ℝ) + 14) * (s : ℝ) ^ 2 ≤ 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by
      calc _ ≤ (2 * η ^ 2 * γ * s) * (s : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hreq' (sq_nonneg _)
        _ = 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by ring
    linarith [mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 2 * η ^ 2)]
  have hub : 2 * (Fintype.card (Subpolyad3 Q) + 1 : ℝ) * Fintype.card κ *
      Real.exp (-2 * (η * #Q.support) ^ 2 / #Q.unorderedSupport) < 1 := by
    rw [← hcardΩ]
    exact two_mul_add_one_mul_exp_lt_of_le_two_pow hIcard hN_bound
  have hQcount (c : κ) : (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) =
      (H.relativeDensity c Q : ℝ) * #Q.support := by
    rw [hdist.card_filter_unorderedSupport H c, H.relativeDensity_def]
    exact_mod_cast (H.relDensityOn_mul_card c Q.support).symm
  have hx₀ (S : Subpolyad3 Q) (c : κ) :
      |(#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) -
        (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) / #Q.unorderedSupport *
          #S.unorderedSupport| ≤ η * #Q.support := by
    have hScount : (#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) =
        (H.relDensityOn c S.support : ℝ) * #S.support := by
      rw [S.card_filter_unorderedSupport hdist H c]
      exact_mod_cast (H.relDensityOn_mul_card c S.support).symm
    rw [hScount, hQcount, hcardΩ, S.card_unorderedSupport hdist,
      mul_div_cancel_right₀ _ hQpos.ne', ← sub_mul, abs_mul, Nat.abs_cast]
    exact hreg.abs_relDensityOn_sub_mul_card_le c S
  have hp0 (c : κ) : 0 ≤ (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) :=
    mod_cast H.relativeDensity_nonneg c _
  have hp1 : ∑ c : κ, (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) = 1 :=
    mod_cast H.sum_relativeDensity hPne
  obtain ⟨x, hxout, hxedit, hxdisc⟩ := exists_recoloring_abs_card_filter_sub_mul_card_le
    Q.unorderedSupport H.color hp0 hp1 (fun S : Subpolyad3 Q ↦ S.unorderedSupport)
    (fun S ↦ S.unorderedSupport_subset) (mul_pos hη hQpos) hx₀ hub
  refine ⟨x, hxout, hxedit.trans_eq ?_, fun S d ↦ (hxdisc S d).trans_eq (by ring)⟩
  congr 1
  · congr 1
    refine sum_congr rfl fun c _ ↦ ?_
    rw [hQcount, hcardΩ, ← sub_mul, abs_mul, Nat.abs_cast, mul_comm]
  · ring

omit [Fintype κ] in
/-- Transfer a local subpolyad discrepancy bound on a permuted representative `Q.perm σ` back to
`Q` when `H'` agrees with the local coloring `x` on `(Q.perm σ).unorderedSupport`. -/
private theorem abs_relDensityOn_sub_of_perm_recoloring (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {Q : Polyad3 D.skeleton} (hdist : Q.HasDistinctCells) (hQne : Q.support.Nonempty)
    (σ : Equiv.Perm (Fin 3)) (x : Set.powersetCard V 3 → κ) (S : Subpolyad3 Q) (d : κ) {B : ℝ}
    (hH'_eq : ∀ {e}, e ∈ (Q.perm σ).unorderedSupport → H'.color e = x e)
    (hdisc : |(#{e ∈ (S.perm σ).unorderedSupport | x e = d} : ℝ) -
        H.relativeDensity d ((Q.perm σ).coarsen hVeq.le π) *
          #(S.perm σ).unorderedSupport| ≤ B) :
    |((H'.relDensityOn d S.support : ℝ) -
        H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤ B := by
  have hcount : (#{e ∈ (S.perm σ).unorderedSupport | x e = d} : ℝ) =
      (H'.relDensityOn d S.support : ℝ) * #S.support := by
    have hfilt : {e ∈ (S.perm σ).unorderedSupport | x e = d} =
        {e ∈ S.unorderedSupport | H'.color e = d} := by
      rw [Subpolyad3.unorderedSupport_perm]
      refine filter_congr fun e he ↦ ?_
      have heQ : e ∈ (Q.perm σ).unorderedSupport := by
        rw [Polyad3.unorderedSupport_perm]; exact S.unorderedSupport_subset he
      rw [hH'_eq heQ]
    rw [hfilt, S.card_filter_unorderedSupport hdist H' d]
    exact_mod_cast (H'.relDensityOn_mul_card d S.support).symm
  rw [hcount, Subpolyad3.unorderedSupport_perm, S.card_unorderedSupport hdist,
    Polyad3.coarsen_perm_of_support_nonempty Q hQne σ hVeq.le π (fun p ↦ (hπ p).symm),
    relativeDensity_perm] at hdisc
  rwa [sub_mul]

/-- Summing the local coupled-recoloring edit budget over canonical `S₃`-representatives is at most
one-sixth of the total polyad-density deviation plus `|κ| η |V| (|V| - 1) (|V| - 2)`. -/
private theorem six_mul_sum_local_budget_le (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η : ℝ} (hη : 0 < η) (G : Finset (Polyad3 D.skeleton))
    (horbit : ∀ Q₁ ∈ G, ∀ Q₂ ∈ G, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.perm σ → Q₁ = Q₂ ∧ σ = 1) :
    6 * ∑ Q ∈ G,
        ((∑ c : κ, #Q.support *
            |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
  let Φ : Polyad3 D.skeleton → ℝ := fun Q ↦
    (∑ c : κ, #Q.support *
      |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * #Q.support
  have htotalD : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) =
      (Fintype.card V).descFactorial 3 := by
    exact_mod_cast Polyad3.sum_card_support_eq_descFactorial D.skeleton
  have hΦperm (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) : Φ (Q.perm σ) = Φ Q := by
    obtain hQ0 | hQne := Q.support.eq_empty_or_nonempty
    · simp [Φ, hQ0]
    · simp only [Φ, Polyad3.card_support_perm, relativeDensity_perm,
        Polyad3.coarsen_perm_of_support_nonempty Q hQne σ hVeq.le π (fun p ↦ (hπ p).symm)]
  have hΦ0 (Q : Polyad3 D.skeleton) : 0 ≤ Φ Q :=
    add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (abs_nonneg _)) (by norm_num)) (by positivity)
  calc 6 * ∑ Q ∈ G, Φ Q
      ≤ ∑ Q : Polyad3 D.skeleton, Φ Q :=
        Polyad3.six_mul_sum_le_of_perm_invariant G Φ hΦ0 hΦperm horbit
    _ = (∑ c : κ, ∑ Q : Polyad3 D.skeleton, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
        dsimp only [Φ]; rw [sum_add_distrib, ← sum_div, sum_comm, ← mul_sum, htotalD]

/-- Coupled recoloring on each canonical `S₃`-representative of a good fine polyad, glued across
their pairwise disjoint unordered supports into a global coloring `H'`. -/
private theorem exists_glued_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s) :
    ∃ H' : Colored3Graph κ V,
      (6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3) ∧
      (∀ Q : Polyad3 D.skeleton, IsGoodFinePolyad H η γ s Q →
        ∀ (S : Subpolyad3 Q) (d : κ),
          |((H'.relDensityOn d S.support : ℝ) -
              H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤
            2 * Fintype.card κ * η * #Q.support) := by
  classical
  let eP : D.skeleton.vertexPart.parts ≃ Fin (Fintype.card D.skeleton.vertexPart.parts) :=
    Fintype.equivFin _
  let GoodCanon : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦
    IsGoodFinePolyad H η γ s Q ∧ StrictMono fun i : Fin 3 ↦ eP ⟨Q.cell i, Q.cell_mem_parts i⟩
  have hcanon_orbit : ∀ Q₁ ∈ GoodCanon, ∀ Q₂ ∈ GoodCanon, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.perm σ → Q₁ = Q₂ ∧ σ = 1 := by
    intro Q₁ hQ₁ Q₂ hQ₂ σ h
    obtain ⟨τ, -, huniq⟩ := (mem_filter.1 hQ₁).2.1.1.existsUnique_perm_strictMono eP eP.injective
    have hσ1 : σ = 1 := (huniq σ (by simpa [← h] using (mem_filter.1 hQ₂).2.2)).trans
      (huniq 1 (by simpa using (mem_filter.1 hQ₁).2.2)).symm
    exact ⟨by simpa [hσ1] using h.symm, hσ1⟩
  have hdisj : (GoodCanon : Set (Polyad3 D.skeleton)).PairwiseDisjoint Polyad3.unorderedSupport :=
    fun Q₁ hQ₁ Q₂ hQ₂ hne ↦ Polyad3.disjoint_unorderedSupport_of_forall_ne_perm fun σ h ↦
      hne (hcanon_orbit Q₁ hQ₁ Q₂ hQ₂ σ h).1
  let xQ (Q : Polyad3 D.skeleton) : Set.powersetCard V 3 → κ :=
    if h : IsGoodFinePolyad H η γ s Q then
      (exists_local_coupled_recoloring H π hVeq hπ hs hη hγ hcells hs_req Q h).choose
    else H.color
  have hxQ_spec {Q : Polyad3 D.skeleton} (hQ : IsGoodFinePolyad H η γ s Q) :=
    (exists_local_coupled_recoloring H π hVeq hπ hs hη hγ hcells hs_req Q hQ).choose_spec
  obtain ⟨h, h_eq, h_out, h_count⟩ :=
    Finset.exists_piecewise_of_pairwiseDisjoint GoodCanon Polyad3.unorderedSupport hdisj H.color xQ
  let H' : Colored3Graph κ V := ⟨h⟩
  have hncard : ({e | H.color e ≠ H'.color e}.ncard : ℝ) =
      ∑ Q ∈ GoodCanon, (#{e ∈ Q.unorderedSupport | xQ Q e ≠ H.color e} : ℝ) := by
    have hedit_set : {e | H.color e ≠ H'.color e} =
        (({e ∈ GoodCanon.biUnion Polyad3.unorderedSupport | h e ≠ H.color e} :
          Finset (Set.powersetCard V 3)) : Set _) := by
      ext e
      simp only [Set.mem_ofPred_eq, mem_coe, mem_filter]
      refine ⟨fun hne ↦ ⟨?_, hne.symm⟩, fun ⟨_, hne⟩ ↦ hne.symm⟩
      by_contra hnot
      exact hne (h_out e hnot).symm
    rw [hedit_set, Set.ncard_coe_finset, h_count, Nat.cast_sum]
  refine ⟨H', ?_, ?_⟩
  · refine (le_trans ?_ (six_mul_sum_local_budget_le H π hVeq hπ hη GoodCanon hcanon_orbit))
    rw [hncard]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun Q hQ ↦ ?_) (by norm_num)
    have hQg := (mem_filter.1 hQ).2.1
    simpa only [xQ, dite_eq_left hQg] using (hxQ_spec hQg).2.1
  · intro Q hQ S d
    have hQne : Q.support.Nonempty := card_pos.1 (Nat.cast_pos.1
      (lt_of_lt_of_le (by positivity : (0 : ℝ) < γ * (s : ℝ) ^ 3) hQ.2.1))
    obtain ⟨σ, hσ, -⟩ := hQ.1.existsUnique_perm_strictMono eP eP.injective
    have hQ'good : IsGoodFinePolyad H η γ s (Q.perm σ) :=
      (isGoodFinePolyad_perm_iff H η γ s Q σ).2 hQ
    have hQ'mem : Q.perm σ ∈ GoodCanon := mem_filter.2 ⟨mem_univ _, hQ'good, hσ⟩
    have hdisc := (hxQ_spec hQ'good).2.2 (S.perm σ) d
    exact (abs_relDensityOn_sub_of_perm_recoloring H H' π hVeq hπ hQ.1 hQne σ
      (xQ (Q.perm σ)) S d (fun he ↦ h_eq (Q.perm σ) hQ'mem _ he)
      (by simpa only [xQ, dite_eq_left hQ'good] using hdisc)).trans_eq
      (by rw [Polyad3.card_support_perm])

/-- Derive `H.Approximates3 H' ε` from the glued global edit bound and the polyad energy gap. -/
private theorem approximates3_of_glued_edit_bound (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    {ε η g : ℝ} (hV6 : 6 ≤ Fintype.card V)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hedit : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * (Fintype.card V).descFactorial 3) :
    H.Approximates3 H' ε := by
  have hdev : ∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)| ≤
      (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
    calc _ ≤ ∑ _c : κ, (√g * (Fintype.card V).descFactorial 3) :=
          sum_le_sum fun c _ ↦ H.sum_card_support_mul_abs_relativeDensity_coarsen_le_of_color_eq
            hVeq.le π (fun p ↦ (hπ p).symm) hgap c
      _ = (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
  have hdesc_le : ((Fintype.card V).descFactorial 3 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 3 := by
    have hV_pos_nat : 0 < Fintype.card V := by omega
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV_pos_nat
    positivity
  have h6 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 3 := by
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast Nat.pow_le_two_mul_descFactorial (k := 3) hV6
    have hdesc_pos : (0 : ℝ) < (Fintype.card V).descFactorial 3 := by linarith
    have h1 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        ε * (Fintype.card V).descFactorial 3 := by
      calc 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ)
          ≤ ((Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3) / 2 +
              (Fintype.card κ : ℝ) * η * (Fintype.card V).descFactorial 3 := by linarith
        _ = ((Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η) *
              (Fintype.card V).descFactorial 3 := by ring
        _ ≤ ε * (Fintype.card V).descFactorial 3 := by gcongr
    have hε0 : 0 ≤ ε :=
      nonneg_of_mul_nonneg_left ((by positivity : (0 : ℝ) ≤ 6 * _).trans h1) hdesc_pos
    exact h1.trans (mul_le_mul_of_nonneg_left hdesc_le hε0)
  rw [approximates3_iff, editDiscrepancy3_def]
  push_cast
  rw [Nat.card_eq_fintype_card, div_le_iff₀ hVpos]
  exact h6

omit [Fintype κ] in
open Classical in
/-- Total bad fine polyad mass over distinct-cell coarse polyads is bounded by the irregular fine
mass plus the tiny fine polyad mass. -/
private theorem sum_card_support_bad_fine_le (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {η μ γ : ℝ} (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V) (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hD : D.IsPolyadDecomposition) (htopD : H.TopRegularOverMostPolyads D η μ 1) :
    ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧
          ¬IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q,
        (#Q.support : ℝ) ≤
      (μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ) * (Fintype.card V).descFactorial 3 := by
  set t := #C.skeleton.vertexPart.parts
  set s := Fintype.card V / t
  have hsplit : ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧ ¬IsGoodFinePolyad H η γ s Q, (#Q.support : ℝ) ≤
      (∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1, (#Q.support : ℝ)) +
      (∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3, (#Q.support : ℝ)) := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun Q _ ↦ ?_
    have : (0 : ℝ) ≤ #Q.support := Nat.cast_nonneg _
    split_ifs with hQ hirr htiny <;> try linarith
    exact absurd ⟨(Polyad3.hasDistinctCells_coarsen_iff Q hVeq π).1 hQ.1,
      not_lt.1 htiny, hirr⟩ hQ.2
  have hirrD := htopD.sum_card_support_univ_le hD
  have htinyD : ∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3,
        (#Q.support : ℝ) ≤
      2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by
    have hcardD : (Fintype.card (Polyad3 D.skeleton) : ℝ) ≤
        (t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3 := by
      have h1 := card_polyad3_le D.skeleton; rw [hVeq, Fintype.card_fin] at h1; exact_mod_cast h1
    have hts : (t : ℝ) * s ≤ Fintype.card V := by exact_mod_cast Nat.mul_div_le (Fintype.card V) t
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast Nat.pow_le_two_mul_descFactorial (k := 3) hV6
    calc _ ≤ ∑ _Q : Polyad3 D.skeleton, (γ * (s : ℝ) ^ 3) := by
          rw [sum_filter]
          refine sum_le_sum fun Q _ ↦ ?_
          split_ifs with hlt <;> [exact hlt.le; positivity]
      _ = (Fintype.card (Polyad3 D.skeleton) : ℝ) * (γ * (s : ℝ) ^ 3) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ((t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3) * (γ * (s : ℝ) ^ 3) := by gcongr
      _ = (D.pairColorCount : ℝ) ^ 3 * γ * ((t : ℝ) * s) ^ 3 := by ring
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V : ℝ) ^ 3 := by gcongr
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = 2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by ring
  linarith

/-- **Coupled recoloring from a fine rank-one top-regular refinement.** Given a coarse triadic
complex `C` with at least `48 / ε` equitable vertex cells and a same-cell palette refinement `D`
over which `H` is `(η, 1)`-top-regular outside a `μ`-proportion and has polyad energy gap at most
`g`, if the cell size `s = |V| / #C.skeleton.vertexPart.parts` and parameters satisfy the coupled
recoloring budgets, then there exists a recoloring `H'` with `H.Approximates3 H' ε` and
`H'.TopRegularOverMostPolyads C δ₁ ε 1`. -/
theorem exists_recoloring_topRegularOverMostPolyads
    (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {ε δ₁ η μ γ g : ℝ}
    (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hη : 0 < η) (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V)
    (hCeq : C.skeleton.vertexPart.IsEquipartition)
    (ht : 48 / ε ≤ #C.skeleton.vertexPart.parts)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (htopD : H.TopRegularOverMostPolyads D η μ 1)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hη_reg : 2 * (Fintype.card κ : ℝ) * η ≤ δ₁ ^ 2 / 4)
    (hμ_γ : μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ ≤ 3 * ε * δ₁ ^ 2 / 16)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤
      ((Fintype.card V / #C.skeleton.vertexPart.parts : ℕ) : ℝ)) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' ε ∧ H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
  classical
  have ht_pos : 0 < #C.skeleton.vertexPart.parts :=
    Nat.cast_pos.1 (lt_of_lt_of_le (by positivity) ht)
  have hs1 : 1 ≤ Fintype.card V / #C.skeleton.vertexPart.parts :=
    Nat.div_pos (C.skeleton.vertexPart.card_parts_le_card.trans_eq card_univ) ht_pos
  have hcell_ub : ∀ A ∈ D.skeleton.vertexPart.parts,
      #A ≤ 2 * (Fintype.card V / #C.skeleton.vertexPart.parts) := fun A hA ↦ by
    simpa only [card_univ, hVeq] using hCeq.card_part_le_two_mul_div (hVeq ▸ hA)
  obtain ⟨H', hedit, hdisc⟩ := exists_glued_coupled_recoloring H π hVeq hπ hs1 hη hγ
    hcell_ub hs_req
  refine ⟨H', approximates3_of_glued_edit_bound H H' π hV6 hVeq hπ hgap hη_eps hedit, ?_⟩
  have hrep : ∑ P : Polyad3 C.skeleton with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      (ε / 4) * (Fintype.card V).descFactorial 3 := by
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast Nat.pow_le_two_mul_descFactorial (k := 3) hV6
    have hdiv : 6 / (#C.skeleton.vertexPart.parts : ℝ) ≤ ε / 8 := by
      rw [div_le_iff₀ (Nat.cast_pos.2 ht_pos)]; rw [div_le_iff₀ hε] at ht; linarith
    calc _ ≤ 6 * (Fintype.card V : ℝ) ^ 3 / #C.skeleton.vertexPart.parts :=
          Polyad3.sum_card_support_not_hasDistinctCells_le C.skeleton hCeq ht_pos
      _ = (6 / #C.skeleton.vertexPart.parts) * (Fintype.card V : ℝ) ^ 3 := by ring
      _ ≤ (ε / 8) * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = (ε / 4) * (Fintype.card V).descFactorial 3 := by ring
  have hbad := sum_card_support_bad_fine_le H π hγ hV6 hVeq hD htopD
  have htol : 2 * (2 * (Fintype.card κ : ℝ) * η + δ₁ ^ 2 / 4) ≤ δ₁ ^ 2 := by linarith
  refine topRegularOverMostPolyads_of_good_children
    hC hVeq.le π (fun p ↦ (hπ p).symm) Polyad3.HasDistinctCells
    (IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts))
    hδ₁ (by positivity) (by positivity) hε.le htol
    (fun P Q _ hQP hGQ d S' ↦ hQP ▸ hdisc Q hGQ S' d) hrep hbad fun _ ↦ ?_
  have hdesc0 : (0 : ℝ) ≤ (Fintype.card V).descFactorial 3 := Nat.cast_nonneg _
  have hbad_div :
      (μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ) * (Fintype.card V).descFactorial 3 /
          (δ₁ ^ 2 / 4) ≤
        (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by
    have h1 := (mul_le_mul_of_nonneg_right hμ_γ hdesc0)
    calc _ ≤ (3 * ε * δ₁ ^ 2 / 16) * (Fintype.card V).descFactorial 3 / (δ₁ ^ 2 / 4) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by field_simp [hδ₁.ne']; ring
  linarith

end EquipartitionRecoloring

end Colored3Graph

end TauCeti
