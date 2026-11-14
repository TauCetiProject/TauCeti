/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Scheduled lower-skeleton regularization of triadic complexes

Top regularization of a `Colored3Graph` refines the pair palette of a `TriadicComplex3`, increasing
`pairColorCount` without updating the vertex partition, which can break
`PairSkeleton3.LowerSkeletonRegular F`. Restoring scheduled lower-skeleton regularity while losing
at most `g` in `Colored3Graph.polyadEnergy` is the lower-level step alternated with top
regularization in the strong hypergraph regularity iteration.

Given a `TriadicComplex3 V` with equitable vertex cells,
`TriadicComplex3.exists_lowerSkeletonRegular` applies
`PairColorSystem.exists_equipartition_lowerSkeletonRegular` and relabels `Option (Fin m)` to
`Fin (m + 1)`, yielding a complex `C'` with `C'.pairColorCount = C.pairColorCount + 1`, refining
equitable vertex cells, `C'.skeleton.LowerSkeletonRegular F`, and at most `α |V|²` recolored
ordered vertex pairs modulo an explicit palette embedding. Choosing `α = g / 36` and invoking
`Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring` bounds the polyad energy drop by `g` once
`4 ≤ |V|` (`Colored3Graph.exists_lowerSkeletonRegular_polyadEnergy_sub_le`). Finally,
`TriadicComplex3.exists_vertexCellsControlled_lowerSkeletonRegular` constructs an initial
one-color polyad decomposition with `t₀` equitable vertex cells satisfying `LowerSkeletonRegular F`.

## Main definitions

* `TauCeti.lowerRegularizationPartBound`: upper bound on `#C'.skeleton.vertexPart.parts` when
  regularizing a lower skeleton with polyad energy loss at most `g`.
* `TauCeti.lowerRegularizationBound`: host-size threshold for
  `Colored3Graph.exists_lowerSkeletonRegular_polyadEnergy_sub_le`.

## Main results

* `TauCeti.TriadicComplex3.exists_lowerSkeletonRegular`: scheduled lower-skeleton regularization of
  a triadic complex with edit budget `α |V|²`.
* `TauCeti.Colored3Graph.exists_lowerSkeletonRegular_polyadEnergy_sub_le`: scheduled
  lower-skeleton regularization losing at most `g` in polyad energy.
* `TauCeti.TriadicComplex3.exists_vertexCellsControlled_lowerSkeletonRegular`: initial equitable
  triadic complex with `t₀` vertex cells, one pair color, and `LowerSkeletonRegular F`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.5 and Lemma 3.3.
-/

public section

open Finset

namespace TauCeti

/-- Upper bound on `#C'.skeleton.vertexPart.parts` when regularizing a lower skeleton of `m` pair
colors and `k₀` vertex cells for schedule `F` with polyad energy loss at most `g`. -/
noncomputable def lowerRegularizationPartBound (g : ℝ) (F : ℕ → ℝ) (m k₀ : ℕ) : ℕ :=
  pairRegularApproximationPartBound (g / 36) F m k₀

/-- Unfolding lemma for `TauCeti.lowerRegularizationPartBound`. -/
theorem lowerRegularizationPartBound_def (g : ℝ) (F : ℕ → ℝ) (m k₀ : ℕ) :
    lowerRegularizationPartBound g F m k₀ = pairRegularApproximationPartBound (g / 36) F m k₀ :=
  (rfl)

/-- `lowerRegularizationPartBound g F m` is monotone in the initial cell count `k₀`. -/
theorem monotone_lowerRegularizationPartBound (g : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    Monotone (lowerRegularizationPartBound g F m) :=
  monotone_pairRegularApproximationPartBound (g / 36) F m

/-- Host-size threshold for `Colored3Graph.exists_lowerSkeletonRegular_polyadEnergy_sub_le`
starting from `m` pair colors and `k₀` vertex cells. -/
noncomputable def lowerRegularizationBound (g : ℝ) (F : ℕ → ℝ) (m k₀ : ℕ) : ℕ :=
  max (pairRegularApproximationBound (g / 36) F m k₀) 4

/-- Unfolding lemma for `TauCeti.lowerRegularizationBound`. -/
theorem lowerRegularizationBound_def (g : ℝ) (F : ℕ → ℝ) (m k₀ : ℕ) :
    lowerRegularizationBound g F m k₀ = max (pairRegularApproximationBound (g / 36) F m k₀) 4 :=
  (rfl)

/-- `lowerRegularizationBound g F m` is monotone in `k₀` when `g > 0` and `F > 0`. -/
theorem monotone_lowerRegularizationBound {g : ℝ} (hg : 0 < g) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (m : ℕ) :
    Monotone (lowerRegularizationBound g F m) := fun _ _ hk ↦
  max_le_max_right 4 (monotone_pairRegularApproximationBound (by positivity) hF m hk)

private theorem pow_three_div_four_le_descFactorial {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 / 4 ≤ (n.descFactorial 3 : ℕ) := by
  have hdesc : n.descFactorial 3 = (n - 2) * ((n - 1) * n) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have hn4 : (4 : ℝ) ≤ n := mod_cast hn
  have hprod : (n : ℝ) / 2 * ((n : ℝ) / 2) ≤ ((n : ℝ) - 2) * ((n : ℝ) - 1) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  rw [hdesc, Nat.cast_mul, Nat.cast_mul, hn1, hn2]
  calc (n : ℝ) ^ 3 / 4 = (n : ℝ) / 2 * ((n : ℝ) / 2) * n := by ring
    _ ≤ ((n : ℝ) - 2) * ((n : ℝ) - 1) * n :=
        mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg n)
    _ = ((n : ℝ) - 2) * (((n : ℝ) - 1) * n) := by ring

namespace TriadicComplex3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Scheduled lower-skeleton regularization of a triadic complex.** Given a complex `C` with
equitable vertex cells, an edit-fraction budget `α > 0`, and any positive schedule `F : ℕ → ℝ`,
once `|V|` reaches
`pairRegularApproximationBound α F C.pairColorCount #C.skeleton.vertexPart.parts`, there exist a
complex `C'` and a palette embedding `g : Fin C.pairColorCount ↪ Fin C'.pairColorCount` such that
`C'` has `C.pairColorCount + 1` pair colors, equitable vertex cells refining those of `C`, all
polyads selected, `C'.skeleton.LowerSkeletonRegular F`, and at most `α |V|²` ordered distinct
vertex pairs recolored modulo `g`. -/
theorem exists_lowerSkeletonRegular (C : TriadicComplex3 V)
    (hCeq : C.skeleton.vertexPart.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairRegularApproximationBound α F C.pairColorCount #C.skeleton.vertexPart.parts ≤
      Fintype.card V) :
    ∃ (C' : TriadicComplex3 V) (g : Fin C.pairColorCount ↪ Fin C'.pairColorCount),
      C'.pairColorCount = C.pairColorCount + 1 ∧
        C'.skeleton.vertexPart ≤ C.skeleton.vertexPart ∧
        C'.skeleton.vertexPart.IsEquipartition ∧
        #C.skeleton.vertexPart.parts ≤ #C'.skeleton.vertexPart.parts ∧
        #C'.skeleton.vertexPart.parts ≤
          pairRegularApproximationPartBound α F C.pairColorCount #C.skeleton.vertexPart.parts ∧
        C'.polyads = univ ∧
        C'.skeleton.LowerSkeletonRegular F ∧
        (#{p | C'.skeleton.pairColors.color p ≠ g (C.skeleton.pairColors.color p)} : ℝ) ≤
          α * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, T, hP, hPeq, hPge, hPle, -, hTreg, hTedit⟩ :=
    C.skeleton.pairColors.exists_equipartition_lowerSkeletonRegular C.skeleton.vertexPart hCeq hα
      hF (by simpa only [Fintype.card_fin] using hV)
  let e : Option (Fin C.pairColorCount) ≃ Fin (C.pairColorCount + 1) :=
    (Fintype.equivFin (Option (Fin C.pairColorCount))).trans (finCongr (by simp))
  let C' : TriadicComplex3 V := ⟨C.pairColorCount + 1, (⟨P, T⟩ : PairSkeleton3 _ V).relabel e, univ⟩
  let g : Fin C.pairColorCount ↪ Fin C'.pairColorCount :=
    ⟨fun c ↦ e (some c), e.injective.comp (Option.some_injective _)⟩
  have hC'V : C'.skeleton.vertexPart = P := PairSkeleton3.relabel_vertexPart e
  refine ⟨C', g, rfl, hC'V ▸ hP, hC'V ▸ hPeq, hC'V ▸ hPge,
    hC'V ▸ by simpa only [Fintype.card_fin] using hPle, rfl,
    (PairSkeleton3.lowerSkeletonRegular_relabel_iff e).2 hTreg, ?_⟩
  have hinj : #{p | C'.skeleton.pairColors.color p ≠ g (C.skeleton.pairColors.color p)} ≤
      #{q : V × V |
        T.colorOfPair q.1 q.2 ≠ (C.skeleton.pairColors.colorOfPair q.1 q.2).map some} :=
    card_le_card_of_injOn Subtype.val
      (fun p hp ↦ mem_filter.2 ⟨mem_univ _, by
        have hp' : e (T.color p) ≠ e (some (C.skeleton.pairColors.color p)) := by
          simpa only [C', g, PairSkeleton3.relabel_pairColors, PairColorSystem.relabel_color,
            Function.Embedding.coeFn_mk] using (mem_filter.1 hp).2
        rw [T.colorOfPair_of_ne p.2, C.skeleton.pairColors.colorOfPair_of_ne p.2]
        simpa only [Option.map_some, ne_eq, Option.some_inj] using e.injective.ne_iff.1 hp'⟩)
      Subtype.coe_injective.injOn
  exact (Nat.cast_le.2 hinj).trans (by convert hTedit)

/-- **Initial regular triadic complex.** For any positive schedule `F` and positive cell floor `t₀`,
once `t₀ * (⌊1 / F (t₀ + 1)⌋₊ + 2) ≤ |V|`, there exists a one-color polyad decomposition `C` into
`t₀` equitable vertex cells satisfying `C.VertexCellsControlled t₀` and
`C.skeleton.LowerSkeletonRegular F`. -/
theorem exists_vertexCellsControlled_lowerSkeletonRegular {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    {t₀ : ℕ} (ht₀ : 0 < t₀) (hV : t₀ * (⌊1 / F (t₀ + 1)⌋₊ + 2) ≤ Fintype.card V) :
    ∃ C : TriadicComplex3 V,
      C.pairColorCount = 1 ∧
        #C.skeleton.vertexPart.parts = t₀ ∧
        C.VertexCellsControlled t₀ ∧
        C.polyads = univ ∧
        C.IsPolyadDecomposition ∧
        C.skeleton.LowerSkeletonRegular F := by
  have ht₀V : t₀ ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.le_mul_of_pos_right _ (by positivity)).trans hV
  obtain ⟨P, hPeq, hPcard⟩ := Finpartition.exists_equipartition_card_eq (univ : Finset V)
    ht₀.ne' ht₀V
  let S₀ : PairColorSystem (Fin 1) V := ⟨fun _ ↦ 0, id, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let C : TriadicComplex3 V := ⟨1, ⟨P, S₀⟩, univ⟩
  refine ⟨C, rfl, hPcard, C.vertexCellsControlled_iff.2 ⟨hPeq, hPcard.symm.le⟩, rfl,
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ mem_univ _, ?_⟩
  rw [PairSkeleton3.lowerSkeletonRegular_iff]
  dsimp only [C]
  rw [hPcard, Fintype.card_fin]
  set ε := F (t₀ + 1)
  have hε : 0 < ε := hF (t₀ + 1)
  obtain hε1 | hε1 := le_or_gt 1 ε
  · exact PairSkeleton3.isPairColorRegular_of_one_le hε1
  have hlarge (A : Finset V) (hA : A ∈ P.parts) : 1 < ε * #A := by
    have hdiv : ⌊1 / ε⌋₊ + 2 ≤ #A :=
      ((Nat.le_div_iff_mul_le ht₀).2 ((mul_comm (⌊1 / ε⌋₊ + 2) t₀).le.trans hV)).trans
        (hPcard ▸ card_univ (α := V) ▸ hPeq.average_le_card_part hA)
    have hlt : 1 / ε < #A := (Nat.lt_floor_add_one (1 / ε)).trans_le
      (by exact_mod_cast (Nat.le_succ _).trans hdiv)
    exact (div_lt_iff₀' hε).1 hlt
  have hdens {u v : Finset V} (hu : 1 < #u) (hv : 1 < #v) (c : Fin 1) :
      pairColorDensity S₀ c u v = 1 := by
    obtain ⟨y, hy⟩ := card_pos.1 (zero_lt_one.trans hv)
    obtain ⟨x, hx, hxy⟩ := exists_mem_ne hu y
    have hne : ((u ×ˢ v).filter fun p ↦ p.1 ≠ p.2).Nonempty :=
      ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, hxy⟩⟩
    have hsum := sum_pairColorDensity S₀ u v hne
    rwa [Fintype.sum_unique, Subsingleton.elim default c] at hsum
  rw [PairSkeleton3.isPairColorRegular_iff]
  intro c A hA B hB s _ t _ hs ht
  have hs1 : 1 < #s := by exact_mod_cast (hlarge A hA).trans_le hs
  have ht1 : 1 < #t := by exact_mod_cast (hlarge B hB).trans_le ht
  have hA1 : 1 < #A := by
    exact_mod_cast (hlarge A hA).trans_le (mul_le_of_le_one_left (Nat.cast_nonneg _) hε1.le)
  have hB1 : 1 < #B := by
    exact_mod_cast (hlarge B hB).trans_le (mul_le_of_le_one_left (Nat.cast_nonneg _) hε1.le)
  simp [hdens hs1 ht1 c, hdens hA1 hB1 c, hε.le]

end TriadicComplex3

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]

/-- **Scheduled lower-skeleton regularization with bounded polyad energy loss.** Given a coloring
`H` of the triples of `V`, a complex `C` with equitable vertex cells, an energy-loss budget `g > 0`,
and a positive schedule `F : ℕ → ℝ`, once `|V|` is at least
`lowerRegularizationBound g F C.pairColorCount #C.skeleton.vertexPart.parts`, there exists a
refining complex `C'` with `C.pairColorCount + 1` pair colors, equitable vertex cells bounded by
`lowerRegularizationPartBound`, `C'.skeleton.LowerSkeletonRegular F`, and
`H.polyadEnergy C.skeleton - H.polyadEnergy C'.skeleton ≤ g`. -/
theorem exists_lowerSkeletonRegular_polyadEnergy_sub_le (H : Colored3Graph κ V)
    (C : TriadicComplex3 V) (hCeq : C.skeleton.vertexPart.IsEquipartition)
    {g : ℝ} (hg : 0 < g) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : lowerRegularizationBound g F C.pairColorCount #C.skeleton.vertexPart.parts ≤
      Fintype.card V) :
    ∃ (C' : TriadicComplex3 V) (ι : Fin C.pairColorCount ↪ Fin C'.pairColorCount),
      C'.pairColorCount = C.pairColorCount + 1 ∧
        C'.skeleton.vertexPart ≤ C.skeleton.vertexPart ∧
        C'.skeleton.vertexPart.IsEquipartition ∧
        #C.skeleton.vertexPart.parts ≤ #C'.skeleton.vertexPart.parts ∧
        #C'.skeleton.vertexPart.parts ≤
          lowerRegularizationPartBound g F C.pairColorCount #C.skeleton.vertexPart.parts ∧
        C'.polyads = univ ∧
        C'.skeleton.LowerSkeletonRegular F ∧
        (#{p | C'.skeleton.pairColors.color p ≠ ι (C.skeleton.pairColors.color p)} : ℝ) ≤
          g / 36 * (Fintype.card V : ℝ) ^ 2 ∧
        H.polyadEnergy C.skeleton - H.polyadEnergy C'.skeleton ≤ g := by
  rw [lowerRegularizationBound_def, max_le_iff] at hV
  obtain ⟨C', ι, hcol, hPV, hPeq, hPge, hPle, hpol, hreg, hedit⟩ :=
    C.exists_lowerSkeletonRegular hCeq (by positivity : 0 < g / 36) hF hV.1
  refine ⟨C', ι, hcol, hPV, hPeq, hPge, hPle, hpol, hreg, hedit, ?_⟩
  set n := Fintype.card V
  have hn4 : (4 : ℝ) ≤ n := mod_cast hV.2
  have hden := pow_three_div_four_le_descFactorial hV.2
  have hden_pos : 0 < (n : ℝ) ^ 3 / 4 := by positivity
  have hnum : ((9 * #{p | C'.skeleton.pairColors.color p ≠ ι (C.skeleton.pairColors.color p)} *
        n : ℕ) : ℝ) ≤ g * ((n : ℝ) ^ 3 / 4) := by
    push_cast
    calc 9 * (#{p | C'.skeleton.pairColors.color p ≠ ι (C.skeleton.pairColors.color p)} : ℝ) * n
        ≤ 9 * (g / 36 * (n : ℝ) ^ 2) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hedit (by norm_num))
            (Nat.cast_nonneg n)
      _ = g * ((n : ℝ) ^ 3 / 4) := by ring
  refine (H.polyadEnergy_sub_le_of_pairRecoloring hPV ι).trans ?_
  rw [Finset.filter_congr_decidable]
  calc ((9 * #{p | C'.skeleton.pairColors.color p ≠ ι (C.skeleton.pairColors.color p)} *
          n : ℕ) : ℝ) / (n.descFactorial 3 : ℕ)
      ≤ g * ((n : ℝ) ^ 3 / 4) / ((n : ℝ) ^ 3 / 4) :=
        div_le_div₀ (by positivity) hnum hden_pos hden
    _ = g := mul_div_cancel_right₀ g hden_pos.ne'

end Colored3Graph

end TauCeti
