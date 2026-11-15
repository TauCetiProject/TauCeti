/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability
public import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
public import TauCeti.Combinatorics.Hypergraph.Polyad.Symmetry
public import TauCeti.Combinatorics.Hypergraph.Triadic.TopRegularization
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Order.Partition.Pi
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Strong regular approximation of colored three-uniform hypergraphs

Proves `TauCeti.Colored3Graph.exists_strong_regular_approximation3` with bound
`TauCeti.regularityBound3` (Rödl–Schacht 2007; Tao 2006).
-/

public section

open Finset Finpartition Function Real

namespace TauCeti
private theorem pow_three_le_four_mul_descFactorial {n : ℕ} (hn : 4 ≤ n) : n ^ 3 ≤ 4 *
    n.descFactorial 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn; simp only [Nat.descFactorial_succ,
    Nat.descFactorial_zero, mul_one, Nat.sub_zero, show k + 4 - 1 = k + 3
    by omega, show k + 4 - 2 = k + 2 by omega]
  exact (Nat.le_add_right ((k + 4) ^ 3) (3 * k ^ 3 + 24 * k ^ 2 + 56 * k + 32)).trans_eq (by ring)
private theorem sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] (s t : Finset ι) {f : ι → ℝ} (hf
    : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  linarith [sum_union_inter (s₁ := s) (s₂ := t) (f := f), sum_nonneg (s := s ∩ t) fun x _ ↦ hf x]
private theorem pairColorDensity_relabel {κ κ' V : Type*} (S : PairColorSystem κ V) (e : κ ≃ κ') (c
    : κ') (s t : Finset V) : pairColorDensity (S.relabel e) c s t = pairColorDensity S (e.symm c) s
    t := by
  classical
  rw [pairColorDensity_def, pairColorDensity_def]; congr 3; ext p
  by_cases h : p.1 = p.2 <;> simp [h, Equiv.eq_symm_apply]
private theorem isPairColorRegular_relabel {κ κ' V : Type*} [Fintype V] [DecidableEq V] (S :
    PairSkeleton3 κ V) (e : κ ≃ κ') {ε : ℝ} : (S.relabel e).IsPairColorRegular ε ↔
    S.IsPairColorRegular ε := by
  simp only [PairSkeleton3.isPairColorRegular_iff, PairSkeleton3.relabel_vertexPart,
    PairSkeleton3.relabel_pairColors, pairColorDensity_relabel]
  exact ⟨fun h c ↦ by simpa using h (e c), fun h c ↦ h (e.symm c)⟩
private noncomputable def triadicEps1 (ε : ℝ) : ℝ := min ε 1
private noncomputable def triadicSched1 (F : ℕ → ℝ) (k : ℕ) : ℝ := min 1 ((range (k + 1)).inf'
  nonempty_range_add_one F)
private noncomputable def triadicRank1Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ := triadicSched1 F k
  ^ 2 / (2 : ℝ) ^ R k
private noncomputable def triadicFineH'Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ := triadicRank1Tol F
  R k ^ 2 / 4
private noncomputable def triadicFineTol (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  min (triadicEps1 ε / (24 * ((q₃ : ℝ) + 1))) (triadicFineH'Tol F R k ^ 2 / (8 * ((q₃ : ℝ) + 1)))
private noncomputable def triadicFineMass (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 * triadicEps1 ε / 24
private noncomputable def triadicEnergyGap (q₃ : ℕ) (ε : ℝ) : ℝ := (triadicEps1 ε / (12 * ((q₃ : ℝ)
  + 1))) ^ 2
private noncomputable def triadicPairEdit (q₃ : ℕ) (ε : ℝ) : ℝ := min (1 / 16) (triadicEnergyGap q₃
  ε / 48)
private noncomputable def triadicInitParts (q₃ : ℕ) (ε : ℝ) (t₀ : ℕ) : ℕ := max (max t₀ 1) (⌈8 /
  triadicPairEdit q₃ ε⌉₊ + ⌈96 / triadicEps1 ε⌉₊)
private def triadicCompCap (T M : ℕ) : ℕ := T + M + T ^ 3 * M ^ 3
private noncomputable def triadicFineColorBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (T M : ℕ)
    : ℕ := (range (T + 1)).sup fun t ↦ (range (triadicCompCap T M + 1)).sup fun k ↦
    topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) M
private noncomputable def triadicOuterStep (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (TM : ℕ × ℕ) : ℕ × ℕ :=
  let dMax := triadicFineColorBound q₃ ε F R TM.1 TM.2
  ((range (dMax + 1)).sup fun d ↦ strongPairColorPartBound d (triadicPairEdit q₃ ε)
      (fun k ↦ triadicSched1 F (k + (d + 1))) TM.1, max TM.2 (dMax + 1))
private noncomputable def triadicMaxSizes (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : ℕ × ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let T₀ := strongPairColorPartBound 1 (triadicPairEdit q₃ ε) (fun k ↦ triadicSched1 F (k + 2)) l₀
  (triadicOuterStep q₃ ε F R)^[⌊2 / triadicEnergyGap q₃ ε⌋₊] (T₀, 2)
private noncomputable def triadicFineAlpha (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k t d : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 * triadicEps1 ε / (96 * ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ))
/-- Host-size and complexity bound for strong regular approximation of colored 3-graphs. -/
noncomputable def regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let δp := triadicPairEdit q₃ ε
  let TM := triadicMaxSizes q₃ ε F R t₀
  let Bcoarse := triadicCompCap TM.1 TM.2
  let Dmax := triadicFineColorBound q₃ ε F R TM.1 TM.2
  let hBasic := max Bcoarse (max 4 (l₀ + ⌈96 / triadicEps1 ε⌉₊))
  let hPairInit := strongPairColorHostBound 1 δp (fun k ↦ triadicSched1 F (k + 2)) l₀
  let hPairStep := (range (Dmax + 1)).sup fun d ↦
    strongPairColorHostBound d δp (fun k ↦ triadicSched1 F (k + (d + 1))) TM.1
  let hHoeff := (range (Bcoarse + 1)).sup fun k ↦ ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R k ^ 2
    * (triadicRank1Tol F R k ^ 2 * triadicEps1 ε / (96 * ((TM.1 ^ 3 * Dmax ^ 3 : ℕ) + 1 : ℝ))))⌉₊ +
    1
  max (max hBasic hPairInit) (max hPairStep hHoeff)
private theorem triadicEps1_pos {ε : ℝ} (hε : 0 < ε) : 0 < triadicEps1 ε := lt_min hε zero_lt_one
private theorem triadicEps1_le (ε : ℝ) : triadicEps1 ε ≤ ε := min_le_left _ _
private theorem triadicSched1_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (k : ℕ) : 0 < triadicSched1 F k
  := lt_min zero_lt_one ((lt_inf'_iff nonempty_range_add_one).2 fun m _ ↦ hF m)
private theorem triadicSched1_le (F : ℕ → ℝ) (k : ℕ) : triadicSched1 F k ≤ F k := (min_le_right _
  _).trans (inf'_le F (self_mem_range_succ k))
private theorem triadicRank1Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) : 0 <
    triadicRank1Tol F R k := by have := triadicSched1_pos hF k; rw [triadicRank1Tol]; positivity
private theorem triadicFineH'Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) : 0 <
    triadicFineH'Tol F R k := div_pos (pow_pos (triadicRank1Tol_pos hF R k) 2) (by norm_num)
private theorem triadicFineH'Tol_le_quarter {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    triadicFineH'Tol F R k ≤ 1 / 4 := by
  have h1 : triadicSched1 F k ^ 2 ≤ 1 := (pow_le_pow_left₀ (triadicSched1_pos hF k).le (min_le_left
    _ _) 2).trans_eq (one_pow 2)
  have hr1 : triadicRank1Tol F R k ≤ 1 := by
    rw [triadicRank1Tol]
    exact div_le_one_of_le₀ (h1.trans (one_le_pow₀ (by norm_num))) (by positivity)
  unfold triadicFineH'Tol
  linarith [(pow_le_pow_left₀ (triadicRank1Tol_pos hF R k).le hr1 2).trans_eq (one_pow 2)]
private theorem triadicFineTol_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R
    : ℕ → ℕ) (k : ℕ) : 0 < triadicFineTol q₃ ε F R k := by
  have := triadicEps1_pos hε; have := triadicFineH'Tol_pos hF R k
  unfold triadicFineTol; exact lt_min (by positivity) (by positivity)
private theorem triadicFineMass_pos {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ →
    ℕ) (k : ℕ) : 0 < triadicFineMass ε F R k := by
  have := triadicEps1_pos hε; have := triadicRank1Tol_pos hF R k; unfold triadicFineMass; positivity
private theorem triadicEnergyGap_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < triadicEnergyGap q₃ ε := by
  have := triadicEps1_pos hε; unfold triadicEnergyGap; positivity
private theorem triadicPairEdit_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < triadicPairEdit q₃ ε :=
  lt_min (by norm_num) (div_pos (triadicEnergyGap_pos q₃ hε) (by norm_num))
private theorem topRegularRefinementBound_le_triadicFineColorBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R
    : ℕ → ℕ) {t T m M k : ℕ} (ht : t ≤ T) (hm : m ≤ M) (hk : k ≤ triadicCompCap T M) :
    topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) m ≤
    triadicFineColorBound q₃ ε F R T M := (topRegularRefinementBound_mono t 1 _ _ hm).trans <|
    (Finset.le_sup (f := fun j ↦ topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R j)
    (triadicFineMass ε F R j) M) (mem_range.2 (Nat.lt_succ_of_le hk))).trans <| Finset.le_sup (f :=
    fun t' ↦ (range (triadicCompCap T M + 1)).sup fun j ↦ topRegularRefinementBound t' 1
    (triadicFineTol q₃ ε F R j) (triadicFineMass ε F R j) M) (mem_range.2 (Nat.lt_succ_of_le ht))
private theorem le_triadicOuterStep_fst (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F
    n) (R : ℕ → ℕ) (TM : ℕ × ℕ) : TM.1 ≤ (triadicOuterStep q₃ ε F R TM).1 :=
    (le_strongPairColorPartBound 0 (triadicPairEdit_pos q₃ hε) (fun k ↦ triadicSched1_pos hF (k +
    (0 + 1))) TM.1).trans <| Finset.le_sup (f := fun d ↦ strongPairColorPartBound d
    (triadicPairEdit q₃ ε) (fun k ↦ triadicSched1 F (k + (d + 1))) TM.1) (mem_range.2 (Nat.succ_pos
    _))
private theorem le_triadicOuterStep_snd (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (TM : ℕ × ℕ) :
    TM.2 ≤ (triadicOuterStep q₃ ε F R TM).2 := le_max_left _ _
private theorem basicFloor_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    max 4 (triadicInitParts q₃ ε t₀ + ⌈96 / triadicEps1 ε⌉₊) ≤ regularityBound3 q₃ ε F R t₀ :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

namespace Colored3Graph
variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]
variable (H H' : Colored3Graph κ V) (C : TriadicComplex3 V) in
/-- **Strong regular approximation of a colored three-uniform hypergraph.** -/
def IsStrongRegularApproximation3 (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : Prop :=
  H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
  H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧ C.ComplexityBounded
  (regularityBound3 (Fintype.card κ) ε F R t₀)
/-- Unfolded form of `Colored3Graph.IsStrongRegularApproximation3`. -/
theorem isStrongRegularApproximation3_iff {H H' : Colored3Graph κ V} {C : TriadicComplex3 V} {ε :
    ℝ} {F : ℕ → ℝ} {R : ℕ → ℕ} {t₀ : ℕ} : H.IsStrongRegularApproximation3 H' C ε F R t₀ ↔
    H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
    H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧ C.ComplexityBounded
    (regularityBound3 (Fintype.card κ) ε F R t₀) := Iff.rfl
end Colored3Graph
private structure AdmissibleCoarse {V : Type*} [Fintype V] [DecidableEq V] (ε : ℝ) (F : ℕ → ℝ) (t₀
    q₃ : ℕ) (C : TriadicComplex3 V) : Prop where
  equi : C.skeleton.vertexPart.IsEquipartition
  parts_ge : triadicInitParts q₃ ε t₀ ≤ #C.skeleton.vertexPart.parts
  polyads_univ : C.polyads = univ
  lower_reg : C.skeleton.LowerSkeletonRegular (triadicSched1 F)
private structure StoppedFine {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]
    (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (H : Colored3Graph κ V) (C D : TriadicComplex3 V) (f :
    Fin D.pairColorCount → Fin C.pairColorCount) : Prop where
  d_le : D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts 1
    (triadicFineTol q₃ ε F R C.complexity) (triadicFineMass ε F R C.complexity) C.pairColorCount
  vertex_eq : D.skeleton.vertexPart = C.skeleton.vertexPart
  proj_color : ∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p
  proj_rev : ∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)
  polyads_univ : D.polyads = univ
  top_reg : H.TopRegularOverMostPolyads D (triadicFineTol q₃ ε F R C.complexity) (triadicFineMass ε
    F R C.complexity) 1
  energy_gap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ triadicEnergyGap q₃ ε
private theorem exists_regularized_coarse_step {α V : Type*} [Fintype α] [Fintype V] [DecidableEq
    V] (q₃ t₀ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (S : PairColorSystem α V)
    (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition) (hparts : triadicInitParts q₃ ε
    t₀ ≤ #P.parts) (hhost : strongPairColorHostBound (Fintype.card α) (triadicPairEdit q₃ ε) (fun k
    ↦ triadicSched1 F (k + (Fintype.card α + 1))) #P.parts ≤ Fintype.card V) : ∃ (C' :
    TriadicComplex3 V) (g : α → Fin C'.pairColorCount), Injective g ∧ C'.skeleton.vertexPart ≤ P ∧
    #C'.skeleton.vertexPart.parts ≤ strongPairColorPartBound (Fintype.card α) (triadicPairEdit q₃
    ε) (fun k ↦ triadicSched1 F (k + (Fintype.card α + 1))) #P.parts ∧ C'.pairColorCount =
    Fintype.card α + 1 ∧ AdmissibleCoarse ε F t₀ q₃ C' ∧ (#{p | C'.skeleton.pairColors.color p ≠ g
    (S.color p)} : ℝ) ≤ triadicPairEdit q₃ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set δp := triadicPairEdit q₃ ε; have hδp := triadicPairEdit_pos q₃ hε
  have hl₀_δ : 8 ≤ δp * #P.parts := by
    have hc : 8 / δp ≤ #P.parts := (Nat.le_ceil _).trans <| Nat.cast_le.2 (((Nat.le_add_right _
      _).trans (le_max_right _ _)).trans hparts)
    linarith [(div_le_iff₀ hδp).1 hc]
  obtain ⟨P', T', hP'_le, hP'_equi, hP'_card, -, hT'_reg, hT'_edits⟩ :=
    S.exists_strong_recoloring_isPairColorRegular P hP hδp hl₀_δ (fun k ↦ triadicSched1_pos hF (k +
    (Fintype.card α + 1))) hhost
  let e' : Option α ≃ Fin (Fintype.card (Option α)) := Fintype.equivFin (Option α)
  let C' : TriadicComplex3 V := ⟨Fintype.card (Option α), (⟨P', T'⟩ : PairSkeleton3 (Option α)
    V).relabel e', univ⟩
  have hvp : C'.skeleton.vertexPart = P' := PairSkeleton3.relabel_vertexPart e'
  have hpcc : C'.pairColorCount = Fintype.card α + 1 := Fintype.card_option
  refine ⟨C', fun c ↦ e' (some c), e'.injective.comp (Option.some_injective _), hvp.symm ▸ hP'_le,
    hvp.symm ▸ hP'_card, hpcc, ⟨hvp.symm ▸ hP'_equi, hvp.symm ▸ hparts.trans (card_mono hP'_le),
    rfl, ?_⟩, ?_⟩
  · rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_fin]
    exact (isPairColorRegular_relabel (⟨P', T'⟩ : PairSkeleton3 (Option α) V) e').2
      (by simpa only [hvp, hpcc] using hT'_reg)
  · refine le_trans ?_ hT'_edits; norm_cast; refine card_le_card fun p hp ↦ ?_
    simpa only [mem_filter, mem_univ, true_and, C', PairSkeleton3.relabel_pairColors,
      PairColorSystem.relabel_color, ne_eq, e'.injective.eq_iff] using hp
private theorem exists_stopped_triadic_pair {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V]
    [DecidableEq V] (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R
    : ℕ → ℕ) (t₀ : ℕ) (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) : ∃ (C D :
    TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
    #C.skeleton.vertexPart.parts ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).1 ∧ C.pairColorCount
    ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).2 ∧ AdmissibleCoarse ε F t₀ (Fintype.card κ) C ∧
    StoppedFine (Fintype.card κ) ε F R H C D f := by
  classical
  let q₃ := Fintype.card κ; let n := Fintype.card V; let g_top := triadicEnergyGap q₃ ε
  let δp := triadicPairEdit q₃ ε; have hg_pos := triadicEnergyGap_pos q₃ hε
  have hn4 : 4 ≤ n := (le_max_left 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans
    hV)
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := by
    have := pow_three_le_four_mul_descFactorial hn4; have : 0 < n ^ 3 := pow_pos (by omega) 3
    exact Nat.cast_pos.2 (by omega)
  let step := triadicOuterStep q₃ ε F R; let TM_max := triadicMaxSizes q₃ ε F R t₀
  let Good (C : TriadicComplex3 V) : Prop := ∃ (D : TriadicComplex3 V) (f : Fin D.pairColorCount →
    Fin C.pairColorCount), StoppedFine q₃ ε F R H C D f
  have advance (TM : ℕ × ℕ) (hTM1 : TM.1 ≤ TM_max.1) (hTM2 : TM.2 ≤ TM_max.2) (C : TriadicComplex3
      V) (hC1 : #C.skeleton.vertexPart.parts ≤ TM.1) (hC2 : C.pairColorCount ≤ TM.2) (hC :
      AdmissibleCoarse ε F t₀ q₃ C) : Good C ∨ ∃ C' : TriadicComplex3 V,
      #C'.skeleton.vertexPart.parts ≤ (step TM).1 ∧ C'.pairColorCount ≤ (step TM).2 ∧
      AdmissibleCoarse ε F t₀ q₃ C' ∧ H.polyadEnergy C.skeleton + g_top / 2 < H.polyadEnergy
      C'.skeleton := by
    obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg⟩ := H.exists_topRegularOverMostPolyads
      C.skeleton (triadicFineTol_pos q₃ hε hF R C.complexity) (triadicFineMass_pos hε hF R
      C.complexity) 1
    rw [Fintype.card_fin] at hDcard
    by_cases hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g_top
    · exact Or.inl ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩
    have hCcomp : C.complexity ≤ triadicCompCap TM.1 TM.2 := C.complexity_le.trans
      (by dsimp [triadicCompCap]; gcongr)
    have hd_step := hDcard.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1
      hC2 hCcomp)
    have h1M := hC1.trans hTM1; have h2M := hC2.trans hTM2
    have hCcompM : C.complexity ≤ triadicCompCap TM_max.1 TM_max.2 := C.complexity_le.trans (by
      dsimp [triadicCompCap]; gcongr)
    have hd_max := hDcard.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R h1M
      h2M hCcompM)
    obtain ⟨C', g, hginj, hC'V, hC'card, hC'pcc, hC'adm, hC'edits⟩ :=
      exists_regularized_coarse_step q₃ t₀ hε hF D.skeleton.pairColors C.skeleton.vertexPart
      hC.equi hC.parts_ge (by
          rw [Fintype.card_fin]; exact ((strongPairColorHostBound_mono _ _ _ h1M).trans <|
            (Finset.le_sup (f := fun d' ↦ strongPairColorHostBound d' δp (fun k ↦ triadicSched1 F
            (k + (d' + 1))) TM_max.1) (mem_range.2 (Nat.lt_succ_of_le hd_max))).trans ((le_max_left
            _ _).trans (le_max_right _ _))).trans hV)
    rw [Fintype.card_fin] at hC'card hC'pcc
    have hC'1 : #C'.skeleton.vertexPart.parts ≤ (step TM).1 := (hC'card.trans
      (strongPairColorPartBound_mono _ _ _ hC1)).trans <| Finset.le_sup (f := fun d' ↦
      strongPairColorPartBound d' δp (fun k ↦ triadicSched1 F (k + (d' + 1))) TM.1) (mem_range.2
      (Nat.lt_succ_of_le hd_step))
    have hC'2 : C'.pairColorCount ≤ (step TM).2 := hC'pcc.symm ▸ (Nat.add_le_add_right hd_step
      1).trans (le_max_right _ _)
    have hdrop := H.polyadEnergy_sub_le_of_pairRecoloring (hDV ▸ hC'V) hginj
    have hpow_le : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) := mod_cast
      pow_three_le_four_mul_descFactorial hn4
    have hdrop_le : H.polyadEnergy D.skeleton - H.polyadEnergy C'.skeleton ≤ g_top / 2 := by
      calc H.polyadEnergy D.skeleton - H.polyadEnergy C'.skeleton
          ≤ (6 * (#{p | C'.skeleton.pairColors.color p ≠ g (D.skeleton.pairColors.color p)} : ℝ) *
              n) / (n.descFactorial 3 : ℝ) := by push_cast at hdrop; convert hdrop
        _ ≤ (6 * (δp * (n : ℝ) ^ 2) * n) / (n.descFactorial 3 : ℝ) := by gcongr
        _ ≤ (6 * δp * (4 * (n.descFactorial 3 : ℝ))) / (n.descFactorial 3 : ℝ) :=
            div_le_div_of_nonneg_right (by nlinarith [triadicPairEdit_pos q₃ hε]) hdesc_pos.le
        _ = 24 * δp := by field_simp [hdesc_pos.ne']; ring
        _ ≤ g_top / 2 := by linarith [show δp ≤ g_top / 48 from min_le_right _ _]
    exact Or.inr ⟨C', hC'1, hC'2, hC'adm, by linarith⟩
  let l₀ := triadicInitParts q₃ ε t₀; have hl₀_pos : 0 < l₀ := (le_max_right t₀ 1).trans
    (le_max_left _ _)
  have hl₀_le : l₀ ≤ #(univ : Finset V) := by
    rw [card_univ]; exact (Nat.le_add_right l₀ _).trans ((le_max_right 4 _).trans
      ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV))
  obtain ⟨P_init, hP_init, hcard_init⟩ := Finpartition.exists_equipartition_card_eq (univ : Finset
    V) hl₀_pos.ne' hl₀_le
  obtain ⟨C₀, -, -, -, hC₀1, hC₀2, hC₀, -⟩ := exists_regularized_coarse_step q₃ t₀ hε hF (⟨fun _ ↦
    (), id, fun _ ↦ rfl, fun _ ↦ rfl⟩ : PairColorSystem Unit V) P_init hP_init hcard_init.ge
    (by rw [Fintype.card_unique, hcard_init]; exact ((le_max_right _ _).trans (le_max_left _
        _)).trans hV)
  rw [Fintype.card_unique, hcard_init] at hC₀1; rw [Fintype.card_unique] at hC₀2
  let TM₀ : ℕ × ℕ := (strongPairColorPartBound 1 δp (fun k ↦ triadicSched1 F (k + 2)) l₀, 2)
  let K_rounds := ⌊2 / g_top⌋₊
  have hstep_mono {j k : ℕ} (hj : j ≤ k) : (step^[j] TM₀).1 ≤ (step^[k] TM₀).1 ∧ (step^[j] TM₀).2 ≤
      (step^[k] TM₀).2 := by
    induction k, hj using Nat.le_induction with
    | base => exact ⟨le_rfl, le_rfl⟩
    | succ _ _ ih =>
      rw [Function.iterate_succ_apply']; exact ⟨ih.1.trans (le_triadicOuterStep_fst q₃ hε hF R _),
        ih.2.trans (le_triadicOuterStep_snd q₃ ε F R _)⟩
  have loop (j : ℕ) (hj : j ≤ K_rounds) : (∃ C, #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧
      C.pairColorCount ≤ (step^[j] TM₀).2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧ Good C) ∨ ∃ C,
      #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧ C.pairColorCount ≤ (step^[j] TM₀).2 ∧
      AdmissibleCoarse ε F t₀ q₃ C ∧ (j : ℝ) * (g_top / 2) ≤ H.polyadEnergy C.skeleton := by
    induction j with
    | zero => exact Or.inr ⟨C₀, hC₀1, hC₀2.le, hC₀, by simpa using H.polyadEnergy_nonneg _⟩
    | succ j ih =>
      have hj' := Nat.le_of_succ_le hj
      have hle1 : (step^[j] TM₀).1 ≤ (step^[j + 1] TM₀).1 := by
        rw [Function.iterate_succ_apply']; exact le_triadicOuterStep_fst q₃ hε hF R _
      have hle2 : (step^[j] TM₀).2 ≤ (step^[j + 1] TM₀).2 := by
        rw [Function.iterate_succ_apply']; exact le_triadicOuterStep_snd q₃ ε F R _
      obtain ⟨C, h1, h2, hC, hg⟩ | ⟨C, h1, h2, hC, hE⟩ := ih hj'
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hg⟩
      obtain ⟨hM1, hM2⟩ := hstep_mono hj'
      obtain hg | ⟨C', h1', h2', hC', hE'⟩ := advance (step^[j] TM₀) hM1 hM2 C h1 h2 hC
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hg⟩
      rw [Function.iterate_succ_apply']; exact Or.inr ⟨C', h1', h2', hC', by push_cast; linarith⟩
  have hK_gt : 1 < ((K_rounds : ℝ) + 1) * (g_top / 2) := by
    linarith [(div_lt_iff₀ hg_pos).1 (Nat.lt_floor_add_one (2 / g_top))]
  obtain ⟨C, hC1, hC2, hC, D, f, hD⟩ : ∃ C, #C.skeleton.vertexPart.parts ≤ TM_max.1 ∧
      C.pairColorCount ≤ TM_max.2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧ Good C := by
    obtain hg | ⟨C, hC1, hC2, hC, hE⟩ := loop K_rounds le_rfl; · exact hg
    obtain hg | ⟨C', -, -, -, hE'⟩ := advance TM_max le_rfl le_rfl C hC1 hC2 hC
    · exact ⟨C, hC1, hC2, hC, hg⟩
    linarith [H.polyadEnergy_le_one C'.skeleton]
  exact ⟨C, D, f, hC1, hC2, hC, hD⟩
private theorem fine_subpolyad_discrepancy_bound {η η_H' q₃_real w q_supp dev : ℝ} (hη_H'_pos : 0 <
    η_H') (hη_H'_le : η_H' ≤ 1 / 4) (hq_tol : 2 * q₃_real * η ≤ η_H' ^ 2 / 4) (hw_ge : η_H' *
    q_supp ≤ w) (hq_pos : 0 < q_supp) (hdev_nn : 0 ≤ dev) (hdev : dev * w ≤ 2 * q₃_real * η *
    q_supp) : dev + 2 * q₃_real * η ≤ η_H' := by
  have h1 : (dev * η_H') * q_supp ≤ (η_H' ^ 2 / 4) * q_supp :=
    (by nlinarith [mul_le_mul_of_nonneg_left hw_ge hdev_nn] : (dev * η_H') * q_supp ≤ 2 * q₃_real *
        η * q_supp).trans (mul_le_mul_of_nonneg_right hq_tol hq_pos.le)
  have h2 : dev * η_H' ≤ (η_H' / 4) * η_H' := (by linarith [le_of_mul_le_mul_right h1 hq_pos])
  nlinarith [le_of_mul_le_mul_right h2 hη_H'_pos, sq_nonneg η_H']

namespace Colored3Graph
variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]
/-- **Strong regular approximation of colored three-uniform hypergraphs.** -/
theorem exists_strong_regular_approximation3 (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε) {F : ℕ →
    ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ) (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤
    Fintype.card V) : ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V), C.VertexCellsControlled
    t₀ ∧ H.IsStrongRegularApproximation3 H' C ε F R t₀ := by
  classical
  let q₃ := Fintype.card κ; let n := Fintype.card V; let ε₁ := triadicEps1 ε
  let TM_max := triadicMaxSizes q₃ ε F R t₀
  obtain ⟨C, D, f, hC1, hC2, hC_adm, hstop⟩ := exists_stopped_triadic_pair H hε hF R t₀ hV
  let K := C.complexity; let t := #C.skeleton.vertexPart.parts; let d := D.pairColorCount
  let δ₁ := triadicRank1Tol F R K; let η_H' := triadicFineH'Tol F R K
  let η := triadicFineTol q₃ ε F R K; let α_fine := triadicFineAlpha ε F R K t d
  have hε₁_pos := triadicEps1_pos hε; have hδ₁_pos := triadicRank1Tol_pos hF R K
  have hη_H'_pos := triadicFineH'Tol_pos hF R K; have hη_H'_le := triadicFineH'Tol_le_quarter hF R K
  have hη_pos := triadicFineTol_pos q₃ hε hF R K
  have hα_pos : 0 < α_fine := (by unfold α_fine triadicFineAlpha; positivity)
  have hn4 : 4 ≤ n := (le_max_left 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans
    hV)
  have hn_pos : (0 : ℝ) < n := (by positivity)
  have hpow : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) := mod_cast
    pow_three_le_four_mul_descFactorial hn4
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := (by linarith [pow_pos hn_pos 3])
  have hf_symm (p) : C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p) :=
    (hstop.proj_color p).symm
  have hK_cap : K ≤ triadicCompCap TM_max.1 TM_max.2 := C.complexity_le.trans
    (by dsimp [triadicCompCap]; gcongr)
  have hd_max := hstop.d_le.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1
    hC2 hK_cap)
  have hC_dec : C.IsPolyadDecomposition := C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦
    hC_adm.polyads_univ ▸ mem_univ _
  obtain ⟨H', hApprox, hGoodTrans⟩ : ∃ H' : Colored3Graph κ V, H.Approximates3 H' ε ∧ ∀ Q' :
      Polyad3 D.skeleton, Q'.IsTransversal → α_fine * (n : ℝ) ^ 3 ≤ #Q'.support →
      H.IsTopRegularOverPolyad Q' η 1 → H'.IsTopRegularOverPolyad Q' η_H' 1 ∧ ∀ c : κ,
      |(H'.relativeDensity c Q' : ℝ) - H.relativeDensity c (Q'.coarsen hstop.vertex_eq.le f)| ≤ 2 *
      q₃ * η := by
    have hD_dec : D.IsPolyadDecomposition := D.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦
      hstop.polyads_univ ▸ mem_univ _
    let idx := Fintype.equivFin D.skeleton.vertexPart.parts
    let U_of (Q : Polyad3 D.skeleton) := Q.support.image tripleSet
    let GoodCanon : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦ Q.IsCanonical idx ∧ α_fine *
      (n : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1
    have hGoodCanon_disj : ((GoodCanon : Set (Polyad3 D.skeleton))).PairwiseDisjoint U_of := fun _
      hQ₁ _ hQ₂ hne ↦ Polyad3.disjoint_image_tripleSet_of_isCanonical (mem_filter.1 hQ₁).2.1
      (mem_filter.1 hQ₂).2.1 hne
    let α_min := triadicFineAlpha ε F R K TM_max.1 (triadicFineColorBound q₃ ε F R TM_max.1
      TM_max.2)
    have hα_min_pos : 0 < α_min := (by unfold α_min triadicFineAlpha; positivity)
    have hα_min_le : α_min ≤ α_fine := by
      dsimp only [α_min, α_fine, triadicFineAlpha]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left
        ?_ (by norm_num))
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul (Nat.pow_le_pow_left hC1 3)
        (Nat.pow_le_pow_left hd_max 3)) 1
    have hhost_strict : (q₃ + 6 : ℝ) < 2 * η ^ 2 * α_fine * n := by
      have hceil_n : ⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ + 1 ≤ n := ((Finset.le_sup (f := fun j ↦
        ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R j ^ 2 * (triadicRank1Tol F R j ^ 2 *
        triadicEps1 ε / (96 * ((TM_max.1 ^ 3 * triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2 ^ 3
        : ℕ) + 1 : ℝ))))⌉₊ + 1) (mem_range.2 (Nat.lt_succ_of_le hK_cap))).trans ((le_max_right _
        _).trans (le_max_right _ _))).trans hV
      have hlt : (q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min) < n := (Nat.le_ceil _).trans_lt
        ((by push_cast; linarith : (_ : ℝ) < (⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ + 1 : ℕ)
          ).trans_le (mod_cast hceil_n))
      exact (by linarith [(div_lt_iff₀ (by positivity : 0 < 2 * η ^ 2 * α_min)).1 hlt] :
        (q₃ + 6 : ℝ) < 2 * η ^ 2 * α_min * n).trans_le (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hα_min_le (by positivity)) hn_pos.le)
    have hrec (Q : GoodCanon) :=
      let hQ2 := (mem_filter.1 Q.2).2; let hcard_U :=
        Polyad3.card_image_tripleSet_of_subset hQ2.1.isTransversal Subset.rfl
      let hQ_pos := Nat.cast_pos.1 ((mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ2.2.1)
      exists_coupled_recoloring_abs_card_filter_sub_le (U_of Q.1) H.color (p := fun c ↦
      (H.relativeDensity c (Q.1.coarsen hstop.vertex_eq.le f) : ℝ)) (fun c ↦ mod_cast
      H.relativeDensity_nonneg c _) (mod_cast H.sum_relativeDensity ((Finset.card_pos.1
      hQ_pos).mono (Polyad3.support_subset_coarsen hstop.vertex_eq.le f hf_symm Q.1))) (fun W :
      Subpolyad3 Q.1 ↦ W.support.image tripleSet) (fun W ↦ image_subset_image W.support_subset) (a
      := η * #(U_of Q.1)) (by rw [hcard_U]; exact mul_pos hη_pos (Nat.cast_pos.2 hQ_pos)) (by
        rw [hcard_U]; refine two_mul_add_one_mul_exp_lt_one (card_subpolyad3_le Q.1) ?_
        have hst : (q₃ + 6 : ℝ) * (n : ℝ) ^ 2 < 2 * η ^ 2 * (α_fine * (n : ℝ) ^ 3) :=
          (mul_lt_mul_of_pos_right hhost_strict (pow_pos hn_pos 2)).trans_eq (by ring)
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; linarith only [hst,
          mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) (Nat.one_le_cast.2 (by omega : 1 ≤ n)))
            (add_nonneg (Nat.cast_nonneg q₃) (by norm_num : (0 : ℝ) ≤ 3)),
          mul_le_mul_of_nonneg_left hQ2.2.1 (mul_nonneg zero_le_two (sq_nonneg η))])
    choose xloc _ hxloc_edits hxloc_sub using hrec
    let H' : Colored3Graph κ V := ⟨fun s ↦ if hs : ∃ Q ∈ GoodCanon, s ∈ U_of Q then xloc
      ⟨hs.choose, hs.choose_spec.1⟩ s else H.color s⟩
    have hH'_on {Q : Polyad3 D.skeleton} (hQ : Q ∈ GoodCanon) {s} (hs : s ∈ U_of Q) : H'.color s =
        xloc ⟨Q, hQ⟩ s := by
      have hex : ∃ Q' ∈ GoodCanon, s ∈ U_of Q' := ⟨Q, hQ, hs⟩
      rw [show H'.color s = xloc ⟨hex.choose, hex.choose_spec.1⟩ s from dite_eq_left hex]
      congr 1; apply Subtype.ext; by_contra hne
      exact disjoint_left.1 (hGoodCanon_disj hex.choose_spec.1 hQ hne) hex.choose_spec.2 hs
    have hApprox : H.Approximates3 H' ε := by
      rw [approximates3_iff, editDiscrepancy3_def, Nat.card_eq_fintype_card]
      let Diff : Finset (Set.powersetCard V 3) := univ.filter fun s ↦ H.color s ≠ H'.color s
      rw [show {s : Set.powersetCard V 3 | H.color s ≠ H'.color s}.ncard = #Diff by
        rw [show {s : Set.powersetCard V 3 | H.color s ≠ H'.color s} = (Diff : Set _) by
          ext s; simp [Diff], Set.ncard_coe_finset]]
      push_cast; refine (div_le_iff₀ (pow_pos hn_pos 3)).2 ?_
      have hDiff_sub : Diff ⊆ GoodCanon.biUnion fun Q ↦ {s ∈ U_of Q | H.color s ≠ H'.color s} := by
        intro s hs; have hne := (mem_filter.1 hs).2; by_cases hex : ∃ Q ∈ GoodCanon, s ∈ U_of Q
        · obtain ⟨Q, hQ, hsU⟩ := hex; exact mem_biUnion.2 ⟨Q, hQ, mem_filter.2 ⟨hsU, hne⟩⟩
        · exact (hne (dite_eq_right hex : H'.color s = H.color s).symm).elim
      have hDiff_card : (#Diff : ℝ) ≤ ∑ Q ∈ GoodCanon, (#{s ∈ U_of Q | H.color s ≠ H'.color s} : ℝ)
        := by
        rw [← Nat.cast_sum, ← card_biUnion (fun _ h1 _ h2 hne ↦ (hGoodCanon_disj h1 h2 hne).mono
          (filter_subset _ _) (filter_subset _ _))]
        exact_mod_cast card_le_card hDiff_sub
      have hQ_edit (Q : Polyad3 D.skeleton) (hQ : Q ∈ GoodCanon) : (#{s ∈ U_of Q | H.color s ≠
          H'.color s} : ℝ) ≤ (∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)|) / 2 + q₃ * η * #Q.support := by
        have hQt := (mem_filter.1 hQ).2.1.isTransversal
        rw [show {s ∈ U_of Q | H.color s ≠ H'.color s} = {s ∈ U_of Q | xloc ⟨Q, hQ⟩ s ≠ H.color s}
          from filter_congr fun s hs ↦ by rw [hH'_on hQ hs, ne_comm]]
        refine (hxloc_edits ⟨Q, hQ⟩).trans ?_
        rw [Polyad3.card_image_tripleSet_of_subset hQt Subset.rfl, ← mul_assoc]
        refine add_le_add_left (div_le_div_of_nonneg_right (le_of_eq (sum_congr rfl fun c _ ↦ ?_))
          zero_le_two) _
        rw [Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c hQt Subset.rfl, ←
          relativeDensity_def, ← sub_mul, abs_mul, abs_of_nonneg (a := (#Q.support : ℝ))
          (Nat.cast_nonneg _), mul_comm]
      have hdesc_le : (n.descFactorial 3 : ℝ) ≤ (n : ℝ) ^ 3 := mod_cast Nat.descFactorial_le_pow n 3
      have hsum_supp : (∑ Q ∈ GoodCanon, (#Q.support : ℝ)) ≤ (n : ℝ) ^ 3 := by
        rw [← Nat.cast_sum]; exact (Nat.cast_le.2 ((sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le
          _).trans_eq (by simpa [hstop.polyads_univ] using hD_dec.sum_card_support))).trans
          hdesc_le
      have hsum_dev : (∑ Q ∈ GoodCanon, ∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)|) ≤ q₃ * √(triadicEnergyGap q₃ ε)
            * (n : ℝ) ^ 3 := by
        rw [sum_comm]; refine (sum_le_sum fun c _ ↦ (sum_le_univ_sum_of_nonneg fun Q ↦ by
          positivity).trans (H.sum_card_support_mul_abs_relativeDensity_coarsen_le
          hstop.vertex_eq.le f hf_symm hstop.energy_gap c)).trans ?_
        rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hdesc_le (by positivity)
      have hsum_edit : (#Diff : ℝ) ≤ (q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3) / 2 + q₃ * η *
          (n : ℝ) ^ 3 := (hDiff_card.trans (sum_le_sum hQ_edit)).trans <| by
          rw [sum_add_distrib, ← sum_div, ← mul_sum]; exact add_le_add (div_le_div_of_nonneg_right
            hsum_dev zero_le_two) (mul_le_mul_of_nonneg_left hsum_supp (by positivity))
      have hterm1 : 3 * (q₃ : ℝ) * √(triadicEnergyGap q₃ ε) ≤ ε₁ / 4 := by
        rw [triadicEnergyGap, sqrt_sq (by positivity)]
        exact (mul_le_mul_of_nonneg_right (by linarith : 3 * (q₃ : ℝ) ≤ 3 * (q₃ + 1)) (by
          positivity)).trans_eq (by field_simp; ring)
      have hterm2 : 6 * (q₃ : ℝ) * η ≤ ε₁ / 4 := (mul_le_mul
        (by linarith : 6 * (q₃ : ℝ) ≤ 6 * (q₃ + 1)) (min_le_left _ _) hη_pos.le
        (by positivity)).trans_eq (by field_simp; ring)
      exact
        (by linarith : 6 * (#Diff : ℝ) ≤ (3 * q₃ * √(triadicEnergyGap q₃ ε) + 6 * q₃ * η) * (n : ℝ)
            ^ 3).trans (mul_le_mul_of_nonneg_right ((add_le_add hterm1 hterm2).trans
        ((by linarith : ε₁ / 4 + ε₁ / 4 ≤ ε₁).trans (triadicEps1_le ε))) (by positivity))
    refine ⟨H', hApprox, fun Q' hQ't hQ'l hQ'r ↦ ?_⟩
    obtain ⟨Q, hQ_can, hQ_card, hQ_rel, hQ_crel, hQ_reg⟩ :=
      Polyad3.exists_isCanonical_of_isTransversal (κ := κ) hstop.vertex_eq hstop.proj_rev idx hQ't
    have hQ_large : α_fine * (n : ℝ) ^ 3 ≤ #Q.support := hQ_card.symm ▸ hQ'l
    have hQ_Hreg : H.IsTopRegularOverPolyad Q η 1 := (hQ_reg H η).2 hQ'r
    have hQ : Q ∈ GoodCanon := mem_filter.2 ⟨mem_univ _, hQ_can, hQ_large, hQ_Hreg⟩
    have hQt := hQ_can.isTransversal
    have hQ_pos : (0 : ℝ) < #Q.support := (mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ_large
    have hW_count (W : Subpolyad3 Q) (c : κ) : |(H'.relDensityOn c W.support : ℝ) -
        H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)| * #W.support ≤ 2 * q₃ * η *
        #Q.support := by
      have hcnt : (#{s ∈ W.support.image tripleSet | xloc ⟨Q, hQ⟩ s = c} : ℝ) = (H'.relDensityOn c
          W.support : ℝ) * #W.support := by
        rw [← show {s ∈ W.support.image tripleSet | H'.color s = c} = {s ∈ W.support.image
          tripleSet | xloc ⟨Q, hQ⟩ s = c} from filter_congr fun s hs ↦ by
            rw [hH'_on hQ (image_subset_image W.support_subset hs)]]
        exact Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H' c hQt W.support_subset
      have hsub := hxloc_sub ⟨Q, hQ⟩ W c
      rw [hcnt, Polyad3.card_image_tripleSet_of_subset hQt W.support_subset,
        Polyad3.card_image_tripleSet_of_subset hQt Subset.rfl, ← sub_mul, abs_mul, abs_of_nonneg (a
        := (#W.support : ℝ)) (Nat.cast_nonneg _)] at hsub
      have hsum_H : ∑ c₀ : κ, |(#{s ∈ W.support.image tripleSet | H.color s = c₀} : ℝ) - (#{s ∈
            U_of Q | H.color s = c₀} : ℝ) / #Q.support * #W.support| ≤ q₃ * (η * #Q.support) :=
            (sum_le_sum (g := fun _ : κ ↦ η * (#Q.support : ℝ)) fun c₀ _ ↦ by
          rw [Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c₀ hQt W.support_subset,
            Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c₀ hQt Subset.rfl,
            mul_div_cancel_right₀ _ hQ_pos.ne', ← relativeDensity_def, ← sub_mul, abs_mul,
            abs_of_nonneg (a := (#W.support : ℝ)) (Nat.cast_nonneg _)]
          simpa only [Subpolyad3.unionSupport_unique] using
            hQ_Hreg.abs_relDensityOn_unionSupport_sub_mul_card_le_of_card_le c₀ (Fintype.card_fin
            1).le (fun _ ↦ W)).trans_eq
          (by rw [sum_const, card_univ, nsmul_eq_mul])
      linarith
    have hrel_dev (c : κ) : |(H'.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen
        hstop.vertex_eq.le f)| ≤ 2 * q₃ * η := by
      have hfull := hW_count (Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂) c
      rw [Subpolyad3.support_ofSubcells_cells, ← relativeDensity_def] at hfull
      exact le_of_mul_le_mul_right hfull hQ_pos
    refine ⟨(hQ_reg H' η_H').1 (isTopRegularOverPolyad_one_iff.2 fun c W hW ↦ ?_), fun c ↦ by
      rw [← hQ_rel H' c, ← hQ_crel H c]; exact hrel_dev c⟩
    have hq_tol : 2 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 4 := (mul_le_mul
      (by linarith : 2 * (q₃ : ℝ) ≤ 2 * (q₃ + 1)) (min_le_right _ _) hη_pos.le
      (by positivity)).trans_eq (by field_simp; ring)
    have htri := abs_sub_le (H'.relDensityOn c W.support : ℝ) (H.relativeDensity c (Q.coarsen
      hstop.vertex_eq.le f)) (H'.relativeDensity c Q)
    rw [abs_sub_comm (H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f) : ℝ)] at htri
    linarith [hrel_dev c, fine_subpolyad_discrepancy_bound hη_H'_pos hη_H'_le hq_tol hW hQ_pos
      (abs_nonneg _) (hW_count W c)]
  have hMost : H'.TopRegularOverMostPolyads C (F K) ε (R K) := by
    let BadFine : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦ (#Q.support : ℝ) < α_fine * (n
      : ℝ) ^ 3 ∨ ¬H.IsTopRegularOverPolyad Q η 1
    have hcharge_trans {P : Polyad3 C.skeleton} (hP_trans : P.IsTransversal) (hP_irreg :
        ¬H'.IsTopRegularOverPolyad P δ₁ 1) : (δ₁ ^ 2 / 2) * #P.support ≤ 3 * ∑ Q ∈ BadFine with
        Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ) := by
      by_contra! hlt
      refine hP_irreg (H'.isTopRegularOverPolyad_of_sum_coarsen_le hstop.vertex_eq.le f hf_symm
        hη_H'_pos.le hδ₁_pos (θ := (3 / 4) * δ₁ ^ 2) (by dsimp [η_H', triadicFineH'Tol]; linarith)
        fun c ↦ ?_)
      have hchild_trans {Q : Polyad3 D.skeleton} (hQP : Q.coarsen hstop.vertex_eq.le f = P) :
          Q.IsTransversal := (Polyad3.isTransversal_coarsen_iff hstop.vertex_eq f Q).1 (hQP.symm ▸
          hP_trans)
      have hirr_le : (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P ∧
            ¬H'.IsTopRegularOverPolyad Q η_H' 1, (#Q.support : ℝ)) ≤ ∑ Q ∈ BadFine with Q.coarsen
            hstop.vertex_eq.le f = P, (#Q.support : ℝ) := sum_le_sum_of_subset_of_nonneg (fun Q hQ
            ↦ by
          obtain ⟨hQP, hnot⟩ := (mem_filter.1 hQ).2
          refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, hQP⟩
          by_contra! hg; exact hnot (hGoodTrans Q (hchild_trans hQP) hg.1 hg.2).1)
          fun _ _ _ ↦ Nat.cast_nonneg _
      let a : ℝ := H.relativeDensity c P
      have hsum_P : (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support
          : ℝ)) = #P.support := by
        rw [← Nat.cast_sum]; exact congrArg Nat.cast
          (by convert Polyad3.sum_card_support_coarsen hstop.vertex_eq.le f hf_symm P)
      have hP_avg : (#P.support : ℝ) * |(H'.relativeDensity c P : ℝ) - a| ≤ ∑ Q : Polyad3
          D.skeleton with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ) *
          |(H'.relativeDensity c Q : ℝ) - a| := by
        have hsplit := H'.relDensityOn_sub_mul_card_eq_sum_inter_support D.skeleton c P.support a
        rw [← relativeDensity_def] at hsplit
        rw [show (#P.support : ℝ) * |(H'.relativeDensity c P : ℝ) - a| = |((H'.relativeDensity c P
            : ℝ) - a) * #P.support| by
              rw [abs_mul, abs_of_nonneg (a := (#P.support : ℝ)) (Nat.cast_nonneg _), mul_comm],
          hsplit, show ∑ Q : Polyad3 D.skeleton, ((H'.relDensityOn c (P.support ∩ Q.support) : ℝ) -
              a) * #(P.support ∩ Q.support) = ∑ Q : Polyad3 D.skeleton with Q.coarsen
              hstop.vertex_eq.le f = P, ((H'.relativeDensity c Q : ℝ) - a) * #Q.support by
            rw [sum_filter]; refine sum_congr rfl fun Q _ ↦ ?_
            by_cases hQP : Q.coarsen hstop.vertex_eq.le f = P
            · simp [hQP, inter_eq_right.2 (hQP ▸ Polyad3.support_subset_coarsen hstop.vertex_eq.le
                f hf_symm Q), relativeDensity_def]
            · simp [hQP, disjoint_iff_inter_eq_empty.1 ((Polyad3.pairwise_disjoint_support (Ne.symm
                hQP)).mono_right (Polyad3.support_subset_coarsen hstop.vertex_eq.le f hf_symm Q))]]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (a := (#Q.support : ℝ)) (Nat.cast_nonneg _), mul_comm]
      have hdev_two : (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) ≤ 2 * ∑ Q :
            Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ) *
            |(H'.relativeDensity c Q : ℝ) - a| := by
        refine (sum_le_sum fun Q _ ↦ mul_le_mul_of_nonneg_left (a := (#Q.support : ℝ)) (b :=
          |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) (c := |(H'.relativeDensity c Q :
          ℝ) - a| + |(H'.relativeDensity c P : ℝ) - a|) ?_ (Nat.cast_nonneg _)).trans ?_
        · have := abs_sub_le (H'.relativeDensity c Q : ℝ) a (H'.relativeDensity c P : ℝ)
          rwa [abs_sub_comm a] at this
        · simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul, hsum_P]; linarith
      have hdev_a : (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support
            : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|) ≤ (∑ Q ∈ BadFine with Q.coarsen
            hstop.vertex_eq.le f = P, (#Q.support : ℝ)) + 2 * q₃ * η * #P.support := by
        refine (sum_le_sum (g := fun Q ↦ (if Q ∈ BadFine then (#Q.support : ℝ) else 0) + 2 * q₃ * η
          * #Q.support) fun Q hQ ↦ ?_).trans ?_
        · have hQP := (mem_filter.1 hQ).2; by_cases hbad : Q ∈ BadFine
          · simp only [hbad, ↓reduceIte]
            have h1 : |(H'.relativeDensity c Q : ℝ) - a| ≤ 1 := abs_sub_le_of_nonneg_of_le
              (mod_cast H'.relativeDensity_nonneg c Q) (mod_cast H'.relativeDensity_le_one c Q)
              (by dsimp [a]; exact_mod_cast H.relativeDensity_nonneg c P)
              (by dsimp [a]; exact_mod_cast H.relativeDensity_le_one c P)
            linarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) #Q.support),
              mul_nonneg (show 0 ≤ 2 * (q₃ : ℝ) * η by positivity) (Nat.cast_nonneg (α := ℝ)
              #Q.support)]
          · simp only [hbad, ↓reduceIte, zero_add]
            have hg : ¬((#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3 ∨ ¬H.IsTopRegularOverPolyad Q η 1)
                := fun h ↦ hbad (mem_filter.2 ⟨mem_univ _, h⟩)
            push Not at hg; have hdev_Q := (hGoodTrans Q (hchild_trans hQP) hg.1 hg.2).2 c
            rw [hQP] at hdev_Q
            exact (mul_le_mul_of_nonneg_left hdev_Q (Nat.cast_nonneg _)).trans_eq (by ring)
        · rw [sum_add_distrib, ← mul_sum, hsum_P, ← sum_filter]
          refine le_of_eq (congrArg (· + _) (sum_congr ?_ fun _ _ ↦ rfl))
          ext Q; simp only [mem_filter, mem_univ, true_and, and_comm]
      have h4qη : 4 * (q₃ : ℝ) * η ≤ δ₁ ^ 2 / 4 := by
        have h1 : 4 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 2 := (mul_le_mul
          (by linarith : 4 * (q₃ : ℝ) ≤ 4 * (q₃ + 1)) (min_le_right _ _) hη_pos.le
          (by positivity)).trans_eq (by field_simp; ring)
        have : η_H' = δ₁ ^ 2 / 4 := rfl; nlinarith [sq_nonneg η_H']
      have hdev_bound : (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P,
          (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) ≤ 2 * (∑ Q ∈
          BadFine with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ)) + (δ₁ ^ 2 / 4) *
          #P.support := (hdev_two.trans (mul_le_mul_of_nonneg_left hdev_a zero_le_two)).trans <|
          (by linarith : _ ≤ 2 * (∑ Q ∈ BadFine with Q.coarsen hstop.vertex_eq.le f = P,
              (#Q.support : ℝ)) + (4 * q₃ * η) * #P.support).trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right h4qη (Nat.cast_nonneg _)))
      convert (add_le_add hirr_le hdev_bound).trans
        (by linarith [hlt] : _ ≤ (3 / 4) * δ₁ ^ 2 * #P.support)
    have hBadFine_sum : (∑ Q ∈ BadFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 12) * n.descFactorial 3
      := by
      let SmallFine := univ.filter fun Q : Polyad3 D.skeleton ↦ (#Q.support : ℝ) < α_fine * (n : ℝ)
        ^ 3
      let IrregFine := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬H.IsTopRegularOverPolyad Q η 1
      have hsub : BadFine ⊆ SmallFine ∪ IrregFine := fun Q hQ ↦ by
        rcases (mem_filter.1 hQ).2 with h1 | h2
        exacts [mem_union_left _ (mem_filter.2 ⟨mem_univ _, h1⟩), mem_union_right _ (mem_filter.2
          ⟨mem_univ _, h2⟩)]
      have hunion := (sum_le_sum_of_subset_of_nonneg hsub fun Q _ _ ↦ Nat.cast_nonneg (α := ℝ)
          #Q.support).trans (sum_union_le_of_nonneg SmallFine IrregFine fun Q ↦ Nat.cast_nonneg (α
          := ℝ) #Q.support)
      have hcard_S : (#SmallFine : ℝ) ≤ ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ) := by
        have hc := card_polyad3_le D.skeleton; rw [hstop.vertex_eq, Fintype.card_fin] at hc
        exact_mod_cast (card_le_univ _).trans (hc.trans (Nat.le_succ _))
      have hSmall_le : (∑ Q ∈ SmallFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 24) * n.descFactorial 3
        := ((sum_le_sum fun Q hQ ↦ (mem_filter.1 hQ).2.le).trans_eq
        (by rw [sum_const, nsmul_eq_mul])).trans <| (mul_le_mul_of_nonneg_right hcard_S
        (by positivity : 0 ≤ α_fine * (n : ℝ) ^ 3)).trans <|
        (by dsimp [α_fine, triadicFineAlpha]; field_simp; ring :
              _ = (δ₁ ^ 2 * ε₁ / 96) * (n : ℝ) ^ 3).trans_le <|
              (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)
      have hIrreg_le : (∑ Q ∈ IrregFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 24) * n.descFactorial 3
        := by
        simpa [IrregFine, hstop.polyads_univ, triadicFineMass] using
          hstop.top_reg.sum_card_support_le
      linarith
    have hTransIrreg_sum : (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧
          ¬H'.IsTopRegularOverPolyad P δ₁ 1, (#P.support : ℝ)) ≤ (ε₁ / 2) * n.descFactorial 3 := by
      have hsum_charge : (δ₁ ^ 2 / 2) * (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧
          ¬H'.IsTopRegularOverPolyad P δ₁ 1, (#P.support : ℝ)) ≤ 3 * ∑ Q ∈ BadFine, (#Q.support :
          ℝ) := by
        rw [mul_sum]; exact (sum_le_sum fun P hP ↦ hcharge_trans (mem_filter.1 hP).2.1
          (mem_filter.1 hP).2.2).trans <| (sum_le_univ_sum_of_nonneg fun _ ↦ mul_nonneg (by
          norm_num) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)).trans_eq <| by
            rw [← mul_sum, sum_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _)]
      exact le_of_mul_le_mul_left (hsum_charge.trans ((mul_le_mul_of_nonneg_left hBadFine_sum (by
        norm_num)).trans_eq (by ring))) (by positivity)
    have hNonTrans_sum : (∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, (#P.support : ℝ)) ≤ (ε₁ /
        4) * n.descFactorial 3 := by
      let NonTransSet := (univ.filter fun P : Polyad3 C.skeleton ↦ ¬P.IsTransversal).biUnion
        Polyad3.support
      have hcard_u : ∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, #P.support = #NonTransSet :=
        (card_biUnion fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne).symm
      have hinj_map : NonTransSet.image Subtype.val ⊆ (Fintype.piFinset fun _ : Fin 3 ↦ (univ :
          Finset V)).filter (fun g ↦ ¬Injective fun i ↦ C.skeleton.vertexPart.part (g i)) := fun g
          hg ↦ by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hg; obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
        have hx' := (P.mem_support x).1 hxP
        refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, fun hinj ↦ (mem_filter.1
          hP).2 ?_⟩
        have hc0 := C.skeleton.vertexPart.part_eq_of_mem P.hc₀ hx'.1
        have hc1 := C.skeleton.vertexPart.part_eq_of_mem P.hc₁ hx'.2.1
        have hc2 := C.skeleton.vertexPart.part_eq_of_mem P.hc₂ hx'.2.2.1
        exact P.isTransversal_iff.2 ⟨fun e ↦ (by decide : (0 : Fin 3) ≠ 1) (hinj (hc0.trans
          (e.trans hc1.symm))), fun e ↦ (by decide : (0 : Fin 3) ≠ 2) (hinj (hc0.trans (e.trans
          hc2.symm))), fun e ↦ (by decide : (1 : Fin 3) ≠ 2) (hinj (hc1.trans (e.trans hc2.symm)))⟩
      have hcard_nt : #NonTransSet ≤ 3 * (n / t + 1) * n ^ 2 := (card_image_of_injective _
        Subtype.val_injective).symm.trans_le <| (card_le_card hinj_map).trans <|
        (C.skeleton.vertexPart.card_filter_not_injective_part_le_of_card_le (m := n / t + 1) fun A
        hA ↦ by simpa [card_univ] using hC_adm.equi.card_part_le_average_add_one hA).trans_eq
        (by rw [Fintype.card_fin, card_univ]; rfl)
      have h96t : 96 ≤ ε₁ * t := by
        have ht_c := ((Nat.le_add_left _ _).trans (le_max_right _ _)).trans hC_adm.parts_ge
        linarith [(div_le_iff₀ hε₁_pos).1 ((Nat.le_ceil (96 / ε₁)).trans (Nat.cast_le.2 ht_c))]
      have h96n : 96 ≤ ε₁ * n := by
        have hn_c := (Nat.le_add_left _ _).trans ((le_max_right 4 _).trans
          ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV))
        linarith [(div_le_iff₀ hε₁_pos).1 ((Nat.le_ceil (96 / ε₁)).trans (Nat.cast_le.2 hn_c))]
      have ht_pos : (0 : ℝ) < t := by
        by_contra! hle; linarith [mul_nonpos_of_nonneg_of_nonpos hε₁_pos.le hle]
      have hdiv_t : 3 * ((n / t : ℕ) : ℝ) ≤ (ε₁ / 32) * n := by
        have h1 : ((n / t : ℕ) : ℝ) * t ≤ n := mod_cast Nat.div_mul_le_self n t
        linarith [le_of_mul_le_mul_right
          (by nlinarith : (96 * ((n / t : ℕ) : ℝ)) * t ≤ (ε₁ * n) * t) ht_pos]
      rw [← Nat.cast_sum, hcard_u]
      exact (mod_cast hcard_nt : (#NonTransSet : ℝ) ≤ ((3 * (n / t + 1) * n ^ 2 : ℕ) : ℝ)).trans <|
        (by push_cast; ring : _ = (3 * ((n / t : ℕ) : ℝ) + 3) * (n : ℝ) ^ 2).trans_le <|
        (mul_le_mul_of_nonneg_right (add_le_add hdiv_t (by linarith : (3 : ℝ) ≤ (ε₁ / 32) * n)) (by
        positivity)).trans <| ((by ring : _ = (ε₁ / 16) * (n : ℝ) ^ 3).trans_le
        (mul_le_mul_of_nonneg_left hpow (by positivity))).trans_eq (by ring)
    have hRank1_most : H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
      rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC_dec, div_le_iff₀
        hdesc_pos]
      let S_tr := univ.filter fun P : Polyad3 C.skeleton ↦ P.IsTransversal ∧
        ¬H'.IsTopRegularOverPolyad P δ₁ 1
      let S_nt := univ.filter fun P : Polyad3 C.skeleton ↦ ¬P.IsTransversal
      have hsub : (univ.filter fun P : Polyad3 C.skeleton ↦ ¬H'.IsTopRegularOverPolyad P δ₁ 1) ⊆
          S_tr ∪ S_nt := fun P hP ↦ by
        by_cases htr : P.IsTransversal
        exacts [mem_union_left _ (mem_filter.2 ⟨mem_univ _, htr, (mem_filter.1 hP).2⟩),
          mem_union_right _ (mem_filter.2 ⟨mem_univ _, htr⟩)]
      refine (sum_le_sum_of_subset_of_nonneg (by convert hsub) fun _ _ _ ↦ Nat.cast_nonneg _).trans
        ((sum_union_le_of_nonneg S_tr S_nt fun _ ↦ Nat.cast_nonneg _).trans ?_)
      exact (add_le_add hTransIrreg_sum hNonTrans_sum).trans
        ((by ring_nf; exact le_rfl : _ ≤ (3 * ε₁ / 4) * n.descFactorial 3).trans
            (mul_le_mul_of_nonneg_right (by linarith [triadicEps1_le ε]) hdesc_pos.le))
    rw [topRegularOverMostPolyads_iff] at hRank1_most ⊢; refine le_trans ?_ hRank1_most
    rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
    refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (fun P hP ↦ ?_) fun _ _ _ ↦
      Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    obtain ⟨hP_mem, hnot⟩ := mem_filter.1 hP
    exact mem_filter.2 ⟨hP_mem, fun h1 ↦ hnot <| (IsTopRegularOverPolyad.of_rank_one_div_pow h1
      (triadicSched1_pos hF K)).mono (triadicSched1_le F K)⟩
  exact ⟨H', C, C.vertexCellsControlled_iff.2 ⟨hC_adm.equi, ((le_max_left t₀ 1).trans (le_max_left
      _ _)).trans hC_adm.parts_ge⟩, hApprox, hC_dec, C.skeleton.lowerSkeletonRegular_iff.2
      (hC_adm.lower_reg.isPairColorRegular (triadicSched1_le F _)), hMost,
      C.complexityBounded_iff.2 (hK_cap.trans ((le_max_left _ _).trans ((le_max_left _ _).trans
      (le_max_left _ _))))⟩
end Colored3Graph
end TauCeti
