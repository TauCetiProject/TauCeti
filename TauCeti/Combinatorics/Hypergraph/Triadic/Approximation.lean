/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Combinatorics.Hypergraph.Polyad.Symmetry
import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Strong regular approximation of colored three-uniform hypergraphs

For any positive tolerance `ε` and positive regularity schedule `F`, every coloring
`H : Colored3Graph κ V` of the unordered triples of a sufficiently large finite vertex set `V`
admits a *strong regular approximation*: a nearby coloring `H'` together with a triadic complex `C`
of bounded complexity whose vertex cells form an equipartition into at least `t₀` cells and whose
selected polyads decompose the injective triples, such that

* `H` approximates `H'` within `ε` in edit discrepancy (`H.Approximates3 H' ε`),
* the lower skeleton of `C` is regular at the arbitrary positive schedule `F` evaluated at the
  number of vertex cells plus the number of pair colors (`C.skeleton.LowerSkeletonRegular F`),
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples, and
* `C.complexity ≤ regularityBound3 (Fintype.card κ) ε F R t₀`, a bound independent of `|V|`.

The proof combines three steps following Rödl–Schacht, Tao, and Alon–Fischer–Krivelevich–Szegedy:

1. **Energy-increment outer loop (`exists_stopped_triadic_pair`).** Each round top-regularizes the
   coarse complex `C` at rank `1` into a fine palette refinement `D`
   (`Colored3Graph.exists_topRegularOverMostPolyads`). If the polyad energy gap exceeds `g_top`,
   re-regularizing the pair coloring (`exists_regularized_coarse_step`) produces a new coarse
   complex losing at most `g_top / 2` in energy
   (`Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`), so some round within `⌊2 / g_top⌋₊`
   steps stops with gap `≤ g_top`.
2. **Coupled recoloring on fine polyads (`exists_coupled_recoloring_of_stopped_pair`).** On each
   large top-regular canonical fine polyad `Q`, coupled recoloring
   (`exists_recoloring_abs_card_filter_sub_mul_card_le`) shifts densities toward the coarse parent
   while preserving subpolyad regularity. Disjointness of canonical supports
   (`Polyad3.disjoint_image_tripleSet_of_isCanonical`) glues these into `H'`, and role symmetry
   (`Polyad3.permute`) extends the bounds to all large top-regular transversal polyads.
3. **Coarse transfer and rank upgrade (`topRegularOverMostPolyads_of_stopped_pair`).** Fine
   regularity and coarse-density agreement imply rank-1 top regularity over most transversal
   polyads (`Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`,
   `Colored3Graph.sum_card_support_mul_abs_relativeDensity_sub_le_two_mul`); charging
   nontransversal polyads via equitability
   (`Polyad3.sum_card_support_not_isTransversal_le_of_isEquipartition`) and upgrading to rank
   `R C.complexity` (`Colored3Graph.IsTopRegularOverPolyad.of_rank_one_div_pow`) completes the
   proof.

## Main definitions

* `TauCeti.regularityBound3`: host-size and complexity bound for strong regular approximation of
  colored three-uniform hypergraphs.
* `TauCeti.Colored3Graph.IsStrongRegularApproximation3`: the bundled regularity, approximation,
  and complexity-bound predicate for `(H', C)`.

## Main results

* `TauCeti.le_regularityBound3`, `TauCeti.four_le_regularityBound3`,
  `TauCeti.regularityBound3_pos`: unconditional floor and positivity bounds for `regularityBound3`.
* `TauCeti.Colored3Graph.exists_strong_regular_approximation3`: every colored three-uniform
  hypergraph on at least `regularityBound3 (Fintype.card κ) ε F R t₀` vertices admits a strong
  regular approximation with vertex cells controlled at `t₀`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 and the regular approximation lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma and coupled edge modification.
-/

public section

open Finset Finpartition Function Real

namespace TauCeti

private noncomputable def triadicEps1 (ε : ℝ) : ℝ := min ε 1

private noncomputable def triadicSched1 (F : ℕ → ℝ) (k : ℕ) : ℝ :=
  min 1 ((range (k + 1)).inf' nonempty_range_add_one F)

private noncomputable def triadicRank1Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicSched1 F k ^ 2 / (2 : ℝ) ^ R k

private noncomputable def triadicFineH'Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 / 4

private noncomputable def triadicFineTol (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  min (triadicEps1 ε / (24 * ((q₃ : ℝ) + 1))) (triadicFineH'Tol F R k ^ 2 / (8 * ((q₃ : ℝ) + 1)))

private noncomputable def triadicFineMass (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 * triadicEps1 ε / 24

private noncomputable def triadicEnergyGap (q₃ : ℕ) (ε : ℝ) : ℝ :=
  (triadicEps1 ε / (12 * ((q₃ : ℝ) + 1))) ^ 2

private noncomputable def triadicPairEdit (q₃ : ℕ) (ε : ℝ) : ℝ :=
  min (1 / 16) (triadicEnergyGap q₃ ε / 48)

private noncomputable def triadicInitParts (q₃ : ℕ) (ε : ℝ) (t₀ : ℕ) : ℕ :=
  max (max t₀ 1) (⌈8 / triadicPairEdit q₃ ε⌉₊ + ⌈96 / triadicEps1 ε⌉₊)

private def triadicCompCap (T M : ℕ) : ℕ := T + M + T ^ 3 * M ^ 3

private noncomputable def triadicFineColorBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (T M : ℕ) : ℕ :=
  (range (T + 1)).sup fun t ↦
    strongTopRegularityStep t (triadicFineTol q₃ ε F R) (triadicFineMass ε F R) (fun _ ↦ 1) M

private noncomputable def triadicOuterStep (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (TM : ℕ × ℕ) : ℕ × ℕ :=
  let dMax := triadicFineColorBound q₃ ε F R TM.1 TM.2
  ((range (dMax + 1)).sup fun d ↦
      pairApproximationPartsBound d (triadicPairEdit q₃ ε) (triadicSched1 F) TM.1,
    max TM.2 (dMax + 1))

private noncomputable def triadicMaxSizes (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : ℕ × ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let T₀ := pairApproximationPartsBound 1 (triadicPairEdit q₃ ε) (triadicSched1 F) l₀
  (triadicOuterStep q₃ ε F R)^[⌊2 / triadicEnergyGap q₃ ε⌋₊] (T₀, 2)

private noncomputable def triadicFineAlpha (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k t d : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 * triadicEps1 ε / (96 * ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ))

/-- Host-size and complexity bound for strong regular approximation of colored three-uniform
hypergraphs with `q₃` top colors, edit and exceptional-mass tolerance `ε`, regularity schedule `F`,
rank schedule `R`, and minimum vertex-cell count `t₀`. Whenever `0 < ε` and `∀ n, 0 < F n`, any
host `V` with `regularityBound3 q₃ ε F R t₀ ≤ |V|` supports a strong regular approximation whose
complex has complexity at most `regularityBound3 q₃ ε F R t₀`
(see `Colored3Graph.exists_strong_regular_approximation3`). -/
noncomputable def regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let δp := triadicPairEdit q₃ ε
  let TM := triadicMaxSizes q₃ ε F R t₀
  let Bcoarse := triadicCompCap TM.1 TM.2
  let Dmax := triadicFineColorBound q₃ ε F R TM.1 TM.2
  let hBasic := max Bcoarse (max 4 (l₀ + ⌈96 / triadicEps1 ε⌉₊))
  let hPairInit := pairApproximationBound 1 δp (triadicSched1 F) l₀
  let hPairStep := (range (Dmax + 1)).sup fun d ↦
    pairApproximationBound d δp (triadicSched1 F) TM.1
  let hHoeff := (range (Bcoarse + 1)).sup fun k ↦
    ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R k ^ 2 *
      triadicFineAlpha ε F R k TM.1 Dmax)⌉₊ + 1
  max (max hBasic hPairInit) (max hPairStep hHoeff)

private theorem triadicEps1_pos {ε : ℝ} (hε : 0 < ε) : 0 < triadicEps1 ε := lt_min hε zero_lt_one

private theorem triadicEps1_le (ε : ℝ) : triadicEps1 ε ≤ ε := min_le_left _ _

private theorem triadicSched1_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (k : ℕ) :
    0 < triadicSched1 F k :=
  lt_min zero_lt_one ((lt_inf'_iff nonempty_range_add_one).2 fun m _ ↦ hF m)

private theorem triadicSched1_le (F : ℕ → ℝ) (k : ℕ) : triadicSched1 F k ≤ F k :=
  (min_le_right _ _).trans (inf'_le F (self_mem_range_succ k))

private theorem triadicRank1Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicRank1Tol F R k :=
  div_pos (pow_pos (triadicSched1_pos hF k) 2) (by positivity)

private theorem triadicFineH'Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicFineH'Tol F R k :=
  div_pos (pow_pos (triadicRank1Tol_pos hF R k) 2) (by norm_num)

private theorem triadicFineH'Tol_le_quarter {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    triadicFineH'Tol F R k ≤ 1 / 4 := by
  have h1 : triadicSched1 F k ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (triadicSched1_pos hF k).le (min_le_left _ _) 2).trans_eq (one_pow 2)
  have hr1 : triadicRank1Tol F R k ≤ 1 :=
    div_le_one_of_le₀ (h1.trans (one_le_pow₀ (by norm_num))) (by positivity)
  unfold triadicFineH'Tol
  linarith [(pow_le_pow_left₀ (triadicRank1Tol_pos hF R k).le hr1 2).trans_eq (one_pow 2)]

private theorem triadicFineTol_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (k : ℕ) : 0 < triadicFineTol q₃ ε F R k :=
  lt_min (div_pos (triadicEps1_pos hε) (by positivity))
    (div_pos (pow_pos (triadicFineH'Tol_pos hF R k) 2) (by positivity))

private theorem triadicFineMass_pos {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (k : ℕ) : 0 < triadicFineMass ε F R k :=
  div_pos (mul_pos (pow_pos (triadicRank1Tol_pos hF R k) 2) (triadicEps1_pos hε)) (by norm_num)

private theorem triadicFineAlpha_pos {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (k t d : ℕ) : 0 < triadicFineAlpha ε F R k t d :=
  div_pos (mul_pos (pow_pos (triadicRank1Tol_pos hF R k) 2) (triadicEps1_pos hε)) (by positivity)

private theorem triadicEnergyGap_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < triadicEnergyGap q₃ ε :=
  pow_pos (div_pos (triadicEps1_pos hε) (by positivity)) 2

private theorem triadicPairEdit_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < triadicPairEdit q₃ ε :=
  lt_min (by norm_num) (div_pos (triadicEnergyGap_pos q₃ hε) (by norm_num))

private theorem topRegularRefinementBound_le_triadicFineColorBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ)
    (R : ℕ → ℕ) {t T m M k : ℕ} (ht : t ≤ T) (hm : m ≤ M) (hk : k ≤ t + M + t ^ 3 * M ^ 3) :
    topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) m ≤
      triadicFineColorBound q₃ ε F R T M :=
  (topRegularRefinementBound_le_strongTopRegularityStep
    (triadicFineTol q₃ ε F R) (triadicFineMass ε F R) (fun _ ↦ 1) hm hk).trans
    (Finset.le_sup (f := fun t' ↦
      strongTopRegularityStep t' (triadicFineTol q₃ ε F R) (triadicFineMass ε F R) (fun _ ↦ 1) M)
      (mem_range.2 (Nat.lt_succ_of_le ht)))

private theorem le_triadicOuterStep_fst (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (TM : ℕ × ℕ) :
    TM.1 ≤ (triadicOuterStep q₃ ε F R TM).1 :=
  (le_pairApproximationPartsBound 0 (triadicPairEdit_pos q₃ hε) (triadicSched1_pos hF) TM.1).trans
    (Finset.le_sup
      (f := fun d ↦ pairApproximationPartsBound d (triadicPairEdit q₃ ε) (triadicSched1 F) TM.1)
      (mem_range.2 (Nat.succ_pos _)))

private theorem le_triadicOuterStep_snd (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (TM : ℕ × ℕ) :
    TM.2 ≤ (triadicOuterStep q₃ ε F R TM).2 := le_max_left _ _

private theorem basicFloor_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    max 4 (triadicInitParts q₃ ε t₀ + ⌈96 / triadicEps1 ε⌉₊) ≤ regularityBound3 q₃ ε F R t₀ :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- `regularityBound3` is always at least the requested vertex-cell floor `t₀`. -/
theorem le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    t₀ ≤ regularityBound3 q₃ ε F R t₀ :=
  ((le_max_left t₀ 1).trans (le_max_left _ _)).trans <|
    (Nat.le_add_right _ _).trans <|
      (le_max_right 4 _).trans (basicFloor_le_regularityBound3 q₃ ε F R t₀)

/-- `regularityBound3` is always at least `4`. -/
theorem four_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    4 ≤ regularityBound3 q₃ ε F R t₀ :=
  (le_max_left 4 _).trans (basicFloor_le_regularityBound3 q₃ ε F R t₀)

/-- `regularityBound3` is always positive. -/
theorem regularityBound3_pos (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    0 < regularityBound3 q₃ ε F R t₀ :=
  lt_of_lt_of_le (by decide) (four_le_regularityBound3 q₃ ε F R t₀)

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

variable (H H' : Colored3Graph κ V) (C : TriadicComplex3 V) in
/-- **Strong regular approximation of a colored three-uniform hypergraph.** A coloring `H'` and a
triadic complex `C` form a strong regular approximation of `H` at tolerance `ε`, regularity
schedule `F`, rank schedule `R`, and vertex-cell floor `t₀` when:

* `H` approximates `H'` within `ε` in edit discrepancy;
* the selected polyads of `C` decompose all injective triples;
* the lower skeleton of `C` is regular for the schedule `F`;
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples; and
* the complexity of `C` is at most `regularityBound3 (Fintype.card κ) ε F R t₀`. -/
def IsStrongRegularApproximation3 (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : Prop :=
  H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
    H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧
    C.ComplexityBounded (regularityBound3 (Fintype.card κ) ε F R t₀)

/-- Unfolded form of `Colored3Graph.IsStrongRegularApproximation3`. -/
theorem isStrongRegularApproximation3_iff {H H' : Colored3Graph κ V} {C : TriadicComplex3 V}
    {ε : ℝ} {F : ℕ → ℝ} {R : ℕ → ℕ} {t₀ : ℕ} :
    H.IsStrongRegularApproximation3 H' C ε F R t₀ ↔
      H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
        H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧
        C.ComplexityBounded (regularityBound3 (Fintype.card κ) ε F R t₀) :=
  Iff.rfl

end Colored3Graph

/-- Invariants maintained on the coarse triadic complex during the outer energy-increment loop. -/
private structure AdmissibleCoarse {V : Type*} [Fintype V] [DecidableEq V] (ε : ℝ) (F : ℕ → ℝ)
    (t₀ q₃ : ℕ) (C : TriadicComplex3 V) : Prop where
  equi : C.skeleton.vertexPart.IsEquipartition
  parts_ge : triadicInitParts q₃ ε t₀ ≤ #C.skeleton.vertexPart.parts
  polyads_univ : C.polyads = univ
  lower_reg : C.skeleton.LowerSkeletonRegular (triadicSched1 F)

/-- Stopping condition for the coarse/fine pair `(C, D)` produced by the outer loop. -/
private structure StoppedFine {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]
    (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (H : Colored3Graph κ V) (C D : TriadicComplex3 V)
    (f : Fin D.pairColorCount → Fin C.pairColorCount) : Prop where
  d_le : D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts 1
    (triadicFineTol q₃ ε F R C.complexity) (triadicFineMass ε F R C.complexity) C.pairColorCount
  vertex_eq : D.skeleton.vertexPart = C.skeleton.vertexPart
  proj_color : ∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p
  proj_rev : ∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)
  polyads_univ : D.polyads = univ
  top_reg : H.TopRegularOverMostPolyads D (triadicFineTol q₃ ε F R C.complexity)
    (triadicFineMass ε F R C.complexity) 1
  energy_gap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ triadicEnergyGap q₃ ε

private theorem exists_regularized_coarse_step {α V : Type*} [Fintype α] [Fintype V]
    [DecidableEq V] (q₃ t₀ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (S : PairColorSystem α V) (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
    (hparts : triadicInitParts q₃ ε t₀ ≤ #P.parts)
    (hhost : pairApproximationBound (Fintype.card α) (triadicPairEdit q₃ ε)
      (triadicSched1 F) #P.parts ≤ Fintype.card V) :
    ∃ (C' : TriadicComplex3 V) (g : α → Fin C'.pairColorCount),
      Injective g ∧ C'.skeleton.vertexPart ≤ P ∧
      #C'.skeleton.vertexPart.parts ≤
        pairApproximationPartsBound (Fintype.card α) (triadicPairEdit q₃ ε)
          (triadicSched1 F) #P.parts ∧
      C'.pairColorCount = Fintype.card α + 1 ∧ AdmissibleCoarse ε F t₀ q₃ C' ∧
      (#{p | C'.skeleton.pairColors.color p ≠ g (S.color p)} : ℝ) ≤
        triadicPairEdit q₃ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨P', T', hP'_le, hP'_equi, hP'_card, -, hT'_reg, hT'_edits⟩ :=
    S.exists_refining_equipartition_lowerSkeletonRegular P hP (triadicPairEdit_pos q₃ hε)
      (triadicSched1_pos hF) hhost
  let e' : Option α ≃ Fin (Fintype.card (Option α)) := Fintype.equivFin (Option α)
  let C' : TriadicComplex3 V :=
    ⟨Fintype.card (Option α), (⟨P', T'⟩ : PairSkeleton3 (Option α) V).relabel e', univ⟩
  have hvp : C'.skeleton.vertexPart = P' := PairSkeleton3.relabel_vertexPart e'
  have hpcc : C'.pairColorCount = Fintype.card α + 1 := Fintype.card_option
  refine ⟨C', fun c ↦ e' (some c), e'.injective.comp (Option.some_injective _), hvp.symm ▸ hP'_le,
    hvp.symm ▸ hP'_card, hpcc,
    ⟨hvp.symm ▸ hP'_equi, hvp.symm ▸ hparts.trans (card_mono hP'_le), rfl, hT'_reg.relabel e'⟩, ?_⟩
  refine le_trans ?_ hT'_edits
  norm_cast
  refine card_le_card fun p hp ↦ ?_
  simpa only [mem_filter, mem_univ, true_and, C', PairSkeleton3.relabel_pairColors,
    PairColorSystem.relabel_color, ne_eq, e'.injective.eq_iff] using hp

private theorem exists_stopped_triadic_pair {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V]
    [DecidableEq V] (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (t₀ : ℕ) (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      #C.skeleton.vertexPart.parts ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).1 ∧
      C.pairColorCount ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).2 ∧
      AdmissibleCoarse ε F t₀ (Fintype.card κ) C ∧
      StoppedFine (Fintype.card κ) ε F R H C D f := by
  let q₃ := Fintype.card κ
  let n := Fintype.card V
  let g_top := triadicEnergyGap q₃ ε
  let δp := triadicPairEdit q₃ ε
  have hg_pos := triadicEnergyGap_pos q₃ hε
  have hn4 : 4 ≤ n := (four_le_regularityBound3 q₃ ε F R t₀).trans hV
  have hpow_le : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) :=
    mod_cast Nat.pow_three_le_four_mul_descFactorial hn4
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := by
    linarith [pow_pos (Nat.cast_pos.2 (by omega : 0 < n) : (0 : ℝ) < n) 3]
  let step := triadicOuterStep q₃ ε F R
  let TM_max := triadicMaxSizes q₃ ε F R t₀
  let Good (C : TriadicComplex3 V) : Prop :=
    ∃ (D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      StoppedFine q₃ ε F R H C D f
  -- One outer round: either the fine top-regularization stops with gap ≤ `g_top`, or
  -- re-regularizing the pair coloring increases the coarse polyad energy by more than `g_top / 2`.
  have advance (TM : ℕ × ℕ) (hTM1 : TM.1 ≤ TM_max.1) (hTM2 : TM.2 ≤ TM_max.2)
      (C : TriadicComplex3 V) (hC1 : #C.skeleton.vertexPart.parts ≤ TM.1)
      (hC2 : C.pairColorCount ≤ TM.2) (hC : AdmissibleCoarse ε F t₀ q₃ C) :
      Good C ∨ ∃ C' : TriadicComplex3 V,
        #C'.skeleton.vertexPart.parts ≤ (step TM).1 ∧ C'.pairColorCount ≤ (step TM).2 ∧
        AdmissibleCoarse ε F t₀ q₃ C' ∧
        H.polyadEnergy C.skeleton + g_top / 2 < H.polyadEnergy C'.skeleton := by
    obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg⟩ :=
      H.exists_topRegularOverMostPolyads C.skeleton
        (triadicFineTol_pos q₃ hε hF R C.complexity)
        (triadicFineMass_pos hε hF R C.complexity) 1
    rw [Fintype.card_fin] at hDcard
    by_cases hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g_top
    · exact Or.inl ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩
    have hd_step := hDcard.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1
      hC2 (C.complexity_le.trans (by gcongr)))
    have h1M := hC1.trans hTM1
    have hd_max := hDcard.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R h1M
      (hC2.trans hTM2) (C.complexity_le.trans (by have := hC2.trans hTM2; gcongr)))
    obtain ⟨C', g, hginj, hC'V, hC'card, hC'pcc, hC'adm, hC'edits⟩ :=
      exists_regularized_coarse_step q₃ t₀ hε hF D.skeleton.pairColors C.skeleton.vertexPart
        hC.equi hC.parts_ge (by
          rw [Fintype.card_fin]
          exact ((pairApproximationBound_mono _ _ _ h1M).trans
            ((Finset.le_sup (f := fun d' ↦ pairApproximationBound d' δp (triadicSched1 F) TM_max.1)
              (mem_range.2 (Nat.lt_succ_of_le hd_max))).trans
              ((le_max_left _ _).trans (le_max_right _ _)))).trans hV)
    rw [Fintype.card_fin] at hC'card hC'pcc
    have hC'1 : #C'.skeleton.vertexPart.parts ≤ (step TM).1 :=
      (hC'card.trans (pairApproximationPartsBound_mono _ _ _ hC1)).trans
        (Finset.le_sup (f := fun d' ↦ pairApproximationPartsBound d' δp (triadicSched1 F) TM.1)
          (mem_range.2 (Nat.lt_succ_of_le hd_step)))
    have hC'2 : C'.pairColorCount ≤ (step TM).2 :=
      hC'pcc.symm ▸ (Nat.add_le_add_right hd_step 1).trans (le_max_right _ _)
    have hdrop := H.polyadEnergy_sub_le_of_pairRecoloring (hDV ▸ hC'V) hginj
    have hdrop_le : H.polyadEnergy D.skeleton - H.polyadEnergy C'.skeleton ≤ g_top / 2 := by
      push_cast at hdrop
      have hnum : 6 * (#{p | C'.skeleton.pairColors.color p ≠
          g (D.skeleton.pairColors.color p)} : ℝ) * n ≤ 24 * δp * n.descFactorial 3 := by
        nlinarith [hC'edits, hpow_le, triadicPairEdit_pos q₃ hε,
          Nat.cast_nonneg (α := ℝ) n]
      exact hdrop.trans (((div_le_iff₀ hdesc_pos).2 hnum).trans
        (by linarith [show δp ≤ g_top / 48 from min_le_right _ _]))
    exact Or.inr ⟨C', hC'1, hC'2, hC'adm, by linarith⟩
  -- Build the initial admissible coarse complex from a monochromatic pair coloring.
  let l₀ := triadicInitParts q₃ ε t₀
  have hl₀_pos : 0 < l₀ := (le_max_right t₀ 1).trans (le_max_left _ _)
  have hl₀_le : l₀ ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.le_add_right l₀ _).trans
      ((le_max_right 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV))
  obtain ⟨P_init, hP_init, hcard_init⟩ :=
    Finpartition.exists_equipartition_card_eq (univ : Finset V) hl₀_pos.ne' hl₀_le
  obtain ⟨C₀, -, -, -, hC₀1, hC₀2, hC₀, -⟩ :=
    exists_regularized_coarse_step q₃ t₀ hε hF
      (⟨fun _ ↦ (), id, fun _ ↦ rfl, fun _ ↦ rfl⟩ : PairColorSystem Unit V) P_init hP_init
      hcard_init.ge (by
        rw [Fintype.card_unique, hcard_init]
        exact ((le_max_right _ _).trans (le_max_left _ _)).trans hV)
  rw [Fintype.card_unique, hcard_init] at hC₀1
  rw [Fintype.card_unique] at hC₀2
  -- Iterate for at most `⌊2 / g_top⌋₊` rounds; polyad energy cannot exceed `1`.
  let TM₀ : ℕ × ℕ := (pairApproximationPartsBound 1 δp (triadicSched1 F) l₀, 2)
  let K_rounds := ⌊2 / g_top⌋₊
  have hstep_mono {j k : ℕ} (hj : j ≤ k) :
      (step^[j] TM₀).1 ≤ (step^[k] TM₀).1 ∧ (step^[j] TM₀).2 ≤ (step^[k] TM₀).2 := by
    induction k, hj using Nat.le_induction with
    | base => exact ⟨le_rfl, le_rfl⟩
    | succ _ _ ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (le_triadicOuterStep_fst q₃ hε hF R _),
        ih.2.trans (le_triadicOuterStep_snd q₃ ε F R _)⟩
  have loop (j : ℕ) (hj : j ≤ K_rounds) :
      (∃ C, #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧
          C.pairColorCount ≤ (step^[j] TM₀).2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧ Good C) ∨
        ∃ C, #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧
          C.pairColorCount ≤ (step^[j] TM₀).2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧
          (j : ℝ) * (g_top / 2) ≤ H.polyadEnergy C.skeleton := by
    induction j with
    | zero => exact Or.inr ⟨C₀, hC₀1, hC₀2.le, hC₀, by simpa using H.polyadEnergy_nonneg _⟩
    | succ j ih =>
      have hj' := Nat.le_of_succ_le hj
      have ⟨hle1, hle2⟩ := hstep_mono (Nat.le_succ j)
      obtain ⟨C, h1, h2, hC, hg⟩ | ⟨C, h1, h2, hC, hE⟩ := ih hj'
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hg⟩
      obtain ⟨hM1, hM2⟩ := hstep_mono hj'
      obtain hg | ⟨C', h1', h2', hC', hE'⟩ := advance (step^[j] TM₀) hM1 hM2 C h1 h2 hC
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hg⟩
      rw [Function.iterate_succ_apply']
      exact Or.inr ⟨C', h1', h2', hC', by push_cast; linarith⟩
  have hK_gt : 1 < ((K_rounds : ℝ) + 1) * (g_top / 2) := by
    linarith [(div_lt_iff₀ hg_pos).1 (Nat.lt_floor_add_one (2 / g_top))]
  obtain ⟨C, hC1, hC2, hC, D, f, hD⟩ | ⟨C, hC1, hC2, hC, hE⟩ := loop K_rounds le_rfl
  · exact ⟨C, D, f, hC1, hC2, hC, hD⟩
  obtain ⟨D, f, hD⟩ | ⟨C', -, -, -, hE'⟩ := advance TM_max le_rfl le_rfl C hC1 hC2 hC
  · exact ⟨C, D, f, hC1, hC2, hC, hD⟩
  linarith [H.polyadEnergy_le_one C'.skeleton]

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

/-- Fine top regularity and coarse-density agreement on all large top-regular transversal polyads
of `D`. -/
private def GoodTransFine {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]
    (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (H H' : Colored3Graph κ V) (C D : TriadicComplex3 V)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart) : Prop :=
  ∀ Q' : Polyad3 D.skeleton, Q'.IsTransversal →
    triadicFineAlpha ε F R C.complexity #C.skeleton.vertexPart.parts D.pairColorCount *
      (Fintype.card V : ℝ) ^ 3 ≤ #Q'.support →
    H.IsTopRegularOverPolyad Q' (triadicFineTol (Fintype.card κ) ε F R C.complexity) 1 →
    H'.IsTopRegularOverPolyad Q' (triadicFineH'Tol F R C.complexity) 1 ∧
      ∀ c : κ,
        |(H'.relativeDensity c Q' : ℝ) - H.relativeDensity c (Q'.coarsen hV f)| ≤
          2 * Fintype.card κ * triadicFineTol (Fintype.card κ) ε F R C.complexity

/-- Given a stopped coarse/fine pair `(C, D)`, construct an approximating coloring `H'` via
independent coupled recolorings on large top-regular canonical fine polyads of `D`, and transfer
fine top regularity and coarse-density agreement to all large top-regular transversal polyads
of `D` by role symmetry. -/
private theorem exists_coupled_recoloring_of_stopped_pair (H : Colored3Graph κ V) {ε : ℝ}
    (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V)
    {C D : TriadicComplex3 V} {f : Fin D.pairColorCount → Fin C.pairColorCount}
    (hC1 : #C.skeleton.vertexPart.parts ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).1)
    (hC2 : C.pairColorCount ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).2)
    (hstop : StoppedFine (Fintype.card κ) ε F R H C D f) :
    ∃ H' : Colored3Graph κ V, H.Approximates3 H' ε ∧
      GoodTransFine ε F R H H' C D f hstop.vertex_eq.le := by
  classical
  let q₃ := Fintype.card κ
  let n := Fintype.card V
  let ε₁ := triadicEps1 ε
  let TM_max := triadicMaxSizes q₃ ε F R t₀
  let K := C.complexity
  let t := #C.skeleton.vertexPart.parts
  let d := D.pairColorCount
  let η_H' := triadicFineH'Tol F R K
  let η := triadicFineTol q₃ ε F R K
  let α_fine := triadicFineAlpha ε F R K t d
  have hε₁_pos := triadicEps1_pos hε
  have hη_H'_pos := triadicFineH'Tol_pos hF R K
  have hη_H'_le := triadicFineH'Tol_le_quarter hF R K
  have hη_pos := triadicFineTol_pos q₃ hε hF R K
  have hα_pos : 0 < α_fine := triadicFineAlpha_pos hε hF R K t d
  have hn4 : 4 ≤ n := (four_le_regularityBound3 q₃ ε F R t₀).trans hV
  have hn_pos : (0 : ℝ) < n := by positivity
  have hf_symm (p) : C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p) :=
    (hstop.proj_color p).symm
  have hK_cap : K ≤ triadicCompCap TM_max.1 TM_max.2 :=
    C.complexity_le.trans (by dsimp [triadicCompCap]; gcongr)
  have hd_max := hstop.d_le.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1
    hC2 (C.complexity_le.trans (by gcongr)))
  have hD_dec : D.IsPolyadDecomposition :=
    D.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hstop.polyads_univ ▸ mem_univ _
  -- Apply coupled recoloring independently on each large top-regular canonical fine polyad.
  let idx := Fintype.equivFin D.skeleton.vertexPart.parts
  let U_of (Q : Polyad3 D.skeleton) := Q.support.image tripleSet
  let GoodCanon : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦
    Q.IsCanonical idx ∧ α_fine * (n : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1
  have hGoodCanon_disj : ((GoodCanon : Set (Polyad3 D.skeleton))).PairwiseDisjoint U_of :=
    fun _ hQ₁ _ hQ₂ hne ↦
      Polyad3.disjoint_image_tripleSet_of_isCanonical
        (mem_filter.1 hQ₁).2.1 (mem_filter.1 hQ₂).2.1 hne
  have hcnt_eq (G : Colored3Graph κ V) {Q : Polyad3 D.skeleton} (hQt : Q.IsTransversal)
      {S} (hS : S ⊆ Q.support) (c : κ) :
      (#{s ∈ S.image tripleSet | G.color s = c} : ℝ) = (G.relDensityOn c S : ℝ) * #S :=
    mod_cast G.card_filter_image_tripleSet_eq_relDensityOn_mul_card c hQt hS
  let α_min :=
    triadicFineAlpha ε F R K TM_max.1 (triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2)
  have hα_min_pos : 0 < α_min := triadicFineAlpha_pos hε hF R K _ _
  have hα_min_le : α_min ≤ α_fine := by
    have := triadicRank1Tol_pos hF R K
    refine div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact_mod_cast Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.pow_le_pow_left hC1 3) (Nat.pow_le_pow_left hd_max 3)) 1
  have hhost_strict : (q₃ + 6 : ℝ) < 2 * η ^ 2 * α_fine * n := by
    have hceil_n : ⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ + 1 ≤ n :=
      ((Finset.le_sup (f := fun j ↦ ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R j ^ 2 *
          triadicFineAlpha ε F R j TM_max.1
            (triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2))⌉₊ + 1)
          (mem_range.2 (Nat.lt_succ_of_le hK_cap))).trans
        ((le_max_right _ _).trans (le_max_right _ _))).trans hV
    have hlt : (q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min) < n :=
      (Nat.le_ceil _).trans_lt ((lt_add_one _).trans_le (mod_cast hceil_n))
    nlinarith [(div_lt_iff₀ (by positivity : 0 < 2 * η ^ 2 * α_min)).1 hlt,
      mul_le_mul_of_nonneg_left hα_min_le (by positivity : 0 ≤ 2 * η ^ 2 * n)]
  have hrec (Q : GoodCanon) :=
    let hQ2 := (mem_filter.1 Q.2).2
    let hcard_U := hQ2.1.isTransversal.card_image_tripleSet Subset.rfl
    let hQ_pos := Nat.cast_pos.1 ((mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ2.2.1)
    have ha_pos : 0 < η * #(U_of Q.1) := by
      rw [hcard_U]
      exact mul_pos hη_pos (Nat.cast_pos.2 hQ_pos)
    exists_recoloring_abs_card_filter_sub_mul_card_le (U_of Q.1) H.color
      (p := fun c ↦ (H.relativeDensity c (Q.1.coarsen hstop.vertex_eq.le f) : ℝ))
      (fun c ↦ mod_cast H.relativeDensity_nonneg c _)
      (mod_cast H.sum_relativeDensity ((Finset.card_pos.1 hQ_pos).mono
        (Polyad3.support_subset_coarsen hstop.vertex_eq.le f hf_symm Q.1)))
      (fun W : Subpolyad3 Q.1 ↦ W.support.image tripleSet)
      (fun W ↦ image_subset_image W.support_subset)
      ha_pos ha_pos.le (fun W c₀ ↦ by
        rw [hcard_U, hQ2.1.isTransversal.card_image_tripleSet W.support_subset,
          hcnt_eq H hQ2.1.isTransversal W.support_subset c₀,
          hcnt_eq H hQ2.1.isTransversal Subset.rfl c₀,
          mul_div_cancel_right₀ _ (Nat.cast_pos.2 hQ_pos).ne', ← relativeDensity_def, ← sub_mul,
          abs_mul, abs_of_nonneg (a := (#W.support : ℝ)) (Nat.cast_nonneg _)]
        exact hQ2.2.2.abs_relDensityOn_sub_mul_card_le c₀ W)
      (by
        rw [hcard_U]
        refine two_mul_add_one_mul_exp_lt_one (card_subpolyad3_le Q.1) ?_
        have hst : (q₃ + 6 : ℝ) * (n : ℝ) ^ 2 < 2 * η ^ 2 * (α_fine * (n : ℝ) ^ 3) :=
          (mul_lt_mul_of_pos_right hhost_strict (pow_pos hn_pos 2)).trans_eq (by ring)
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        linarith only [hst,
          mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) (Nat.one_le_cast.2 (by omega : 1 ≤ n)))
            (add_nonneg (Nat.cast_nonneg q₃) (by norm_num : (0 : ℝ) ≤ 3)),
          mul_le_mul_of_nonneg_left hQ2.2.1 (mul_nonneg zero_le_two (sq_nonneg η))])
  -- Glue the local recolorings on disjoint canonical supports into `H'`.
  choose xloc _ hxloc_edits hxloc_sub using hrec
  let H' : Colored3Graph κ V := ⟨fun s ↦
    if hs : ∃ Q ∈ GoodCanon, s ∈ U_of Q then xloc ⟨hs.choose, hs.choose_spec.1⟩ s else H.color s⟩
  have hH'_on {Q : Polyad3 D.skeleton} (hQ : Q ∈ GoodCanon) {s} (hs : s ∈ U_of Q) :
      H'.color s = xloc ⟨Q, hQ⟩ s := by
    have hex : ∃ Q' ∈ GoodCanon, s ∈ U_of Q' := ⟨Q, hQ, hs⟩
    refine (dite_eq_left hex).trans (congrArg (xloc · s) (Subtype.ext ?_))
    exact by_contra fun hne ↦
      disjoint_left.1 (hGoodCanon_disj hex.choose_spec.1 hQ hne) hex.choose_spec.2 hs
  have hApprox : H.Approximates3 H' ε := by
    rw [approximates3_iff, editDiscrepancy3_def, Nat.card_eq_fintype_card]
    let Diff : Finset (Set.powersetCard V 3) := univ.filter fun s ↦ H.color s ≠ H'.color s
    rw [show {s : Set.powersetCard V 3 | H.color s ≠ H'.color s} = (Diff : Set _) from
      Set.ext fun _ ↦ by simp [Diff], Set.ncard_coe_finset]
    push_cast
    refine (div_le_iff₀ (pow_pos hn_pos 3)).2 ?_
    have hDiff_card :
        (#Diff : ℝ) ≤ ∑ Q ∈ GoodCanon, (#{s ∈ U_of Q | H.color s ≠ H'.color s} : ℝ) := by
      rw [← Nat.cast_sum, ← card_biUnion fun _ h1 _ h2 hne ↦
        (hGoodCanon_disj h1 h2 hne).mono (filter_subset _ _) (filter_subset _ _)]
      exact_mod_cast card_le_card fun s hs ↦
        have hne : H.color s ≠ H'.color s := (mem_filter.1 hs).2
        if hex : ∃ Q ∈ GoodCanon, s ∈ U_of Q then
          mem_biUnion.2 ⟨hex.choose, hex.choose_spec.1, mem_filter.2 ⟨hex.choose_spec.2, hne⟩⟩
        else (hne (dite_eq_right hex : H'.color s = H.color s).symm).elim
    have hQ_edit (Q : Polyad3 D.skeleton) (hQ : Q ∈ GoodCanon) :
        (#{s ∈ U_of Q | H.color s ≠ H'.color s} : ℝ) ≤
          (∑ c, (#Q.support : ℝ) *
            |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)|) /
            2 + q₃ * η * #Q.support := by
      have hQt := (mem_filter.1 hQ).2.1.isTransversal
      rw [show {s ∈ U_of Q | H.color s ≠ H'.color s} = {s ∈ U_of Q | xloc ⟨Q, hQ⟩ s ≠ H.color s}
        from filter_congr fun s hs ↦ by rw [hH'_on hQ hs, ne_comm]]
      refine (hxloc_edits ⟨Q, hQ⟩).trans ?_
      rw [hQt.card_image_tripleSet Subset.rfl, ← mul_assoc]
      refine add_le_add_left (div_le_div_of_nonneg_right
        (le_of_eq (sum_congr rfl fun c _ ↦ by
          rw [hcnt_eq H hQt Subset.rfl c, ← relativeDensity_def, ← sub_mul, abs_mul,
            abs_of_nonneg (a := (#Q.support : ℝ)) (Nat.cast_nonneg _), mul_comm])) zero_le_two) _
    have hdesc_le : (n.descFactorial 3 : ℝ) ≤ (n : ℝ) ^ 3 :=
      mod_cast Nat.descFactorial_le_pow n 3
    have hsum_supp : (∑ Q ∈ GoodCanon, (#Q.support : ℝ)) ≤ (n : ℝ) ^ 3 := by
      rw [← Nat.cast_sum]
      exact (Nat.cast_le.2 ((sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _).trans_eq
        (by simpa [hstop.polyads_univ] using hD_dec.sum_card_support))).trans hdesc_le
    have hsum_dev :
        (∑ Q ∈ GoodCanon, ∑ c, (#Q.support : ℝ) *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)|) ≤
          q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3 := by
      rw [sum_comm]
      refine (sum_le_sum fun c _ ↦ (sum_le_univ_sum_of_nonneg fun _ ↦ by positivity).trans
        (H.sum_card_support_mul_abs_relativeDensity_coarsen_le
          hstop.vertex_eq.le f hf_symm hstop.energy_gap c)).trans ?_
      rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hdesc_le (by positivity)
    have hsum_edit :
        (#Diff : ℝ) ≤ (q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3) / 2 + q₃ * η * (n : ℝ) ^ 3 :=
      (hDiff_card.trans (sum_le_sum hQ_edit)).trans <| by
        rw [sum_add_distrib, ← sum_div, ← mul_sum]
        exact add_le_add (div_le_div_of_nonneg_right hsum_dev zero_le_two)
          (mul_le_mul_of_nonneg_left hsum_supp (by positivity))
    have hterm1 : 3 * (q₃ : ℝ) * √(triadicEnergyGap q₃ ε) ≤ ε₁ / 4 := by
      rw [triadicEnergyGap, sqrt_sq (by positivity)]
      exact (mul_le_mul_of_nonneg_right (by linarith : 3 * (q₃ : ℝ) ≤ 3 * (q₃ + 1))
        (by positivity)).trans_eq (by field_simp; ring)
    have hterm2 : 6 * (q₃ : ℝ) * η ≤ ε₁ / 4 :=
      (mul_le_mul (by linarith : 6 * (q₃ : ℝ) ≤ 6 * (q₃ + 1)) (min_le_left _ _)
        hη_pos.le (by positivity)).trans_eq (by field_simp; ring)
    exact (by linarith :
      6 * (#Diff : ℝ) ≤ (3 * q₃ * √(triadicEnergyGap q₃ ε) + 6 * q₃ * η) * (n : ℝ) ^ 3).trans
      (mul_le_mul_of_nonneg_right ((add_le_add hterm1 hterm2).trans
        ((by linarith : ε₁ / 4 + ε₁ / 4 ≤ ε₁).trans (triadicEps1_le ε))) (by positivity))
  refine ⟨H', hApprox, fun Q' hQ't hQ'l hQ'r ↦ ?_⟩
  obtain ⟨σ, hQ_can⟩ := Polyad3.exists_permute_isCanonical idx.injective hQ't
  set Q := Q'.permute σ
  have hQ_large : α_fine * (n : ℝ) ^ 3 ≤ #Q.support := by rwa [Polyad3.card_support_permute]
  have hQ : Q ∈ GoodCanon := mem_filter.2
    ⟨mem_univ _, hQ_can, hQ_large, (H.isTopRegularOverPolyad_permute_iff Q' σ η 1).2 hQ'r⟩
  have hQt := hQ_can.isTransversal
  have hQ_pos : (0 : ℝ) < #Q.support := (mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ_large
  have hW_count (W : Subpolyad3 Q) (c : κ) :
      |(H'.relDensityOn c W.support : ℝ) -
          H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)| * #W.support ≤
        2 * q₃ * η * #Q.support := by
    have hsub := hxloc_sub ⟨Q, hQ⟩ W c
    rw [show {s ∈ W.support.image tripleSet | xloc ⟨Q, hQ⟩ s = c} =
        {s ∈ W.support.image tripleSet | H'.color s = c} from
        filter_congr fun s hs ↦ by rw [hH'_on hQ (image_subset_image W.support_subset hs)],
      hcnt_eq H' hQt W.support_subset c, hQt.card_image_tripleSet W.support_subset,
      hQt.card_image_tripleSet Subset.rfl, ← sub_mul, abs_mul,
      abs_of_nonneg (a := (#W.support : ℝ)) (Nat.cast_nonneg _)] at hsub
    linarith
  have hrel_dev (c : κ) :
      |(H'.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)| ≤
        2 * q₃ * η := by
    have hfull := hW_count (Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂) c
    rw [Subpolyad3.support_ofSubcells_cells, ← relativeDensity_def] at hfull
    exact le_of_mul_le_mul_right hfull hQ_pos
  refine ⟨(H'.isTopRegularOverPolyad_permute_iff Q' σ η_H' 1).1
      (isTopRegularOverPolyad_one_iff.2 fun c W hW ↦ ?_),
    fun c ↦ ?_⟩
  · have hq_tol : 2 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 4 :=
      (mul_le_mul (by linarith : 2 * (q₃ : ℝ) ≤ 2 * (q₃ + 1)) (min_le_right _ _)
        hη_pos.le (by positivity)).trans_eq (by field_simp; ring)
    have htri := abs_sub_le (H'.relDensityOn c W.support : ℝ)
      (H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f)) (H'.relativeDensity c Q)
    rw [abs_sub_comm (H.relativeDensity c (Q.coarsen hstop.vertex_eq.le f) : ℝ)] at htri
    linarith [hrel_dev c,
      add_le_of_mul_le_mul_of_le_sq_div_two hη_H'_pos (hη_H'_le.trans (by norm_num))
        (hq_tol.trans (by nlinarith [sq_nonneg η_H'])) hW hQ_pos (hW_count W c)]
  · rw [← H'.relativeDensity_permute c Q' σ,
      ← H.relativeDensity_permute c (Q'.coarsen hstop.vertex_eq.le f) σ,
      ← Polyad3.coarsen_permute hstop.vertex_eq.le hstop.proj_rev Q' σ]
    exact hrel_dev c

/-- Transfer fine top regularity and coarse-density agreement on large regular transversal polyads
of `D` to `(F C.complexity, R C.complexity)`-top-regularity of `H'` over most polyads of `C`. -/
private theorem topRegularOverMostPolyads_of_stopped_pair (H H' : Colored3Graph κ V) {ε : ℝ}
    (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V)
    {C D : TriadicComplex3 V} {f : Fin D.pairColorCount → Fin C.pairColorCount}
    (hC_adm : AdmissibleCoarse ε F t₀ (Fintype.card κ) C)
    (hstop : StoppedFine (Fintype.card κ) ε F R H C D f)
    (hGoodTrans : GoodTransFine ε F R H H' C D f hstop.vertex_eq.le) :
    H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) := by
  classical
  let q₃ := Fintype.card κ
  let n := Fintype.card V
  let ε₁ := triadicEps1 ε
  let K := C.complexity
  let t := #C.skeleton.vertexPart.parts
  let d := D.pairColorCount
  let δ₁ := triadicRank1Tol F R K
  let η_H' := triadicFineH'Tol F R K
  let η := triadicFineTol q₃ ε F R K
  let α_fine := triadicFineAlpha ε F R K t d
  have hε₁_pos := triadicEps1_pos hε
  have hδ₁_pos := triadicRank1Tol_pos hF R K
  have hη_H'_pos := triadicFineH'Tol_pos hF R K
  have hη_pos := triadicFineTol_pos q₃ hε hF R K
  have hn4 : 4 ≤ n := (four_le_regularityBound3 q₃ ε F R t₀).trans hV
  have hn_pos : (0 : ℝ) < n := by positivity
  have hpow : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) :=
    mod_cast Nat.pow_three_le_four_mul_descFactorial hn4
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := by linarith [pow_pos hn_pos 3]
  have hf_symm (p) : C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p) :=
    (hstop.proj_color p).symm
  have hC_dec : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hC_adm.polyads_univ ▸ mem_univ _
  -- Charge each rank-1 irregular transversal coarse polyad to its bad fine children.
  let BadFine : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦
    (#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3 ∨ ¬H.IsTopRegularOverPolyad Q η 1
  have hcharge_trans {P : Polyad3 C.skeleton} (hP_trans : P.IsTransversal)
      (hP_irreg : ¬H'.IsTopRegularOverPolyad P δ₁ 1) :
      (δ₁ ^ 2 / 2) * #P.support ≤
        3 * ∑ Q ∈ BadFine with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ) := by
    by_contra! hlt
    refine hP_irreg (H'.isTopRegularOverPolyad_of_sum_coarsen_le hstop.vertex_eq.le f hf_symm
      hη_H'_pos.le hδ₁_pos (θ := (3 / 4) * δ₁ ^ 2)
      (by dsimp [η_H', triadicFineH'Tol]; linarith) fun c ↦ ?_)
    have hchild_trans {Q : Polyad3 D.skeleton} (hQP : Q.coarsen hstop.vertex_eq.le f = P) :
        Q.IsTransversal :=
      (Polyad3.isTransversal_coarsen_iff hstop.vertex_eq f Q).1 (hQP.symm ▸ hP_trans)
    have hirr_le :
        (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P ∧
            ¬H'.IsTopRegularOverPolyad Q η_H' 1, (#Q.support : ℝ)) ≤
          ∑ Q ∈ BadFine with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (fun Q hQ ↦ by
        obtain ⟨hQP, hnot⟩ := (mem_filter.1 hQ).2
        refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, hQP⟩
        by_contra! hg
        exact hnot (hGoodTrans Q (hchild_trans hQP) hg.1 hg.2).1)
        fun _ _ _ ↦ Nat.cast_nonneg _
    let a : ℝ := H.relativeDensity c P
    have hsum_P :
        (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ)) =
          #P.support := by
      rw [← Nat.cast_sum]
      exact congrArg Nat.cast ((sum_congr (by ext Q; simp) fun _ _ ↦ rfl).trans
        (Polyad3.sum_card_support_coarsen hstop.vertex_eq.le f hf_symm P))
    have hdev_a :
        (∑ Q : Polyad3 D.skeleton with Q.coarsen hstop.vertex_eq.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|) ≤
          (∑ Q ∈ BadFine with Q.coarsen hstop.vertex_eq.le f = P, (#Q.support : ℝ)) +
            2 * q₃ * η * #P.support := by
      refine (sum_le_sum (g := fun Q ↦
          (if Q ∈ BadFine then (#Q.support : ℝ) else 0) + 2 * q₃ * η * #Q.support)
        fun Q hQ ↦ ?_).trans ?_
      · have hQP := (mem_filter.1 hQ).2
        by_cases hbad : Q ∈ BadFine
        · simp only [hbad, ↓reduceIte]
          have h1 : |(H'.relativeDensity c Q : ℝ) - a| ≤ 1 := abs_sub_le_of_nonneg_of_le
            (mod_cast H'.relativeDensity_nonneg c Q) (mod_cast H'.relativeDensity_le_one c Q)
            (by dsimp [a]; exact_mod_cast H.relativeDensity_nonneg c P)
            (by dsimp [a]; exact_mod_cast H.relativeDensity_le_one c P)
          linarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) #Q.support),
            mul_nonneg (by positivity : 0 ≤ 2 * (q₃ : ℝ) * η) (Nat.cast_nonneg (α := ℝ) #Q.support)]
        · simp only [hbad, ↓reduceIte, zero_add]
          have hg : α_fine * (n : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1 := by
            simpa [BadFine, not_or] using hbad
          have hdev_Q := (hGoodTrans Q (hchild_trans hQP) hg.1 hg.2).2 c
          rw [hQP] at hdev_Q
          exact (mul_le_mul_of_nonneg_left hdev_Q (Nat.cast_nonneg _)).trans_eq (by ring)
      · rw [sum_add_distrib, ← mul_sum, hsum_P, ← sum_filter]
        exact le_of_eq (congrArg (· + _) (sum_congr (by ext Q; simp [and_comm]) fun _ _ ↦ rfl))
    have h4qη : 4 * (q₃ : ℝ) * η ≤ δ₁ ^ 2 / 4 := by
      have h1 : 4 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 2 :=
        (mul_le_mul (by linarith : 4 * (q₃ : ℝ) ≤ 4 * (q₃ + 1)) (min_le_right _ _)
          hη_pos.le (by positivity)).trans_eq (by field_simp; ring)
      nlinarith [hη_H'_pos, triadicFineH'Tol_le_quarter hF R K, show η_H' = δ₁ ^ 2 / 4 from rfl]
    have hdev_two := (H'.sum_card_support_mul_abs_relativeDensity_sub_le_two_mul
        hstop.vertex_eq.le f hf_symm P c a).trans <|
      mul_le_mul_of_nonneg_left
        ((le_of_eq (sum_congr (by ext Q; simp) fun _ _ ↦ rfl)).trans hdev_a) zero_le_two
    refine (add_le_add
      ((le_of_eq (sum_congr (by ext Q; simp [η_H']) fun _ _ ↦ rfl)).trans hirr_le)
      hdev_two).trans ?_
    linarith [hlt, mul_le_mul_of_nonneg_right h4qη (Nat.cast_nonneg (α := ℝ) #P.support)]
  -- Bound the total support of small and irregular fine polyads, hence irregular transversal ones.
  have hBadFine_sum :
      (∑ Q ∈ BadFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 12) * n.descFactorial 3 := by
    let SmallFine :=
      univ.filter fun Q : Polyad3 D.skeleton ↦ (#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3
    let IrregFine := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬H.IsTopRegularOverPolyad Q η 1
    have hsub : BadFine ⊆ SmallFine ∪ IrregFine := fun Q hQ ↦
      ((mem_filter.1 hQ).2).elim (fun h1 ↦ mem_union_left _ (mem_filter.2 ⟨mem_univ _, h1⟩))
        (fun h2 ↦ mem_union_right _ (mem_filter.2 ⟨mem_univ _, h2⟩))
    have hcard_S : (#SmallFine : ℝ) ≤ ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ) := by
      have hc := card_polyad3_le D.skeleton
      rw [hstop.vertex_eq, Fintype.card_fin] at hc
      exact_mod_cast (card_le_univ _).trans (hc.trans (Nat.le_succ _))
    have hSmall_le :
        (∑ Q ∈ SmallFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 24) * n.descFactorial 3 :=
      ((sum_le_sum fun Q hQ ↦ (mem_filter.1 hQ).2.le).trans_eq
        (by rw [sum_const, nsmul_eq_mul])).trans <|
      (mul_le_mul_of_nonneg_right hcard_S
        (mul_nonneg (triadicFineAlpha_pos hε hF R K t d).le (by positivity))).trans <|
      (by dsimp [α_fine, triadicFineAlpha]; field_simp; ring :
        _ = (δ₁ ^ 2 * ε₁ / 96) * (n : ℝ) ^ 3).trans_le <|
      (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)
    have hIrreg_le :
        (∑ Q ∈ IrregFine, (#Q.support : ℝ)) ≤ (δ₁ ^ 2 * ε₁ / 24) * n.descFactorial 3 := by
      simpa [IrregFine, hstop.polyads_univ, triadicFineMass] using hstop.top_reg.sum_card_support_le
    linarith [sum_le_sum_of_subset_of_nonneg hsub fun Q _ _ ↦ Nat.cast_nonneg (α := ℝ) #Q.support,
      sum_union_inter (s₁ := SmallFine) (s₂ := IrregFine)
        (f := fun Q : Polyad3 D.skeleton ↦ (#Q.support : ℝ)),
      sum_nonneg (s := SmallFine ∩ IrregFine) fun Q _ ↦ Nat.cast_nonneg (α := ℝ) #Q.support]
  have hTransIrreg_sum :
      (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1,
          (#P.support : ℝ)) ≤ (ε₁ / 2) * n.descFactorial 3 := by
    have hsum_charge :
        (δ₁ ^ 2 / 2) * (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧
            ¬H'.IsTopRegularOverPolyad P δ₁ 1, (#P.support : ℝ)) ≤
          3 * ∑ Q ∈ BadFine, (#Q.support : ℝ) := by
      rw [mul_sum]
      exact (sum_le_sum fun P hP ↦ hcharge_trans (mem_filter.1 hP).2.1 (mem_filter.1 hP).2.2).trans
        <| (sum_le_univ_sum_of_nonneg fun _ ↦
          mul_nonneg (by norm_num) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)).trans_eq <| by
            rw [← mul_sum, sum_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _)]
    exact le_of_mul_le_mul_left
      (hsum_charge.trans ((mul_le_mul_of_nonneg_left hBadFine_sum (by norm_num)).trans_eq
        (by ring))) (by positivity)
  -- Bound the support of nontransversal coarse polyads via equitability.
  have hNonTrans_sum :
      (∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, (#P.support : ℝ)) ≤
        (ε₁ / 4) * n.descFactorial 3 := by
    have hcard_nt :
        (∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, #P.support) ≤
          3 * (n / t + 1) * n ^ 2 :=
      Polyad3.sum_card_support_not_isTransversal_le_of_isEquipartition C.skeleton hC_adm.equi
    have h96 {m : ℕ} (hm : ⌈96 / ε₁⌉₊ ≤ m) : 96 ≤ ε₁ * m := by
      linarith [(div_le_iff₀ hε₁_pos).1 ((Nat.le_ceil _).trans (Nat.cast_le.2 hm))]
    have h96t := h96 (((Nat.le_add_left _ _).trans (le_max_right _ _)).trans hC_adm.parts_ge)
    have h96n := h96 ((Nat.le_add_left _ _).trans
      ((le_max_right 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV)))
    have ht_pos : (0 : ℝ) < t :=
      Nat.cast_pos.2 (((le_max_right t₀ 1).trans (le_max_left _ _)).trans hC_adm.parts_ge)
    have hdiv_t : 3 * ((n / t : ℕ) : ℝ) ≤ (ε₁ / 32) * n := by
      have h1 : ((n / t : ℕ) : ℝ) * t ≤ n := mod_cast Nat.div_mul_le_self n t
      linarith [le_of_mul_le_mul_right
        (by nlinarith : (96 * ((n / t : ℕ) : ℝ)) * t ≤ (ε₁ * n) * t) ht_pos]
    rw [← Nat.cast_sum]
    exact (mod_cast hcard_nt :
        ((∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, #P.support : ℕ) : ℝ) ≤
          ((3 * (n / t + 1) * n ^ 2 : ℕ) : ℝ)).trans <|
      (by push_cast; ring : _ = (3 * ((n / t : ℕ) : ℝ) + 3) * (n : ℝ) ^ 2).trans_le <|
      (mul_le_mul_of_nonneg_right (add_le_add hdiv_t (by linarith : (3 : ℝ) ≤ (ε₁ / 32) * n))
        (by positivity)).trans <|
      ((by ring : _ = (ε₁ / 16) * (n : ℝ) ^ 3).trans_le
        (mul_le_mul_of_nonneg_left hpow (by positivity))).trans_eq (by ring)
  -- Upgrade rank-1 top regularity to rank `R C.complexity` and sum the two exceptional charges.
  rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC_dec,
    div_le_iff₀ hdesc_pos]
  let S_tr := univ.filter fun P : Polyad3 C.skeleton ↦
    P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1
  let S_nt := univ.filter fun P : Polyad3 C.skeleton ↦ ¬P.IsTransversal
  refine (sum_le_sum_of_subset_of_nonneg (t := S_tr ∪ S_nt) (fun P hP ↦ ?_)
    fun _ _ _ ↦ Nat.cast_nonneg _).trans ?_
  · by_cases htr : P.IsTransversal
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, htr, fun h1 ↦ (mem_filter.1 hP).2 <|
        (IsTopRegularOverPolyad.of_rank_one_div_pow h1 (triadicSched1_pos hF K)).mono
          (triadicSched1_le F K)⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, htr⟩)
  rw [sum_union (disjoint_filter.2 fun _ _ h1 h2 ↦ h2 h1.1)]
  exact (add_le_add hTransIrreg_sum hNonTrans_sum).trans
    ((by ring_nf; exact le_rfl : _ ≤ (3 * ε₁ / 4) * n.descFactorial 3).trans
      (mul_le_mul_of_nonneg_right (by linarith [triadicEps1_le ε]) hdesc_pos.le))

/-- **Strong regular approximation of colored three-uniform hypergraphs.** For any finite palette
`κ`, tolerance `ε > 0`, positive regularity schedule `F`, rank schedule `R`, and vertex-cell floor
`t₀`, every colored three-uniform hypergraph `H` on at least
`regularityBound3 (Fintype.card κ) ε F R t₀` vertices admits a coloring `H'` and a triadic complex
`C` whose vertex cells form an equipartition into at least `t₀` cells and which satisfy
`H.IsStrongRegularApproximation3 H' C ε F R t₀`. -/
theorem exists_strong_regular_approximation3 (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V),
      C.VertexCellsControlled t₀ ∧ H.IsStrongRegularApproximation3 H' C ε F R t₀ := by
  obtain ⟨C, D, f, hC1, hC2, hC_adm, hstop⟩ := exists_stopped_triadic_pair H hε hF R t₀ hV
  obtain ⟨H', hApprox, hGoodTrans⟩ :=
    exists_coupled_recoloring_of_stopped_pair H hε hF R t₀ hV hC1 hC2 hstop
  have hC_dec : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hC_adm.polyads_univ ▸ mem_univ _
  have hK_cap : C.complexity ≤ triadicCompCap
      (triadicMaxSizes (Fintype.card κ) ε F R t₀).1
      (triadicMaxSizes (Fintype.card κ) ε F R t₀).2 :=
    C.complexity_le.trans (by dsimp [triadicCompCap]; gcongr)
  exact ⟨H', C,
    C.vertexCellsControlled_iff.2 ⟨hC_adm.equi,
      ((le_max_left t₀ 1).trans (le_max_left _ _)).trans hC_adm.parts_ge⟩,
    hApprox, hC_dec,
    C.skeleton.lowerSkeletonRegular_iff.2
      (hC_adm.lower_reg.isPairColorRegular (triadicSched1_le F _)),
    topRegularOverMostPolyads_of_stopped_pair H H' hε hF R t₀ hV hC_adm hstop hGoodTrans,
    C.complexityBounded_iff.2
      (hK_cap.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))⟩

end Colored3Graph

end TauCeti
