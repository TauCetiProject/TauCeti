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
import TauCeti.Order.Partition.Pi
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Strong regular approximation of colored three-uniform hypergraphs

Let `H` color the unordered triples of a finite vertex type `V` with a finite palette `κ`, let
`ε > 0`, let `F : ℕ → ℝ` be a positive regularity schedule, let `R : ℕ → ℕ` be a rank schedule, and
let `t₀ : ℕ` be a floor on the number of vertex cells. On any host of size at least
`regularityBound3 (Fintype.card κ) ε F R t₀`, this file constructs an explicit approximant coloring
`H'` and a bounded-complexity triadic complex `C` on `V` such that:

* the vertex cells of `C` form an equipartition into at least `t₀` cells
  (`TriadicComplex3.VertexCellsControlled`);
* `H` approximates `H'` within edit discrepancy `ε` (`Colored3Graph.Approximates3`);
* the selected polyads of `C` decompose all injective triples
  (`TriadicComplex3.IsPolyadDecomposition`);
* the lower skeleton of `C` is `F`-regular at its lower complexity
  (`PairSkeleton3.LowerSkeletonRegular`);
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples (`Colored3Graph.TopRegularOverMostPolyads`);
* `C.complexity` is bounded by `regularityBound3 (Fintype.card κ) ε F R t₀`
  (`TriadicComplex3.ComplexityBounded`).

## Proof outline

1. **Outer energy-increment loop.** Starting from an equipartition with at least `t₀` cells and an
   initial regular lower skeleton, each round refines the pair palette by rank-one top
   regularization (`Colored3Graph.exists_topRegularOverMostPolyads`) at tolerances scheduled at the
   current coarse complexity. If the polyad energy gap between the coarse complex `C` and its fine
   refinement `D` is already below a fixed threshold `g_top`, the loop stops. Otherwise, strong
   pair-color regularization (`PairColorSystem.exists_strong_recoloring_isPairColorRegular`)
   produces a new regular coarse complex `C'` whose pair coloring differs from `D` on so few pairs
   that the polyad energy drops by at most `g_top / 2`
   (`Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`), guaranteeing net progress of at least
   `g_top / 2` per round.
2. **Coupled triple recoloring.** Over the stopped pair `(C, D)`, canonical transversal fine polyads
   with large support and `H`-regularity have pairwise disjoint unordered-triple supports. On each
   such support, `exists_coupled_recoloring_abs_card_filter_sub_le` recolors `H` toward the coarse
   relative densities of `H` over `C` while preserving uniformity across all subpolyads. Role-swap
   symmetries (`Polyad3.exists_isCanonical_of_isTransversal`) transfer fine regularity and coarse
   density agreement from canonical fine polyads to every transversal large `H`-regular fine polyad.
3. **Coarse assembly and rank promotion.** Nontransversal coarse polyads carry a negligible fraction
   of injective triples once the vertex partition has enough equitable cells. On transversal coarse
   polyads, every fine child is transversal, so
   `Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le` transfers rank-one regularity from `D`
   to `C` at tolerance `(F₁ C.complexity) ^ 2 / 2 ^ (R C.complexity)`, and
   `Colored3Graph.IsTopRegularOverPolyad.of_rank_one_div_pow` promotes rank one to rank
   `R C.complexity`.

## Main definitions

* `TauCeti.regularityBound3`: host-size and complexity bound for strong three-uniform regular
  approximation.
* `TauCeti.Colored3Graph.IsStrongRegularApproximation3`: the strong arity-three regular
  approximation predicate.

## Main results

* `TauCeti.Colored3Graph.exists_strong_regular_approximation3`: existence of a strong regular
  approximation with controlled vertex cells on sufficiently large hosts.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorems 2.2 and 2.3 and Lemma 4.2.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset Finpartition Function Real

namespace TauCeti

/-! ### Arithmetic, relabeling, and Hoeffding helpers -/

section Preliminaries

private theorem pow_three_le_four_mul_descFactorial {n : ℕ} (hn : 4 ≤ n) :
    n ^ 3 ≤ 4 * n.descFactorial 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := Nat.exists_eq_add_of_le' hn
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, Nat.sub_zero,
    show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  calc (k + 4) ^ 3
      ≤ (k + 4) ^ 3 + (3 * k ^ 3 + 24 * k ^ 2 + 56 * k + 32) := Nat.le_add_right _ _
    _ = 4 * ((k + 2) * ((k + 3) * (k + 4))) := by ring

private theorem sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] (s t : Finset ι) {f : ι → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  linarith [sum_union_inter (s₁ := s) (s₂ := t) (f := f),
    sum_nonneg (s := s ∩ t) fun x _ ↦ hf x]

private theorem pairColorDensity_relabel {κ κ' V : Type*} (S : PairColorSystem κ V) (e : κ ≃ κ')
    (c : κ') (s t : Finset V) :
    pairColorDensity (S.relabel e) c s t = pairColorDensity S (e.symm c) s t := by
  classical
  rw [pairColorDensity_def, pairColorDensity_def]
  apply congrArg (· / _)
  apply congrArg Nat.cast
  apply congrArg card
  ext p
  simp only [mem_filter]
  by_cases h : p.1 = p.2
  · simp [h]
  · simp [h, Equiv.eq_symm_apply]

private theorem isPairColorRegular_relabel {κ κ' V : Type*} [Fintype V] [DecidableEq V]
    (S : PairSkeleton3 κ V) (e : κ ≃ κ') {ε : ℝ} :
    (S.relabel e).IsPairColorRegular ε ↔ S.IsPairColorRegular ε := by
  simp only [PairSkeleton3.isPairColorRegular_iff, PairSkeleton3.relabel_vertexPart,
    PairSkeleton3.relabel_pairColors, pairColorDensity_relabel]
  exact ⟨fun h c ↦ by simpa using h (e c), fun h c ↦ h (e.symm c)⟩

private theorem hoeffding_subpolyad_lt_one {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {S : PairSkeleton3 κ₂ V} (Q : Polyad3 S) {q₃ m : ℕ} {η α : ℝ}
    (hη : 0 < η) (hα : 0 < α) (hn1 : 1 ≤ Fintype.card V)
    (hsupp : α * (Fintype.card V : ℝ) ^ 3 ≤ (m : ℝ))
    (hhost : (q₃ + 6 : ℝ) < 2 * η ^ 2 * α * Fintype.card V) :
    2 * (Fintype.card (Subpolyad3 Q) + 1) * q₃ * exp (-2 * (η * m) ^ 2 / m) < 1 := by
  rcases Nat.eq_zero_or_pos q₃ with rfl | _
  · simp
  set n := Fintype.card V
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have hm_pos : (0 : ℝ) < m := (mul_pos hα (pow_pos hn_pos 3)).trans_le hsupp
  have h2_le_exp1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow_le : ((2 ^ (3 * n ^ 2) : ℕ) : ℝ) ≤ exp (3 * (n : ℝ) ^ 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc (2 : ℝ) ^ (3 * n ^ 2) ≤ (exp 1) ^ (3 * n ^ 2) :=
          pow_le_pow_left₀ zero_le_two h2_le_exp1 _
      _ = exp ((3 * n ^ 2 : ℕ) * 1) := (exp_nat_mul 1 (3 * n ^ 2)).symm
      _ = exp (3 * (n : ℝ) ^ 2) := congrArg exp (by push_cast; ring)
  have hcard_le : (Fintype.card (Subpolyad3 Q) : ℝ) ≤ ((2 ^ (3 * n ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast card_subpolyad3_le Q
  have h1_le_pow : (1 : ℝ) ≤ ((2 ^ (3 * n ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow (3 * n ^ 2) 2 two_pos
  have h4_le_exp2 : (4 : ℝ) ≤ exp 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this]
    calc (2 : ℝ) ^ 2 ≤ (exp 1) ^ 2 := pow_le_pow_left₀ zero_le_two h2_le_exp1 2
      _ = exp (2 * 1) := (exp_nat_mul 1 2).symm
      _ = exp 2 := by ring_nf
  have hfactor1 : 2 * ((Fintype.card (Subpolyad3 Q) : ℝ) + 1) ≤ exp (2 + 3 * (n : ℝ) ^ 2) := by
    calc 2 * ((Fintype.card (Subpolyad3 Q) : ℝ) + 1)
        ≤ 4 * ((2 ^ (3 * n ^ 2) : ℕ) : ℝ) := by linarith
      _ ≤ exp 2 * exp (3 * (n : ℝ) ^ 2) :=
          mul_le_mul h4_le_exp2 hpow_le (by positivity) (exp_pos 2).le
      _ = exp (2 + 3 * (n : ℝ) ^ 2) := (exp_add _ _).symm
  have hq₃_le : (q₃ : ℝ) ≤ exp q₃ := by linarith [add_one_le_exp (q₃ : ℝ)]
  have hexp_arg : -2 * (η * m) ^ 2 / m = -2 * η ^ 2 * m := by
    field_simp [hm_pos.ne']
  have hprod_le :
      2 * ((Fintype.card (Subpolyad3 Q) : ℝ) + 1) * q₃ * exp (-2 * (η * m) ^ 2 / m) ≤
        exp (2 + 3 * (n : ℝ) ^ 2 + q₃ - 2 * η ^ 2 * m) := by
    rw [hexp_arg]
    calc 2 * ((Fintype.card (Subpolyad3 Q) : ℝ) + 1) * q₃ * exp (-2 * η ^ 2 * m)
        ≤ exp (2 + 3 * (n : ℝ) ^ 2) * exp (q₃ : ℝ) * exp (-2 * η ^ 2 * m) := by
          refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
          exact mul_le_mul hfactor1 hq₃_le (Nat.cast_nonneg _) (exp_pos _).le
      _ = exp (2 + 3 * (n : ℝ) ^ 2 + q₃ - 2 * η ^ 2 * m) := by
          rw [← exp_add, ← exp_add]
          ring_nf
  refine hprod_le.trans_lt (exp_lt_one_iff.2 ?_)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn1
    calc (1 : ℝ) = 1 ^ 2 := by ring
      _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ zero_le_one this 2
  have hquad : 2 + 3 * (n : ℝ) ^ 2 + q₃ ≤ (q₃ + 6 : ℝ) * (n : ℝ) ^ 2 := by
    have hq_nn : (0 : ℝ) ≤ q₃ + 3 := by positivity
    calc 2 + 3 * (n : ℝ) ^ 2 + q₃ ≤ (q₃ + 3 : ℝ) * 1 + 3 * (n : ℝ) ^ 2 := by linarith
      _ ≤ (q₃ + 3 : ℝ) * (n : ℝ) ^ 2 + 3 * (n : ℝ) ^ 2 :=
          add_le_add_left (mul_le_mul_of_nonneg_left hn1R hq_nn) _
      _ = (q₃ + 6 : ℝ) * (n : ℝ) ^ 2 := by ring
  have hstrict : (q₃ + 6 : ℝ) * (n : ℝ) ^ 2 < 2 * η ^ 2 * α * (n : ℝ) ^ 3 := by
    calc (q₃ + 6 : ℝ) * (n : ℝ) ^ 2
        < (2 * η ^ 2 * α * n) * (n : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right hhost (pow_pos hn_pos 2)
      _ = 2 * η ^ 2 * α * (n : ℝ) ^ 3 := by ring
  have hcub : 2 * η ^ 2 * α * (n : ℝ) ^ 3 ≤ 2 * η ^ 2 * m := by
    calc 2 * η ^ 2 * α * (n : ℝ) ^ 3 = 2 * η ^ 2 * (α * (n : ℝ) ^ 3) := by ring
      _ ≤ 2 * η ^ 2 * m := mul_le_mul_of_nonneg_left hsupp (by positivity)
  linarith

end Preliminaries

/-! ### Parameter schedules, `regularityBound3`, and `IsStrongRegularApproximation3` -/

section Bounds

private noncomputable def triadicEps1 (ε : ℝ) : ℝ :=
  min ε 1

private noncomputable def triadicSched1 (F : ℕ → ℝ) (k : ℕ) : ℝ :=
  min 1 ((range (k + 1)).inf' nonempty_range_add_one F)

private noncomputable def triadicRank1Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicSched1 F k ^ 2 / (2 : ℝ) ^ R k

private noncomputable def triadicFineH'Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 / 4

private noncomputable def triadicFineTol (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  min (triadicEps1 ε / (24 * ((q₃ : ℝ) + 1)))
    (triadicFineH'Tol F R k ^ 2 / (8 * ((q₃ : ℝ) + 1)))

private noncomputable def triadicFineMass (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 * triadicEps1 ε / 24

private noncomputable def triadicEnergyGap (q₃ : ℕ) (ε : ℝ) : ℝ :=
  (triadicEps1 ε / (12 * ((q₃ : ℝ) + 1))) ^ 2

private noncomputable def triadicPairEdit (q₃ : ℕ) (ε : ℝ) : ℝ :=
  min (1 / 16) (triadicEnergyGap q₃ ε / 48)

private noncomputable def triadicInitParts (q₃ : ℕ) (ε : ℝ) (t₀ : ℕ) : ℕ :=
  max (max t₀ 1) (⌈8 / triadicPairEdit q₃ ε⌉₊ + ⌈96 / triadicEps1 ε⌉₊)

private def triadicCompCap (T M : ℕ) : ℕ :=
  T + M + T ^ 3 * M ^ 3

private noncomputable def triadicFineColorBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (T M : ℕ) : ℕ :=
  (range (T + 1)).sup fun t ↦
    (range (triadicCompCap T M + 1)).sup fun k ↦
      topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) M

private noncomputable def triadicOuterStep (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (TM : ℕ × ℕ) : ℕ × ℕ :=
  let dMax := triadicFineColorBound q₃ ε F R TM.1 TM.2
  ((range (dMax + 1)).sup fun d ↦
      strongPairColorPartBound d (triadicPairEdit q₃ ε)
        (fun k ↦ triadicSched1 F (k + (d + 1))) TM.1,
    max TM.2 (dMax + 1))

private noncomputable def triadicMaxSizes (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : ℕ × ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let T₀ := strongPairColorPartBound 1 (triadicPairEdit q₃ ε)
    (fun k ↦ triadicSched1 F (k + 2)) l₀
  (triadicOuterStep q₃ ε F R)^[⌊2 / triadicEnergyGap q₃ ε⌋₊] (T₀, 2)

/-- Host-size and complexity bound for strong regular approximation of a colored three-uniform
hypergraph with `q₃` top colors, error tolerance `ε`, regularity schedule `F`, rank schedule `R`,
and vertex-cell floor `t₀`. -/
noncomputable def regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : ℕ :=
  let l₀ := triadicInitParts q₃ ε t₀
  let δp := triadicPairEdit q₃ ε
  let TM := triadicMaxSizes q₃ ε F R t₀
  let Tmax := TM.1
  let Mmax := TM.2
  let Bcoarse := triadicCompCap Tmax Mmax
  let Dmax := triadicFineColorBound q₃ ε F R Tmax Mmax
  let hBasic := max Bcoarse (max 4 (l₀ + ⌈96 / triadicEps1 ε⌉₊))
  let hPairInit := strongPairColorHostBound 1 δp (fun k ↦ triadicSched1 F (k + 2)) l₀
  let hPairStep := (range (Dmax + 1)).sup fun d ↦
    strongPairColorHostBound d δp (fun k ↦ triadicSched1 F (k + (d + 1))) Tmax
  let hHoeff := (range (Bcoarse + 1)).sup fun k ↦
    ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R k ^ 2 *
      (triadicRank1Tol F R k ^ 2 * triadicEps1 ε /
        (96 * ((Tmax ^ 3 * Dmax ^ 3 : ℕ) + 1 : ℝ))))⌉₊ + 1
  max (max hBasic hPairInit) (max hPairStep hHoeff)

private theorem triadicEps1_pos {ε : ℝ} (hε : 0 < ε) : 0 < triadicEps1 ε :=
  lt_min hε zero_lt_one

private theorem triadicEps1_le (ε : ℝ) : triadicEps1 ε ≤ ε :=
  min_le_left _ _

private theorem triadicSched1_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (k : ℕ) :
    0 < triadicSched1 F k :=
  lt_min zero_lt_one ((lt_inf'_iff nonempty_range_add_one).2 fun m _ ↦ hF m)

private theorem triadicSched1_le_one (F : ℕ → ℝ) (k : ℕ) : triadicSched1 F k ≤ 1 :=
  min_le_left _ _

private theorem triadicSched1_le (F : ℕ → ℝ) (k : ℕ) : triadicSched1 F k ≤ F k :=
  (min_le_right _ _).trans (inf'_le F (self_mem_range_succ k))

private theorem triadicRank1Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicRank1Tol F R k := by
  have := triadicSched1_pos hF k
  unfold triadicRank1Tol
  positivity

private theorem triadicRank1Tol_le_one {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    triadicRank1Tol F R k ≤ 1 := by
  unfold triadicRank1Tol
  have h1 : triadicSched1 F k ^ 2 ≤ 1 := by
    calc triadicSched1 F k ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (triadicSched1_pos hF k).le (triadicSched1_le_one F k) 2
      _ = 1 := one_pow 2
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ R k := one_le_pow₀ (by norm_num)
  exact div_le_one_of_le₀ (h1.trans h2) (by positivity)

private theorem triadicFineH'Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicFineH'Tol F R k := by
  have := triadicRank1Tol_pos hF R k
  unfold triadicFineH'Tol
  positivity

private theorem triadicFineH'Tol_le_quarter {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    triadicFineH'Tol F R k ≤ 1 / 4 := by
  unfold triadicFineH'Tol
  have h1 : triadicRank1Tol F R k ^ 2 ≤ 1 := by
    calc triadicRank1Tol F R k ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (triadicRank1Tol_pos hF R k).le (triadicRank1Tol_le_one hF R k) 2
      _ = 1 := one_pow 2
  linarith

private theorem triadicFineTol_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicFineTol q₃ ε F R k := by
  have := triadicEps1_pos hε
  have := triadicFineH'Tol_pos hF R k
  unfold triadicFineTol
  exact lt_min (by positivity) (by positivity)

private theorem triadicFineMass_pos {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicFineMass ε F R k := by
  have := triadicEps1_pos hε
  have := triadicRank1Tol_pos hF R k
  unfold triadicFineMass
  positivity

private theorem triadicEnergyGap_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < triadicEnergyGap q₃ ε := by
  have := triadicEps1_pos hε
  unfold triadicEnergyGap
  positivity

private theorem triadicPairEdit_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < triadicPairEdit q₃ ε := by
  have := triadicEnergyGap_pos q₃ hε
  unfold triadicPairEdit
  exact lt_min (by norm_num) (by positivity)

private theorem triadicFineColorBound_mono (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    {T₁ T₂ M₁ M₂ : ℕ} (hT : T₁ ≤ T₂) (hM : M₁ ≤ M₂) :
    triadicFineColorBound q₃ ε F R T₁ M₁ ≤ triadicFineColorBound q₃ ε F R T₂ M₂ := by
  have hcap : triadicCompCap T₁ M₁ ≤ triadicCompCap T₂ M₂ := by
    dsimp [triadicCompCap]
    gcongr
  unfold triadicFineColorBound
  refine Finset.sup_le fun t ht ↦ ?_
  have ht' : t ∈ range (T₂ + 1) :=
    mem_range.2 ((mem_range.1 ht).trans_le (Nat.add_le_add_right hT 1))
  refine le_trans ?_
    (Finset.le_sup (f := fun t' ↦ (range (triadicCompCap T₂ M₂ + 1)).sup fun k ↦
      topRegularRefinementBound t' 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) M₂) ht')
  refine Finset.sup_le fun k hk ↦ ?_
  have hk' : k ∈ range (triadicCompCap T₂ M₂ + 1) :=
    mem_range.2 ((mem_range.1 hk).trans_le (Nat.add_le_add_right hcap 1))
  exact (topRegularRefinementBound_mono t 1 _ _ hM).trans
    (Finset.le_sup (f := fun j ↦ topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R j)
      (triadicFineMass ε F R j) M₂) hk')

private theorem topRegularRefinementBound_le_triadicFineColorBound (q₃ : ℕ) (ε : ℝ)
    (F : ℕ → ℝ) (R : ℕ → ℕ) {t T m M k : ℕ} (ht : t ≤ T) (hm : m ≤ M)
    (hk : k ≤ triadicCompCap T M) :
    topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R k) (triadicFineMass ε F R k) m ≤
      triadicFineColorBound q₃ ε F R T M := by
  have h1 := topRegularRefinementBound_mono t 1 (triadicFineTol q₃ ε F R k)
    (triadicFineMass ε F R k) hm
  have h2 := Finset.le_sup
    (f := fun j ↦ topRegularRefinementBound t 1 (triadicFineTol q₃ ε F R j)
      (triadicFineMass ε F R j) M)
    (mem_range.2 (by omega : k < triadicCompCap T M + 1))
  have h3 := Finset.le_sup
    (f := fun t' ↦ (range (triadicCompCap T M + 1)).sup fun j ↦
      topRegularRefinementBound t' 1 (triadicFineTol q₃ ε F R j) (triadicFineMass ε F R j) M)
    (mem_range.2 (by omega : t < T + 1))
  exact (h1.trans h2).trans h3

private theorem le_triadicOuterStep_fst (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (TM : ℕ × ℕ) :
    TM.1 ≤ (triadicOuterStep q₃ ε F R TM).1 := by
  dsimp only [triadicOuterStep]
  have h0 : 0 ∈ range (triadicFineColorBound q₃ ε F R TM.1 TM.2 + 1) :=
    mem_range.2 (Nat.succ_pos _)
  exact (le_strongPairColorPartBound 0 (triadicPairEdit_pos q₃ hε)
    (fun k ↦ triadicSched1_pos hF (k + (0 + 1))) TM.1).trans
    (Finset.le_sup
      (f := fun d ↦ strongPairColorPartBound d (triadicPairEdit q₃ ε)
        (fun k ↦ triadicSched1 F (k + (d + 1))) TM.1) h0)

private theorem le_triadicOuterStep_snd (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (TM : ℕ × ℕ) :
    TM.2 ≤ (triadicOuterStep q₃ ε F R TM).2 :=
  le_max_left _ _

-- Host-bound component extractors, proved here so main proofs never unfold `regularityBound3`.
private theorem coarseCap_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    triadicCompCap (triadicMaxSizes q₃ ε F R t₀).1 (triadicMaxSizes q₃ ε F R t₀).2 ≤
      regularityBound3 q₃ ε F R t₀ :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

private theorem basicFloor_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    max 4 (triadicInitParts q₃ ε t₀ + ⌈96 / triadicEps1 ε⌉₊) ≤
      regularityBound3 q₃ ε F R t₀ :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

private theorem pairInitHost_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) :
    strongPairColorHostBound 1 (triadicPairEdit q₃ ε) (fun k ↦ triadicSched1 F (k + 2))
      (triadicInitParts q₃ ε t₀) ≤ regularityBound3 q₃ ε F R t₀ :=
  (le_max_right _ _).trans (le_max_left _ _)

private theorem pairStepHost_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) {d t : ℕ}
    (hd : d ≤ triadicFineColorBound q₃ ε F R (triadicMaxSizes q₃ ε F R t₀).1
      (triadicMaxSizes q₃ ε F R t₀).2)
    (ht : t ≤ (triadicMaxSizes q₃ ε F R t₀).1) :
    strongPairColorHostBound d (triadicPairEdit q₃ ε) (fun k ↦ triadicSched1 F (k + (d + 1))) t ≤
      regularityBound3 q₃ ε F R t₀ := by
  have h1 := strongPairColorHostBound_mono d (triadicPairEdit q₃ ε)
    (fun k ↦ triadicSched1 F (k + (d + 1))) ht
  have h2 := Finset.le_sup
    (f := fun d' ↦ strongPairColorHostBound d' (triadicPairEdit q₃ ε)
      (fun k ↦ triadicSched1 F (k + (d' + 1))) (triadicMaxSizes q₃ ε F R t₀).1)
    (mem_range.2 (by omega : d < triadicFineColorBound q₃ ε F R
      (triadicMaxSizes q₃ ε F R t₀).1 (triadicMaxSizes q₃ ε F R t₀).2 + 1))
  exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_right _ _))

private theorem hoeffHost_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ)
    {k : ℕ}
    (hk : k ≤ triadicCompCap (triadicMaxSizes q₃ ε F R t₀).1 (triadicMaxSizes q₃ ε F R t₀).2) :
    ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R k ^ 2 *
      (triadicRank1Tol F R k ^ 2 * triadicEps1 ε /
        (96 * (((triadicMaxSizes q₃ ε F R t₀).1 ^ 3 *
          triadicFineColorBound q₃ ε F R (triadicMaxSizes q₃ ε F R t₀).1
            (triadicMaxSizes q₃ ε F R t₀).2 ^ 3 : ℕ) + 1 : ℝ))))⌉₊ + 1 ≤
      regularityBound3 q₃ ε F R t₀ := by
  have h1 := Finset.le_sup
    (f := fun j ↦ ⌈(q₃ + 6 : ℝ) / (2 * triadicFineTol q₃ ε F R j ^ 2 *
      (triadicRank1Tol F R j ^ 2 * triadicEps1 ε /
        (96 * (((triadicMaxSizes q₃ ε F R t₀).1 ^ 3 *
          triadicFineColorBound q₃ ε F R (triadicMaxSizes q₃ ε F R t₀).1
            (triadicMaxSizes q₃ ε F R t₀).2 ^ 3 : ℕ) + 1 : ℝ))))⌉₊ + 1)
    (mem_range.2 (by omega : k < triadicCompCap (triadicMaxSizes q₃ ε F R t₀).1
      (triadicMaxSizes q₃ ε F R t₀).2 + 1))
  exact h1.trans ((le_max_right _ _).trans (le_max_right _ _))

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

variable (H H' : Colored3Graph κ V) (C : TriadicComplex3 V) in
/-- **Strong regular approximation of a colored three-uniform hypergraph.** `H'` is within edit
discrepancy `ε` of `H`, `C` decomposes the injective triples, the lower skeleton of `C` is
`F`-regular, `H'` is `(F C.complexity, R C.complexity)`-top-regular over `C` off an `ε`-proportion
of the injective triples, and `C.complexity` is bounded by
`regularityBound3 (Fintype.card κ) ε F R t₀`. -/
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

end Bounds

/-! ### The outer energy-increment loop -/

section OuterLoop

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

private structure AdmissibleCoarse (ε : ℝ) (F : ℕ → ℝ) (t₀ : ℕ) (q₃ : ℕ)
    (C : TriadicComplex3 V) : Prop where
  equi : C.skeleton.vertexPart.IsEquipartition
  parts_ge : triadicInitParts q₃ ε t₀ ≤ #C.skeleton.vertexPart.parts
  polyads_univ : C.polyads = univ
  lower_reg : C.skeleton.LowerSkeletonRegular (triadicSched1 F)

private structure StoppedFine (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (H : Colored3Graph κ V) (C D : TriadicComplex3 V)
    (f : Fin D.pairColorCount → Fin C.pairColorCount) : Prop where
  d_le : D.pairColorCount ≤
    topRegularRefinementBound #C.skeleton.vertexPart.parts 1
      (triadicFineTol q₃ ε F R C.complexity) (triadicFineMass ε F R C.complexity) C.pairColorCount
  vertex_eq : D.skeleton.vertexPart = C.skeleton.vertexPart
  proj_color : ∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p
  proj_rev : ∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)
  polyads_univ : D.polyads = univ
  top_reg : H.TopRegularOverMostPolyads D (triadicFineTol q₃ ε F R C.complexity)
    (triadicFineMass ε F R C.complexity) 1
  energy_gap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ triadicEnergyGap q₃ ε

omit [DecidableEq κ] in
private theorem exists_initial_coarse {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ C₀ : TriadicComplex3 V,
      #C₀.skeleton.vertexPart.parts ≤
        strongPairColorPartBound 1 (triadicPairEdit (Fintype.card κ) ε)
          (fun k ↦ triadicSched1 F (k + 2)) (triadicInitParts (Fintype.card κ) ε t₀) ∧
      C₀.pairColorCount ≤ 2 ∧
      AdmissibleCoarse ε F t₀ (Fintype.card κ) C₀ := by
  set q₃ := Fintype.card κ
  set l₀ := triadicInitParts q₃ ε t₀
  set δp := triadicPairEdit q₃ ε
  have hδp : 0 < δp := triadicPairEdit_pos q₃ hε
  have hl₀_pos : 0 < l₀ := (le_max_right t₀ 1).trans (le_max_left _ _)
  have hl₀_le_n : l₀ ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.le_add_right l₀ _).trans
      ((le_max_right 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV))
  obtain ⟨P_init, hP_init, hcard_init⟩ :=
    Finpartition.exists_equipartition_card_eq (univ : Finset V) hl₀_pos.ne' hl₀_le_n
  let S_triv : PairColorSystem Unit V :=
    { color := fun _ ↦ ()
      rev := id
      rev_involutive := fun _ ↦ rfl
      color_rev := fun _ ↦ rfl }
  have hl₀_δ : 8 ≤ δp * #P_init.parts := by
    rw [hcard_init]
    have hceil : ⌈8 / δp⌉₊ ≤ l₀ := (Nat.le_add_right _ _).trans (le_max_right _ _)
    have hc : 8 / δp ≤ l₀ := (Nat.le_ceil _).trans (Nat.cast_le.2 hceil)
    linarith [(div_le_iff₀ hδp).1 hc]
  have hhost : strongPairColorHostBound (Fintype.card Unit) δp
      (fun k ↦ triadicSched1 F (k + 2)) #P_init.parts ≤ Fintype.card V := by
    rw [Fintype.card_unique, hcard_init]
    exact (pairInitHost_le_regularityBound3 q₃ ε F R t₀).trans hV
  obtain ⟨P₀, T₀, hP₀_le, hP₀_equi, hP₀_card, -, hT₀_reg, -⟩ :=
    S_triv.exists_strong_recoloring_isPairColorRegular P_init hP_init hδp hl₀_δ
      (fun k ↦ triadicSched1_pos hF (k + 2)) hhost
  rw [Fintype.card_unique, hcard_init] at hP₀_card
  let e₀ : Option Unit ≃ Fin (Fintype.card (Option Unit)) := Fintype.equivFin (Option Unit)
  have hcard_opt : Fintype.card (Option Unit) = 2 := by simp
  let C₀ : TriadicComplex3 V :=
    ⟨Fintype.card (Option Unit), (⟨P₀, T₀⟩ : PairSkeleton3 (Option Unit) V).relabel e₀, univ⟩
  have hC₀_vp : C₀.skeleton.vertexPart = P₀ := PairSkeleton3.relabel_vertexPart e₀
  have hC₀_pcc : C₀.pairColorCount = 2 := hcard_opt
  refine ⟨C₀, hC₀_vp.symm ▸ hP₀_card, hC₀_pcc.le, hC₀_vp.symm ▸ hP₀_equi, ?_, rfl, ?_⟩
  · rw [hC₀_vp]
    exact hcard_init.symm.trans_le (card_mono hP₀_le)
  · rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_fin]
    refine (isPairColorRegular_relabel (⟨P₀, T₀⟩ : PairSkeleton3 (Option Unit) V) e₀).2 ?_
    simpa only [hC₀_vp, hC₀_pcc] using hT₀_reg

private theorem exists_stopped_triadic_pair (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      #C.skeleton.vertexPart.parts ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).1 ∧
      C.pairColorCount ≤ (triadicMaxSizes (Fintype.card κ) ε F R t₀).2 ∧
      AdmissibleCoarse ε F t₀ (Fintype.card κ) C ∧
      StoppedFine (Fintype.card κ) ε F R H C D f := by
  let q₃ := Fintype.card κ
  let n := Fintype.card V
  let g_top := triadicEnergyGap q₃ ε
  let δp := triadicPairEdit q₃ ε
  have hg_pos : 0 < g_top := triadicEnergyGap_pos q₃ hε
  have hδp_pos : 0 < δp := triadicPairEdit_pos q₃ hε
  have hn4 : 4 ≤ n :=
    (le_max_left 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV)
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := by
    have hpow : 0 < n ^ 3 := pow_pos (by omega) 3
    have hle := pow_three_le_four_mul_descFactorial hn4
    exact Nat.cast_pos.2 (by omega)
  let step := triadicOuterStep q₃ ε F R
  let TM_max := triadicMaxSizes q₃ ε F R t₀
  let Good (C : TriadicComplex3 V) : Prop :=
    ∃ (D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      StoppedFine q₃ ε F R H C D f
  -- One round from a coarse complex bounded by `TM ≤ TM_max` either stops or advances energy by
  -- more than `g_top / 2` with new bounds `step TM`.
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
    have hCcomp : C.complexity ≤ triadicCompCap TM.1 TM.2 :=
      C.complexity_le.trans (by dsimp [triadicCompCap]; gcongr)
    have hd_le_step : D.pairColorCount ≤ triadicFineColorBound q₃ ε F R TM.1 TM.2 :=
      hDcard.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1 hC2 hCcomp)
    have hd_le_max : D.pairColorCount ≤ triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2 :=
      hd_le_step.trans (triadicFineColorBound_mono q₃ ε F R hTM1 hTM2)
    let d := D.pairColorCount
    have hl₀_δ : 8 ≤ δp * #C.skeleton.vertexPart.parts := by
      have hceil : ⌈8 / δp⌉₊ ≤ #C.skeleton.vertexPart.parts :=
        ((Nat.le_add_right _ _).trans (le_max_right _ _)).trans hC.parts_ge
      have hc : 8 / δp ≤ #C.skeleton.vertexPart.parts :=
        (Nat.le_ceil _).trans (Nat.cast_le.2 hceil)
      linarith [(div_le_iff₀ hδp_pos).1 hc]
    have hhost : strongPairColorHostBound (Fintype.card (Fin d)) δp
        (fun k ↦ triadicSched1 F (k + (d + 1))) #C.skeleton.vertexPart.parts ≤ n := by
      rw [Fintype.card_fin]
      exact (pairStepHost_le_regularityBound3 q₃ ε F R t₀ hd_le_max (hC1.trans hTM1)).trans hV
    obtain ⟨P', T', hP'_le, hP'_equi, hP'_card, -, hT'_reg, hT'_edits⟩ :=
      D.skeleton.pairColors.exists_strong_recoloring_isPairColorRegular C.skeleton.vertexPart
        hC.equi hδp_pos hl₀_δ (fun k ↦ triadicSched1_pos hF (k + (d + 1))) hhost
    rw [Fintype.card_fin] at hP'_card
    let e' : Option (Fin d) ≃ Fin (Fintype.card (Option (Fin d))) :=
      Fintype.equivFin (Option (Fin d))
    have hcard_opt : Fintype.card (Option (Fin d)) = d + 1 := by simp
    let C' : TriadicComplex3 V :=
      ⟨Fintype.card (Option (Fin d)), (⟨P', T'⟩ : PairSkeleton3 (Option (Fin d)) V).relabel e',
        univ⟩
    have hC'_vp : C'.skeleton.vertexPart = P' := PairSkeleton3.relabel_vertexPart e'
    have hC'_pcc : C'.pairColorCount = d + 1 := hcard_opt
    have hC'1 : #C'.skeleton.vertexPart.parts ≤ (step TM).1 := by
      rw [hC'_vp]
      have hmono := strongPairColorPartBound_mono d δp
        (fun k ↦ triadicSched1 F (k + (d + 1))) hC1
      have hsup := Finset.le_sup
        (f := fun d' ↦ strongPairColorPartBound d' δp
          (fun k ↦ triadicSched1 F (k + (d' + 1))) TM.1)
        (mem_range.2 (by omega : d < triadicFineColorBound q₃ ε F R TM.1 TM.2 + 1))
      exact (hP'_card.trans hmono).trans hsup
    have hC'2 : C'.pairColorCount ≤ (step TM).2 := by
      rw [hC'_pcc]
      exact (Nat.add_le_add_right hd_le_step 1).trans (le_max_right _ _)
    have hC'_adm : AdmissibleCoarse ε F t₀ q₃ C' := by
      refine ⟨hC'_vp.symm ▸ hP'_equi, ?_, rfl, ?_⟩
      · rw [hC'_vp]
        exact hC.parts_ge.trans (card_mono hP'_le)
      · rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_fin]
        refine (isPairColorRegular_relabel (⟨P', T'⟩ : PairSkeleton3 (Option (Fin d)) V) e').2 ?_
        simpa only [hC'_vp, hC'_pcc] using hT'_reg
    -- Bound the polyad energy drop from `D` to `C'` by `g_top / 2`.
    have hV_C'D : C'.skeleton.vertexPart ≤ D.skeleton.vertexPart := by
      rw [hC'_vp, hDV]
      exact hP'_le
    have hginj : Injective (fun c : Fin d ↦ e' (some c)) :=
      e'.injective.comp (Option.some_injective _)
    have hdrop := H.polyadEnergy_sub_le_of_pairRecoloring hV_C'D hginj
    have hcard_edits_le :
        #{p | C'.skeleton.pairColors.color p ≠ e' (some (D.skeleton.pairColors.color p))} ≤
          #{p | T'.color p ≠ some (D.skeleton.pairColors.color p)} :=
      card_le_card fun p hp ↦ by
        simp only [mem_filter, mem_univ, true_and, C', PairSkeleton3.relabel_pairColors,
          PairColorSystem.relabel_color, ne_eq, e'.injective.eq_iff] at hp ⊢
        exact hp
    have hdrop_le : H.polyadEnergy D.skeleton - H.polyadEnergy C'.skeleton ≤ g_top / 2 := by
      have hnum1 :
          ((6 * #{p | C'.skeleton.pairColors.color p ≠
              e' (some (D.skeleton.pairColors.color p))} * n : ℕ) : ℝ) ≤
            ((6 * #{p | T'.color p ≠ some (D.skeleton.pairColors.color p)} * n : ℕ) : ℝ) :=
        Nat.cast_le.2 (Nat.mul_le_mul_right n (Nat.mul_le_mul_left 6 hcard_edits_le))
      have hnum2 : ((6 * #{p | T'.color p ≠ some (D.skeleton.pairColors.color p)} * n : ℕ) : ℝ) ≤
          6 * δp * (n : ℝ) ^ 3 := by
        push_cast
        calc 6 * (#{p | T'.color p ≠ some (D.skeleton.pairColors.color p)} : ℝ) * n
            ≤ 6 * (δp * (n : ℝ) ^ 2) * n :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by convert hT'_edits) (by norm_num))
                (Nat.cast_nonneg _)
          _ = 6 * δp * (n : ℝ) ^ 3 := by ring
      have hpow_le : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) := by
        exact_mod_cast pow_three_le_four_mul_descFactorial hn4
      have h24 : 24 * δp ≤ g_top / 2 := by
        have : δp ≤ g_top / 48 := min_le_right _ _
        linarith
      calc H.polyadEnergy D.skeleton - H.polyadEnergy C'.skeleton
          ≤ ((6 * #{p | C'.skeleton.pairColors.color p ≠
                e' (some (D.skeleton.pairColors.color p))} * n : ℕ) : ℝ) /
              (n.descFactorial 3 : ℝ) := by convert hdrop
        _ ≤ (6 * δp * (n : ℝ) ^ 3) / (n.descFactorial 3 : ℝ) :=
            div_le_div_of_nonneg_right (hnum1.trans hnum2) hdesc_pos.le
        _ ≤ (6 * δp * (4 * (n.descFactorial 3 : ℝ))) / (n.descFactorial 3 : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow_le (by positivity)) hdesc_pos.le
        _ = 24 * δp := by field_simp [hdesc_pos.ne']; ring
        _ ≤ g_top / 2 := h24
    exact Or.inr ⟨C', hC'1, hC'2, hC'_adm, by linarith⟩
  -- Iterate up to `K_rounds := ⌊2 / g_top⌋₊`.
  obtain ⟨C₀, hC₀1, hC₀2, hC₀⟩ := exists_initial_coarse (κ := κ) hε hF R t₀ hV
  set TM₀ : ℕ × ℕ :=
    (strongPairColorPartBound 1 δp (fun k ↦ triadicSched1 F (k + 2))
      (triadicInitParts q₃ ε t₀), 2)
  set K_rounds := ⌊2 / g_top⌋₊
  have hstep_le_max : ∀ j ≤ K_rounds,
      (step^[j] TM₀).1 ≤ TM_max.1 ∧ (step^[j] TM₀).2 ≤ TM_max.2 := by
    intro j hj
    have hmon1 : ∀ a b, a ≤ b → (step^[a] TM₀).1 ≤ (step^[b] TM₀).1 := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b _ ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (le_triadicOuterStep_fst q₃ hε hF R _)
    have hmon2 : ∀ a b, a ≤ b → (step^[a] TM₀).2 ≤ (step^[b] TM₀).2 := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b _ ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (le_triadicOuterStep_snd q₃ ε F R _)
    exact ⟨hmon1 j K_rounds hj, hmon2 j K_rounds hj⟩
  have loop : ∀ j ≤ K_rounds,
      (∃ C, #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧
        C.pairColorCount ≤ (step^[j] TM₀).2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧ Good C) ∨
      (∃ C, #C.skeleton.vertexPart.parts ≤ (step^[j] TM₀).1 ∧
        C.pairColorCount ≤ (step^[j] TM₀).2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧
        (j : ℝ) * (g_top / 2) ≤ H.polyadEnergy C.skeleton) := by
    intro j hj
    induction j with
    | zero =>
      refine Or.inr ⟨C₀, hC₀1, hC₀2, hC₀, ?_⟩
      simpa using H.polyadEnergy_nonneg C₀.skeleton
    | succ j ih =>
      have hj' : j ≤ K_rounds := Nat.le_of_succ_le hj
      have hle1 : (step^[j] TM₀).1 ≤ (step^[j + 1] TM₀).1 := by
        rw [Function.iterate_succ_apply']
        exact le_triadicOuterStep_fst q₃ hε hF R _
      have hle2 : (step^[j] TM₀).2 ≤ (step^[j + 1] TM₀).2 := by
        rw [Function.iterate_succ_apply']
        exact le_triadicOuterStep_snd q₃ ε F R _
      obtain ⟨C, h1, h2, hC, hgood⟩ | ⟨C, h1, h2, hC, hE⟩ := ih hj'
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hgood⟩
      obtain ⟨hM1, hM2⟩ := hstep_le_max j hj'
      obtain hgood | ⟨C', h1', h2', hC', hE'⟩ := advance (step^[j] TM₀) hM1 hM2 C h1 h2 hC
      · exact Or.inl ⟨C, h1.trans hle1, h2.trans hle2, hC, hgood⟩
      refine Or.inr ⟨C', ?_, ?_, hC', ?_⟩
      · rwa [Function.iterate_succ_apply']
      · rwa [Function.iterate_succ_apply']
      · push_cast
        linarith
  have hK_gt : 1 < ((K_rounds + 1 : ℕ) : ℝ) * (g_top / 2) := by
    have hfloor : 2 / g_top < (K_rounds : ℝ) + 1 := Nat.lt_floor_add_one (2 / g_top)
    have hmul := (div_lt_iff₀ hg_pos).1 hfloor
    push_cast
    linarith
  obtain ⟨C, hC1, hC2, hC, D, f, hD⟩ :
      ∃ C, #C.skeleton.vertexPart.parts ≤ TM_max.1 ∧
        C.pairColorCount ≤ TM_max.2 ∧ AdmissibleCoarse ε F t₀ q₃ C ∧ Good C := by
    obtain hgood | ⟨C, hC1, hC2, hC, hE⟩ := loop K_rounds le_rfl
    · exact hgood
    obtain hgood | ⟨C', -, -, -, hE'⟩ := advance TM_max le_rfl le_rfl C hC1 hC2 hC
    · exact ⟨C, hC1, hC2, hC, hgood⟩
    push_cast at hK_gt
    linarith [H.polyadEnergy_le_one C'.skeleton]
  exact ⟨C, D, f, hC1, hC2, hC, hD⟩

end OuterLoop

/-! ### Coupled triple recoloring and coarse assembly -/

section Recoloring

private theorem fine_subpolyad_discrepancy_bound {η η_H' q₃_real w q_supp dev : ℝ}
    (hη_H'_pos : 0 < η_H') (hη_H'_le : η_H' ≤ 1 / 4)
    (hq_tol : 2 * q₃_real * η ≤ η_H' ^ 2 / 4)
    (hw_ge : η_H' * q_supp ≤ w) (hq_pos : 0 < q_supp) (hdev_nn : 0 ≤ dev)
    (hdev : dev * w ≤ 2 * q₃_real * η * q_supp) :
    dev + 2 * q₃_real * η ≤ η_H' := by
  have h1 : (dev * η_H') * q_supp ≤ (η_H' ^ 2 / 4) * q_supp := by
    calc (dev * η_H') * q_supp = dev * (η_H' * q_supp) := by ring
      _ ≤ dev * w := mul_le_mul_of_nonneg_left hw_ge hdev_nn
      _ ≤ 2 * q₃_real * η * q_supp := hdev
      _ ≤ (η_H' ^ 2 / 4) * q_supp := mul_le_mul_of_nonneg_right hq_tol hq_pos.le
  have h2 : dev * η_H' ≤ (η_H' / 4) * η_H' := by
    have := le_of_mul_le_mul_right h1 hq_pos
    linarith
  have h3 : dev ≤ η_H' / 4 := le_of_mul_le_mul_right h2 hη_H'_pos
  have h4 : η_H' ^ 2 / 4 ≤ η_H' / 4 := by
    have : η_H' ^ 2 ≤ η_H' * 1 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (by linarith) hη_H'_pos.le
    linarith
  linarith

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

/-- **Strong regular approximation of colored three-uniform hypergraphs.** For every positive error
tolerance `ε`, positive regularity schedule `F : ℕ → ℝ`, rank schedule `R : ℕ → ℕ`, and vertex-cell
floor `t₀`, any colored three-uniform hypergraph `H` on a vertex type `V` of cardinality at least
`regularityBound3 (Fintype.card κ) ε F R t₀` admits an explicit approximant `H'` and a triadic
complex `C` with `t₀`-controlled equitable vertex cells satisfying
`H.IsStrongRegularApproximation3 H' C ε F R t₀`. -/
theorem exists_strong_regular_approximation3 (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V),
      C.VertexCellsControlled t₀ ∧ H.IsStrongRegularApproximation3 H' C ε F R t₀ := by
  classical
  let q₃ := Fintype.card κ
  let n := Fintype.card V
  let ε₁ := triadicEps1 ε
  have hε₁_pos : 0 < ε₁ := triadicEps1_pos hε
  obtain ⟨C, D, f, hC1, hC2, hC_adm, hD_stop⟩ := exists_stopped_triadic_pair H hε hF R t₀ hV
  obtain ⟨hd_le, hDV, hproj_color, hproj_rev, hDpol, hDtop, hgap⟩ := hD_stop
  let K := C.complexity
  let t := #C.skeleton.vertexPart.parts
  let d := D.pairColorCount
  let δ₁ := triadicRank1Tol F R K
  let η_H' := triadicFineH'Tol F R K
  let η := triadicFineTol q₃ ε F R K
  have hδ₁_pos : 0 < δ₁ := triadicRank1Tol_pos hF R K
  have hη_H'_pos : 0 < η_H' := triadicFineH'Tol_pos hF R K
  have hη_H'_le : η_H' ≤ 1 / 4 := triadicFineH'Tol_le_quarter hF R K
  have hη_pos : 0 < η := triadicFineTol_pos q₃ hε hF R K
  have hn4 : 4 ≤ n :=
    (le_max_left 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV)
  have hn_pos : (0 : ℝ) < n := by positivity
  have hdesc_pos : (0 : ℝ) < n.descFactorial 3 := by
    have hpow : 0 < n ^ 3 := pow_pos (by omega) 3
    have hle := pow_three_le_four_mul_descFactorial hn4
    exact Nat.cast_pos.2 (by omega)
  have hf_symm : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p) :=
    fun p ↦ (hproj_color p).symm
  have hC_dec : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hC_adm.polyads_univ ▸ mem_univ _
  have hD_dec : D.IsPolyadDecomposition :=
    D.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hDpol ▸ mem_univ _
  -- Complexity bound for `C` and fine palette bound for `D`.
  let TM_max := triadicMaxSizes q₃ ε F R t₀
  have hK_cap : K ≤ triadicCompCap TM_max.1 TM_max.2 :=
    C.complexity_le.trans (by dsimp [triadicCompCap]; gcongr)
  have hC_comp : C.ComplexityBounded (regularityBound3 q₃ ε F R t₀) :=
    C.complexityBounded_iff.2 (hK_cap.trans (coarseCap_le_regularityBound3 q₃ ε F R t₀))
  have hd_max : d ≤ triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2 :=
    hd_le.trans (topRegularRefinementBound_le_triadicFineColorBound q₃ ε F R hC1 hC2 hK_cap)
  -- Large-support threshold `α_fine * n ^ 3` for fine polyads.
  let α_fine : ℝ := δ₁ ^ 2 * ε₁ / (96 * ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ))
  have hα_pos : 0 < α_fine := by positivity
  let idx : D.skeleton.vertexPart.parts ≃ Fin (Fintype.card D.skeleton.vertexPart.parts) :=
    Fintype.equivFin _
  let U_of (Q : Polyad3 D.skeleton) : Finset (Set.powersetCard V 3) :=
    Q.support.image tripleSet
  let GoodCanon : Finset (Polyad3 D.skeleton) :=
    univ.filter fun Q ↦ Q.IsCanonical idx ∧
      α_fine * (n : ℝ) ^ 3 ≤ (#Q.support : ℝ) ∧ H.IsTopRegularOverPolyad Q η 1
  have hGoodCanon_disj : ((GoodCanon : Set (Polyad3 D.skeleton))).PairwiseDisjoint U_of :=
    fun _ hQ₁ _ hQ₂ hne ↦ Polyad3.disjoint_image_tripleSet_of_isCanonical
      (mem_filter.1 hQ₁).2.1 (mem_filter.1 hQ₂).2.1 hne
  -- Coupled recoloring on each `Q ∈ GoodCanon`.
  have hrecolor_each (Q : Polyad3 D.skeleton) (hQ : Q ∈ GoodCanon) :
      ∃ xloc : Set.powersetCard V 3 → κ,
        (∀ s ∉ U_of Q, xloc s = H.color s) ∧
        (#{s ∈ U_of Q | xloc s ≠ H.color s} : ℝ) ≤
          (∑ c, |(#{s ∈ U_of Q | H.color s = c} : ℝ) -
              (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ) * #(U_of Q)|) / 2 +
            q₃ * (η * #(U_of Q)) ∧
        ∀ (W : Subpolyad3 Q) (c : κ),
          |(#{s ∈ W.support.image tripleSet | xloc s = c} : ℝ) -
              (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ) * #(W.support.image tripleSet)| ≤
            q₃ * (η * #(U_of Q)) +
              ∑ c₀, |(#{s ∈ W.support.image tripleSet | H.color s = c₀} : ℝ) -
                (#{s ∈ U_of Q | H.color s = c₀} : ℝ) / #(U_of Q) *
                  #(W.support.image tripleSet)| := by
    obtain ⟨hQ_can, hQ_large, -⟩ := (mem_filter.1 hQ).2
    have hQ_trans : Q.IsTransversal := hQ_can.isTransversal
    have hcard_U : #(U_of Q) = #Q.support :=
      Polyad3.card_image_tripleSet_of_subset hQ_trans Subset.rfl
    have hQ_pos : 0 < #Q.support := by
      have : (0 : ℝ) < #Q.support := (mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ_large
      exact Nat.cast_pos.1 this
    have hP_nonempty : (Q.coarsen hDV.le f).support.Nonempty :=
      (Finset.card_pos.1 hQ_pos).mono (Polyad3.support_subset_coarsen hDV.le f hf_symm Q)
    have hp_nonneg (c : κ) : 0 ≤ (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ) := by
      exact_mod_cast H.relativeDensity_nonneg c _
    have hp_sum : ∑ c : κ, (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ) = 1 := by
      exact_mod_cast H.sum_relativeDensity hP_nonempty
    have hW_sub (W : Subpolyad3 Q) : W.support.image tripleSet ⊆ U_of Q :=
      image_subset_image W.support_subset
    have ha_pos : 0 < η * (#(U_of Q) : ℝ) := by
      rw [hcard_U]
      exact mul_pos hη_pos (Nat.cast_pos.2 hQ_pos)
    -- Discharge the Hoeffding condition from `hoeffHost_le_regularityBound3`.
    let α_min : ℝ := δ₁ ^ 2 * ε₁ /
      (96 * (((TM_max.1 ^ 3 * triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2 ^ 3 : ℕ) + 1 : ℝ)))
    have hα_min_pos : 0 < α_min := by positivity
    have hα_min_le : α_min ≤ α_fine := by
      dsimp only [α_min, α_fine]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have htd : t ^ 3 * d ^ 3 ≤
          TM_max.1 ^ 3 * triadicFineColorBound q₃ ε F R TM_max.1 TM_max.2 ^ 3 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hC1 3) (Nat.pow_le_pow_left hd_max 3)
      exact_mod_cast Nat.add_le_add_right htd 1
    have hceil_n : ⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ + 1 ≤ n :=
      (hoeffHost_le_regularityBound3 q₃ ε F R t₀ hK_cap).trans hV
    have hhost_strict : (q₃ + 6 : ℝ) < 2 * η ^ 2 * α_fine * n := by
      have hlt : (q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min) < n := by
        calc (q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)
            ≤ ⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ := Nat.le_ceil _
          _ < (⌈(q₃ + 6 : ℝ) / (2 * η ^ 2 * α_min)⌉₊ + 1 : ℕ) := by push_cast; linarith
          _ ≤ n := by exact_mod_cast hceil_n
      have hmul1 : (q₃ + 6 : ℝ) < 2 * η ^ 2 * α_min * n := by
        have := (div_lt_iff₀ (by positivity : 0 < 2 * η ^ 2 * α_min)).1 hlt
        linarith
      have hmul2 : 2 * η ^ 2 * α_min * n ≤ 2 * η ^ 2 * α_fine * n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hα_min_le (by positivity)) hn_pos.le
      exact hmul1.trans_le hmul2
    have hhoeff : 2 * (Fintype.card (Subpolyad3 Q) + 1) * q₃ *
        exp (-2 * (η * #(U_of Q)) ^ 2 / #(U_of Q)) < 1 := by
      rw [hcard_U]
      exact hoeffding_subpolyad_lt_one Q hη_pos hα_pos (by omega) hQ_large hhost_strict
    obtain ⟨xloc, hx1, hx2, hx3⟩ :=
      exists_coupled_recoloring_abs_card_filter_sub_le (U_of Q) H.color hp_nonneg hp_sum
        (fun W : Subpolyad3 Q ↦ W.support.image tripleSet) hW_sub ha_pos hhoeff
    exact ⟨xloc, hx1, by convert hx2, fun W c ↦ by convert hx3 W c⟩
  choose xloc _ hxloc_edits hxloc_sub using fun Q : GoodCanon ↦ hrecolor_each Q.1 Q.2
  -- Glue the local recolorings on the pairwise disjoint supports `U_of Q` (`Q ∈ GoodCanon`).
  let H' : Colored3Graph κ V :=
    { color := fun s ↦
        if hs : ∃ Q ∈ GoodCanon, s ∈ U_of Q then
          xloc ⟨hs.choose, hs.choose_spec.1⟩ s
        else
          H.color s }
  have hH'_on {Q : Polyad3 D.skeleton} (hQ : Q ∈ GoodCanon) {s : Set.powersetCard V 3}
      (hs : s ∈ U_of Q) : H'.color s = xloc ⟨Q, hQ⟩ s := by
    have hex : ∃ Q' ∈ GoodCanon, s ∈ U_of Q' := ⟨Q, hQ, hs⟩
    have hH's : H'.color s = xloc ⟨hex.choose, hex.choose_spec.1⟩ s := dite_eq_left hex
    rw [hH's]
    have hQ_eq : hex.choose = Q := by
      by_contra hne
      exact Finset.disjoint_left.1 (hGoodCanon_disj hex.choose_spec.1 hQ hne)
        hex.choose_spec.2 hs
    congr 1
    exact Subtype.ext hQ_eq
  have hH'_out {s : Set.powersetCard V 3} (hs : ¬∃ Q ∈ GoodCanon, s ∈ U_of Q) :
      H'.color s = H.color s :=
    dite_eq_right hs
  -- Step A: `H` approximates `H'` within `ε`.
  have hApprox : H.Approximates3 H' ε := by
    rw [approximates3_iff]
    let Diff : Finset (Set.powersetCard V 3) := univ.filter fun s ↦ H.color s ≠ H'.color s
    have hncard : {s : Set.powersetCard V 3 | H.color s ≠ H'.color s}.ncard = #Diff := by
      have hset : {s : Set.powersetCard V 3 | H.color s ≠ H'.color s} = (Diff : Set _) := by
        ext s; simp [Diff]
      rw [hset, Set.ncard_coe_finset]
    have hDiff_sub : Diff ⊆ GoodCanon.biUnion fun Q ↦ {s ∈ U_of Q | H.color s ≠ H'.color s} := by
      intro s hs
      have hne := (mem_filter.1 hs).2
      by_cases hex : ∃ Q ∈ GoodCanon, s ∈ U_of Q
      · obtain ⟨Q, hQ, hsU⟩ := hex
        exact mem_biUnion.2 ⟨Q, hQ, mem_filter.2 ⟨hsU, hne⟩⟩
      · exact (hne (hH'_out hex).symm).elim
    have hDiff_disj : ((GoodCanon : Set (Polyad3 D.skeleton))).PairwiseDisjoint
        (fun Q ↦ {s ∈ U_of Q | H.color s ≠ H'.color s}) :=
      fun _ h1 _ h2 hne ↦ (hGoodCanon_disj h1 h2 hne).mono (filter_subset _ _) (filter_subset _ _)
    have hDiff_card : (#Diff : ℝ) ≤
        ∑ Q ∈ GoodCanon, (#{s ∈ U_of Q | H.color s ≠ H'.color s} : ℝ) := by
      rw [← Nat.cast_sum, ← card_biUnion hDiff_disj]
      exact_mod_cast card_le_card hDiff_sub
    have hQ_edit (Q : Polyad3 D.skeleton) (hQ : Q ∈ GoodCanon) :
        (#{s ∈ U_of Q | H.color s ≠ H'.color s} : ℝ) ≤
          (∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
              H.relativeDensity c (Q.coarsen hDV.le f)|) / 2 +
            q₃ * η * (#Q.support : ℝ) := by
      have hQ_trans : Q.IsTransversal := (mem_filter.1 hQ).2.1.isTransversal
      have hcard_U : #(U_of Q) = #Q.support :=
        Polyad3.card_image_tripleSet_of_subset hQ_trans Subset.rfl
      have hfilt_eq : {s ∈ U_of Q | H.color s ≠ H'.color s} =
          {s ∈ U_of Q | xloc ⟨Q, hQ⟩ s ≠ H.color s} := by
        refine filter_congr fun s hs ↦ ?_
        rw [hH'_on hQ hs, ne_comm]
      rw [hfilt_eq]
      refine (hxloc_edits ⟨Q, hQ⟩).trans ?_
      rw [hcard_U, ← mul_assoc]
      refine add_le_add_left (div_le_div_of_nonneg_right (le_of_eq ?_) zero_le_two) _
      refine sum_congr rfl fun c _ ↦ ?_
      rw [Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c hQ_trans Subset.rfl,
        ← relativeDensity_def, ← sub_mul, abs_mul,
        abs_of_nonneg (a := (#Q.support : ℝ)) (Nat.cast_nonneg _), mul_comm]
    have hsum_Q_supp : (∑ Q ∈ GoodCanon, (#Q.support : ℝ)) ≤ (n : ℝ) ^ 3 := by
      have h1 : ∑ Q ∈ GoodCanon, #Q.support ≤ ∑ Q : Polyad3 D.skeleton, #Q.support :=
        sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
      have h2 : ∑ Q : Polyad3 D.skeleton, #Q.support = n.descFactorial 3 := by
        simpa [hDpol] using hD_dec.sum_card_support
      have h3 : n.descFactorial 3 ≤ n ^ 3 := Nat.descFactorial_le_pow n 3
      exact_mod_cast (h1.trans_eq h2).trans h3
    have hsum_dev :
        (∑ Q ∈ GoodCanon, ∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hDV.le f)|) ≤
          q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3 := by
      rw [sum_comm]
      calc ∑ c, ∑ Q ∈ GoodCanon, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
              H.relativeDensity c (Q.coarsen hDV.le f)|
          ≤ ∑ c, ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
              H.relativeDensity c (Q.coarsen hDV.le f)| :=
            sum_le_sum fun c _ ↦ sum_le_univ_sum_of_nonneg fun Q ↦
              mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
        _ ≤ ∑ _c : κ, √(triadicEnergyGap q₃ ε) * (n.descFactorial 3 : ℝ) :=
            sum_le_sum fun c _ ↦
              H.sum_card_support_mul_abs_relativeDensity_coarsen_le hDV.le f hf_symm hgap c
        _ = q₃ * √(triadicEnergyGap q₃ ε) * (n.descFactorial 3 : ℝ) := by
            rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
        _ ≤ q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast Nat.descFactorial_le_pow n 3
    have hDiff_bound : 6 * (#Diff : ℝ) ≤ ε * (n : ℝ) ^ 3 := by
      have hsum_edit : (#Diff : ℝ) ≤
          (q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3) / 2 + q₃ * η * (n : ℝ) ^ 3 := by
        calc (#Diff : ℝ) ≤ ∑ Q ∈ GoodCanon,
                ((∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
                    H.relativeDensity c (Q.coarsen hDV.le f)|) / 2 +
                  q₃ * η * (#Q.support : ℝ)) :=
              hDiff_card.trans (sum_le_sum fun Q hQ ↦ hQ_edit Q hQ)
          _ = (∑ Q ∈ GoodCanon, ∑ c, (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) -
                  H.relativeDensity c (Q.coarsen hDV.le f)|) / 2 +
                q₃ * η * (∑ Q ∈ GoodCanon, (#Q.support : ℝ)) := by
              rw [sum_add_distrib, ← sum_div, ← mul_sum]
          _ ≤ (q₃ * √(triadicEnergyGap q₃ ε) * (n : ℝ) ^ 3) / 2 + q₃ * η * (n : ℝ) ^ 3 :=
              add_le_add (div_le_div_of_nonneg_right hsum_dev zero_le_two)
                (mul_le_mul_of_nonneg_left hsum_Q_supp (by positivity))
      have hsqrt : √(triadicEnergyGap q₃ ε) = ε₁ / (12 * ((q₃ : ℝ) + 1)) := by
        unfold triadicEnergyGap
        exact Real.sqrt_sq (by positivity)
      have hterm1 : 3 * q₃ * √(triadicEnergyGap q₃ ε) ≤ ε₁ / 4 := by
        rw [hsqrt]
        have : (q₃ : ℝ) ≤ (q₃ : ℝ) + 1 := by linarith
        calc 3 * (q₃ : ℝ) * (ε₁ / (12 * ((q₃ : ℝ) + 1)))
            ≤ 3 * ((q₃ : ℝ) + 1) * (ε₁ / (12 * ((q₃ : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num))
                (by positivity)
          _ = ε₁ / 4 := by field_simp; ring
      have hterm2 : 6 * q₃ * η ≤ ε₁ / 4 := by
        have hη_le : η ≤ ε₁ / (24 * ((q₃ : ℝ) + 1)) := min_le_left _ _
        have : (q₃ : ℝ) ≤ (q₃ : ℝ) + 1 := by linarith
        calc 6 * (q₃ : ℝ) * η
            ≤ 6 * ((q₃ : ℝ) + 1) * (ε₁ / (24 * ((q₃ : ℝ) + 1))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num)) hη_le hη_pos.le
                (by positivity)
          _ = ε₁ / 4 := by field_simp; ring
      have hcoef : 3 * q₃ * √(triadicEnergyGap q₃ ε) + 6 * q₃ * η ≤ ε :=
        (add_le_add hterm1 hterm2).trans ((by linarith : ε₁ / 4 + ε₁ / 4 ≤ ε₁).trans
          (triadicEps1_le ε))
      calc 6 * (#Diff : ℝ)
          ≤ (3 * q₃ * √(triadicEnergyGap q₃ ε) + 6 * q₃ * η) * (n : ℝ) ^ 3 := by
            linarith
        _ ≤ ε * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hcoef (by positivity)
    rw [editDiscrepancy3_def, Nat.card_eq_fintype_card, hncard]
    push_cast
    exact (div_le_iff₀ (pow_pos hn_pos 3)).2 hDiff_bound
  -- Step B: On every `Q ∈ GoodCanon`, `H'` is `(η_H', 1)`-top-regular and has density within
  -- `2 * q₃ * η` of `H`'s coarse density.
  have hGoodCanon_props (Q : Polyad3 D.skeleton) (hQ : Q ∈ GoodCanon) :
      H'.IsTopRegularOverPolyad Q η_H' 1 ∧
        ∀ c : κ, |(H'.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hDV.le f)| ≤ 2 * q₃ * η := by
    obtain ⟨hQ_can, hQ_large, hQ_Hreg⟩ := (mem_filter.1 hQ).2
    have hQ_trans : Q.IsTransversal := hQ_can.isTransversal
    have hcard_U : #(U_of Q) = #Q.support :=
      Polyad3.card_image_tripleSet_of_subset hQ_trans Subset.rfl
    have hQ_pos : (0 : ℝ) < #Q.support := (mul_pos hα_pos (pow_pos hn_pos 3)).trans_le hQ_large
    have hW_count (W : Subpolyad3 Q) (c : κ) :
        |(H'.relDensityOn c W.support : ℝ) - H.relativeDensity c (Q.coarsen hDV.le f)| *
          #W.support ≤ 2 * q₃ * η * #Q.support := by
      have hcard_W : #(W.support.image tripleSet) = #W.support :=
        Polyad3.card_image_tripleSet_of_subset hQ_trans W.support_subset
      have hfilt_W : {s ∈ W.support.image tripleSet | H'.color s = c} =
          {s ∈ W.support.image tripleSet | xloc ⟨Q, hQ⟩ s = c} := by
        refine filter_congr fun s hs ↦ ?_
        rw [hH'_on hQ (image_subset_image W.support_subset hs)]
      have hcount_H' : (#{s ∈ W.support.image tripleSet | xloc ⟨Q, hQ⟩ s = c} : ℝ) =
          (H'.relDensityOn c W.support : ℝ) * #W.support := by
        rw [← hfilt_W]
        exact Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H' c hQ_trans W.support_subset
      have hsub := hxloc_sub ⟨Q, hQ⟩ W c
      rw [hcount_H', hcard_W, hcard_U, ← sub_mul, abs_mul,
        abs_of_nonneg (a := (#W.support : ℝ)) (Nat.cast_nonneg _)] at hsub
      refine hsub.trans ?_
      have hsum_H : ∑ c₀ : κ,
          |(#{s ∈ W.support.image tripleSet | H.color s = c₀} : ℝ) -
            (#{s ∈ U_of Q | H.color s = c₀} : ℝ) / #Q.support * #W.support| ≤
          q₃ * (η * #Q.support) := by
        calc _ ≤ ∑ _c₀ : κ, η * (#Q.support : ℝ) := by
              refine sum_le_sum fun c₀ _ ↦ ?_
              rw [Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c₀ hQ_trans
                  W.support_subset,
                Polyad3.card_filter_image_tripleSet_eq_mul_relDensityOn H c₀ hQ_trans Subset.rfl,
                mul_div_cancel_right₀ _ hQ_pos.ne', ← relativeDensity_def, ← sub_mul, abs_mul,
                abs_of_nonneg (a := (#W.support : ℝ)) (Nat.cast_nonneg _)]
              have := hQ_Hreg.abs_relDensityOn_unionSupport_sub_mul_card_le_of_card_le c₀
                (Fintype.card_fin 1).le (fun _ ↦ W)
              rwa [Subpolyad3.unionSupport_unique] at this
          _ = q₃ * (η * #Q.support) := by rw [sum_const, card_univ, nsmul_eq_mul]
      linarith
    have hrel_dev (c : κ) :
        |(H'.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hDV.le f)| ≤
          2 * q₃ * η := by
      let W_full := Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂
      have hW_full := hW_count W_full c
      rw [Subpolyad3.support_ofSubcells_cells, ← relativeDensity_def] at hW_full
      exact le_of_mul_le_mul_right hW_full hQ_pos
    refine ⟨isTopRegularOverPolyad_one_iff.2 fun c W hW ↦ ?_, hrel_dev⟩
    have hq_tol : 2 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 4 := by
      have hη_le : η ≤ η_H' ^ 2 / (8 * ((q₃ : ℝ) + 1)) := min_le_right _ _
      have hq_le : (q₃ : ℝ) ≤ (q₃ : ℝ) + 1 := by linarith
      calc 2 * (q₃ : ℝ) * η
          ≤ 2 * ((q₃ : ℝ) + 1) * (η_H' ^ 2 / (8 * ((q₃ : ℝ) + 1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq_le zero_le_two) hη_le hη_pos.le
              (by positivity)
        _ = η_H' ^ 2 / 4 := by field_simp; ring
    have htri : |(H'.relDensityOn c W.support : ℝ) - H'.relativeDensity c Q| ≤
        |(H'.relDensityOn c W.support : ℝ) - H.relativeDensity c (Q.coarsen hDV.le f)| +
          |(H'.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hDV.le f)| := by
      have := abs_sub_le (H'.relDensityOn c W.support : ℝ)
        (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ) (H'.relativeDensity c Q : ℝ)
      rwa [abs_sub_comm (H.relativeDensity c (Q.coarsen hDV.le f) : ℝ)] at this
    have hdisc := fine_subpolyad_discrepancy_bound hη_H'_pos hη_H'_le hq_tol hW hQ_pos
      (abs_nonneg _) (hW_count W c)
    linarith [hrel_dev c]
  -- Transfer Step B to every transversal, large, `H`-regular fine polyad via role swaps.
  let GoodTrans : Polyad3 D.skeleton → Prop := fun Q' ↦
    Q'.IsTransversal ∧ α_fine * (n : ℝ) ^ 3 ≤ (#Q'.support : ℝ) ∧
      H.IsTopRegularOverPolyad Q' η 1
  have hGoodTrans_props {Q' : Polyad3 D.skeleton} (hQ' : GoodTrans Q') :
      H'.IsTopRegularOverPolyad Q' η_H' 1 ∧
        ∀ c : κ, |(H'.relativeDensity c Q' : ℝ) -
          H.relativeDensity c (Q'.coarsen hDV.le f)| ≤ 2 * q₃ * η := by
    obtain ⟨Q, hQ_can, hQ_card, hQ_rel, hQ_crel, hQ_reg⟩ :=
      Polyad3.exists_isCanonical_of_isTransversal (κ := κ) hDV hproj_rev idx hQ'.1
    have hQ_mem : Q ∈ GoodCanon := mem_filter.2 ⟨mem_univ _, hQ_can,
      by rw [hQ_card]; exact hQ'.2.1, (hQ_reg H η).2 hQ'.2.2⟩
    obtain ⟨hH'reg, hH'dev⟩ := hGoodCanon_props Q hQ_mem
    refine ⟨(hQ_reg H' η_H').1 hH'reg, fun c ↦ ?_⟩
    rw [← hQ_rel H' c, ← hQ_crel H c]
    exact hH'dev c
  -- Step C: Coarse top regularity of `H'` over most polyads of `C`.
  have hTopCoarse : H'.TopRegularOverMostPolyads C (F K) ε (R K) := by
    -- Charge every transversal coarse polyad failing `(δ₁, 1)`-top regularity in `H'` to its
    -- small or `H`-irregular fine children.
    let BadTransFine : Finset (Polyad3 D.skeleton) :=
      univ.filter fun Q ↦ (#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3 ∨ ¬H.IsTopRegularOverPolyad Q η 1
    have hcharge_trans {P : Polyad3 C.skeleton} (hP_trans : P.IsTransversal)
        (hP_irreg : ¬H'.IsTopRegularOverPolyad P δ₁ 1) :
        (δ₁ ^ 2 / 2) * (#P.support : ℝ) ≤
          3 * ∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ) := by
      by_contra! hlt
      refine hP_irreg (H'.isTopRegularOverPolyad_of_sum_coarsen_le hDV.le f hf_symm
        hη_H'_pos.le hδ₁_pos (θ := (3 / 4) * δ₁ ^ 2)
        (by dsimp [η_H', triadicFineH'Tol]; linarith) fun c ↦ ?_)
      have hchild_trans {Q : Polyad3 D.skeleton} (hQP : Q.coarsen hDV.le f = P) :
          Q.IsTransversal :=
        (Polyad3.isTransversal_coarsen_iff hDV f Q).1 (hQP.symm ▸ hP_trans)
      have hirr_le :
          (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P ∧
              ¬H'.IsTopRegularOverPolyad Q η_H' 1, (#Q.support : ℝ)) ≤
            ∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun Q hQ ↦ ?_) fun _ _ _ ↦ Nat.cast_nonneg _
        obtain ⟨hQP, hnot⟩ := (mem_filter.1 hQ).2
        refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, hQP⟩
        by_contra! hgood
        exact hnot (hGoodTrans_props ⟨hchild_trans hQP, hgood.1, hgood.2⟩).1
      let a : ℝ := (H.relativeDensity c P : ℝ)
      have hsum_P : (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) =
          #P.support := by
        rw [← Nat.cast_sum]
        exact congrArg (Nat.cast (R := ℝ))
          (by convert Polyad3.sum_card_support_coarsen hDV.le f hf_symm P)
      have hP_avg : (#P.support : ℝ) * |(H'.relativeDensity c P : ℝ) - a| ≤
          ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a| := by
        have hsplit := H'.relDensityOn_sub_mul_card_eq_sum_inter_support D.skeleton c P.support a
        rw [← relativeDensity_def] at hsplit
        have hsum_eq : ∑ Q : Polyad3 D.skeleton,
              ((H'.relDensityOn c (P.support ∩ Q.support) : ℝ) - a) * #(P.support ∩ Q.support) =
            ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
              ((H'.relativeDensity c Q : ℝ) - a) * #Q.support := by
          rw [sum_filter]
          refine sum_congr rfl fun Q _ ↦ ?_
          by_cases hQP : Q.coarsen hDV.le f = P
          · have hinter : P.support ∩ Q.support = Q.support :=
              inter_eq_right.2 (hQP ▸ Polyad3.support_subset_coarsen hDV.le f hf_symm Q)
            simp [hQP, hinter, relativeDensity_def]
          · have hinter : P.support ∩ Q.support = ∅ :=
              disjoint_iff_inter_eq_empty.1
                ((Polyad3.pairwise_disjoint_support (Ne.symm hQP)).mono_right
                  (Polyad3.support_subset_coarsen hDV.le f hf_symm Q))
            simp [hQP, hinter]
        rw [mul_comm, ← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) #P.support), ← abs_mul,
          hsplit, hsum_eq]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (a := (#Q.support : ℝ)) (Nat.cast_nonneg _), mul_comm]
      have hdev_two :
          (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) ≤
          2 * ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a| := by
        calc _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
              (#Q.support : ℝ) * (|(H'.relativeDensity c Q : ℝ) - a| +
                |(H'.relativeDensity c P : ℝ) - a|) := by
              refine sum_le_sum fun Q _ ↦ mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              have := abs_sub_le (H'.relativeDensity c Q : ℝ) a (H'.relativeDensity c P : ℝ)
              rwa [abs_sub_comm a] at this
          _ = (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
                (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|) +
              (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) *
                |(H'.relativeDensity c P : ℝ) - a| := by
              simp_rw [mul_add]
              rw [sum_add_distrib, ← sum_mul]
          _ = (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
                (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|) +
              (#P.support : ℝ) * |(H'.relativeDensity c P : ℝ) - a| := by
              rw [hsum_P]
          _ ≤ 2 * ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
                (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a| := by linarith
      have hdev_a :
          (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|) ≤
          (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
            2 * q₃ * η * (#P.support : ℝ) := by
        have hterm (Q : Polyad3 D.skeleton)
            (hQ : Q ∈ univ.filter fun Q : Polyad3 D.skeleton ↦ Q.coarsen hDV.le f = P) :
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a| ≤
              (if Q ∈ BadTransFine then (#Q.support : ℝ) else 0) +
                2 * q₃ * η * (#Q.support : ℝ) := by
          have hQP := (mem_filter.1 hQ).2
          by_cases hbad : Q ∈ BadTransFine
          · simp only [hbad, ↓reduceIte]
            have h1 : |(H'.relativeDensity c Q : ℝ) - (H.relativeDensity c P : ℝ)| ≤ 1 :=
              abs_sub_le_of_nonneg_of_le (mod_cast H'.relativeDensity_nonneg c Q)
                (mod_cast H'.relativeDensity_le_one c Q) (mod_cast H.relativeDensity_nonneg c P)
                (mod_cast H.relativeDensity_le_one c P)
            calc (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|
                ≤ (#Q.support : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
              _ ≤ (#Q.support : ℝ) + 2 * q₃ * η * (#Q.support : ℝ) := by
                  linarith [mul_nonneg (by positivity : 0 ≤ 2 * (q₃ : ℝ) * η)
                    (Nat.cast_nonneg (α := ℝ) #Q.support)]
          · simp only [hbad, ↓reduceIte, zero_add]
            have hgood : ¬((#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3 ∨
                ¬H.IsTopRegularOverPolyad Q η 1) := fun h ↦
              hbad (mem_filter.2 ⟨mem_univ _, h⟩)
            push Not at hgood
            have hdev_Q := (hGoodTrans_props ⟨hchild_trans hQP, hgood.1, hgood.2⟩).2 c
            rw [hQP] at hdev_Q
            calc (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - a|
                ≤ (#Q.support : ℝ) * (2 * q₃ * η) :=
                  mul_le_mul_of_nonneg_left hdev_Q (Nat.cast_nonneg _)
              _ = 2 * q₃ * η * (#Q.support : ℝ) := by ring
        calc _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
              ((if Q ∈ BadTransFine then (#Q.support : ℝ) else 0) +
                2 * q₃ * η * (#Q.support : ℝ)) := sum_le_sum hterm
          _ = (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
                2 * q₃ * η * (#P.support : ℝ) := by
              rw [sum_add_distrib, ← mul_sum, hsum_P, ← sum_filter]
              congr 1
              refine sum_congr ?_ fun _ _ ↦ rfl
              ext Q
              simp only [mem_filter, mem_univ, true_and, and_comm]
      have h4qη : 4 * (q₃ : ℝ) * η ≤ δ₁ ^ 2 / 4 := by
        have hη_le : η ≤ η_H' ^ 2 / (8 * ((q₃ : ℝ) + 1)) := min_le_right _ _
        have hq_le : (q₃ : ℝ) ≤ (q₃ : ℝ) + 1 := by linarith
        have h1 : 4 * (q₃ : ℝ) * η ≤ η_H' ^ 2 / 2 := by
          calc 4 * (q₃ : ℝ) * η
              ≤ 4 * ((q₃ : ℝ) + 1) * (η_H' ^ 2 / (8 * ((q₃ : ℝ) + 1))) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hq_le (by norm_num)) hη_le hη_pos.le
                  (by positivity)
            _ = η_H' ^ 2 / 2 := by field_simp; ring
        have h2 : η_H' ^ 2 / 2 ≤ η_H' := by
          have : η_H' ^ 2 ≤ η_H' * 1 := by
            rw [sq]
            exact mul_le_mul_of_nonneg_left (by linarith) hη_H'_pos.le
          linarith
        have h3 : η_H' = δ₁ ^ 2 / 4 := rfl
        linarith
      have hdev_bound :
          (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
            (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) ≤
          2 * (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
            (δ₁ ^ 2 / 4) * (#P.support : ℝ) := by
        calc _ ≤ 2 * ((∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
              2 * q₃ * η * (#P.support : ℝ)) :=
              hdev_two.trans (mul_le_mul_of_nonneg_left hdev_a zero_le_two)
          _ = 2 * (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
              (4 * q₃ * η) * (#P.support : ℝ) := by ring
          _ ≤ 2 * (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
              (δ₁ ^ 2 / 4) * (#P.support : ℝ) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right h4qη (Nat.cast_nonneg _))
      have htotal :
          (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P ∧
              ¬H'.IsTopRegularOverPolyad Q η_H' 1, (#Q.support : ℝ)) +
            (∑ Q : Polyad3 D.skeleton with Q.coarsen hDV.le f = P,
              (#Q.support : ℝ) * |(H'.relativeDensity c Q : ℝ) - H'.relativeDensity c P|) <
          (3 / 4) * δ₁ ^ 2 * (#P.support : ℝ) := by
        calc _ ≤ 3 * (∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ)) +
              (δ₁ ^ 2 / 4) * (#P.support : ℝ) := by linarith [hirr_le, hdev_bound]
          _ < (δ₁ ^ 2 / 2) * (#P.support : ℝ) + (δ₁ ^ 2 / 4) * (#P.support : ℝ) :=
              add_lt_add_of_lt_of_le hlt le_rfl
          _ = (3 / 4) * δ₁ ^ 2 * (#P.support : ℝ) := by ring
      convert htotal.le
    -- Sum the charge over all transversal irregular coarse polyads.
    have hBadTransFine_sum :
        (∑ Q ∈ BadTransFine, (#Q.support : ℝ)) ≤
          (δ₁ ^ 2 * ε₁ / 12) * (n.descFactorial 3 : ℝ) := by
      let SmallFine := univ.filter fun Q : Polyad3 D.skeleton ↦
        (#Q.support : ℝ) < α_fine * (n : ℝ) ^ 3
      let IrregFine := univ.filter fun Q : Polyad3 D.skeleton ↦
        ¬H.IsTopRegularOverPolyad Q η 1
      have hsub : BadTransFine ⊆ SmallFine ∪ IrregFine := fun Q hQ ↦ by
        rcases (mem_filter.1 hQ).2 with h1 | h2
        · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h1⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h2⟩)
      have hunion : (∑ Q ∈ BadTransFine, (#Q.support : ℝ)) ≤
          (∑ Q ∈ SmallFine, (#Q.support : ℝ)) + (∑ Q ∈ IrregFine, (#Q.support : ℝ)) :=
        (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.cast_nonneg _).trans
          (sum_union_le_of_nonneg SmallFine IrregFine fun _ ↦ Nat.cast_nonneg _)
      have hSmall_le : (∑ Q ∈ SmallFine, (#Q.support : ℝ)) ≤
          (δ₁ ^ 2 * ε₁ / 24) * (n.descFactorial 3 : ℝ) := by
        have hcard_D : Fintype.card (Polyad3 D.skeleton) ≤ t ^ 3 * d ^ 3 := by
          have h := card_polyad3_le D.skeleton
          rwa [hDV, Fintype.card_fin] at h
        have hcard_S : (#SmallFine : ℝ) ≤ ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ) := by
          have : #SmallFine ≤ t ^ 3 * d ^ 3 + 1 :=
            (card_le_univ _).trans (hcard_D.trans (Nat.le_succ _))
          exact_mod_cast this
        have hpow : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) := by
          exact_mod_cast pow_three_le_four_mul_descFactorial hn4
        calc (∑ Q ∈ SmallFine, (#Q.support : ℝ))
            ≤ ∑ _Q ∈ SmallFine, α_fine * (n : ℝ) ^ 3 :=
              sum_le_sum fun Q hQ ↦ (mem_filter.1 hQ).2.le
          _ = #SmallFine * (α_fine * (n : ℝ) ^ 3) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ((t ^ 3 * d ^ 3 : ℕ) + 1 : ℝ) * (α_fine * (n : ℝ) ^ 3) :=
              mul_le_mul_of_nonneg_right hcard_S (by positivity)
          _ = (δ₁ ^ 2 * ε₁ / 96) * (n : ℝ) ^ 3 := by
              dsimp [α_fine]; field_simp
          _ ≤ (δ₁ ^ 2 * ε₁ / 96) * (4 * (n.descFactorial 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = (δ₁ ^ 2 * ε₁ / 24) * (n.descFactorial 3 : ℝ) := by ring
      have hIrreg_le : (∑ Q ∈ IrregFine, (#Q.support : ℝ)) ≤
          (δ₁ ^ 2 * ε₁ / 24) * (n.descFactorial 3 : ℝ) := by
        simpa [IrregFine, hDpol, triadicFineMass] using hDtop.sum_card_support_le
      linarith
    have hTransIrreg_sum :
        (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1,
          (#P.support : ℝ)) ≤ (ε₁ / 2) * (n.descFactorial 3 : ℝ) := by
      have hsum_charge :
          (δ₁ ^ 2 / 2) *
            (∑ P : Polyad3 C.skeleton with P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1,
              (#P.support : ℝ)) ≤
          3 * ∑ Q ∈ BadTransFine, (#Q.support : ℝ) := by
        rw [mul_sum]
        calc _ ≤ ∑ P : Polyad3 C.skeleton with P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1,
              3 * ∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ) :=
              sum_le_sum fun P hP ↦ hcharge_trans (mem_filter.1 hP).2.1 (mem_filter.1 hP).2.2
          _ ≤ ∑ P : Polyad3 C.skeleton,
              3 * ∑ Q ∈ BadTransFine with Q.coarsen hDV.le f = P, (#Q.support : ℝ) :=
              sum_le_univ_sum_of_nonneg fun P ↦
                mul_nonneg (by norm_num) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
          _ = 3 * ∑ Q ∈ BadTransFine, (#Q.support : ℝ) := by
              rw [← mul_sum, sum_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _)]
      have hbound : 3 * ∑ Q ∈ BadTransFine, (#Q.support : ℝ) ≤
          (δ₁ ^ 2 / 2) * ((ε₁ / 2) * (n.descFactorial 3 : ℝ)) := by
        calc 3 * ∑ Q ∈ BadTransFine, (#Q.support : ℝ)
            ≤ 3 * ((δ₁ ^ 2 * ε₁ / 12) * (n.descFactorial 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hBadTransFine_sum (by norm_num)
          _ = (δ₁ ^ 2 / 2) * ((ε₁ / 2) * (n.descFactorial 3 : ℝ)) := by ring
      exact le_of_mul_le_mul_left (hsum_charge.trans hbound) (by positivity)
    -- Bound the nontransversal coarse polyad supports by `(ε₁ / 4) * n.descFactorial 3`.
    have hNonTrans_sum :
        (∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, (#P.support : ℝ)) ≤
          (ε₁ / 4) * (n.descFactorial 3 : ℝ) := by
      have hmA (A : Finset V) (hA : A ∈ C.skeleton.vertexPart.parts) : #A ≤ n / t + 1 := by
        simpa [card_univ, n, t] using hC_adm.equi.card_part_le_average_add_one hA
      let NonTransSet := (univ.filter fun P : Polyad3 C.skeleton ↦ ¬P.IsTransversal).biUnion
        Polyad3.support
      have hcard_union : ∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, #P.support =
          #NonTransSet :=
        (card_biUnion fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne).symm
      have hinj_map : NonTransSet.image Subtype.val ⊆
          (Fintype.piFinset fun _ : Fin 3 ↦ (univ : Finset V)).filter
            (fun g ↦ ¬Injective fun i ↦ C.skeleton.vertexPart.part (g i)) := by
        intro g hg
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hg
        obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
        have hnot := (mem_filter.1 hP).2
        have hx' := (P.mem_support x).1 hxP
        refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, fun hinj ↦ hnot ?_⟩
        have hc0 := C.skeleton.vertexPart.part_eq_of_mem P.hc₀ hx'.1
        have hc1 := C.skeleton.vertexPart.part_eq_of_mem P.hc₁ hx'.2.1
        have hc2 := C.skeleton.vertexPart.part_eq_of_mem P.hc₂ hx'.2.2.1
        exact P.isTransversal_iff.2
          ⟨fun h01 ↦ (by decide : (0 : Fin 3) ≠ 1) (hinj (hc0.trans (h01.trans hc1.symm))),
          fun h02 ↦ (by decide : (0 : Fin 3) ≠ 2) (hinj (hc0.trans (h02.trans hc2.symm))),
          fun h12 ↦ (by decide : (1 : Fin 3) ≠ 2) (hinj (hc1.trans (h12.trans hc2.symm)))⟩
      have hcard_nt : #NonTransSet ≤ 3 * (n / t + 1) * n ^ 2 := by
        calc #NonTransSet = #(NonTransSet.image Subtype.val) :=
              (card_image_of_injective _ Subtype.val_injective).symm
          _ ≤ #{g ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (univ : Finset V)) |
                ¬Injective fun i ↦ C.skeleton.vertexPart.part (g i)} :=
              card_le_card hinj_map
          _ ≤ (Fintype.card (Fin 3)).choose 2 * (n / t + 1) * #(univ : Finset V) ^
                (Fintype.card (Fin 3) - 1) :=
              C.skeleton.vertexPart.card_filter_not_injective_part_le_of_card_le hmA
          _ = 3 * (n / t + 1) * n ^ 2 := by simp [n]
      have ht_ceil : ⌈96 / ε₁⌉₊ ≤ t :=
        ((Nat.le_add_left _ _).trans (le_max_right _ _)).trans hC_adm.parts_ge
      have hn_ceil : ⌈96 / ε₁⌉₊ ≤ n :=
        (Nat.le_add_left _ _).trans
          ((le_max_right 4 _).trans ((basicFloor_le_regularityBound3 q₃ ε F R t₀).trans hV))
      have h96t : 96 ≤ ε₁ * t := by
        linarith [(div_le_iff₀ hε₁_pos).1 ((Nat.le_ceil (96 / ε₁)).trans (Nat.cast_le.2 ht_ceil))]
      have h96n : 96 ≤ ε₁ * n := by
        linarith [(div_le_iff₀ hε₁_pos).1 ((Nat.le_ceil (96 / ε₁)).trans (Nat.cast_le.2 hn_ceil))]
      have ht_pos : (0 : ℝ) < t := by
        by_contra! hle
        linarith [mul_nonpos_of_nonneg_of_nonpos hε₁_pos.le hle]
      have hdiv_t : 3 * ((n / t : ℕ) : ℝ) ≤ (ε₁ / 32) * n := by
        have h1 : ((n / t : ℕ) : ℝ) * t ≤ n := by exact_mod_cast Nat.div_mul_le_self n t
        have h2 : (96 * ((n / t : ℕ) : ℝ)) * t ≤ (ε₁ * n) * t := by
          calc (96 * ((n / t : ℕ) : ℝ)) * t = 96 * (((n / t : ℕ) : ℝ) * t) := by ring
            _ ≤ 96 * n := mul_le_mul_of_nonneg_left h1 (by norm_num)
            _ ≤ (ε₁ * t) * n := mul_le_mul_of_nonneg_right h96t hn_pos.le
            _ = (ε₁ * n) * t := by ring
        have h3 := le_of_mul_le_mul_right h2 ht_pos
        linarith
      have h1_n : (3 : ℝ) ≤ (ε₁ / 32) * n := by linarith
      have hpow : (n : ℝ) ^ 3 ≤ 4 * (n.descFactorial 3 : ℝ) := by
        exact_mod_cast pow_three_le_four_mul_descFactorial hn4
      calc (∑ P : Polyad3 C.skeleton with ¬P.IsTransversal, (#P.support : ℝ))
          = (#NonTransSet : ℝ) := by rw [← Nat.cast_sum, hcard_union]
        _ ≤ ((3 * (n / t + 1) * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard_nt
        _ = (3 * ((n / t : ℕ) : ℝ) + 3) * (n : ℝ) ^ 2 := by push_cast; ring
        _ ≤ ((ε₁ / 32) * n + (ε₁ / 32) * n) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (add_le_add hdiv_t h1_n) (by positivity)
        _ = (ε₁ / 16) * (n : ℝ) ^ 3 := by ring
        _ ≤ (ε₁ / 16) * (4 * (n.descFactorial 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (ε₁ / 4) * (n.descFactorial 3 : ℝ) := by ring
    -- Combine transversal and nontransversal parts, promote rank `1` to `R K`, and weaken
    -- `triadicSched1 F K` to `F K`.
    have hRank1_most : H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
      rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC_dec,
        div_le_iff₀ hdesc_pos]
      let S_tr := univ.filter fun P : Polyad3 C.skeleton ↦
        P.IsTransversal ∧ ¬H'.IsTopRegularOverPolyad P δ₁ 1
      let S_nt := univ.filter fun P : Polyad3 C.skeleton ↦ ¬P.IsTransversal
      have hsub :
          (univ.filter fun P : Polyad3 C.skeleton ↦ ¬H'.IsTopRegularOverPolyad P δ₁ 1) ⊆
            S_tr ∪ S_nt := by
        intro P hP
        by_cases htr : P.IsTransversal
        · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, htr, (mem_filter.1 hP).2⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, htr⟩)
      calc _ ≤ ∑ P ∈ S_tr ∪ S_nt, (#P.support : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (by convert hsub) fun _ _ _ ↦ Nat.cast_nonneg _
        _ ≤ (∑ P ∈ S_tr, (#P.support : ℝ)) + (∑ P ∈ S_nt, (#P.support : ℝ)) :=
            sum_union_le_of_nonneg S_tr S_nt fun _ ↦ Nat.cast_nonneg _
        _ ≤ (ε₁ / 2) * (n.descFactorial 3 : ℝ) + (ε₁ / 4) * (n.descFactorial 3 : ℝ) :=
            add_le_add hTransIrreg_sum hNonTrans_sum
        _ = (3 * ε₁ / 4) * (n.descFactorial 3 : ℝ) := by ring
        _ ≤ ε * (n.descFactorial 3 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith [triadicEps1_le ε]) hdesc_pos.le
    rw [topRegularOverMostPolyads_iff] at hRank1_most ⊢
    refine le_trans ?_ hRank1_most
    rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
    refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    intro P hP
    obtain ⟨hP_mem, hnot⟩ := mem_filter.1 hP
    refine mem_filter.2 ⟨hP_mem, fun h1 ↦ hnot ?_⟩
    exact (IsTopRegularOverPolyad.of_rank_one_div_pow h1 (triadicSched1_pos hF K)).mono
      (triadicSched1_le F K)
  have hCells : C.VertexCellsControlled t₀ :=
    C.vertexCellsControlled_iff.2
      ⟨hC_adm.equi, ((le_max_left t₀ 1).trans (le_max_left _ _)).trans hC_adm.parts_ge⟩
  have hLower : C.skeleton.LowerSkeletonRegular F :=
    C.skeleton.lowerSkeletonRegular_iff.2
      (hC_adm.lower_reg.isPairColorRegular (triadicSched1_le F _))
  exact ⟨H', C, hCells, hApprox, hC_dec, hLower, hTopCoarse, hC_comp⟩

end Colored3Graph

end Recoloring

end TauCeti
