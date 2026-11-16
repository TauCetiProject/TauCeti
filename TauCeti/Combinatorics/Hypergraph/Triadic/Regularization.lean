/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
public import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability

/-!
# Simultaneous lower-skeleton and top regularization of colored three-graphs

Strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) keeps the
vertex partition fixed, so its coarse complex need not have a regular lower skeleton. Conversely,
pair-regularizing the lower skeleton after stopping would change the complexity of the complex and
thereby alter the regularity schedule evaluated at that complexity.

This file resolves the circularity by an alternating energy-gap iteration that maintains lower
regularity as a loop invariant. Starting from an equitable vertex partition `P₀` equipped with the
constant one-color pair system (which is `F`-regular once every cell has more than
`1 / F (#P₀.parts + 1)` vertices), each round applies
`Colored3Graph.exists_topRegularOverMostPolyads` to `C_j` at the schedules `(η, μ, r)` evaluated at
`C_j.complexity`, producing a pair-palette refinement `D_j` on the same vertex cells. If the polyad
energy gap `H.polyadEnergy D_j.skeleton - H.polyadEnergy C_j.skeleton` is at most `g`, the
iteration stops and returns `(C_j, D_j)`. Otherwise, strong regular approximation of pair-color
systems (`PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`) refines the vertex
partition of `D_j` and recolors at most `(g / 24) |V|²` ordered pairs to produce a new equitable
`F`-regular complex `C_{j+1}` with one additional pair color. By one-sided polyad energy stability
(`Colored3Graph.polyadEnergy_sub_polyadEnergy_le_of_le_of_pairRecoloring`), when `6 ≤ |V|` this
recoloring lowers the polyad energy by at most `g / 2`, so the net gain is strictly greater than
`g / 2`. Since polyad energy lies in `[0, 1]`, the iteration stops after at most `⌊2 / g⌋₊`
advances with host-independent bounds on the vertex cells and pair colors.

Initializing with an equipartition of size `max t₀ 1` yields controlled vertex cells
(`C.VertexCellsControlled t₀`), lower-skeleton `F`-regularity, and a fine palette refinement `D`
with energy gap at most `g` over which `H` is top-regular at the schedules evaluated at
`C.complexity` (`Colored3Graph.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads`).
Combining the energy gap with `Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le`
gives the Rödl–Schacht regularity lemma for colored three-graphs: a single complex with controlled
vertex cells, an `F`-regular lower skeleton, and `(δ, r C.complexity)`-top regularity off an
`ε`-proportion of the triples
(`Colored3Graph.exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank`).

## Main definitions

* `TauCeti.strongTriadicRegularityStep`: one step of the alternating `(parts, pairColors)` bound
  recursion.
* `TauCeti.strongTriadicRegularityBounds`: host-independent upper bounds on the vertex-cell count
  and pair-color count of the coarse complex.
* `TauCeti.strongTriadicRegularityHostBound`: minimum host size for simultaneous strong
  lower-skeleton and top regularization.

## Main results

* `TauCeti.Colored3Graph.exists_strong_refining_lowerSkeletonRegular_topRegularOverMostPolyads`:
  simultaneous strong lower-skeleton and top regularization refining an equitable vertex partition.
* `TauCeti.Colored3Graph.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads`:
  simultaneous strong lower-skeleton and top regularization with controlled vertex cells.
* `TauCeti.Colored3Graph.exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank`:
  the Rödl–Schacht regularity lemma for colored three-graphs with controlled vertex cells, an
  `F`-regular lower skeleton, and scheduled-rank top regularity.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 and Lemma 4.2.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
-/

public section

open Finset Finpartition

namespace TauCeti

/-! ### Quantitative bounds -/

/-- One round of the alternating bound recursion on `(T, Q)`, where `T` bounds the number of vertex
cells and `Q` bounds the number of pair colors: top regularization raises the palette bound to
`Q' = strongTopRegularityStep T η μ r Q`, and strong pair-color approximation with edit budget
`g / 24` refines the vertex cells and adds one fresh diagonal pair color. -/
noncomputable def strongTriadicRegularityStep (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (p : ℕ × ℕ) : ℕ × ℕ :=
  let Q' := strongTopRegularityStep p.1 η μ r p.2
  ((range (Q' + 1)).sup fun q ↦ pairApproximationPartsBound q (g / 24) F p.1, Q' + 1)

/-- Unfolding lemma for `TauCeti.strongTriadicRegularityStep`. -/
theorem strongTriadicRegularityStep_def (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (p : ℕ × ℕ) :
    strongTriadicRegularityStep g F η μ r p =
      ((range (strongTopRegularityStep p.1 η μ r p.2 + 1)).sup
        (fun q ↦ pairApproximationPartsBound q (g / 24) F p.1),
        strongTopRegularityStep p.1 η μ r p.2 + 1) :=
  (rfl)

/-- `strongTriadicRegularityStep` is monotone in both coordinates. -/
theorem strongTriadicRegularityStep_mono (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) :
    Monotone (strongTriadicRegularityStep g F η μ r) := by
  intro p₁ p₂ hp
  have hQ : strongTopRegularityStep p₁.1 η μ r p₁.2 ≤ strongTopRegularityStep p₂.1 η μ r p₂.2 :=
    strongTopRegularityStep_mono η μ r hp.1 hp.2
  rw [strongTriadicRegularityStep_def, strongTriadicRegularityStep_def]
  refine ⟨?_, Nat.succ_le_succ hQ⟩
  dsimp only
  refine Finset.sup_le fun q hq ↦ ?_
  exact (pairApproximationPartsBound_mono q (g / 24) F hp.1).trans
    (le_sup (f := fun q ↦ pairApproximationPartsBound q (g / 24) F p₂.1)
      (mem_range.2 (Nat.lt_of_lt_of_le (mem_range.1 hq) (Nat.succ_le_succ hQ))))

/-- For nonnegative `g` and a positive schedule `F`, `strongTriadicRegularityStep` never lowers
either coordinate. -/
theorem le_strongTriadicRegularityStep {g : ℝ} (hg : 0 ≤ g) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (η μ : ℕ → ℝ) (r : ℕ → ℕ) (p : ℕ × ℕ) :
    p ≤ strongTriadicRegularityStep g F η μ r p := by
  rw [strongTriadicRegularityStep_def]
  refine ⟨?_, (le_strongTopRegularityStep p.1 η μ r p.2).trans (Nat.le_succ _)⟩
  have hp1 : p.1 ≤ pairApproximationPartsBound 0 (g / 24) F p.1 := by
    obtain rfl | hg' := hg.eq_or_lt
    · simp [pairApproximationPartsBound_def, strongPairColorRegularityBound_def]
    · exact le_pairApproximationPartsBound 0 (by positivity) hF p.1
  exact hp1.trans
    (le_sup (f := fun q ↦ pairApproximationPartsBound q (g / 24) F p.1)
      (mem_range.2 (Nat.succ_pos _)))

/-- Upper bounds `(T, Q)` on the number of vertex cells and pair colors of the coarse complex in
simultaneous strong lower-skeleton and top regularization starting from `max t₀ 1` vertex cells
and one pair color: at most `⌊2 / g⌋₊` advances precede a round with polyad energy gap at most
`g`. -/
noncomputable def strongTriadicRegularityBounds (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (t₀ : ℕ) : ℕ × ℕ :=
  (strongTriadicRegularityStep g F η μ r)^[⌊2 / g⌋₊] (max t₀ 1, 1)

/-- Unfolding lemma for `TauCeti.strongTriadicRegularityBounds`. -/
theorem strongTriadicRegularityBounds_def (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    strongTriadicRegularityBounds g F η μ r t₀ =
      (strongTriadicRegularityStep g F η μ r)^[⌊2 / g⌋₊] (max t₀ 1, 1) :=
  (rfl)

/-- Clamping `t₀` below by `1` does not change `strongTriadicRegularityBounds`. -/
theorem strongTriadicRegularityBounds_max_one (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    strongTriadicRegularityBounds g F η μ r (max t₀ 1) =
      strongTriadicRegularityBounds g F η μ r t₀ := by
  simp [strongTriadicRegularityBounds_def]

/-- `strongTriadicRegularityBounds` is monotone in `t₀`. -/
theorem strongTriadicRegularityBounds_mono (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) :
    Monotone (strongTriadicRegularityBounds g F η μ r) :=
  fun _ _ ht ↦ (strongTriadicRegularityStep_mono g F η μ r).iterate _ ⟨max_le_max ht le_rfl, le_rfl⟩

/-- For a positive schedule `F`, `strongTriadicRegularityBounds` dominates the starting bounds
`(max t₀ 1, 1)`. -/
theorem le_strongTriadicRegularityBounds (g : ℝ) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    (max t₀ 1, 1) ≤ strongTriadicRegularityBounds g F η μ r t₀ := by
  rw [strongTriadicRegularityBounds_def]
  obtain hg | hg := le_total g 0
  · have hzero : ⌊2 / g⌋₊ = 0 := Nat.floor_eq_zero.2 (lt_of_le_of_lt
      (div_nonpos_of_nonneg_of_nonpos (by norm_num) hg) zero_lt_one)
    rw [hzero]
    exact le_rfl
  · exact Function.id_le_iterate_of_id_le (le_strongTriadicRegularityStep hg hF η μ r) _ _

/-- Minimum host size `|V|` above which simultaneous strong lower-skeleton and top regularization
succeeds from an equipartition with `max t₀ 1` vertex cells. -/
noncomputable def strongTriadicRegularityHostBound (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (t₀ : ℕ) : ℕ :=
  let t₁ := max t₀ 1
  let b := strongTriadicRegularityBounds g F η μ r t₀
  let Q' := strongTopRegularityStep b.1 η μ r b.2
  max (t₁ * (⌈1 / F (t₁ + 1)⌉₊ + 1))
    (max 6 ((range (Q' + 1)).sup fun q ↦ pairApproximationBound q (g / 24) F b.1))

/-- Unfolding lemma for `TauCeti.strongTriadicRegularityHostBound`. -/
theorem strongTriadicRegularityHostBound_def (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    strongTriadicRegularityHostBound g F η μ r t₀ =
      let t₁ := max t₀ 1
      let b := strongTriadicRegularityBounds g F η μ r t₀
      max (t₁ * (⌈1 / F (t₁ + 1)⌉₊ + 1))
        (max 6 ((range (strongTopRegularityStep b.1 η μ r b.2 + 1)).sup
          fun q ↦ pairApproximationBound q (g / 24) F b.1)) :=
  (rfl)

/-- Clamping `t₀` below by `1` does not change `strongTriadicRegularityHostBound`. -/
theorem strongTriadicRegularityHostBound_max_one (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    strongTriadicRegularityHostBound g F η μ r (max t₀ 1) =
      strongTriadicRegularityHostBound g F η μ r t₀ := by
  simp [strongTriadicRegularityHostBound_def, strongTriadicRegularityBounds_max_one]

/-- `strongTriadicRegularityHostBound` is at least `6`, ensuring
`|V|³ ≤ 2 |V|.descFactorial 3`. -/
theorem six_le_strongTriadicRegularityHostBound (g : ℝ) (F η μ : ℕ → ℝ) (r : ℕ → ℕ) (t₀ : ℕ) :
    6 ≤ strongTriadicRegularityHostBound g F η μ r t₀ :=
  (le_max_left 6 _).trans (le_max_right _ _)

/-! ### Auxiliary lemmas -/

section Helpers

/-- For `n ≥ 6`, `n³ ≤ 2 n (n - 1) (n - 2)`, so normalizing by `n.descFactorial 3` loses at most a
factor of two relative to `n³`. -/
private theorem pow_three_le_two_mul_descFactorial {n : ℕ} (hn : 6 ≤ n) :
    n ^ 3 ≤ 2 * n.descFactorial 3 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, Nat.sub_zero]
  have h1 : m + 6 - 1 = m + 5 := by omega
  have h2 : m + 6 - 2 = m + 4 := by omega
  rw [h1, h2]
  have hquad : (m + 6) ^ 2 ≤ 2 * ((m + 4) * (m + 5)) := by nlinarith
  calc (m + 6) ^ 3 = (m + 6) ^ 2 * (m + 6) := by ring
    _ ≤ 2 * ((m + 4) * (m + 5)) * (m + 6) := Nat.mul_le_mul_right _ hquad
    _ = 2 * ((m + 4) * ((m + 5) * (m + 6))) := by ring

/-- The constant one-color pair-color system on `V`. -/
private def constOnePairColorSystem (V : Type*) : PairColorSystem (Fin 1) V where
  color _ := 0
  rev := id
  rev_involutive _ := rfl
  color_rev _ := rfl

/-- The constant one-color lower skeleton is `ε`-regular whenever every cell satisfies `1 < ε * #A`
(so every tested subcell has at least two vertices, avoiding empty distinct-pair supports). -/
private theorem isPairColorRegular_constOnePairColorSystem {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) {ε : ℝ} (hsize : ∀ A ∈ P.parts, 1 < ε * #A) :
    (⟨P, constOnePairColorSystem V⟩ : PairSkeleton3 (Fin 1) V).IsPairColorRegular ε := by
  by_cases h1 : 1 ≤ ε
  · exact PairSkeleton3.isPairColorRegular_of_one_le h1
  have hdens {s t : Finset V} (hs : 1 < #s) (ht : t.Nonempty) (c : Fin 1) :
      pairColorDensity (constOnePairColorSystem V) c s t = 1 := by
    obtain ⟨y, hy⟩ := ht
    obtain ⟨x, hx, hxy⟩ := exists_mem_ne hs y
    have hne : ((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2).Nonempty :=
      ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, hxy⟩⟩
    have hsum := sum_pairColorDensity (constOnePairColorSystem V) s t hne
    rw [Fintype.sum_unique] at hsum
    rwa [Subsingleton.elim c default]
  rw [PairSkeleton3.isPairColorRegular_iff]
  intro c A hA B hB A' _ B' _ hA'size hB'size
  have hε0 : 0 < ε := pos_of_mul_pos_left (one_pos.trans (hsize A hA)) (Nat.cast_nonneg _)
  have hε1 : ε < 1 := not_le.1 h1
  have hAcard : 1 < #A := by
    have : ε * (#A : ℝ) ≤ #A := mul_le_of_le_one_left (Nat.cast_nonneg _) hε1.le
    exact_mod_cast (hsize A hA).trans_le this
  have hBcard : 1 < #B := by
    have : ε * (#B : ℝ) ≤ #B := mul_le_of_le_one_left (Nat.cast_nonneg _) hε1.le
    exact_mod_cast (hsize B hB).trans_le this
  have hA'card : 1 < #A' := by exact_mod_cast (hsize A hA).trans_le hA'size
  have hB'card : 1 < #B' := by exact_mod_cast (hsize B hB).trans_le hB'size
  rw [hdens hA'card (card_pos.1 (by omega)) c, hdens hAcard (card_pos.1 (by omega)) c]
  simpa using hε0.le

/-- An equipartition `P₀` equipped with the constant one-color pair system is `F`-regular once
`|V|` is large enough that every cell has more than `1 / F (#P₀.parts + 1)` vertices. -/
private theorem lowerSkeletonRegular_constOnePairColorSystem {V : Type*} [Fintype V] [DecidableEq V]
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (P₀ : Finpartition (univ : Finset V))
    (hP₀eq : P₀.IsEquipartition) (hP₀pos : 0 < #P₀.parts)
    (hV : #P₀.parts * (⌈1 / F (#P₀.parts + 1)⌉₊ + 1) ≤ Fintype.card V) :
    (⟨P₀, constOnePairColorSystem V⟩ : PairSkeleton3 (Fin 1) V).LowerSkeletonRegular F := by
  rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_fin]
  refine isPairColorRegular_constOnePairColorSystem P₀ fun A hA ↦ ?_
  have hdiv : ⌈1 / F (#P₀.parts + 1)⌉₊ + 1 ≤ #(univ : Finset V) / #P₀.parts := by
    rw [card_univ, Nat.le_div_iff_mul_le hP₀pos, mul_comm]
    exact hV
  have hAcard : (⌈1 / F (#P₀.parts + 1)⌉₊ + 1 : ℝ) ≤ #A := by
    exact_mod_cast hdiv.trans (hP₀eq.average_le_card_part hA)
  have hlt : 1 / F (#P₀.parts + 1) < (#A : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
  exact (div_lt_iff₀' (hF (#P₀.parts + 1))).1 hlt

open Classical in
/-- Recoloring at most `(g / 24) |V|²` ordered pairs while refining the vertex partition lowers the
polyad energy by at most `g / 2` whenever `6 ≤ |V|`. -/
private theorem polyadEnergy_sub_relabel_le_half {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq κ] [Fintype κ] (H : Colored3Graph κ V)
    {S : PairSkeleton3 κ₂ V} {P : Finpartition (univ : Finset V)}
    {Topt : PairColorSystem (Option κ₂) V} {e : Option κ₂ ≃ κ₂'} {g : ℝ}
    (hg : 0 ≤ g) (hV6 : 6 ≤ Fintype.card V) (hPS : P ≤ S.vertexPart)
    (hedit : (#{p | Topt.color p ≠ some (S.pairColors.color p)} : ℝ) ≤
      g / 24 * (Fintype.card V : ℝ) ^ 2) :
    H.polyadEnergy S - H.polyadEnergy ((⟨P, Topt⟩ : PairSkeleton3 (Option κ₂) V).relabel e) ≤
      g / 2 := by
  let T : PairSkeleton3 κ₂' V := (⟨P, Topt⟩ : PairSkeleton3 (Option κ₂) V).relabel e
  have hTV : T.vertexPart ≤ S.vertexPart := by
    rwa [PairSkeleton3.relabel_vertexPart]
  have hloss := H.polyadEnergy_sub_polyadEnergy_le_of_le_of_pairRecoloring (S := S) (T := T) hTV
    (g := e ∘ some) (e.injective.comp (Option.some_injective _))
  have hfilt : (#{p | T.pairColors.color p ≠ (e ∘ some) (S.pairColors.color p)} : ℝ) =
      #{p | Topt.color p ≠ some (S.pairColors.color p)} := by
    congr 1
    apply congr_arg Finset.card
    ext p
    simp [T, PairSkeleton3.relabel_pairColors, e.injective.ne_iff]
  rw [hfilt] at hloss
  have hdesc_pos : (0 : ℝ) < ((Fintype.card V).descFactorial 3 : ℝ) :=
    Nat.cast_pos.2 (Nat.descFactorial_pos.2 (by omega))
  have hcube : (Fintype.card V : ℝ) ^ 3 ≤ 2 * ((Fintype.card V).descFactorial 3 : ℝ) := by
    exact_mod_cast pow_three_le_two_mul_descFactorial hV6
  refine hloss.trans ((div_le_iff₀ hdesc_pos).2 ?_)
  have hmul := mul_le_mul_of_nonneg_right hedit (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  calc 6 * (#{p | Topt.color p ≠ some (S.pairColors.color p)} : ℝ) * (Fintype.card V : ℝ)
      ≤ 6 * (g / 24 * (Fintype.card V : ℝ) ^ 2 * (Fintype.card V : ℝ)) := by linarith
    _ = g / 4 * (Fintype.card V : ℝ) ^ 3 := by ring
    _ ≤ g / 4 * (2 * ((Fintype.card V).descFactorial 3 : ℝ)) := by gcongr
    _ = g / 2 * ((Fintype.card V).descFactorial 3 : ℝ) := by ring

/-- One alternating round from an equitable complex `C`: top-regularize `C` at its own complexity
to obtain `(D, f)`. Either the polyad energy gap is at most `g` (stopping), or strong pair-color
approximation at edit budget `g / 24` refines `D` into an equitable `F`-regular complex `C'`
whose polyad energy exceeds that of `C` by more than `g / 2`. -/
private theorem advance_lower_top_round {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
    [Fintype κ] (H : Colored3Graph κ V) {g : ℝ} (hg : 0 < g) {F η μ : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hη : ∀ n, 0 < η n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) {T Q : ℕ}
    (hV6 : 6 ≤ Fintype.card V)
    (hVstep : ∀ q ≤ strongTopRegularityStep T η μ r Q,
      pairApproximationBound q (g / 24) F T ≤ Fintype.card V)
    (C : TriadicComplex3 V) (hCT : #C.skeleton.vertexPart.parts ≤ T) (hCQ : C.pairColorCount ≤ Q)
    (hCeq : C.skeleton.vertexPart.IsEquipartition) :
    (∃ (D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
        D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
          (η C.complexity) (μ C.complexity) C.pairColorCount ∧
        D.skeleton.vertexPart = C.skeleton.vertexPart ∧
        (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
        (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
        D.polyads = univ ∧
        H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
        H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g) ∨
      ∃ C' : TriadicComplex3 V,
        C'.skeleton.vertexPart ≤ C.skeleton.vertexPart ∧
        C'.skeleton.vertexPart.IsEquipartition ∧
        C'.skeleton.LowerSkeletonRegular F ∧
        C'.polyads = univ ∧
        #C'.skeleton.vertexPart.parts ≤ (strongTriadicRegularityStep g F η μ r (T, Q)).1 ∧
        C'.pairColorCount ≤ (strongTriadicRegularityStep g F η μ r (T, Q)).2 ∧
        H.polyadEnergy C.skeleton + g / 2 < H.polyadEnergy C'.skeleton := by
  obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg⟩ :=
    H.exists_topRegularOverMostPolyads C.skeleton (hη C.complexity) (hμ C.complexity)
      (r C.complexity)
  rw [Fintype.card_fin] at hDcard
  by_cases hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g
  · exact Or.inl ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩
  set Q' := strongTopRegularityStep T η μ r Q
  have hcomp : C.complexity ≤ T + Q + T ^ 3 * Q ^ 3 :=
    C.complexity_le.trans (by gcongr)
  have hDQ' : D.pairColorCount ≤ Q' :=
    hDcard.trans ((topRegularRefinementBound_mono_parts _ _ _ _ hCT).trans
      (topRegularRefinementBound_le_strongTopRegularityStep η μ r hCQ hcomp))
  have hDV_eq : D.skeleton.vertexPart.IsEquipartition := hDV ▸ hCeq
  have hDV_le : #D.skeleton.vertexPart.parts ≤ T := hDV ▸ hCT
  have hV_approx : pairApproximationBound (Fintype.card (Fin D.pairColorCount)) (g / 24) F
      #D.skeleton.vertexPart.parts ≤ Fintype.card V := by
    rw [Fintype.card_fin]
    exact (pairApproximationBound_mono _ _ _ hDV_le).trans (hVstep _ hDQ')
  obtain ⟨P, Topt, hPD, hPeq, hPcard, -, hPlow, hedit⟩ :=
    D.skeleton.pairColors.exists_refining_equipartition_lowerSkeletonRegular D.skeleton.vertexPart
      hDV_eq (by positivity) hF hV_approx
  let e : Option (Fin D.pairColorCount) ≃ Fin (D.pairColorCount + 1) :=
    (finSuccEquiv D.pairColorCount).symm
  let S' : PairSkeleton3 (Option (Fin D.pairColorCount)) V := ⟨P, Topt⟩
  let C' : TriadicComplex3 V := ⟨D.pairColorCount + 1, S'.relabel e, univ⟩
  have hC'V : C'.skeleton.vertexPart = P := S'.relabel_vertexPart e
  refine Or.inr ⟨C', hC'V.le.trans (hDV ▸ hPD), hC'V ▸ hPeq, hPlow.relabel e, rfl, ?_,
    Nat.succ_le_succ hDQ', ?_⟩
  · rw [Fintype.card_fin] at hPcard
    rw [hC'V, strongTriadicRegularityStep_def]
    exact hPcard.trans ((pairApproximationPartsBound_mono _ _ _ hDV_le).trans
      (le_sup (f := fun q ↦ pairApproximationPartsBound q (g / 24) F T)
        (mem_range.2 (Nat.lt_succ_of_le hDQ'))))
  · have hloss := polyadEnergy_sub_relabel_le_half H (S := D.skeleton) (e := e) hg.le hV6 hPD hedit
    linarith

/-- Induction invariant for the alternating loop: after `j ≤ ⌊2 / g⌋₊` rounds from an equitable
vertex partition `P₀` whose constant one-color skeleton is `F`-regular, either a stopping pair
`(C, D, f)` has already been found, or the current equitable `F`-regular complex `C` has polyad
energy at least `j * (g / 2)`. -/
private theorem exists_stop_or_energy_ge {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
    [Fintype κ] (H : Colored3Graph κ V) (P₀ : Finpartition (univ : Finset V))
    {g : ℝ} (hg : 0 < g) {F η μ : ℕ → ℝ} (hF : ∀ n, 0 < F n) (hη : ∀ n, 0 < η n)
    (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ)
    (hP₀eq : P₀.IsEquipartition)
    (hP₀reg : (⟨P₀, constOnePairColorSystem V⟩ : PairSkeleton3 (Fin 1) V).LowerSkeletonRegular F)
    (hV6 : 6 ≤ Fintype.card V)
    (hVstep : ∀ j ≤ ⌊2 / g⌋₊, ∀ q ≤ strongTopRegularityStep
        ((strongTriadicRegularityStep g F η μ r)^[j] (#P₀.parts, 1)).1 η μ r
        ((strongTriadicRegularityStep g F η μ r)^[j] (#P₀.parts, 1)).2,
      pairApproximationBound q (g / 24) F
        ((strongTriadicRegularityStep g F η μ r)^[j] (#P₀.parts, 1)).1 ≤ Fintype.card V)
    {j : ℕ} (hj : j ≤ ⌊2 / g⌋₊) :
    let b := (strongTriadicRegularityStep g F η μ r)^[j] (#P₀.parts, 1)
    (∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      #C.skeleton.vertexPart.parts ≤ b.1 ∧ C.pairColorCount ≤ b.2 ∧
      C.skeleton.vertexPart ≤ P₀ ∧ C.skeleton.vertexPart.IsEquipartition ∧
      C.skeleton.LowerSkeletonRegular F ∧ C.polyads = univ ∧
      D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      D.skeleton.vertexPart = C.skeleton.vertexPart ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g) ∨
    ∃ C : TriadicComplex3 V,
      #C.skeleton.vertexPart.parts ≤ b.1 ∧ C.pairColorCount ≤ b.2 ∧
      C.skeleton.vertexPart ≤ P₀ ∧ C.skeleton.vertexPart.IsEquipartition ∧
      C.skeleton.LowerSkeletonRegular F ∧ C.polyads = univ ∧
      j * (g / 2) ≤ H.polyadEnergy C.skeleton := by
  induction j with
  | zero =>
    refine Or.inr ⟨⟨1, ⟨P₀, constOnePairColorSystem V⟩, univ⟩, le_rfl, le_rfl, le_rfl, hP₀eq,
      hP₀reg, rfl, ?_⟩
    simpa using H.polyadEnergy_nonneg _
  | succ j ih =>
    have hj' : j ≤ ⌊2 / g⌋₊ := Nat.le_of_succ_le hj
    have hle :
        (strongTriadicRegularityStep g F η μ r)^[j] (#P₀.parts, 1) ≤
          (strongTriadicRegularityStep g F η μ r)^[j + 1] (#P₀.parts, 1) := by
      rw [Function.iterate_succ_apply']
      exact le_strongTriadicRegularityStep hg.le hF η μ r _
    obtain ⟨C, D, f, hCT, hCQ, hCV, hCeq, hCreg, hCpol, hDcard, hDV, hf, hfrev, hDpol, hDreg,
        hgap⟩ | ⟨C, hCT, hCQ, hCV, hCeq, hCreg, hCpol, hE⟩ := ih hj'
    · exact Or.inl ⟨C, D, f, hCT.trans hle.1, hCQ.trans hle.2, hCV, hCeq, hCreg, hCpol, hDcard,
        hDV, hf, hfrev, hDpol, hDreg, hgap⟩
    obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩ |
        ⟨C', hC'V, hC'eq, hC'reg, hC'pol, hC'T, hC'Q, hE'⟩ :=
      advance_lower_top_round H hg hF hη hμ r hV6 (hVstep j hj') C hCT hCQ hCeq
    · exact Or.inl ⟨C, D, f, hCT.trans hle.1, hCQ.trans hle.2, hCV, hCeq, hCreg, hCpol, hDcard,
        hDV, hf, hfrev, hDpol, hDreg, hgap⟩
    refine Or.inr ⟨C', by rwa [Function.iterate_succ_apply'], by rwa [Function.iterate_succ_apply'],
      hC'V.trans hCV, hC'eq, hC'reg, hC'pol, ?_⟩
    push_cast
    linarith

end Helpers

/-! ### Simultaneous strong lower-skeleton and top regularization -/

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] (H : Colored3Graph κ V)

/-- **Simultaneous strong lower-skeleton and top regularization refining an equipartition.** Let
`g > 0`, let `F, η, μ` be positive schedules and `r` a rank schedule, and let `P₀` be an
equipartition of `V`. Once `|V|` is at least `strongTriadicRegularityHostBound g F η μ r #P₀.parts`,
there exist triadic complexes `C` and `D` (selecting all their polyads) and a reversal-equivariant
projection `f` of pair colors from `D` to `C` such that:

* `C` has equitable vertex cells refining `P₀`,
* `C.skeleton` is `F`-regular at its own lower complexity,
* `D` shares the vertex cells of `C` and refines its pair palette along `f`,
* `H` is `(η C.complexity, r C.complexity)`-top-regular over all polyads of `D` outside a
  `μ C.complexity`-proportion of the injective triples,
* the polyad energy gap `H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton` is at most `g`, and
* the vertex cells and pair colors of `C` are bounded independently of `V` by
  `strongTriadicRegularityBounds g F η μ r #P₀.parts`. -/
theorem exists_strong_refining_lowerSkeletonRegular_topRegularOverMostPolyads [Fintype κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    {g : ℝ} (hg : 0 < g) {F η μ : ℕ → ℝ} (hF : ∀ n, 0 < F n) (hη : ∀ n, 0 < η n)
    (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ)
    (hV : strongTriadicRegularityHostBound g F η μ r #P₀.parts ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      C.skeleton.vertexPart ≤ P₀ ∧
      C.skeleton.vertexPart.IsEquipartition ∧
      #C.skeleton.vertexPart.parts ≤ (strongTriadicRegularityBounds g F η μ r #P₀.parts).1 ∧
      C.pairColorCount ≤ (strongTriadicRegularityBounds g F η μ r #P₀.parts).2 ∧
      D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      C.skeleton.LowerSkeletonRegular F ∧
      D.skeleton.vertexPart = C.skeleton.vertexPart ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      C.polyads = univ ∧ D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g := by
  have hV6 : 6 ≤ Fintype.card V :=
    (six_le_strongTriadicRegularityHostBound g F η μ r _).trans hV
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hP₀pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  have hmax : max #P₀.parts 1 = #P₀.parts := max_eq_left hP₀pos
  have hP₀reg :
      (⟨P₀, constOnePairColorSystem V⟩ : PairSkeleton3 (Fin 1) V).LowerSkeletonRegular F :=
    lowerSkeletonRegular_constOnePairColorSystem hF P₀ hP₀ hP₀pos
      (hmax ▸ (le_max_left _ _).trans hV)
  set step := strongTriadicRegularityStep g F η μ r
  set K : ℕ := ⌊2 / g⌋₊
  have hb : strongTriadicRegularityBounds g F η μ r #P₀.parts = step^[K] (#P₀.parts, 1) := by
    rw [strongTriadicRegularityBounds_def, hmax]
  have hVstep (j : ℕ) (hj : j ≤ K) (q : ℕ)
      (hq : q ≤ strongTopRegularityStep (step^[j] (#P₀.parts, 1)).1 η μ r
        (step^[j] (#P₀.parts, 1)).2) :
      pairApproximationBound q (g / 24) F (step^[j] (#P₀.parts, 1)).1 ≤ Fintype.card V := by
    have hjb : step^[j] (#P₀.parts, 1) ≤ step^[K] (#P₀.parts, 1) :=
      Function.monotone_iterate_of_id_le (le_strongTriadicRegularityStep hg.le hF η μ r) hj _
    have hqK : q ≤ strongTopRegularityStep (step^[K] (#P₀.parts, 1)).1 η μ r
        (step^[K] (#P₀.parts, 1)).2 :=
      hq.trans (strongTopRegularityStep_mono η μ r hjb.1 hjb.2)
    refine (pairApproximationBound_mono q (g / 24) F hjb.1).trans ?_
    refine (le_sup (f := fun q ↦ pairApproximationBound q (g / 24) F (step^[K] (#P₀.parts, 1)).1)
      (mem_range.2 (Nat.lt_succ_of_le hqK))).trans ?_
    rw [← hb]
    exact (le_max_right 6 _).trans ((le_max_right _ _).trans hV)
  obtain ⟨C, D, f, hCT, hCQ, hCV, hCeq, hCreg, hCpol, hDcard, hDV, hf, hfrev, hDpol, hDreg,
      hgap⟩ | ⟨C, hCT, hCQ, hCV, hCeq, hCreg, hCpol, hE⟩ :=
    exists_stop_or_energy_ge H P₀ hg hF hη hμ r hP₀ hP₀reg hV6 hVstep le_rfl
  · exact ⟨C, D, f, hCV, hCeq, hb ▸ hCT, hb ▸ hCQ, hDcard, hCreg, hDV, hf, hfrev, hCpol, hDpol,
      hDreg, hgap⟩
  obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩ | ⟨C', -, -, -, -, -, -, hE'⟩ :=
    advance_lower_top_round H hg hF hη hμ r hV6 (hVstep K le_rfl) C hCT hCQ hCeq
  · exact ⟨C, D, f, hCV, hCeq, hb ▸ hCT, hb ▸ hCQ, hDcard, hCreg, hDV, hf, hfrev, hCpol, hDpol,
      hDreg, hgap⟩
  have hlt : 2 / g < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hg] at hlt
  linarith [H.polyadEnergy_le_one C'.skeleton]

/-- **Simultaneous strong lower-skeleton and top regularization with controlled vertex cells.**
Let `g > 0`, let `F, η, μ` be positive schedules, `r` a rank schedule, and `t₀` a vertex-cell
floor. Once `|V|` is at least `strongTriadicRegularityHostBound g F η μ r t₀`, there exist triadic
complexes `C` and `D` (selecting all their polyads) and a reversal-equivariant pair-color
projection `f` from `D` to `C` such that `C` has controlled vertex cells at `t₀` and an
`F`-regular lower skeleton, `D` shares the vertex cells of `C` and refines its pair palette along
`f`, `H` is `(η C.complexity, r C.complexity)`-top-regular over all polyads of `D` outside a
`μ C.complexity`-proportion of the triples, the polyad energy gap from `C` to `D` is at most `g`,
and the vertex cells and pair colors of `C` are bounded independently of `V` by
`strongTriadicRegularityBounds g F η μ r t₀`. -/
theorem exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads [Fintype κ]
    {g : ℝ} (hg : 0 < g) {F η μ : ℕ → ℝ} (hF : ∀ n, 0 < F n) (hη : ∀ n, 0 < η n)
    (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) (t₀ : ℕ)
    (hV : strongTriadicRegularityHostBound g F η μ r t₀ ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      C.VertexCellsControlled t₀ ∧
      #C.skeleton.vertexPart.parts ≤ (strongTriadicRegularityBounds g F η μ r t₀).1 ∧
      C.pairColorCount ≤ (strongTriadicRegularityBounds g F η μ r t₀).2 ∧
      D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      C.skeleton.LowerSkeletonRegular F ∧
      D.skeleton.vertexPart = C.skeleton.vertexPart ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      C.polyads = univ ∧ D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g := by
  have ht₁_pos : 0 < max t₀ 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right t₀ 1)
  have ht₁_le : max t₀ 1 ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans ((le_max_left _ _).trans hV)
  obtain ⟨P₀, hP₀eq, hP₀card⟩ :=
    Finpartition.exists_equipartition_card_eq (s := (univ : Finset V)) ht₁_pos.ne' ht₁_le
  have hVseed : strongTriadicRegularityHostBound g F η μ r #P₀.parts ≤ Fintype.card V := by
    rwa [hP₀card, strongTriadicRegularityHostBound_max_one]
  obtain ⟨C, D, f, hCV, hCeq, hCT, hCQ, hDcard, hCreg, hDV, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_refining_lowerSkeletonRegular_topRegularOverMostPolyads P₀ hP₀eq
      hg hF hη hμ r hVseed
  rw [hP₀card, strongTriadicRegularityBounds_max_one] at hCT hCQ
  have hcells : C.VertexCellsControlled t₀ :=
    TriadicComplex3.vertexCellsControlled_iff.2
      ⟨hCeq, (le_max_left t₀ 1).trans (hP₀card ▸ card_mono hCV)⟩
  exact ⟨C, D, f, hcells, hCT, hCQ, hDcard, hCreg, hDV, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩

/-- **Rödl–Schacht regularity lemma for colored three-graphs.** Let `δ > 0`, `ε > 0`, let `F` be a
positive lower-regularity schedule, `r` a rank schedule, and `t₀` a vertex-cell floor. Once `|V|`
is large enough, there exists a triadic complex `C` selecting all its polyads with controlled
vertex cells at `t₀`, an `F`-regular lower skeleton, host-independent bounds on its vertex cells
and pair colors, and such that `H` is `(δ, r C.complexity)`-top-regular over all polyads of `C`
outside an `ε`-proportion of the injective triples. -/
theorem exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank [Finite κ]
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (r : ℕ → ℕ) (t₀ : ℕ)
    (hV : strongTriadicRegularityHostBound ((ε * δ ^ 2 / (4 * (Nat.card κ + 1))) ^ 2) F
      (fun _ ↦ δ ^ 2 / 2) (fun _ ↦ ε * δ ^ 2 / 4) r t₀ ≤ Fintype.card V) :
    ∃ C : TriadicComplex3 V,
      C.VertexCellsControlled t₀ ∧
      #C.skeleton.vertexPart.parts ≤
        (strongTriadicRegularityBounds ((ε * δ ^ 2 / (4 * (Nat.card κ + 1))) ^ 2) F
          (fun _ ↦ δ ^ 2 / 2) (fun _ ↦ ε * δ ^ 2 / 4) r t₀).1 ∧
      C.pairColorCount ≤
        (strongTriadicRegularityBounds ((ε * δ ^ 2 / (4 * (Nat.card κ + 1))) ^ 2) F
          (fun _ ↦ δ ^ 2 / 2) (fun _ ↦ ε * δ ^ 2 / 4) r t₀).2 ∧
      C.skeleton.LowerSkeletonRegular F ∧
      C.polyads = univ ∧
      H.TopRegularOverMostPolyads C δ ε (r C.complexity) := by
  have := Fintype.ofFinite κ
  set q : ℝ := (Nat.card κ : ℝ)
  set γ := ε * δ ^ 2 / (4 * (q + 1))
  have hγ : 0 < γ := by positivity
  obtain ⟨C, D, f, hcells, hCT, hCQ, -, hCreg, hDV, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads (pow_pos hγ 2) hF
      (η := fun _ ↦ δ ^ 2 / 2) (μ := fun _ ↦ ε * δ ^ 2 / 4)
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) r t₀ hV
  refine ⟨C, hcells, hCT, hCQ, hCreg, hCpol, ?_⟩
  have hdec {C : TriadicComplex3 V} (h : C.polyads = univ) : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ h ▸ mem_univ _
  have hreg := hDreg.of_polyadEnergy_sub_le (hdec hCpol) (hdec hDpol) hDV.le f
    (fun p ↦ (hf p).symm) hgap (by positivity) hδ (by linarith [pow_pos hδ 2])
  refine hreg.mono le_rfl ?_ le_rfl
  rw [Real.sqrt_sq hγ.le, ← Nat.card_eq_fintype_card, div_le_iff₀ (by nlinarith [pow_pos hδ 2])]
  have hqγ : q * γ ≤ ε * δ ^ 2 / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hε (pow_pos hδ 2)]
  linarith

end Colored3Graph

end TauCeti
