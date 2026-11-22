/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability
public import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Strong top regularization over a regular lower skeleton

Strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) refines the
pair palette of a lower skeleton until a coloring `H` of the triples is top-regular over the
polyads of a finer complex at schedules evaluated at the complexity of a coarser one, with a small
polyad energy gap between the two. It keeps the vertex cells and does not regularize the pair
colors, so the coarse lower skeleton is in general not regular.

This file proves the form of the regularity lemma for three-uniform hypergraphs in which the
coarse lower skeleton is itself regular at an arbitrary positive schedule `F`
(`Colored3Graph.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular`). Starting from an
equipartition `P₀`, rounds alternate two steps.

* Top regularization of the current coarse complex `C`, at the schedules `η`, `μ`, `r` evaluated
  at `C.complexity`, gives a palette refinement `D`. If the polyad energy gap from `C` to `D` is
  at most `g`, the pair `(C, D)` is returned.
* Otherwise regular approximation of the pair colors of `D`
  (`PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le`)
  refines the vertex cells to an equipartition and recolors at most a `g / 24` proportion of the
  pairs, giving an `F`-regular lower skeleton. Refining does not lower the energy, and the
  recoloring lowers it by at most `g / 2` (`Colored3Graph.polyadEnergy_le_add_of_vertexPart_eq`),
  so the new coarse complex has energy larger than that of `C` by more than `g / 2`.

Since the energy lies in `[0, 1]`, a round within the first `⌊2 / g⌋₊ + 1` stops. The numbers of
vertex cells and pair colors are bounded independently of `V` by `strongTriadicRegularityBound`,
which is also the size of host required by the regular approximations. Choosing the initial
equipartition to have `max t₀ 1` cells gives controlled vertex cells at `t₀`
(`Colored3Graph.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads`), and transferring top
regularity across the small energy gap yields the scheduled-rank Rödl–Schacht regularity lemma for
colored three-graphs
(`Colored3Graph.exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank`).

## Main definitions

* `TauCeti.strongTriadicRegularityStep`: the bound for one round.
* `TauCeti.strongTriadicRegularityBound`: the bound on the coarse complex and on the host size.

## Main results

* `TauCeti.Colored3Graph.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular`: a coarse
  complex with an `F`-regular lower skeleton on an equipartition refining `P₀`, and a palette
  refinement with energy gap at most `g` over which `H` is top-regular at the schedules evaluated
  at the coarse complexity.
* `TauCeti.Colored3Graph.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads`:
  simultaneous strong lower-skeleton and top regularization with controlled vertex cells.
* `TauCeti.Colored3Graph.exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank`:
  the Rödl–Schacht regularity lemma for colored three-graphs with controlled vertex cells, an
  `F`-regular lower skeleton, and scheduled-rank top regularity.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 and its proof.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- The bound for one round of strong top regularization over a regular lower skeleton, from a
coarse complex with at most `B` vertex cells and at most `B` pair colors. Top regularization at
the schedules evaluated at the coarse complexity leads to at most
`strongTopRegularityStep t η μ r B` pair colors over `t ≤ B` cells, and the regular approximation
of these pair colors at edit tolerance `g / 24` needs a host of at most this size and produces at
most this many vertex cells and pair colors. -/
noncomputable def strongTriadicRegularityStep (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (B : ℕ) : ℕ :=
  (range (B + 1)).sup fun t ↦ (range (strongTopRegularityStep t η μ r B + 1)).sup fun m ↦
    max (pairApproximationBound m (g / 24) F t) (m + 1)

/-- Unfolding lemma for `strongTriadicRegularityStep`. -/
theorem strongTriadicRegularityStep_def (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (B : ℕ) :
    strongTriadicRegularityStep F g η μ r B =
      (range (B + 1)).sup fun t ↦ (range (strongTopRegularityStep t η μ r B + 1)).sup fun m ↦
        max (pairApproximationBound m (g / 24) F t) (m + 1) :=
  (rfl)

/-- One round of strong top regularization over a regular lower skeleton, from at most `t ≤ B`
cells and with at most `strongTopRegularityStep t η μ r B` refined pair colors, is dominated by
`strongTriadicRegularityStep`. -/
theorem max_pairApproximationBound_le_strongTriadicRegularityStep {F : ℕ → ℝ} {g : ℝ}
    {η μ : ℕ → ℝ} {r : ℕ → ℕ} {B t m : ℕ} (ht : t ≤ B)
    (hm : m ≤ strongTopRegularityStep t η μ r B) :
    max (pairApproximationBound m (g / 24) F t) (m + 1) ≤
      strongTriadicRegularityStep F g η μ r B :=
  (le_sup (f := fun m ↦ max (pairApproximationBound m (g / 24) F t) (m + 1))
    (mem_range.2 (Nat.lt_succ_of_le hm))).trans
    (le_sup (f := fun t ↦ (range (strongTopRegularityStep t η μ r B + 1)).sup fun m ↦
      max (pairApproximationBound m (g / 24) F t) (m + 1)) (mem_range.2 (Nat.lt_succ_of_le ht)))

/-- `strongTriadicRegularityStep` strictly increases its argument. -/
theorem lt_strongTriadicRegularityStep (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (B : ℕ) :
    B < strongTriadicRegularityStep F g η μ r B :=
  Nat.lt_succ_of_le (le_strongTopRegularityStep 0 η μ r B) |>.trans_le
    ((le_max_right _ _).trans
      (max_pairApproximationBound_le_strongTriadicRegularityStep (Nat.zero_le B) le_rfl))

/-- The iterates of `strongTriadicRegularityStep` dominate their starting point. -/
theorem le_iterate_strongTriadicRegularityStep (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (j B : ℕ) : B ≤ (strongTriadicRegularityStep F g η μ r)^[j] B :=
  Function.id_le_iterate_of_id_le (fun B ↦ (lt_strongTriadicRegularityStep F g η μ r B).le) j B

/-- The bound in strong top regularization over a regular lower skeleton, starting from an
equipartition with `l₀` parts: it bounds the numbers of vertex cells and pair colors of the coarse
complex and is the size of host required. At most `⌊2 / g⌋₊ + 1` rounds precede an energy gap of
at most `g`. -/
noncomputable def strongTriadicRegularityBound (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (l₀ : ℕ) : ℕ :=
  (strongTriadicRegularityStep F g η μ r)^[⌊2 / g⌋₊ + 1]
    (max (pairApproximationBound 1 (g / 24) F l₀) 6)

/-- Unfolding lemma for `strongTriadicRegularityBound`. -/
theorem strongTriadicRegularityBound_def (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ)
    (l₀ : ℕ) :
    strongTriadicRegularityBound F g η μ r l₀ =
      (strongTriadicRegularityStep F g η μ r)^[⌊2 / g⌋₊ + 1]
        (max (pairApproximationBound 1 (g / 24) F l₀) 6) :=
  (rfl)

/-- `strongTriadicRegularityStep` is monotone in its bound argument. -/
theorem strongTriadicRegularityStep_mono (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) :
    Monotone (strongTriadicRegularityStep F g η μ r) := by
  intro B₁ B₂ hB
  rw [strongTriadicRegularityStep_def, strongTriadicRegularityStep_def]
  refine (Finset.sup_mono_fun fun t _ ↦ Finset.sup_mono (Finset.range_mono
    (Nat.succ_le_succ (strongTopRegularityStep_mono η μ r le_rfl hB)))).trans
    (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hB)))

/-- `strongTriadicRegularityBound` is at least the requested vertex-cell floor `l₀`. -/
theorem le_strongTriadicRegularityBound {F : ℕ → ℝ} {g : ℝ} (hg : 0 < g)
    (hF : ∀ n, 0 < F n) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (l₀ : ℕ) :
    l₀ ≤ strongTriadicRegularityBound F g η μ r l₀ := by
  calc l₀
      ≤ pairApproximationPartsBound 1 (g / 24) F l₀ :=
        le_pairApproximationPartsBound 1 (by positivity) hF l₀
    _ ≤ pairApproximationBound 1 (g / 24) F l₀ :=
        pairApproximationPartsBound_le_pairApproximationBound 1 (by positivity) hF l₀
    _ ≤ max (pairApproximationBound 1 (g / 24) F l₀) 6 := le_max_left _ _
    _ ≤ strongTriadicRegularityBound F g η μ r l₀ := by
        rw [strongTriadicRegularityBound_def]
        exact le_iterate_strongTriadicRegularityStep F g η μ r _ _

/-- `strongTriadicRegularityBound` is monotone in the starting vertex-cell count `l₀`. -/
theorem strongTriadicRegularityBound_mono (F : ℕ → ℝ) (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) :
    Monotone (strongTriadicRegularityBound F g η μ r) := by
  intro l₁ l₂ hl
  rw [strongTriadicRegularityBound_def, strongTriadicRegularityBound_def]
  exact (strongTriadicRegularityStep_mono F g η μ r).iterate _
    (max_le_max (pairApproximationBound_mono 1 (g / 24) F hl) le_rfl)

namespace Colored3Graph

variable [DecidableEq κ] [Fintype κ] (H : Colored3Graph κ V)

/-- **One regularization step.** Regular approximation of a pair coloring `X` over an
equipartition `P`, at edit tolerance `g / 24`, gives a triadic complex with an `F`-regular lower
skeleton on an equipartition refining `P`, selecting all its polyads, with one more pair color
than `X`, over which the polyad energy of `H` is at most `g / 2` below that over `⟨P, X⟩`. -/
private theorem exists_regularization (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) {m : ℕ} (X : PairColorSystem (Fin m) V) {g : ℝ} (hg : 0 < g)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound m (g / 24) F #P.parts ≤ Fintype.card V)
    (h6 : 6 ≤ Fintype.card V) :
    ∃ C : TriadicComplex3 V, C.skeleton.vertexPart ≤ P ∧
      C.skeleton.vertexPart.IsEquipartition ∧ C.skeleton.LowerSkeletonRegular F ∧
      C.polyads = univ ∧
      #C.skeleton.vertexPart.parts ≤ pairApproximationBound m (g / 24) F #P.parts ∧
      C.pairColorCount = m + 1 ∧
      H.polyadEnergy ⟨P, X⟩ ≤ H.polyadEnergy C.skeleton + g / 2 := by
  have hα : 0 < g / 24 := by positivity
  obtain ⟨P', T, hP'P, hP', hcard, -, hreg, -, -, hedit⟩ :=
    X.exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le P hP hα hF
      (by rwa [Fintype.card_fin])
  rw [Fintype.card_fin] at hcard
  let e := Fintype.equivFin (Option (Fin m))
  let S : PairSkeleton3 (Option (Fin m)) V := ⟨P', T⟩
  let C : TriadicComplex3 V := ⟨_, S.relabel e, univ⟩
  have hCV : C.skeleton.vertexPart = P' := S.relabel_vertexPart e
  refine ⟨C, hCV ▸ hP'P, hCV ▸ hP', hreg.relabel e, rfl, hCV ▸ hcard.trans
    (pairApproximationPartsBound_le_pairApproximationBound _ hα hF _), by simp [C], ?_⟩
  -- Refining the cells of `⟨P, X⟩` to those of `S` does not lower the energy, recoloring the
  -- few edited pairs lowers it by at most `g / 2`, and renaming the palette changes nothing.
  have hrefine : H.polyadEnergy ⟨P, X⟩ ≤ H.polyadEnergy ⟨P', X⟩ :=
    H.polyadEnergy_mono_of_refines fun x y ↦
      Polyad3.ofTriple_eq_ofTriple_of_le (S := ⟨P, X⟩) (T := ⟨P', X⟩) hP'P id fun _ ↦ rfl
  have hrecolor : H.polyadEnergy ⟨P', X⟩ ≤ H.polyadEnergy S +
      6 * (#{p | T.color p ≠ some (X.color p)} : ℝ) * Fintype.card V /
        (Fintype.card V).descFactorial 3 :=
    H.polyadEnergy_le_add_of_vertexPart_eq (S := S) (T := ⟨P', X⟩) rfl
      (Option.some_injective (Fin m))
  have hrelabel : H.polyadEnergy S ≤ H.polyadEnergy (S.relabel e) :=
    H.polyadEnergy_mono_of_refines fun x y ↦
      (Polyad3.ofTriple_relabel_eq_ofTriple_relabel_iff e).1
  -- The energy lost by recoloring is at most `6 (g / 24) |V|³ / |V|.descFactorial 3 ≤ g / 2`.
  set n := Fintype.card V
  have hN : (0 : ℝ) < n.descFactorial 3 := Nat.cast_pos.2 (Nat.descFactorial_pos.2 (by omega))
  have hcube : (n : ℝ) ^ 3 ≤ 2 * n.descFactorial 3 := by
    exact_mod_cast Nat.pow_three_le_two_mul_descFactorial_three h6
  have hloss : 6 * (#{p | T.color p ≠ some (X.color p)} : ℝ) * n /
      n.descFactorial 3 ≤ g / 2 := by
    rw [div_le_iff₀ hN]
    calc 6 * (#{p | T.color p ≠ some (X.color p)} : ℝ) * n ≤ 6 * (g / 24 * n ^ 2) * n := by
          gcongr
          -- `hedit` counts the same pairs with another decidability instance for the filter.
          convert hedit using 4
      _ = g / 4 * n ^ 3 := by ring
      _ ≤ g / 4 * (2 * n.descFactorial 3) := by gcongr
      _ = g / 2 * n.descFactorial 3 := by ring
  linarith

/-- The coarse complexes of strong top regularization over a regular lower skeleton: an
`F`-regular lower skeleton on an equipartition refining `P₀`, selecting all its polyads. -/
private def IsRegularCoarse (P₀ : Finpartition (univ : Finset V)) (F : ℕ → ℝ)
    (C : TriadicComplex3 V) : Prop :=
  C.skeleton.vertexPart ≤ P₀ ∧ C.skeleton.vertexPart.IsEquipartition ∧
    C.skeleton.LowerSkeletonRegular F ∧ C.polyads = univ

/-- The stopping condition of strong top regularization: a refinement `D` of the pair palette of
`C` along `f`, with the cells of `C` and all its polyads, over which `H` is top-regular at the
schedules evaluated at `C.complexity`, with polyad energy gap at most `g`. -/
private def HasStrongRefinement (g : ℝ) (η μ : ℕ → ℝ) (r : ℕ → ℕ) (C : TriadicComplex3 V) :
    Prop :=
  ∃ (D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
    D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      D.skeleton.vertexPart = C.skeleton.vertexPart ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g

/-- **One round.** From a coarse complex with at most `B` cells and `B` pair colors, top
regularization either stops, or is followed by a regularization producing a coarse complex
bounded by `strongTriadicRegularityStep F g η μ r B`, with energy larger by more than `g / 2`. -/
private theorem exists_round (P₀ : Finpartition (univ : Finset V)) {g : ℝ} (hg : 0 < g)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {η μ : ℕ → ℝ} (hη : ∀ n, 0 < η n) (hμ : ∀ n, 0 < μ n)
    (r : ℕ → ℕ) {B : ℕ} (hB : strongTriadicRegularityStep F g η μ r B ≤ Fintype.card V)
    (h6 : 6 ≤ Fintype.card V) {C : TriadicComplex3 V} (hCt : #C.skeleton.vertexPart.parts ≤ B)
    (hCm : C.pairColorCount ≤ B) (hC : IsRegularCoarse P₀ F C) :
    H.HasStrongRefinement g η μ r C ∨ ∃ C' : TriadicComplex3 V,
      #C'.skeleton.vertexPart.parts ≤ strongTriadicRegularityStep F g η μ r B ∧
      C'.pairColorCount ≤ strongTriadicRegularityStep F g η μ r B ∧ IsRegularCoarse P₀ F C' ∧
      H.polyadEnergy C.skeleton + g / 2 < H.polyadEnergy C'.skeleton := by
  obtain ⟨hCP₀, hCeq, -, -⟩ := hC
  obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg⟩ :=
    H.exists_topRegularOverMostPolyads C.skeleton (hη C.complexity) (hμ C.complexity)
      (r C.complexity)
  rw [Fintype.card_fin] at hDcard
  by_cases hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g
  · exact Or.inl ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩
  refine Or.inr ?_
  -- The refined palette is small enough for one bounded round of regular approximation.
  have hDstep : D.pairColorCount ≤ strongTopRegularityStep #C.skeleton.vertexPart.parts η μ r B :=
    hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η μ r hCm
      (C.complexity_le.trans (by gcongr)))
  have hround :=
    max_pairApproximationBound_le_strongTriadicRegularityStep (F := F) (g := g) hCt hDstep
  have hhost : pairApproximationBound D.pairColorCount (g / 24) F
      #D.skeleton.vertexPart.parts ≤ strongTriadicRegularityStep F g η μ r B := by
    rw [hDV]
    exact (le_max_left _ _).trans hround
  obtain ⟨C', hC'P, hC'eq, hC'reg, hC'pol, hC'card, hC'col, hE⟩ :=
    H.exists_regularization D.skeleton.vertexPart (hDV ▸ hCeq) D.skeleton.pairColors hg hF
      (hhost.trans hB) h6
  refine ⟨C', hC'card.trans hhost, hC'col ▸ (le_max_right _ _).trans hround,
    ⟨hC'P.trans (hDV ▸ hCP₀), hC'eq, hC'reg, hC'pol⟩, ?_⟩
  linarith [not_le.1 hgap]

/-- **The iteration.** After `j` rounds, starting from the regularization of the one-color
skeleton on `P₀`, either some coarse complex bounded by the `j`-th iterate of
`strongTriadicRegularityStep` stops, or one has energy at least `j * (g / 2)`. -/
private theorem exists_iterate (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    {g : ℝ} (hg : 0 < g) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {η μ : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) (j : ℕ)
    (hj : (strongTriadicRegularityStep F g η μ r)^[j]
      (max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6) ≤ Fintype.card V) :
    (∃ C : TriadicComplex3 V, #C.skeleton.vertexPart.parts ≤
        (strongTriadicRegularityStep F g η μ r)^[j]
          (max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6) ∧
      C.pairColorCount ≤ (strongTriadicRegularityStep F g η μ r)^[j]
          (max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6) ∧
      IsRegularCoarse P₀ F C ∧ H.HasStrongRefinement g η μ r C) ∨
    ∃ C : TriadicComplex3 V, #C.skeleton.vertexPart.parts ≤
        (strongTriadicRegularityStep F g η μ r)^[j]
          (max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6) ∧
      C.pairColorCount ≤ (strongTriadicRegularityStep F g η μ r)^[j]
          (max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6) ∧
      IsRegularCoarse P₀ F C ∧ j * (g / 2) ≤ H.polyadEnergy C.skeleton := by
  set step := strongTriadicRegularityStep F g η μ r
  set B₀ := max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6
  induction j with
  | zero =>
    -- Regularize the one-color skeleton on `P₀`.
    have h6 : 6 ≤ Fintype.card V := (le_max_right _ _).trans hj
    let X : PairColorSystem (Fin 1) V := ⟨fun _ ↦ 0, id, fun _ ↦ rfl, fun _ ↦ rfl⟩
    obtain ⟨C, hCP, hCeq, hCreg, hCpol, hCcard, hCcol, -⟩ :=
      H.exists_regularization P₀ hP₀ X hg hF ((le_max_left _ _).trans hj) h6
    refine Or.inr ⟨C, hCcard.trans (le_max_left _ _), hCcol ▸ le_max_of_le_right (by norm_num),
      ⟨hCP, hCeq, hCreg, hCpol⟩, by simpa using H.polyadEnergy_nonneg _⟩
  | succ j ih =>
    have h6 : 6 ≤ Fintype.card V :=
      (le_max_right _ _).trans
        ((le_iterate_strongTriadicRegularityStep F g η μ r (j + 1) B₀).trans hj)
    rw [Function.iterate_succ_apply'] at hj ⊢
    have hle := (lt_strongTriadicRegularityStep F g η μ r (step^[j] B₀)).le
    obtain ⟨C, hCt, hCm, hC, hgood⟩ | ⟨C, hCt, hCm, hC, hE⟩ := ih (hle.trans hj)
    · exact Or.inl ⟨C, hCt.trans hle, hCm.trans hle, hC, hgood⟩
    obtain hgood | ⟨C', hC't, hC'm, hC', hE'⟩ :=
      H.exists_round P₀ hg hF hη hμ r hj h6 hCt hCm hC
    · exact Or.inl ⟨C, hCt.trans hle, hCm.trans hle, hC, hgood⟩
    refine Or.inr ⟨C', hC't, hC'm, hC', ?_⟩
    push_cast
    linarith

/-- **Strong top regularization over a regular lower skeleton.** Let `P₀` be an equipartition,
`g > 0`, `F`, `η`, `μ` positive schedules and `r` a rank schedule, and let the host have at least
`strongTriadicRegularityBound F g η μ r #P₀.parts` vertices. There is a triadic complex `C`,
selecting all its polyads, whose vertex cells form an equipartition refining `P₀` and whose lower
skeleton is `F`-regular, together with a refinement `D` of its pair palette along `f`, with the
same vertex cells and all its polyads, such that the polyad energy gap of `H` from `C` to `D` is
at most `g` and `H` is `(η C.complexity, r C.complexity)`-top-regular over all polyads of `D`
outside a `μ C.complexity`-proportion of the injective triples. The numbers of vertex cells and
pair colors of `C` are at most `strongTriadicRegularityBound F g η μ r #P₀.parts`, and that of `D`
is bounded by top regularization at the schedules evaluated at `C.complexity`. -/
theorem exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {g : ℝ} (hg : 0 < g)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {η μ : ℕ → ℝ} (hη : ∀ n, 0 < η n) (hμ : ∀ n, 0 < μ n)
    (r : ℕ → ℕ) (hV : strongTriadicRegularityBound F g η μ r #P₀.parts ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      #C.skeleton.vertexPart.parts ≤ strongTriadicRegularityBound F g η μ r #P₀.parts ∧
      C.pairColorCount ≤ strongTriadicRegularityBound F g η μ r #P₀.parts ∧
      D.pairColorCount ≤ topRegularRefinementBound #C.skeleton.vertexPart.parts (r C.complexity)
        (η C.complexity) (μ C.complexity) C.pairColorCount ∧
      C.skeleton.vertexPart ≤ P₀ ∧ C.skeleton.vertexPart.IsEquipartition ∧
      D.skeleton.vertexPart = C.skeleton.vertexPart ∧ C.skeleton.LowerSkeletonRegular F ∧
      (∀ p, f (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p) ∧
      (∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c)) ∧
      C.polyads = univ ∧ D.polyads = univ ∧
      H.TopRegularOverMostPolyads D (η C.complexity) (μ C.complexity) (r C.complexity) ∧
      H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g := by
  -- Each round that does not stop raises the energy by more than `g / 2`, and the energy lies in
  -- `[0, 1]`, so a round within the first `⌊2 / g⌋₊ + 1` stops.
  set step := strongTriadicRegularityStep F g η μ r
  set B₀ := max (pairApproximationBound 1 (g / 24) F #P₀.parts) 6
  rw [strongTriadicRegularityBound_def, Function.iterate_succ_apply'] at hV ⊢
  have hle : step^[⌊2 / g⌋₊] B₀ ≤ step (step^[⌊2 / g⌋₊] B₀) :=
    (lt_strongTriadicRegularityStep F g η μ r _).le
  have h6 : 6 ≤ Fintype.card V := (le_max_right _ _).trans
    ((le_iterate_strongTriadicRegularityStep F g η μ r _ B₀).trans (hle.trans hV))
  have hK : 1 < (⌊2 / g⌋₊ + 1 : ℕ) * (g / 2) := by
    rw [← div_lt_iff₀ (by positivity), one_div_div, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hCt, hCm, hC, hgood⟩ : ∃ C : TriadicComplex3 V,
      #C.skeleton.vertexPart.parts ≤ step (step^[⌊2 / g⌋₊] B₀) ∧
        C.pairColorCount ≤ step (step^[⌊2 / g⌋₊] B₀) ∧ IsRegularCoarse P₀ F C ∧
        H.HasStrongRefinement g η μ r C := by
    obtain ⟨C, hCt, hCm, hC, hgood⟩ | ⟨C, hCt, hCm, hC, hE⟩ :=
      H.exists_iterate P₀ hP₀ hg hF hη hμ r ⌊2 / g⌋₊ (hle.trans hV)
    · exact ⟨C, hCt.trans hle, hCm.trans hle, hC, hgood⟩
    obtain hgood | ⟨C', -, -, -, hE'⟩ := H.exists_round P₀ hg hF hη hμ r hV h6 hCt hCm hC
    · exact ⟨C, hCt.trans hle, hCm.trans hle, hC, hgood⟩
    push_cast at hK
    linarith [H.polyadEnergy_le_one C'.skeleton]
  obtain ⟨hCP₀, hCeq, hCreg, hCpol⟩ := hC
  obtain ⟨D, f, hDcard, hDV, hf, hfrev, hDpol, hDreg, hgap⟩ := hgood
  exact ⟨C, D, f, hCt, hCm, hDcard, hCP₀, hCeq, hDV, hCreg, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩

/-- **Simultaneous strong lower-skeleton and top regularization with controlled vertex cells.**
Let `g > 0`, let `F`, `η`, `μ` be positive schedules, `r` a rank schedule, and `t₀` a vertex-cell
floor. Once `|V|` is at least `strongTriadicRegularityBound F g η μ r (max t₀ 1)`, there exist
triadic complexes `C` and `D` (selecting all their polyads) and a reversal-equivariant pair-color
projection `f` from `D` to `C` such that `C` has controlled vertex cells at `t₀` and an
`F`-regular lower skeleton, `D` shares the vertex cells of `C` and refines its pair palette along
`f`, `H` is `(η C.complexity, r C.complexity)`-top-regular over all polyads of `D` outside a
`μ C.complexity`-proportion of the triples, the polyad energy gap from `C` to `D` is at most `g`,
and the vertex cells and pair colors of `C` are bounded independently of `V` by
`strongTriadicRegularityBound F g η μ r (max t₀ 1)`. -/
theorem exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads
    {g : ℝ} (hg : 0 < g) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {η μ : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) (t₀ : ℕ)
    (hV : strongTriadicRegularityBound F g η μ r (max t₀ 1) ≤ Fintype.card V) :
    ∃ (C D : TriadicComplex3 V) (f : Fin D.pairColorCount → Fin C.pairColorCount),
      C.VertexCellsControlled t₀ ∧
      #C.skeleton.vertexPart.parts ≤ strongTriadicRegularityBound F g η μ r (max t₀ 1) ∧
      C.pairColorCount ≤ strongTriadicRegularityBound F g η μ r (max t₀ 1) ∧
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
    exact (le_strongTriadicRegularityBound hg hF η μ r (max t₀ 1)).trans hV
  obtain ⟨P₀, hP₀eq, hP₀card⟩ :=
    Finpartition.exists_equipartition_card_eq (s := (univ : Finset V)) ht₁_pos.ne' ht₁_le
  obtain ⟨C, D, f, hCt, hCm, hDcard, hCV, hCeq, hDV, hCreg, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular P₀ hP₀eq hg hF hη hμ r
      (by rwa [hP₀card])
  rw [hP₀card] at hCt hCm
  have hcells : C.VertexCellsControlled t₀ :=
    TriadicComplex3.vertexCellsControlled_iff.2
      ⟨hCeq, (le_max_left t₀ 1).trans (hP₀card ▸ Finpartition.card_mono hCV)⟩
  exact ⟨C, D, f, hcells, hCt, hCm, hDcard, hCreg, hDV, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩

omit [Fintype κ] in
/-- **Rödl–Schacht regularity lemma for colored three-graphs.** Let `δ > 0`, `ε > 0`, let `F` be a
positive lower-regularity schedule, `r` a rank schedule, and `t₀` a vertex-cell floor. Once `|V|`
is large enough, there exists a triadic complex `C` selecting all its polyads with controlled
vertex cells at `t₀`, an `F`-regular lower skeleton, host-independent bounds on its vertex cells
and pair colors, and such that `H` is `(δ, r C.complexity)`-top-regular over all polyads of `C`
outside an `ε`-proportion of the injective triples. -/
theorem exists_lowerSkeletonRegular_topRegularOverMostPolyads_scheduledRank [Finite κ]
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (r : ℕ → ℕ) (t₀ : ℕ) :
    let B := strongTriadicRegularityBound F (topRegularEnergyGap (Nat.card κ) δ ε)
      (fun _ ↦ topRegularFineTolerance δ) (fun _ ↦ topRegularFineProportion δ ε) r (max t₀ 1)
    B ≤ Fintype.card V →
    ∃ C : TriadicComplex3 V,
      C.VertexCellsControlled t₀ ∧
      #C.skeleton.vertexPart.parts ≤ B ∧
      C.pairColorCount ≤ B ∧
      C.skeleton.LowerSkeletonRegular F ∧
      C.polyads = univ ∧
      H.TopRegularOverMostPolyads C δ ε (r C.complexity) := by
  intro B hV
  have := Fintype.ofFinite κ
  obtain ⟨C, D, f, hcells, hCt, hCm, -, hCreg, hDV, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_lowerSkeletonRegular_topRegularOverMostPolyads
      (topRegularEnergyGap_pos (Nat.card κ) hδ hε) hF
      (fun _ ↦ topRegularFineTolerance_pos hδ) (fun _ ↦ topRegularFineProportion_pos hδ hε)
      r t₀ hV
  exact ⟨C, hcells, hCt, hCm, hCreg, hCpol,
    hDreg.of_polyadEnergy_sub_le_topRegularEnergyGap
      (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
      (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) hDV.le f
      (fun p ↦ (hf p).symm) hgap hδ⟩

end Colored3Graph

end TauCeti
