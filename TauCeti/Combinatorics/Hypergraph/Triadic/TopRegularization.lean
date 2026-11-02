/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Increment
public import TauCeti.Combinatorics.Hypergraph.Polyad.Refinement
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Top regularity over most polyads by refining the pair palette

Let `H` color the triples of a finite vertex type `V` with a finite palette, and let `S` be a lower
skeleton. If the polyads over `S` at which `H` is not `(η, r)`-top-regular carry a proportion `μ`
of the injective triples, then each of them has a family of `r` subpolyads witnessing the
failure. Refining the pair palette of `S` along all these witnesses at once keeps the vertex
cells, multiplies the number of pair colors by at most `2 ^ (6 r t³ m³)`, where `t` is the
number of vertex cells and `m` the number of pair colors, and raises the polyad energy of `H` by
at least `η³ μ` (`Colored3Graph.exists_refinement_polyadEnergy_add_le`).

The polyad energy lies in `[0, 1]`, so after at most `⌊1 / (η³ ε)⌋₊ + 1` such rounds the
irregular polyads carry at most an `ε`-proportion of the triples. The result is a triadic
complex whose skeleton refines `S` with the same vertex cells, whose palette size is bounded
independently of `V` by `topRegularRefinementBound`, and over most of whose polyads `H` is
top-regular (`Colored3Graph.exists_topRegularOverMostPolyads`). This is the top-level half of
the Rödl–Schacht regularity lemma for three-uniform hypergraphs: it leaves the vertex cells
alone and does not regularize the pair colors.

## Main definitions

* `TauCeti.topRegularRefinementBound`: the bound on the number of pair colors.

## Main results

* `TauCeti.Colored3Graph.exists_refinement_polyadEnergy_add_le`: one round of refinement along
  irregularity witnesses, with its energy gain.
* `TauCeti.Colored3Graph.exists_topRegularOverMostPolyads`: a bounded refinement of the pair
  palette over most of whose polyads the coloring is top-regular.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the index-increment proof of the regularity lemma.
* The regularization of polyad colorings by iterated energy increments, with a palette recursion
  of the same shape `K ↦ K · 2 ^ O(K³)`, appears as `exists_goodPolyadColoring` in the Lean
  library `cameronfreer/regularity-lemmata` (`Hypergraph/`).
-/

public section

open Finset

namespace TauCeti

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V]

/-- The bound on the number of pair colors produced by top regularization. Starting from `m`
pair colors over `t` vertex cells, one round of refinement at rank `r` leads to at most
`m * 2 ^ (6 * r * (t ^ 3 * m ^ 3))` pair colors, and `⌊1 / (η ^ 3 * ε)⌋₊ + 1` rounds suffice for
`(η, r)`-top regularity off an `ε`-proportion of the triples. -/
noncomputable def topRegularRefinementBound (t r : ℕ) (η ε : ℝ) (m : ℕ) : ℕ :=
  (fun m ↦ m * 2 ^ (6 * r * (t ^ 3 * m ^ 3)))^[⌊1 / (η ^ 3 * ε)⌋₊ + 1] m

/-- Unfolding lemma for `topRegularRefinementBound`. -/
theorem topRegularRefinementBound_def (t r : ℕ) (η ε : ℝ) (m : ℕ) :
    topRegularRefinementBound t r η ε m =
      (fun m ↦ m * 2 ^ (6 * r * (t ^ 3 * m ^ 3)))^[⌊1 / (η ^ 3 * ε)⌋₊ + 1] m :=
  (rfl)

namespace Colored3Graph

variable [DecidableEq κ] (H : Colored3Graph κ V)

open Classical in
/-- **One round of top regularization.** Refining the pair palette of `S` along witnesses of
`(η, r)`-top irregularity gives a skeleton `T` with the same vertex cells, whose pair colors
project to those of `S` compatibly with reversal, with a number of pair colors bounded
independently of `V`, and whose polyad energy exceeds that of `S` by at least `η³` times the
proportion of injective triples lying in polyads over `S` at which `H` is not
`(η, r)`-top-regular. -/
theorem exists_refinement_polyadEnergy_add_le [Fintype κ] [Fintype κ₂] (S : PairSkeleton3 κ₂ V)
    {η : ℝ} (hη : 0 ≤ η) (r : ℕ) :
    ∃ (m : ℕ) (T : PairSkeleton3 (Fin m) V) (π : Fin m → κ₂),
      m ≤ Fintype.card κ₂ * 2 ^ (6 * r * (#S.vertexPart.parts ^ 3 * Fintype.card κ₂ ^ 3)) ∧
      T.vertexPart = S.vertexPart ∧
      (∀ p, π (T.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (T.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      η ^ 3 * ((∑ P : Polyad3 S with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ)) /
          (Fintype.card V).descFactorial 3) + H.polyadEnergy S ≤ H.polyadEnergy T := by
  -- Choose `r` subpolyads witnessing the irregularity of each irregular polyad.
  have hw (P : Polyad3 S) : ∃ Q : Fin r → Subpolyad3 P, ¬H.IsTopRegularOverPolyad P η r →
      ∃ c, η * #P.support ≤ #(Subpolyad3.unionSupport Q) ∧
        η < |(H.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) - H.relativeDensity c P| := by
    by_cases hP : H.IsTopRegularOverPolyad P η r
    · exact ⟨fun _ ↦ Subpolyad3.ofSubcells P ∅ ∅ ∅, fun h ↦ (h hP).elim⟩
    · simp only [isTopRegularOverPolyad_iff, not_forall, not_le] at hP
      obtain ⟨c, Q, hQ, hdev⟩ := hP
      exact ⟨Q, fun _ ↦ ⟨c, hQ, hdev⟩⟩
  choose Q hQ using hw
  -- Resolve all witnesses by one bounded refinement, then rename its palette to `Fin m`.
  obtain ⟨κ', _, T, π, hcard, hV, hπ, hrev, hA⟩ :=
    S.exists_bounded_refinement_subpolyads (fun i : Polyad3 S × Fin r ↦ i.1) fun i ↦ Q i.1 i.2
  let e := Fintype.equivFin κ'
  let T' := T.relabel e
  have hT'T (x y) (h : Polyad3.ofTriple T' x = Polyad3.ofTriple T' y) :
      Polyad3.ofTriple T x = Polyad3.ofTriple T y :=
    Polyad3.ofTriple_relabel_eq_ofTriple_relabel_iff e |>.1 h
  have hT'S (x y) (h : Polyad3.ofTriple T' x = Polyad3.ofTriple T' y) :
      Polyad3.ofTriple S x = Polyad3.ofTriple S y :=
    Polyad3.ofTriple_eq_ofTriple_of_le (S := S) (T := T) hV.le π (fun p ↦ (hπ p).symm)
      (hT'T x y h)
  refine ⟨Fintype.card κ', T', π ∘ e.symm, hcard.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right two_pos ?_)), (T.relabel_vertexPart e).trans hV, fun p ↦ by simp [T', hπ],
    fun c ↦ by simp [T', hrev], ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin]
    calc 6 * (Fintype.card (Polyad3 S) * r)
        ≤ 6 * (#S.vertexPart.parts ^ 3 * Fintype.card κ₂ ^ 3 * r) := by
          gcongr
          exact card_polyad3_le S
      _ = 6 * r * (#S.vertexPart.parts ^ 3 * Fintype.card κ₂ ^ 3) := by ring
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- Without top colors every polyad is top-regular, and refining does not lower the energy.
    have hreg (P : Polyad3 S) : H.IsTopRegularOverPolyad P η r :=
      isTopRegularOverPolyad_iff.2 fun c ↦ isEmptyElim c
    simpa [hreg] using H.polyadEnergy_mono_of_refines hT'S
  -- Choose a top color witnessing the irregularity of each irregular polyad.
  have hc (P : Polyad3 S) : ∃ c : κ, ¬H.IsTopRegularOverPolyad P η r →
      η * #P.support ≤ #(Subpolyad3.unionSupport (Q P)) ∧
        η ≤ |(H.relDensityOn c (Subpolyad3.unionSupport (Q P)) : ℝ) - H.relativeDensity c P| := by
    by_cases hP : H.IsTopRegularOverPolyad P η r
    · exact ⟨Classical.arbitrary κ, fun h ↦ (h hP).elim⟩
    · obtain ⟨c, hsize, hdev⟩ := hQ P hP
      exact ⟨c, fun _ ↦ ⟨hsize, hdev.le⟩⟩
  choose c hc using hc
  have hgain := H.polyadEnergy_increment_of_witnesses hT'S
    (univ.filter fun P ↦ ¬H.IsTopRegularOverPolyad P η r) c
    (fun P ↦ Subpolyad3.unionSupport (Q P)) hη (fun P _ ↦ Subpolyad3.unionSupport_subset _)
    (fun P _ x y hxy ↦ by
      -- Each witness support is a union of polyads over `T`, hence over `T'`.
      simp only [Subpolyad3.mem_unionSupport]
      refine exists_congr fun i ↦ ?_
      obtain ⟨A, hAi⟩ := hA (P, i)
      simp only [hAi, mem_biUnion, Polyad3.mem_support_iff_eq_ofTriple,
        hT'T x y hxy])
    (fun P hP ↦ (hc P (mem_filter.1 hP).2).1) (fun P hP ↦ (hc P (mem_filter.1 hP).2).2)
  linarith

open Classical in
/-- Iterating `Colored3Graph.exists_refinement_polyadEnergy_add_le` for `j` rounds either
reaches top regularity off an `ε`-proportion of the triples, or raises the energy by
`j * η ^ 3 * ε`. -/
private theorem exists_refinement_iterate [Fintype κ] [Fintype κ₂] (S : PairSkeleton3 κ₂ V)
    {η ε : ℝ} (hη : 0 ≤ η) (r j : ℕ) :
    ∃ (m : ℕ) (T : PairSkeleton3 (Fin m) V) (π : Fin m → κ₂),
      m ≤ (fun m ↦ m * 2 ^ (6 * r * (#S.vertexPart.parts ^ 3 * m ^ 3)))^[j]
        (Fintype.card κ₂) ∧
      T.vertexPart = S.vertexPart ∧
      (∀ p, π (T.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (T.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      ((∑ P : Polyad3 T with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ)) /
          (Fintype.card V).descFactorial 3 ≤ ε ∨
        j * (η ^ 3 * ε) + H.polyadEnergy S ≤ H.polyadEnergy T) := by
  set g : ℕ → ℕ := fun m ↦ m * 2 ^ (6 * r * (#S.vertexPart.parts ^ 3 * m ^ 3))
  have hg : Monotone g := fun a b hab ↦ by
    simp only [g]
    gcongr
  have hid : id ≤ g := fun m ↦ Nat.le_mul_of_pos_right m (by positivity)
  induction j with
  | zero =>
    let e := Fintype.equivFin κ₂
    refine ⟨_, S.relabel e, e.symm, le_rfl, S.relabel_vertexPart e, fun p ↦ by simp,
      fun c ↦ by simp, Or.inr ?_⟩
    rw [Nat.cast_zero, zero_mul, zero_add]
    exact H.polyadEnergy_mono_of_refines fun x y ↦
      (Polyad3.ofTriple_relabel_eq_ofTriple_relabel_iff e).1
  | succ j ih =>
    obtain ⟨m, T, π, hm, hV, hπ, hrev, hT⟩ := ih
    by_cases hgood : (∑ P : Polyad3 T with ¬H.IsTopRegularOverPolyad P η r,
        (#P.support : ℝ)) / (Fintype.card V).descFactorial 3 ≤ ε
    · exact ⟨m, T, π, hm.trans (Function.monotone_iterate_of_id_le hid j.le_succ _), hV, hπ,
        hrev, Or.inl hgood⟩
    obtain ⟨m', T', π', hm', hV', hπ', hrev', hE⟩ := H.exists_refinement_polyadEnergy_add_le T hη r
    refine ⟨m', T', π ∘ π', ?_, hV'.trans hV, fun p ↦ by simp [hπ', hπ],
      fun c ↦ by simp [hrev', hrev], Or.inr ?_⟩
    · rw [Function.iterate_succ_apply']
      refine hm'.trans ?_
      rw [Fintype.card_fin, hV]
      exact hg hm
    · have hET := hT.resolve_left hgood
      set μ := (∑ P : Polyad3 T with ¬H.IsTopRegularOverPolyad P η r, (#P.support : ℝ)) /
        (Fintype.card V).descFactorial 3
      have hgap : η ^ 3 * ε ≤ η ^ 3 * μ :=
        mul_le_mul_of_nonneg_left (not_le.1 hgood).le (by positivity)
      push_cast
      linarith

/-- **Top regularity over most polyads.** For `0 < η`, `0 < ε` and a rank `r`, every lower
skeleton `S` has a refinement of its pair palette over most of whose polyads `H` is
`(η, r)`-top-regular: there is a triadic complex `C`, selecting all polyads over its skeleton,
whose vertex cells are those of `S`, whose pair colors project to those of `S` compatibly with
reversal, whose number of pair colors is at most
`topRegularRefinementBound #S.vertexPart.parts r η ε (Fintype.card κ₂)`, and such that the
polyads at which `H` is not `(η, r)`-top-regular carry at most an `ε`-proportion of the
injective triples. -/
theorem exists_topRegularOverMostPolyads [Finite κ] [Fintype κ₂] (S : PairSkeleton3 κ₂ V) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (r : ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂),
      C.pairColorCount ≤
        topRegularRefinementBound #S.vertexPart.parts r η ε (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧ H.TopRegularOverMostPolyads C η ε r := by
  classical
  have := Fintype.ofFinite κ
  -- Run enough rounds that their energy gains would together exceed one.
  obtain ⟨K, hKdef, hK⟩ : ∃ K : ℕ, K = ⌊1 / (η ^ 3 * ε)⌋₊ + 1 ∧ 1 < K * (η ^ 3 * ε) := by
    refine ⟨_, rfl, ?_⟩
    rw [← div_lt_iff₀ (by positivity), Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨m, T, π, hm, hV, hπ, hrev, hT⟩ := exists_refinement_iterate H S (ε := ε) hη.le r K
  have hgood := hT.resolve_right fun h ↦ by
    linarith only [h, hK, H.polyadEnergy_nonneg S, H.polyadEnergy_le_one T]
  let C : TriadicComplex3 V := ⟨m, T, univ⟩
  have hdec : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ mem_univ _
  refine ⟨C, π, by rw [topRegularRefinementBound_def, ← hKdef]; exact hm, hV, hπ, hrev, rfl, ?_⟩
  have hsum : ∑ P ∈ C.polyads, (#P.support : ℝ) = (Fintype.card V).descFactorial 3 := by
    exact_mod_cast hdec.sum_card_support
  rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_def, hsum]
  exact hgood

end Colored3Graph

end TauCeti
