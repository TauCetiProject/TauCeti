/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.BorelColoring
import TauCeti.MeasureTheory.Constructions.Polish.Analytic

/-!
# Miller's ideal of small families of assignments

Fix a relation `G : SetRel X X` on a measurable space `X`, read as a directed graph in which loops
are allowed. An *assignment* is a map `φ : ι → X`, which labels the points of an index type
`ι` (in applications, the vertices of a finite approximation to a graph homomorphism) by points
of `X`. A family `Φ : Set (ι → X)` of assignments is **small** (`SetRel.IsSmallFamily G Φ`) if
countably many measurable `G`-independent sets capture a value of every member of `Φ`: some
`B : ℕ → Set X` of measurable independent sets has, for each `φ ∈ Φ`, some `i` and `n` with
`φ i ∈ B n`.

The small families form a σ-ideal (`SetRel.isSmallFamily_iUnion`), so a family that is not small
and is covered by countably many pieces has a piece that is not small
(`SetRel.exists_not_isSmallFamily_inter`). For nonempty `ι` the family of all assignments is
small exactly when `G` has a countable Borel coloring (`SetRel.isSmallFamily_univ_iff`). This is
the ideal through which B. D. Miller proves the Kechris–Solecki–Todorcevic G₀ dichotomy: starting
from the family of all assignments, which is not small when `G` has no countable Borel coloring,
one refines and amalgamates families while keeping them analytic and not small, and reads a
continuous homomorphism from the graph G₀ into `G` off the limit of the construction.

The steps of that construction are the following statements.

* *Amalgamation.* Let `comb : (ι → X) → (ι → X) → κ → X` take only values of its arguments. If `Φ`
  is not small, neither is the family `Set.image2 comb Φ Φ` of combinations of its members
  (`SetRel.not_isSmallFamily_image2`). If moreover `ι` is countable and `X` is a Hausdorff space
  with its Borel σ-algebra, and `Φ` and `G` are analytic, then neither is the family of
  combinations of pairs `φ₀, φ₁ ∈ Φ` joined by an edge `(φ₀ s, φ₁ s) ∈ G` at a designated index `s`
  (`SetRel.not_isSmallFamily_comb_cross`). This is where the Kechris–Solecki–Todorcevic lemma
  `SetRel.exists_measurableSet_isIndependent_superset` enters. When `comb` is jointly continuous
  both combined families are analytic (`MeasureTheory.AnalyticSet.image2`,
  `SetRel.analyticSet_comb_cross`).
* *Vertex shrinking.* For finite `ι`, a family that is not small has, for any countable cover of
  `X`, a subfamily that is not small whose members take each coordinate in one prescribed piece
  of the cover (`SetRel.exists_not_isSmallFamily_inter_pi`). In a separable pseudometric space
  this gives, for every `ε > 0`, an analytic subfamily that is not small and whose members are
  uniformly within `ε` of each other at every coordinate
  (`SetRel.exists_subset_not_isSmallFamily_dist_lt`).

## Main definitions

* `SetRel.IsSmallFamily G Φ`: countably many measurable `G`-independent sets capture a value of
  every member of `Φ`.

## Main results

* `SetRel.isSmallFamily_iff_exists_countable`: smallness through a countable set of capturing sets.
* `SetRel.isSmallFamily_iUnion`: small families form a σ-ideal.
* `SetRel.isSmallFamily_univ_iff`: for nonempty `ι`, all assignments form a small family iff `G`
  has a countable Borel coloring.
* `SetRel.IsSmallFamily.of_exists_range_subset`: smallness transfers back along families whose
  members take only values of members of the original family.
* `SetRel.not_isSmallFamily_image2`, `SetRel.not_isSmallFamily_comb_cross`: amalgamation keeps
  families from being small.
* `SetRel.exists_not_isSmallFamily_inter_pi`, `SetRel.exists_subset_not_isSmallFamily_dist_lt`:
  vertex shrinking.

## References

* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of Symbolic
  Logic 18 (2012), 554–575: the classical proof of the G₀ dichotomy through this ideal.
* A. S. Kechris, S. Solecki and S. Todorcevic, *Borel chromatic numbers*, Advances in Mathematics
  141 (1999), 1–44: the G₀ dichotomy and the independent-superset lemma.
* `SetRel.IsSmallFamily` corresponds to `SmallFam` in `InfinitaryLogic/Descriptive/G0Dichotomy.lean`
  and `InfinitaryLogic/Descriptive/G0Fusion.lean` of `cameronfreer/infinitary-logic`
  (Apache-2.0), commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. Here the ideal is stated for an
  arbitrary relation on a measurable space, and the amalgamation statements for any combination
  map whose values are values of its arguments.
-/

public section

open MeasureTheory Set

namespace SetRel

variable {X ι κ : Type*} [MeasurableSpace X] {G H : SetRel X X} {Φ Ψ : Set (ι → X)}

/-- A family `Φ` of assignments `ι → X` is **small** for a relation `G` if countably many
measurable `G`-independent sets capture a value of every member of `Φ`. -/
def IsSmallFamily (G : SetRel X X) (Φ : Set (ι → X)) : Prop :=
  ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n) ∧ G.IsIndependent (B n)) ∧
    ∀ φ ∈ Φ, ∃ i n, φ i ∈ B n

/-- Unfolding lemma for `SetRel.IsSmallFamily`. -/
theorem isSmallFamily_iff :
    G.IsSmallFamily Φ ↔ ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n) ∧ G.IsIndependent (B n)) ∧
      ∀ φ ∈ Φ, ∃ i n, φ i ∈ B n :=
  Iff.rfl

/-- A family is small iff some countable set of measurable independent sets captures a value of
every member. -/
theorem isSmallFamily_iff_exists_countable :
    G.IsSmallFamily Φ ↔ ∃ 𝒞 : Set (Set X), 𝒞.Countable ∧
      (∀ C ∈ 𝒞, MeasurableSet C ∧ G.IsIndependent C) ∧ ∀ φ ∈ Φ, ∃ i, ∃ C ∈ 𝒞, φ i ∈ C := by
  refine ⟨fun ⟨B, hB, hΦ⟩ ↦ ⟨range B, countable_range B, forall_mem_range.2 hB, fun φ hφ ↦ ?_⟩,
    fun ⟨𝒞, h𝒞, hB, hΦ⟩ ↦ ?_⟩
  · obtain ⟨i, n, hn⟩ := hΦ φ hφ
    exact ⟨i, B n, mem_range_self n, hn⟩
  -- Enumerate `𝒞` together with the empty set, which keeps the enumerated set nonempty.
  obtain ⟨B, hB'⟩ := (h𝒞.insert ∅).exists_eq_range (insert_nonempty _ _)
  refine ⟨B, fun n ↦ ?_, fun φ hφ ↦ ?_⟩
  · rcases (hB' ▸ mem_range_self n : B n ∈ insert ∅ 𝒞) with h | h
    · rw [h]
      exact ⟨.empty, .empty⟩
    · exact hB _ h
  · obtain ⟨i, C, hC, hφC⟩ := hΦ φ hφ
    obtain ⟨n, rfl⟩ : C ∈ range B := hB' ▸ mem_insert_of_mem _ hC
    exact ⟨i, n, hφC⟩

/-- Smallness for a relation passes to its subrelations. -/
theorem IsSmallFamily.mono_left (hHG : H ⊆ G) (h : G.IsSmallFamily Φ) : H.IsSmallFamily Φ :=
  let ⟨B, hB, hΦ⟩ := h
  ⟨B, fun n ↦ ⟨(hB n).1, (hB n).2.mono_left hHG⟩, hΦ⟩

/-- Smallness passes to subfamilies. -/
theorem IsSmallFamily.mono_right (hΨΦ : Ψ ⊆ Φ) (h : G.IsSmallFamily Φ) : G.IsSmallFamily Ψ :=
  let ⟨B, hB, hΦ⟩ := h
  ⟨B, hB, fun φ hφ ↦ hΦ φ (hΨΦ hφ)⟩

/-- The empty family is small. -/
@[simp]
theorem isSmallFamily_empty : G.IsSmallFamily (∅ : Set (ι → X)) :=
  ⟨fun _ ↦ ∅, fun _ ↦ ⟨.empty, .empty⟩, fun _ h ↦ h.elim⟩

/-- **Small families form a σ-ideal.** A countable union of families is small iff each of them
is. -/
@[simp]
theorem isSmallFamily_iUnion [Countable κ] {Φ : κ → Set (ι → X)} :
    G.IsSmallFamily (⋃ k, Φ k) ↔ ∀ k, G.IsSmallFamily (Φ k) := by
  refine ⟨fun h k ↦ h.mono_right (subset_iUnion Φ k), fun h ↦ ?_⟩
  choose B hB hΦ using h
  refine isSmallFamily_iff_exists_countable.2 ⟨range (Function.uncurry B), countable_range _,
    forall_mem_range.2 fun p ↦ hB p.1 p.2, fun φ hφ ↦ ?_⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hφ
  obtain ⟨i, n, hn⟩ := hΦ k φ hk
  exact ⟨i, B k n, ⟨(k, n), rfl⟩, hn⟩

/-- A union of two families is small iff both are. -/
@[simp]
theorem isSmallFamily_union : G.IsSmallFamily (Φ ∪ Ψ) ↔ G.IsSmallFamily Φ ∧ G.IsSmallFamily Ψ := by
  rw [union_eq_iUnion, isSmallFamily_iUnion, Bool.forall_bool, and_comm, Bool.cond_true,
    Bool.cond_false]

/-- **Pigeonhole for small families.** If a family that is not small is covered by countably
many families, its intersection with one of them is not small. -/
theorem exists_not_isSmallFamily_inter [Countable κ] {Ψ : κ → Set (ι → X)}
    (hΦ : ¬ G.IsSmallFamily Φ) (hcov : Φ ⊆ ⋃ k, Ψ k) : ∃ k, ¬ G.IsSmallFamily (Φ ∩ Ψ k) := by
  by_contra! h
  refine hΦ ?_
  rw [← inter_eq_left.2 hcov, inter_iUnion]
  exact isSmallFamily_iUnion.2 h

/-- A family that is not small is nonempty. -/
theorem nonempty_of_not_isSmallFamily (hΦ : ¬ G.IsSmallFamily Φ) : Φ.Nonempty :=
  nonempty_iff_ne_empty.2 fun h ↦ hΦ (h ▸ isSmallFamily_empty)

/-- **The seed of the G₀ construction.** For nonempty `ι`, the family of all assignments is small
iff the relation has a countable Borel coloring. -/
theorem isSmallFamily_univ_iff [Nonempty ι] :
    G.IsSmallFamily (univ : Set (ι → X)) ↔ G.HasCountableBorelColoring := by
  rw [hasCountableBorelColoring_iff_exists_cover]
  refine ⟨fun ⟨B, hB, hΦ⟩ ↦ ⟨B, hB, iUnion_eq_univ_iff.2 fun x ↦ ?_⟩,
    fun ⟨B, hB, hcov⟩ ↦ ⟨B, hB, fun φ _ ↦ ?_⟩⟩
  · -- A constant assignment is captured at its only value.
    obtain ⟨-, n, hn⟩ := hΦ (fun _ : ι ↦ x) (mem_univ _)
    exact ⟨n, hn⟩
  · obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.1 hcov (φ (Classical.arbitrary ι))
    exact ⟨_, n, hn⟩

/-- Smallness transfers back along value inclusion: if `Ψ` is small and every member of `Φ` has
all values of some member of `Ψ` among its own values, then `Φ` is small. -/
theorem IsSmallFamily.of_exists_range_subset {Ψ : Set (κ → X)} (hΨ : G.IsSmallFamily Ψ)
    (h : ∀ φ ∈ Φ, ∃ ψ ∈ Ψ, range ψ ⊆ range φ) : G.IsSmallFamily Φ := by
  obtain ⟨B, hB, hcap⟩ := hΨ
  refine ⟨B, hB, fun φ hφ ↦ ?_⟩
  obtain ⟨ψ, hψ, hsub⟩ := h φ hφ
  obtain ⟨v, n, hn⟩ := hcap ψ hψ
  obtain ⟨i, hi⟩ := hsub (mem_range_self v)
  exact ⟨i, n, hi ▸ hn⟩

/-- **Amalgamation keeps families from being small.** If `Φ` is not small and `comb φ φ` takes
only values of `φ`, then the family of combinations `comb φ₀ φ₁` of members of `Φ` is not
small. -/
theorem not_isSmallFamily_image2 (hΦ : ¬ G.IsSmallFamily Φ) {comb : (ι → X) → (ι → X) → κ → X}
    (hcomb : ∀ φ, range (comb φ φ) ⊆ range φ) : ¬ G.IsSmallFamily (image2 comb Φ Φ) :=
  fun h ↦ hΦ <| h.of_exists_range_subset fun φ hφ ↦ ⟨comb φ φ, mem_image2_of_mem hφ hφ, hcomb φ⟩

/-- **Amalgamation across a fresh edge keeps analytic families from being small.** Let `X` be a
Hausdorff space with its Borel σ-algebra, `G` an analytic relation, `ι` countable, and `Φ` an
analytic family that is not small. If `comb φ₀ φ₁` takes only values of `φ₀` and `φ₁`, then for
every index `s` the family of combinations `comb φ₀ φ₁` of members `φ₀, φ₁ ∈ Φ` with
`(φ₀ s, φ₁ s) ∈ G` is not small. -/
theorem not_isSmallFamily_comb_cross [TopologicalSpace X] [T2Space X] [BorelSpace X]
    [Countable ι] (hG : AnalyticSet G) (hΦa : AnalyticSet Φ) (hΦ : ¬ G.IsSmallFamily Φ) (s : ι)
    {comb : (ι → X) → (ι → X) → κ → X}
    (hcomb : ∀ φ₀ φ₁, range (comb φ₀ φ₁) ⊆ range φ₀ ∪ range φ₁) :
    ¬ G.IsSmallFamily {ψ | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ comb φ₀ φ₁ = ψ} := by
  rintro ⟨B, hB, hcap⟩
  -- The members of `Φ` with no value in any `B n` still form a family that is not small, since
  -- `B` captures all the other members.
  set Φ' := {φ ∈ Φ | ∀ i n, φ i ∉ B n} with hΦ'_def
  have hcapB : G.IsSmallFamily {φ : ι → X | ∃ i n, φ i ∈ B n} := ⟨B, hB, fun _ h ↦ h⟩
  have hΦ' : ¬ G.IsSmallFamily Φ' := by
    refine fun h ↦ hΦ ((isSmallFamily_union.2 ⟨h, hcapB⟩).mono_right fun φ hφ ↦ ?_)
    by_cases hφB : ∀ i n, φ i ∉ B n
    exacts [.inl ⟨hφ, hφB⟩, .inr (by simpa using hφB)]
  -- `Φ'` is analytic: it is cut out of `Φ` by countably many Borel conditions.
  have hΦ'a : AnalyticSet Φ' := by
    borelize (ι → X)
    have : Φ' = Φ ∩ ⋂ i, ⋂ n, (fun φ : ι → X ↦ φ i) ⁻¹' (B n)ᶜ := by
      ext φ
      simp [hΦ'_def]
    rw [this]
    exact hΦa.inter_measurableSet <| .iInter fun i ↦ .iInter fun n ↦
      (continuous_apply i).measurable (hB n).1.compl
  -- The values at `s` of members of `Φ'` form an analytic independent set: an edge between two
  -- of them yields a combination whose values avoid every `B n`, so it is not captured.
  have hind : G.IsIndependent ((fun φ : ι → X ↦ φ s) '' Φ') := by
    rw [isIndependent_iff]
    rintro _ ⟨φ₀, ⟨hφ₀, h₀⟩, rfl⟩ _ ⟨φ₁, ⟨hφ₁, h₁⟩, rfl⟩ hedge
    obtain ⟨v, n, hn⟩ := hcap _ ⟨φ₀, hφ₀, φ₁, hφ₁, hedge, rfl⟩
    rcases hcomb φ₀ φ₁ (mem_range_self v) with ⟨i, hi⟩ | ⟨i, hi⟩
    exacts [h₀ i n (hi ▸ hn), h₁ i n (hi ▸ hn)]
  -- By the Kechris–Solecki–Todorcevic lemma that set lies in a Borel independent set, which then
  -- captures every member of `Φ'` at `s`.
  obtain ⟨C, hCm, hsC, hCi⟩ := exists_measurableSet_isIndependent_superset hG
    (hΦ'a.image_of_continuous (continuous_apply s)) hind
  exact hΦ' ⟨fun _ ↦ C, fun _ ↦ ⟨hCm, hCi⟩, fun φ hφ ↦ ⟨s, 0, hsC (mem_image_of_mem _ hφ)⟩⟩

omit [MeasurableSpace X] in
/-- For a jointly continuous combination map and an analytic relation on a Hausdorff space, the
combinations of pairs of members of an analytic family joined by an edge at a designated index
form an analytic family. -/
theorem analyticSet_comb_cross [TopologicalSpace X] [T2Space X] (hG : AnalyticSet G)
    (hΦ : AnalyticSet Φ) (s : ι) {comb : (ι → X) → (ι → X) → κ → X}
    (hcomb : Continuous (Function.uncurry comb)) :
    AnalyticSet {ψ | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ comb φ₀ φ₁ = ψ} := by
  have : {ψ | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ comb φ₀ φ₁ = ψ} =
      Function.uncurry comb '' (Φ ×ˢ Φ ∩ (fun p : (ι → X) × (ι → X) ↦ (p.1 s, p.2 s)) ⁻¹' G) := by
    ext ψ
    simp [and_assoc]
  rw [this]
  exact ((hΦ.prod hΦ).inter_preimage (by fun_prop) hG).image_of_continuous hcomb

/-- **Vertex shrinking.** For finite `ι` and a countable cover `U` of `X`, a family that is not
small has a subfamily that is not small whose members take each coordinate `i` in one piece
`U (c i)`. -/
theorem exists_not_isSmallFamily_inter_pi [Finite ι] [Countable κ] {U : κ → Set X}
    (hU : ⋃ k, U k = univ) (hΦ : ¬ G.IsSmallFamily Φ) :
    ∃ c : ι → κ, ¬ G.IsSmallFamily (Φ ∩ univ.pi fun i ↦ U (c i)) :=
  exists_not_isSmallFamily_inter hΦ fun φ _ ↦ by
    choose c hc using fun i ↦ iUnion_eq_univ_iff.1 hU (φ i)
    exact mem_iUnion.2 ⟨c, fun i _ ↦ hc i⟩

/-- **Vertex shrinking in a metric.** In a separable pseudometric space, for finite `ι` and
`ε > 0`, an analytic family that is not small has an analytic subfamily that is not small and
whose members are within `ε` of each other at every coordinate. -/
theorem exists_subset_not_isSmallFamily_dist_lt [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [Finite ι] (hΦa : AnalyticSet Φ)
    (hΦ : ¬ G.IsSmallFamily Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ ⊆ Φ, AnalyticSet Ψ ∧ ¬ G.IsSmallFamily Ψ ∧
      ∀ φ ∈ Ψ, ∀ ψ ∈ Ψ, ∀ i, dist (φ i) (ψ i) < ε := by
  -- Cover `X` by the balls of radius `ε / 2` about a countable dense set.
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense X
  have := hSc.to_subtype
  have hU : ⋃ x : S, Metric.ball (x : X) (ε / 2) = univ := by
    refine iUnion_eq_univ_iff.2 fun y ↦ ?_
    obtain ⟨x, hx, hxy⟩ := hSd.exists_dist_lt y (half_pos hε)
    exact ⟨⟨x, hx⟩, Metric.mem_ball.2 (dist_comm x y ▸ hxy)⟩
  obtain ⟨c, hc⟩ := exists_not_isSmallFamily_inter_pi hU hΦ
  refine ⟨_, inter_subset_left, ?_, hc, fun φ ⟨_, hφ⟩ ψ ⟨_, hψ⟩ i ↦ ?_⟩
  · borelize (ι → X)
    exact hΦa.inter_measurableSet
      (isOpen_set_pi finite_univ fun _ _ ↦ Metric.isOpen_ball).measurableSet
  · have h₀ := Metric.mem_ball.1 (hφ i (mem_univ i))
    have h₁ := Metric.mem_ball.1 (hψ i (mem_univ i))
    linarith [dist_triangle_right (φ i) (ψ i) (c i : X)]

end SetRel
