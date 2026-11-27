/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UnitInterval

/-!
# Lebesgue covering dimension

A topological space `X` has *covering dimension at most `d`* when every open cover of `X` has an
open refinement in which every point lies in at most `d + 1` distinct members. Covers and
refinements are sets of open sets, so a member listed twice counts once. The covering dimension
of `X` is the least such `d`, valued in `WithBot ℕ∞`: it is `⊥` (dimension `-1`) exactly for the
empty space and `⊤` when no finite bound exists.

Covers here are arbitrary families of open sets, not only finite ones. For compact spaces this
agrees with the finite-cover definition of Čech–Lebesgue dimension used by Engelking, since a
finite subcover of a refinement is again a refinement, of no larger order.

Covering dimension is the dimension theory used for function rings: the Bass stable rank of
`C(X, ℝ)` and `C(X, ℂ)` over a compact Hausdorff space `X` is computed from the covering dimension
of `X` (Vaserstein). This file sets up the predicate and the dimension value, their invariance
properties, the description by shrinkings of open covers, Hemmingsen's characterization by covers
with `d + 2` members, the sum theorem for finite closed covers, and the first computations.

## Main definitions

* `TauCeti.HasCoveringDimensionLE X d`: every open cover of `X` has an open refinement of order at
  most `d + 1`.
* `TauCeti.coveringDimension X`: the covering dimension of `X` in `WithBot ℕ∞`.

## Main results

* `TauCeti.hasCoveringDimensionLE_iff`, `TauCeti.HasCoveringDimensionLE.exists_refinement`: the
  refinement form of the predicate.
* `TauCeti.HasCoveringDimensionLE.mono`: the predicate is monotone in `d`.
* `TauCeti.coveringDimension_le_iff`, `TauCeti.coveringDimension_lt_add_one_iff`,
  `TauCeti.coveringDimension_eq_bot_iff`, `TauCeti.coveringDimension_neg_iff`,
  `TauCeti.coveringDimension_eq_top_iff`, `TauCeti.coveringDimension_lt_top_iff`,
  `TauCeti.coveringDimension_eq_zero_iff`, `TauCeti.coveringDimension_eq_add_one_iff`: the order
  characterization of the dimension value.
* `Topology.IsClosedEmbedding.hasCoveringDimensionLE`: a closed subspace has dimension at most that
  of the ambient space, with `IsHomeomorph.hasCoveringDimensionLE_iff` and
  `IsHomeomorph.coveringDimension_eq` for homeomorphism invariance.
* `TauCeti.hasCoveringDimensionLE_iff_exists_shrinking`: covering dimension at most `d` means
  that every open cover `U` has an open shrinking `V` (so `V i ⊆ U i`) of order at most `d + 1`;
  `TauCeti.HasCoveringDimensionLE.exists_shrinking` gives such shrinkings for covers indexed by an
  arbitrary type.
* `TauCeti.HasCoveringDimensionLE.exists_shrinking_iInter_eq_empty` and
  `TauCeti.hasCoveringDimensionLE_iff_forall_exists_shrinking_iInter_eq_empty`: Hemmingsen's
  characterization; a compact space has covering dimension at most `d` exactly when every open
  cover by `d + 2` sets has an open shrinking with empty intersection.
* `TauCeti.hasCoveringDimensionLE_of_iUnion_eq_univ`,
  `TauCeti.coveringDimension_eq_iSup_of_iUnion_eq_univ`: the sum theorem; a space covered by
  finitely many closed subsets of covering dimension at most `d` has covering dimension at most
  `d`, so its covering dimension is the largest of theirs.
* `TauCeti.coveringDimension_eq_zero_of_discreteTopology`: a nonempty discrete space has covering
  dimension `0`.
* `TauCeti.hasCoveringDimensionLE_zero_iff_of_connectedSpace`,
  `TauCeti.not_hasCoveringDimensionLE_zero`: a preconnected `T₁` space with two points does not have
  covering dimension `0`.
* `Real.hasCoveringDimensionLE_one_of_isCompact`: a compact subset of `ℝ` has covering dimension
  at most `1`, and `unitInterval.coveringDimension_eq_one`: the unit interval has covering
  dimension `1`.

## References

* R. Engelking, *Dimension Theory*, North-Holland, 1978, §3.1 (Definition 3.1.1 of the covering
  dimension, Theorem 3.1.4 for closed subspaces, and Theorem 3.1.8 for the sum theorem, of which
  `TauCeti.hasCoveringDimensionLE_of_iUnion_eq_univ` is the case of a finite closed cover), and
  §3.2 for Hemmingsen's characterization by covers with `n + 2` members.
* E. Hemmingsen, *Some theorems in dimension theory for normal Hausdorff spaces*, Duke Math. J.
  13 (1946), 495–504.
* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Funct. Anal.
  Appl. 5 (1971), 102–110.
* The set-of-sets encoding of covers and refinements, counting distinct members, follows the
  design of the closed Mathlib proposals
  https://github.com/leanprover-community/mathlib4/pull/43476 and
  https://github.com/leanprover-community/mathlib4/pull/43475.
-/

public section

universe u

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- Lebesgue covering dimension at most `d`: every open cover `𝒰` of `X` has an open refinement
`𝒱`, each member of which lies in a member of `𝒰`, such that every point of `X` lies in at most
`d + 1` distinct members of `𝒱`. -/
def HasCoveringDimensionLE (X : Type*) [TopologicalSpace X] (d : ℕ) : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ →
    ∃ 𝒱 : Set (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ ⋃₀ 𝒱 = univ ∧ (∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U) ∧
      ∀ x : X, {V | V ∈ 𝒱 ∧ x ∈ V}.encard ≤ ((d + 1 : ℕ) : ℕ∞)

/-- Unfolding `HasCoveringDimensionLE`: every open cover `𝒰` of `X` has an open refinement `𝒱` in
which every point lies in at most `d + 1` distinct members. -/
theorem hasCoveringDimensionLE_iff {d : ℕ} :
    HasCoveringDimensionLE X d ↔ ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ →
      ∃ 𝒱 : Set (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ ⋃₀ 𝒱 = univ ∧ (∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U) ∧
        ∀ x : X, {V | V ∈ 𝒱 ∧ x ∈ V}.encard ≤ ((d + 1 : ℕ) : ℕ∞) :=
  Iff.rfl

/-- In a space of covering dimension at most `d`, every open cover `𝒰` has an open refinement `𝒱`
in which every point lies in at most `d + 1` distinct members. -/
theorem HasCoveringDimensionLE.exists_refinement {d : ℕ} (h : HasCoveringDimensionLE X d)
    {𝒰 : Set (Set X)} (h𝒰o : ∀ U ∈ 𝒰, IsOpen U) (h𝒰c : ⋃₀ 𝒰 = univ) :
    ∃ 𝒱 : Set (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ ⋃₀ 𝒱 = univ ∧ (∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U) ∧
      ∀ x : X, {V | V ∈ 𝒱 ∧ x ∈ V}.encard ≤ ((d + 1 : ℕ) : ℕ∞) :=
  h 𝒰 h𝒰o h𝒰c

/-- Covering dimension at most `d` implies covering dimension at most `e` for `d ≤ e`. -/
theorem HasCoveringDimensionLE.mono {d e : ℕ} (h : HasCoveringDimensionLE X d) (hde : d ≤ e) :
    HasCoveringDimensionLE X e := by
  -- A refinement of order at most `d + 1` also has order at most `e + 1`.
  intro 𝒰 h𝒰o h𝒰c
  obtain ⟨𝒱, h𝒱o, h𝒱c, h𝒱r, h𝒱m⟩ := h 𝒰 h𝒰o h𝒰c
  exact ⟨𝒱, h𝒱o, h𝒱c, h𝒱r, fun x ↦ (h𝒱m x).trans (by exact_mod_cast Nat.succ_le_succ hde)⟩

/-- The empty space has covering dimension at most `d` for every `d`. -/
theorem hasCoveringDimensionLE_of_isEmpty [IsEmpty X] (d : ℕ) : HasCoveringDimensionLE X d :=
  -- The empty family refines every cover.
  fun _ _ _ ↦ ⟨∅, by simp, Subsingleton.elim _ _, by simp, fun x ↦ isEmptyElim x⟩

/-- A discrete space has covering dimension at most `0`. -/
theorem hasCoveringDimensionLE_zero_of_discreteTopology [DiscreteTopology X] :
    HasCoveringDimensionLE X 0 := by
  -- The singletons refine every open cover, and each point lies in only one of them.
  intro 𝒰 _ h𝒰c
  refine ⟨range fun x : X ↦ ({x} : Set X), ?_, ?_, ?_, fun x ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact isOpen_discrete _
  · exact eq_univ_of_forall fun x ↦ mem_sUnion.2 ⟨{x}, mem_range_self x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 (h𝒰c ▸ mem_univ x)
    exact ⟨U, hU, singleton_subset_iff.2 hxU⟩
  · refine (encard_le_encard (t := {{x}}) ?_).trans (by simp)
    rintro _ ⟨⟨y, rfl⟩, hxy⟩
    rw [mem_singleton_iff.1 hxy]
    exact mem_singleton _

/-- In a connected space, covering dimension at most `0` means that every open cover contains the
whole space. -/
theorem hasCoveringDimensionLE_zero_iff_of_connectedSpace [ConnectedSpace X] :
    HasCoveringDimensionLE X 0 ↔
      ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ → univ ∈ 𝒰 := by
  constructor
  · intro h 𝒰 h𝒰o h𝒰c
    obtain ⟨𝒱, h𝒱o, h𝒱c, h𝒱r, h𝒱m⟩ := h 𝒰 h𝒰o h𝒰c
    obtain ⟨x⟩ := ‹ConnectedSpace X›.toNonempty
    obtain ⟨V, hV, hxV⟩ := mem_sUnion.1 (h𝒱c ▸ mem_univ x)
    -- A point lies in at most one member of `𝒱`, so distinct members are disjoint.
    have hdisj : ∀ W ∈ 𝒱, ∀ y ∈ V, y ∈ W → W = V := fun W hW y hyV hyW ↦ by
      have hle := h𝒱m y
      rw [Nat.cast_one, encard_le_one_iff] at hle
      exact hle W V ⟨hW, hyW⟩ ⟨hV, hyV⟩
    -- Hence `V` is clopen: its complement is the union of the other members.
    have hcompl : Vᶜ = ⋃₀ (𝒱 \ {V}) := by
      ext y
      simp only [mem_compl_iff, mem_sUnion, mem_sdiff, mem_singleton_iff]
      constructor
      · intro hyV
        obtain ⟨W, hW, hyW⟩ := mem_sUnion.1 (h𝒱c ▸ mem_univ y)
        exact ⟨W, ⟨hW, fun hWV ↦ hyV (hWV ▸ hyW)⟩, hyW⟩
      · rintro ⟨W, ⟨hW, hWV⟩, hyW⟩ hyV
        exact hWV (hdisj W hW y hyV hyW)
    have hclopen : IsClopen V :=
      ⟨isOpen_compl_iff.1 (hcompl ▸ isOpen_sUnion fun W hW ↦ h𝒱o W hW.1), h𝒱o V hV⟩
    have hVuniv : V = univ := (isClopen_iff.1 hclopen).resolve_left (nonempty_of_mem hxV).ne_empty
    obtain ⟨U, hU, hVU⟩ := h𝒱r V hV
    rwa [← univ_subset_iff.1 (hVuniv ▸ hVU)]
  · intro h 𝒰 h𝒰o h𝒰c
    exact ⟨{univ}, by simp, by simp, fun V hV ↦ ⟨univ, h 𝒰 h𝒰o h𝒰c, (mem_singleton_iff.1 hV).le⟩,
      fun x ↦ (encard_le_encard (sep_subset _ _)).trans (by simp)⟩

/-- A preconnected `T₁` space with two distinct points does not have covering dimension `0`. The
`T₁` hypothesis is needed: the Sierpiński space is connected, and has covering dimension `0` since
every open cover of it contains the whole space. -/
theorem not_hasCoveringDimensionLE_zero [PreconnectedSpace X] [T1Space X] [Nontrivial X] :
    ¬ HasCoveringDimensionLE X 0 := by
  -- The complements of two distinct points form an open cover without the whole space.
  have : ConnectedSpace X := { toNonempty := inferInstance }
  rw [hasCoveringDimensionLE_zero_iff_of_connectedSpace]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  intro h
  have hmem := h {{x}ᶜ, {y}ᶜ} (by simp) (by
    refine eq_univ_of_forall fun z ↦ ?_
    by_cases hzx : z = x
    · exact mem_sUnion.2 ⟨{y}ᶜ, by simp, by simpa [hzx] using hxy⟩
    · exact mem_sUnion.2 ⟨{x}ᶜ, by simp, hzx⟩)
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact mem_compl_singleton_iff.1 (eq_univ_iff_forall.1 hmem.symm x) rfl
  · exact mem_compl_singleton_iff.1 (eq_univ_iff_forall.1 hmem.symm y) rfl

open Classical in
/-- The Lebesgue covering dimension of `X`: `⊥` for the empty space, and otherwise the least `d`
with `HasCoveringDimensionLE X d`, or `⊤` if there is none. -/
noncomputable def coveringDimension (X : Type*) [TopologicalSpace X] : WithBot ℕ∞ :=
  if IsEmpty X then ⊥ else ⨅ (d : ℕ) (_ : HasCoveringDimensionLE X d), (d : WithBot ℕ∞)

/-- The covering dimension is at most `d` exactly when `X` has covering dimension at most `d`. -/
theorem coveringDimension_le_iff {d : ℕ} :
    coveringDimension X ≤ d ↔ HasCoveringDimensionLE X d := by
  rw [coveringDimension]
  split_ifs with hX
  · exact iff_of_true bot_le (hasCoveringDimensionLE_of_isEmpty d)
  · refine ⟨fun hle ↦ ?_, fun h ↦ iInf₂_le d h⟩
    by_contra hd
    -- Every admissible bound exceeds `d`, so the infimum is at least `d + 1`.
    have hge : ((d + 1 : ℕ) : WithBot ℕ∞) ≤
        ⨅ (e : ℕ) (_ : HasCoveringDimensionLE X e), (e : WithBot ℕ∞) := by
      refine le_iInf₂ fun e he ↦ ?_
      have hde : d + 1 ≤ e := by
        by_contra hlt
        exact hd (he.mono (by omega))
      exact_mod_cast hde
    have := hge.trans hle
    norm_cast at this
    omega

/-- The covering dimension is less than `d + 1` exactly when `X` has covering dimension at most
`d`. -/
theorem coveringDimension_lt_add_one_iff {d : ℕ} :
    coveringDimension X < (d + 1 : ℕ) ↔ HasCoveringDimensionLE X d := by
  rw [← coveringDimension_le_iff]
  generalize coveringDimension X = n
  induction n using WithBot.recBotCoe with
  | bot => simp
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => simpa using (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top d)).ne
    | coe n => norm_cast; omega

/-- The covering dimension is `⊥` exactly for the empty space. -/
@[simp]
theorem coveringDimension_eq_bot_iff : coveringDimension X = ⊥ ↔ IsEmpty X := by
  rw [coveringDimension]
  split_ifs with hX
  · exact iff_of_true rfl hX
  · refine iff_of_false (ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe 0) ?_)) hX
    exact le_iInf₂ fun e _ ↦ by exact_mod_cast Nat.zero_le e

/-- The covering dimension is negative exactly for the empty space. -/
theorem coveringDimension_neg_iff : coveringDimension X < 0 ↔ IsEmpty X := by
  rw [← coveringDimension_eq_bot_iff]
  generalize coveringDimension X = n
  induction n using WithBot.recBotCoe with
  | bot => simp
  | coe n => simp

/-- The covering dimension is `⊤` exactly when no finite bound holds. -/
theorem coveringDimension_eq_top_iff :
    coveringDimension X = ⊤ ↔ ∀ d : ℕ, ¬ HasCoveringDimensionLE X d := by
  simp_rw [← coveringDimension_le_iff, not_le, ENat.WithBot.eq_top_iff_forall_ge]
  refine ⟨fun h d ↦ ?_, fun h d ↦ (h d).le⟩
  exact lt_of_lt_of_le (by exact_mod_cast d.lt_succ_self) (h (d + 1))

/-- The covering dimension is finite exactly when some finite bound holds. -/
theorem coveringDimension_lt_top_iff :
    coveringDimension X < ⊤ ↔ ∃ d : ℕ, HasCoveringDimensionLE X d := by
  rw [lt_top_iff_ne_top, Ne, coveringDimension_eq_top_iff, not_forall_not]

/-- The covering dimension is `0` exactly for a nonempty space of covering dimension at most `0`. -/
theorem coveringDimension_eq_zero_iff :
    coveringDimension X = 0 ↔ Nonempty X ∧ HasCoveringDimensionLE X 0 := by
  rw [← coveringDimension_le_iff, Nat.cast_zero, ← not_isEmpty_iff,
    ← coveringDimension_neg_iff, not_lt, and_comm, le_antisymm_iff]

/-- The covering dimension is `d + 1` exactly when `X` has covering dimension at most `d + 1` but
not at most `d`. -/
theorem coveringDimension_eq_add_one_iff {d : ℕ} :
    coveringDimension X = (d + 1 : ℕ) ↔
      HasCoveringDimensionLE X (d + 1) ∧ ¬ HasCoveringDimensionLE X d := by
  rw [← coveringDimension_le_iff, ← coveringDimension_lt_add_one_iff, not_lt, le_antisymm_iff]

/-- A nonempty discrete space has covering dimension `0`. -/
theorem coveringDimension_eq_zero_of_discreteTopology [DiscreteTopology X] [Nonempty X] :
    coveringDimension X = 0 :=
  coveringDimension_eq_zero_iff.2 ⟨‹_›, hasCoveringDimensionLE_zero_of_discreteTopology⟩

end TauCeti

namespace Topology.IsClosedEmbedding

open TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed subspace of a space of covering dimension at most `d` has covering dimension at most
`d` (Engelking, Theorem 3.1.4). -/
theorem hasCoveringDimensionLE {f : X → Y} (hf : IsClosedEmbedding f) {d : ℕ}
    (h : HasCoveringDimensionLE Y d) : HasCoveringDimensionLE X d := by
  -- An open cover of `X` extends to an open cover of `Y` by adding the complement of the image;
  -- a refinement of the latter pulls back to a refinement of the former.
  intro 𝒰 h𝒰o h𝒰c
  have hext : ∀ U ∈ 𝒰, ∃ U' : Set Y, IsOpen U' ∧ f ⁻¹' U' = U :=
    fun U hU ↦ hf.isInducing.isOpen_iff.1 (h𝒰o U hU)
  choose! g hgo hgU using hext
  obtain ⟨𝒱, h𝒱o, h𝒱c, h𝒱r, h𝒱m⟩ := h (insert (range f)ᶜ (g '' 𝒰))
    (by
      rintro _ (rfl | ⟨U, hU, rfl⟩)
      · exact hf.isClosed_range.isOpen_compl
      · exact hgo U hU)
    (by
      refine eq_univ_of_forall fun y ↦ ?_
      by_cases hy : y ∈ range f
      · obtain ⟨x, rfl⟩ := hy
        obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 (h𝒰c ▸ mem_univ x)
        exact mem_sUnion.2 ⟨g U, mem_insert_of_mem _ (mem_image_of_mem g hU),
          by rw [← mem_preimage, hgU U hU]; exact hxU⟩
      · exact mem_sUnion.2 ⟨(range f)ᶜ, mem_insert _ _, hy⟩)
  refine ⟨{W | ∃ V ∈ 𝒱, f ⁻¹' V = W ∧ W.Nonempty}, ?_, ?_, ?_, fun x ↦ ?_⟩
  · rintro _ ⟨V, hV, rfl, -⟩
    exact (h𝒱o V hV).preimage hf.continuous
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨V, hV, hxV⟩ := mem_sUnion.1 (h𝒱c ▸ mem_univ (f x))
    exact mem_sUnion.2 ⟨f ⁻¹' V, ⟨V, hV, rfl, x, hxV⟩, hxV⟩
  · rintro _ ⟨V, hV, rfl, z, hz⟩
    obtain ⟨U', hU', hVU'⟩ := h𝒱r V hV
    rcases hU' with rfl | ⟨U, hU, rfl⟩
    · exact absurd (mem_range_self z) (hVU' hz)
    · exact ⟨U, hU, hgU U hU ▸ preimage_mono hVU'⟩
  · refine le_trans (encard_le_encard ?_) ((encard_image_le (preimage f) _).trans (h𝒱m (f x)))
    rintro _ ⟨⟨V, hV, rfl, -⟩, hxV⟩
    exact ⟨V, ⟨hV, hxV⟩, rfl⟩

/-- A closed subspace has covering dimension at most that of the ambient space. -/
theorem coveringDimension_le {f : X → Y} (hf : IsClosedEmbedding f) :
    coveringDimension X ≤ coveringDimension Y := by
  by_cases hX : IsEmpty X
  · rw [coveringDimension_eq_bot_iff.2 hX]
    exact bot_le
  have hY : ¬ IsEmpty Y := fun hY ↦ hX ⟨fun x ↦ hY.elim (f x)⟩
  simp only [coveringDimension, hX, hY, ↓reduceIte]
  exact le_iInf₂ fun d hd ↦ iInf₂_le d (hf.hasCoveringDimensionLE hd)

end Topology.IsClosedEmbedding

namespace IsHomeomorph

open TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Covering dimension at most `d` is invariant under homeomorphisms. -/
theorem hasCoveringDimensionLE_iff {f : X → Y} (hf : IsHomeomorph f) {d : ℕ} :
    HasCoveringDimensionLE X d ↔ HasCoveringDimensionLE Y d :=
  ⟨(hf.homeomorph f).symm.isClosedEmbedding.hasCoveringDimensionLE,
    hf.isClosedEmbedding.hasCoveringDimensionLE⟩

/-- Covering dimension is invariant under homeomorphisms. -/
theorem coveringDimension_eq {f : X → Y} (hf : IsHomeomorph f) :
    coveringDimension X = coveringDimension Y :=
  le_antisymm hf.isClosedEmbedding.coveringDimension_le
    (hf.homeomorph f).symm.isClosedEmbedding.coveringDimension_le

end IsHomeomorph

namespace TauCeti

/-! ### Shrinkings and the finite sum theorem -/

variable {X : Type*} [TopologicalSpace X]

/-- In a space of covering dimension at most `d`, every open cover `U`, indexed by any type, has an
open shrinking: an open cover `V` with `V i ⊆ U i` for every `i`, in which every point lies in at
most `d + 1` of the sets `V i`. -/
theorem HasCoveringDimensionLE.exists_shrinking {d : ℕ} (h : HasCoveringDimensionLE X d)
    {ι : Type*} {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ∀ x, {i | x ∈ V i}.encard ≤ ((d + 1 : ℕ) : ℕ∞) := by
  obtain ⟨𝒱, h𝒱o, h𝒱c, h𝒱r, h𝒱m⟩ :=
    h (range U) (forall_mem_range.2 hUo) (by rwa [sUnion_range])
  -- Choose for every member `W` of the refinement an index `p W` with `W ⊆ U (p W)`, and let
  -- `V i` be the union of the members with index `i`.
  choose p hp using fun W : 𝒱 ↦ exists_range_iff.1 (h𝒱r W.val W.property)
  refine ⟨fun i ↦ ⋃ (W : 𝒱) (_ : p W = i), W.val,
    fun i ↦ isOpen_iUnion fun W ↦ isOpen_iUnion fun _ ↦ h𝒱o W.val W.property,
    fun i ↦ iUnion₂_subset fun W hW ↦ hW ▸ hp W, ?_, fun x ↦ ?_⟩
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.1 (h𝒱c ▸ mem_univ x)
    exact mem_iUnion.2 ⟨p ⟨W, hW⟩, mem_iUnion₂.2 ⟨⟨W, hW⟩, rfl, hxW⟩⟩
  · -- An index `i` with `x ∈ V i` is the index of a member containing `x`.
    have hsub : {i | x ∈ ⋃ (W : 𝒱) (_ : p W = i), W.val} ⊆ p '' {W : 𝒱 | x ∈ W.val} := by
      intro i hi
      obtain ⟨W, hWi, hxW⟩ := mem_iUnion₂.1 hi
      exact ⟨W, hxW, hWi⟩
    refine (encard_le_encard hsub).trans ((encard_image_le _ _).trans ?_)
    rw [← Subtype.val_injective.encard_image]
    refine (encard_le_encard ?_).trans (h𝒱m x)
    rintro _ ⟨W, hxW, rfl⟩
    exact ⟨W.property, hxW⟩

/-- Covering dimension at most `d` means that every open cover has an open shrinking in which
every point lies in at most `d + 1` members. -/
theorem hasCoveringDimensionLE_iff_exists_shrinking {X : Type u} [TopologicalSpace X] {d : ℕ} :
    HasCoveringDimensionLE X d ↔ ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) →
      ⋃ i, U i = univ → ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧
        ⋃ i, V i = univ ∧ ∀ x, {i | x ∈ V i}.encard ≤ ((d + 1 : ℕ) : ℕ∞) := by
  refine ⟨fun h ι U hUo hU ↦ h.exists_shrinking hUo hU, fun h 𝒰 h𝒰o h𝒰c ↦ ?_⟩
  -- A shrinking of the cover indexed by its own members is a refinement of the same order.
  obtain ⟨V, hVo, hVU, hVc, hVm⟩ :=
    h 𝒰 Subtype.val (fun U ↦ h𝒰o U.val U.property) (by rwa [← sUnion_eq_iUnion])
  refine ⟨range V, forall_mem_range.2 hVo, by rwa [sUnion_range],
    forall_mem_range.2 fun U ↦ ⟨U.val, U.property, hVU U⟩, fun x ↦ ?_⟩
  refine le_trans (encard_le_encard ?_) ((encard_image_le V _).trans (hVm x))
  rintro _ ⟨⟨U, rfl⟩, hxU⟩
  exact ⟨U, hxU, rfl⟩

/-- If a closed subset `s` of `X` has covering dimension at most `d`, then every open cover `U` of
`X` has an open shrinking in which every point of `s` lies in at most `d + 1` members. -/
theorem HasCoveringDimensionLE.exists_shrinking_of_isClosed {s : Set X} (hs : IsClosed s)
    {d : ℕ} (h : HasCoveringDimensionLE s d) {ι : Type*} {U : ι → Set X}
    (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ∀ x ∈ s, {i | x ∈ V i}.encard ≤ ((d + 1 : ℕ) : ℕ∞) := by
  -- Shrink the trace of `U` on `s`, extend the pieces to open sets `O i` of `X`, and keep `U i`
  -- unchanged off `s`.
  obtain ⟨G, hGo, hGU, hGc, hGm⟩ := h.exists_shrinking (U := fun i ↦ (↑) ⁻¹' U i)
    (fun i ↦ (hUo i).preimage continuous_subtypeVal) (by rw [← preimage_iUnion, hU, preimage_univ])
  choose O hOo hOG using fun i ↦ isOpen_induced_iff.1 (hGo i)
  refine ⟨fun i ↦ O i ∩ U i ∪ U i \ s, fun i ↦ ((hOo i).inter (hUo i)).union ((hUo i).sdiff hs),
    fun i ↦ union_subset inter_subset_right sdiff_subset, ?_, fun x hx ↦ ?_⟩
  · refine eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ s
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hGc ▸ mem_univ (⟨x, hx⟩ : s))
      exact mem_iUnion.2 ⟨i, Or.inl
        ⟨mem_preimage.1 ((Set.ext_iff.1 (hOG i) _).2 hi), mem_preimage.1 (hGU i hi)⟩⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hU ▸ mem_univ x)
      exact mem_iUnion.2 ⟨i, Or.inr ⟨hi, hx⟩⟩
  · refine (encard_le_encard fun i hi ↦ ?_).trans (hGm ⟨x, hx⟩)
    obtain ⟨hxO, -⟩ := hi.resolve_right fun hi ↦ hi.2 hx
    exact (Set.ext_iff.1 (hOG i) _).1 (mem_preimage.2 hxO)

/-- The finite sum theorem: a space covered by finitely many closed subsets of covering dimension
at most `d` has covering dimension at most `d` (Engelking, Theorem 3.1.8 for finite covers). -/
theorem hasCoveringDimensionLE_of_iUnion_eq_univ {ι : Type*} [Finite ι] {F : ι → Set X}
    (hF : ∀ i, IsClosed (F i)) (hFX : ⋃ i, F i = univ) {d : ℕ}
    (h : ∀ i, HasCoveringDimensionLE (F i) d) : HasCoveringDimensionLE X d := by
  classical
  have := Fintype.ofFinite ι
  rw [hasCoveringDimensionLE_iff_exists_shrinking]
  intro κ U hUo hU
  -- Shrink `U` successively along the closed sets `F i`, `i ∈ S`; shrinking further does not
  -- increase the order at points of the sets already treated.
  suffices ∀ S : Finset ι, ∃ V : κ → Set X, (∀ k, IsOpen (V k)) ∧ (∀ k, V k ⊆ U k) ∧
      ⋃ k, V k = univ ∧ ∀ i ∈ S, ∀ x ∈ F i, {k | x ∈ V k}.encard ≤ ((d + 1 : ℕ) : ℕ∞) by
    obtain ⟨V, hVo, hVU, hVc, hVm⟩ := this Finset.univ
    refine ⟨V, hVo, hVU, hVc, fun x ↦ ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hFX ▸ mem_univ x)
    exact hVm i (Finset.mem_univ i) x hi
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨U, hUo, fun _ ↦ subset_rfl, hU, by simp⟩
  | insert i S _ ih =>
    obtain ⟨V, hVo, hVU, hVc, hVm⟩ := ih
    obtain ⟨W, hWo, hWV, hWc, hWm⟩ := (h i).exists_shrinking_of_isClosed (hF i) hVo hVc
    refine ⟨W, hWo, fun k ↦ (hWV k).trans (hVU k), hWc, fun j hj x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hWm x hx
    · exact (encard_le_encard fun k hk ↦ hWV k hk).trans (hVm j hj x hx)

/-- The covering dimension of a space covered by finitely many closed subsets is the largest
covering dimension of these subsets. -/
theorem coveringDimension_eq_iSup_of_iUnion_eq_univ {ι : Type*} [Finite ι] {F : ι → Set X}
    (hF : ∀ i, IsClosed (F i)) (hFX : ⋃ i, F i = univ) :
    coveringDimension X = ⨆ i, coveringDimension (F i) := by
  refine le_antisymm ?_
    (iSup_le fun i ↦ (hF i).isClosedEmbedding_subtypeVal.coveringDimension_le)
  generalize hb : ⨆ i, coveringDimension (F i) = b
  induction b using WithBot.recBotCoe with
  | bot =>
    -- Every `F i` is empty, hence so is `X`.
    have : IsEmpty X := ⟨fun x ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hFX ▸ mem_univ x)
      exact (coveringDimension_eq_bot_iff.1 (iSup_eq_bot.1 hb i)).elim ⟨x, hi⟩⟩
    exact (coveringDimension_eq_bot_iff.2 this).le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe d =>
      rw [WithBot.coe_natCast] at hb ⊢
      exact coveringDimension_le_iff.2 (hasCoveringDimensionLE_of_iUnion_eq_univ hF hFX
        fun i ↦ coveringDimension_le_iff.1 (hb ▸ le_iSup (fun j ↦ coveringDimension (F j)) i))

/-! ### Hemmingsen's characterization -/

/-- In a space of covering dimension at most `d`, every open cover by `d + 2` sets has an open
shrinking with empty intersection. -/
theorem HasCoveringDimensionLE.exists_shrinking_iInter_eq_empty {d : ℕ}
    (h : HasCoveringDimensionLE X d) {U : Fin (d + 2) → Set X} (hUo : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) :
    ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i, V i = ∅ := by
  -- A shrinking of order at most `d + 1` has no point in all `d + 2` of its members.
  obtain ⟨V, hVo, hVU, hVc, hVm⟩ := h.exists_shrinking hUo hU
  refine ⟨V, hVo, hVU, hVc, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  have hall : {i | x ∈ V i} = univ := eq_univ_of_forall (mem_iInter.1 hx)
  have := hVm x
  simp [hall] at this

/-- The hypothesis of Hemmingsen's characterization: every open cover of `X` by `d + 2` sets has
an open shrinking with empty intersection. -/
private abbrev ShrinkingCondition (X : Type*) [TopologicalSpace X] (d : ℕ) : Prop :=
  ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
    ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i, V i = ∅

/-- One shrinking step: under Hemmingsen's condition, an open cover indexed by any type has an
open shrinking whose members indexed by a given set `S` of `d + 2` indices have empty
intersection. -/
private theorem exists_shrinking_biInter_eq_empty {d : ℕ} (h : ShrinkingCondition X d)
    {ι : Type*} {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ)
    {S : Finset ι} (hS : S.card = d + 2) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i ∈ S, V i = ∅ := by
  classical
  -- Enlarge each `U i`, `i ∈ S`, by the union `W` of the members outside `S`, shrink the
  -- resulting cover by `d + 2` sets, and intersect back with `U i`.
  let e : Fin (d + 2) ≃ S := (S.equivFin.trans (finCongr hS)).symm
  let W := ⋃ (j) (_ : j ∉ S), U j
  have hWo : IsOpen W := isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hUo j
  obtain ⟨V', hV'o, hV'O, hV'c, hV'e⟩ := h (fun k ↦ U (e k) ∪ W)
    (fun k ↦ (hUo _).union hWo) (eq_univ_of_forall fun x ↦ by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hU ▸ mem_univ x)
      by_cases hjS : j ∈ S
      · exact mem_iUnion.2 ⟨e.symm ⟨j, hjS⟩, Or.inl (by simpa using hj)⟩
      · exact mem_iUnion.2 ⟨0, Or.inr (mem_iUnion₂.2 ⟨j, hjS, hj⟩)⟩)
  refine ⟨fun j ↦ if hj : j ∈ S then U j ∩ V' (e.symm ⟨j, hj⟩) else U j, fun j ↦ ?_,
    fun j ↦ ?_, eq_univ_of_forall fun x ↦ ?_, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  · dsimp only
    split_ifs
    exacts [(hUo j).inter (hV'o _), hUo j]
  · dsimp only
    split_ifs
    exacts [inter_subset_left, subset_rfl]
  · by_cases hxW : x ∈ W
    · obtain ⟨j, hjS, hxj⟩ := mem_iUnion₂.1 hxW
      exact mem_iUnion.2 ⟨j, by simpa [hjS] using hxj⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hV'c ▸ mem_univ x)
      have hxU : x ∈ U (e k) := ((hV'O k hk).resolve_right hxW)
      exact mem_iUnion.2 ⟨e k, by simpa [(e k).property] using ⟨hxU, hk⟩⟩
  · refine (eq_empty_iff_forall_notMem.1 hV'e) x (mem_iInter.2 fun k ↦ ?_)
    have := mem_iInter₂.1 hx (e k) (e k).property
    simp only [(e k).property, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply] at this
    exact this.2

/-- Under Hemmingsen's condition, a finite open cover has an open shrinking in which every
`d + 2` members have empty intersection. -/
private theorem exists_shrinking_forall_biInter_eq_empty {d : ℕ} (h : ShrinkingCondition X d)
    {ι : Type*} [Finite ι] {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ∀ S : Finset ι, S.card = d + 2 → ⋂ i ∈ S, V i = ∅ := by
  classical
  have := Fintype.ofFinite ι
  -- Treat the finitely many sets of `d + 2` indices one at a time; shrinking further keeps the
  -- intersections already made empty.
  suffices ∀ 𝒮 : Finset (Finset ι), ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧
      ⋃ i, V i = univ ∧ ∀ S ∈ 𝒮, S.card = d + 2 → ⋂ i ∈ S, V i = ∅ by
    obtain ⟨V, hVo, hVU, hVc, hVe⟩ := this Finset.univ
    exact ⟨V, hVo, hVU, hVc, fun S hS ↦ hVe S (Finset.mem_univ S) hS⟩
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty => exact ⟨U, hUo, fun _ ↦ subset_rfl, hU, by simp⟩
  | insert S 𝒮 _ ih =>
    obtain ⟨V, hVo, hVU, hVc, hVe⟩ := ih
    by_cases hS : S.card = d + 2
    · obtain ⟨V', hV'o, hV'V, hV'c, hV'e⟩ := exists_shrinking_biInter_eq_empty h hVo hVc hS
      refine ⟨V', hV'o, fun i ↦ (hV'V i).trans (hVU i), hV'c, fun T hT hTc ↦ ?_⟩
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact hV'e
      · exact eq_empty_of_subset (biInter_mono subset_rfl fun i _ ↦ hV'V i) (hVe T hT hTc)
    · refine ⟨V, hVo, hVU, hVc, fun T hT hTc ↦ ?_⟩
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact absurd hTc hS
      · exact hVe T hT hTc

/-- **Hemmingsen's characterization**, the converse direction: a compact space in which every open
cover by `d + 2` sets has an open shrinking with empty intersection has covering dimension at most
`d`. -/
theorem hasCoveringDimensionLE_of_forall_exists_shrinking_iInter_eq_empty [CompactSpace X]
    {d : ℕ} (h : ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
      ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
        ⋂ i, V i = ∅) :
    HasCoveringDimensionLE X d := by
  classical
  rw [hasCoveringDimensionLE_iff]
  intro 𝒰 h𝒰o h𝒰c
  -- Pass to a finite subcover and shrink it so that no point lies in `d + 2` of its members.
  obtain ⟨t, ht𝒰, htf, htc⟩ := isCompact_univ.elim_finite_subcover_image (c := id) h𝒰o
    (by simpa [← sUnion_eq_biUnion] using h𝒰c.ge)
  have := htf.to_subtype
  have := Fintype.ofFinite t
  obtain ⟨V, hVo, hVU, hVc, hVe⟩ := exists_shrinking_forall_biInter_eq_empty (U := Subtype.val)
    h (fun i : t ↦ h𝒰o _ (ht𝒰 i.property))
    (eq_univ_of_forall fun x ↦ by simpa using htc (mem_univ x))
  refine ⟨range V, forall_mem_range.2 hVo, by rwa [sUnion_range],
    forall_mem_range.2 fun i ↦ ⟨i, ht𝒰 i.property, hVU i⟩, fun x ↦ ?_⟩
  -- The members containing `x` are the images of the indices `i` with `x ∈ V i`.
  have hsub : {W | W ∈ range V ∧ x ∈ W} ⊆ V '' (Finset.univ.filter (x ∈ V ·) : Finset t) := by
    rintro _ ⟨⟨i, rfl⟩, hx⟩
    exact ⟨i, by simpa using hx, rfl⟩
  refine (encard_le_encard hsub).trans ((encard_image_le _ _).trans ?_)
  rw [encard_coe_eq_coe_finsetCard, Nat.cast_le]
  by_contra! hlt
  obtain ⟨S, hSs, hSc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hlt)
  refine (eq_empty_iff_forall_notMem.1 (hVe S hSc)) x (mem_iInter₂.2 fun i hi ↦ ?_)
  simpa using hSs hi

/-- **Hemmingsen's characterization**: a compact space has covering dimension at most `d` exactly
when every open cover by `d + 2` sets has an open shrinking with empty intersection. -/
theorem hasCoveringDimensionLE_iff_forall_exists_shrinking_iInter_eq_empty [CompactSpace X]
    {d : ℕ} :
    HasCoveringDimensionLE X d ↔ ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) →
      ⋃ i, U i = univ → ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧
        ⋃ i, V i = univ ∧ ⋂ i, V i = ∅ :=
  ⟨fun h _ hUo hU ↦ h.exists_shrinking_iInter_eq_empty hUo hU,
    hasCoveringDimensionLE_of_forall_exists_shrinking_iInter_eq_empty⟩

end TauCeti

namespace Real

open TauCeti

/-- A compact subset of `ℝ` has covering dimension at most `1`. -/
theorem hasCoveringDimensionLE_one_of_isCompact {s : Set ℝ} (hs : IsCompact s) :
    HasCoveringDimensionLE s 1 := by
  -- For a Lebesgue number `3 h` of the cover, the traces of the open intervals of radius `h`
  -- around the points `k h`, `k ∈ ℤ`, refine it, and every point lies in at most two of them.
  have : CompactSpace s := isCompact_iff_compactSpace.1 hs
  intro 𝒰 h𝒰o h𝒰c
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric_sUnion isCompact_univ h𝒰o
    (h𝒰c ▸ subset_rfl)
  set h : ℝ := δ / 3 with hh
  have hh0 : 0 < h := by positivity
  -- The trace on `s` of the open interval of radius `h` around `k h`.
  let V : ℤ → Set s := fun k ↦ {x | |(x : ℝ) - k * h| < h}
  -- Every point lies in `[⌊x / h⌋ h, ⌊x / h⌋ h + h)`.
  have hfloor (x : s) : ⌊(x : ℝ) / h⌋ * h ≤ x ∧ (x : ℝ) < ⌊(x : ℝ) / h⌋ * h + h :=
    ⟨by linarith [Int.sub_floor_div_mul_nonneg (x : ℝ) hh0],
      by linarith [Int.sub_floor_div_mul_lt (x : ℝ) hh0]⟩
  refine ⟨{W | ∃ k : ℤ, V k = W ∧ W.Nonempty}, ?_, ?_, ?_, fun x ↦ ?_⟩
  · rintro _ ⟨k, rfl, -⟩
    exact isOpen_lt (continuous_abs.comp (continuous_subtypeVal.sub continuous_const))
      continuous_const
  · -- The point `x` lies in the interval around `⌊x / h⌋ h`.
    have hmem (x : s) : x ∈ V ⌊(x : ℝ) / h⌋ := by
      simp only [V, mem_ofPred_eq, abs_lt]
      constructor <;> linarith [hfloor x]
    exact eq_univ_of_forall fun x ↦ mem_sUnion.2 ⟨_, ⟨_, rfl, x, hmem x⟩, hmem x⟩
  · rintro _ ⟨k, rfl, y, hy⟩
    obtain ⟨U, hU, hyU⟩ := hball y (mem_univ y)
    refine ⟨U, hU, fun z hz ↦ hyU ?_⟩
    simp only [V, mem_ofPred_eq] at hy hz
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    calc |(z : ℝ) - y| ≤ |(z : ℝ) - k * h| + |k * h - (y : ℝ)| := abs_sub_le _ _ _
      _ < h + h := add_lt_add hz (abs_sub_comm (y : ℝ) (k * h) ▸ hy)
      _ < δ := by rw [hh]; linarith
  · -- The point `x` can only lie in the intervals around `m h` and `(m + 1) h`, `m = ⌊x / h⌋`.
    set m := ⌊(x : ℝ) / h⌋
    have hsub : {W | W ∈ {W | ∃ k : ℤ, V k = W ∧ W.Nonempty} ∧ x ∈ W} ⊆ V '' {m, m + 1} := by
      rintro _ ⟨⟨k, rfl, -⟩, hx⟩
      refine ⟨k, ?_, rfl⟩
      simp only [V, mem_ofPred_eq, abs_lt] at hx
      obtain ⟨h1, h2⟩ := hfloor x
      have hk1 : m - 1 < k := by
        have : ((m : ℝ) - 1) * h < k * h := by linarith
        exact_mod_cast lt_of_mul_lt_mul_right this hh0.le
      have hk2 : k < m + 2 := by
        have : (k : ℝ) * h < (m + 2) * h := by linarith
        exact_mod_cast lt_of_mul_lt_mul_right this hh0.le
      simp only [mem_insert_iff, mem_singleton_iff]
      omega
    refine (encard_le_encard hsub).trans ((encard_image_le _ _).trans ?_)
    exact (encard_insert_le _ _).trans (by simp; norm_num)

end Real

namespace unitInterval

open TauCeti

/-- The unit interval has covering dimension `1`. -/
theorem coveringDimension_eq_one : coveringDimension I = 1 :=
  coveringDimension_eq_add_one_iff (d := 0).2
    ⟨Real.hasCoveringDimensionLE_one_of_isCompact isCompact_Icc, not_hasCoveringDimensionLE_zero⟩

end unitInterval
