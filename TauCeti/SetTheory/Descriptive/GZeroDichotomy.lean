/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.GSGraph
public import TauCeti.SetTheory.Descriptive.SmallFamily.WitnessExtension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import TauCeti.Data.Vector.Basic
import TauCeti.MeasureTheory.Constructions.Polish.Analytic

/-!
# The Kechris–Solecki–Todorcevic G₀ dichotomy

Let `X` be a Polish space with its Borel σ-algebra and `G : SetRel X X` an analytic relation,
read as a directed graph in which loops are allowed. The **G₀ dichotomy** says that exactly one
of the following holds:

* `G` has a countable Borel coloring (`SetRel.HasCountableBorelColoring`);
* there is a continuous map `φ` of Cantor space into `X` sending every oriented edge of
  `orientedGS canonicalWords` to a pair of `G`.

The homomorphism half, `exists_continuous_orientedGS_hom`, says that the second alternative
holds when the first fails, and it does so for every sparse word set `S` (at most one word
of each length) in place of `canonicalWords`; neither symmetry nor irreflexivity of `G` is
assumed. The two alternatives exclude each other
whenever `S` is dense (`not_hasCountableBorelColoring_of_orientedGS_hom`, in
`TauCeti.SetTheory.Descriptive.GSGraph`): a coloring of `G`
would pull back to a countable Borel coloring of `orientedGS S`, which Miller's independence
lemma forbids. For a simple graph `G` on `X` with analytic edge relation, the dichotomy reads:
either `G` has a measurable coloring by `ℕ`, or there is a continuous homomorphism
`gZero →g G` (`SimpleGraph.g0_dichotomy`).

Applied to the inequivalence relation of a Borel equivalence relation `E` with uncountably many
classes, the homomorphism half gives a continuous map sending `gZero`-adjacent points to
`E`-inequivalent points, and more generally adjacent points of `gSGraph S` for every sparse `S`
(`Setoid.exists_continuous_forall_gSGraph_adj_not`). This is the input to the category proof of
Silver's theorem.

## The fusion construction

The homomorphism half is proved by B. D. Miller's fusion argument through the σ-ideal of small
families of assignments (`SetRel.IsSmallFamily`). Choose a complete metric on `X` and write `G`
as the range of a continuous `g : (ℕ → ℕ) → X × X`. The vertices of level `n` are the binary
words of length `n`, recorded newest letter first as in `PiNat.res`. A *level edge* is the
level-`n` trace of an oriented edge of `orientedGS S`, a pair `r ++ false :: s.reverse` and
`r ++ true :: s.reverse` with `s ∈ S`. A stage of level `n` is an analytic family of maps from
the vertices of level `n` to `X` that is not small, whose members are uniformly within `2⁻ⁿ` of
each other at every vertex, together with a word of naturals for every level edge through whose
cylinder `g` witnesses the values of every member at the two ends of that edge.

A stage of level `n + 1` is obtained by combining two members of a stage of level `n` according
to the newest letter. When `S` has a word `s` of length `n`, the two combined members are
required to form a pair of `G` at `s.reverse`, which creates the one fresh level edge
`(false :: s.reverse, true :: s.reverse)` (`SetRel.not_isSmallFamily_comb_cross`); sparseness is
what makes the fresh edge unique. Every witness word is then extended by one letter
(`SetRel.exists_subset_not_isSmallFamily_witness_extension`) and the vertices are shrunk
(`SetRel.exists_subset_not_isSmallFamily_dist_lt`). Picking one member per stage, the values
along a branch of Cantor space form a Cauchy sequence whose limit is the continuous map `φ`.
Along an oriented edge the witness words grow and nest, and so define a point of Baire space
whose image under `g` is the pair of limit values.

## Main results

* `TauCeti.exists_continuous_orientedGS_hom`: the homomorphism half, for every sparse `S`.
* `TauCeti.g0_dichotomy_oriented`: the G₀ dichotomy for analytic relations.
* `SimpleGraph.g0_dichotomy`: the G₀ dichotomy for simple graphs.
* `Setoid.exists_continuous_forall_gSGraph_adj_not`: a Borel equivalence relation with
  uncountably many classes receives, for every sparse `S`, a continuous map sending adjacent
  points of `gSGraph S` to inequivalent points.

## References

* A. S. Kechris, S. Solecki and S. Todorcevic, *Borel chromatic numbers*, Advances in
  Mathematics 141 (1999), 1–44, Theorem 6.3.
* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of Symbolic
  Logic 18 (2012), 554–575, the classical proof of the G₀ dichotomy through small families.
* The fusion follows `FusionStage`, `exists_fusionStage_succ` and `exists_gsGraph_hom` in
  `InfinitaryLogic/Descriptive/G0Fusion.lean` of `cameronfreer/infinitary-logic` (Apache-2.0),
  checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. There the homomorphism half is proved
  for one fixed word set and symmetric relations; here it is proved for every sparse word set and
  every analytic relation, with vertices recorded newest letter first, and exclusivity and both
  forms of the dichotomy are added.
-/

public section

open Set Function Filter Topology MeasureTheory PiNat

namespace TauCeti

/-! ### Level edges -/

section LevelEdges

variable {S : Set (List Bool)} {n : ℕ}

/-- The level-`n` traces of the oriented edges of `orientedGS S`, with vertices recorded newest
letter first: the pairs `r ++ false :: s.reverse` and `r ++ true :: s.reverse` with `s ∈ S`. -/
private def levelEdges (S : Set (List Bool)) (n : ℕ) :
    Set (List.Vector Bool n × List.Vector Bool n) :=
  {p | ∃ s ∈ S, ∃ r : List Bool,
    p.1.toList = r ++ false :: s.reverse ∧ p.2.toList = r ++ true :: s.reverse}

private theorem not_mem_levelEdges_zero (p : List.Vector Bool 0 × List.Vector Bool 0) :
    p ∉ levelEdges S 0 := by
  rintro ⟨s, -, r, h, -⟩
  simpa using congrArg List.length h

/-- Prepending a common letter to a level edge gives a level edge. -/
private theorem cons_mem_levelEdges {p : List.Vector Bool n × List.Vector Bool n}
    (hp : p ∈ levelEdges S n) (b : Bool) : (b ::ᵥ p.1, b ::ᵥ p.2) ∈ levelEdges S (n + 1) := by
  obtain ⟨s, hs, r, h₁, h₂⟩ := hp
  exact ⟨s, hs, b :: r, by simp [h₁], by simp [h₂]⟩

/-- A level edge of level `n + 1` is either fresh, coming from a word of `S` of length `n`, or
obtained from a level edge of level `n` by prepending a common letter. -/
private theorem mem_levelEdges_succ {p : List.Vector Bool (n + 1) × List.Vector Bool (n + 1)}
    (hp : p ∈ levelEdges S (n + 1)) :
    (∃ s ∈ S, s.length = n ∧ p.1.toList = false :: s.reverse ∧
      p.2.toList = true :: s.reverse) ∨
    (p.1.head = p.2.head ∧ (p.1.tail, p.2.tail) ∈ levelEdges S n) := by
  obtain ⟨s, hs, r, h₁, h₂⟩ := hp
  cases r with
  | nil =>
    refine .inl ⟨s, hs, ?_, h₁, h₂⟩
    simpa using (congrArg List.length h₁).symm
  | cons b r =>
    obtain ⟨hb₁, ht₁⟩ := List.Vector.toList_eq_cons_iff.1 h₁
    obtain ⟨hb₂, ht₂⟩ := List.Vector.toList_eq_cons_iff.1 h₂
    exact .inr ⟨hb₁.trans hb₂.symm, s, hs, r, ht₁, ht₂⟩

/-- The first `n` coordinates of a point of Cantor space, newest first, as a vertex of level
`n`. -/
private def resVec (n : ℕ) (y : ℕ → Bool) : List.Vector Bool n :=
  ⟨res y n, res_length y n⟩

private theorem resVec_eq_resVec_of_res_eq {n : ℕ} {y z : ℕ → Bool} (h : res y n = res z n) :
    resVec n y = resVec n z :=
  List.Vector.toList_injective h

private theorem resVec_succ (y : ℕ → Bool) (n : ℕ) : resVec (n + 1) y = y n ::ᵥ resVec n y :=
  List.Vector.toList_injective <| by rw [List.Vector.toList_cons]; simp [resVec, res_succ]

end LevelEdges

/-! ### Stages of the fusion -/

section Stage

variable {X : Type*}

/-- Combine two assignments of level `n` into one of level `n + 1`, choosing by the newest
letter. -/
private def comb {n : ℕ} (φ₀ φ₁ : List.Vector Bool n → X) (v : List.Vector Bool (n + 1)) : X :=
  (bif v.head then φ₁ else φ₀) v.tail

private theorem comb_cons {n : ℕ} (φ₀ φ₁ : List.Vector Bool n → X) (b : Bool)
    (u : List.Vector Bool n) : comb φ₀ φ₁ (b ::ᵥ u) = (bif b then φ₁ else φ₀) u := by
  simp [comb]

private theorem range_comb_subset {n : ℕ} (φ₀ φ₁ : List.Vector Bool n → X) :
    range (comb φ₀ φ₁) ⊆ range φ₀ ∪ range φ₁ := by
  rintro _ ⟨v, rfl⟩
  cases h : v.head
  · exact .inl ⟨v.tail, by simp [comb, h]⟩
  · exact .inr ⟨v.tail, by simp [comb, h]⟩

private theorem continuous_comb [TopologicalSpace X] {n : ℕ} :
    Continuous (uncurry
      (comb : (List.Vector Bool n → X) → _ → List.Vector Bool (n + 1) → X)) := by
  refine continuous_pi fun v ↦ ?_
  cases h : v.head <;> simp only [uncurry_def, comb, h, Bool.cond_false, Bool.cond_true] <;>
    fun_prop

variable [MetricSpace X] [MeasurableSpace X]

variable (X) in
/-- A stage of level `n` of the fusion: an analytic family of assignments of level `n` that is
not small, whose members are uniformly within `2⁻ⁿ` at every vertex, with a word for each level
edge through whose cylinder `g` witnesses the values of every member at the ends of the edge. -/
private structure Stage (G : SetRel X X) (g : (ℕ → ℕ) → X × X) (S : Set (List Bool)) (n : ℕ)
    where
  fam : Set (List.Vector Bool n → X)
  word : List.Vector Bool n × List.Vector Bool n → List ℕ
  analyticSet_fam : AnalyticSet fam
  not_isSmallFamily_fam : ¬ G.IsSmallFamily fam
  dist_lt : ∀ φ ∈ fam, ∀ ψ ∈ fam, ∀ u, dist (φ u) (ψ u) < (1 / 2 : ℝ) ^ n
  mem_image : ∀ p ∈ levelEdges S n, ∀ φ ∈ fam, (φ p.1, φ p.2) ∈ g '' wordCylinder (word p)

variable {G : SetRel X X} {g : (ℕ → ℕ) → X × X} {S : Set (List Bool)} {n : ℕ}

/-- Combining two members of a stage along a level edge with equal newest letters keeps the
witness of the edge it extends. -/
private theorem comb_mem_image (T : Stage X G g S n) {φ₀ φ₁ : List.Vector Bool n → X}
    (h₀ : φ₀ ∈ T.fam) (h₁ : φ₁ ∈ T.fam) {u v : List.Vector Bool (n + 1)}
    (hhead : u.head = v.head) (htail : (u.tail, v.tail) ∈ levelEdges S n) :
    (comb φ₀ φ₁ u, comb φ₀ φ₁ v) ∈ g '' wordCylinder (T.word (u.tail, v.tail)) := by
  have hφ : (bif u.head then φ₁ else φ₀) ∈ T.fam := by cases u.head <;> assumption
  unfold comb
  rw [← hhead]
  exact T.mem_image _ htail _ hφ

variable [BorelSpace X]

/-- **The combined family.** Combining members of a stage gives an analytic family that is not
small, and whose members send every edge of the next level into the range of `g` along the word of
its parent edge, or along the empty word for a fresh edge. -/
private theorem exists_comb_family (hS : SparseWords S) (hG : AnalyticSet G)
    (hgG : range g = G) (T : Stage X G g S n) :
    ∃ Ψ ⊆ image2 comb T.fam T.fam, AnalyticSet Ψ ∧ ¬ G.IsSmallFamily Ψ ∧
      ∀ p ∈ levelEdges S (n + 1), ∀ ψ ∈ Ψ, (ψ p.1, ψ p.2) ∈ g '' wordCylinder
        (if p.1.head = p.2.head then T.word (p.1.tail, p.2.tail) else []) := by
  classical
  -- Combining along a level edge that extends one of level `n` keeps its witness.
  have hold {φ₀ φ₁ : List.Vector Bool n → X} (h₀ : φ₀ ∈ T.fam) (h₁ : φ₁ ∈ T.fam)
      {u v : List.Vector Bool (n + 1)} (hhead : u.head = v.head)
      (htail : (u.tail, v.tail) ∈ levelEdges S n) :
      (comb φ₀ φ₁ u, comb φ₀ φ₁ v) ∈ g '' wordCylinder
        (if u.head = v.head then T.word (u.tail, v.tail) else []) := by
    simpa only [ite_eq_left hhead] using comb_mem_image T h₀ h₁ hhead htail
  by_cases hfresh : ∃ s ∈ S, s.length = n
  · -- A fresh edge is born at `s.reverse`: combine members forming a pair of `G` there.
    obtain ⟨s₀, hs₀, hlen₀⟩ := hfresh
    let σ : List.Vector Bool n := ⟨s₀.reverse, by simp [hlen₀]⟩
    refine ⟨_, ?_, SetRel.analyticSet_comb_cross hG T.analyticSet_fam σ continuous_comb,
      SetRel.not_isSmallFamily_comb_cross hG T.analyticSet_fam T.not_isSmallFamily_fam σ
        fun _ _ ↦ range_comb_subset _ _, ?_⟩
    · rintro _ ⟨φ₀, h₀, φ₁, h₁, -, rfl⟩
      exact mem_image2_of_mem h₀ h₁
    · rintro ⟨u, v⟩ hp _ ⟨φ₀, h₀, φ₁, h₁, hσ, rfl⟩
      rcases mem_levelEdges_succ hp with ⟨s, hs, hlen, hu, hv⟩ | ⟨hhead, htail⟩
      · obtain rfl : s = s₀ := sparseWords_iff.1 hS s hs s₀ hs₀ (hlen.trans hlen₀.symm)
        obtain ⟨hu₁, hu₂⟩ := List.Vector.toList_eq_cons_iff.1 hu
        obtain ⟨hv₁, hv₂⟩ := List.Vector.toList_eq_cons_iff.1 hv
        obtain ⟨hut, hvt⟩ : u.tail = σ ∧ v.tail = σ :=
          ⟨List.Vector.toList_injective hu₂, List.Vector.toList_injective hv₂⟩
        rw [ite_eq_right (by simp [hu₁, hv₁]), wordCylinder_nil,
          image_univ, hgG]
        simpa [comb, hu₁, hv₁, hut, hvt] using hσ
      · exact hold h₀ h₁ hhead htail
  · -- No fresh edge: combine arbitrary pairs of members.
    refine ⟨_, Subset.rfl, AnalyticSet.image2 continuous_comb T.analyticSet_fam T.analyticSet_fam,
      SetRel.not_isSmallFamily_image2 T.not_isSmallFamily_fam
        fun φ ↦ (range_comb_subset φ φ).trans (union_self _).subset, ?_⟩
    rintro ⟨u, v⟩ hp _ ⟨φ₀, h₀, φ₁, h₁, rfl⟩
    rcases mem_levelEdges_succ hp with ⟨s, hs, hlen, -, -⟩ | ⟨hhead, htail⟩
    · exact absurd ⟨s, hs, hlen⟩ hfresh
    · exact hold h₀ h₁ hhead htail

variable [SecondCountableTopology X]

/-- **The one-step extension.** Every stage of level `n` extends to a stage of level `n + 1` whose
members take, at each vertex `b ::ᵥ u`, the value at `u` of a member of the given stage, and
whose words properly extend the words of the level edges they come from. -/
private theorem exists_stage_succ (hS : SparseWords S) (hG : AnalyticSet G) (hg : Continuous g)
    (hgG : range g = G) (T : Stage X G g S n) :
    ∃ T' : Stage X G g S (n + 1),
      (∀ ψ ∈ T'.fam, ∀ b u, ∃ φ ∈ T.fam, ψ (b ::ᵥ u) = φ u) ∧
      ∀ p ∈ levelEdges S n, ∀ b, T.word p <+: T'.word (b ::ᵥ p.1, b ::ᵥ p.2) ∧
        (T.word p).length < (T'.word (b ::ᵥ p.1, b ::ᵥ p.2)).length := by
  classical
  -- The words a combined family inherits: the word of the parent edge, or the empty word for the
  -- fresh edge.
  let w₀ (p : List.Vector Bool (n + 1) × List.Vector Bool (n + 1)) : List ℕ :=
    if p.1.head = p.2.head then T.word (p.1.tail, p.2.tail) else []
  obtain ⟨Ψ, hΨsub, hΨa, hΨ, hΨw⟩ := exists_comb_family hS hG hgG T
  -- Then extend its words by one letter and shrink its vertices.
  obtain ⟨w, hpre, hlen, Ψ₁, hΨ₁, hΨ₁a, hΨ₁s, hΨ₁w⟩ :=
    SetRel.exists_subset_not_isSmallFamily_witness_extension (κ := levelEdges S (n + 1))
      (e := Subtype.val) (w := fun k ↦ w₀ k.1) hg hΨa hΨ (fun ψ hψ k ↦ hΨw k.1 k.2 ψ hψ) 1
  obtain ⟨Ψ₂, hΨ₂, hΨ₂a, hΨ₂s, hΨ₂d⟩ :=
    SetRel.exists_subset_not_isSmallFamily_dist_lt hΨ₁a hΨ₁s
      (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))
  refine ⟨⟨Ψ₂, fun p ↦ if hp : p ∈ levelEdges S (n + 1) then w ⟨p, hp⟩ else [], hΨ₂a, hΨ₂s,
    hΨ₂d, fun p hp ψ hψ ↦ by simpa [hp] using hΨ₁w ψ (hΨ₂ hψ) ⟨p, hp⟩⟩, ?_, ?_⟩
  · rintro ψ hψ b u
    obtain ⟨φ₀, h₀, φ₁, h₁, rfl⟩ := hΨsub (hΨ₁ (hΨ₂ hψ))
    exact ⟨_, by cases b <;> assumption, comb_cons φ₀ φ₁ b u⟩
  · intro p hp b
    have hp' := cons_mem_levelEdges hp b
    have hw₀ : w₀ (b ::ᵥ p.1, b ::ᵥ p.2) = T.word p := by simp [w₀]
    have hpre' := hpre ⟨_, hp'⟩
    have hlen' := hlen ⟨_, hp'⟩
    simp only [hw₀] at hpre' hlen'
    simp only [dite_eq_left hp']
    exact ⟨hpre', by omega⟩

omit [SecondCountableTopology X] [BorelSpace X] in
/-- **Edges in the fusion limit.** Let a tower of stages have words cohering as in
`exists_stage_succ`, and pick a member `ψ n` of each stage. If the values of `ψ n` along every
branch of Cantor space converge to `φ`, then `φ` sends every oriented edge of `orientedGS S` into
the range of `g`. -/
private theorem mem_range_of_stages (hg : Continuous g) (T : ∀ n, Stage X G g S n)
    (hword : ∀ n, ∀ p ∈ levelEdges S n, ∀ b,
      (T n).word p <+: (T (n + 1)).word (b ::ᵥ p.1, b ::ᵥ p.2) ∧
        ((T n).word p).length < ((T (n + 1)).word (b ::ᵥ p.1, b ::ᵥ p.2)).length)
    {ψ : ∀ n, List.Vector Bool n → X} (hψ : ∀ n, ψ n ∈ (T n).fam) {φ : (ℕ → Bool) → X}
    (hφ : ∀ y, Tendsto (fun n ↦ ψ n (resVec n y)) atTop (𝓝 (φ y))) ⦃y z : ℕ → Bool⦄
    (hyz : (y, z) ∈ orientedGS S) : (φ y, φ z) ∈ range g := by
  obtain ⟨s, hs, x, rfl, rfl⟩ := mem_orientedGS_iff.1 hyz
  set L := s.length + 1
  have hres (b : Bool) (m : ℕ) :
      res (prependWord (s ++ [b]) x) (L + m) = res x m ++ b :: s.reverse := by
    simpa using res_prependWord_length_add (s ++ [b]) x m
  have hcoord (b : Bool) (m : ℕ) : prependWord (s ++ [b]) x (L + m) = x m := by
    simpa using prependWord_apply_length_add (s ++ [b]) x m
  -- The level edges along the oriented edge and their witness words.
  let k (m : ℕ) : List.Vector Bool (L + m) × List.Vector Bool (L + m) :=
    (resVec (L + m) (prependWord (s ++ [false]) x), resVec (L + m) (prependWord (s ++ [true]) x))
  have hk (m : ℕ) : k m ∈ levelEdges S (L + m) :=
    ⟨s, hs, res x m, hres false m, hres true m⟩
  let c (m : ℕ) : List ℕ := (T (L + m)).word (k m)
  -- The levels `L + (m + 1)` and `L + m + 1` agree by definition of addition, so the stage of
  -- level `L + (m + 1)` is the one-step extension of the stage of level `L + m`.
  have hc (m : ℕ) : c m <+: c (m + 1) ∧ (c m).length < (c (m + 1)).length := by
    have e (b : Bool) : resVec (L + (m + 1)) (prependWord (s ++ [b]) x) =
        x m ::ᵥ resVec (L + m) (prependWord (s ++ [b]) x) := by
      rw [← hcoord b m]
      exact resVec_succ _ _
    have hk' : k (m + 1) = (x m ::ᵥ (k m).1, x m ::ᵥ (k m).2) := Prod.ext (e false) (e true)
    simp only [c, hk']
    exact hword _ _ (hk m) (x m)
  have hlen (m : ℕ) : m ≤ (c m).length := by
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih => exact ih.trans_lt (hc m).2
  -- Points of Baire space witnessing the approximating pairs converge, since their words grow
  -- and nest.
  choose γ hγ hgγ using fun m ↦ (T (L + m)).mem_image (k m) (hk m) _ (hψ (L + m))
  obtain ⟨β, hγβ⟩ := exists_tendsto_of_mem_wordCylinder (fun m ↦ (hc m).1)
    (tendsto_atTop_mono hlen tendsto_id) hγ
  have hpair : Tendsto (fun m ↦ g (γ m)) atTop
      (𝓝 (φ (prependWord (s ++ [false]) x), φ (prependWord (s ++ [true]) x))) := by
    simp only [hgγ]
    exact ((hφ _).prodMk_nhds (hφ _)).comp
      (tendsto_atTop_mono (fun m ↦ Nat.le_add_left m L) tendsto_id)
  exact ⟨β, tendsto_nhds_unique ((hg.tendsto β).comp hγβ) hpair⟩

omit [SecondCountableTopology X] [BorelSpace X] in
/-- **The fusion limit.** A tower of stages whose members and words cohere as in
`exists_stage_succ` yields a continuous map of Cantor space sending every oriented edge of
`orientedGS S` into the range of `g`. -/
private theorem exists_continuous_of_stages [CompleteSpace X] (hg : Continuous g)
    (T : ∀ n, Stage X G g S n)
    (hval : ∀ n, ∀ ψ ∈ (T (n + 1)).fam, ∀ b u, ∃ φ ∈ (T n).fam, ψ (b ::ᵥ u) = φ u)
    (hword : ∀ n, ∀ p ∈ levelEdges S n, ∀ b,
      (T n).word p <+: (T (n + 1)).word (b ::ᵥ p.1, b ::ᵥ p.2) ∧
        ((T n).word p).length < ((T (n + 1)).word (b ::ᵥ p.1, b ::ᵥ p.2)).length) :
    ∃ φ : (ℕ → Bool) → X, Continuous φ ∧
      ∀ ⦃y z⦄, (y, z) ∈ orientedGS S → (φ y, φ z) ∈ range g := by
  choose ψ hψ using fun n ↦ SetRel.nonempty_of_not_isSmallFamily (T n).not_isSmallFamily_fam
  -- The approximations of `φ y` along the branch `y`.
  let a (y : ℕ → Bool) (n : ℕ) : X := ψ n (resVec n y)
  have hstep (y : ℕ → Bool) (n : ℕ) : dist (a y n) (a y (n + 1)) ≤ 1 * (1 / 2) ^ n := by
    obtain ⟨φ, hφ, heq⟩ := hval n _ (hψ (n + 1)) (y n) (resVec n y)
    simp only [a, resVec_succ, heq, one_mul]
    exact ((T n).dist_lt _ (hψ n) _ hφ _).le
  choose φ hφ using fun y ↦
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ (by norm_num) (hstep y))
  have hdist (n : ℕ) (y : ℕ → Bool) : dist (a y n) (φ y) ≤ 2 * (1 / 2) ^ n := by
    have := dist_le_of_le_geometric_of_tendsto _ _ (by norm_num) (hstep y) (hφ y) n
    convert this using 1
    ring
  refine ⟨φ, continuous_of_res_eq_of_dist_le (F := fun n y ↦ a y n)
    (fun n y z h ↦ by simp only [a, resVec_eq_resVec_of_res_eq h]) hdist ?_,
    mem_range_of_stages hg T hword hψ hφ⟩
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2

end Stage

/-! ### The G₀ dichotomy -/

section Dichotomy

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The homomorphism half of the G₀ dichotomy.** Let `G` be an analytic relation on a Polish
space with no countable Borel coloring. For every set `S` of words with at most one word of each
length, some continuous map of Cantor space into the space sends every oriented edge of
`orientedGS S` to a pair of `G`. -/
theorem exists_continuous_orientedGS_hom {G : SetRel X X} (hG : AnalyticSet G)
    {S : Set (List Bool)} (hS : SparseWords S) (hcol : ¬ G.HasCountableBorelColoring) :
    ∃ φ : (ℕ → Bool) → X, Continuous φ ∧ ∀ ⦃y z⦄, (y, z) ∈ orientedGS S → (φ y, φ z) ∈ G := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  -- The empty relation is colored by a constant, so `G` is the range of a continuous map on
  -- Baire space.
  have hparam : G = ∅ ∨ ∃ g : (ℕ → ℕ) → _, Continuous g ∧ Set.range g = G := by
    obtain ⟨Z, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hG
    rcases isEmpty_or_nonempty Z with _ | _
    · exact Or.inl (Set.range_eq_empty f)
    · obtain ⟨g, hg, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective Z
      exact Or.inr ⟨f ∘ g, hf.comp hg, hsurj.range_comp f⟩
  obtain hG₀ | ⟨g, hg, rfl⟩ := hparam
  · exact absurd
      (SetRel.hasCountableBorelColoring_iff.2 ⟨fun _ ↦ 0, measurable_const, by simp [hG₀]⟩) hcol
  -- The first stage: all assignments of level `0`, shrunk.
  have : Nonempty (List.Vector Bool 0) := ⟨List.Vector.nil⟩
  obtain ⟨Φ, -, hΦa, hΦ, hΦd⟩ := SetRel.exists_subset_not_isSmallFamily_dist_lt
    (MeasurableSet.univ.analyticSet (α := List.Vector Bool 0 → X))
    (SetRel.isSmallFamily_univ_iff.not.2 hcol)
    (by norm_num : (0 : ℝ) < (1 / 2) ^ 0)
  let T₀ : Stage X (range g) g S 0 :=
    ⟨Φ, fun _ ↦ [], hΦa, hΦ, hΦd, fun p hp ↦ absurd hp (not_mem_levelEdges_zero p)⟩
  -- Iterate the one-step extension.
  choose next hnext using fun n (T : Stage X (range g) g S n) ↦ exists_stage_succ hS hG hg rfl T
  let tower (n : ℕ) : Stage X (range g) g S n := Nat.rec (motive := _) T₀ next n
  exact exists_continuous_of_stages hg tower (fun n ↦ (hnext n (tower n)).1)
    (fun n ↦ (hnext n (tower n)).2)

/-- **The G₀ dichotomy**, oriented form. An analytic relation `G` on a Polish space has a
countable Borel coloring, or there is a continuous map of Cantor space sending every oriented
edge of `orientedGS canonicalWords` to a pair of `G`, and not both. -/
theorem g0_dichotomy_oriented {G : SetRel X X} (hG : AnalyticSet G) :
    Xor G.HasCountableBorelColoring (∃ φ : (ℕ → Bool) → X, Continuous φ ∧
      ∀ ⦃y z⦄, (y, z) ∈ orientedGS canonicalWords → (φ y, φ z) ∈ G) := by
  rw [xor_def]
  by_cases h : G.HasCountableBorelColoring
  · exact .inl ⟨h, fun ⟨φ, hφ, hφG⟩ ↦ not_hasCountableBorelColoring_of_orientedGS_hom
      denseWords_canonicalWords hφ.measurable hφG h⟩
  · exact .inr ⟨exists_continuous_orientedGS_hom hG sparseWords_canonicalWords h, h⟩

end Dichotomy

end TauCeti

open TauCeti in
/-- **The Kechris–Solecki–Todorcevic G₀ dichotomy.** A simple graph on a Polish space whose edge
relation is analytic has a measurable coloring by `ℕ`, or receives a continuous homomorphism from
`gZero`, and not both. -/
theorem SimpleGraph.g0_dichotomy {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (G : SimpleGraph X)
    (hG : AnalyticSet {p : X × X | G.Adj p.1 p.2}) :
    Xor (∃ c : G.Coloring ℕ, Measurable c) (∃ φ : gZero →g G, Continuous φ) := by
  have : (∃ φ : gZero →g G, Continuous φ) ↔ ∃ φ : (ℕ → Bool) → X, Continuous φ ∧
      ∀ ⦃y z⦄, (y, z) ∈ orientedGS canonicalWords → (φ y, φ z) ∈ {p : X × X | G.Adj p.1 p.2} :=
    ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ, hφ, fun _ _ h ↦ φ.map_adj (gZero_adj_iff.2 (.inl h))⟩,
      fun ⟨φ, hφ, hφG⟩ ↦ ⟨⟨φ, fun h ↦ (gZero_adj_iff.1 h).elim (fun h ↦ hφG h)
        fun h ↦ G.adj_symm (hφG h)⟩, hφ⟩⟩
  rw [← G.hasCountableBorelColoring_adj_iff, this]
  exact g0_dichotomy_oriented hG

/-- Let `E` be a Borel equivalence relation on a Polish space with uncountably many classes. For
every set `S` of words with at most one word of each length, some continuous map of Cantor space
sends adjacent points of `gSGraph S` to `E`-inequivalent points. -/
theorem Setoid.exists_continuous_forall_gSGraph_adj_not {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E p.1 p.2}) (hc : ¬ Countable (Quotient E))
    {S : Set (List Bool)} (hS : TauCeti.SparseWords S) :
    ∃ φ : (ℕ → Bool) → X, Continuous φ ∧
      ∀ ⦃y z⦄, (TauCeti.gSGraph S).Adj y z → ¬ E (φ y) (φ z) := by
  obtain ⟨φ, hφ, hφE⟩ := TauCeti.exists_continuous_orientedGS_hom hE.compl.analyticSet hS
    fun h ↦ hc (E.countable_quotient_of_hasCountableBorelColoring_not h)
  exact ⟨φ, hφ, fun y z h ↦ (TauCeti.gSGraph_adj_iff.1 h).elim (fun h ↦ hφE h)
    fun h hyz ↦ hφE h (E.symm hyz)⟩
