/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Minimal.Basic
public import TauCeti.ModelTheory.Counting.Scattered.Vaught
import Mathlib.Data.List.OfFn

/-!
# Minimally uncountable strengthenings of scattered sentences

Every scattered sentence with uncountably many countably infinite models up to isomorphism
has a strengthening whose models on `ℕ` are minimally uncountable. This is the splitting-tree
reduction of Harnik–Makkai and Steel.

If no strengthening is minimal, each large sentence class splits into two large sentence
classes. Scott approximation sentences and saturation let us choose the children to be whole
back-and-forth classes, at higher countable levels. The limit-model theorem realizes every
infinite branch. Distinct branches then give distinct classes at a single countable level,
contradicting scatteredness. The argument uses no continuum hypothesis and makes no continuity
claim about the chosen branch models.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2, Lemmas XII.5–XII.6 and Theorem XII.7. We use the one-element back-and-forth hierarchy,
  with the `+ ω` chain offset supplied by `exists_limit_of_bfEquiv_chain`.
* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proceedings of the
  American Mathematical Society 67 (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689,
  Springer, 1978, 193–208.
-/

public section

universe u v

open FirstOrder FirstOrder.Language Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

private theorem exists_large_levelClass {K : Set (RelationalConfiguration L ℕ)}
    (hK : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) (hscat : BFScattered K)
    {α : Ordinal.{0}} (hα : α < ω₁)
    (hsat : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α c d → d ∈ K) :
    ∃ c ∈ K, ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ α c d}).Countable ∧
      {d | bfEquivSetoid L ℕ α c d} ⊆ K := by
  have := hscat.countable_quotient hα
  -- If every class were small, the countable-partition selection theorem would contradict it.
  have hex : ∃ c ∈ K,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (K ∩ {d | bfEquivSetoid L ℕ α c d})).Countable := by
    by_contra! h
    obtain ⟨c, hc, hlarge, _⟩ := (bfEquivSetoid L ℕ α).exists_class_not_small_and_small_sdiff
      K (fun A => (Quotient.mk (isoSetoid L ℕ) '' A).Countable)
      (fun S hS hs => by rw [image_sUnion, sUnion_image]; exact hS.biUnion hs)
      hK (fun c hc => Or.inl (h c hc))
    exact hlarge (h c hc)
  obtain ⟨c, hc, hlarge⟩ := hex
  exact ⟨c, hc, fun h => hlarge (h.mono (image_mono inter_subset_right)), hsat c hc⟩

/-- A node records a large whole level class inside the given sentence class. -/
private structure LargeNode (Θ : L.Sentenceω) where
  level : Ordinal.{0}
  countable_level : level < ω₁
  centre : RelationalConfiguration L ℕ
  large : ¬ (Quotient.mk (isoSetoid L ℕ) ''
    {d | bfEquivSetoid L ℕ level centre d}).Countable
  subset_models : {d | bfEquivSetoid L ℕ level centre d} ⊆ modelsOf Θ

private theorem exists_largeNode [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (hΘ : BFScattered (modelsOf (V := ℕ) Θ))
    (hlarge : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    Nonempty (LargeNode Θ) := by
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated_modelsOf (V := ℕ) Θ
  obtain ⟨c, _, hc, hsub⟩ := exists_large_levelClass hlarge hΘ hα
    (fun c hc d hcd => (hsat α le_rfl c d hcd).mp hc)
  exact ⟨⟨α, hα, c, hc, hsub⟩⟩

private theorem LargeNode.exists_children [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (hΘ : BFScattered (modelsOf (V := ℕ) Θ))
    (hnomin : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)))
    (p : LargeNode Θ) :
    ∃ q : Bool → LargeNode Θ,
      (∀ b, p.level + ω ≤ (q b).level) ∧
      (∀ b, bfEquivSetoid L ℕ p.level p.centre (q b).centre) ∧
      (q false).level = (q true).level ∧
      ¬ bfEquivSetoid L ℕ (q false).level (q false).centre (q true).centre := by
  let C := {d | bfEquivSetoid L ℕ p.level p.centre d}
  have hC : modelsOf (V := ℕ) (Θ ⊓ p.centre.scottSentenceAtLevel p.level) = C := by
    rw [modelsOf_inf, modelsOf_scottSentenceAtLevel p.centre p.countable_level]
    exact inter_eq_right.mpr p.subset_models
  have hnot := hnomin (p.centre.scottSentenceAtLevel p.level)
  rw [hC, minimallyUncountableOn_iff] at hnot
  obtain ⟨θ, hleft, hright⟩ : ∃ θ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (C ∩ modelsOf θ)).Countable ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) '' (C \ modelsOf θ)).Countable := by
    have hs : ¬ ∀ θ : L.Sentenceω,
        (Quotient.mk (isoSetoid L ℕ) '' (C ∩ modelsOf θ)).Countable ∨
          (Quotient.mk (isoSetoid L ℕ) '' (C \ modelsOf θ)).Countable := fun h => hnot ⟨p.large, h⟩
    push Not at hs
    exact hs
  obtain ⟨δ, hδ, hsat⟩ := exists_bfLevel_saturated_modelsOf (V := ℕ) θ
  let β := max (p.level + ω) δ
  have hβ : β < ω₁ := max_lt
    (Ordinal.isPrincipal_add_omega 1 p.countable_level Ordinal.omega0_lt_omega_one) hδ
  have hpβ : p.level ≤ β := le_trans le_self_add (le_max_left _ _)
  have hsame (c d : RelationalConfiguration L ℕ) (hcd : bfEquivSetoid L ℕ β c d) :
      c ∈ modelsOf θ ↔ d ∈ modelsOf θ := hsat β (le_max_right _ _) c d hcd
  have hCclosed (c : RelationalConfiguration L ℕ) (hc : c ∈ C) (d)
      (hcd : bfEquivSetoid L ℕ β c d) : d ∈ C :=
    (bfEquivSetoid L ℕ p.level).trans hc (bfEquivSetoid_anti hpβ hcd)
  obtain ⟨c₀, hc₀, hlarge₀, hsub₀⟩ := exists_large_levelClass hleft
    (hΘ.mono (inter_subset_left.trans p.subset_models)) hβ
    (fun c hc d hcd => ⟨hCclosed c hc.1 d hcd, (hsame c d hcd).mp hc.2⟩)
  obtain ⟨c₁, hc₁, hlarge₁, hsub₁⟩ := exists_large_levelClass hright
    (hΘ.mono (sdiff_subset.trans p.subset_models)) hβ
    (fun c hc d hcd => ⟨hCclosed c hc.1 d hcd, fun hd => hc.2 ((hsame c d hcd).mpr hd)⟩)
  let q₀ : LargeNode Θ :=
    ⟨β, hβ, c₀, hlarge₀, hsub₀.trans (inter_subset_left.trans p.subset_models)⟩
  let q₁ : LargeNode Θ :=
    ⟨β, hβ, c₁, hlarge₁, hsub₁.trans (sdiff_subset.trans p.subset_models)⟩
  refine ⟨(fun b => if b then q₁ else q₀), ?_, ?_, rfl, ?_⟩
  · intro b; cases b <;> exact le_max_left _ _
  · intro b; cases b
    · exact hc₀.1
    · exact hc₁.1
  · exact fun h => hc₁.2 ((hsame c₀ c₁ h).mp hc₀.2)

/-- The node on a binary branch after reading its first `n` bits. -/
private def branchNode {Θ : L.Sentenceω} (a : List Bool → LargeNode Θ)
    (z : ℕ → Bool) (n : ℕ) : LargeNode Θ :=
  a (List.ofFn fun i : Fin n => z i)

private theorem branchNode_succ {Θ : L.Sentenceω} (a : List Bool → LargeNode Θ)
    (z : ℕ → Bool) (n : ℕ) :
    branchNode a z (n + 1) = a ((List.ofFn fun i : Fin n => z i) ++ [z n]) := by
  dsimp only [branchNode]
  rw [List.ofFn_succ']
  simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]

private theorem LargeNode.exists_branch_limit {Θ : L.Sentenceω} (p : ℕ → LargeNode Θ)
    (hgrow : ∀ n, (p n).level + ω ≤ (p (n + 1)).level)
    (hlink : ∀ n, bfEquivSetoid L ℕ (p n).level (p n).centre (p (n + 1)).centre) :
    ∃ d, d ∈ modelsOf Θ ∧ ∀ n, bfEquivSetoid L ℕ (p n).level d (p n).centre := by
  have hmono : Monotone (fun n => (p n).level) := monotone_nat_of_le_succ
    fun n => le_trans le_self_add (hgrow n)
  -- Shift the codes by one node: their links then have the extra omega required by the limit.
  obtain ⟨d, hd⟩ := exists_limit_of_bfEquiv_chain hmono
    (fun n => bfEquivSetoid_anti (hgrow n) (hlink (n + 1)))
  have hmatch (n : ℕ) : bfEquivSetoid L ℕ (p n).level d (p n).centre :=
    (bfEquivSetoid L ℕ (p n).level).trans (hd n)
      ((bfEquivSetoid L ℕ (p n).level).symm (hlink n))
  exact ⟨d, (p 0).subset_models ((bfEquivSetoid L ℕ (p 0).level).symm (hmatch 0)), hmatch⟩

private theorem branches_separated {Θ : L.Sentenceω} (a : List Bool → LargeNode Θ)
    (hsame : ∀ s, (a (s ++ [false])).level = (a (s ++ [true])).level)
    (hsplit : ∀ s, ¬ bfEquivSetoid L ℕ (a (s ++ [false])).level
      (a (s ++ [false])).centre (a (s ++ [true])).centre)
    {β : Ordinal.{0}} (hbound : ∀ s, (a s).level ≤ β)
    (f : (ℕ → Bool) → RelationalConfiguration L ℕ)
    (hf : ∀ z n, bfEquivSetoid L ℕ (branchNode a z n).level (f z) (branchNode a z n).centre)
    {z w : ℕ → Bool} (hne : z ≠ w) : ¬ bfEquivSetoid L ℕ β (f z) (f w) := by
  classical
  have hsiblings (s : List Bool) (b c : Bool) (hne : b ≠ c) :
      (a (s ++ [b])).level = (a (s ++ [c])).level ∧
        ¬ bfEquivSetoid L ℕ (a (s ++ [b])).level
          (a (s ++ [b])).centre (a (s ++ [c])).centre := by
    cases b <;> cases c
    · exact (hne rfl).elim
    · exact ⟨hsame s, hsplit s⟩
    · refine ⟨(hsame s).symm, ?_⟩
      rw [← hsame s]
      exact fun h => hsplit s ((bfEquivSetoid L ℕ _).symm h)
    · exact (hne rfl).elim
  -- At the first differing bit the branches choose separated siblings of the same node.
  let n := Nat.find (Function.ne_iff.mp hne)
  have hn : z n ≠ w n := Nat.find_spec (Function.ne_iff.mp hne)
  have heq : (List.ofFn fun i : Fin n => z i) = List.ofFn (fun i : Fin n => w i) := by
    apply congrArg List.ofFn
    funext i
    exact not_ne_iff.mp (Nat.find_min (Function.ne_iff.mp hne) i.2)
  obtain ⟨hzw, hnsep⟩ :
      (branchNode a z (n + 1)).level = (branchNode a w (n + 1)).level ∧
        ¬ bfEquivSetoid L ℕ (branchNode a z (n + 1)).level
          (branchNode a z (n + 1)).centre (branchNode a w (n + 1)).centre := by
    rw [branchNode_succ a z n, branchNode_succ a w n, ← heq]
    exact hsiblings _ (z n) (w n) hn
  intro h
  have hw := hf w (n + 1)
  rw [← hzw] at hw
  exact hnsep ((bfEquivSetoid L ℕ _).trans
    ((bfEquivSetoid L ℕ _).symm (hf z (n + 1)))
    ((bfEquivSetoid L ℕ _).trans (bfEquivSetoid_anti (hbound _) h) hw))

/-- A splitting tree of large whole classes contradicts scatteredness. -/
private theorem not_bfScattered_of_splittingTree {Θ : L.Sentenceω}
    (a : List Bool → LargeNode Θ)
    (hgrow : ∀ s b, (a s).level + ω ≤ (a (s ++ [b])).level)
    (hparent : ∀ s b, bfEquivSetoid L ℕ (a s).level (a s).centre (a (s ++ [b])).centre)
    (hsame : ∀ s, (a (s ++ [false])).level = (a (s ++ [true])).level)
    (hsplit : ∀ s, ¬ bfEquivSetoid L ℕ (a (s ++ [false])).level
      (a (s ++ [false])).centre (a (s ++ [true])).centre) :
    ¬ BFScattered (modelsOf (V := ℕ) Θ) := by
  classical
  -- All node levels, including those on different branches, have one countable bound.
  let β : Ordinal.{0} := ⨆ s : List Bool, (a s).level
  have hβ : β < ω₁ := iSup_lt_omega_one fun s => (a s).countable_level
  have hgrow' (z : ℕ → Bool) (n : ℕ) :
      (branchNode a z n).level + ω ≤ (branchNode a z (n + 1)).level := by
    rw [branchNode_succ]; exact hgrow _ _
  have hparent' (z : ℕ → Bool) (n : ℕ) : bfEquivSetoid L ℕ (branchNode a z n).level
      (branchNode a z n).centre (branchNode a z (n + 1)).centre := by
    rw [branchNode_succ]; exact hparent _ _
  choose f hmodel hf using fun z =>
    LargeNode.exists_branch_limit (branchNode a z) (hgrow' z) (hparent' z)
  intro hscat
  have := hscat.countable_quotient hβ
  have hinj : Function.Injective (fun z : ℕ → Bool =>
      Quotient.mk ((bfEquivSetoid L ℕ β).comap (Subtype.val : modelsOf (V := ℕ) Θ → _))
        ⟨f z, hmodel z⟩) := by
    intro z w h
    by_contra hne
    exact branches_separated a hsame hsplit (Ordinal.le_iSup _) f hf hne (Quotient.exact
      (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : modelsOf (V := ℕ) Θ → _)) h)
  have : Countable (ℕ → Bool) := hinj.countable
  have hle : Cardinal.mk (ℕ → Bool) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  exact Cardinal.aleph0_lt_continuum.not_ge (by
    simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
      Cardinal.two_power_aleph0] using hle)

/-- **The minimal-counterexample reduction.** A sentence with back-and-forth scattered models
on `ℕ` meeting uncountably many isomorphism classes has a minimally uncountable strengthening.
The count concerns models on `ℕ`; finite tiers need not be thin. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered [Countable (Σ n, L.Relations n)]
    {Θ : L.Sentenceω}
    (hΘ : BFScattered (modelsOf (V := ℕ) Θ))
    (hlarge : ¬ Countable (Quotient (isoSetoidOn ℕ Θ))) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  classical
  by_contra! hnomin
  have hlarge' : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable := by
    simpa only [isoSetoidOn, Setoid.countable_quotient_comap_val_iff] using hlarge
  obtain ⟨root⟩ := exists_largeNode hΘ hlarge'
  choose child hgrow hparent hsame hsplit using LargeNode.exists_children hΘ hnomin
  let a (s : List Bool) : LargeNode Θ := s.foldl (fun p b => child p b) root
  have ha (s : List Bool) (b : Bool) : a (s ++ [b]) = child (a s) b := by
    simp [a, List.foldl_append]
  apply not_bfScattered_of_splittingTree a _ _ _ _ hΘ
  · intro s b; rw [ha]; exact hgrow _ b
  · intro s b; rw [ha]; exact hparent _ b
  · intro s; rw [ha, ha]; exact hsame _
  · intro s; rw [ha, ha]; exact hsplit _

/-- Every counterexample to the witnessed Vaught dichotomy has a strengthening with minimally
uncountable models on `ℕ`. This is a reduction of counterexamples, without any assumption on CH. -/
theorem exists_minimallyUncountableOn_inf_of_not_hasVaughtDichotomy
    [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (h : ¬ HasVaughtDichotomy Θ) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  have hlarge : ¬ Countable (Quotient (isoSetoidOn ℕ Θ)) :=
    fun hc => h (hasVaughtDichotomy_of_nat (.inl hc))
  have hthin : IsThinOnNatModels Θ := isThinOnNatModels_iff.2
    fun hp => h (hasVaughtDichotomy_of_nat (.inr hp))
  exact exists_minimallyUncountableOn_inf_of_bfScattered hthin.bfScattered_modelsOf hlarge

end TauCeti
