/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import Mathlib.ModelTheory.DirectLimit

/-!
# Direct limits of fragment-elementary embeddings

A directed system whose transition embeddings are elementary for a fragment `A` has
`A`-elementary maps into its direct limit. More generally, the same holds for any compatible
cocone of embeddings that jointly cover its target. Consequently sentences and theories in
`A` hold in the limit exactly when they hold in any component. Neither countability nor
formation closure of the fragment is required.

The covering-cocone statement is useful without choosing a particular construction of the
limit. Its universal-quantifier step moves a proposed counterexample and the original tuple
to a common later component; fragment elementarity of the transition maps then reflects it
back to the original component.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016,
  Chapter 1 (elementary chains).

The direct limit and its canonical embeddings are Mathlib's
`FirstOrder.Language.DirectLimit` and `FirstOrder.Language.DirectLimit.of`.
-/

public section

universe u v w w' wι

namespace FirstOrder.Language

variable {L : Language.{u, v}} {ι : Type wι} [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type w} [∀ i, L.Structure (G i)]
  {f : ∀ i j, i ≤ j → G i ↪[L] G j}
  {M : Type w'} [L.Structure M] {A : Fragment L}

private theorem realize_all_of_cocone
    (g : ∀ i, G i ↪[L] M)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hcover : ∀ x, ∃ i y, g i y = x)
    (hf : ∀ i j hij, AElementary A (f i j hij))
    {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)}
    (hφ : (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (ih : ∀ i (a : Fin (n + 1) → G i),
      φ.Realize Empty.elim (g i ∘ a) ↔ φ.Realize Empty.elim a)
    (i : ι) (a : Fin n → G i) :
    φ.all.Realize Empty.elim (g i ∘ a) ↔ φ.all.Realize Empty.elim a := by
  simp only [BoundedFormulaInf.realize_all]
  constructor
  · intro h b
    exact (ih i (Fin.snoc a b)).1 (by simpa only [Fin.comp_snoc] using h (g i b))
  · intro h m
    obtain ⟨j, b, rfl⟩ := hcover m
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have htuple : g k ∘ (f i k hik ∘ a) = g i ∘ a :=
      funext fun t => hg i k hik (a t)
    have hstage : φ.all.Realize Empty.elim (f i k hik ∘ a) := by
      -- At this point only the transition map, not the cocone map, is known elementary.
      exact (AElementary.realize_iff (hf i k hik) hφ a).2 h
    have hbody := (ih k (Fin.snoc (f i k hik ∘ a) (f j k hjk b))).2
      (BoundedFormulaInf.realize_all.1 hstage (f j k hjk b))
    simpa only [Fin.comp_snoc, htuple, hg] using hbody

/-- A jointly covering compatible cocone of embeddings from a directed system of
`A`-elementary transition embeddings has `A`-elementary cocone maps. No directed-system
laws need to be supplied separately: compatibility with the embeddings into `M` suffices. -/
theorem aElementary_of_cocone
    (g : ∀ i, G i ↪[L] M)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hcover : ∀ x, ∃ i y, g i y = x)
    (hf : ∀ i j hij, AElementary A (f i j hij)) (i : ι) :
    AElementary A (g i) := by
  rw [aElementary_iff]
  intro n φ hφ a
  -- Induct simultaneously over all components: a quantifier may need a later component.
  induction φ generalizing i with
  | falsum => simp only [BoundedFormulaInf.realize_falsum]
  | equal t₁ t₂ =>
    have hv : (Empty.elim : Empty → M) = g i ∘ (Empty.elim : Empty → G i) :=
      Subsingleton.elim _ _
    simp only [BoundedFormulaInf.realize_equal, hv, ← Sum.comp_elim,
      HomClass.realize_term, (g i).injective.eq_iff]
  | rel R ts =>
    have hv : (Empty.elim : Empty → M) = g i ∘ (Empty.elim : Empty → G i) :=
      Subsingleton.elim _ _
    simp only [BoundedFormulaInf.realize_rel, hv, ← Sum.comp_elim, HomClass.realize_term]
    exact (g i).map_rel R _
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.realize_imp]
    exact imp_congr (ihφ i (A.imp_left_mem hφ) a) (ihψ i (A.imp_right_mem hφ) a)
  | all φ ih =>
    exact realize_all_of_cocone g hg hcover hf hφ
      (fun j b => ih j (A.all_mem hφ) b) i a
  | iSup φs ih =>
    simp only [BoundedFormulaInf.realize_iSup]
    exact exists_congr fun k => ih k i (A.iSup_mem hφ k) a
  | iInf φs ih =>
    simp only [BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun k => ih k i (A.iInf_mem hφ k) a

section DirectLimit

variable [Nonempty ι] [DirectedSystem G fun i j h => f i j h]

/-- Each canonical embedding into the direct limit of a directed system of
`A`-elementary embeddings is `A`-elementary. -/
theorem aElementary_directLimit_of (hf : ∀ i j hij, AElementary A (f i j hij)) (i : ι) :
    AElementary A (DirectLimit.of L ι G f i) :=
  aElementary_of_cocone (DirectLimit.of L ι G f)
    (fun _ _ _ _ => DirectLimit.of_f) DirectLimit.exists_of hf i

namespace DirectLimit

/-- A sentence in `A` holds in a direct limit of `A`-elementary embeddings exactly
when it holds in any specified component. -/
theorem realize_sentenceInf_iff (hf : ∀ i j hij, AElementary A (f i j hij))
    {φ : L.Sentenceω} (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (i : ι) :
    SentenceInf.Realize φ (DirectLimit G f) ↔ SentenceInf.Realize φ (G i) :=
  AElementary.realize_sentenceInf_iff (aElementary_directLimit_of hf i) hφ

/-- A theory of sentences in `A` holds in a direct limit of `A`-elementary embeddings
exactly when it holds in any specified component. -/
theorem theoryω_model_iff (hf : ∀ i j hij, AElementary A (f i j hij))
    {T : L.Theoryω} (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (i : ι) :
    T.Model (DirectLimit G f) ↔ T.Model (G i) :=
  AElementary.theoryω_model_iff (aElementary_directLimit_of hf i) hT

end DirectLimit

end DirectLimit

end FirstOrder.Language
