/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Fragment
public import TauCeti.ModelTheory.Infinitary.Theory

/-!
# Elementarity relative to a fragment and the Tarski–Vaught criterion

Let `A` be a fragment of `L_{ω₁ω}`. An embedding `f : N ↪[L] M` is **`A`-elementary** when every
member `⟨n, φ⟩` of `A` holds of `f ∘ a` in `M` exactly when it holds of `a` in `N`, for every tuple
`a : Fin n → N`. It is stated as an equivalence, since a fragment need not contain negations.

The fragment Tarski–Vaught criterion upgrades a witness condition to `A`-elementarity: if, for
every universal member `∀ x, φ` of `A` and every tuple from `N`, whenever `φ` has a counterexample
in `M` at that tuple it has one in the image of `N`, then `f` is `A`-elementary. The witnesses
are elements, so no substitution of terms enters the induction, which uses exactly the component
closure of `A`. No formation closure of `A`, countability of the language or nonemptiness of the
carriers is needed.

## Main definitions

* `FirstOrder.Language.AElementary A f`: `f` is `A`-elementary.

## Main results

* `FirstOrder.Language.AElementary.refl`, `FirstOrder.Language.AElementary.comp` and
  `FirstOrder.Language.AElementary.of_comp`: identity, composition, and the two-out-of-three
  lemma.
* `FirstOrder.Language.AElementary.mono`: `A`-elementarity passes to smaller fragments.
* `FirstOrder.Language.Equiv.aElementary`: an isomorphism is `A`-elementary for every `A`.
* `FirstOrder.Language.AElementary.realize_sentenceInf_iff` and
  `FirstOrder.Language.AElementary.theoryω_model_iff`: sentences and theories of `A` hold in `N`
  exactly when they hold in `M`.
* `FirstOrder.Language.OmitsType.of_aElementary`: omission of a partial type in `A` passes along
  `A`-elementary embeddings.
* `FirstOrder.Language.aElementary_of_tarskiVaught`: the fragment Tarski–Vaught criterion.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/ModelTheory/AElementary.lean`.
* Divergences from that source: monotonicity in the fragment and isomorphism transport are added;
  the atomic cases are proved from Mathlib's term realization along homomorphisms. As in the
  source, the language and the carriers live in independent universes.
-/

public section

universe u v w w' w''

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-- An embedding `f : N ↪[L] M` is **`A`-elementary** for a fragment `A` when every member of `A`
holds of `f ∘ a` in `M` exactly when it holds of `a` in `N`, at every tuple `a` from `N`. -/
def AElementary (A : Fragment L) (f : N ↪[L] M) : Prop :=
  ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n), (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
    ∀ a : Fin n → N, φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a

/-- Unfolding lemma for `AElementary`. -/
theorem aElementary_iff {A : Fragment L} {f : N ↪[L] M} :
    AElementary A f ↔ ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
        ∀ a : Fin n → N, φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a :=
  Iff.rfl

namespace AElementary

variable {A B : Fragment L}

/-- An `A`-elementary embedding preserves and reflects every member of `A` at every tuple. -/
theorem realize_iff {f : N ↪[L] M} (h : AElementary A f) {n : ℕ} {φ : L.BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (a : Fin n → N) :
    φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a :=
  h φ hφ a

/-- The identity embedding is `A`-elementary. -/
theorem refl (A : Fragment L) : AElementary A (Embedding.refl L M) :=
  fun _ _ _ => Iff.rfl

/-- `A`-elementary embeddings compose. -/
theorem comp {f : N ↪[L] M} {g : P ↪[L] N} (hf : AElementary A f) (hg : AElementary A g) :
    AElementary A (f.comp g) :=
  fun _ hφ a => (hf.realize_iff hφ (g ∘ a)).trans (hg.realize_iff hφ a)

/-- **Two out of three.** If `f` and `f ∘ g` are `A`-elementary, so is `g`. -/
theorem of_comp {f : N ↪[L] M} {g : P ↪[L] N} (hf : AElementary A f)
    (hfg : AElementary A (f.comp g)) : AElementary A g :=
  fun _ hφ a => (hf.realize_iff hφ (g ∘ a)).symm.trans (hfg.realize_iff hφ a)

/-- `A`-elementarity passes to smaller fragments. -/
theorem mono {f : N ↪[L] M} (hAB : A ≤ B) (h : AElementary B f) : AElementary A f :=
  fun _ hφ a => h.realize_iff (IsConcreteLE.le_iff.1 hAB hφ) a

/-- **Sentences of `A`** hold in `N` exactly when they hold in `M`. -/
theorem realize_sentenceInf_iff {f : N ↪[L] M} (h : AElementary A f) {φ : L.Sentenceω}
    (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  rw [← h.realize_iff hφ default]
  -- the empty tuples of `M` agree
  exact Iff.of_eq (congrArg _ (Subsingleton.elim _ _))

/-- **Theories of `A`** hold in `N` exactly when they hold in `M`. -/
theorem theoryω_model_iff {f : N ↪[L] M} (h : AElementary A f) {T : L.Theoryω}
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    T.Model M ↔ T.Model N := by
  simp only [Theoryω.model_iff]
  exact forall₂_congr fun φ hφ => h.realize_sentenceInf_iff (hT φ hφ)

end AElementary

/-- **Omission passes along `A`-elementary embeddings.** If `M` omits a partial type whose members
lie in `A`, so does every structure embedded in `M` by an `A`-elementary embedding. -/
theorem OmitsType.of_aElementary {A : Fragment L} {f : N ↪[L] M} (hf : AElementary A f) {n : ℕ}
    {p : Set (L.BoundedFormulaω Empty n)}
    (hp : ∀ φ ∈ p, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (h : OmitsType M p) :
    OmitsType N p :=
  omitsType_iff.2 fun a =>
    let ⟨φ, hφp, hφ⟩ := omitsType_iff.1 h (f ∘ a)
    ⟨φ, hφp, fun hr => hφ ((hf.realize_iff (hp φ hφp) a).2 hr)⟩

/-- An isomorphism is `A`-elementary for every fragment `A`. -/
theorem Equiv.aElementary (A : Fragment L) (e : N ≃[L] M) : AElementary A e.toEmbedding := by
  intro n φ _ a
  -- the empty valuation of the free variables is transported along `e` as well
  have h := StrongHomClass.realize_boundedFormulaInf e φ (v := (Empty.elim : Empty → N)) (xs := a)
  rwa [Subsingleton.elim (e ∘ (Empty.elim : Empty → N)) Empty.elim] at h

/-- **The fragment Tarski–Vaught criterion.** If, for every universal member `∀ x, φ` of `A` and
every tuple `a` from `N`, whenever `φ` has a counterexample at `f ∘ a` in `M` it has one in the
image of `f`, then `f` is `A`-elementary. -/
theorem aElementary_of_tarskiVaught {A : Fragment L} (f : N ↪[L] M)
    (htv : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1)),
      (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A → ∀ a : Fin n → N,
        (∃ m : M, ¬ φ.Realize Empty.elim (Fin.snoc (f ∘ a) m)) →
          ∃ b : N, ¬ φ.Realize Empty.elim (Fin.snoc (f ∘ a) (f b))) :
    AElementary A f := by
  intro n φ
  -- the free-variable valuation of `M` is the image of that of `N`
  have hv : (Empty.elim : Empty → M) = f ∘ (Empty.elim : Empty → N) :=
    Subsingleton.elim _ _
  induction φ with
  | falsum => exact fun _ _ => by simp only [BoundedFormulaInf.realize_falsum]
  | equal t₁ t₂ =>
    intro _ a
    simp only [BoundedFormulaInf.realize_equal, hv, ← Sum.comp_elim, HomClass.realize_term,
      f.injective.eq_iff]
  | rel R ts =>
    intro _ a
    simp only [BoundedFormulaInf.realize_rel, hv, ← Sum.comp_elim, HomClass.realize_term]
    exact f.map_rel R _
  | imp φ ψ ihφ ihψ =>
    intro hmem a
    simp only [BoundedFormulaInf.realize_imp]
    exact imp_congr (ihφ (A.imp_left_mem hmem) a) (ihψ (A.imp_right_mem hmem) a)
  | all φ ih =>
    intro hmem a
    have hbody := A.all_mem hmem
    -- a point of the image extends `f ∘ a` as the image of the extended tuple
    have hsnoc (b : N) : (Fin.snoc (f ∘ a) (f b) : Fin _ → M) = f ∘ Fin.snoc a b :=
      (Fin.comp_snoc f a b).symm
    simp only [BoundedFormulaInf.realize_all]
    constructor
    · intro hM b
      exact (ih hbody (Fin.snoc a b)).1 (hsnoc b ▸ hM (f b))
    · intro hN m
      by_contra hm
      obtain ⟨b, hb⟩ := htv φ hmem a ⟨m, hm⟩
      exact hb (hsnoc b ▸ (ih hbody (Fin.snoc a b)).2 (hN b))
  | iSup φs ih =>
    intro hmem a
    simp only [BoundedFormulaInf.realize_iSup]
    exact exists_congr fun k => ih k (A.iSup_mem hmem k) a
  | iInf φs ih =>
    intro hmem a
    simp only [BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun k => ih k (A.iInf_mem hmem k) a

end Language

end FirstOrder
