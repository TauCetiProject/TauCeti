/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import TauCeti.ModelTheory.ModelExistence.ModelExistence
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import TauCeti.Logic.Function.Update
import TauCeti.ModelTheory.Infinitary.ConstantSupport
import TauCeti.ModelTheory.Infinitary.Sublanguage

/-!
# Boundedness of well-orderings in `L_{ω₁ω}`

Fix a binary relation symbol `lt` of an arbitrary language. An `L_{ω₁ω}` sentence `φ` whose models
carry `lt`-chains of every countable length also has a countable model carrying an `lt`-chain
indexed by the rationals (Marker, *Lectures on Infinitary Model Theory*, 4.4.1). Such a chain is
not well-founded, so a sentence all of whose models are well-founded for `lt` bounds their chains
by a countable ordinal. Consequently the well-ordered models of a sentence have uniformly bounded
countable order type, and no sentence defines the class of well-orders.

The proof applies model existence to a consistency property. Name each rational `q` by a Henkin
constant `d_q`. A member is `{φ} ∪ {d_q < d_r : q < r} ∪ σ` with `σ` finite and mentioning finitely
many constants, such that for every countable `α` some model of `φ` carries a well-ordered chain
in which the rational constants of `σ` are placed in order with gaps of length more than `α`,
including before the first and after the last. The disjunctive clauses hold because `ω₁` is
regular: countably many choices, each failing below some countable `α`, cannot all fail at the
supremum of these bounds, and the gap condition is downward closed in `α`. A new rational is placed
inside a gap of a model chosen for a larger bound. Witnesses are obtained by reinterpreting a
constant that does not occur in `σ`.

## Main definitions

* `FirstOrder.Language.RelChain`: a map whose image is an `lt`-chain along the order of its domain.
* `FirstOrder.Language.Sentenceω.HasWellOrderedChains`: models of a sentence carry `lt`-chains of
  every countable length.

## Main results

* `FirstOrder.Language.RelChain.not_wellFounded`: a chain indexed by an order without a least
  element makes `lt` ill-founded.
* `FirstOrder.Language.RelChain.injective_of_irreflexive`: a chain for an irreflexive `lt` is
  injective.
* `FirstOrder.Language.Sentenceω.exists_model_relChain_rat`: a sentence with well-ordered chains of
  every countable length has a countable nonempty model with a chain indexed by `ℚ`.
* `FirstOrder.Language.Sentenceω.wellFounded_boundedness`: if `lt` is well-founded in every nonempty
  model of a sentence, some countable ordinal indexes a chain in no such model.
* `FirstOrder.Language.Sentenceω.wellOrder_type_boundedness`: if `lt` well-orders every model of a
  sentence, the order types of its models are bounded by a countable ordinal.
* `FirstOrder.Language.wellOrdering_undefinable`: no `L_{ω₁ω}` sentence defines the structures in
  which `lt` is a well-order.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, §4.4.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/WellOrdering/`, formalizes these theorems. Its `StarCondition.lean` has
  the same member shape: a fixed base with a finite remainder, the atoms `d_q < d_r` being read off
  the chain rather than realized in full. Divergences from that source: it works over
  `Language.{0, 0}` with models in `Type`, proves countable relational cores and reaches function
  symbols through a graph translation, while here the language and the universes are arbitrary and
  no graph translation is needed, since model existence handles closed terms through its naming
  clause. The rationals are marked by a `Finset` with ordinal positions rather than by an increasing
  enumeration, and all closure clauses go through one extension step.
-/

public section

universe u v w w'

namespace FirstOrder.Language

open BoundedFormulaInf Structure Ordinal

variable {L : Language.{u, v}}

/-! ### Chains -/

section RelChain

variable {M : Type w} [L.Structure M] {lt : L.Relations 2} {β : Type*}

/-- A map `f` is an `lt`-chain when `lt` holds of `f x` and `f y` whenever `x < y`. -/
def RelChain (lt : L.Relations 2) [LT β] (f : β → M) : Prop :=
  ∀ x y, x < y → RelMap lt ![f x, f y]

/-- The defining property of a chain. -/
theorem relChain_iff [LT β] {f : β → M} :
    RelChain lt f ↔ ∀ x y, x < y → RelMap lt ![f x, f y] :=
  Iff.rfl

/-- A chain indexed by a nonempty order without a least element makes `lt` ill-founded. -/
theorem RelChain.not_wellFounded [LT β] [NoMinOrder β] [Nonempty β] {f : β → M}
    (h : RelChain lt f) : ¬WellFounded fun x y : M => RelMap lt ![x, y] := by
  intro wf
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := wf.has_min (Set.range f) (Set.range_nonempty f)
  obtain ⟨y, hy⟩ := exists_lt x
  exact hx _ ⟨y, rfl⟩ (h y x hy)

/-- A chain for an irreflexive relation is injective. -/
theorem RelChain.injective_of_irreflexive [LinearOrder β] {f : β → M} (h : RelChain lt f)
    (hlt : ∀ x : M, ¬RelMap lt ![x, x]) : Function.Injective f := by
  have : Std.Irrefl (fun x y : M => RelMap lt ![x, y]) := ⟨hlt⟩
  exact injective_of_increasing (· < ·) (fun x y : M => RelMap lt ![x, y]) f
    fun hxy => h _ _ hxy

end RelChain

namespace Sentenceω

/-- A sentence **has well-ordered chains** when, for every countable ordinal `α`, some nonempty
model of the sentence in `Type w` carries an `lt`-chain indexed by `α`. -/
def HasWellOrderedChains (φ : L.Sentenceω) (lt : L.Relations 2) : Prop :=
  ∀ α : Ordinal.{w}, α < ω₁ → ∃ (M : Type w) (_ : L.Structure M), Nonempty M ∧
    SentenceInf.Realize φ M ∧ ∃ f : α.ToType → M, RelChain lt f

/-- The defining property of a sentence with well-ordered chains. -/
theorem hasWellOrderedChains_iff {φ : L.Sentenceω} {lt : L.Relations 2} :
    HasWellOrderedChains.{u, v, w} φ lt ↔
      ∀ α : Ordinal.{w}, α < ω₁ → ∃ (M : Type w) (_ : L.Structure M), Nonempty M ∧
        SentenceInf.Realize φ M ∧ ∃ f : α.ToType → M, RelChain lt f :=
  Iff.rfl

/-! ### Truth under an interpretation of the constants -/

section Sat

variable {M : Type w} [L.Structure M]

/-- Truth of a sentence of `L[[ℕ]]` in the expansion of `M` interpreting `L.con c` as `e c`. -/
private def Sat (e : ℕ → M) (χ : L[[ℕ]].Sentenceω) : Prop :=
  letI := constantsOn.structure e
  SentenceInf.Realize χ M

/-- The value of a closed term of `L[[ℕ]]` in the expansion of `M` given by `e`. -/
private def val (e : ℕ → M) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) : M :=
  letI := constantsOn.structure e
  t.realize (Sum.elim Empty.elim default)

/-- Truth of a formula with one bound position at `m`, in the expansion of `M` given by `e`. -/
private def Holds (e : ℕ → M) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) (m : M) : Prop :=
  letI := constantsOn.structure e
  ψ.Realize Empty.elim fun _ => m

private theorem sat_congr {e e' : ℕ → M} {χ : L[[ℕ]].Sentenceω}
    (h : Set.EqOn e e' χ.constantSupport) : Sat e χ ↔ Sat e' χ := by
  simp only [Sat, SentenceInf.realize_def, FormulaInf.realize_def]
  exact χ.realize_congr_of_eqOn_constantSupport h _ _

private theorem val_congr {e e' : ℕ → M} {t : L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (h : Set.EqOn e e' t.constantSupport) : val e t = val e' t :=
  t.realize_congr_of_eqOn_constantSupport h _

private theorem holds_congr {e e' : ℕ → M} {ψ : L[[ℕ]].BoundedFormulaω Empty 1} {m : M}
    (h : Set.EqOn e e' ψ.constantSupport) : Holds e ψ m ↔ Holds e' ψ m :=
  ψ.realize_congr_of_eqOn_constantSupport h _ _

private theorem sat_not {e : ℕ → M} {χ : L[[ℕ]].Sentenceω} : Sat e χ.not ↔ ¬Sat e χ := by
  let := constantsOn.structure e
  exact SentenceInf.realize_not

private theorem not_sat_bot {e : ℕ → M} : ¬Sat e (⊥ : L[[ℕ]].Sentenceω) := by
  let := constantsOn.structure e
  exact SentenceInf.realize_bot.1

private theorem sat_imp {e : ℕ → M} {χ ξ : L[[ℕ]].Sentenceω} :
    Sat e (χ.imp ξ) ↔ (Sat e χ → Sat e ξ) := by
  simp only [Sat, SentenceInf.realize_def, FormulaInf.realize_def, realize_imp]

private theorem sat_iInf {e : ℕ → M} {χs : ℕ → L[[ℕ]].Sentenceω} :
    Sat e (BoundedFormulaInf.iInf χs) ↔ ∀ k, Sat e (χs k) := by
  let := constantsOn.structure e
  exact SentenceInf.realize_iInf

private theorem sat_iSup {e : ℕ → M} {χs : ℕ → L[[ℕ]].Sentenceω} :
    Sat e (BoundedFormulaInf.iSup χs) ↔ ∃ k, Sat e (χs k) := by
  let := constantsOn.structure e
  exact SentenceInf.realize_iSup

private theorem sat_equal {e : ℕ → M} {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} :
    Sat e (equal t t') ↔ val e t = val e t' := by
  simp only [Sat, val, SentenceInf.realize_def, FormulaInf.realize_def, realize_equal]

private theorem sat_all {e : ℕ → M} {ψ : L[[ℕ]].BoundedFormulaω Empty 1} :
    Sat e ψ.all ↔ ∀ m, Holds e ψ m := by
  simp only [Sat, Holds, SentenceInf.realize_def, FormulaInf.realize_def, realize_all,
    Fin.snoc_zero]

private theorem sat_inst {e : ℕ → M} {ψ : L[[ℕ]].BoundedFormulaω Empty 1}
    {t : L[[ℕ]].Term (Empty ⊕ Fin 0)} : Sat e (ψ.inst t) ↔ Holds e ψ (val e t) := by
  simp only [Sat, Holds, val, SentenceInf.realize_def, realize_inst]

private theorem val_con (e : ℕ → M) (c : ℕ) : val e (L.con c).term = e c := by
  let := constantsOn.structure e
  exact Term.realize_constants

private theorem sat_onBoundedFormulaInf {e : ℕ → M} {φ : L.Sentenceω} :
    Sat e ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ) ↔ SentenceInf.Realize φ M := by
  let := constantsOn.structure e
  simp only [Sat, SentenceInf.realize_def, FormulaInf.realize_def]
  exact (L.lhomWithConstants ℕ).realize_onBoundedFormulaInf φ _ _

end Sat

/-! ### Rational constants and gaps -/

/-- The Henkin constant naming a rational. These are the even constants, so the odd constants
remain free to serve as witnesses. -/
private def ratCon (q : ℚ) : ℕ := 2 * Encodable.encode q

private theorem ratCon_injective : Function.Injective ratCon := fun _ _ h =>
  Encodable.encode_injective (by simpa [ratCon] using h)

/-- The rationals named by the constants in a finite set. -/
private noncomputable def ratsIn {S : Set ℕ} (hS : S.Finite) : Finset ℚ :=
  (hS.preimage ratCon_injective.injOn).toFinset

private theorem mem_ratsIn {S : Set ℕ} {hS : S.Finite} {q : ℚ} : q ∈ ratsIn hS ↔ ratCon q ∈ S :=
  Set.Finite.mem_toFinset _

/-- The positions `x q`, for `q ∈ Q`, follow the order of `Q` inside the ordinal `γ`, with
gaps of length more than `α` between consecutive positions and before the first and after the
last. -/
private structure Gapped (Q : Finset ℚ) (x : ℚ → Ordinal.{w}) (γ α : Ordinal.{w}) : Prop where
  lt_top : α < γ
  lt_position {q : ℚ} : q ∈ Q → α < x q
  add_lt_top {q : ℚ} : q ∈ Q → x q + α < γ
  add_lt_position {q r : ℚ} : q ∈ Q → r ∈ Q → q < r → x q + α < x r

namespace Gapped

variable {Q : Finset ℚ} {x : ℚ → Ordinal.{w}} {γ α β : Ordinal.{w}}

/-- The gap condition is downward closed in `α`. -/
private theorem mono (h : Gapped Q x γ β) (hαβ : α ≤ β) : Gapped Q x γ α where
  lt_top := hαβ.trans_lt h.lt_top
  lt_position hq := hαβ.trans_lt (h.lt_position hq)
  add_lt_top hq := lt_of_le_of_lt (by gcongr) (h.add_lt_top hq)
  add_lt_position hq hr hqr := lt_of_le_of_lt (by gcongr) (h.add_lt_position hq hr hqr)

/-- A new rational can be placed inside a gap of length more than `α + 1 + α`: just after the
positions of the smaller rationals, leaving gaps of length more than `α` on both sides. -/
private theorem insert (h : Gapped Q x γ (α + 1 + α)) (s : ℚ) :
    Gapped (insert s Q) (Function.update x s ((Q.filter (· < s)).sup x + α + 1)) γ α := by
  classical
  set lo := (Q.filter (· < s)).sup x
  have hsup {p : Ordinal.{w} → Prop} (h0 : p 0) (hp : ∀ a, p a → ∀ b, p b → p (a ⊔ b))
      (hx : ∀ q ∈ Q, q < s → p (x q)) : p lo :=
    Finset.sup_induction h0 hp fun q hq =>
      hx q (Finset.mem_filter.1 hq).1 (Finset.mem_filter.1 hq).2
  have hmax {c : Ordinal.{w}} : ∀ a, a + (α + 1 + α) < c → ∀ b, b + (α + 1 + α) < c →
      (a ⊔ b) + (α + 1 + α) < c := fun a ha b hb => by
    obtain h | h := le_total a b
    · rwa [sup_eq_right.2 h]
    · rwa [sup_eq_left.2 h]
  have hβ : α ≤ α + 1 + α := le_add_self
  have hlt_top : lo + (α + 1 + α) < γ :=
    hsup (by simpa using h.lt_top) hmax fun q hq _ => h.add_lt_top hq
  have hlt_pos {r : ℚ} (hr : r ∈ Q) (hsr : s < r) : lo + (α + 1 + α) < x r :=
    hsup (by simpa using h.lt_position hr) hmax
      fun q hq hqs => h.add_lt_position hq hr (hqs.trans hsr)
  have hy : lo + α + 1 + α = lo + (α + 1 + α) := by simp only [add_assoc]
  have hle (q : ℚ) (hq : q ∈ Q) (hqs : q < s) : x q ≤ lo :=
    Finset.le_sup (f := x) (Finset.mem_filter.2 ⟨hq, hqs⟩)
  refine ⟨hβ.trans_lt h.lt_top, fun {q} hq => ?_, fun {q} hq => ?_, fun {q r} hq hr hqr => ?_⟩
  · by_cases hqs : q = s
    · subst hqs
      rw [Function.update_self]
      exact (le_add_self : α ≤ lo + α).trans_lt (by simp)
    · rw [Function.update_of_ne hqs]
      exact hβ.trans_lt (h.lt_position ((Finset.mem_insert.1 hq).resolve_left hqs))
  · by_cases hqs : q = s
    · subst hqs
      rwa [Function.update_self, hy]
    · rw [Function.update_of_ne hqs]
      exact (h.mono hβ).add_lt_top ((Finset.mem_insert.1 hq).resolve_left hqs)
  · by_cases hqs : q = s
    · subst hqs
      have hrs : r ≠ q := hqr.ne'
      rw [Function.update_self, Function.update_of_ne hrs, hy]
      exact hlt_pos ((Finset.mem_insert.1 hr).resolve_left hrs) hqr
    · have hq' := (Finset.mem_insert.1 hq).resolve_left hqs
      rw [Function.update_of_ne hqs]
      by_cases hrs : r = s
      · subst hrs
        rw [Function.update_self]
        have hqlo := hle q hq' hqr
        have hle' : x q + α ≤ lo + α := by gcongr
        exact hle'.trans_lt (by simp)
      · rw [Function.update_of_ne hrs]
        exact (h.mono hβ).add_lt_position hq' ((Finset.mem_insert.1 hr).resolve_left hrs) hqr

end Gapped

/-! ### The consistency property -/

variable (φ : L.Sentenceω) (lt : L.Relations 2)

/-- The sentence `lt(c, d)` of `L[[ℕ]]`. -/
private def ltSentence (c d : ℕ) : L[[ℕ]].Sentenceω :=
  .rel ((L.lhomWithConstants ℕ).onRelation lt) ![(L.con c).term, (L.con d).term]

private theorem constantSupport_ltSentence (c d : ℕ) :
    (ltSentence lt c d).constantSupport = {c, d} := by
  ext a
  rw [ltSentence, constantSupport_rel]
  simp [Fin.exists_fin_two]

private theorem realize_ltSentence {M : Type w} [L[[ℕ]].Structure M] (c d : ℕ) :
    SentenceInf.Realize (ltSentence lt c d) M ↔
      RelMap ((L.lhomWithConstants ℕ).onRelation lt) ![(L.con c : M), (L.con d : M)] := by
  have hv : (fun i => (![(L.con c).term, (L.con d).term] i : L[[ℕ]].Term (Empty ⊕ Fin 0)).realize
      (Sum.elim Empty.elim (default : Fin 0 → M))) = ![(L.con c : M), (L.con d : M)] := by
    funext i
    match i with
    | 0 => simp
    | 1 => simp
  simp only [ltSentence, SentenceInf.realize_def, FormulaInf.realize_def, realize_rel, hv]

/-- The sentences common to every member: `φ`, and `d_q < d_r` for all rationals `q < r`. -/
private def base : L[[ℕ]].Theoryω :=
  insert ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ)
    {χ | ∃ q r : ℚ, q < r ∧ χ = ltSentence lt (ratCon q) (ratCon r)}

/-- The expansion of `M` by `e` satisfies `σ`, and a well-ordered chain of `M` carries the rational
constants of `Q` with gaps of length more than `α`. -/
private def Witness (Q : Finset ℚ) (σ : L[[ℕ]].Theoryω) (α : Ordinal.{w}) (M : Type w)
    [L.Structure M] (e : ℕ → M) : Prop :=
  SentenceInf.Realize φ M ∧ (∀ χ ∈ σ, Sat e χ) ∧
    ∃ (g : Ordinal.{w} → M) (x : ℚ → Ordinal.{w}) (γ : Ordinal.{w}),
      (∀ a b, a < b → b < γ → RelMap lt ![g a, g b]) ∧ Gapped Q x γ α ∧
        ∀ q ∈ Q, e (ratCon q) = g (x q)

/-- The pairs `(Q, σ)` defining the members: `σ` is a finite set of sentences mentioning finitely
many constants, with its rational constants in `Q`, and it has witnesses for every countable
ordinal. -/
private structure Member (Q : Finset ℚ) (σ : L[[ℕ]].Theoryω) : Prop where
  finite : σ.Finite
  finite_constantSupport : ∀ χ ∈ σ, χ.constantSupport.Finite
  mem_of_ratCon_mem : ∀ χ ∈ σ, ∀ q, ratCon q ∈ χ.constantSupport → q ∈ Q
  exists_witness : ∀ α : Ordinal.{w}, α < ω₁ → ∃ (M : Type w) (_ : L.Structure M) (e : ℕ → M),
    Witness φ lt Q σ α M e

/-- The family of members. -/
private def chainSets : Set L[[ℕ]].Theoryω :=
  {s | ∃ (Q : Finset ℚ) (σ : L[[ℕ]].Theoryω), Member.{u, v, w} φ lt Q σ ∧ s = base φ lt ∪ σ}

variable {φ lt}

section Witness

variable {Q : Finset ℚ} {σ : L[[ℕ]].Theoryω} {α β : Ordinal.{w}} {M : Type w} [L.Structure M]
  {e : ℕ → M}

private theorem Witness.mono (h : Witness φ lt Q σ β M e) (hαβ : α ≤ β) :
    Witness φ lt Q σ α M e := by
  obtain ⟨hφ, hσ, g, x, γ, hg, hx, he⟩ := h
  exact ⟨hφ, hσ, g, x, γ, hg, hx.mono hαβ, he⟩

/-- Witnesses survive reinterpreting a constant that is not a rational of `Q` and does not occur
in `σ`. -/
private theorem Witness.update (h : Witness φ lt Q σ α M e) {c : ℕ}
    (hσ : ∀ χ ∈ σ, c ∉ χ.constantSupport) (hQ : ∀ q ∈ Q, c ≠ ratCon q) (m : M) :
    Witness φ lt Q σ α M (Function.update e c m) := by
  obtain ⟨hφ, hsat, g, x, γ, hg, hx, he⟩ := h
  refine ⟨hφ, fun χ hχ => (sat_congr fun d hd => ?_).1 (hsat χ hχ), g, x, γ, hg, hx,
    fun q hq => ?_⟩
  · rw [Function.update_of_ne (ne_of_mem_of_not_mem hd (hσ χ hχ))]
  · rw [Function.update_of_ne (hQ q hq).symm, he q hq]

/-- A sentence of a member holds in a witness as soon as its rational constants lie in `Q`. -/
private theorem Witness.sat_of_mem (h : Witness φ lt Q σ α M e) {P : L[[ℕ]].Sentenceω}
    (hP : P ∈ base φ lt ∪ σ) (hQ : ∀ q, ratCon q ∈ P.constantSupport → q ∈ Q) : Sat e P := by
  obtain ⟨hφ, hσ, g, x, γ, hg, hx, he⟩ := h
  obtain (rfl | ⟨q, r, hqr, rfl⟩) | hP := hP
  · exact sat_onBoundedFormulaInf.2 hφ
  · have hq := hQ q (by simp [constantSupport_ltSentence])
    have hr := hQ r (by simp [constantSupport_ltSentence])
    have hlt := hg (x q) (x r) (le_self_add.trans_lt (hx.add_lt_position hq hr hqr))
      (le_self_add.trans_lt (hx.add_lt_top hr))
    rw [← he q hq, ← he r hr] at hlt
    let := constantsOn.structure e
    exact (realize_ltSentence lt _ _).2 (((L.lhomWithConstants ℕ).map_onRelation lt _).mpr hlt)
  · exact hσ P hP

end Witness

namespace Member

variable {Q : Finset ℚ} {σ : L[[ℕ]].Theoryω}

private theorem insert_rat (h : Member.{u, v, w} φ lt Q σ) (s : ℚ) :
    Member.{u, v, w} φ lt (insert s Q) σ := by
  classical
  refine ⟨h.finite, h.finite_constantSupport,
    fun χ hχ q hq => Finset.mem_insert_of_mem (h.mem_of_ratCon_mem χ hχ q hq), fun α hα => ?_⟩
  by_cases hs : s ∈ Q
  · rw [Finset.insert_eq_of_mem hs]
    exact h.exists_witness α hα
  obtain ⟨M, _, e, hφ, hsat, g, x, γ, hg, hx, he⟩ :=
    h.exists_witness _ (isPrincipal_add_omega 1
      ((Cardinal.isSuccLimit_omega 1).add_one_lt hα) hα)
  refine ⟨M, inferInstance,
    Function.update e (ratCon s) (g ((Q.filter (· < s)).sup x + α + 1)), hφ,
    fun χ hχ => (sat_congr fun d hd => ?_).1 (hsat χ hχ), g, _, γ, hg, hx.insert s,
    fun q hq => ?_⟩
  · rw [Function.update_of_ne]
    rintro rfl
    exact hs (h.mem_of_ratCon_mem χ hχ s hd)
  · by_cases hqs : q = s
    · subst hqs
      simp
    · rw [Function.update_of_ne (ratCon_injective.ne hqs),
        Function.update_of_ne hqs, he q ((Finset.mem_insert.1 hq).resolve_left hqs)]

private theorem union (h : Member.{u, v, w} φ lt Q σ) (R : Finset ℚ) :
    Member.{u, v, w} φ lt (Q ∪ R) σ := by
  classical
  induction R using Finset.induction_on with
  | empty => simpa
  | insert s R _ ih => simpa using ih.insert_rat s

private theorem finite_constantSupport_of_mem (h : Member.{u, v, w} φ lt Q σ)
    {P : L[[ℕ]].Sentenceω} (hP : P ∈ base φ lt ∪ σ) : P.constantSupport.Finite := by
  obtain (rfl | ⟨q, r, -, rfl⟩) | hP := hP
  · simp
  · simp [constantSupport_ltSentence]
  · exact h.finite_constantSupport P hP

/-- There is a constant occurring neither in `σ` nor in a given finite set, and naming no
rational. -/
private theorem exists_fresh (h : Member.{u, v, w} φ lt Q σ) {F : Set ℕ} (hF : F.Finite) :
    ∃ c, c ∉ F ∧ (∀ χ ∈ σ, c ∉ χ.constantSupport) ∧ ∀ q, c ≠ ratCon q := by
  obtain ⟨b, hb⟩ := (hF.union (h.finite.biUnion h.finite_constantSupport)).bddAbove
  refine ⟨2 * b + 1, fun hc => ?_, fun χ hχ hc => ?_, fun q hq => ?_⟩
  · have := hb (Or.inl hc)
    omega
  · have := hb (Or.inr (Set.mem_biUnion hχ hc))
    omega
  · simp only [ratCon] at hq
    omega

/-- Some witness satisfies every sentence of a member with its constants in a finite set `S`. -/
private theorem exists_sat (h : Member.{u, v, w} φ lt Q σ) {S : Set ℕ} (hS : S.Finite) :
    ∃ (M : Type w) (_ : L.Structure M) (e : ℕ → M),
      ∀ P ∈ base φ lt ∪ σ, P.constantSupport ⊆ S → Sat e P := by
  obtain ⟨M, _, e, hW⟩ := (h.union (ratsIn hS)).exists_witness 0 (omega_pos 1)
  exact ⟨M, inferInstance, e, fun P hP hPS =>
    hW.sat_of_mem hP fun q hq => Finset.mem_union_right _ (mem_ratsIn.2 (hPS hq))⟩

/-- **The general extension step.** Let the constants of the countably many sentences `ξ k` lie in
a finite set `S`. If every witness for `(Q, σ)`, with `Q` enlarged by the rationals named in `S`,
can be made to satisfy some `ξ k`, then adding a suitable `ξ k` gives a member. Countably many
sentences suffice because `ω₁` is regular. -/
private theorem exists_insert_mem (h : Member.{u, v, w} φ lt Q σ) {κ : Type} [Countable κ]
    {S : Set ℕ} (hS : S.Finite) (ξ : κ → L[[ℕ]].Sentenceω)
    (hξ : ∀ k, (ξ k).constantSupport ⊆ S)
    (hw : ∀ (Q' : Finset ℚ) (α : Ordinal.{w}) (M : Type w) [L.Structure M] (e : ℕ → M),
      Witness φ lt Q' σ α M e → (∀ P ∈ base φ lt ∪ σ, P.constantSupport ⊆ S → Sat e P) →
        ∃ k e', Witness φ lt Q' σ α M e' ∧ Sat e' (ξ k)) :
    ∃ k, insert (ξ k) (base φ lt ∪ σ) ∈ chainSets.{u, v, w} φ lt := by
  classical
  have hm := h.union (ratsIn hS)
  by_contra hcon
  have hbad (k : κ) : ∃ α : Ordinal.{w}, α < ω₁ ∧ ¬∃ (M : Type w) (_ : L.Structure M) (e : ℕ → M),
      Witness φ lt (Q ∪ ratsIn hS) (insert (ξ k) σ) α M e := by
    by_contra hall
    push Not at hall
    refine hcon ⟨k, Q ∪ ratsIn hS, insert (ξ k) σ, ⟨hm.finite.insert _, ?_, ?_, ?_⟩,
      (Set.union_insert ..).symm⟩
    · rintro χ (rfl | hχ)
      · exact hS.subset (hξ k)
      · exact hm.finite_constantSupport χ hχ
    · rintro χ (rfl | hχ) q hq
      · exact Finset.mem_union_right _ (mem_ratsIn.2 (hξ k hq))
      · exact hm.mem_of_ratCon_mem χ hχ q hq
    · exact hall
  choose a ha hna using hbad
  obtain ⟨M, _, e, hW⟩ := hm.exists_witness (⨆ k, a k) (iSup_lt_omega_one ha)
  obtain ⟨k, e', hW', hsat⟩ := hw _ _ M e hW fun P hP hPS =>
    hW.sat_of_mem hP fun q hq => Finset.mem_union_right _ (mem_ratsIn.2 (hPS hq))
  refine hna k ⟨M, inferInstance, e', ?_⟩
  obtain ⟨hφ, hσ, hrest⟩ := hW'.mono (le_ciSup (f := a) bddAbove_of_small k)
  refine ⟨hφ, ?_, hrest⟩
  rintro χ (rfl | hχ)
  · exact hsat
  · exact hσ χ hχ

/-- The extension step for a single sentence. -/
private theorem insert_mem (h : Member.{u, v, w} φ lt Q σ) {S : Set ℕ} (hS : S.Finite)
    (ξ : L[[ℕ]].Sentenceω) (hξ : ξ.constantSupport ⊆ S)
    (hw : ∀ (Q' : Finset ℚ) (α : Ordinal.{w}) (M : Type w) [L.Structure M] (e : ℕ → M),
      Witness φ lt Q' σ α M e → (∀ P ∈ base φ lt ∪ σ, P.constantSupport ⊆ S → Sat e P) →
        ∃ e', Witness φ lt Q' σ α M e' ∧ Sat e' ξ) :
    insert ξ (base φ lt ∪ σ) ∈ chainSets.{u, v, w} φ lt := by
  obtain ⟨-, hk⟩ := h.exists_insert_mem hS (fun _ : Unit => ξ) (fun _ => hξ) fun Q' α M _ e hW hP =>
    (hw Q' α M e hW hP).elim fun e' he' => ⟨(), e', he'⟩
  exact hk

end Member

variable (φ lt) in
/-- **Marker's consistency property**: its members are the sets `base φ lt ∪ σ` for the pairs
`(Q, σ)` of `Member`. -/
private noncomputable def chainProperty : ConsistencyProperty L where
  sets := chainSets.{u, v, w} φ lt
  no_falsum := by
    rintro _ ⟨Q, σ, hm, rfl⟩ hbot
    obtain ⟨M, _, e, he⟩ := hm.exists_sat Set.finite_empty
    exact not_sat_bot (he _ hbot (by simp))
  no_contradiction := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χ h h'
    obtain ⟨M, _, e, he⟩ := hm.exists_sat (hm.finite_constantSupport_of_mem h)
    exact sat_not.1 (he _ h' (by simp)) (he _ h subset_rfl)
  imp := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χ ξ h
    obtain ⟨b, hb⟩ := hm.exists_insert_mem (hm.finite_constantSupport_of_mem h)
      (fun b : Bool => bif b then χ.not else ξ) (by rintro (_ | _) <;> simp)
      fun Q' α M _ e hW hP => by
        by_cases hχ : Sat e χ
        · exact ⟨false, e, hW, sat_imp.1 (hP _ h subset_rfl) hχ⟩
        · exact ⟨true, e, hW, sat_not.2 hχ⟩
    cases b
    · exact .inr hb
    · exact .inl hb
  not_imp := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χ ξ h
    have hS := hm.finite_constantSupport_of_mem h
    have hsat {M : Type w} [L.Structure M] {e : ℕ → M}
        (hP : ∀ P ∈ base φ lt ∪ σ, P.constantSupport ⊆ (χ.imp ξ).not.constantSupport → Sat e P) :
        ¬(Sat e χ → Sat e ξ) := fun hn => sat_not.1 (hP _ h subset_rfl) (sat_imp.2 hn)
    refine ⟨hm.insert_mem hS _ (by simp) fun Q' α M _ e hW hP => ⟨e, hW, ?_⟩,
      hm.insert_mem hS _ (by simp) fun Q' α M _ e hW hP => ⟨e, hW, ?_⟩⟩
    · exact (Classical.not_imp.1 (hsat hP)).1
    · exact sat_not.2 (Classical.not_imp.1 (hsat hP)).2
  iInf := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χs h k
    refine hm.insert_mem (hm.finite_constantSupport_of_mem h) _
      (by simpa using Set.subset_iUnion (fun i => (χs i).constantSupport) k)
      fun Q' α M _ e hW hP => ⟨e, hW, sat_iInf.1 (hP _ h subset_rfl) k⟩
  not_iInf := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χs h
    refine hm.exists_insert_mem (hm.finite_constantSupport_of_mem h) (fun k => (χs k).not)
      (fun k => by simpa using Set.subset_iUnion (fun i => (χs i).constantSupport) k)
      fun Q' α M _ e hW hP => ?_
    obtain ⟨k, hk⟩ := not_forall.1 (mt sat_iInf.2 (sat_not.1 (hP _ h subset_rfl)))
    exact ⟨k, e, hW, sat_not.2 hk⟩
  iSup := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χs h
    refine hm.exists_insert_mem (hm.finite_constantSupport_of_mem h) χs
      (fun k => by simpa using Set.subset_iUnion (fun i => (χs i).constantSupport) k)
      fun Q' α M _ e hW hP => ?_
    obtain ⟨k, hk⟩ := sat_iSup.1 (hP _ h subset_rfl)
    exact ⟨k, e, hW, hk⟩
  not_iSup := by
    rintro _ ⟨Q, σ, hm, rfl⟩ χs h k
    refine hm.insert_mem (hm.finite_constantSupport_of_mem h) _
      (by simpa using Set.subset_iUnion (fun i => (χs i).constantSupport) k)
      fun Q' α M _ e hW hP =>
        ⟨e, hW, sat_not.2 fun hk => sat_not.1 (hP _ h subset_rfl) (sat_iSup.2 ⟨k, hk⟩)⟩
  all := by
    rintro _ ⟨Q, σ, hm, rfl⟩ ψ h c
    have hS := hm.finite_constantSupport_of_mem h
    refine hm.insert_mem (hS.insert c) _ ?_ fun Q' α M _ e hW hP =>
      ⟨e, hW, sat_inst.2 (sat_all.1 (hP _ h (Set.subset_insert _ _)) _)⟩
    refine (constantSupport_inst_subset _ _).trans ?_
    simp [Set.union_comm]
  not_all := by
    rintro _ ⟨Q, σ, hm, rfl⟩ ψ h
    have hS := hm.finite_constantSupport_of_mem h
    obtain ⟨c, hcS, hcσ, hcq⟩ := hm.exists_fresh hS
    rw [constantSupport_not, constantSupport_all] at hS hcS
    refine ⟨c, hm.insert_mem (hS.insert c) _ ?_ fun Q' α M _ e hW hP => ?_⟩
    · rw [constantSupport_not]
      refine (constantSupport_inst_subset _ _).trans ?_
      simp [Set.union_comm]
    · obtain ⟨m, hm'⟩ := not_forall.1 (mt sat_all.2 (sat_not.1 (hP _ h (by simp))))
      refine ⟨Function.update e c m, hW.update hcσ (fun q _ => hcq q) m, sat_not.2 fun hsat => ?_⟩
      rw [sat_inst, val_con, Function.update_self] at hsat
      exact hm' ((holds_congr (Set.eqOn_update_of_notMem hcS m)).2 hsat)
  eq_refl := by
    rintro _ ⟨Q, σ, hm, rfl⟩ t
    exact hm.insert_mem t.finite_constantSupport _ (by simp)
      fun Q' α M _ e hW _ => ⟨e, hW, sat_equal.2 rfl⟩
  eq_subst := by
    rintro _ ⟨Q, σ, hm, rfl⟩ t t' ψ _ ht hψ
    refine hm.insert_mem ((hm.finite_constantSupport_of_mem ht).union
      (hm.finite_constantSupport_of_mem hψ)) _ ?_ fun Q' α M _ e hW hP => ⟨e, hW, ?_⟩
    · refine (constantSupport_inst_subset _ _).trans (Set.union_subset
        ((constantSupport_subset_inst _ t).trans Set.subset_union_right) ?_)
      exact Set.subset_union_of_subset_left (by simp) _
    · have heq := sat_equal.1 (hP _ ht Set.subset_union_left)
      exact sat_inst.2 (heq ▸ sat_inst.1 (hP _ hψ Set.subset_union_right))
  eq_name := by
    rintro _ ⟨Q, σ, hm, rfl⟩ t
    have hS := t.finite_constantSupport
    obtain ⟨c, hcS, hcσ, hcq⟩ := hm.exists_fresh hS
    refine ⟨c, hm.insert_mem (hS.insert c) _ (by simp) fun Q' α M _ e hW _ =>
      ⟨Function.update e c (val e t), hW.update hcσ (fun q _ => hcq q) _, sat_equal.2 ?_⟩⟩
    rw [val_con, Function.update_self]
    exact val_congr (Set.eqOn_update_of_notMem hcS _)

private theorem member_empty (h : HasWellOrderedChains.{u, v, w} φ lt) :
    Member.{u, v, w} φ lt ∅ ∅ := by
  refine ⟨Set.finite_empty, by simp, by simp, fun α hα => ?_⟩
  obtain ⟨M, _, ⟨m⟩, hφ, f, hf⟩ := h (α + 1) ((Cardinal.isSuccLimit_omega 1).add_one_lt hα)
  refine ⟨M, inferInstance, fun _ => m, hφ, by simp,
    fun a => if ha : a < α + 1 then f (ToType.mk ⟨a, ha⟩) else m, 0, α + 1, fun a b hab hb => ?_,
    ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
  simp only [hb, hab.trans hb, ↓reduceDIte]
  exact hf _ _ (ToType.mk.strictMono hab)

private theorem countable_base : (base φ lt).Countable := by
  refine ((Set.countable_range fun p : ℚ × ℚ =>
    ltSentence lt (ratCon p.1) (ratCon p.2)).mono ?_).insert _
  rintro _ ⟨q, r, -, rfl⟩
  exact ⟨(q, r), rfl⟩

/-- The countable case of `exists_model_relChain_rat`, where model existence applies directly. -/
private theorem exists_model_relChain_rat_of_countable [Countable (Σ n, L.Functions n)]
    [Countable (Σ n, L.Relations n)] (h : HasWellOrderedChains.{u, v, w} φ lt) :
    ∃ (M : Type w') (_ : L.Structure M), Nonempty M ∧ Countable M ∧ SentenceInf.Realize φ M ∧
      ∃ f : ℚ → M, RelChain lt f := by
  obtain ⟨N, _, hc, hne, hN, -⟩ := (chainProperty.{u, v, w} φ lt).model_existence.{u, v, w'}
    (s := base φ lt) ⟨∅, ∅, member_empty h, by simp⟩ countable_base
  let := (L.lhomWithConstants ℕ).reduct N
  refine ⟨N, inferInstance, hne, hc, ?_, fun q => (L.con (ratCon q) : N), fun q r hqr => ?_⟩
  · simpa only [SentenceInf.realize_def, FormulaInf.realize_def,
      (L.lhomWithConstants ℕ).realize_onBoundedFormulaInf] using
      Theoryω.Model.realize_of_mem hN (Set.mem_insert _ _)
  · exact ((L.lhomWithConstants ℕ).map_onRelation lt _).mp ((realize_ltSentence lt _ _).1
      (Theoryω.Model.realize_of_mem hN (Set.mem_insert_of_mem _ ⟨q, r, hqr, rfl⟩)))

/-- **Boundedness of well-ordered chains, positive form** (Marker, 4.4.1). If models of `φ`
carry `lt`-chains of every countable length, then `φ` has a countable nonempty model, in any
universe, carrying an `lt`-chain indexed by the rationals. The language is arbitrary. -/
theorem exists_model_relChain_rat (h : HasWellOrderedChains.{u, v, w} φ lt) :
    ∃ (M : Type w') (_ : L.Structure M), Nonempty M ∧ Countable M ∧ SentenceInf.Realize φ M ∧
      ∃ f : ℚ → M, RelChain lt f := by
  classical
  let F : Set (Σ n, L.Functions n) := φ.functionsIn
  let R : Set (Σ n, L.Relations n) := insert ⟨2, lt⟩ φ.relationsIn
  have : Countable F := φ.functionsIn_countable.to_subtype
  have : Countable R := (φ.relationsIn_countable.insert _).to_subtype
  let ι := symbSublangIncl F R
  let φ₀ : (symbSublang F R).Sentenceω := φ.restrictSymbols subset_rfl (Set.subset_insert _ _)
  let lt₀ : (symbSublang F R).Relations 2 := ⟨lt, Set.mem_insert _ _⟩
  have hlt₀ : ι.onRelation lt₀ = lt := symbSublangIncl_onRelation lt₀
  have h₀ : HasWellOrderedChains.{u, v, w} φ₀ lt₀ := fun α hα => by
    obtain ⟨M, _, hne, hφ, f, hf⟩ := h α hα
    let := ι.reduct M
    refine ⟨M, inferInstance, hne, ?_, f, fun x y hxy => ?_⟩
    · simpa only [φ₀, SentenceInf.realize_def, FormulaInf.realize_def, realize_restrictSymbols]
        using hφ
    · exact (ι.map_onRelation lt₀ _).mp (hlt₀ ▸ hf x y hxy)
  obtain ⟨N, _, hne, hc, hφ, f, hf⟩ := exists_model_relChain_rat_of_countable.{u, v, w, w'} h₀
  have : Inhabited N := Classical.inhabited_of_nonempty hne
  let : L.Structure N := ι.defaultExpansion N
  have : ι.IsExpansionOn N := (symbSublangIncl_injective F R).isExpansionOn_default N
  refine ⟨N, inferInstance, hne, hc, ?_, f, fun x y hxy => ?_⟩
  · simpa only [φ₀, SentenceInf.realize_def, FormulaInf.realize_def, realize_restrictSymbols]
      using hφ
  · exact hlt₀ ▸ (ι.map_onRelation lt₀ _).mpr (hf x y hxy)

/-! ### Boundedness -/

/-- **Boundedness of chains.** If `lt` is well-founded in every nonempty model of `φ` in `Type w`,
some countable ordinal indexes an `lt`-chain in no such model. -/
theorem wellFounded_boundedness
    (hwf : ∀ (M : Type w) (_ : L.Structure M), Nonempty M → SentenceInf.Realize φ M →
      WellFounded fun x y : M => RelMap lt ![x, y]) :
    ∃ α : Ordinal.{w}, α < ω₁ ∧ ∀ (M : Type w) (_ : L.Structure M), Nonempty M →
      SentenceInf.Realize φ M → ∀ f : α.ToType → M, ¬RelChain lt f := by
  by_contra hcon
  push Not at hcon
  obtain ⟨M, _, hne, -, hφ, f, hf⟩ := exists_model_relChain_rat.{u, v, w, w}
    fun α hα => (hcon α hα).imp fun M h => h.imp fun _ h => ⟨h.1, h.2.1, h.2.2⟩
  exact hf.not_wellFounded (hwf M _ hne hφ)

/-- **Boundedness of order types** (Marker, Chapter 4). If `lt` well-orders every model of `φ` in
`Type w`, of any cardinality, then their order types are bounded by a countable ordinal. -/
theorem wellOrder_type_boundedness
    (hwo : ∀ (M : Type w) (_ : L.Structure M), SentenceInf.Realize φ M →
      IsWellOrder M fun x y : M => RelMap lt ![x, y]) :
    ∃ α : Ordinal.{w}, α < ω₁ ∧ ∀ (M : Type w) (inst : L.Structure M)
      (h : SentenceInf.Realize φ M),
        @Ordinal.type M (fun x y => RelMap lt ![x, y]) (hwo M inst h) < α := by
  obtain ⟨α, hα, hbound⟩ := wellFounded_boundedness (φ := φ) (lt := lt)
    fun M _ _ hφ => (hwo M _ hφ).wf
  refine ⟨α + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt hα, fun M _ hφ => ?_⟩
  by_contra hlt
  have := hwo M _ hφ
  have hle := not_lt.1 hlt
  have hne : Nonempty M := type_ne_zero_iff_nonempty.1 (lt_of_lt_of_le (by simp) hle).ne'
  let r : M → M → Prop := fun x y => RelMap lt ![x, y]
  have hαr : Ordinal.type (α := α.ToType) (· < ·) ≤ type r := by
    rw [Ordinal.type_toType]
    exact (Order.le_succ α).trans hle
  obtain ⟨g⟩ := Ordinal.type_le_iff'.1 hαr
  exact hbound M _ hne hφ g fun _ _ hxy => g.map_rel_iff.2 hxy

end Sentenceω

/-- The `L`-structure on an ordered type interpreting `lt` as `<`, every other relation symbol as
empty and every function symbol as the constant `m`. -/
@[instance_reducible]
private def ltStructure (lt : L.Relations 2) {M : Type w} [LT M] (m : M) : L.Structure M where
  funMap _ _ := m
  RelMap {n} R xs := match n, R, xs with
    | 2, R, xs => R = lt ∧ xs 0 < xs 1
    | _, _, _ => False

/-- **Undefinability of well-ordering.** No `L_{ω₁ω}` sentence has as its models exactly the
structures in `Type w` in which `lt` is a well-order. -/
theorem wellOrdering_undefinable (lt : L.Relations 2) :
    ¬∃ φ : L.Sentenceω, ∀ (M : Type w) (_ : L.Structure M),
      SentenceInf.Realize φ M ↔ IsWellOrder M fun x y : M => RelMap lt ![x, y] := by
  rintro ⟨φ, hφ⟩
  obtain ⟨α, -, hbound⟩ := Sentenceω.wellFounded_boundedness (φ := φ) (lt := lt)
    fun M _ _ h => ((hφ M _).1 h).wf
  -- `α + 1` is a nonempty well-order of length at least `α`
  let M := (α + 1).ToType
  have hne : Nonempty M := nonempty_toType_iff.2 (by simp)
  let := ltStructure lt (Classical.arbitrary M)
  have hrel (x y : M) : RelMap lt ![x, y] ↔ x < y := and_iff_right rfl
  have hwo : IsWellOrder M fun x y : M => RelMap lt ![x, y] := by
    simpa only [hrel] using (inferInstance : IsWellOrder M (· < ·))
  let f : α.ToType → M := fun a => ToType.mk
    ⟨(ToType.toOrd a).1, (ToType.toOrd a).2.trans_le (Order.le_succ α)⟩
  exact hbound M _ hne ((hφ M _).2 hwo) f fun x y hxy => (hrel _ _).2
    (ToType.mk.strictMono (Subtype.mk_lt_mk.2 (ToType.mk.symm.strictMono hxy)))

end FirstOrder.Language
