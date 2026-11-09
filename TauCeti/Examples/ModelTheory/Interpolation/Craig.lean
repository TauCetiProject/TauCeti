/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Graph
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.ModelTheory.Infinitary.Infinite
public import TauCeti.ModelTheory.Interpolation.Craig
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Examples: relational Craig interpolation and PC separation

Downstream regression and worked examples exercising the public relational interpolation core and
the projective-class separation interface:

* **Degenerate interpolants**: when `φ` is unsatisfiable (`φ ⊨ ⊥`), `⊥` interpolates `φ ⊨ ψ` with
  empty relation support; when `ψ` is valid (`⊤ ⊨ ψ`), `⊤` interpolates `φ ⊨ ψ` with empty relation
  support; and `craig_interpolation_relational` applies in both cases.
* **Non-degenerate pure-equality interpolant**: over `Language.graph.sum Language.graph`, the
  sentence `∃ x y, x ≠ y ∧ R₁(x, y)` entails `(∃ x y, x ≠ y) ∨ ∃ x, R₂(x, x)`; relational Craig
  interpolation produces a relation-free sentence `θ` satisfied on `Bool` and refuted on `Unit`, so
  `θ` is semantically neither `⊥` nor `⊤`.
* **Parity of finite sets**: over `Language.empty`, finite sets of even cardinality form a
  projective class along `LHom.sumInl : Language.empty →ᴸ Language.empty.sum Language.graph`
  (finiteness together with the graph of a fixed-point-free involution), as do finite sets of odd
  cardinality (finiteness together with the graph of an involution with a unique fixed point).
  Their disjointness on countable nonempty carriers yields, via `pcSeparation`, a
  pure-equality sentence of `Language.empty` separating even from odd nonempty finite sets in every
  universe, and the countable disjunction `evenCardSentence` asserting "exactly `2n` elements for
  some `n`" gives an explicit such sentence.
-/

public noncomputable section

universe u v w

namespace TauCeti

open Cardinal FirstOrder FirstOrder.Language

/-! ### Degenerate interpolants -/

-- An unsatisfiable antecedent admits `⊥` as a relation-free interpolant, and
-- `craig_interpolation_relational` applies directly.
example {L : Language.{u, v}} [L.IsRelational] {φ ψ : L.Sentenceω}
    (hφ : Sentenceω.Entails φ ⊥) :
    (⊥ : L.Sentenceω).relationsIn = ∅ ∧
      Sentenceω.Entails φ ⊥ ∧
      Sentenceω.Entails (⊥ : L.Sentenceω) ψ ∧
      ∃ θ : L.Sentenceω,
        θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
          Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  have hφψ : Sentenceω.Entails φ ψ :=
    Sentenceω.entails_iff.2 fun M _ _ hM => False.elim (by
      have hbot := hφ.realize M hM
      rwa [SentenceInf.realize_bot] at hbot)
  refine ⟨BoundedFormulaInf.relationsIn_falsum, hφ, ?_, craig_interpolation_relational φ ψ hφψ⟩
  refine Sentenceω.entails_iff.2 fun M _ _ hbot => False.elim ?_
  rwa [SentenceInf.realize_bot] at hbot

-- A valid consequent admits `⊤` as a relation-free interpolant, and
-- `craig_interpolation_relational` applies directly.
example {L : Language.{u, v}} [L.IsRelational] {φ ψ : L.Sentenceω}
    (hψ : Sentenceω.Entails ⊤ ψ) :
    (⊤ : L.Sentenceω).relationsIn = ∅ ∧
      Sentenceω.Entails φ ⊤ ∧
      Sentenceω.Entails ⊤ ψ ∧
      ∃ θ : L.Sentenceω,
        θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
          Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  have hφtop : Sentenceω.Entails φ ⊤ :=
    Sentenceω.entails_iff.2 fun _ _ _ _ => by
      simp [SentenceInf.realize_def, FormulaInf.realize_def]
  have hφψ : Sentenceω.Entails φ ψ :=
    hφtop.trans hψ
  exact ⟨BoundedFormulaInf.relationsIn_top, hφtop, hψ, craig_interpolation_relational φ ψ hφψ⟩

/-! ### A non-degenerate pure-equality Craig interpolant -/

section Nondegenerate

private abbrev TwoGraph := Language.graph.sum Language.graph

private def bvar {L : Language} {n : ℕ} (i : Fin n) : L.Term (Empty ⊕ Fin n) :=
  .var (.inr i)

private def leftRel : TwoGraph.Relations 2 := .inl Language.adj

private def rightRel : TwoGraph.Relations 2 := .inr Language.adj

-- `∃ x y, x ≠ y ∧ R₁(x, y)` in `Language.graph.sum Language.graph`.
private def leftTwoElem : TwoGraph.Sentenceω :=
  BoundedFormulaInf.ex <| BoundedFormulaInf.ex <|
    (BoundedFormulaInf.equal (bvar 0) (bvar 1)).not ⊓
      BoundedFormulaInf.rel leftRel ![bvar 0, bvar 1]

-- `(∃ x y, x ≠ y) ∨ ∃ x, R₂(x, x)` in `Language.graph.sum Language.graph`.
private def rightTwoElem : TwoGraph.Sentenceω :=
  (BoundedFormulaInf.ex <| BoundedFormulaInf.ex <|
      (BoundedFormulaInf.equal (bvar 0) (bvar 1)).not) ⊔
    BoundedFormulaInf.ex (BoundedFormulaInf.rel rightRel ![bvar 0, bvar 0])

-- Relational Craig interpolation produces a sentence with empty relation support that holds on a
-- two-element structure and fails on a one-element structure.
example :
    ∃ θ : TwoGraph.Sentenceω,
      θ.relationsIn = ∅ ∧
      Sentenceω.Entails leftTwoElem θ ∧
      Sentenceω.Entails θ rightTwoElem ∧
      (∃ S₂ : TwoGraph.Structure Bool, @SentenceInf.Realize _ ℕ θ Bool S₂) ∧
      (∃ S₁ : TwoGraph.Structure Unit, ¬ @SentenceInf.Realize _ ℕ θ Unit S₁) := by
  have hent : Sentenceω.Entails leftTwoElem rightTwoElem := by
    refine Sentenceω.entails_iff.2 fun M _ _ h => ?_
    simp only [leftTwoElem, rightTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf,
      BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal, bvar, Term.realize_var,
      Sum.elim_inr] at h ⊢
    obtain ⟨x, y, hxy, -⟩ := h
    exact .inl ⟨x, y, hxy⟩
  obtain ⟨θ, hrel, h₁, h₂⟩ := craig_interpolation_relational leftTwoElem rightTwoElem hent
  have hdisj : leftTwoElem.relationsIn ∩ rightTwoElem.relationsIn = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    simp only [leftTwoElem, rightTwoElem, BoundedFormulaInf.relationsIn_ex,
      BoundedFormulaInf.relationsIn_inf, BoundedFormulaInf.relationsIn_sup,
      BoundedFormulaInf.relationsIn_not, BoundedFormulaInf.relationsIn_equal,
      BoundedFormulaInf.relationsIn_rel, Set.empty_union, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    rintro _ ⟨hL, hR⟩
    exact Sum.inl_ne_inr (eq_of_heq (Sigma.mk.inj (hL.symm.trans hR)).2)
  refine ⟨θ, Set.subset_empty_iff.1 (hdisj ▸ hrel), h₁, h₂, ?_, ?_⟩
  · let S₂ : TwoGraph.Structure Bool := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    let : TwoGraph.Structure Bool := S₂
    refine ⟨S₂, h₁.realize Bool ?_⟩
    simp only [leftTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_equal, BoundedFormulaInf.realize_rel, bvar, Term.realize_var,
      Sum.elim_inr]
    exact ⟨false, true, Bool.false_ne_true, trivial⟩
  · let S₁ : TwoGraph.Structure Unit := ⟨fun f => isEmptyElim f, fun _ _ => False⟩
    let : TwoGraph.Structure Unit := S₁
    refine ⟨S₁, fun hθ => ?_⟩
    have hr := h₂.realize Unit hθ
    simp only [rightTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_equal, BoundedFormulaInf.realize_rel, bvar, Term.realize_var,
      Sum.elim_inr] at hr
    rcases hr with ⟨_, _, hxy⟩ | ⟨_, hx⟩
    · exact hxy trivial
    · exact hx

end Nondegenerate

/-! ### Worked example: parity of finite sets via PC separation -/

namespace ParityOfFiniteSetsExample

/-- The expanded language `Language.empty.sum Language.graph` adding one binary relation symbol to
the empty language. -/
abbrev InvLang := Language.empty.sum Language.graph

private def bvar {L : Language} {n : ℕ} (i : Fin n) : L.Term (Empty ⊕ Fin n) :=
  .var (.inr i)

private abbrev invRel : InvLang.Relations 2 := .inr Language.adj

private def invAtom {n : ℕ} (i j : Fin n) : InvLang.BoundedFormulaω Empty n :=
  BoundedFormulaInf.rel invRel ![bvar i, bvar j]

@[simp]
private theorem realize_invAtom {M : Type w} [InvLang.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (invAtom i j).Realize Empty.elim xs ↔
      Structure.RelMap (L := InvLang) invRel ![xs i, xs j] := by
  rw [invAtom, BoundedFormulaInf.realize_rel]
  refine of_eq (congrArg (Structure.RelMap (L := InvLang) invRel) ?_)
  ext k; fin_cases k <;> simp [bvar]

/-- Axioms saying that the binary relation of `Language.graph` is the graph of an involution:
totality (`∀ x, ∃ y, R(x, y)`), functionality (`∀ x y z, R(x, y) → R(x, z) → y = z`), and
symmetry (`∀ x y, R(x, y) → R(y, x)`). -/
def involutionGraphSentence : InvLang.Sentenceω :=
  (BoundedFormulaInf.all (BoundedFormulaInf.ex (invAtom 0 1))) ⊓
    (BoundedFormulaInf.all <| BoundedFormulaInf.all <| BoundedFormulaInf.all <|
      (invAtom 0 1).imp ((invAtom 0 2).imp (BoundedFormulaInf.equal (bvar 1) (bvar 2)))) ⊓
    (BoundedFormulaInf.all <| BoundedFormulaInf.all <|
      (invAtom 0 1).imp (invAtom 1 0))

/-- Finiteness together with the graph of a fixed-point-free involution. -/
def evenFiniteSentence : InvLang.Sentenceω :=
  InvLang.infiniteSentence.not ⊓ involutionGraphSentence ⊓
    BoundedFormulaInf.all (invAtom 0 0).not

/-- Finiteness together with the graph of an involution having a unique fixed point. -/
def oddFiniteSentence : InvLang.Sentenceω :=
  InvLang.infiniteSentence.not ⊓ involutionGraphSentence ⊓
    BoundedFormulaInf.ex (invAtom 0 0) ⊓
    (BoundedFormulaInf.all <| BoundedFormulaInf.all <|
      (invAtom 0 0).imp ((invAtom 1 1).imp (BoundedFormulaInf.equal (bvar 0) (bvar 1))))

/-- Pure-equality sentence over `Language.empty` asserting that the carrier has size `2n` for some
natural number `n`. -/
def evenCardSentence : Language.empty.Sentenceω :=
  .iSup fun n : ℕ =>
    (Sentence.cardGe Language.empty (n + n)).toInf ⊓
      (Sentence.cardGe Language.empty (n + n + 1)).toInf.not

private theorem involutionGraphSentence_realize_iff {M : Type w} [InvLang.Structure M] :
    SentenceInf.Realize involutionGraphSentence M ↔
      (∀ x : M, ∃ y : M, Structure.RelMap (L := InvLang) invRel ![x, y]) ∧
      (∀ x y z : M,
        Structure.RelMap (L := InvLang) invRel ![x, y] →
        Structure.RelMap (L := InvLang) invRel ![x, z] → y = z) ∧
      (∀ x y : M,
        Structure.RelMap (L := InvLang) invRel ![x, y] →
        Structure.RelMap (L := InvLang) invRel ![y, x]) := by
  simp only [involutionGraphSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_ex,
    BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_equal, realize_invAtom, bvar,
    Term.realize_var, Sum.elim_inr, Fin.snoc_apply_zero, Fin.snoc_zero,
    show (1 : Fin 2) = Fin.last 1 from rfl, show (1 : Fin 3) = (Fin.last 1).castSucc from rfl,
    show (2 : Fin 3) = Fin.last 2 from rfl, Fin.snoc_castSucc, Fin.snoc_last, and_assoc]

/-- Extract an involutive permutation whose graph is `invRel` from `involutionGraphSentence`. -/
private theorem exists_perm_of_involutionGraphSentence {M : Type w} [InvLang.Structure M]
    (h : SentenceInf.Realize involutionGraphSentence M) :
    ∃ σ : Equiv.Perm M, σ ^ (2 ^ 1) = 1 ∧
      ∀ x y : M, Structure.RelMap (L := InvLang) invRel ![x, y] ↔ σ x = y := by
  obtain ⟨htot, hfun, hsym⟩ := involutionGraphSentence_realize_iff.1 h
  let f : M → M := fun x => (htot x).choose
  have hf : ∀ x, Structure.RelMap (L := InvLang) invRel ![x, f x] := fun x => (htot x).choose_spec
  have hinvf : Function.Involutive f := fun x =>
    hfun (f x) (f (f x)) x (hf (f x)) (hsym x (f x) (hf x))
  exact ⟨hinvf.toPerm, by ext x; simp [sq, hinvf x],
    fun x y => ⟨fun hxy => by simpa using hfun x (f x) y (hf x) hxy,
      fun hxy => by rw [← hxy]; simpa using hf x⟩⟩

@[instance_reducible]
private def structureOfInvolutive {M : Type w} [Language.empty.Structure M] (f : M → M) :
    InvLang.Structure M :=
  @Language.sumStructure Language.empty Language.graph M _
    { RelMap | .adj, xs => f (xs 0) = xs 1 }

@[simp]
private theorem relMap_structureOfInvolutive {M : Type w} [Language.empty.Structure M]
    (f : M → M) (xs : Fin 2 → M) :
    @Structure.RelMap InvLang M (structureOfInvolutive f) 2 invRel xs ↔ f (xs 0) = xs 1 :=
  Iff.rfl

private theorem realize_structureOfInvolutive_involution {M : Type w}
    [Language.empty.Structure M] {f : M → M} (hf : Function.Involutive f) :
    @SentenceInf.Realize _ ℕ involutionGraphSentence M (structureOfInvolutive f) := by
  let : InvLang.Structure M := structureOfInvolutive f
  rw [involutionGraphSentence_realize_iff]
  simp only [relMap_structureOfInvolutive, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun x => ⟨f x, rfl⟩, fun _ _ _ hxy hxz => hxy.symm.trans hxz,
    fun x _ hxy => by rw [← hxy, hf x]⟩

/-- Over `Language.empty`, the projective class of `evenFiniteSentence` consists of the finite
structures whose carrier has even cardinality. -/
theorem pcMem_evenFiniteSentence_iff {M : Type w} [Language.empty.Structure M] :
    LHom.PCMem LHom.sumInl evenFiniteSentence M ↔ Finite M ∧ Even (Nat.card M) := by
  rw [LHom.pcMem_iff]
  constructor
  · rintro ⟨S, -, hS⟩
    let : InvLang.Structure M := S
    obtain ⟨h₁, hlast⟩ := SentenceInf.realize_inf.1 hS
    obtain ⟨hfin0, hinv⟩ := SentenceInf.realize_inf.1 h₁
    have hfin : Finite M := not_infinite_iff_finite.1
      (by rwa [SentenceInf.realize_not, realize_infiniteSentence_iff] at hfin0)
    let : Fintype M := Fintype.ofFinite M
    obtain ⟨σ, hσ, hgraph⟩ := exists_perm_of_involutionGraphSentence hinv
    have hnofix : ∀ x : M, σ x ≠ x := by
      simpa [SentenceInf.realize_def, FormulaInf.realize_def, Fin.snoc_zero, hgraph] using hlast
    refine ⟨hfin, ?_⟩
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd]
    by_contra hndvd
    obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hndvd hσ
    exact hnofix x hx
  · rintro ⟨hfin, k, hk⟩
    let : Fintype M := Fintype.ofFinite M
    let e : M ≃ Fin k ⊕ Fin k := Fintype.equivOfCardEq <| by
      rw [← Nat.card_eq_fintype_card, hk, Fintype.card_sum, Fintype.card_fin]
    let f : M → M := fun x => e.symm ((Equiv.sumComm (Fin k) (Fin k)) (e x))
    have hnofix : ∀ x, f x ≠ x := fun x hx => by
      have hx' : (e x).swap = e x := by simpa [f] using congrArg e hx
      rcases h : e x with i | i <;> simp [h] at hx'
    let S : InvLang.Structure M := structureOfInvolutive f
    let : InvLang.Structure M := S
    refine ⟨S, ⟨fun f => isEmptyElim f, fun R => isEmptyElim R⟩, ?_⟩
    rw [evenFiniteSentence, SentenceInf.realize_inf, SentenceInf.realize_inf,
      SentenceInf.realize_not, realize_infiniteSentence_iff]
    exact ⟨⟨not_infinite_iff_finite.2 hfin,
      realize_structureOfInvolutive_involution fun x => by simp [f]⟩,
      by simp [S, SentenceInf.realize_def, FormulaInf.realize_def, Fin.snoc_zero, hnofix]⟩

/-- Over `Language.empty`, every finite structure of odd cardinality is in the projective
class of `oddFiniteSentence`: expand it by an involution with a single fixed point. -/
private theorem pcMem_oddFiniteSentence_of_odd {M : Type w} [Language.empty.Structure M]
    {k : ℕ} (hk : Nat.card M = 2 * k + 1) :
    LHom.PCMem LHom.sumInl oddFiniteSentence M := by
  rw [LHom.pcMem_iff]
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype M := Fintype.ofFinite M
  let e : M ≃ (Fin k ⊕ Fin k) ⊕ Unit := Fintype.equivOfCardEq <| by
    rw [← Nat.card_eq_fintype_card, hk, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unique, two_mul]
  let swapOdd := Equiv.sumCongr (Equiv.sumComm (Fin k) (Fin k)) (Equiv.refl Unit)
  let f : M → M := fun x => e.symm (swapOdd (e x))
  have hfix_iff : ∀ x, f x = x ↔ x = e.symm (.inr ()) := fun x =>
    ⟨fun hx => by
      have hx' : swapOdd (e x) = e x := by simpa [f] using congrArg e hx
      rcases h : e x with (i | i) | ⟨⟩
      · simp [swapOdd, h] at hx'
      · simp [swapOdd, h] at hx'
      · exact e.injective (by simpa using h),
     by rintro rfl; simp [f, swapOdd]⟩
  let S : InvLang.Structure M := structureOfInvolutive f
  let : InvLang.Structure M := S
  refine ⟨S, ⟨fun f => isEmptyElim f, fun R => isEmptyElim R⟩, ?_⟩
  rw [oddFiniteSentence, SentenceInf.realize_inf, SentenceInf.realize_inf,
    SentenceInf.realize_inf, SentenceInf.realize_not, realize_infiniteSentence_iff]
  refine ⟨⟨⟨not_infinite_iff_finite.2 hfin,
    realize_structureOfInvolutive_involution fun x => by simp [f, swapOdd]⟩, ?_⟩, ?_⟩
  · -- the `rfl` rewrites `0 : Fin 1` as `Fin.last 0`, the index form `Fin.snoc_last` expects
    simp only [S, SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_ex,
      realize_invAtom, relMap_structureOfInvolutive, Matrix.cons_val_zero, Matrix.cons_val_one,
      show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
    exact ⟨e.symm (.inr ()), (hfix_iff (e.symm (.inr ()))).2 rfl⟩
  · -- the `rfl` rewrites `1 : Fin 2` as `Fin.last 1`, the index form `Fin.snoc_last` expects
    simp only [S, SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_all,
      BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_equal, realize_invAtom, bvar,
      Term.realize_var, Sum.elim_inr, relMap_structureOfInvolutive, Matrix.cons_val_zero,
      Fin.snoc_apply_zero, Fin.snoc_zero, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    exact fun x y hx hy => ((hfix_iff x).1 hx).trans ((hfix_iff y).1 hy).symm

/-- Over `Language.empty`, the projective class of `oddFiniteSentence` consists of the finite
structures whose carrier has odd cardinality. -/
theorem pcMem_oddFiniteSentence_iff {M : Type w} [Language.empty.Structure M] :
    LHom.PCMem LHom.sumInl oddFiniteSentence M ↔ Finite M ∧ Odd (Nat.card M) := by
  constructor
  · intro h
    obtain ⟨S, -, hS⟩ := LHom.pcMem_iff.1 h
    let : InvLang.Structure M := S
    obtain ⟨h₁, huniq0⟩ := SentenceInf.realize_inf.1 hS
    obtain ⟨h₂, hex0⟩ := SentenceInf.realize_inf.1 h₁
    obtain ⟨hfin0, hinv⟩ := SentenceInf.realize_inf.1 h₂
    have hfin : Finite M := not_infinite_iff_finite.1
      (by rwa [SentenceInf.realize_not, realize_infiniteSentence_iff] at hfin0)
    let : Fintype M := Fintype.ofFinite M
    obtain ⟨σ, hσ, hgraph⟩ := exists_perm_of_involutionGraphSentence hinv
    obtain ⟨x₀, hx₀⟩ : ∃ x : M, σ x = x := by
      simpa [SentenceInf.realize_def, FormulaInf.realize_def, Fin.snoc_zero, hgraph] using hex0
    have huniqfix : ∀ x y : M, σ x = x → σ y = y → x = y := by
      simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_all,
        BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_equal, realize_invAtom, bvar,
        Term.realize_var, Sum.elim_inr, Fin.snoc_apply_zero, Fin.snoc_zero,
        show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last, hgraph] at huniq0
      exact huniq0
    refine ⟨hfin, Nat.card_eq_fintype_card (α := M) ▸ Nat.not_even_iff_odd.1
      (even_iff_two_dvd.not.2 fun hdvd => ?_)⟩
    obtain ⟨y, hy, hne⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hdvd hσ hx₀
    exact hne (huniqfix y x₀ hy hx₀)
  · rintro ⟨-, k, hk⟩
    exact pcMem_oddFiniteSentence_of_odd hk

/-- `evenCardSentence` holds in `M` exactly when `M` is finite of even cardinality. -/
theorem realize_evenCardSentence_iff (M : Type w) [Language.empty.Structure M] :
    SentenceInf.Realize evenCardSentence M ↔ Finite M ∧ Even (Nat.card M) := by
  simp only [evenCardSentence, SentenceInf.realize_iSup, SentenceInf.realize_inf,
    SentenceInf.realize_not, Sentence.realize_toInf, Sentence.realize_cardGe, not_le]
  constructor
  · rintro ⟨n, hle, hlt⟩
    have hfin : Finite M :=
      Cardinal.lt_aleph0_iff_finite.1 (hlt.trans Cardinal.natCast_lt_aleph0)
    let : Fintype M := Fintype.ofFinite M
    rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, Nat.cast_le] at hle
    rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, Nat.cast_lt] at hlt
    exact ⟨hfin, n, Nat.le_antisymm (Nat.lt_succ_iff.1 hlt) hle⟩
  · rintro ⟨hfin, n, hn⟩
    let : Fintype M := Fintype.ofFinite M
    refine ⟨n, ?_, ?_⟩
    · rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, hn, Nat.cast_le]
    · rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, hn, Nat.cast_lt]
      exact Nat.lt_succ_self (n + n)

end ParityOfFiniteSetsExample

open ParityOfFiniteSetsExample

-- By `pcSeparation`, disjointness on countable nonempty sets in `Type` produces a
-- single pure-equality sentence separating even from odd nonempty finite sets in every universe.
example :
    ∃ θ : Language.empty.Sentenceω,
      (∀ (M : Type w) [Language.empty.Structure M] [Nonempty M],
        Finite M → Even (Nat.card M) → SentenceInf.Realize θ M) ∧
      (∀ (M : Type w) [Language.empty.Structure M] [Nonempty M],
        Finite M → Odd (Nat.card M) → ¬ SentenceInf.Realize θ M) := by
  obtain ⟨θ, h₁, h₂⟩ :=
    pcSeparation.{0, 0, 0, 0, 0, 0, 0, w} evenFiniteSentence oddFiniteSentence
      (fun M _ _ _ heven hodd =>
        (Nat.not_even_iff_odd.2 (pcMem_oddFiniteSentence_iff.1 hodd).2)
          (pcMem_evenFiniteSentence_iff.1 heven).2)
  exact ⟨θ,
    fun M _ _ hfin heven => h₁ M (pcMem_evenFiniteSentence_iff.2 ⟨hfin, heven⟩),
    fun M _ _ hfin hodd => h₂ M (pcMem_oddFiniteSentence_iff.2 ⟨hfin, hodd⟩)⟩

-- Explicitly, `evenCardSentence` ("exactly `2n` elements for some `n`") separates the two
-- projective classes on all structures.
example (M : Type w) [Language.empty.Structure M] :
    (LHom.PCMem LHom.sumInl evenFiniteSentence M → SentenceInf.Realize evenCardSentence M) ∧
    (LHom.PCMem LHom.sumInl oddFiniteSentence M → ¬ SentenceInf.Realize evenCardSentence M) :=
  ⟨fun h => (realize_evenCardSentence_iff M).2 (pcMem_evenFiniteSentence_iff.1 h),
   fun h hreal => (Nat.not_even_iff_odd.2 (pcMem_oddFiniteSentence_iff.1 h).2)
     ((realize_evenCardSentence_iff M).1 hreal).2⟩

end TauCeti

end
