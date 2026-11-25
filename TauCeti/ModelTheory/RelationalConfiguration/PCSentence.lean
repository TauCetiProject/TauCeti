/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.CodedConnectives
public import TauCeti.ModelTheory.Interpolation.PCClass
public import TauCeti.ModelTheory.RelationalConfiguration.QueryCode
public import TauCeti.ModelTheory.RelationalConfiguration.Structure

/-!
# The PC sentence of a tree

Let `T` be a tree on `Bool × ℕ`. Through the query code, `T` describes the set of configurations
`c` on `ℕ` for which some `g : ℕ → ℕ` makes `n ↦ (queryCode c n, g n)` a branch of `T`; every
analytic set of configurations has this form (`exists_tree_of_analyticSet`). This file writes down
an `L_{ω₁ω}` sentence `pcSentence T` in the language `L.sum pcWitnessLanguage` such that in each
model the interpretations of `zero` and `succ` enumerate the domain by `ℕ`, and the interpretation
of `branch` is the graph of a function `g` whose pairing with the query code of the `L`-reduct,
read along that enumeration, lies in `body T`.

The witness language `pcWitnessLanguage` is relational, with a unary symbol `zero` and binary
symbols `succ` and `branch`. Writing `νₖ(x)` for the first-order numeral formula
(`ν₀(x) := zero(x)`, `νₖ₊₁(x) := ∃ y, νₖ(y) ∧ succ(y, x)`) and `χᵢ` for the sentence saying that
the `i`-th atom (decoded as by `queryCode`) holds at the numerals, `pcSentence T` is the
conjunction of:

1. `zero` has exactly one element, `succ` is the graph of an injective total function whose range
   misses `zero`, and every element satisfies some `νₖ`;
2. `branch` is the graph of a total function;
3. for every `n`, some node `s` of `T` of length `n` has, for every `i < n`, `χᵢ` true exactly
   when `(s i).1` is, and `branch` sending the `i`-th numeral to the `(s i).2`-th one.

## Main definitions

* `TauCeti.RelationalConfiguration.pcWitnessLanguage`: the relational witness vocabulary.
* `TauCeti.RelationalConfiguration.standardWitness`: the witness structure on `ℕ` of a branch
  `g`: zero `{0}`, successor `n ↦ n + 1`, branch `g`.
* `TauCeti.RelationalConfiguration.pcSentence`: the PC sentence of a tree.

## Main results

* `TauCeti.RelationalConfiguration.realize_pcSentence_iff`: a structure is a model of
  `pcSentence T` exactly when there are a bijection `e : M ≃ ℕ` sending `zero` to `0` and `succ`
  to the successor, and a `g : ℕ → ℕ` whose graph is `branch` read through `e`, such that
  `n ↦ (queryCode e.encodeVia n, g n)` is a branch of `T`.
* `TauCeti.RelationalConfiguration.pcMem_pcSentence_iff`: an `L`-structure lies in the projective
  class of `pcSentence T` along `LHom.sumInl` exactly when some enumeration `e : M ≃ ℕ` and some
  `g : ℕ → ℕ` make `n ↦ (queryCode e.encodeVia n, g n)` a branch of `T`.
* `TauCeti.RelationalConfiguration.realize_pcSentence_standardWitness` (**completeness**): if
  `n ↦ (queryCode c n, g n)` is a branch of `T`, then `ℕ` with `c.toStructure` and
  `standardWitness g` is a model of `pcSentence T`.
* `TauCeti.RelationalConfiguration.exists_mem_body_of_realize_pcSentence` (**soundness**): every
  model `M`, of any cardinality and in any universe, has a bijection `e : M ≃ ℕ` sending `zero`
  to `0` and `succ` to the successor, and some `g : ℕ → ℕ` whose graph is `branch` read through
  `e`, making `n ↦ (queryCode e.encodeVia n, g n)` a branch of `T`.

## Implementation notes

The sentence `χᵢ` reads the atom `p` decoded from `i` through its components `p.2.1` and `p.2.2`,
matched with the atom API by `Atom.eta`.

## References

* D. Marker, *Infinitary Logic*, lecture notes for Math 512, University of Illinois at Chicago,
  Fall 2013, Lemma 4.24, pp. 50–51. There the successor and the branch are function symbols and
  zero is a constant; here they are relational graphs, and the numeral axiom makes every model
  countable.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Descriptive Descriptive.Tree

namespace TauCeti.RelationalConfiguration

/-! ### The witness language -/

/-- The relation symbols of the witness vocabulary: a unary zero, the binary graph of a successor
and the binary graph of a branch. -/
inductive PCWitnessRel : ℕ → Type
  /-- The unary zero predicate. -/
  | zero : PCWitnessRel 1
  /-- The graph of the successor function. -/
  | succ : PCWitnessRel 2
  /-- The graph of the branch function. -/
  | branch : PCWitnessRel 2

/-- The relational witness vocabulary of the PC sentence of a tree. -/
abbrev pcWitnessLanguage : Language.{0, 0} :=
  ⟨fun _ => Empty, PCWitnessRel⟩

instance instIsRelationalPcWitnessLanguage : pcWitnessLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The witness vocabulary has finitely many, hence countably many, relation symbols of each
arity. -/
instance instCountableRelationsPcWitnessLanguage (n : ℕ) :
    Countable (pcWitnessLanguage.Relations n) := by
  refine Function.Injective.countable (f := fun R : PCWitnessRel n => match R with
    | .zero => (0 : Fin 3) | .succ => 1 | .branch => 2) ?_
  intro R R' h
  cases R <;> cases R' <;> first | rfl | exact absurd h (by decide)

/-- The relations of the standard witness structure on `ℕ` for a branch `g`: zero is `{0}`, the
successor graph is `n ↦ n + 1`, the branch graph is `n ↦ g n`. -/
def standardWitnessRel (g : ℕ → ℕ) : {n : ℕ} → PCWitnessRel n → (Fin n → ℕ) → Prop
  | _, .zero, v => v 0 = 0
  | _, .succ, v => v 1 = v 0 + 1
  | _, .branch, v => v 1 = g (v 0)

/-- The standard witness structure on `ℕ` for a branch `g`. -/
@[instance_reducible]
def standardWitness (g : ℕ → ℕ) : pcWitnessLanguage.Structure ℕ where
  funMap f := isEmptyElim f
  RelMap := standardWitnessRel g

/-- In the standard witness structure, `zero` holds exactly at `0`. -/
@[simp]
theorem standardWitness_relMap_zero (g : ℕ → ℕ) (v : Fin 1 → ℕ) :
    (standardWitness g).RelMap PCWitnessRel.zero v ↔ v 0 = 0 :=
  (Iff.rfl)

/-- In the standard witness structure, `succ` is the graph of `n ↦ n + 1`. -/
@[simp]
theorem standardWitness_relMap_succ (g : ℕ → ℕ) (v : Fin 2 → ℕ) :
    (standardWitness g).RelMap PCWitnessRel.succ v ↔ v 1 = v 0 + 1 :=
  (Iff.rfl)

/-- In the standard witness structure, `branch` is the graph of `g`. -/
@[simp]
theorem standardWitness_relMap_branch (g : ℕ → ℕ) (v : Fin 2 → ℕ) :
    (standardWitness g).RelMap PCWitnessRel.branch v ↔ v 1 = g (v 0) :=
  (Iff.rfl)

/-! ### Numerals -/

section Numerals

variable {M : Type w} [pcWitnessLanguage.Structure M]

/-- `IsNumeral k x`: `x` is reached from an element of `zero` by `k` steps along `succ`. -/
private inductive IsNumeral : ℕ → M → Prop
  | zero {x : M} : RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] → IsNumeral 0 x
  | succ {k : ℕ} {x y : M} : IsNumeral k y →
      RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, x] → IsNumeral (k + 1) x

private theorem isNumeral_zero_iff {x : M} :
    IsNumeral 0 x ↔ RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] :=
  ⟨fun h => by cases h; assumption, .zero⟩

private theorem isNumeral_succ_iff {k : ℕ} {x : M} :
    IsNumeral (k + 1) x ↔
      ∃ y, IsNumeral k y ∧ RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, x] :=
  ⟨fun h => by cases h with | succ hy hs => exact ⟨_, hy, hs⟩, fun ⟨_, hy, hs⟩ => .succ hy hs⟩

/-- Under the axioms on `zero` and `succ`, each `k` has at most one numeral. -/
private theorem IsNumeral.unique
    (hzero : ∀ x y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] →
      RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y] → x = y)
    (hsucc : ∀ x y z : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
      RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] → y = z)
    {k : ℕ} {x y : M} (hx : IsNumeral k x) (hy : IsNumeral k y) : x = y := by
  induction k generalizing x y with
  | zero => exact hzero x y (isNumeral_zero_iff.1 hx) (isNumeral_zero_iff.1 hy)
  | succ k ih =>
    obtain ⟨x', hx', hx⟩ := isNumeral_succ_iff.1 hx
    obtain ⟨y', hy', hy⟩ := isNumeral_succ_iff.1 hy
    obtain rfl := ih hx' hy'
    exact hsucc x' x y hx hy

/-- Under the axioms on `zero` and `succ`, an element is the numeral of at most one `k`. -/
private theorem IsNumeral.inj
    (hinj : ∀ x y z : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] →
      RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, z] → x = y)
    (hmiss : ∀ x y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
      ¬ RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y])
    {k k' : ℕ} {x : M} (hk : IsNumeral k x) (hk' : IsNumeral k' x) : k = k' := by
  induction k generalizing k' x with
  | zero =>
    cases k' with
    | zero => rfl
    | succ k' =>
      obtain ⟨y, -, hy⟩ := isNumeral_succ_iff.1 hk'
      exact (hmiss y x hy (isNumeral_zero_iff.1 hk)).elim
  | succ k ih =>
    obtain ⟨y, hy, hyx⟩ := isNumeral_succ_iff.1 hk
    cases k' with
    | zero => exact (hmiss y x hyx (isNumeral_zero_iff.1 hk')).elim
    | succ k' =>
      obtain ⟨y', hy', hyx'⟩ := isNumeral_succ_iff.1 hk'
      obtain rfl := hinj y y' x hyx hyx'
      rw [ih hy hy']

/-- Under the axioms on `zero` and `succ`, every `k` has a numeral. -/
private theorem exists_isNumeral
    (hzero : ∃ x : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x])
    (hsucc : ∀ x : M, ∃ y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y]) :
    ∀ k, ∃ x : M, IsNumeral k x
  | 0 => hzero.imp fun _ => .zero
  | k + 1 => (exists_isNumeral hzero hsucc k).elim fun y hy =>
    (hsucc y).imp fun _ => .succ hy

end Numerals

/-! ### The formulas -/

section Formulas

variable (L : Language.{u, v})

local notation "LW" => L.sum pcWitnessLanguage

/-- A witness relation applied to bound variables. -/
private def wRel {n l : ℕ} (R : PCWitnessRel l) (is : Fin l → Fin n) :
    (LW).BoundedFormulaω Empty n :=
  .rel ((LHom.sumInr : pcWitnessLanguage →ᴸ LW).onRelation R) fun j => Term.var (Sum.inr (is j))

/-- Equality of two bound variables. -/
private def eqv {n : ℕ} (i j : Fin n) : (LW).BoundedFormulaω Empty n :=
  .equal (Term.var (Sum.inr i)) (Term.var (Sum.inr j))

/-- The numeral formula `νₖ` applied to a bound variable. -/
private def numeral : ℕ → {n : ℕ} → Fin n → (LW).BoundedFormulaω Empty n
  | 0, _, i => wRel L PCWitnessRel.zero ![i]
  | k + 1, n, i =>
    (numeral k (Fin.last n) ⊓ wRel L PCWitnessRel.succ ![Fin.last n, i.castSucc]).ex

/-- `R` is the graph of a total function: `∀ x, ∃ y, R(x, y)` and `∀ x y z, R(x, y) → R(x, z) →
y = z`. -/
private def graphSentence (R : PCWitnessRel 2) : (LW).Sentenceω :=
  (wRel (n := 2) L R ![0, 1]).ex.alls ⊓
    ((wRel (n := 3) L R ![0, 1] ⊓ wRel L R ![0, 2]).imp (eqv L 1 2)).alls

/-- Clause 1 of the PC sentence: the numerals enumerate the universe without repetition. -/
private def numeralSentence : (LW).Sentenceω :=
  (wRel (n := 1) L PCWitnessRel.zero ![0]).exs ⊓
    ((wRel (n := 2) L PCWitnessRel.zero ![0] ⊓ wRel L PCWitnessRel.zero ![1]).imp
      (eqv L 0 1)).alls ⊓
    graphSentence L PCWitnessRel.succ ⊓
    ((wRel (n := 3) L PCWitnessRel.succ ![0, 2] ⊓ wRel L PCWitnessRel.succ ![1, 2]).imp
      (eqv L 0 1)).alls ⊓
    (wRel (n := 2) L PCWitnessRel.succ ![0, 1] ⊓ wRel L PCWitnessRel.zero ![1]).not.alls ⊓
    (BoundedFormulaInf.iSup fun k : ℕ => numeral L k (0 : Fin 1)).alls

variable {L}

/-- The sentence saying that `R` holds at the numerals of the entries of `a`. -/
private def relFormula {l : ℕ} (R : L.Relations l) (a : Fin l → ℕ) : (LW).Sentenceω :=
  (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin l)) (fun j => numeral L (a j) j) ⊓
    .rel ((LHom.sumInl : L →ᴸ LW).onRelation R) fun j => Term.var (Sum.inr j)).exs

/-- The sentence saying that an atom holds at the numerals of its arguments. -/
private def atomFormula (p : Atom L ℕ) : (LW).Sentenceω :=
  relFormula p.2.1 p.2.2

variable [∀ n, Countable (L.Relations n)]

variable (L) in
/-- The sentence `χᵢ`: the atom decoded from `i`, as by `queryCode`, holds at the numerals, and
`⊥` where decoding fails. -/
private noncomputable def atomSentence (i : ℕ) : (LW).Sentenceω :=
  ((@Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) i).map atomFormula).getD ⊥

variable (L) in
/-- `branch` sends the `i`-th numeral to the `j`-th one. -/
private def branchSentence (i j : ℕ) : (LW).Sentenceω :=
  (numeral L i (0 : Fin 2) ⊓ numeral L j 1 ⊓ wRel L PCWitnessRel.branch ![0, 1]).exs

variable (L) in
/-- The sentence saying that a node `s` describes the first `s.length` values of the query code and
the branch. -/
private noncomputable def nodeSentence (s : List (Bool × ℕ)) : (LW).Sentenceω :=
  BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin s.length)) fun i =>
    (if s[i].1 then atomSentence L i else (atomSentence L i).not) ⊓ branchSentence L i s[i].2

end Formulas

/-! ### Realization of the formulas -/

section Realize

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [pcWitnessLanguage.Structure M]

/-- A witness relation applied to bound variables holds when the relation holds at their values:
`wRel` is an atomic formula of the `pcWitnessLanguage` summand, realized through the sum
structure. -/
private theorem realize_wRel {n l : ℕ} (R : PCWitnessRel l) (is : Fin l → Fin n) (v : Empty → M)
    (xs : Fin n → M) :
    (wRel L R is).Realize v xs ↔ RelMap (L := pcWitnessLanguage) R (fun j => xs (is j)) := by
  simp only [wRel, BoundedFormulaInf.realize_rel, LHom.map_onRelation, Term.realize_var,
    Sum.elim_inr]

private theorem realize_wRel₁ {n : ℕ} (R : PCWitnessRel 1) (a : Fin n) (v : Empty → M)
    (xs : Fin n → M) :
    (wRel L R ![a]).Realize v xs ↔ RelMap (L := pcWitnessLanguage) R ![xs a] := by
  rw [realize_wRel]
  exact iff_of_eq (congrArg _ (funext fun j => by fin_cases j; rfl))

private theorem realize_wRel₂ {n : ℕ} (R : PCWitnessRel 2) (a b : Fin n) (v : Empty → M)
    (xs : Fin n → M) :
    (wRel L R ![a, b]).Realize v xs ↔ RelMap (L := pcWitnessLanguage) R ![xs a, xs b] := by
  rw [realize_wRel]
  exact iff_of_eq (congrArg _ (funext fun j => by fin_cases j <;> rfl))

private theorem realize_eqv {n : ℕ} (i j : Fin n) (v : Empty → M) (xs : Fin n → M) :
    (eqv L i j).Realize v xs ↔ xs i = xs j := by
  simp only [eqv, BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr]

private theorem realize_numeral (v : Empty → M) (k : ℕ) :
    ∀ {n : ℕ} (i : Fin n) (xs : Fin n → M), (numeral L k i).Realize v xs ↔ IsNumeral k (xs i) := by
  induction k with
  | zero =>
    intro n i xs
    simp [numeral, realize_wRel₁, isNumeral_zero_iff]
  | succ k ih =>
    intro n i xs
    simp [numeral, realize_wRel₂, ih, isNumeral_succ_iff]

/-- Shorthand for realization of a sentence of the witness language as a bounded formula. -/
local notation "Holds " φ => BoundedFormulaInf.Realize φ (Empty.elim : Empty → M) default

private theorem realize_graphSentence (R : PCWitnessRel 2) :
    (Holds graphSentence L R) ↔
      (∀ x : M, ∃ y : M, RelMap (L := pcWitnessLanguage) R ![x, y]) ∧
      ∀ x y z : M, RelMap (L := pcWitnessLanguage) R ![x, y] →
        RelMap (L := pcWitnessLanguage) R ![x, z] → y = z := by
  simp only [graphSentence, BoundedFormulaInf.realize_inf]
  simp [realize_wRel₂, realize_eqv, Fin.snoc]

private theorem realize_numeralSentence :
    (Holds numeralSentence L) ↔
      (∃ x : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x]) ∧
      (∀ x y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] →
        RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y] → x = y) ∧
      (∀ x : M, ∃ y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y]) ∧
      (∀ x y z : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
        RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] → y = z) ∧
      (∀ x y z : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] →
        RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, z] → x = y) ∧
      (∀ x y : M, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
        ¬ RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y]) ∧
      ∀ x : M, ∃ k, IsNumeral k x := by
  simp only [numeralSentence, BoundedFormulaInf.realize_inf, realize_graphSentence]
  simp [realize_wRel₁, realize_wRel₂, realize_eqv, Fin.snoc, realize_numeral, and_assoc]

private theorem realize_relFormula {l : ℕ} (R : L.Relations l) (a : Fin l → ℕ) :
    (Holds relFormula R a) ↔ ∃ ys : Fin l → M, (∀ j, IsNumeral (a j) (ys j)) ∧ RelMap R ys := by
  simp only [relFormula, BoundedFormulaInf.realize_exs, BoundedFormulaInf.realize_inf,
    BoundedFormulaInf.realize_iInfAlong, realize_numeral, BoundedFormulaInf.realize_rel,
    LHom.map_onRelation, Term.realize_var, Sum.elim_inr]

section Enumerated

variable [∀ n, Countable (L.Relations n)] {e : M ≃ ℕ}

private theorem realize_atomSentence (he : ∀ k (x : M), IsNumeral k x ↔ e x = k) (i : ℕ) :
    (Holds atomSentence L i) ↔ queryCode (e.encodeVia (L := L)) i = true := by
  rcases h : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) i with _ | p
  · simp [atomSentence, h, queryCode_of_decode_eq_none h]
  · simp only [atomSentence, h, Option.map_some, Option.getD_some, atomFormula]
    rw [realize_relFormula, queryCode_of_decode_eq_some h]
    conv_rhs => rw [← Atom.eta p]
    simp only [Equiv.eval_encodeVia, decide_eq_true_iff, he, ← Equiv.eq_symm_apply]
    refine ⟨fun ⟨ys, hys, hR⟩ => ?_, fun hR => ⟨_, fun _ => rfl, hR⟩⟩
    have hys' : ys = fun j => e.symm (p.2.2 j) := funext hys
    rwa [hys'] at hR

omit [∀ n, Countable (L.Relations n)] in
private theorem realize_branchSentence (he : ∀ k (x : M), IsNumeral k x ↔ e x = k)
    (i j : ℕ) :
    (Holds branchSentence L i j) ↔
      RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![e.symm i, e.symm j] := by
  simp only [branchSentence, BoundedFormulaInf.realize_exs, BoundedFormulaInf.realize_inf,
    realize_numeral, realize_wRel₂, he, ← Equiv.eq_symm_apply]
  refine ⟨fun ⟨_, ⟨h₀, h₁⟩, h⟩ => h₀ ▸ h₁ ▸ h, fun h => ⟨![e.symm i, e.symm j], ⟨rfl, rfl⟩, h⟩⟩

private theorem realize_nodeSentence (he : ∀ k (x : M), IsNumeral k x ↔ e x = k)
    (s : List (Bool × ℕ)) :
    (Holds nodeSentence L s) ↔ ∀ i (hi : i < s.length),
      queryCode (e.encodeVia (L := L)) i = s[i].1 ∧
        RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![e.symm i, e.symm s[i].2] := by
  simp only [nodeSentence, BoundedFormulaInf.realize_iInfAlong, Fin.forall_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  simp only [Fin.getElem_fin, BoundedFormulaInf.realize_inf, realize_branchSentence he]
  refine and_congr_left' ?_
  cases s[i].1 <;> simp [realize_atomSentence he]

end Enumerated

end Realize

variable {L : Language.{u, v}} [∀ n, Countable (L.Relations n)]

/-- **The PC sentence of a tree** `T` on `Bool × ℕ`: in a model, the numerals of `zero` and
`succ` enumerate the universe without repetition, `branch` is the graph of a total function `g`,
and the code read along the numerals, together with `g`, is a branch of `T`. -/
noncomputable def pcSentence (T : tree (Bool × ℕ)) : (L.sum pcWitnessLanguage).Sentenceω :=
  numeralSentence L ⊓ graphSentence L PCWitnessRel.branch ⊓
    .iInf fun n : ℕ => BoundedFormulaInf.iSupAlong
      (IndexCoding.ofEncodableWith (Encodable.ofCountable {s : List (Bool × ℕ) //
        s ∈ T ∧ s.length = n}))
      fun s => nodeSentence L s.val

/-! ### Completeness and soundness -/

section Realize

variable {M : Type w} [L.Structure M] [pcWitnessLanguage.Structure M]

private theorem realize_pcSentence_iff_clauses {T : tree (Bool × ℕ)} :
    SentenceInf.Realize (pcSentence (L := L) T) M ↔
      BoundedFormulaInf.Realize (numeralSentence L) (Empty.elim : Empty → M) default ∧
      BoundedFormulaInf.Realize (graphSentence L PCWitnessRel.branch)
        (Empty.elim : Empty → M) default ∧
      ∀ n, ∃ s, (s ∈ T ∧ s.length = n) ∧
        BoundedFormulaInf.Realize (nodeSentence L s) (Empty.elim : Empty → M) default := by
  simp only [pcSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInf,
    BoundedFormulaInf.realize_iSupAlong, and_assoc, Subtype.exists, exists_prop]

omit [∀ n, Countable (L.Relations n)] in
/-- Under the axioms of clause 1, the numerals enumerate `M` by a bijection with `ℕ`. -/
private theorem exists_equiv_isNumeral
    (h : BoundedFormulaInf.Realize (numeralSentence L) (Empty.elim : Empty → M) default) :
    ∃ e : M ≃ ℕ, ∀ k (x : M), IsNumeral k x ↔ e x = k := by
  obtain ⟨hz, hzu, hsucc, hsuccu, hinj, hmiss, hcover⟩ := realize_numeralSentence.1 h
  choose f hf using hcover
  have hbij : Function.Bijective f :=
    ⟨fun x y hxy => (hf x).unique hzu hsuccu (hxy ▸ hf y),
      fun k => (exists_isNumeral hz hsucc k).imp fun x hx => (hf x).inj hinj hmiss hx⟩
  exact ⟨.ofBijective f hbij, fun k x => ⟨fun hx => (hf x).inj hinj hmiss hx, fun h => h ▸ hf x⟩⟩

/-- **Soundness of the PC sentence.** Every model `M` of `pcSentence T`, of any cardinality and in
any universe, is countably infinite: there are a bijection `e : M ≃ ℕ` sending the `zero` of `M`
to `0` and its `succ` to the successor, and a function `g : ℕ → ℕ` whose graph is the `branch` of
`M` read through `e`, such that `n ↦ (queryCode e.encodeVia n, g n)` is a branch of `T`. -/
theorem exists_mem_body_of_realize_pcSentence {T : tree (Bool × ℕ)}
    (h : SentenceInf.Realize (pcSentence (L := L) T) M) :
    ∃ e : M ≃ ℕ, ∃ g : ℕ → ℕ,
      (∀ x, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] ↔ e x = 0) ∧
      (∀ x y, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] ↔ e y = e x + 1) ∧
      (∀ x y, RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y] ↔ e y = g (e x)) ∧
      (fun n => (queryCode (e.encodeVia (L := L)) n, g n)) ∈ body T := by
  obtain ⟨hnum, hbr, htree⟩ := realize_pcSentence_iff_clauses.1 h
  obtain ⟨e, he⟩ := exists_equiv_isNumeral hnum
  rw [realize_graphSentence] at hbr
  choose f hf using hbr.1
  have hfx (x y : M) : RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y] ↔ y = f x :=
    ⟨fun hxy => hbr.2 x y (f x) hxy (hf x), fun hy => hy ▸ hf x⟩
  refine ⟨e, fun k => e (f (e.symm k)), fun x => ?_, fun x y => ?_, fun x y => ?_,
    mem_body.2 fun n => ?_⟩
  · rw [← he 0 x, isNumeral_zero_iff]
  · rw [← he]
    refine ⟨fun hxy => .succ ((he _ x).2 rfl) hxy, fun hy => ?_⟩
    obtain ⟨x', hx', hx'y⟩ := isNumeral_succ_iff.1 hy
    obtain rfl : x' = x := e.injective ((he _ x').1 hx')
    exact hx'y
  · simp only [hfx, Equiv.symm_apply_apply, e.injective.eq_iff]
  obtain ⟨s, ⟨hsT, rfl⟩, hs⟩ := htree n
  rw [realize_nodeSentence he] at hs
  convert hsT using 1
  refine List.ext_getElem (length_initialSegment _ _) fun i hi hi' => ?_
  obtain ⟨hq, hb⟩ := hs i hi'
  simp only [initialSegment_def, List.getElem_ofFn]
  refine Prod.ext hq ?_
  simp only [← (hfx _ _).1 hb, Equiv.apply_symm_apply]

/-- **The models of the PC sentence.** A structure `M` is a model of `pcSentence T` exactly when
there are a bijection `e : M ≃ ℕ` sending the `zero` of `M` to `0` and its `succ` to the successor,
and a function `g : ℕ → ℕ` whose graph is the `branch` of `M` read through `e`, such that
`n ↦ (queryCode e.encodeVia n, g n)` is a branch of `T`. -/
theorem realize_pcSentence_iff {T : tree (Bool × ℕ)} :
    SentenceInf.Realize (pcSentence (L := L) T) M ↔
      ∃ e : M ≃ ℕ, ∃ g : ℕ → ℕ,
        (∀ x, RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] ↔ e x = 0) ∧
        (∀ x y, RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] ↔ e y = e x + 1) ∧
        (∀ x y, RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y] ↔ e y = g (e x)) ∧
        (fun n => (queryCode (e.encodeVia (L := L)) n, g n)) ∈ body T := by
  refine ⟨exists_mem_body_of_realize_pcSentence, fun ⟨e, g, hz, hs, hb, hT⟩ => ?_⟩
  have hnum : ∀ k (x : M), IsNumeral k x ↔ e x = k := by
    intro k
    induction k with
    | zero => exact fun x => isNumeral_zero_iff.trans (hz x)
    | succ k ih =>
      refine fun x => isNumeral_succ_iff.trans ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ?_⟩
      · rw [(hs y x).1 hyx, (ih y).1 hy]
      · exact ⟨e.symm k, (ih _).2 (e.apply_symm_apply k),
          (hs _ x).2 (by rw [hx, e.apply_symm_apply])⟩
  rw [realize_pcSentence_iff_clauses, realize_numeralSentence, realize_graphSentence]
  refine ⟨⟨⟨e.symm 0, (hz _).2 (e.apply_symm_apply 0)⟩,
    fun x y hx hy => e.injective (((hz x).1 hx).trans ((hz y).1 hy).symm),
    fun x => ⟨e.symm (e x + 1), (hs _ _).2 (e.apply_symm_apply _)⟩,
    fun x y z hy hz' => e.injective (((hs x y).1 hy).trans ((hs x z).1 hz').symm),
    fun x y z hx hy => e.injective
      (Nat.succ_injective (((hs x z).1 hx).symm.trans ((hs y z).1 hy))),
    fun x y hxy hy => Nat.succ_ne_zero (e x) (((hs x y).1 hxy).symm.trans ((hz y).1 hy)),
    fun x => ⟨e x, (hnum _ x).2 rfl⟩⟩,
    ⟨fun x => ⟨e.symm (g (e x)), (hb _ _).2 (e.apply_symm_apply _)⟩,
      fun x y z hy hz' => e.injective (((hb x y).1 hy).trans ((hb x z).1 hz').symm)⟩,
    fun n => ⟨initialSegment _ n, ⟨mem_body.1 hT n, length_initialSegment _ _⟩, ?_⟩⟩
  rw [realize_nodeSentence hnum]
  intro i hi
  simp only [initialSegment_def, List.getElem_ofFn]
  exact ⟨trivial, (hb _ _).2 (by simp only [Equiv.apply_symm_apply])⟩

/-- **Completeness of the PC sentence.** If `n ↦ (queryCode c n, g n)` is a branch of `T`, then
`ℕ`, with the structure decoded from `c` and the standard witness structure of `g`, is a model of
`pcSentence T`. -/
theorem realize_pcSentence_standardWitness [L.IsRelational] {T : tree (Bool × ℕ)}
    {c : RelationalConfiguration L ℕ} {g : ℕ → ℕ}
    (hcg : (fun n => (queryCode c n, g n)) ∈ body T) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentence T) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ c.toStructure (standardWitness g)) := by
  let := c.toStructure
  let := standardWitness g
  have hc : (Equiv.refl ℕ).encodeVia (L := L) = c := by
    rw [Equiv.encodeVia_refl, ofStructure_toStructure]
  refine realize_pcSentence_iff.2 ⟨Equiv.refl ℕ, g, fun x => ?_, fun x y => ?_, fun x y => ?_, ?_⟩
  · simp only [standardWitness_relMap_zero, Matrix.cons_val_zero, Equiv.refl_apply]
  · simp only [standardWitness_relMap_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Equiv.refl_apply]
  · simp only [standardWitness_relMap_branch, Matrix.cons_val_zero, Matrix.cons_val_one,
      Equiv.refl_apply]
  · rwa [hc]

omit [pcWitnessLanguage.Structure M] in
/-- **The projective class of the PC sentence.** An `L`-structure `M` lies in the projective class
of `pcSentence T` along `LHom.sumInl` exactly when some bijection `e : M ≃ ℕ` and some
`g : ℕ → ℕ` make `n ↦ (queryCode e.encodeVia n, g n)` a branch of `T`. -/
theorem pcMem_pcSentence_iff {T : tree (Bool × ℕ)} :
    (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence T) M ↔
      ∃ e : M ≃ ℕ, ∃ g : ℕ → ℕ, (fun n => (queryCode (e.encodeVia (L := L)) n, g n)) ∈ body T := by
  refine ⟨fun hM => ?_, fun ⟨e, g, hT⟩ => ?_⟩
  · obtain ⟨S, hS, h⟩ := LHom.pcMem_iff.1 hM
    let : pcWitnessLanguage.Structure M :=
      (LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M
    rw [← LHom.sumStructure_reduct_sumInr_eq (L := L) (L' := pcWitnessLanguage) M] at h
    obtain ⟨e, g, -, -, -, hT⟩ := exists_mem_body_of_realize_pcSentence h
    exact ⟨e, g, hT⟩
  · let : pcWitnessLanguage.Structure M := @Equiv.inducedStructure _ ℕ M (standardWitness g) e.symm
    refine LHom.pcMem_of_isExpansionOn (realize_pcSentence_iff.2 ⟨e, g, fun x => ?_,
      fun x y => ?_, fun x y => ?_, hT⟩)
    · simp only [Equiv.inducedStructure_RelMap, Equiv.symm_symm, standardWitness_relMap_zero,
        Function.comp_apply, Matrix.cons_val_zero]
    · simp only [Equiv.inducedStructure_RelMap, Equiv.symm_symm, standardWitness_relMap_succ,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    · simp only [Equiv.inducedStructure_RelMap, Equiv.symm_symm, standardWitness_relMap_branch,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

end Realize

end TauCeti.RelationalConfiguration
