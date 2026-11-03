/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Evaln
public import TauCeti.Computability.Primrec.FiniteSet

/-!
# Bounded evaluation of oracle programs is primitive recursive

Bounded evaluation `TauCeti.Oracle.Single.Code.evaln σ k c n` runs the program `c` on the input
`n` with fuel `k` against the oracle answers `σ`. This file proves that the run, its output and its
use, is primitive recursive in the program, the fuel and the input, uniformly in a parameter on
which the oracle answers depend primitive recursively. The finite oracle data of a stage
construction are the main instances: a finite oracle string `l`, answering `l[z]?`, and a finite
set `D`, given by its binary code and answering `1` on `D` and `0` outside it.

This is what makes stage computations effective: for instance, whether `Φ_{e,s}^{A_s}(x)`
converges, with which output and with which use, is primitive recursive in `e`, `s`, `x` and the
binary code of the finite stage `A_s`.

## Main definitions

* `TauCeti.Oracle.Single.Code.Halt.equivProd`: a successful run is its output and its use. This
  equivalence gives the `Primcodable` instance of `TauCeti.Oracle.Single.Code.Halt`.

## Main results

* `TauCeti.Oracle.Single.Code.Halt.primrec_output`, `TauCeti.Oracle.Single.Code.Halt.primrec_use`,
  `TauCeti.Oracle.Single.Code.Halt.primrec₂_mk`: the output, the use and the constructor of
  successful runs are primitive recursive.
* `TauCeti.Oracle.Single.Code.primrec_evaln`: bounded evaluation is primitive recursive, uniformly
  in a parameter on which the oracle answers depend primitive recursively.
* `TauCeti.Oracle.Single.Code.primrec_evaln_list`: bounded evaluation against a finite oracle
  string is primitive recursive in the string.
* `TauCeti.Oracle.Single.Code.primrec_evaln_equivBitIndices`: bounded evaluation against a finite
  set, answering `1` on the set and `0` outside it, is primitive recursive in the binary code of
  the set.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
* The proof follows Mathlib's `Nat.Partrec.Code.primrec_evaln`: a course-of-values recursion on
  `Nat.pair k (encode c)` whose table lists the runs at fuel `k` of the program `c`, extended by
  the oracle instruction, the use and the parameter.
-/

public section

open Encodable Denumerable Primrec

namespace TauCeti.Oracle.Single.Code

/-! ### Encoding successful runs -/

/-- A successful run is its output and its use. -/
def Halt.equivProd : Halt ≃ ℕ × ℕ where
  toFun d := (d.output, d.use)
  invFun p := ⟨p.1, p.2⟩

/-- Successful runs are encoded as pairs of their output and their use. -/
instance : Primcodable Halt :=
  Primcodable.ofEquiv (ℕ × ℕ) Halt.equivProd

namespace Halt

/-- A successful run corresponds to the pair of its output and its use. -/
@[simp]
theorem equivProd_apply (d : Halt) : equivProd d = (d.output, d.use) :=
  (rfl)

/-- A pair corresponds to the successful run with that output and use. -/
@[simp]
theorem equivProd_symm_apply (p : ℕ × ℕ) : equivProd.symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-- The output of a successful run is primitive recursive. -/
theorem primrec_output : Primrec output :=
  (fst.comp (of_equiv (e := equivProd))).of_eq fun _ => rfl

/-- The use of a successful run is primitive recursive. -/
theorem primrec_use : Primrec use :=
  (snd.comp (of_equiv (e := equivProd))).of_eq fun _ => rfl

/-- Forming a successful run from its output and its use is primitive recursive. -/
theorem primrec₂_mk : Primrec₂ mk :=
  (of_equiv_symm (e := equivProd)).of_eq fun _ => rfl

end Halt

/-! ### One step of bounded evaluation -/

/-- The run at fuel `k + 1` of the program `c` on an input `n ≤ k`, computed from the runs looked
up in `F`: `F (k + 1) c' n'` for the immediate subprograms `c'` of `c`, and `F k c n'` for the
recursive calls of `prec` and `rfind'`. With `F = evaln σ` this is `evaln σ (k + 1) c n`. -/
private def evalnStep (σ : ℕ → Option ℕ) (F : ℕ → Code → ℕ → Option Halt) (k : ℕ) :
    Code → ℕ → Option Halt
  | zero, _ => some ⟨0, 0⟩
  | succ, n => some ⟨n + 1, 0⟩
  | left, n => some ⟨n.unpair.1, 0⟩
  | right, n => some ⟨n.unpair.2, 0⟩
  | oracle, n => (σ n).map fun y => ⟨y, n + 1⟩
  | pair cf cg, n => (F (k + 1) cf n).bind fun df => (F (k + 1) cg n).map fun dg =>
      ⟨Nat.pair df.output dg.output, max df.use dg.use⟩
  | comp cf cg, n => (F (k + 1) cg n).bind fun dg => (F (k + 1) cf dg.output).map fun df =>
      ⟨df.output, max dg.use df.use⟩
  | prec cf cg, n => n.unpair.2.casesOn (F (k + 1) cf n.unpair.1) fun y =>
      (F k (prec cf cg) (Nat.pair n.unpair.1 y)).bind fun di =>
        (F (k + 1) cg (Nat.pair n.unpair.1 (Nat.pair y di.output))).map fun d =>
          ⟨d.output, max di.use d.use⟩
  | rfind' cf, n => (F (k + 1) cf n).bind fun dx =>
      if dx.output = 0 then some ⟨n.unpair.2, dx.use⟩ else
        (F k (rfind' cf) (Nat.pair n.unpair.1 (n.unpair.2 + 1))).map fun d =>
          ⟨d.output, max dx.use d.use⟩

variable {σ : ℕ → Option ℕ}

/-- On inputs within the fuel, bounded evaluation at fuel `k + 1` is one step from the runs at
fuel `k + 1` of the subprograms and at fuel `k` of the program. -/
private theorem evaln_succ_eq_evalnStep {k n : ℕ} (hn : n ≤ k) (c : Code) :
    evaln σ (k + 1) c n = evalnStep σ (evaln σ) k c n := by
  refine Option.ext fun d => ?_
  obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m := ⟨_, _, (Nat.pair_unpair n).symm⟩
  cases c with
  | prec cf cg =>
    cases m <;> simp [evalnStep, hn, Option.bind_eq_some_iff, @eq_comm Halt]
  | rfind' cf =>
    simp only [evaln_succ_rfind'_eq_some, evalnStep, Nat.unpair_pair, Option.bind_eq_some_iff,
      hn, true_and]
    refine exists_congr fun dx => and_congr_right fun _ => ?_
    split_ifs with h0 <;> simp [h0, eq_comm]
  | _ => simp [evalnStep, hn, Option.bind_eq_some_iff, Option.map_eq_some_iff, @eq_comm Halt]

/-- One step only looks up runs at pairs `Nat.pair k' (encode c')` below
`Nat.pair (k + 1) (encode c)`. -/
private theorem evalnStep_congr {F F' : ℕ → Code → ℕ → Option Halt} {k : ℕ} {c : Code}
    (h : ∀ k' c', Nat.pair k' (encode c') < Nat.pair (k + 1) (encode c) → F k' c' = F' k' c')
    (n : ℕ) : evalnStep σ F k c n = evalnStep σ F' k c n := by
  cases c with
  | zero | succ | left | right | oracle => rfl
  | pair cf cg =>
    simp only [evalnStep, h _ _ (Nat.pair_lt_pair_right _ (encode_lt_pair cf cg).1),
      h _ _ (Nat.pair_lt_pair_right _ (encode_lt_pair cf cg).2)]
  | comp cf cg =>
    simp only [evalnStep, h _ _ (Nat.pair_lt_pair_right _ (encode_lt_comp cf cg).1),
      h _ _ (Nat.pair_lt_pair_right _ (encode_lt_comp cf cg).2)]
  | prec cf cg =>
    simp only [evalnStep, h _ _ (Nat.pair_lt_pair_right _ (encode_lt_prec cf cg).1),
      h _ _ (Nat.pair_lt_pair_right _ (encode_lt_prec cf cg).2),
      h _ _ (Nat.pair_lt_pair_left _ k.lt_succ_self)]
  | rfind' cf =>
    simp only [evalnStep, h _ _ (Nat.pair_lt_pair_right _ (encode_lt_rfind' cf)),
      h _ _ (Nat.pair_lt_pair_left _ k.lt_succ_self)]

/-! ### The course-of-values table -/

/-- The entry of the table at `q = Nat.pair k (encode c)`: the runs at fuel `k` of the program
`c` on the inputs below `k`. -/
private def evalnTable (σ : ℕ → Option ℕ) (q : ℕ) : List (Option Halt) :=
  (List.range (ofNat (ℕ × Code) q).1).map
    (evaln σ (ofNat (ℕ × Code) q).1 (ofNat (ℕ × Code) q).2)

/-- Looking up the run at fuel `k` of the program `c` on the input `n` in a table. -/
private def lup (L : List (List (Option Halt))) (p : ℕ × Code) (n : ℕ) : Option Halt :=
  L[encode p]?.bind fun l => l[n]?.bind id

private theorem primrec_lup {β : Type*} [Primcodable β] {L : β → List (List (Option Halt))}
    {p : β → ℕ × Code} {n : β → ℕ} (hL : Primrec L) (hp : Primrec p) (hn : Primrec n) :
    Primrec fun b => lup (L b) (p b) (n b) :=
  option_bind (list_getElem?.comp hL (encode_iff.2 hp)) <|
    option_bind (list_getElem?.comp snd (hn.comp fst)) Primrec₂.right

/-- The table entry of the program `c` at fuel `k` lists the runs on the inputs below `k`, and
there are none on the other inputs. -/
private theorem getElem?_evalnTable_bind (k : ℕ) (c : Code) (n : ℕ) :
    (evalnTable σ (encode (k, c)))[n]?.bind id = evaln σ k c n := by
  rw [evalnTable, ofNat_encode, List.getElem?_map]
  by_cases hn : n < k
  · simp [List.getElem?_range hn]
  · rw [List.getElem?_eq_none (by simpa using hn)]
    cases h : evaln σ k c n
    · rfl
    · exact absurd (evaln_bound h) hn

private theorem lup_evalnTable {P k : ℕ} {c : Code} (h : encode (k, c) < P) (n : ℕ) :
    lup ((List.range P).map (evalnTable σ)) (k, c) n = evaln σ k c n := by
  rw [lup, List.getElem?_map, List.getElem?_range h, Option.map_some, Option.bind_some]
  exact getElem?_evalnTable_bind k c n

/-- The step of the course-of-values recursion: the table entry at `L.length` from the entries
`L` below it. -/
private def evalnTableStep (σ : ℕ → Option ℕ) (L : List (List (Option Halt))) :
    Option (List (Option Halt)) :=
  some <| (List.range (ofNat (ℕ × Code) L.length).1).map fun n =>
    (ofNat (ℕ × Code) L.length).1.casesOn none fun k =>
      evalnStep σ (fun k' c' => lup L (k', c')) k (ofNat (ℕ × Code) L.length).2 n

private theorem evalnTableStep_eq (q : ℕ) :
    evalnTableStep σ ((List.range q).map (evalnTable σ)) = some (evalnTable σ q) := by
  rw [evalnTableStep, evalnTable, List.length_map, List.length_range, Option.some_inj]
  obtain ⟨⟨k, c⟩, rfl⟩ : ∃ p : ℕ × Code, encode p = q := ⟨_, encode_ofNat q⟩
  rw [ofNat_encode]
  refine List.map_congr_left fun n hn => ?_
  cases k with
  | zero => simp at hn
  | succ k =>
    rw [evaln_succ_eq_evalnStep (by simpa [Nat.lt_succ_iff] using hn)]
    refine evalnStep_congr (fun k' c' h => funext fun n' => lup_evalnTable ?_ n') n
    simpa [encode_prod_val] using h

/-! ### Primitive recursiveness -/

/-- The run combining two successive runs `d₁` and `d₂`: the output of `d₂` and the larger use. -/
private theorem primrec_mk_output_max_use {γ : Type*} [Primcodable γ] {d₁ d₂ : γ → Halt}
    (h₁ : Primrec d₁) (h₂ : Primrec d₂) :
    Primrec fun x => (⟨(d₂ x).output, max (d₁ x).use (d₂ x).use⟩ : Halt) :=
  Halt.primrec₂_mk.comp (Halt.primrec_output.comp h₂)
    (nat_max.comp (Halt.primrec_use.comp h₁) (Halt.primrec_use.comp h₂))

variable {α : Type*} [Primcodable α]

private theorem primrec_evalnStep {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) {β : Type*}
    [Primcodable β] {a : β → α} {L : β → List (List (Option Halt))} {k : β → ℕ} {c : β → Code}
    {n : β → ℕ} (ha : Primrec a) (hL : Primrec L) (hk : Primrec k) (hc : Primrec c)
    (hn : Primrec n) :
    Primrec fun b => evalnStep (σ (a b)) (fun k' c' => lup (L b) (k', c')) (k b) (c b) (n b) := by
  -- Case analysis on the program by `primrec_casesOn`. Each branch is the matching clause of
  -- `evalnStep`, assembled from table lookups `primrec_lup`; the clauses for `prec` and `rfind'`
  -- are the two goals left over. The final `rfl` unfolds the clauses of `evalnStep`.
  -- projections out of the context of a branch, which adds the components of the program
  have hL₁ : Primrec fun x : β × (Code × Code) => L x.1 := hL.comp fst
  have hk₁ : Primrec fun x : β × (Code × Code) => k x.1 := hk.comp fst
  have hn₁ : Primrec fun x : β × (Code × Code) => n x.1 := hn.comp fst
  have hcf : Primrec fun x : β × (Code × Code) => x.2.1 := fst.comp snd
  have hcg : Primrec fun x : β × (Code × Code) => x.2.2 := snd.comp snd
  have hout := Halt.primrec_output
  have huse := Halt.primrec_use
  refine (primrec_casesOn hc (const (some ⟨0, 0⟩))
    (option_some.comp (Halt.primrec₂_mk.comp (Primrec.succ.comp hn) (const 0)))
    (option_some.comp (Halt.primrec₂_mk.comp (fst.comp (Primrec.unpair.comp hn)) (const 0)))
    (option_some.comp (Halt.primrec₂_mk.comp (snd.comp (Primrec.unpair.comp hn)) (const 0)))
    (option_map (hσ.comp ha hn)
      (Halt.primrec₂_mk.comp snd (Primrec.succ.comp (hn.comp fst))).to₂)
    (pr := fun b cs => (lup (L b) (k b + 1, cs.1) (n b)).bind fun df =>
      (lup (L b) (k b + 1, cs.2) (n b)).map fun dg =>
        ⟨Nat.pair df.output dg.output, max df.use dg.use⟩)
    (option_bind (primrec_lup hL₁ ((Primrec.succ.comp hk₁).pair hcf) hn₁) <| .mk <|
      option_map (primrec_lup (hL₁.comp fst)
        ((Primrec.succ.comp (hk₁.comp fst)).pair (hcg.comp fst)) (hn₁.comp fst)) <| .mk <|
      Halt.primrec₂_mk.comp (Primrec₂.natPair.comp (hout.comp (snd.comp fst)) (hout.comp snd))
        (nat_max.comp (huse.comp (snd.comp fst)) (huse.comp snd)))
    (co := fun b cs => (lup (L b) (k b + 1, cs.2) (n b)).bind fun dg =>
      (lup (L b) (k b + 1, cs.1) dg.output).map fun df => ⟨df.output, max dg.use df.use⟩)
    (option_bind (primrec_lup hL₁ ((Primrec.succ.comp hk₁).pair hcg) hn₁) <| .mk <|
      option_map (primrec_lup (hL₁.comp fst)
        ((Primrec.succ.comp (hk₁.comp fst)).pair (hcf.comp fst)) (hout.comp snd)) <| .mk <|
      primrec_mk_output_max_use (snd.comp fst) snd)
    (pc := fun b cs => (n b).unpair.2.casesOn (lup (L b) (k b + 1, cs.1) (n b).unpair.1) fun y =>
      (lup (L b) (k b, prec cs.1 cs.2) (Nat.pair (n b).unpair.1 y)).bind fun di =>
        (lup (L b) (k b + 1, cs.2) (Nat.pair (n b).unpair.1 (Nat.pair y di.output))).map fun d =>
          ⟨d.output, max di.use d.use⟩)
    ?_ (rf := fun b cf => (lup (L b) (k b + 1, cf) (n b)).bind fun dx =>
      if dx.output = 0 then some ⟨(n b).unpair.2, dx.use⟩ else
        (lup (L b) (k b, rfind' cf) (Nat.pair (n b).unpair.1 ((n b).unpair.2 + 1))).map fun d =>
          ⟨d.output, max dx.use d.use⟩) ?_).of_eq fun b => by cases c b <;> rfl
  · -- `prec`: the base program at zero, the recursion and the step program at a successor
    have ha₁ : Primrec fun x : β × (Code × Code) => (n x.1).unpair.1 :=
      fst.comp (Primrec.unpair.comp hn₁)
    refine nat_casesOn (snd.comp (Primrec.unpair.comp hn₁))
      (primrec_lup hL₁ ((Primrec.succ.comp hk₁).pair hcf) ha₁) <| .mk <|
      option_bind (primrec_lup (hL₁.comp fst) ((hk₁.comp fst).pair
        (primrec₂_prec.comp (hcf.comp fst) (hcg.comp fst)))
        (Primrec₂.natPair.comp (ha₁.comp fst) snd)) <| .mk <|
      option_map (primrec_lup (hL₁.comp (fst.comp fst))
        ((Primrec.succ.comp (hk₁.comp (fst.comp fst))).pair (hcg.comp (fst.comp fst)))
        (Primrec₂.natPair.comp (ha₁.comp (fst.comp fst))
          (Primrec₂.natPair.comp (snd.comp fst) (hout.comp snd)))) <| .mk <|
      primrec_mk_output_max_use (snd.comp fst) snd
  · -- `rfind'`: the program at the current point, then the search from the next point
    have hn₁ : Primrec fun x : β × Code => n x.1 := hn.comp fst
    have hu : Primrec fun x : (β × Code) × Halt => (n x.1.1).unpair :=
      Primrec.unpair.comp (hn₁.comp fst)
    refine option_bind
      (primrec_lup (hL.comp fst) ((Primrec.succ.comp (hk.comp fst)).pair snd) hn₁) <| .mk <|
      Primrec.ite (Primrec.eq.comp (hout.comp snd) (const 0))
        (option_some.comp (Halt.primrec₂_mk.comp (snd.comp hu) (huse.comp snd))) <|
      option_map (primrec_lup (hL.comp (fst.comp fst))
        ((hk.comp (fst.comp fst)).pair (primrec_rfind'.comp (snd.comp fst)))
        (Primrec₂.natPair.comp (fst.comp hu) (Primrec.succ.comp (snd.comp hu)))) <| .mk <|
      primrec_mk_output_max_use (snd.comp fst) snd

/-- **Bounded evaluation is primitive recursive**, uniformly in a parameter `a` on which the
oracle answers `σ a` depend primitive recursively: the output and the use of the run of the program
`c` on the input `n` with fuel `k` against `σ a`, or its failure, are primitive recursive in
`a`, `k`, `c` and `n`. -/
theorem primrec_evaln {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    Primrec fun p : α × ℕ × Code × ℕ => evaln (σ p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  have hstep : Primrec₂ fun a L => evalnTableStep (σ a) L := by
    have hq : Primrec fun x : α × List (List (Option Halt)) => ofNat (ℕ × Code) x.2.length :=
      (Primrec.ofNat _).comp (list_length.comp snd)
    refine option_some.comp (list_map (list_range.comp (fst.comp hq)) ?_)
    exact nat_casesOn (fst.comp (hq.comp fst)) (const none) <| .mk <|
      primrec_evalnStep hσ (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) snd
        (snd.comp (hq.comp (fst.comp fst))) (snd.comp fst)
  have htable : Primrec₂ fun a q => evalnTable (σ a) q :=
    nat_strong_rec _ hstep fun a q => evalnTableStep_eq q
  refine (option_bind (list_getElem?.comp (htable.comp fst
    (encode_iff.2 ((fst.comp snd).pair (fst.comp (snd.comp snd))))) (snd.comp (snd.comp snd)))
    Primrec₂.right).of_eq fun p => ?_
  exact getElem?_evalnTable_bind (σ := σ p.1) _ _ _

/-- Bounded evaluation against a finite oracle string `l`, which answers `l[z]?` at `z`, is
primitive recursive in the string, the fuel, the program and the input. -/
theorem primrec_evaln_list :
    Primrec fun p : List ℕ × ℕ × Code × ℕ => evaln (fun z => p.1[z]?) p.2.1 p.2.2.1 p.2.2.2 :=
  primrec_evaln list_getElem?

/-- Bounded evaluation against a finite set, given by its binary code `m` and answering `1` on the
set `Finset.equivBitIndices m` and `0` outside it, is primitive recursive in the code, the fuel,
the program and the input. -/
theorem primrec_evaln_equivBitIndices :
    Primrec fun p : ℕ × ℕ × Code × ℕ =>
      evaln (fun z => some (if z ∈ Finset.equivBitIndices p.1 then 1 else 0))
        p.2.1 p.2.2.1 p.2.2.2 :=
  primrec_evaln <| (option_some.comp (Primrec.ite mem_equivBitIndices (const 1) (const 0))).to₂

end TauCeti.Oracle.Single.Code
