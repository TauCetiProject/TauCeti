/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec

/-!
# Stage-bounded oracle evaluation

`TauCeti.Oracle.Single.Code.evalStage` normalizes raw bounded evaluation to the stage convention
of Soare, III.1.7: a successful computation at stage `s` has program index, input and output
strictly below `s`, and use at most `s`. Stage zero has no successful computations.

Raw fuel and normalized stages are different: an oracle can return an arbitrarily large number
even at small fuel. Normalization delays such a result until the output and program index fit
inside the stage bound. It does not alter the output or use. Every successful raw run appears at
an explicitly bounded later stage, and successful stage computations persist with the same use
when the oracle is fixed. Agreement below the recorded use also permits changing the oracle.

The primitive-recursive certificates include both finite strings (unanswered beyond their length)
and binary-coded finite sets (answering zero outside the set). This supplies effective finite
stage observations for constructions using oracle computations and restraints.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.1.7–9.
-/

public section

namespace TauCeti.Oracle.Single.Code

open Encodable

/-- Oracle evaluation at stage `s`: raw evaluation with fuel `s`, retaining only computations whose
program index and output are below `s`. Raw evaluation already bounds the input and the use.
Failure is `none`, distinct from a successful computation with use zero. -/
def evalStage (σ : ℕ → Option ℕ) (s : ℕ) (c : Code) (n : ℕ) : Option Halt :=
  if encode c < s then
    (evaln σ s c n).bind fun d => if d.output < s then some d else none
  else none

variable {σ τ : ℕ → Option ℕ} {s t k n : ℕ} {c : Code} {d : Halt}

/-- Normalization keeps exactly the raw runs whose program index and output fit the stage. -/
@[simp]
theorem evalStage_eq_some_iff :
    evalStage σ s c n = some d ↔
      encode c < s ∧ evaln σ s c n = some d ∧ d.output < s := by
  by_cases hc : encode c < s
  · simp only [evalStage, hc, ↓reduceIte, true_and, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨d', hd', h⟩
      split_ifs at h with hd
      grind
    · rintro ⟨h, hd⟩
      exact ⟨d, h, by simp [hd]⟩
  · simp [evalStage, hc]

/-- Stage zero has no successful computations. -/
@[simp]
theorem evalStage_zero (σ : ℕ → Option ℕ) (c : Code) (n : ℕ) :
    evalStage σ 0 c n = none := by
  simp [evalStage]

/-- Programs whose indices are at least the stage have no successful stage computations. This
bounds the program indices that a finite-priority search needs to inspect. -/
theorem evalStage_eq_none_of_le_encode (hs : s ≤ encode c) : evalStage σ s c n = none := by
  simp [evalStage, not_lt.mpr hs]

/-- A successful stage computation has program index below the stage. -/
theorem evalStage_index_lt (h : evalStage σ s c n = some d) : encode c < s :=
  (evalStage_eq_some_iff.1 h).1

/-- A successful stage computation has input below the stage. -/
theorem evalStage_input_lt (h : evalStage σ s c n = some d) : n < s :=
  evaln_bound (evalStage_eq_some_iff.1 h).2.1

/-- A successful stage computation has output below the stage. -/
theorem evalStage_output_lt (h : evalStage σ s c n = some d) : d.output < s :=
  (evalStage_eq_some_iff.1 h).2.2

/-- A successful stage computation queries only addresses below the stage. -/
theorem evalStage_use_le (h : evalStage σ s c n = some d) : d.use ≤ s :=
  evaln_use_le (evalStage_eq_some_iff.1 h).2.1

/-- A raw run is retained at any later stage large enough for its program index and output. -/
theorem evalStage_eq_some_of_evaln (h : evaln σ k c n = some d) (hks : k ≤ s)
    (hc : encode c < s) (hd : d.output < s) : evalStage σ s c n = some d :=
  evalStage_eq_some_iff.2 ⟨hc, evaln_mono hks h, hd⟩

/-- An explicit raw-fuel to stage comparison, preserving both output and use. -/
theorem evalStage_max_eq_some (h : evaln σ k c n = some d) :
    evalStage σ (max k (max (encode c) d.output + 1)) c n = some d :=
  evalStage_eq_some_of_evaln h (by omega) (by omega) (by omega)

/-- Successful stage computations persist, with unchanged output and use, for a fixed oracle. -/
theorem evalStage_mono (hst : s ≤ t) (h : evalStage σ s c n = some d) :
    evalStage σ t c n = some d := by
  obtain ⟨hc, h, hd⟩ := evalStage_eq_some_iff.1 h
  exact evalStage_eq_some_of_evaln h hst (hc.trans_le hst) (hd.trans_le hst)

/-- Two successful stage computations against the same oracle have the same output and use. -/
theorem evalStage_unique {d' : Halt} (h : evalStage σ s c n = some d)
    (h' : evalStage σ t c n = some d') : d = d' :=
  evaln_unique (evalStage_eq_some_iff.1 h).2.1 (evalStage_eq_some_iff.1 h').2.1

/-- Stage-to-stage use principle: agreement below the recorded use and an increased stage bound
preserve both output and use. No persistence is asserted for arbitrary moving oracles. -/
theorem evalStage_eq_some_of_eqOn (h : evalStage σ s c n = some d)
    (hστ : Set.EqOn σ τ (Set.Iio d.use)) (hst : s ≤ t) :
    evalStage τ t c n = some d := by
  obtain ⟨hc, h, hd⟩ := evalStage_eq_some_iff.1 h
  exact evalStage_eq_some_of_evaln (evaln_eq_some_of_eqOn h hστ) hst
    (hc.trans_le hst) (hd.trans_le hst)

/-- Every successful raw run is eventually retained at all normalized stages. The output and
recorded use are those of the original run, not merely some run with the same output. -/
theorem exists_forall_evalStage_eq_some (h : evaln σ k c n = some d) :
    ∃ s₀, ∀ s ≥ s₀, evalStage σ s c n = some d :=
  ⟨_, fun _ hs => evalStage_mono hs (evalStage_max_eq_some h)⟩

/-- A successful normalized computation is sound for every partial oracle containing the supplied
answers below its use. -/
theorem evalStage_sound {O : ℕ →. ℕ} (h : evalStage σ s c n = some d)
    (hσ : ∀ z < d.use, ∀ y, σ z = some y → y ∈ O z) : d.output ∈ eval O c n :=
  evaln_sound (evalStage_eq_some_iff.1 h).2.1 hσ

/-- Completeness at normalized stages: if all values of an oracle are supplied, every output
appears at all sufficiently large stages, with one fixed recorded use. -/
theorem exists_eventually_evalStage_eq_some_of_mem_eval {O : ℕ →. ℕ}
    (hσ : ∀ z y, y ∈ O z → σ z = some y) {y : ℕ} (h : y ∈ eval O c n) :
    ∃ d, d.output = y ∧ ∃ s₀, ∀ s ≥ s₀, evalStage σ s c n = some d := by
  obtain ⟨k, d, hd, hy⟩ := exists_evaln_eq_some_of_mem_eval hσ h
  exact ⟨d, hy, exists_forall_evalStage_eq_some hd⟩

/-- Normalized stages present exactly the partial evaluation when the supplied answers are exactly
the values of the oracle. -/
theorem mem_eval_iff_exists_evalStage {O : ℕ →. ℕ}
    (hσ : ∀ z y, σ z = some y ↔ y ∈ O z) {y : ℕ} :
    y ∈ eval O c n ↔ ∃ s d, evalStage σ s c n = some d ∧ d.output = y := by
  constructor
  · intro h
    obtain ⟨d, hy, s, hs⟩ := exists_eventually_evalStage_eq_some_of_mem_eval
      (fun z y => (hσ z y).2) h
    exact ⟨s, d, hs s le_rfl, hy⟩
  · rintro ⟨s, d, hd, rfl⟩
    exact evalStage_sound hd fun z _ y hy => (hσ z y).1 hy

section Primrec

open Primrec

variable {α : Type*} [Primcodable α]

/-- Stage evaluation is primitive recursive uniformly in any primitive-recursive family of finite
oracle answers. The normalization tests require no unbounded search. -/
theorem primrec_evalStage {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    Primrec fun p : α × ℕ × Code × ℕ => evalStage (σ p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  have hs : Primrec fun p : α × ℕ × Code × ℕ => p.2.1 := fst.comp snd
  have hc : Primrec fun p : α × ℕ × Code × ℕ => encode p.2.2.1 :=
    encode_iff.2 (fst.comp (snd.comp snd))
  exact Primrec.ite (nat_lt.comp hc hs)
    (option_bind (primrec_evaln hσ) <| Primrec₂.mk <|
      Primrec.ite (nat_lt.comp (Halt.primrec_output.comp snd) (hs.comp fst))
        (option_some.comp snd) (const none)) (const none)

/-- Normalized evaluation on finite strings is primitive recursive. Missing answers are not
replaced by zero. -/
theorem primrec_evalStage_list :
    Primrec fun p : List ℕ × ℕ × Code × ℕ =>
      evalStage (fun z => p.1[z]?) p.2.1 p.2.2.1 p.2.2.2 :=
  primrec_evalStage list_getElem?

/-- Normalized evaluation on binary-coded finite sets, answering zero outside the set, is
primitive recursive in the code, the stage, the program and the input. -/
theorem primrec_evalStage_equivBitIndices :
    Primrec fun p : ℕ × ℕ × Code × ℕ =>
      evalStage (fun z => some (if z ∈ Finset.equivBitIndices p.1 then 1 else 0))
        p.2.1 p.2.2.1 p.2.2.2 :=
  primrec_evalStage <| (option_some.comp
    (Primrec.ite mem_equivBitIndices (const 1) (const 0))).to₂

end Primrec

end TauCeti.Oracle.Single.Code
