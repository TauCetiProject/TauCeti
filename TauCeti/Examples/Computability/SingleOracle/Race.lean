/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Race

/-!
# Regression examples for earliest-discovery racing

A composite zero program has a larger index than the zero instruction, so its normalized run
is discovered later. A left-preferred choice of current runs switches from right to left; the
earliest-discovery race correctly retains the right winner. A simultaneous pair of raw query
runs demonstrates the left tie rule and retention of a nonzero use even on an oracle answer of
zero. The final example exercises the uniform primitive-recursive certificate on finite strings.
-/

open TauCeti.Staged TauCeti.Oracle.Single Code

-- Fixed-oracle observations are persistent, but current left preference is not a tagged race.
example (σ : ℕ → Option ℕ) : ∃ s t, s < t ∧
    ((evalStage σ s (comp zero zero) 0).map Sum.inl <|>
      (evalStage σ s zero 0).map Sum.inr) = some (Sum.inr (⟨0, 0⟩ : Halt)) ∧
    ((evalStage σ t (comp zero zero) 0).map Sum.inl <|>
      (evalStage σ t zero 0).map Sum.inr) = some (Sum.inl (⟨0, 0⟩ : Halt)) ∧
    ∀ u ≥ s, raceStage σ u (comp zero zero) zero 0 = some (Sum.inr ⟨0, 0⟩) := by
  let s := Encodable.encode (zero : Code) + 1
  let t := Encodable.encode (comp zero zero) + 1
  have hindex := (encode_lt_comp zero zero).1
  have hst : s < t := by omega
  have hc : evalStage σ s (comp zero zero) 0 = none :=
    evalStage_eq_none_of_le_encode (by omega)
  have hd : evalStage σ s zero 0 = some ⟨0, 0⟩ :=
    evalStage_eq_some_of_evaln (k := 1) (by simp) (by omega) (by omega) (by simp [s])
  have hc' : evalStage σ t (comp zero zero) 0 = some ⟨0, 0⟩ :=
    evalStage_eq_some_of_evaln (k := 1) (by simp) (by omega) (by omega) (by simp [t])
  refine ⟨s, t, hst, by simp [hc, hd], by simp [hc'], fun u hu => raceStage_mono hu ?_⟩
  rw [raceStage_eq_some_inr_iff]
  refine ⟨s, le_rfl, hc, ?_, hd⟩
  intro u hu
  exact evalStage_eq_none_of_le_encode (by omega)

-- Negative oracle answers are successful queries, and their use is retained across a tie.
example (s : ℕ) (hs : 1 ≤ s) :
    race (fun k => evaln (fun q => [0][q]?) k oracle 0)
      (fun k => evaln (fun q => [0][q]?) k oracle 0) s = some (Sum.inl ⟨0, 1⟩) := by
  apply race_mono hs
  rw [race_eq_some_inl_iff]
  refine ⟨1, le_rfl, ?_, by simp⟩
  intro t ht
  have : t = 0 := by omega
  subst t
  simp

-- Neither absent observation can create a winner, including at stage zero.
example (s : ℕ) : race (fun _ => (none : Option ℕ)) (fun _ => (none : Option ℕ)) s = none := by
  simp

-- Effectivity is uniform in the string, stage, both programs, and input, with no totality test.
example : Primrec fun p : List ℕ × ℕ × Code × Code × ℕ =>
    raceStage (fun q => p.1[q]?) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  exact primrec_raceStage
    (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp Primrec.snd)
