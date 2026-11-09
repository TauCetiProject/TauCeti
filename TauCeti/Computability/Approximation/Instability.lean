/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Modulus
public import TauCeti.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn

/-!
# Instability of an approximation

The instability set records the coordinate-stage pairs after which an approximation changes.
Its membership is c.e. relative to any oracle computing the approximation. An oracle computing
the stages and deciding instability computes the limit by finding a stage after which the value
no longer changes.
This is the common search underlying the Limit Lemma and the c.e.-degree criterion for moduli.

## Main results

* `TauCeti.Approximation.exists_recursiveIn_dom_iff_mem_instabilitySet`: instability is a relative
  c.e. domain.
* `TauCeti.Approximation.rePred_mem_instabilitySet`: instability of a computable approximation
  is c.e.
* `TauCeti.Approximation.Converges.computableIn_of_instabilitySet`: stable-stage search computes
  the limit from the stages and their instability set.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.3.3–4.
-/

public section

open Encodable

namespace TauCeti.Approximation

variable {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ → ℕ} {g m : ℕ → ℕ}

/-- Codes `Nat.pair x s` of coordinate-stage pairs after which the approximation changes. -/
def instabilitySet (f : ℕ → ℕ → ℕ) : Set ℕ :=
  {n | ∃ t, f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1}

/-- Membership in the instability set on arbitrary codes. -/
theorem mem_instabilitySet_iff {n : ℕ} :
    n ∈ instabilitySet f ↔ ∃ t, f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1 :=
  Iff.rfl

/-- Membership at a coordinate-stage pair means some later value differs. -/
@[simp]
theorem mem_instabilitySet_pair_iff {x s : ℕ} :
    Nat.pair x s ∈ instabilitySet f ↔ ∃ t, f (s + t) x ≠ f s x := by
  simp only [mem_instabilitySet_iff, Nat.unpair_pair]

/-- A modulus bounds the search for a later different value, even at stages before the modulus. -/
theorem IsModulus.mem_instabilitySet_iff (hm : IsModulus f g m) (x s : ℕ) :
    Nat.pair x s ∈ instabilitySet f ↔ ∃ t < m x + 1, f (s + t) x ≠ f s x := by
  have hm' := isModulus_iff.1 hm
  rw [mem_instabilitySet_pair_iff]
  constructor
  · rintro ⟨t, ht⟩
    by_cases htm : t ≤ m x
    · exact ⟨t, by omega, ht⟩
    · refine ⟨m x, by omega, ?_⟩
      rw [hm' x (s + m x) (by omega)]
      rwa [hm' x (s + t) (by omega)] at ht
  · rintro ⟨t, -, ht⟩
    exact ⟨t, ht⟩

/-- The stages `s` of a sequence `f` after which the value at `x` changes, coded as
`Nat.pair x s`, form the domain of a function recursive in `O` when `f` is computable in `O`. -/
theorem exists_recursiveIn_dom_iff_mem_instabilitySet (hf : ComputableIn₂ O f) :
    ∃ F : ℕ →. ℕ, Nat.RecursiveIn O F ∧
      ∀ n, (F n).Dom ↔ n ∈ instabilitySet f := by
  -- `f` as a function on codes of pairs `Nat.pair s x`
  have hF : Nat.RecursiveIn O fun n => Part.some (f n.unpair.1 n.unpair.2) :=
    ComputableIn₂.iff_nat.1 hf
  -- on `Nat.pair (Nat.pair x s) t`, the values `f (s + t) x` and `f s x`
  have h₁ := hF.comp_primrec (g := fun m =>
    Nat.pair (m.unpair.1.unpair.2 + m.unpair.2) m.unpair.1.unpair.1) <|
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.snd.comp <| Primrec.unpair.comp <|
        Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  have h₂ := hF.comp_primrec (g := fun m => Nat.pair m.unpair.1.unpair.2 m.unpair.1.unpair.1) <|
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  -- compare them: `0` when they differ, `1` when they agree
  have hq := (h₁.pair h₂).map_primrec (g := fun p => if p.unpair.1 = p.unpair.2 then 1 else 0) <|
    Primrec.nat_iff.1 <| Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1) (Primrec.const 0)
  refine ⟨_, hq.rfind, fun n => ?_⟩
  rw [mem_instabilitySet_iff]
  simp only [Seq.seq, Nat.unpair_pair, Part.map_some]
  refine ⟨fun hd => ?_, fun ⟨t, ht⟩ => Nat.rfind_dom.2 ⟨t, by simpa using ht, fun _ => by simp⟩⟩
  obtain ⟨t, ht, -⟩ := Nat.rfind_dom.1 hd
  exact ⟨t, by simpa using ht⟩

/-- The instability set of a uniformly computable approximation is c.e. -/
theorem rePred_mem_instabilitySet (hf : Computable₂ f) : REPred (· ∈ instabilitySet f) := by
  obtain ⟨F, hF, hdom⟩ := exists_recursiveIn_dom_iff_mem_instabilitySet (O := ∅) hf.computableIn
  exact ((recursiveIn_empty_iff.1 (RecursiveIn.iff_nat.2 hF)).dom_re).of_eq hdom

/-- An oracle computing the stages and deciding instability computes the limit. -/
theorem Converges.computableIn_of_instabilitySet (h : Converges f g)
    (hf : ComputableIn₂ O f) (hU : RecursiveIn O (instabilitySet f).oracle) :
    ComputableIn O g := by
  classical
  have hS := (RecursiveIn.iff_nat.1 hU).rfind
  have hfO := ComputableIn₂.iff_nat.1 hf
  refine RecursiveIn.iff_nat.2 <| (hfO.comp (hS.pair Nat.Primrec.id.recursiveIn)).of_eq_tot
    fun x => ?_
  -- the stages after which the value at `x` no longer changes
  have hex : ∃ s, ∀ t, f (s + t) x = f s x := by
    obtain ⟨s, hs⟩ := Approximation.converges_iff_forall_exists.1 h x
    exact ⟨s, fun t => (hs _ (Nat.le_add_right s t)).trans (hs s le_rfl).symm⟩
  have hmem : Nat.find hex ∈ Nat.rfind fun s =>
      (fun m => decide (m = 0)) <$> (instabilitySet f).oracle (Nat.pair x s) := by
    refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
    · have : Nat.pair x (Nat.find hex) ∉ instabilitySet f := by
        simpa [mem_instabilitySet_pair_iff] using Nat.find_spec hex
      simp [this]
    · have : Nat.pair x m ∈ instabilitySet f := by
        simpa [mem_instabilitySet_pair_iff] using Nat.find_min hex hm
      simp [this]
  have hlim : f (Nat.find hex) x = g x := h.apply_eq_of_forall_le fun t ht => by
    simpa [Nat.add_sub_cancel' ht] using Nat.find_spec hex (t - Nat.find hex)
  rw [Part.eq_some_iff.2 hmem]
  simp [Seq.seq, hlim]

end TauCeti.Approximation
