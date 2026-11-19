/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Instability
import TauCeti.Computability.Approximation.CEOracle
import TauCeti.Computability.RE
import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.TuringDegree

/-!
# Total functions of c.e. degree

A total function has c.e. degree exactly when it has a uniformly computable approximation with a
modulus computable from the function itself (Soare, III.3.4).

If such an approximation and modulus exist, the function is Turing equivalent to the
approximation's instability set: whether a coordinate changes after a given stage. The limit is
computable from this set by stable-stage search, while a modulus bounds the finite search deciding
instability. Conversely, a function Turing equivalent to a c.e. set `U` has, by the Modulus Lemma,
a computable approximation with a `U`-computable modulus, and that modulus is computable from the
function because `U` is.

The criterion is also stated for set oracles: for characteristic functions, and, through graph
coding, for the set of codes of a function's graph.

## Main results

* `TauCeti.Approximation.IsModulus.instabilitySet_turingReducible`: any oracle computing a modulus
  decides the instability set of a computable approximation.
* `TauCeti.Approximation.IsModulus.turingEquivalent_instabilitySet`: a modulus computable from the
  limit identifies the limit's degree with the c.e. instability set.
* `TauCeti.Approximation.IsModulus.exists_rePred_turingEquivalent`: the limit has a c.e. degree.
* `TauCeti.Approximation.exists_isModulus_of_turingEquivalent`: a function of c.e. degree has a
  computable approximation with a modulus computable from the function.
* `TauCeti.Approximation.exists_rePred_turingEquivalent_iff_exists_isModulus`: Soare's criterion
  III.3.4, with its specializations
  `TauCeti.Approximation.exists_rePred_turingEquivalent_oracle_iff_exists_isModulus` to sets and
  `TauCeti.Approximation.exists_rePred_turingEquivalent_graph_iff_exists_isModulus` to graph sets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.3.4.
-/

public section

namespace TauCeti.Approximation

variable {f : ℕ → ℕ → ℕ} {g m : ℕ → ℕ}

/-- Every oracle computing a modulus decides the instability set of a computable approximation. -/
theorem IsModulus.instabilitySet_turingReducible {O : ℕ →. ℕ} (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {O} m) :
    TuringReducible (instabilitySet f).oracle O := by
  classical
  have hq : ComputablePred fun p : (ℕ × ℕ) × ℕ =>
      f (p.1.2 + p.2) p.1.1 ≠ f p.1.2 p.1.1 := by
    exact (Computable.computablePred <| Primrec.eq.decide.to_comp.comp
      (hf.comp (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
        (Computable.fst.comp Computable.fst))
      (hf.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.fst))).not
  have hbound := ComputablePred.exists_lt (p := fun p : ℕ × ℕ => fun t =>
    f (p.2 + t) p.1 ≠ f p.2 p.1) hq
  have hb : ComputableIn {O} fun n : ℕ => m n.unpair.1 + 1 :=
    (Primrec.nat_add.to_comp.computableIn.comp <|
      (hmc.comp (Primrec.fst.comp Primrec.unpair).computableIn).pair
        (ComputableIn.const 1))
  have htest : ComputableIn {O} fun n : ℕ =>
      decide (∃ t < m n.unpair.1 + 1,
        f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1) :=
    hbound.decide.computableIn.comp (ComputableIn.unpair.pair hb)
  have hχ := Nat.RecursiveIn.cond htest
    (Nat.Primrec.const 1).recursiveIn (Nat.Primrec.const 0).recursiveIn
  apply (Set.turingReducible_iff_computableIn_indicator _ _).2
  refine RecursiveIn.of_eq (RecursiveIn.iff_nat.2 hχ) fun n => ?_
  have hiff : n ∈ instabilitySet f ↔ ∃ t < m n.unpair.1 + 1,
      f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1 := by
    simpa only [Nat.pair_unpair] using hm.mem_instabilitySet_iff n.unpair.1 n.unpair.2
  by_cases hn : n ∈ instabilitySet f
  · simp only [decide_eq_true (hiff.1 hn)]
    simp [hn]
  · simp only [decide_eq_false (mt hiff.2 hn)]
    simp [hn]

/-- A modulus computable from the limit makes the limit equivalent to the c.e. instability set. -/
theorem IsModulus.turingEquivalent_instabilitySet (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {fun x => Part.some (g x)} m) :
    TuringEquivalent (fun x => Part.some (g x)) (instabilitySet f).oracle :=
  ⟨hm.converges.computableIn_of_instabilitySet hf.computableIn
      (RecursiveIn.oracle _ rfl), hm.instabilitySet_turingReducible hf hmc⟩

/-- A total function with a computable approximation and a modulus computable from itself
has the degree of a c.e. set. -/
theorem IsModulus.exists_rePred_turingEquivalent (hm : IsModulus f g m)
    (hf : Computable₂ f) (hmc : ComputableIn {fun x => Part.some (g x)} m) :
    ∃ U : Set ℕ, REPred (· ∈ U) ∧ TuringEquivalent (fun x => Part.some (g x)) U.oracle :=
  ⟨instabilitySet f, rePred_mem_instabilitySet hf, hm.turingEquivalent_instabilitySet hf hmc⟩

/-- A total function Turing equivalent to a c.e. set has a computable approximation with a
modulus computable from the function itself. -/
theorem exists_isModulus_of_turingEquivalent {U : Set ℕ} (hU : REPred (· ∈ U))
    (hgU : TuringEquivalent (fun x => Part.some (g x)) U.oracle) :
    ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
      ComputableIn {fun x => Part.some (g x)} m ∧ IsModulus f g m := by
  obtain ⟨f, m, hf, hm, hmod⟩ := (computableIn_iff_exists_isModulus_of_rePred hU).1 hgU.1
  -- `ComputableIn {O} m` is by definition reducibility of `m` to `O`, so reductions compose.
  exact ⟨f, m, hf, TuringReducible.trans hm hgU.2, hmod⟩

/-- **Soare's criterion for c.e. degree.** A total function is Turing equivalent to a c.e. set
exactly when it has a computable approximation with a modulus computable from the function. -/
theorem exists_rePred_turingEquivalent_iff_exists_isModulus :
    (∃ U : Set ℕ, REPred (· ∈ U) ∧ TuringEquivalent (fun x => Part.some (g x)) U.oracle) ↔
      ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
        ComputableIn {fun x => Part.some (g x)} m ∧ IsModulus f g m :=
  ⟨fun ⟨_, hU, hgU⟩ => exists_isModulus_of_turingEquivalent hU hgU,
    fun ⟨_, _, hf, hm, hmod⟩ => hmod.exists_rePred_turingEquivalent hf hm⟩

/-- **Soare's criterion for sets.** A set is Turing equivalent to a c.e. set exactly when its
characteristic function has a computable approximation with a modulus computable from the set. -/
theorem exists_rePred_turingEquivalent_oracle_iff_exists_isModulus {A : Set ℕ} :
    (∃ U : Set ℕ, REPred (· ∈ U) ∧ TuringEquivalent A.oracle U.oracle) ↔
      ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
        ComputableIn {A.oracle} m ∧ IsModulus f (A.indicator 1) m := by
  rw [show A.oracle = fun x => Part.some (A.indicator 1 x) from funext A.oracle_apply]
  exact exists_rePred_turingEquivalent_iff_exists_isModulus

/-- **Soare's criterion through graph coding.** The set coding the graph of a total function is
Turing equivalent to a c.e. set exactly when the function has a computable approximation with a
modulus computable from that graph set. -/
theorem exists_rePred_turingEquivalent_graph_iff_exists_isModulus :
    (∃ U : Set ℕ, REPred (· ∈ U) ∧
      TuringEquivalent (Nat.unpair ⁻¹' g.graph).oracle U.oracle) ↔
      ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
        ComputableIn {(Nat.unpair ⁻¹' g.graph).oracle} m ∧ IsModulus f g m := by
  have hG := g.turingEquivalent_oracle_preimage_unpair_graph
  -- As above, computability in an oracle is reducibility to it, so `hG` transports moduli.
  have hm (m : ℕ → ℕ) : ComputableIn {(Nat.unpair ⁻¹' g.graph).oracle} m ↔
      ComputableIn {fun x => Part.some (g x)} m :=
    ⟨fun h => TuringReducible.trans h hG.2, fun h => TuringReducible.trans h hG.1⟩
  simp only [hm, ← exists_rePred_turingEquivalent_iff_exists_isModulus]
  exact exists_congr fun U => and_congr_right fun _ =>
    ⟨hG.trans _ _ _, hG.symm.trans _ _ _⟩

end TauCeti.Approximation
