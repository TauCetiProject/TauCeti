/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Closure

/-!
# Bounded number quantifiers in the arithmetical hierarchy

Bounded existential and universal number quantifiers preserve each of the quantifier-defined
classes Σ⁰ₙ, Π⁰ₙ and Δ⁰ₙ, including level zero. The bound may depend on the free parameters
by any total function computable in the base oracle.

The nontrivial closure is bounded universal quantification of an existential normal form.
A finite list collects the witnesses for its leading existential quantifiers; the list is
represented by one natural number, and its entries are read by primitive recursive operations.
This allows finite families of conditions, such as the answers in a finite oracle computation,
to be checked without increasing quantifier depth. These are semantic closure results, not
computable extraction of normal-form codes from pointclass-membership proofs.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

namespace TauCeti.ArithmeticalHierarchy

open Encodable

variable {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α]
  {r : α × ℕ → Prop} {f : α → ℕ}

/-- A bounded existential number quantifier preserves Σ⁰ₙ, with an oracle-computable bound. -/
theorem IsSigma.exists_lt (hr : IsSigma Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z n (fun x => ∃ y < f x, r (x, y)) := by
  cases n with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hr
    have hlist := (ComputableIn₂.list_range_map (f := fun x y => b (x, y)) hb).comp
      (ComputableIn.id.pair hf)
    have hcheck : PrimrecPred (fun l : List Bool => ∃ a ∈ l, a = true) :=
      (Primrec.eq.comp Primrec.id (Primrec.const true)).exists_mem_list
    refine isSigma_zero_iff.2 ⟨_, hcheck.decide.computableIn.comp hlist, fun x => ?_⟩
    simp [heq]
  | succ n =>
    have hbound : IsSigma Z 0 (fun a : α × ℕ => a.2 < f a.1) :=
      isSigma_zero_iff.2 ⟨_, Primrec.nat_lt.decide.computableIn.comp
        (ComputableIn.snd.pair (hf.comp ComputableIn.fst)), fun _ => by simp⟩
    exact ((hbound.of_le (Nat.zero_le _)).and hr).exists_nat

/-- A bounded universal number quantifier preserves Π⁰ₙ, with an oracle-computable bound. -/
theorem IsPi.forall_lt (hr : IsPi Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsPi Z n (fun x => ∀ y < f x, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 (((isSigma_not_iff.2 hr).exists_lt hf).of_eq (by simp))

/-- A bounded universal number quantifier preserves Σ⁰ₙ. A single coded finite list supplies
all leading existential witnesses, so no additional quantifier alternation is needed. -/
theorem IsSigma.forall_lt (hr : IsSigma Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z n (fun x => ∀ y < f x, r (x, y)) := by
  cases n with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hr
    have hlist := (ComputableIn₂.list_range_map (f := fun x y => b (x, y)) hb).comp
      (ComputableIn.id.pair hf)
    have hcheck : PrimrecPred (fun l : List Bool => ∀ a ∈ l, a = true) :=
      (Primrec.eq.comp Primrec.id (Primrec.const true)).forall_mem_list
    refine isSigma_zero_iff.2 ⟨_, hcheck.decide.computableIn.comp hlist, fun x => ?_⟩
    simp [heq]
  | succ n =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hr
    have hdecode : Primrec (fun c => (decode (α := List ℕ) c).getD []) :=
      Primrec.option_getD.comp Primrec.decode (Primrec.const [])
    have hread : Primrec (fun a : (α × ℕ) × ℕ =>
        ((a.1.1, a.2), ((decode (α := List ℕ) a.1.2).getD []).getD a.2 0)) :=
      (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd).pair
        ((Primrec.list_getD 0).comp (hdecode.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)
    have hmatrix := (hq.preimage hread.computableIn).forall_lt (hf.comp ComputableIn.fst)
    refine isSigma_succ_iff.2 ⟨_, hmatrix, fun x => ?_⟩
    constructor
    · intro h
      let g : Fin (f x) → ℕ := fun i => Classical.choose ((heq (x, i)).1 (h i i.isLt))
      refine ⟨encode (List.ofFn g), fun y hy => ?_⟩
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hy] using
        (Classical.choose_spec ((heq (x, y)).1 (h y hy)))
    · rintro ⟨c, hc⟩ y hy
      exact (heq (x, y)).2 ⟨_, hc y hy⟩

/-- A bounded existential number quantifier preserves Π⁰ₙ, with an oracle-computable bound. -/
theorem IsPi.exists_lt (hr : IsPi Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsPi Z n (fun x => ∃ y < f x, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 (((isSigma_not_iff.2 hr).forall_lt hf).of_eq (by simp))

/-- Bounded existential number quantification preserves Δ⁰ₙ. -/
theorem IsDelta.exists_lt (hr : IsDelta Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsDelta Z n (fun x => ∃ y < f x, r (x, y)) :=
  isDelta_iff.2 ⟨(isDelta_iff.1 hr).1.exists_lt hf, (isDelta_iff.1 hr).2.exists_lt hf⟩

/-- Bounded universal number quantification preserves Δ⁰ₙ. -/
theorem IsDelta.forall_lt (hr : IsDelta Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsDelta Z n (fun x => ∀ y < f x, r (x, y)) :=
  isDelta_iff.2 ⟨(isDelta_iff.1 hr).1.forall_lt hf, (isDelta_iff.1 hr).2.forall_lt hf⟩

/-- An inclusive bounded existential number quantifier preserves Σ⁰ₙ. -/
theorem IsSigma.exists_le (hr : IsSigma Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z n (fun x => ∃ y ≤ f x, r (x, y)) :=
  (hr.exists_lt (Primrec.succ.computableIn.comp hf)).of_eq (by simp [Nat.lt_succ_iff])

/-- An inclusive bounded universal number quantifier preserves Σ⁰ₙ. -/
theorem IsSigma.forall_le (hr : IsSigma Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z n (fun x => ∀ y ≤ f x, r (x, y)) :=
  (hr.forall_lt (Primrec.succ.computableIn.comp hf)).of_eq (by simp [Nat.lt_succ_iff])

/-- An inclusive bounded existential number quantifier preserves Π⁰ₙ. -/
theorem IsPi.exists_le (hr : IsPi Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsPi Z n (fun x => ∃ y ≤ f x, r (x, y)) :=
  (hr.exists_lt (Primrec.succ.computableIn.comp hf)).of_eq (by simp [Nat.lt_succ_iff])

/-- An inclusive bounded universal number quantifier preserves Π⁰ₙ. -/
theorem IsPi.forall_le (hr : IsPi Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsPi Z n (fun x => ∀ y ≤ f x, r (x, y)) :=
  (hr.forall_lt (Primrec.succ.computableIn.comp hf)).of_eq (by simp [Nat.lt_succ_iff])

/-- Inclusive bounded existential number quantification preserves Δ⁰ₙ. -/
theorem IsDelta.exists_le (hr : IsDelta Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsDelta Z n (fun x => ∃ y ≤ f x, r (x, y)) :=
  isDelta_iff.2 ⟨(isDelta_iff.1 hr).1.exists_le hf, (isDelta_iff.1 hr).2.exists_le hf⟩

/-- Inclusive bounded universal number quantification preserves Δ⁰ₙ. -/
theorem IsDelta.forall_le (hr : IsDelta Z n r) (hf : ComputableIn {Z.oracle} f) :
    IsDelta Z n (fun x => ∀ y ≤ f x, r (x, y)) :=
  isDelta_iff.2 ⟨(isDelta_iff.1 hr).1.forall_le hf, (isDelta_iff.1 hr).2.forall_le hf⟩

end TauCeti.ArithmeticalHierarchy
