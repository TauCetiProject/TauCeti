/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic
import Mathlib.Computability.Primrec.List

/-!
# Closure and quantifier contraction for arithmetical pointclasses

Both existential and universal arithmetical pointclasses are closed under finite conjunction,
disjunction, and number quantifiers bounded by an oracle-computable function of the parameters.
At positive levels, an additional existential quantifier over any primitive-codable type can be
contracted into the leading number quantifier on an existential pointclass, and the dual
statement holds for universal pointclasses. Bounded universal quantifiers at positive existential
levels use finite witness lists to commute the bounded universal quantifier past the leading
existential quantifier.

The classes are increasing in the level, and either class at one level is contained in the
intersection class at the next. All statements retain the oracle and arbitrary primitive-codable
free parameters. No jump characterization is used.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {n m : ℕ} {α : Type*} [Primcodable α] {p q : α → Prop}

-- Conjunction and disjunction must be established together: complementation in the
-- successor definition exchanges them at the preceding level.
private theorem sigma_and_or (hp : IsSigma Z n p) (hq : IsSigma Z n q) :
    IsSigma Z n (fun x => p x ∧ q x) ∧ IsSigma Z n (fun x => p x ∨ q x) := by
  classical
  induction n generalizing α with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hp
    obtain ⟨c, hc, hceq⟩ := isSigma_zero_iff.1 hq
    exact ⟨isSigma_zero_iff.2
      ⟨fun x => b x && c x, Primrec.and.computableIn.comp (hb.pair hc),
        fun x => by simp [heq, hceq]⟩,
      isSigma_zero_iff.2
        ⟨fun x => b x || c x, Primrec.or.computableIn.comp (hb.pair hc),
          fun x => by simp [heq, hceq]⟩⟩
  | succ n ih =>
    obtain ⟨r, hr, her⟩ := isSigma_succ_iff.1 hp
    obtain ⟨t, ht, het⟩ := isSigma_succ_iff.1 hq
    have hr' := (isSigma_not_iff.2 hr).preimage (ComputableIn.fst.pair
      ((Primrec.fst.comp Primrec.unpair).computableIn.comp ComputableIn.snd))
    have ht' := (isSigma_not_iff.2 ht).preimage (ComputableIn.fst.pair
      ((Primrec.snd.comp Primrec.unpair).computableIn.comp ComputableIn.snd))
    obtain ⟨hand, hor⟩ := ih hr' ht'
    constructor
    · refine isSigma_succ_iff.2
        ⟨fun a => r (a.1, a.2.unpair.1) ∧ t (a.1, a.2.unpair.2),
          isSigma_not_iff.1 (hor.of_eq (fun _ => not_and_or.symm)), fun x => ?_⟩
      simp only [her, het]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨Nat.pair i j, by simpa using And.intro hi hj⟩
      · rintro ⟨k, hi, hj⟩
        exact ⟨⟨_, hi⟩, ⟨_, hj⟩⟩
    · refine isSigma_succ_iff.2
        ⟨fun a => r (a.1, a.2.unpair.1) ∨ t (a.1, a.2.unpair.2),
          isSigma_not_iff.1 (hand.of_eq (by simp)), fun x => ?_⟩
      simp only [her, het]
      constructor
      · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
        · exact ⟨Nat.pair i 0, by simpa using Or.inl hi⟩
        · exact ⟨Nat.pair 0 j, by simpa using Or.inr hj⟩
      · rintro ⟨k, hi | hj⟩
        · exact Or.inl ⟨_, hi⟩
        · exact Or.inr ⟨_, hj⟩

/-- Existential pointclasses are closed under conjunction. -/
theorem IsSigma.and (hp : IsSigma Z n p) (hq : IsSigma Z n q) :
    IsSigma Z n (fun x => p x ∧ q x) :=
  (sigma_and_or hp hq).1

/-- Existential pointclasses are closed under disjunction. -/
theorem IsSigma.or (hp : IsSigma Z n p) (hq : IsSigma Z n q) :
    IsSigma Z n (fun x => p x ∨ q x) :=
  (sigma_and_or hp hq).2

/-- Universal pointclasses are closed under conjunction. -/
theorem IsPi.and (hp : IsPi Z n p) (hq : IsPi Z n q) :
    IsPi Z n (fun x => p x ∧ q x) := by
  classical
  exact isSigma_not_iff.1
    (((isSigma_not_iff.2 hp).or (isSigma_not_iff.2 hq)).of_eq
      (fun _ => not_and_or.symm))

/-- Universal pointclasses are closed under disjunction. -/
theorem IsPi.or (hp : IsPi Z n p) (hq : IsPi Z n q) :
    IsPi Z n (fun x => p x ∨ q x) := by
  exact isSigma_not_iff.1
    (((isSigma_not_iff.2 hp).and (isSigma_not_iff.2 hq)).of_eq (by simp))

/-- The intersection pointclass is closed under conjunction. -/
theorem IsDelta.and (hp : IsDelta Z n p) (hq : IsDelta Z n q) :
    IsDelta Z n (fun x => p x ∧ q x) := by
  obtain ⟨hpS, hpP⟩ := isDelta_iff.1 hp
  obtain ⟨hqS, hqP⟩ := isDelta_iff.1 hq
  exact isDelta_iff.2 ⟨hpS.and hqS, hpP.and hqP⟩

/-- The intersection pointclass is closed under disjunction. -/
theorem IsDelta.or (hp : IsDelta Z n p) (hq : IsDelta Z n q) :
    IsDelta Z n (fun x => p x ∨ q x) := by
  obtain ⟨hpS, hpP⟩ := isDelta_iff.1 hp
  obtain ⟨hqS, hqP⟩ := isDelta_iff.1 hq
  exact isDelta_iff.2 ⟨hpS.or hqS, hpP.or hqP⟩

/-- At a positive existential level, an extra existential number quantifier can be
contracted into the leading quantifier. -/
theorem IsSigma.exists_nat {r : α × ℕ → Prop} (hr : IsSigma Z (n + 1) r) :
    IsSigma Z (n + 1) (fun x => ∃ y, r (x, y)) := by
  obtain ⟨t, ht, heq⟩ := isSigma_succ_iff.1 hr
  refine isSigma_succ_iff.2 ⟨fun a => t ((a.1, a.2.unpair.1), a.2.unpair.2),
    ht.preimage ((ComputableIn.fst.pair
      ((Primrec.fst.comp Primrec.unpair).computableIn.comp ComputableIn.snd)).pair
      ((Primrec.snd.comp Primrec.unpair).computableIn.comp ComputableIn.snd)), fun x => ?_⟩
  simp only [heq]
  constructor
  · rintro ⟨i, j, hij⟩
    exact ⟨Nat.pair i j, by simpa using hij⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, _, hk⟩

/-- At a positive universal level, an extra universal number quantifier can be
contracted into the leading quantifier. -/
theorem IsPi.forall_nat {r : α × ℕ → Prop} (hr : IsPi Z (n + 1) r) :
    IsPi Z (n + 1) (fun x => ∀ y, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 ((isSigma_not_iff.2 hr).exists_nat.of_eq (by simp))

/-- A universal predicate becomes existential at the next level by adding a dummy variable. -/
theorem IsPi.sigma_succ (hp : IsPi Z n p) : IsSigma Z (n + 1) p :=
  isSigma_succ_iff.2
    ⟨fun a => p a.1, hp.preimage ComputableIn.fst, fun _ => by simp⟩

/-- An existential predicate becomes universal at the next level by adding a dummy variable. -/
theorem IsSigma.pi_succ (hp : IsSigma Z n p) : IsPi Z (n + 1) p := by
  exact isPi_succ_iff.2
    ⟨fun a => p a.1, hp.preimage ComputableIn.fst, fun _ => by simp⟩

/-- Existential pointclasses increase with the level. -/
theorem IsSigma.succ (hp : IsSigma Z n p) : IsSigma Z (n + 1) p := by
  induction n generalizing α with
  | zero => exact hp.one_of_zero
  | succ n ih =>
    obtain ⟨r, hr, heq⟩ := isSigma_succ_iff.1 hp
    exact isSigma_succ_iff.2 ⟨r, isSigma_not_iff.1 (ih (isSigma_not_iff.2 hr)), heq⟩

/-- Universal pointclasses increase with the level. -/
theorem IsPi.succ (hp : IsPi Z n p) : IsPi Z (n + 1) p :=
  isSigma_not_iff.1 (isSigma_not_iff.2 hp).succ

/-- An existential predicate belongs to both pointclasses at the next level. -/
theorem IsSigma.delta_succ (hp : IsSigma Z n p) : IsDelta Z (n + 1) p :=
  isDelta_iff.2 ⟨hp.succ, hp.pi_succ⟩

/-- A universal predicate belongs to both pointclasses at the next level. -/
theorem IsPi.delta_succ (hp : IsPi Z n p) : IsDelta Z (n + 1) p :=
  isDelta_iff.2 ⟨hp.sigma_succ, hp.succ⟩

/-- Existential pointclasses are monotone in the level. -/
theorem IsSigma.of_le (hp : IsSigma Z n p) (hnm : n ≤ m) : IsSigma Z m p := by
  induction hnm with
  | refl => exact hp
  | step _ ih => exact ih.succ

/-- Universal pointclasses are monotone in the level. -/
theorem IsPi.of_le (hp : IsPi Z n p) (hnm : n ≤ m) : IsPi Z m p :=
  isSigma_not_iff.1 ((isSigma_not_iff.2 hp).of_le hnm)

/-- Intersection pointclasses are monotone in the level. -/
theorem IsDelta.of_le (hp : IsDelta Z n p) (hnm : n ≤ m) : IsDelta Z m p := by
  obtain ⟨hpS, hpP⟩ := isDelta_iff.1 hp
  exact isDelta_iff.2 ⟨hpS.of_le hnm, hpP.of_le hnm⟩

-- Guarding a predicate by `o = some y` preserves `Σ⁰ₙ` at every level: at level `0` only the
-- `some` branch is evaluated, and at successor levels negation splits into `o = none` or a
-- negated `some` branch.
private theorem sigma_option_some {β : Type*} [Primcodable β] {r : α × β → Prop}
    (hr : IsSigma Z n r) :
    IsSigma Z n (fun a : α × Option β => ∃ y, a.2 = some y ∧ r (a.1, y)) := by
  classical
  induction n generalizing α β with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hr
    have hcases : ComputableIn {Z.oracle}
        (fun a : α × Option β =>
          Option.casesOn (motive := fun _ => Bool) a.2 false (fun y => b (a.1, y))) :=
      ComputableIn.option_casesOn ComputableIn.snd (ComputableIn.const false)
        (hb.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
    refine isSigma_zero_iff.2 ⟨_, hcases, fun ⟨x, o⟩ => ?_⟩
    cases o <;> simp [heq]
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hr
    have hnone : IsSigma Z n (fun t : (α × Option β) × ℕ => t.1.2 = none) :=
      (isSigma_zero_iff.2
        ⟨fun t => !t.1.2.isSome,
          (Primrec.not.comp Primrec.option_isSome).computableIn.comp
            (ComputableIn.snd.comp ComputableIn.fst),
          fun ⟨⟨_, o⟩, _⟩ => by cases o <;> simp⟩).of_le (Nat.zero_le n)
    have hsome : IsSigma Z n
        (fun t : (α × Option β) × ℕ => ∃ y, t.1.2 = some y ∧ ¬q ((t.1.1, y), t.2)) := by
      have hq' : IsSigma Z n (fun u : (α × ℕ) × β => ¬q ((u.1.1, u.2), u.1.2)) :=
        (isSigma_not_iff.2 hq).preimage
          (((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd).pair
            (ComputableIn.snd.comp ComputableIn.fst))
      exact (ih hq').preimage
        (((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd).pair
          (ComputableIn.snd.comp ComputableIn.fst))
    refine isSigma_succ_iff.2
      ⟨fun t => ∃ y, t.1.2 = some y ∧ q ((t.1.1, y), t.2),
        isSigma_not_iff.1 ((hnone.or hsome).of_eq fun ⟨⟨x, o⟩, w⟩ => ?_),
        fun ⟨x, o⟩ => ?_⟩
    · cases o <;> simp
    · cases o <;> simp [heq]

/-- At a positive existential level, an existential quantifier over any primitive-codable type
contracts into the leading number quantifier via `Encodable.decode`. -/
theorem IsSigma.exists {β : Type*} [Primcodable β] {r : α × β → Prop}
    (hr : IsSigma Z (n + 1) r) :
    IsSigma Z (n + 1) (fun x => ∃ y, r (x, y)) := by
  have hdec : IsSigma Z (n + 1)
      (fun a : α × ℕ => ∃ y, Encodable.decode (α := β) a.2 = some y ∧ r (a.1, y)) :=
    (sigma_option_some hr).preimage
      (ComputableIn.fst.pair (Computable.decode.computableIn.comp ComputableIn.snd))
  refine hdec.exists_nat.of_eq fun x => ⟨fun ⟨_, y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ?_⟩
  exact ⟨Encodable.encode y, y, Encodable.encodek y, hy⟩

/-- At a positive universal level, a universal quantifier over any primitive-codable type
contracts into the leading number quantifier via `Encodable.decode`. -/
theorem IsPi.forall {β : Type*} [Primcodable β] {r : α × β → Prop}
    (hr : IsPi Z (n + 1) r) :
    IsPi Z (n + 1) (fun x => ∀ y, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 ((isSigma_not_iff.2 hr).exists.of_eq (by simp))

-- Bounded existential and universal closure must be proved together by induction on `n`:
-- bounded universal closure at `n + 1` packages the `bound x` witnesses into a `List ℕ` and
-- negates the resulting bounded universal `Π⁰ₙ` body into a bounded existential `Σ⁰ₙ` body.
private theorem sigma_exists_lt_and_forall_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsSigma Z n (fun x => ∃ y < bound x, r (x, y)) ∧
      IsSigma Z n (fun x => ∀ y < bound x, r (x, y)) := by
  classical
  induction n generalizing α with
  | zero =>
    obtain ⟨b, hcomp, heq⟩ := isSigma_zero_iff.1 hr
    have hlist : ComputableIn {Z.oracle}
        (fun x => (List.range (bound x)).map (fun y => b (x, y))) :=
      (ComputableIn₂.list_range_map (f := fun x y => b (x, y)) hcomp).comp
        (ComputableIn.id.pair hb)
    have htrue : PrimrecPred (fun a : Bool => a = true) :=
      Primrec.eq.comp Primrec.id (Primrec.const true)
    have hex : PrimrecPred (fun L : List Bool => ∃ a ∈ L, a = true) :=
      PrimrecPred.exists_mem_list htrue
    have hall : PrimrecPred (fun L : List Bool => ∀ a ∈ L, a = true) :=
      PrimrecPred.forall_mem_list htrue
    refine ⟨isSigma_zero_iff.2 ⟨_, hex.decide.computableIn.comp hlist, fun x => by simp [heq]⟩,
      isSigma_zero_iff.2 ⟨_, hall.decide.computableIn.comp hlist, fun x => by simp [heq]⟩⟩
  | succ n ih =>
    have hlt : IsSigma Z (n + 1) (fun a : α × ℕ => a.2 < bound a.1) :=
      (isSigma_zero_iff.2
        ⟨fun a : α × ℕ => decide (a.2 < bound a.1),
          Primrec.nat_lt.decide.computableIn.comp
            (ComputableIn.snd.pair (hb.comp ComputableIn.fst)),
          fun _ => decide_eq_true_iff⟩).of_le (Nat.zero_le (n + 1))
    refine ⟨((hlt.and hr).exists_nat).of_eq (fun _ => Iff.rfl), ?_⟩
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hr
    have hq' : IsSigma Z n
        (fun t : (α × List ℕ) × ℕ => ¬q ((t.1.1, t.2), List.getD t.1.2 t.2 0)) :=
      (isSigma_not_iff.2 hq).preimage
        (((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd).pair
          ((Primrec.list_getD 0).computableIn.comp
            ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd)))
    have hbody : IsPi Z n
        (fun u : α × List ℕ =>
          ∀ y < bound u.1, q ((u.1, y), List.getD u.2 y 0)) :=
      isSigma_not_iff.1
        (((ih hq' (hb.comp ComputableIn.fst)).1).of_eq fun _ => by simp)
    refine hbody.sigma_succ.exists.of_eq fun x => ?_
    simp only [heq]
    constructor
    · rintro ⟨l, hl⟩ y hy
      exact ⟨List.getD l y 0, hl y hy⟩
    · intro h
      let w : ℕ → ℕ := fun y => if hy : y < bound x then Classical.choose (h y hy) else 0
      refine ⟨(List.range (bound x)).map w, fun y hy => ?_⟩
      have hget : List.getD ((List.range (bound x)).map w) y 0 = w y := by
        simp [List.getD_eq_getElem?_getD, hy]
      rw [hget]
      simpa [w, hy] using Classical.choose_spec (h y hy)

/-- Existential pointclasses are closed under strict bounded existential number quantifiers. -/
theorem IsSigma.exists_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsSigma Z n (fun x => ∃ y < bound x, r (x, y)) :=
  (sigma_exists_lt_and_forall_lt hr hb).1

/-- Existential pointclasses are closed under strict bounded universal number quantifiers. -/
theorem IsSigma.forall_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsSigma Z n (fun x => ∀ y < bound x, r (x, y)) :=
  (sigma_exists_lt_and_forall_lt hr hb).2

/-- Universal pointclasses are closed under strict bounded existential number quantifiers. -/
theorem IsPi.exists_lt {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsPi Z n (fun x => ∃ y < bound x, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 (((isSigma_not_iff.2 hr).forall_lt hb).of_eq (by simp))

/-- Universal pointclasses are closed under strict bounded universal number quantifiers. -/
theorem IsPi.forall_lt {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsPi Z n (fun x => ∀ y < bound x, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 (((isSigma_not_iff.2 hr).exists_lt hb).of_eq (by simp))

/-- Intersection pointclasses are closed under strict bounded existential number quantifiers. -/
theorem IsDelta.exists_lt {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsDelta Z n (fun x => ∃ y < bound x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.exists_lt hb, hrP.exists_lt hb⟩

/-- Intersection pointclasses are closed under strict bounded universal number quantifiers. -/
theorem IsDelta.forall_lt {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsDelta Z n (fun x => ∀ y < bound x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.forall_lt hb, hrP.forall_lt hb⟩

/-- Existential pointclasses are closed under non-strict bounded existential number quantifiers. -/
theorem IsSigma.exists_le {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsSigma Z n (fun x => ∃ y ≤ bound x, r (x, y)) :=
  (hr.exists_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Existential pointclasses are closed under non-strict bounded universal number quantifiers. -/
theorem IsSigma.forall_le {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsSigma Z n (fun x => ∀ y ≤ bound x, r (x, y)) :=
  (hr.forall_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Universal pointclasses are closed under non-strict bounded existential number quantifiers. -/
theorem IsPi.exists_le {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsPi Z n (fun x => ∃ y ≤ bound x, r (x, y)) :=
  (hr.exists_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Universal pointclasses are closed under non-strict bounded universal number quantifiers. -/
theorem IsPi.forall_le {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsPi Z n (fun x => ∀ y ≤ bound x, r (x, y)) :=
  (hr.forall_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Intersection pointclasses are closed under non-strict bounded existential number quantifiers. -/
theorem IsDelta.exists_le {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsDelta Z n (fun x => ∃ y ≤ bound x, r (x, y)) :=
  (hr.exists_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Intersection pointclasses are closed under non-strict bounded universal number quantifiers. -/
theorem IsDelta.forall_le {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {bound : α → ℕ} (hb : ComputableIn {Z.oracle} bound) :
    IsDelta Z n (fun x => ∀ y ≤ bound x, r (x, y)) :=
  (hr.forall_lt (Primrec.succ.computableIn.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

end TauCeti.ArithmeticalHierarchy
