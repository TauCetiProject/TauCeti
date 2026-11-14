/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic

/-!
# Closure and quantifier contraction for arithmetical pointclasses

Both existential and universal arithmetical pointclasses are closed under finite conjunction
and disjunction, and under implication with the antecedent in the dual class. An additional
existential number quantifier at a positive existential level can be contracted with the
leading quantifier, using Mathlib's pairing of natural numbers; the dual statement holds for
universal levels. Bounded existential and universal number quantifiers with oracle-computable
bounds preserve every pointclass: at positive existential levels, universal bounded
quantification collects a uniform numerical upper bound on the existential witnesses.

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

/-- Implication from a universal antecedent to an existential consequent stays in the
existential pointclass. -/
theorem IsSigma.imp (hp : IsPi Z n p) (hq : IsSigma Z n q) :
    IsSigma Z n (fun x => p x → q x) := by
  classical
  exact ((isSigma_not_iff.2 hp).or hq).of_eq fun _ => imp_iff_not_or.symm

/-- Implication from an existential antecedent to a universal consequent stays in the
universal pointclass. -/
theorem IsPi.imp (hp : IsSigma Z n p) (hq : IsPi Z n q) :
    IsPi Z n (fun x => p x → q x) := by
  classical
  exact isSigma_not_iff.1 ((hp.and (isSigma_not_iff.2 hq)).of_eq fun _ => not_imp.symm)

/-- The intersection pointclass is closed under implication. -/
theorem IsDelta.imp (hp : IsDelta Z n p) (hq : IsDelta Z n q) :
    IsDelta Z n (fun x => p x → q x) := by
  obtain ⟨hpS, hpP⟩ := isDelta_iff.1 hp
  obtain ⟨hqS, hqP⟩ := isDelta_iff.1 hq
  exact isDelta_iff.2 ⟨IsSigma.imp hpP hqS, IsPi.imp hpS hqP⟩

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

-- Bounded existential and universal closure must be established together: universal bounded
-- quantification at `n + 1` collects a uniform upper bound on the existential witnesses and
-- pushes a bounded existential quantifier inside the preceding universal matrix.
private theorem sigma_exists_lt_and_forall_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsSigma Z n (fun x => ∃ y < b x, r (x, y)) ∧
      IsSigma Z n (fun x => ∀ y < b x, r (x, y)) := by
  classical
  induction n generalizing α with
  | zero =>
    have hex0 {t : α × ℕ → Prop} (ht : IsSigma Z 0 t) :
        IsSigma Z 0 (fun x => ∃ y < b x, t (x, y)) := by
      obtain ⟨d, hd, hdeq⟩ := isSigma_zero_iff.1 ht
      have hstep : ComputableIn₂ {Z.oracle} (fun (x : α) (p : ℕ × Bool) => p.2 || d (x, p.1)) :=
        Primrec.or.computableIn.comp <|
          (ComputableIn.snd.comp ComputableIn.snd).pair
            (hd.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd)))
      refine isSigma_zero_iff.2 ⟨fun x =>
        Nat.rec (motive := fun _ => Bool) false (fun y acc => acc || d (x, y)) (b x),
        ComputableIn.nat_rec hb (ComputableIn.const false) hstep, fun x => ?_⟩
      simp only [← hdeq]
      generalize b x = k
      induction k with
      | zero => simp
      | succ k ihk =>
        simp only [Bool.or_eq_true, ihk]
        constructor
        · rintro (⟨y, hy, hdy⟩ | hdk)
          · exact ⟨y, Nat.lt_succ_of_lt hy, hdy⟩
          · exact ⟨k, k.lt_succ_self, hdk⟩
        · rintro ⟨y, hy, hdy⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hlt | rfl
          · exact Or.inl ⟨y, hlt, hdy⟩
          · exact Or.inr hdy
    have hnot : IsSigma Z 0 (fun a => ¬r a) := isSigma_not_iff.2 (isPi_zero_iff.2 hr)
    exact ⟨hex0 hr,
      (isSigma_not_iff.2 (isPi_zero_iff.2 (hex0 hnot))).of_eq fun _ => by simp⟩
  | succ n ih =>
    constructor
    · have hlt : IsSigma Z (n + 1) (fun a : α × ℕ => a.2 < b a.1) :=
        (isSigma_zero_iff.2 ⟨fun a : α × ℕ => decide (a.2 < b a.1),
          Primrec.nat_lt.decide.computableIn.comp
            (ComputableIn.snd.pair (hb.comp ComputableIn.fst)),
          fun _ => decide_eq_true_iff⟩).of_le (Nat.zero_le _)
      exact (hlt.and hr).exists_nat.of_eq fun _ => by simp
    · obtain ⟨q, hq, hreq⟩ := isSigma_succ_iff.1 hr
      have hq' : IsSigma Z n (fun p : ((α × ℕ) × ℕ) × ℕ => ¬q ((p.1.1.1, p.1.2), p.2)) :=
        (isSigma_not_iff.2 hq).preimage <|
          ((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
            (ComputableIn.snd.comp ComputableIn.fst)).pair ComputableIn.snd
      have h₁ : IsSigma Z n (fun v : (α × ℕ) × ℕ => ∀ w < v.1.2, ¬q ((v.1.1, v.2), w)) :=
        (ih hq' (ComputableIn.snd.comp ComputableIn.fst)).2
      have h₂ : IsPi Z n (fun a : α × ℕ => ∀ y < b a.1, ∃ w < a.2, q ((a.1, y), w)) :=
        isSigma_not_iff.1 ((ih h₁ (hb.comp ComputableIn.fst)).1.of_eq fun _ => by simp)
      refine isSigma_succ_iff.2
        ⟨fun a => ∀ y < b a.1, ∃ w < a.2, q ((a.1, y), w), h₂, fun x => ?_⟩
      simp only [hreq]
      generalize b x = m
      constructor
      · intro hm
        induction m with
        | zero => exact ⟨0, by simp⟩
        | succ m ihm =>
          obtain ⟨B, hB⟩ := ihm fun y hy => hm y (Nat.lt_succ_of_lt hy)
          obtain ⟨wm, hwm⟩ := hm m m.lt_succ_self
          refine ⟨max B (wm + 1), fun y hy => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hlt | rfl
          · obtain ⟨w, hwB, hw⟩ := hB y hlt
            exact ⟨w, hwB.trans_le (le_max_left _ _), hw⟩
          · exact ⟨wm, wm.lt_succ_self.trans_le (le_max_right _ _), hwm⟩
      · rintro ⟨B, hB⟩ y hy
        obtain ⟨w, -, hw⟩ := hB y hy
        exact ⟨w, hw⟩

/-- Existential pointclasses are closed under bounded existential number quantifiers with
oracle-computable bounds. -/
theorem IsSigma.exists_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsSigma Z n (fun x => ∃ y < b x, r (x, y)) :=
  (sigma_exists_lt_and_forall_lt hr hb).1

/-- Existential pointclasses are closed under bounded universal number quantifiers with
oracle-computable bounds. -/
theorem IsSigma.forall_lt {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsSigma Z n (fun x => ∀ y < b x, r (x, y)) :=
  (sigma_exists_lt_and_forall_lt hr hb).2

/-- Universal pointclasses are closed under bounded existential number quantifiers with
oracle-computable bounds. -/
theorem IsPi.exists_lt {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsPi Z n (fun x => ∃ y < b x, r (x, y)) :=
  isSigma_not_iff.1 (((isSigma_not_iff.2 hr).forall_lt hb).of_eq fun _ => by simp)

/-- Universal pointclasses are closed under bounded universal number quantifiers with
oracle-computable bounds. -/
theorem IsPi.forall_lt {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsPi Z n (fun x => ∀ y < b x, r (x, y)) := by
  classical
  exact isSigma_not_iff.1 (((isSigma_not_iff.2 hr).exists_lt hb).of_eq fun _ => by simp)

/-- Intersection pointclasses are closed under bounded existential number quantifiers with
oracle-computable bounds. -/
theorem IsDelta.exists_lt {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsDelta Z n (fun x => ∃ y < b x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.exists_lt hb, hrP.exists_lt hb⟩

/-- Intersection pointclasses are closed under bounded universal number quantifiers with
oracle-computable bounds. -/
theorem IsDelta.forall_lt {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsDelta Z n (fun x => ∀ y < b x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.forall_lt hb, hrP.forall_lt hb⟩

/-- Existential pointclasses are closed under inclusive bounded existential number quantifiers
with oracle-computable bounds. -/
theorem IsSigma.exists_le {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsSigma Z n (fun x => ∃ y ≤ b x, r (x, y)) :=
  (hr.exists_lt (ComputableIn.succ.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Existential pointclasses are closed under inclusive bounded universal number quantifiers
with oracle-computable bounds. -/
theorem IsSigma.forall_le {r : α × ℕ → Prop} (hr : IsSigma Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsSigma Z n (fun x => ∀ y ≤ b x, r (x, y)) :=
  (hr.forall_lt (ComputableIn.succ.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Universal pointclasses are closed under inclusive bounded existential number quantifiers
with oracle-computable bounds. -/
theorem IsPi.exists_le {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsPi Z n (fun x => ∃ y ≤ b x, r (x, y)) :=
  (hr.exists_lt (ComputableIn.succ.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Universal pointclasses are closed under inclusive bounded universal number quantifiers
with oracle-computable bounds. -/
theorem IsPi.forall_le {r : α × ℕ → Prop} (hr : IsPi Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsPi Z n (fun x => ∀ y ≤ b x, r (x, y)) :=
  (hr.forall_lt (ComputableIn.succ.comp hb)).of_eq fun _ => by simp [Nat.lt_succ_iff]

/-- Intersection pointclasses are closed under inclusive bounded existential number quantifiers
with oracle-computable bounds. -/
theorem IsDelta.exists_le {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsDelta Z n (fun x => ∃ y ≤ b x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.exists_le hb, hrP.exists_le hb⟩

/-- Intersection pointclasses are closed under inclusive bounded universal number quantifiers
with oracle-computable bounds. -/
theorem IsDelta.forall_le {r : α × ℕ → Prop} (hr : IsDelta Z n r)
    {b : α → ℕ} (hb : ComputableIn {Z.oracle} b) :
    IsDelta Z n (fun x => ∀ y ≤ b x, r (x, y)) := by
  obtain ⟨hrS, hrP⟩ := isDelta_iff.1 hr
  exact isDelta_iff.2 ⟨hrS.forall_le hb, hrP.forall_le hb⟩

end TauCeti.ArithmeticalHierarchy
