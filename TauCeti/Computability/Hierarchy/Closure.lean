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
and disjunction. An additional existential number quantifier at a positive existential level
can be contracted with the leading quantifier, using Mathlib's pairing of natural numbers;
the dual statement holds for universal levels. These operations manipulate normal forms
without increasing their alternating quantifier depth.

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

end TauCeti.ArithmeticalHierarchy
