/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift
public import TauCeti.Combinatorics.Network.Flow

/-!
# Closing a terminal assignment with a return arrow

Adjoining a fresh tagged arrow from the sink to the source turns a bounded terminal assignment
into a circulation. Its value is exactly the value on the return arrow. Fixing that arrow's
bounds to `[q, q]` prescribes the terminal value; bounds `[a, b]` prescribe a value interval.
The original arrows retain their identities, even if there are already arrows from sink to
source. Signed bounds and negative terminal values are allowed.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- Adjoin one tagged arrow `t → s`, distinct from all original arrows. -/
abbrev ReturnHom (Q : V → V → Type v) (s t : V) (x y : V) : Type v :=
  Q x y ⊕ PLift (x = t ∧ y = s)

noncomputable instance ReturnHom.instFintype [∀ x y, Fintype (Q x y)] (s t x y : V) :
    Fintype (ReturnHom Q s t x y) := by
  classical
  exact inferInstanceAs (Fintype (Q x y ⊕ PLift (x = t ∧ y = s)))

namespace ReturnHom

variable {s t : V}

/-- An original arrow in the enlarged family. -/
def original {x y : V} (e : Q x y) : ReturnHom Q s t x y := Sum.inl e

/-- The new return arrow from sink to source. -/
def back (Q : V → V → Type v) (s t : V) : ReturnHom Q s t t s :=
  Sum.inr ⟨rfl, rfl⟩

@[simp]
theorem original_inj {x y : V} {e e' : Q x y} :
    original (s := s) (t := t) e = original e' ↔ e = e' := Sum.inl.inj_iff

@[simp]
theorem original_ne_back (e : Q t s) : original e ≠ back Q s t := by
  simp [original, back]

@[simp]
theorem back_ne_original (e : Q t s) : back Q s t ≠ original e := by
  simp [original, back]

/-- A property of enlarged arrows amounts to a property of the original arrows and of the
single return arrow. -/
theorem forall_iff {P : ∀ ⦃x y⦄, ReturnHom Q s t x y → Prop} :
    (∀ ⦃x y⦄ (e : ReturnHom Q s t x y), P e) ↔
      (∀ ⦃x y⦄ (e : Q x y), P (original e)) ∧ P (back Q s t) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h _, h _⟩, ?_⟩
  rintro ⟨ho, hb⟩ x y (e | ⟨⟨rfl, rfl⟩⟩)
  · exact ho e
  · exact hb

/-- Extend an assignment by giving the new return arrow value `q`. This also extends bounds. -/
def extend (f : Assignment Q K) (q : K) : Assignment (ReturnHom Q s t) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ f e) (fun _ ↦ q) e

/-- Restriction to the original arrows. -/
def restrict (g : Assignment (ReturnHom Q s t) K) : Assignment Q K :=
  fun _ _ e ↦ g (original e)

@[simp]
theorem extend_original (f : Assignment Q K) (q : K) {x y : V} (e : Q x y) :
    extend (s := s) (t := t) f q (original e) = f e := (rfl)

@[simp]
theorem extend_back (f : Assignment Q K) (q : K) :
    extend f q (back Q s t) = q := (rfl)

@[simp]
theorem restrict_apply (g : Assignment (ReturnHom Q s t) K) {x y : V} (e : Q x y) :
    restrict g e = g (original e) := (rfl)

@[simp]
theorem restrict_extend (f : Assignment Q K) (q : K) :
    restrict (extend (s := s) (t := t) f q) = f := (rfl)

/-- Restriction and the value on the return arrow determine an enlarged assignment. -/
@[simp]
theorem extend_restrict (g : Assignment (ReturnHom Q s t) K) :
    extend (restrict g) (g (back Q s t)) = g := by
  funext x y e
  cases e with
  | inl e => rfl
  | inr h => rcases h with ⟨⟨rfl, rfl⟩⟩; rfl

/-- The enlarged bounds are exactly the original bounds and the interval on the return value. -/
theorem extend_mem_Icc [Preorder K] (f lo hi : Assignment Q K) (q a b : K) :
    extend (s := s) (t := t) f q ∈ Set.Icc (extend lo a) (extend hi b) ↔
      f ∈ Set.Icc lo hi ∧ q ∈ Set.Icc a b := by
  simp only [Set.mem_Icc, Pi.le_def, forall_iff, extend_original, extend_back]
  tauto

section Sums

variable [∀ x y, Fintype (Q x y)] [AddCommMonoid K]

open Classical in
/-- The sum over one enlarged arrow carrier includes the return value exactly at `t → s`. -/
theorem sum_extend (f : Assignment Q K) (q : K) (x y : V) :
    ∑ e : ReturnHom Q s t x y, extend f q e =
      (∑ e : Q x y, f e) + if x = t ∧ y = s then q else 0 := by
  rw [Fintype.sum_sum_type]
  by_cases h : x = t ∧ y = s
  · simp only [extend, Sum.elim_inl, Sum.elim_inr, ite_eq_left h]
    rw [Fintype.sum_subsingleton _ (PLift.up h)]
  · have : IsEmpty (PLift (x = t ∧ y = s)) := ⟨fun p ↦ h p.down⟩
    simp [extend, h]

end Sums

section Excess

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

open Classical in
/-- Adding the return arrow adds its value to excess at the source and subtracts it at the sink.
This formula also applies when the two terminals coincide, making the new arrow a loop. -/
theorem excessAt_extend (f : Assignment Q K) (q : K) (x : V) :
    excessAt (extend (s := s) (t := t) f q) x =
      excessAt f x + (if x = s then q else 0) - (if x = t then q else 0) := by
  classical
  simp only [excessAt_def, sum_extend, Finset.sum_add_distrib]
  simp [ite_and, Finset.sum_ite_irrel]
  abel

/-- The return extension is a circulation exactly when the original assignment is conserved
away from the terminals and its sink excess is the return value. -/
theorem isCirculation_extend_iff (hst : s ≠ t) (f : Assignment Q K) (q : K) :
    IsCirculation (extend (s := s) (t := t) f q) ↔
      (∀ x, x ≠ s → x ≠ t → excessAt f x = 0) ∧ excessAt f t = q := by
  classical
  rw [isCirculation_iff]
  constructor
  · intro h
    exact ⟨fun x hxs hxt ↦ by simpa [excessAt_extend, hxs, hxt] using h x,
      by simpa [excessAt_extend, hst.symm, sub_eq_zero] using h t⟩
  · rintro ⟨hc, ht⟩ x
    by_cases hxs : x = s
    · subst x
      simp [excessAt_extend, hst, excessAt_source_eq_neg_sink f hc, ht]
    · by_cases hxt : x = t
      · subst x
        simp [excessAt_extend, hst.symm, ht]
      · simp [excessAt_extend, hxs, hxt, hc x hxs hxt]

end Excess

end ReturnHom

namespace Network

/-- Adjoin a fresh return arrow `t → s` with bounds `[a, b]`, inheriting all original bounds.
The carrier is reducible so bundled and unbundled assignments use the same arrow identities. -/
@[expose, reducible] def withReturnArrow [LE K] (N : Network K V) (s t : V) (a b : K)
    (hab : a ≤ b) : Network K V where
  Hom := ReturnHom N.Hom s t
  lower := ReturnHom.extend N.lower a
  upper := ReturnHom.extend N.upper b
  lower_le_upper := by
    intro x y e
    exact (ReturnHom.forall_iff (Q := N.Hom) (s := s) (t := t)
      (P := fun {_ _} e ↦ ReturnHom.extend N.lower a e ≤ ReturnHom.extend N.upper b e)).2
        ⟨fun _ _ e ↦ N.lower_le_upper e, hab⟩ e

@[simp]
theorem withReturnArrow_Hom [LE K] (N : Network K V) (s t : V) (a b : K) (hab : a ≤ b) :
    (N.withReturnArrow s t a b hab).Hom = ReturnHom N.Hom s t := (rfl)

@[simp]
theorem withReturnArrow_lower [LE K] (N : Network K V) (s t : V) (a b : K) (hab : a ≤ b) :
    (N.withReturnArrow s t a b hab).lower = ReturnHom.extend N.lower a := (rfl)

@[simp]
theorem withReturnArrow_upper [LE K] (N : Network K V) (s t : V) (a b : K) (hab : a ≤ b) :
    (N.withReturnArrow s t a b hab).upper = ReturnHom.extend N.upper b := (rfl)

end Network

namespace BoundedFlow

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]
variable {s t : V}

open ReturnHom

/-- Bounded terminal assignments with value in `[a, b]` correspond to bounded circulations with
one extra return arrow of bounds `[a, b]`. No ordering assumption on these endpoints is needed
for the equivalence: either side may be empty. -/
def returnIntervalEquiv (hst : s ≠ t) (lo hi : Assignment Q K) (a b : K) :
    {f : BoundedFlow lo hi s t // f.val ∈ Set.Icc a b} ≃
      ExcessFlow (extend (s := s) (t := t) lo a) (extend hi b) 0 where
  toFun f := ⟨extend f.val.toFun f.val.val,
    (extend_mem_Icc _ _ _ _ _ _).2 ⟨f.val.mem_Icc, f.property⟩,
    funext ((isCirculation_iff _).1
      ((isCirculation_extend_iff hst _ _).2 ⟨f.val.conserve, f.val.val_def.symm⟩))⟩
  invFun g := by
    have hg : IsCirculation g.val := (isCirculation_iff _).2 fun x ↦ g.excessAt_eq x
    rw [← extend_restrict g.val, isCirculation_extend_iff hst] at hg
    have hb := g.mem_Icc
    rw [← extend_restrict g.val, extend_mem_Icc] at hb
    exact ⟨⟨restrict g.val, hb.1, hg.1⟩, by simpa only [val_def, hg.2] using hb.2⟩
  left_inv f := by
    apply Subtype.ext
    exact BoundedFlow.ext (restrict_extend (s := s) (t := t) f.val.toFun f.val.val)
  right_inv g := by
    apply Subtype.ext
    have hg : IsCirculation g.val := (isCirculation_iff _).2 fun x ↦ g.excessAt_eq x
    rw [← extend_restrict g.val, isCirculation_extend_iff hst] at hg
    simpa only [val_def] using
      (congrArg (extend (restrict g.val)) hg.2).trans (extend_restrict g.val)

@[simp]
theorem returnIntervalEquiv_apply_original (hst : s ≠ t) (lo hi : Assignment Q K) (a b : K)
    (f : {f : BoundedFlow lo hi s t // f.val ∈ Set.Icc a b}) {x y : V} (e : Q x y) :
    (returnIntervalEquiv hst lo hi a b f).val (original e) = f.val.toFun e := (rfl)

@[simp]
theorem returnIntervalEquiv_apply_back (hst : s ≠ t) (lo hi : Assignment Q K) (a b : K)
    (f : {f : BoundedFlow lo hi s t // f.val ∈ Set.Icc a b}) :
    (returnIntervalEquiv hst lo hi a b f).val (back Q s t) = f.val.val := (rfl)

@[simp]
theorem returnIntervalEquiv_symm_apply_toFun (hst : s ≠ t) (lo hi : Assignment Q K) (a b : K)
    (g : ExcessFlow (extend (s := s) (t := t) lo a) (extend hi b) 0) :
    ((returnIntervalEquiv hst lo hi a b).symm g).val.toFun = restrict g.val := (rfl)

/-- Restricting a circulation recovers its return-arrow value as terminal value. -/
@[simp]
theorem returnIntervalEquiv_symm_apply_val (hst : s ≠ t) (lo hi : Assignment Q K) (a b : K)
    (g : ExcessFlow (extend (s := s) (t := t) lo a) (extend hi b) 0) :
    ((returnIntervalEquiv hst lo hi a b).symm g).val.val = g.val (back Q s t) := by
  have hg : IsCirculation g.val := (isCirculation_iff _).2 fun x ↦ g.excessAt_eq x
  rw [← extend_restrict g.val, isCirculation_extend_iff hst] at hg
  simpa only [val_def, returnIntervalEquiv_symm_apply_toFun] using hg.2

end BoundedFlow

namespace BoundedFlow

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [PartialOrder K]
variable {s t : V}

open ReturnHom

/-- Prescribing terminal value `q` is equivalent to fixing the new return arrow to `q`.
In particular, `q` may be negative. -/
def returnEquiv (hst : s ≠ t) (lo hi : Assignment Q K) (q : K) :
    {f : BoundedFlow lo hi s t // f.val = q} ≃
      ExcessFlow (extend (s := s) (t := t) lo q) (extend hi q) 0 :=
  (Equiv.subtypeEquivRight fun _ ↦ by simp).trans (returnIntervalEquiv hst lo hi q q)

@[simp]
theorem returnEquiv_apply_original (hst : s ≠ t) (lo hi : Assignment Q K) (q : K)
    (f : {f : BoundedFlow lo hi s t // f.val = q}) {x y : V} (e : Q x y) :
    (returnEquiv hst lo hi q f).val (original e) = f.val.toFun e := by
  simp [returnEquiv]

@[simp]
theorem returnEquiv_apply_back (hst : s ≠ t) (lo hi : Assignment Q K) (q : K)
    (f : {f : BoundedFlow lo hi s t // f.val = q}) :
    (returnEquiv hst lo hi q f).val (back Q s t) = q := by
  simpa [returnEquiv] using f.property

@[simp]
theorem returnEquiv_symm_apply_toFun (hst : s ≠ t) (lo hi : Assignment Q K) (q : K)
    (g : ExcessFlow (extend (s := s) (t := t) lo q) (extend hi q) 0) :
    ((returnEquiv hst lo hi q).symm g).val.toFun = restrict g.val := by
  simp [returnEquiv]

end BoundedFlow

namespace Flow

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [PartialOrder K]
variable {s t : V}

open ReturnHom

/-- Ordinary flows of nonnegative value `q` correspond to circulations with a return arrow fixed
to `q`. Original lower bounds are zero; the return arrow has lower and upper bound `q`. -/
def returnEquiv (hst : s ≠ t) (cap : Assignment Q K) (q : K) (hq : 0 ≤ q) :
    {f : Flow cap s t // f.val = q} ≃
      ExcessFlow (extend (s := s) (t := t) (0 : Assignment Q K) q) (extend cap q) 0 where
  toFun f := BoundedFlow.returnEquiv hst 0 cap q ⟨f.val.toBoundedFlow, f.property⟩
  invFun g := by
    let f := (BoundedFlow.returnEquiv hst 0 cap q).symm g
    exact ⟨{ toBoundedFlow := f.val
             excessAt_sink_nonneg := by rw [← BoundedFlow.val_def, f.property]; exact hq },
      f.property⟩
  left_inv f := by
    apply Subtype.ext
    apply Flow.ext
    simpa only [BoundedFlow.returnEquiv_symm_apply_toFun] using
      congrArg (fun g ↦ g.val.toFun)
        ((BoundedFlow.returnEquiv hst 0 cap q).symm_apply_apply
          ⟨f.val.toBoundedFlow, f.property⟩)
  right_inv g := (BoundedFlow.returnEquiv hst 0 cap q).apply_symm_apply g

@[simp]
theorem returnEquiv_apply_original (hst : s ≠ t) (cap : Assignment Q K) (q : K) (hq : 0 ≤ q)
    (f : {f : Flow cap s t // f.val = q}) {x y : V} (e : Q x y) :
    (returnEquiv hst cap q hq f).val (original e) = f.val.toFun e := by
  simp [returnEquiv]

@[simp]
theorem returnEquiv_apply_back (hst : s ≠ t) (cap : Assignment Q K) (q : K) (hq : 0 ≤ q)
    (f : {f : Flow cap s t // f.val = q}) :
    (returnEquiv hst cap q hq f).val (back Q s t) = q := by
  simp [returnEquiv]

@[simp]
theorem returnEquiv_symm_apply_toFun (hst : s ≠ t) (cap : Assignment Q K) (q : K) (hq : 0 ≤ q)
    (g : ExcessFlow (extend (s := s) (t := t) (0 : Assignment Q K) q) (extend cap q) 0) :
    ((returnEquiv hst cap q hq).symm g).val.toFun = restrict g.val := by
  simp [returnEquiv]

end Flow

/-! ### Negative return values and existing reverse arrows -/

-- The original sink-to-source arrow carries two, while the fresh return arrow carries minus two.
-- Both loops and the existing reverse arrow retain their original identities and values.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun _ _ _ ↦ -3
    let hi : Assignment Q ℤ := fun _ _ _ ↦ 3
    ∃ f : {f : BoundedFlow lo hi false true // f.val = -2},
      (BoundedFlow.returnEquiv (by decide) lo hi (-2) f).val
        (ReturnHom.original (x := true) (y := false) ()) = 2 ∧
      (BoundedFlow.returnEquiv (by decide) lo hi (-2) f).val
        (ReturnHom.back Q false true) = -2 ∧
      (BoundedFlow.returnIntervalEquiv (by decide) lo hi (-3) (-1)
        ⟨f.val, by rw [f.property]; decide⟩).val (ReturnHom.back Q false true) = -2 := by
  intro Q lo hi
  let f : BoundedFlow lo hi false true :=
    { toFun := fun x _ _ ↦ if x then 2 else 0
      mem_Icc := by
        constructor <;> intro x y e <;> cases x <;> norm_num [lo, hi]
      conserve := by intro x hs ht; cases x <;> simp_all }
  have hv : f.val = -2 := by norm_num [BoundedFlow.val_def, excessAt_def, f]
  refine ⟨⟨f, hv⟩, ?_, by simp, ?_⟩
  · simp [f]
  · simp [hv]

-- An ordinary flow with nonzero traffic in both directions closes with a positive return value.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let cap : Assignment Q ℤ := fun _ _ _ ↦ 3
    ∃ f : {f : Flow cap false true // f.val = 1},
      (Flow.returnEquiv (by decide) cap 1 (by decide) f).val
        (ReturnHom.original (x := true) (y := false) ()) = 1 ∧
      (Flow.returnEquiv (by decide) cap 1 (by decide) f).val
        (ReturnHom.back Q false true) = 1 := by
  intro Q cap
  let f : Flow cap false true :=
    { toFun := fun x _ _ ↦ if x then 1 else 2
      mem_Icc := by
        constructor <;> intro x y e <;> cases x <;> norm_num [cap]
      conserve := by intro x hs ht; cases x <;> simp_all
      excessAt_sink_nonneg := by norm_num [excessAt_def] }
  have hv : f.val = 1 := by norm_num [BoundedFlow.val_def, excessAt_def, f]
  exact ⟨⟨f, hv⟩, by simp [f], by simp⟩

end TauCeti
