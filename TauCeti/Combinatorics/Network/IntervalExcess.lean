/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift

/-!
# Interval excess as bounded circulation

Adjoin one fresh vertex to a directed network and one arrow from each original vertex to the
fresh vertex. Giving that arrow the original vertex's excess turns an interval-excess assignment
into a circulation; its bounds are precisely the bounds on vertex excess. Restriction to the
original arrows is the inverse. Negative bounds, parallel arrows and loops are allowed.

`ExcessIntervalFlow.circulationEquiv` preserves every original arrow value. Conservation at the
fresh vertex follows from `sum_excessAt`, including when the original vertex type is empty.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- The original arrows between vertices `some v`, with one arrow from each `some v` to the
fresh vertex `none` and no arrows leaving `none`. The family is exposed to identify its indexed
arrow carriers with the original carriers. -/
@[expose] def IntervalExcessHom (Q : V → V → Type v) : Option V → Option V → Type v
  | some x, some y => Q x y
  | some _, none => PUnit
  | none, _ => PEmpty

instance IntervalExcessHom.instFintype [∀ x y, Fintype (Q x y)] :
    ∀ x y, Fintype (IntervalExcessHom Q x y)
  | some _, some _ => inferInstanceAs (Fintype (Q _ _))
  | some _, none => inferInstanceAs (Fintype PUnit)
  | none, _ => inferInstanceAs (Fintype PEmpty)

namespace IntervalExcessHom

/-- An original arrow in the enlarged network. -/
def original {x y : V} (e : Q x y) : IntervalExcessHom Q (some x) (some y) := e

/-- The auxiliary arrow from `some v` to `none`. -/
def auxiliary (v : V) : IntervalExcessHom Q (some v) none := PUnit.unit

instance instSubsingletonAuxiliary (v : V) :
    Subsingleton (IntervalExcessHom Q (some v) none) :=
  inferInstanceAs (Subsingleton PUnit)

/-- No arrow leaves the fresh vertex. -/
instance instIsEmptyFromNone (y : Option V) : IsEmpty (IntervalExcessHom Q none y) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- A property of all enlarged arrows is a property of the original and auxiliary arrows. -/
theorem forall_iff {P : ∀ ⦃x y⦄, IntervalExcessHom Q x y → Prop} :
    (∀ ⦃x y⦄ (e : IntervalExcessHom Q x y), P e) ↔
      (∀ ⦃x y⦄ (e : Q x y), P (original e)) ∧ ∀ v, P (auxiliary v) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h _, fun v ↦ h _⟩, ?_⟩
  rintro ⟨ho, ha⟩ (_ | x) (_ | y) e
  · exact e.elim
  · exact e.elim
  · cases e
    exact ha x
  · exact ho e

end IntervalExcessHom

/-- Extend an original assignment by giving the auxiliary arrow at `v` the value `c v`.
This also extends lower and upper bounds. -/
def intervalExcessExtend (f : Assignment Q K) (c : V → K) :
    Assignment (IntervalExcessHom Q) K
  | some _, some _, e => f e
  | some v, none, _ => c v
  | none, _, e => e.elim

/-- Restrict an enlarged assignment to the original arrows. -/
def intervalExcessRestrict (g : Assignment (IntervalExcessHom Q) K) : Assignment Q K :=
  fun _ _ e ↦ g (IntervalExcessHom.original e)

@[simp]
theorem intervalExcessExtend_original (f : Assignment Q K) (c : V → K) {x y : V}
    (e : Q x y) : intervalExcessExtend f c (IntervalExcessHom.original e) = f e := (rfl)

@[simp]
theorem intervalExcessExtend_auxiliary (f : Assignment Q K) (c : V → K) (v : V) :
    intervalExcessExtend f c (IntervalExcessHom.auxiliary v) = c v := (rfl)

@[simp]
theorem intervalExcessRestrict_apply (g : Assignment (IntervalExcessHom Q) K) {x y : V}
    (e : Q x y) : intervalExcessRestrict g e = g (IntervalExcessHom.original e) := (rfl)

@[simp]
theorem intervalExcessRestrict_extend (f : Assignment Q K) (c : V → K) :
    intervalExcessRestrict (intervalExcessExtend f c) = f := (rfl)

/-- Restriction together with the values on auxiliary arrows determines the full assignment. -/
theorem intervalExcessExtend_restrict (g : Assignment (IntervalExcessHom Q) K) :
    intervalExcessExtend (intervalExcessRestrict g)
      (fun v ↦ g (IntervalExcessHom.auxiliary v)) = g := by
  funext x y e
  cases x with
  | none => exact e.elim
  | some x =>
    cases y with
    | none => cases e; rfl
    | some y => rfl

/-- The enlarged bounds impose the original arrow bounds and the auxiliary vertex bounds. -/
theorem intervalExcessExtend_mem_Icc [Preorder K] (f lo hi : Assignment Q K) (c a b : V → K) :
    intervalExcessExtend f c ∈ Set.Icc (intervalExcessExtend lo a) (intervalExcessExtend hi b) ↔
      f ∈ Set.Icc lo hi ∧ c ∈ Set.Icc a b := by
  simp only [Set.mem_Icc, Pi.le_def, IntervalExcessHom.forall_iff,
    intervalExcessExtend_original, intervalExcessExtend_auxiliary]
  tauto

namespace Network

/-- Enlarge a bounded network by one fresh vertex and auxiliary arrows with bounds `[a v, b v]`.
The dependent arrow family is reducible so callers can use the same original and auxiliary
arrows in the bundled and unbundled presentations. -/
@[expose, reducible] def intervalExcess [LE K] (N : Network K V) (a b : V → K)
    (hab : a ≤ b) : Network K (Option V) where
  Hom := IntervalExcessHom N.Hom
  lower := intervalExcessExtend N.lower a
  upper := intervalExcessExtend N.upper b
  lower_le_upper := by
    intro x y e
    exact (IntervalExcessHom.forall_iff (Q := N.Hom)
      (P := fun {_ _} e ↦ intervalExcessExtend N.lower a e ≤ intervalExcessExtend N.upper b e)).2
        ⟨fun _ _ e ↦ by simpa using N.lower_le_upper e, fun v ↦ by simpa using hab v⟩ e

@[simp]
theorem intervalExcess_Hom [LE K] (N : Network K V) (a b : V → K) (hab : a ≤ b) :
    (N.intervalExcess a b hab).Hom = IntervalExcessHom N.Hom := (rfl)

@[simp]
theorem intervalExcess_lower [LE K] (N : Network K V) (a b : V → K) (hab : a ≤ b) :
    (N.intervalExcess a b hab).lower = intervalExcessExtend N.lower a := (rfl)

@[simp]
theorem intervalExcess_upper [LE K] (N : Network K V) (a b : V → K) (hab : a ≤ b) :
    (N.intervalExcess a b hab).upper = intervalExcessExtend N.upper b := (rfl)

end Network

/-- Summing over original enlarged arrows is summing over the original arrow carrier. -/
private theorem IntervalExcessHom.sum_original [AddCommMonoid K]
    [∀ x y, Fintype (Q x y)] {x y : V}
    (g : IntervalExcessHom Q (some x) (some y) → K) :
    ∑ e, g e = ∑ e : Q x y, g (original e) :=
  (Fintype.sum_equiv (Equiv.refl (Q x y)) _ _ fun _ ↦ rfl).symm

/-- A sum over the auxiliary arrow is its single value. -/
private theorem IntervalExcessHom.sum_auxiliary [AddCommMonoid K]
    [∀ x y, Fintype (Q x y)] (v : V)
    (g : IntervalExcessHom Q (some v) none → K) : ∑ e, g e = g (auxiliary v) :=
  Fintype.sum_subsingleton g _

section Excess

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-- At an original vertex, enlarged excess is original excess minus the auxiliary value. -/
theorem IntervalExcessHom.excessAt_some (g : Assignment (IntervalExcessHom Q) K) (v : V) :
    excessAt g (some v) = excessAt (intervalExcessRestrict g) v -
      g (IntervalExcessHom.auxiliary v) := by
  simp only [excessAt_def, Fintype.sum_option, Fintype.sum_empty, zero_add,
    IntervalExcessHom.sum_original, IntervalExcessHom.sum_auxiliary, intervalExcessRestrict_apply]
  abel

/-- Excess at the fresh vertex is the total value of the auxiliary arrows. -/
theorem IntervalExcessHom.excessAt_none (g : Assignment (IntervalExcessHom Q) K) :
    excessAt g none = ∑ v, g (IntervalExcessHom.auxiliary v) := by
  simp [excessAt_def, Fintype.sum_option, IntervalExcessHom.sum_auxiliary]

/-- Conservation at the original vertices forces each auxiliary value to equal original excess. -/
theorem IntervalExcessHom.auxiliary_eq_excessAt {g : Assignment (IntervalExcessHom Q) K}
    (hg : IsCirculation g) (v : V) :
    g (auxiliary v) = excessAt (intervalExcessRestrict g) v := by
  have h := (isCirculation_iff g).1 hg (some v)
  rw [excessAt_some, sub_eq_zero] at h
  exact h.symm

/-- Sending original excess along each auxiliary arrow gives a circulation. -/
theorem isCirculation_intervalExcessExtend (f : Assignment Q K) :
    IsCirculation (intervalExcessExtend f (excessAt f)) := by
  refine (isCirculation_iff _).2 ?_
  rintro (_ | v)
  · simpa only [IntervalExcessHom.excessAt_none, intervalExcessExtend_auxiliary]
      using sum_excessAt f
  · simp [IntervalExcessHom.excessAt_some]

namespace ExcessIntervalFlow

variable [Preorder K]

/-- An interval-excess assignment is equivalently a bounded circulation on the network with one
fresh vertex. The auxiliary arrow at each vertex carries that vertex's original excess. -/
def circulationEquiv (lo hi : Assignment Q K) (a b : V → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessFlow (intervalExcessExtend lo a) (intervalExcessExtend hi b) 0 where
  toFun f := ⟨intervalExcessExtend f.val (excessAt f.val),
    (intervalExcessExtend_mem_Icc _ _ _ _ _ _).2 f.property,
    funext ((isCirculation_iff _).1 (isCirculation_intervalExcessExtend f.val))⟩
  invFun g := ⟨intervalExcessRestrict g.val, by
    have hg : IsCirculation g.val := (isCirculation_iff _).2 fun v ↦ g.excessAt_eq v
    have hb := g.mem_Icc
    rw [← intervalExcessExtend_restrict g.val, intervalExcessExtend_mem_Icc] at hb
    have he : (fun v ↦ g.val (IntervalExcessHom.auxiliary v)) =
        excessAt (intervalExcessRestrict g.val) :=
      funext (IntervalExcessHom.auxiliary_eq_excessAt hg)
    exact ⟨hb.1, he ▸ hb.2⟩⟩
  left_inv f := Subtype.ext (intervalExcessRestrict_extend f.val (excessAt f.val))
  right_inv g := by
    apply Subtype.ext
    dsimp only
    have hg : IsCirculation g.val := (isCirculation_iff _).2 fun v ↦ g.excessAt_eq v
    have he : (fun v ↦ g.val (IntervalExcessHom.auxiliary v)) =
        excessAt (intervalExcessRestrict g.val) :=
      funext (IntervalExcessHom.auxiliary_eq_excessAt hg)
    rw [← he, intervalExcessExtend_restrict]

@[simp]
theorem circulationEquiv_apply_original (lo hi : Assignment Q K) (a b : V → K)
    (f : ExcessIntervalFlow lo hi a b) {x y : V} (e : Q x y) :
    (circulationEquiv lo hi a b f).val (IntervalExcessHom.original e) = f.val e := (rfl)

@[simp]
theorem circulationEquiv_apply_auxiliary (lo hi : Assignment Q K) (a b : V → K)
    (f : ExcessIntervalFlow lo hi a b) (v : V) :
    (circulationEquiv lo hi a b f).val (IntervalExcessHom.auxiliary v) = excessAt f.val v := (rfl)

@[simp]
theorem circulationEquiv_symm_apply_val (lo hi : Assignment Q K) (a b : V → K)
    (g : ExcessFlow (intervalExcessExtend lo a) (intervalExcessExtend hi b) 0) :
    ((circulationEquiv lo hi a b).symm g).val = intervalExcessRestrict g.val := (rfl)

end ExcessIntervalFlow

end Excess

/-! ### Empty vertices and signed loops -/

-- Even with no original vertices, the enlarged circulation has its fresh vertex.
example :
    let Q : Empty → Empty → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := 0
    let hi : Assignment Q ℤ := 0
    let a : Empty → ℤ := 0
    let b : Empty → ℤ := 0
    ∃ f : ExcessIntervalFlow lo hi a b,
      excessAt (ExcessIntervalFlow.circulationEquiv lo hi a b f).val none = 0 := by
  intro Q lo hi a b
  have f : ExcessIntervalFlow lo hi a b := ⟨0, by simp [lo, hi], by
    constructor <;> intro x <;> exact x.elim⟩
  exact ⟨f, (ExcessIntervalFlow.circulationEquiv lo hi a b f).excessAt_eq none⟩

-- A negative loop keeps its value, and its auxiliary arrow carries zero excess.
example :
    let Q : Unit → Unit → Type := fun _ _ ↦ Unit
    let lo : Assignment Q ℤ := fun _ _ _ ↦ -3
    let hi : Assignment Q ℤ := fun _ _ _ ↦ -1
    let a : Unit → ℤ := fun _ ↦ -1
    let b : Unit → ℤ := fun _ ↦ 2
    ∃ f : ExcessIntervalFlow lo hi a b,
      (ExcessIntervalFlow.circulationEquiv lo hi a b f).val
        (IntervalExcessHom.original (x := ()) (y := ()) ()) = -2 ∧
      (ExcessIntervalFlow.circulationEquiv lo hi a b f).val
        (IntervalExcessHom.auxiliary ()) = 0 := by
  intro Q lo hi a b
  let f : ExcessIntervalFlow lo hi a b := ⟨fun _ _ _ ↦ -2, by
    constructor <;> intro x y e <;> norm_num [lo, hi], by
    constructor <;> intro x <;> norm_num [a, b, excessAt_def]⟩
  exact ⟨f, by simp [f], by simp [f, excessAt_def]⟩

end TauCeti
