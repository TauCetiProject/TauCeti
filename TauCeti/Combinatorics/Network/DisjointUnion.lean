/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift

/-!
# Disjoint unions of bounded networks

The disjoint union of two arrow families has vertex type `V ⊕ W`, retains each original arrow,
and has no arrows between the two summands. Assignments on the union are equivalently pairs of
assignments on the summands. This equivalence preserves arrow bounds and computes excess separately
on each side.

Consequently, prescribed-excess and interval-excess problems on a disjoint union are equivalent to
the corresponding pair of problems on its summands. This lets bounded-circulation arguments split
and reassemble disconnected pieces without introducing zero-valued cross arrows.
-/

public section

namespace TauCeti

universe u u' v v' w

variable {V : Type u} {W : Type u'}
variable {Q : V → V → Type v} {R : W → W → Type v'} {K : Type w}

/-- The arrow family obtained by taking the disjoint union of two arrow families. There are no
arrows between the two vertex summands. -/
inductive DisjointUnionHom (Q : V → V → Type v) (R : W → W → Type v') :
    V ⊕ W → V ⊕ W → Type (max u u' v v') where
  /-- An arrow inherited from the left summand. -/
  | inl {x y : V} (e : Q x y) : DisjointUnionHom Q R (.inl x) (.inl y)
  /-- An arrow inherited from the right summand. -/
  | inr {x y : W} (e : R x y) : DisjointUnionHom Q R (.inr x) (.inr y)

namespace DisjointUnionHom

instance instIsEmptyInlInr (x : V) (y : W) :
    IsEmpty (DisjointUnionHom Q R (.inl x) (.inr y)) where
  false e := by cases e

instance instIsEmptyInrInl (x : W) (y : V) :
    IsEmpty (DisjointUnionHom Q R (.inr x) (.inl y)) where
  false e := by cases e

/-- The left arrow carrier is equivalent to its carrier in the disjoint union. -/
def inlEquiv (x y : V) : Q x y ≃ DisjointUnionHom Q R (.inl x) (.inl y) where
  toFun := .inl
  invFun
    | .inl e => e
  left_inv _ := rfl
  right_inv
    | .inl _ => rfl

/-- The right arrow carrier is equivalent to its carrier in the disjoint union. -/
def inrEquiv (x y : W) : R x y ≃ DisjointUnionHom Q R (.inr x) (.inr y) where
  toFun := .inr
  invFun
    | .inr e => e
  left_inv _ := rfl
  right_inv
    | .inr _ => rfl

instance instFintype [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] :
    ∀ x y, Fintype (DisjointUnionHom Q R x y)
  | .inl x, .inl y => Fintype.ofEquiv (Q x y) (inlEquiv x y)
  | .inr x, .inr y => Fintype.ofEquiv (R x y) (inrEquiv x y)
  | .inl _, .inr _ => ⟨∅, fun e ↦ by cases e⟩
  | .inr _, .inl _ => ⟨∅, fun e ↦ by cases e⟩

/-- A property holds for every arrow of a disjoint union exactly when it holds for the arrows in
both summands. -/
theorem forall_iff {P : ∀ ⦃x y⦄, DisjointUnionHom Q R x y → Prop} :
    (∀ ⦃x y⦄ (e : DisjointUnionHom Q R x y), P e) ↔
      (∀ ⦃x y⦄ (e : Q x y), P (inl e)) ∧ ∀ ⦃x y⦄ (e : R x y), P (inr e) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h _, fun _ _ e ↦ h _⟩, ?_⟩
  rintro ⟨hQ, hR⟩ _ _ (e | e)
  · exact hQ e
  · exact hR e

end DisjointUnionHom

namespace Assignment

/-- Combine assignments on two arrow families into an assignment on their disjoint union. -/
def disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    Assignment (DisjointUnionHom Q R) K
  | _, _, .inl e => f e
  | _, _, .inr e => g e

/-- Restrict an assignment on a disjoint union to its left summand. -/
def restrictLeft (f : Assignment (DisjointUnionHom Q R) K) : Assignment Q K :=
  fun _ _ e ↦ f (DisjointUnionHom.inl e)

/-- Restrict an assignment on a disjoint union to its right summand. -/
def restrictRight (f : Assignment (DisjointUnionHom Q R) K) : Assignment R K :=
  fun _ _ e ↦ f (DisjointUnionHom.inr e)

@[simp]
theorem disjointUnion_inl (f : Assignment Q K) (g : Assignment R K) {x y : V} (e : Q x y) :
    f.disjointUnion g (DisjointUnionHom.inl e) = f e :=
  (rfl)

@[simp]
theorem disjointUnion_inr (f : Assignment Q K) (g : Assignment R K) {x y : W} (e : R x y) :
    f.disjointUnion g (DisjointUnionHom.inr e) = g e :=
  (rfl)

@[simp]
theorem restrictLeft_apply (f : Assignment (DisjointUnionHom Q R) K) {x y : V} (e : Q x y) :
    f.restrictLeft e = f (DisjointUnionHom.inl e) :=
  (rfl)

@[simp]
theorem restrictRight_apply (f : Assignment (DisjointUnionHom Q R) K) {x y : W} (e : R x y) :
    f.restrictRight e = f (DisjointUnionHom.inr e) :=
  (rfl)

@[simp]
theorem restrictLeft_disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    (f.disjointUnion g).restrictLeft = f :=
  (rfl)

@[simp]
theorem restrictRight_disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    (f.disjointUnion g).restrictRight = g :=
  (rfl)

/-- Assignments on a disjoint union are equivalently pairs of assignments on its summands. -/
def disjointUnionEquiv :
    Assignment Q K × Assignment R K ≃ Assignment (DisjointUnionHom Q R) K where
  toFun f := f.1.disjointUnion f.2
  invFun f := ⟨f.restrictLeft, f.restrictRight⟩
  left_inv f := rfl
  right_inv f := by
    funext x y e
    cases e <;> rfl

@[simp]
theorem disjointUnionEquiv_apply (f : Assignment Q K × Assignment R K) :
    disjointUnionEquiv f = f.1.disjointUnion f.2 :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply (f : Assignment (DisjointUnionHom Q R) K) :
    disjointUnionEquiv.symm f = ⟨f.restrictLeft, f.restrictRight⟩ :=
  (rfl)

/-- An assignment on a disjoint union satisfies pointwise bounds exactly when its restrictions
satisfy the corresponding bounds on both summands. -/
theorem disjointUnion_mem_Icc [Preorder K]
    (f lo hi : Assignment Q K) (g lo' hi' : Assignment R K) :
    f.disjointUnion g ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi') ↔
      f ∈ Set.Icc lo hi ∧ g ∈ Set.Icc lo' hi' := by
  simp only [Set.mem_Icc, Pi.le_def, DisjointUnionHom.forall_iff,
    disjointUnion_inl, disjointUnion_inr]
  tauto

/-- Restricting a bounded assignment on a disjoint union preserves the left arrow bounds. -/
theorem restrictLeft_mem_Icc [Preorder K]
    {f : Assignment (DisjointUnionHom Q R) K} {lo hi : Assignment Q K}
    {lo' hi' : Assignment R K}
    (hf : f ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi')) :
    f.restrictLeft ∈ Set.Icc lo hi := by
  constructor <;> intro x y e
  · exact hf.1 (.inl x) (.inl y) (DisjointUnionHom.inl e)
  · exact hf.2 (.inl x) (.inl y) (DisjointUnionHom.inl e)

/-- Restricting a bounded assignment on a disjoint union preserves the right arrow bounds. -/
theorem restrictRight_mem_Icc [Preorder K]
    {f : Assignment (DisjointUnionHom Q R) K} {lo hi : Assignment Q K}
    {lo' hi' : Assignment R K}
    (hf : f ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi')) :
    f.restrictRight ∈ Set.Icc lo' hi' := by
  constructor <;> intro x y e
  · exact hf.1 (.inr x) (.inr y) (DisjointUnionHom.inr e)
  · exact hf.2 (.inr x) (.inr y) (DisjointUnionHom.inr e)

end Assignment

namespace Network

/-- The disjoint union of two bounded networks, retaining both sets of bounds and introducing no
arrows between the vertex summands. -/
@[expose, reducible] def disjointUnion [LE K] (N : Network K V) (M : Network K W) :
    Network K (V ⊕ W) where
  Hom := DisjointUnionHom N.Hom M.Hom
  lower := N.lower.disjointUnion M.lower
  upper := N.upper.disjointUnion M.upper
  lower_le_upper := by
    rw [DisjointUnionHom.forall_iff]
    exact ⟨fun _ _ e ↦ N.lower_le_upper e, fun _ _ e ↦ M.lower_le_upper e⟩

@[simp]
theorem disjointUnion_Hom [LE K] (N : Network K V) (M : Network K W) :
    (N.disjointUnion M).Hom = DisjointUnionHom N.Hom M.Hom :=
  (rfl)

@[simp]
theorem disjointUnion_lower [LE K] (N : Network K V) (M : Network K W) :
    (N.disjointUnion M).lower = N.lower.disjointUnion M.lower :=
  (rfl)

@[simp]
theorem disjointUnion_upper [LE K] (N : Network K V) (M : Network K W) :
    (N.disjointUnion M).upper = N.upper.disjointUnion M.upper :=
  (rfl)

end Network

section Excess

variable [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommGroup K]

/-- A sum over a left-to-left arrow carrier is the corresponding sum in the left family. -/
private theorem DisjointUnionHom.sum_inl {x y : V}
    (f : DisjointUnionHom Q R (.inl x) (.inl y) → K) :
    ∑ e, f e = ∑ e : Q x y, f (DisjointUnionHom.inl e) :=
  (Fintype.sum_equiv (DisjointUnionHom.inlEquiv x y)
    (fun e ↦ f (DisjointUnionHom.inl e)) f fun _ ↦ rfl).symm

/-- A sum over a right-to-right arrow carrier is the corresponding sum in the right family. -/
private theorem DisjointUnionHom.sum_inr {x y : W}
    (f : DisjointUnionHom Q R (.inr x) (.inr y) → K) :
    ∑ e, f e = ∑ e : R x y, f (DisjointUnionHom.inr e) :=
  (Fintype.sum_equiv (DisjointUnionHom.inrEquiv x y)
    (fun e ↦ f (DisjointUnionHom.inr e)) f fun _ ↦ rfl).symm

variable [Fintype V] [Fintype W]

@[simp]
theorem excessAt_disjointUnion_inl (f : Assignment Q K) (g : Assignment R K) (x : V) :
    excessAt (f.disjointUnion g) (.inl x) = excessAt f x := by
  simp [excessAt_def, DisjointUnionHom.sum_inl]

@[simp]
theorem excessAt_disjointUnion_inr (f : Assignment Q K) (g : Assignment R K) (x : W) :
    excessAt (f.disjointUnion g) (.inr x) = excessAt g x := by
  simp [excessAt_def, DisjointUnionHom.sum_inr]

@[simp]
theorem excessAt_restrictLeft (f : Assignment (DisjointUnionHom Q R) K) (x : V) :
    excessAt f.restrictLeft x = excessAt f (.inl x) := by
  simp [excessAt_def, DisjointUnionHom.sum_inl]

@[simp]
theorem excessAt_restrictRight (f : Assignment (DisjointUnionHom Q R) K) (x : W) :
    excessAt f.restrictRight x = excessAt f (.inr x) := by
  simp [excessAt_def, DisjointUnionHom.sum_inr]

section Bounded

variable [Preorder K]
variable {lo hi : Assignment Q K} {lo' hi' : Assignment R K}
variable {a b d : V → K} {a' b' d' : W → K}

namespace ExcessFlow

/-- Prescribed-excess assignments on a disjoint union are equivalently pairs of
prescribed-excess assignments on its two summands. -/
def disjointUnionEquiv :
    ExcessFlow lo hi d × ExcessFlow lo' hi' d' ≃
      ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d') where
  toFun f := ⟨f.1.val.disjointUnion f.2.val,
    (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2 ⟨f.1.mem_Icc, f.2.mem_Icc⟩,
    funext fun x ↦ by cases x <;> simp⟩
  invFun f :=
    ⟨⟨f.val.restrictLeft, Assignment.restrictLeft_mem_Icc f.mem_Icc,
        funext fun x ↦ by simp [f.excessAt_eq]⟩,
      ⟨f.val.restrictRight, Assignment.restrictRight_mem_Icc f.mem_Icc,
        funext fun x ↦ by simp [f.excessAt_eq]⟩⟩
  left_inv f := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv f := Subtype.ext (Assignment.disjointUnionEquiv.apply_symm_apply f.val)

@[simp]
theorem disjointUnionEquiv_apply_val (f : ExcessFlow lo hi d × ExcessFlow lo' hi' d') :
    (disjointUnionEquiv f).val = f.1.val.disjointUnion f.2.val :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_fst_val
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d')) :
    (disjointUnionEquiv.symm f).1.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_snd_val
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d')) :
    (disjointUnionEquiv.symm f).2.val = f.val.restrictRight :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

/-- Interval-excess assignments on a disjoint union are equivalently pairs of interval-excess
assignments on its two summands. -/
def disjointUnionEquiv :
    ExcessIntervalFlow lo hi a b × ExcessIntervalFlow lo' hi' a' b' ≃
      ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
        (Sum.elim a a') (Sum.elim b b') where
  toFun f := ⟨f.1.val.disjointUnion f.2.val,
    (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2 ⟨f.1.mem_Icc, f.2.mem_Icc⟩,
    ⟨fun
        | .inl x => by simpa using f.1.excessAt_mem_Icc.1 x
        | .inr x => by simpa using f.2.excessAt_mem_Icc.1 x,
      fun
        | .inl x => by simpa using f.1.excessAt_mem_Icc.2 x
        | .inr x => by simpa using f.2.excessAt_mem_Icc.2 x⟩⟩
  invFun f :=
    ⟨⟨f.val.restrictLeft, Assignment.restrictLeft_mem_Icc f.mem_Icc,
        ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inl x),
          fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inl x)⟩⟩,
      ⟨f.val.restrictRight, Assignment.restrictRight_mem_Icc f.mem_Icc,
        ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inr x),
          fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inr x)⟩⟩⟩
  left_inv f := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv f := Subtype.ext (Assignment.disjointUnionEquiv.apply_symm_apply f.val)

@[simp]
theorem disjointUnionEquiv_apply_val
    (f : ExcessIntervalFlow lo hi a b × ExcessIntervalFlow lo' hi' a' b') :
    (disjointUnionEquiv f).val = f.1.val.disjointUnion f.2.val :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_fst_val
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    (disjointUnionEquiv.symm f).1.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_snd_val
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    (disjointUnionEquiv.symm f).2.val = f.val.restrictRight :=
  (rfl)

end ExcessIntervalFlow

end Bounded

end Excess

end TauCeti
