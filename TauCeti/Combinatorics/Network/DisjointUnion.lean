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
@[expose] def DisjointUnionHom (Q : V → V → Type v) (R : W → W → Type v') :
    V ⊕ W → V ⊕ W → Type (max v v')
  | .inl x, .inl y => ULift.{v'} (Q x y)
  | .inr x, .inr y => ULift.{v} (R x y)
  | _, _ => PEmpty

namespace DisjointUnionHom

/-- An arrow inherited from the left summand. -/
def inl {x y : V} (e : Q x y) : DisjointUnionHom Q R (.inl x) (.inl y) :=
  ULift.up e

/-- An arrow inherited from the right summand. -/
def inr {x y : W} (e : R x y) : DisjointUnionHom Q R (.inr x) (.inr y) :=
  ULift.up e

instance instIsEmptyInlInr (x : V) (y : W) :
    IsEmpty (DisjointUnionHom Q R (.inl x) (.inr y)) :=
  inferInstanceAs (IsEmpty PEmpty)

instance instIsEmptyInrInl (x : W) (y : V) :
    IsEmpty (DisjointUnionHom Q R (.inr x) (.inl y)) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The left arrow carrier is equivalent to its carrier in the disjoint union. -/
def inlEquiv (x y : V) : Q x y ≃ DisjointUnionHom Q R (.inl x) (.inl y) where
  toFun := inl
  invFun e := e.down
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem inlEquiv_apply {x y : V} (e : Q x y) :
    inlEquiv (R := R) x y e = inl e :=
  (rfl)

@[simp]
theorem inlEquiv_symm_inl {x y : V} (e : Q x y) :
    (inlEquiv (R := R) x y).symm (inl e) = e :=
  (rfl)

@[simp]
theorem inl_inlEquiv_symm {x y : V} (e : DisjointUnionHom Q R (.inl x) (.inl y)) :
    inl ((inlEquiv x y).symm e) = e :=
  (rfl)

/-- The right arrow carrier is equivalent to its carrier in the disjoint union. -/
def inrEquiv (x y : W) : R x y ≃ DisjointUnionHom Q R (.inr x) (.inr y) where
  toFun := inr
  invFun e := e.down
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem inrEquiv_apply {x y : W} (e : R x y) :
    inrEquiv (Q := Q) x y e = inr e :=
  (rfl)

@[simp]
theorem inrEquiv_symm_inr {x y : W} (e : R x y) :
    (inrEquiv (Q := Q) x y).symm (inr e) = e :=
  (rfl)

@[simp]
theorem inr_inrEquiv_symm {x y : W} (e : DisjointUnionHom Q R (.inr x) (.inr y)) :
    inr ((inrEquiv x y).symm e) = e :=
  (rfl)

instance instFintype [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] :
    ∀ x y, Fintype (DisjointUnionHom Q R x y)
  | .inl x, .inl y => Fintype.ofEquiv (Q x y) (inlEquiv x y)
  | .inr x, .inr y => Fintype.ofEquiv (R x y) (inrEquiv x y)
  | .inl _, .inr _ => inferInstanceAs (Fintype PEmpty)
  | .inr _, .inl _ => inferInstanceAs (Fintype PEmpty)

/-- A property holds for every arrow of a disjoint union exactly when it holds for the arrows in
both summands. -/
theorem forall_iff {P : ∀ ⦃x y⦄, DisjointUnionHom Q R x y → Prop} :
    (∀ ⦃x y⦄ (e : DisjointUnionHom Q R x y), P e) ↔
      (∀ ⦃x y⦄ (e : Q x y), P (inl e)) ∧ ∀ ⦃x y⦄ (e : R x y), P (inr e) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h _, fun _ _ e ↦ h _⟩, ?_⟩
  rintro ⟨hQ, hR⟩ (x | x) (y | y) e
  · exact hQ e.down
  · exact e.elim
  · exact e.elim
  · exact hR e.down

end DisjointUnionHom

namespace Assignment

/-- Combine assignments on two arrow families into an assignment on their disjoint union. -/
def disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    Assignment (DisjointUnionHom Q R) K
  | .inl _, .inl _, e => f e.down
  | .inl _, .inr _, e => e.elim
  | .inr _, .inl _, e => e.elim
  | .inr _, .inr _, e => g e.down

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

/-- Combining both restrictions recovers an assignment on a disjoint union. -/
@[simp]
theorem restrictLeft_disjointUnion_restrictRight
    (f : Assignment (DisjointUnionHom Q R) K) :
    f.restrictLeft.disjointUnion f.restrictRight = f := by
  funext x y e
  rcases x with x | x <;> rcases y with y | y
  · cases e
    rfl
  · exact e.elim
  · exact e.elim
  · cases e
    rfl

/-- Assignments on a disjoint union are equivalently pairs of assignments on its summands. -/
def disjointUnionEquiv :
    Assignment Q K × Assignment R K ≃ Assignment (DisjointUnionHom Q R) K where
  toFun f := f.1.disjointUnion f.2
  invFun f := ⟨f.restrictLeft, f.restrictRight⟩
  left_inv _ := rfl
  right_inv f := restrictLeft_disjointUnion_restrictRight f

@[simp]
theorem disjointUnionEquiv_apply (f : Assignment Q K × Assignment R K) :
    disjointUnionEquiv f = f.1.disjointUnion f.2 :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply (f : Assignment (DisjointUnionHom Q R) K) :
    disjointUnionEquiv.symm f = ⟨f.restrictLeft, f.restrictRight⟩ :=
  (rfl)

@[simp]
theorem disjointUnion_inj {f f' : Assignment Q K} {g g' : Assignment R K} :
    f.disjointUnion g = f'.disjointUnion g' ↔ f = f' ∧ g = g' := by
  constructor
  · intro h
    have hp : (f, g) = (f', g') :=
      (disjointUnionEquiv (Q := Q) (R := R) (K := K)).injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem disjointUnion_le_disjointUnion_iff [LE K]
    {f f' : Assignment Q K} {g g' : Assignment R K} :
    f.disjointUnion g ≤ f'.disjointUnion g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [Pi.le_def, DisjointUnionHom.forall_iff, disjointUnion_inl, disjointUnion_inr]

@[simp]
theorem disjointUnion_zero [Zero K] :
    (0 : Assignment Q K).disjointUnion (0 : Assignment R K) = 0 := by
  rw [← restrictLeft_disjointUnion_restrictRight (0 : Assignment (DisjointUnionHom Q R) K)]
  rfl

@[simp]
theorem restrictLeft_zero [Zero K] :
    restrictLeft (0 : Assignment (DisjointUnionHom Q R) K) = 0 :=
  (rfl)

@[simp]
theorem restrictRight_zero [Zero K] :
    restrictRight (0 : Assignment (DisjointUnionHom Q R) K) = 0 :=
  (rfl)

/-- Pointwise bounds on a disjoint-union assignment are equivalent to the corresponding bounds on
both restrictions. -/
theorem mem_Icc_iff [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} :
    f ∈ Set.Icc lo hi ↔
      f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft ∧
        f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight := by
  simp only [Set.mem_Icc, Pi.le_def, DisjointUnionHom.forall_iff,
    restrictLeft_apply, restrictRight_apply]
  tauto

/-- An assignment on a disjoint union satisfies pointwise bounds exactly when its restrictions
satisfy the corresponding bounds on both summands. -/
theorem disjointUnion_mem_Icc [Preorder K]
    (f lo hi : Assignment Q K) (g lo' hi' : Assignment R K) :
    f.disjointUnion g ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi') ↔
      f ∈ Set.Icc lo hi ∧ g ∈ Set.Icc lo' hi' := by
  rw [mem_Icc_iff]
  simp

/-- Restricting a bounded assignment on a disjoint union preserves the left arrow bounds. -/
theorem restrictLeft_mem_Icc [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} (hf : f ∈ Set.Icc lo hi) :
    f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft :=
  mem_Icc_iff.mp hf |>.1

/-- Restricting a bounded assignment on a disjoint union preserves the right arrow bounds. -/
theorem restrictRight_mem_Icc [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} (hf : f ∈ Set.Icc lo hi) :
    f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight :=
  mem_Icc_iff.mp hf |>.2

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

section Sums

variable [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommMonoid K]

/-- A sum over a left-to-left arrow carrier is the corresponding sum in the left family. -/
@[simp]
theorem DisjointUnionHom.sum_inl {x y : V}
    (f : DisjointUnionHom Q R (.inl x) (.inl y) → K) :
    ∑ e, f e = ∑ e : Q x y, f (DisjointUnionHom.inl e) :=
  (Fintype.sum_equiv (DisjointUnionHom.inlEquiv x y)
    (fun e ↦ f (DisjointUnionHom.inl e)) f fun _ ↦ rfl).symm

/-- A sum over a right-to-right arrow carrier is the corresponding sum in the right family. -/
@[simp]
theorem DisjointUnionHom.sum_inr {x y : W}
    (f : DisjointUnionHom Q R (.inr x) (.inr y) → K) :
    ∑ e, f e = ∑ e : R x y, f (DisjointUnionHom.inr e) :=
  (Fintype.sum_equiv (DisjointUnionHom.inrEquiv x y)
    (fun e ↦ f (DisjointUnionHom.inr e)) f fun _ ↦ rfl).symm

/-- Arrow sums on a disjoint union split into the corresponding arrow sums on both summands. -/
theorem arrowSum_disjointUnion (f : Assignment Q K) (g : Assignment R K)
    (S T : Finset (V ⊕ W)) :
    arrowSum (f.disjointUnion g) S T =
      arrowSum f S.toLeft T.toLeft + arrowSum g S.toRight T.toRight := by
  simp only [arrowSum_def, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight,
    DisjointUnionHom.sum_inl, DisjointUnionHom.sum_inr, Assignment.disjointUnion_inl,
    Assignment.disjointUnion_inr]
  simp

end Sums

section Excess

variable [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommGroup K]

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

@[simp]
theorem isCirculation_disjointUnion_iff (f : Assignment Q K) (g : Assignment R K) :
    IsCirculation (f.disjointUnion g) ↔ IsCirculation f ∧ IsCirculation g := by
  simp only [isCirculation_iff, Sum.forall, excessAt_disjointUnion_inl,
    excessAt_disjointUnion_inr]

section Bounded

variable [Preorder K]
variable {lo hi : Assignment Q K} {lo' hi' : Assignment R K}
variable {a b d : V → K} {a' b' d' : W → K}

namespace ExcessFlow

/-- Prescribed-excess assignments on a disjoint union are equivalently pairs of
prescribed-excess assignments on its two summands. -/
def disjointUnionEquiv :
    ExcessFlow lo hi d × ExcessFlow lo' hi' d' ≃
      ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d') :=
  Equiv.subtypeProdEquivProd.symm.trans <|
    Assignment.disjointUnionEquiv.subtypeEquiv fun ⟨f, g⟩ ↦ by
      simp only [Assignment.disjointUnionEquiv_apply, Assignment.disjointUnion_mem_Icc,
        funext_iff, Sum.forall, excessAt_disjointUnion_inl, excessAt_disjointUnion_inr,
        Sum.elim_inl, Sum.elim_inr]
      tauto

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
        (Sum.elim a a') (Sum.elim b b') :=
  Equiv.subtypeProdEquivProd.symm.trans <|
    Assignment.disjointUnionEquiv.subtypeEquiv fun ⟨f, g⟩ ↦ by
      rw [Assignment.disjointUnionEquiv_apply, Assignment.disjointUnion_mem_Icc]
      simp only [Set.mem_Icc, Pi.le_def, Sum.forall, excessAt_disjointUnion_inl,
        excessAt_disjointUnion_inr, Sum.elim_inl, Sum.elim_inr]
      tauto

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
