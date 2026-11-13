/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift

/-!
# Disjoint unions of bounded excess assignments

The disjoint union of two explicit arrow families has the sum of their vertex types, retains the
arrows inside each summand, and has no arrows between the summands. Arrow assignments on this
family are equivalent to pairs of assignments on the original families. Under this equivalence,
arrow bounds and vertex excess split componentwise.

The resulting equivalences for `ExcessFlow` and `ExcessIntervalFlow` let exact- and
interval-excess feasibility problems be assembled from, or restricted to, disjoint components.
They preserve every arrow value and every vertex bound.
-/

public section

namespace TauCeti

universe u u' v w

variable {V : Type u} {W : Type u'}
variable {Q : V → V → Type v} {R : W → W → Type v} {K : Type w}

/-- The disjoint union of two arrow families. It retains arrows within each vertex summand and
has no arrows between the two summands. -/
@[expose]
def DisjointUnionHom (Q : V → V → Type v) (R : W → W → Type v) :
    V ⊕ W → V ⊕ W → Type v
  | .inl x, .inl y => Q x y
  | .inr x, .inr y => R x y
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl _ => PEmpty

instance DisjointUnionHom.instFintype [∀ x y, Fintype (Q x y)]
    [∀ x y, Fintype (R x y)] : ∀ x y, Fintype (DisjointUnionHom Q R x y)
  | .inl _, .inl _ => inferInstanceAs (Fintype (Q _ _))
  | .inr _, .inr _ => inferInstanceAs (Fintype (R _ _))
  | .inl _, .inr _ => inferInstanceAs (Fintype PEmpty)
  | .inr _, .inl _ => inferInstanceAs (Fintype PEmpty)

namespace DisjointUnionHom

/-- An arrow of the left family as an arrow of the disjoint union. -/
@[expose]
def inl {x y : V} (e : Q x y) : DisjointUnionHom Q R (.inl x) (.inl y) := e

/-- An arrow of the right family as an arrow of the disjoint union. -/
@[expose]
def inr {x y : W} (e : R x y) : DisjointUnionHom Q R (.inr x) (.inr y) := e

/-- The arrows in the left summand are equivalent to the original left arrows. -/
def inlEquiv {x y : V} : Q x y ≃ DisjointUnionHom Q R (.inl x) (.inl y) :=
  Equiv.refl _

@[simp]
theorem inlEquiv_apply {x y : V} (e : Q x y) : inlEquiv (R := R) e = inl e :=
  (rfl)

@[simp]
theorem inlEquiv_symm_inl {x y : V} (e : Q x y) : inlEquiv.symm (inl (R := R) e) = e :=
  (rfl)

@[simp]
theorem inl_inlEquiv_symm {x y : V} (e : DisjointUnionHom Q R (.inl x) (.inl y)) :
    inl (inlEquiv.symm e) = e :=
  (rfl)

theorem inl_injective {x y : V} :
    Function.Injective (inl (R := R) : Q x y → _) :=
  inlEquiv.injective

@[simp]
theorem inl_inj {x y : V} {e e' : Q x y} : inl (R := R) e = inl e' ↔ e = e' :=
  inl_injective.eq_iff

/-- The arrows in the right summand are equivalent to the original right arrows. -/
def inrEquiv {x y : W} : R x y ≃ DisjointUnionHom Q R (.inr x) (.inr y) :=
  Equiv.refl _

@[simp]
theorem inrEquiv_apply {x y : W} (e : R x y) : inrEquiv (Q := Q) e = inr e :=
  (rfl)

@[simp]
theorem inrEquiv_symm_inr {x y : W} (e : R x y) : inrEquiv.symm (inr (Q := Q) e) = e :=
  (rfl)

@[simp]
theorem inr_inrEquiv_symm {x y : W} (e : DisjointUnionHom Q R (.inr x) (.inr y)) :
    inr (inrEquiv.symm e) = e :=
  (rfl)

theorem inr_injective {x y : W} :
    Function.Injective (inr (Q := Q) : R x y → _) :=
  inrEquiv.injective

@[simp]
theorem inr_inj {x y : W} {e e' : R x y} : inr (Q := Q) e = inr e' ↔ e = e' :=
  inr_injective.eq_iff

/-- A property holds for every disjoint-union arrow exactly when it holds on both summands. -/
theorem forall_iff {P : ∀ ⦃x y⦄, DisjointUnionHom Q R x y → Prop} :
    (∀ ⦃x y⦄ (e : DisjointUnionHom Q R x y), P e) ↔
      (∀ ⦃x y⦄ (e : Q x y), P (inl e)) ∧ ∀ ⦃x y⦄ (e : R x y), P (inr e) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h (inl e), fun _ _ e ↦ h (inr e)⟩, ?_⟩
  rintro ⟨hl, hr⟩ (x | x) (y | y) e
  · exact hl e
  · exact e.elim
  · exact e.elim
  · exact hr e

/-- There are no arrows from the left summand to the right summand. -/
instance instIsEmptyInlInr (x : V) (y : W) :
    IsEmpty (DisjointUnionHom Q R (.inl x) (.inr y)) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- There are no arrows from the right summand to the left summand. -/
instance instIsEmptyInrInl (x : W) (y : V) :
    IsEmpty (DisjointUnionHom Q R (.inr x) (.inl y)) :=
  inferInstanceAs (IsEmpty PEmpty)

end DisjointUnionHom

namespace Assignment

/-- Combine two assignments into an assignment on the disjoint union of their arrow families. -/
@[expose]
def disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    Assignment (DisjointUnionHom Q R) K
  | .inl _, .inl _, e => f e
  | .inr _, .inr _, e => g e
  | .inl _, .inr _, e => e.elim
  | .inr _, .inl _, e => e.elim

/-- Restrict an assignment on a disjoint union to its left arrow family. -/
@[expose]
def restrictLeft (f : Assignment (DisjointUnionHom Q R) K) : Assignment Q K :=
  fun _ _ e ↦ f (DisjointUnionHom.inl e)

/-- Restrict an assignment on a disjoint union to its right arrow family. -/
@[expose]
def restrictRight (f : Assignment (DisjointUnionHom Q R) K) : Assignment R K :=
  fun _ _ e ↦ f (DisjointUnionHom.inr e)

@[simp]
theorem restrictLeft_apply (f : Assignment (DisjointUnionHom Q R) K) {x y : V} (e : Q x y) :
    f.restrictLeft e = f (DisjointUnionHom.inl e) :=
  (rfl)

@[simp]
theorem restrictRight_apply (f : Assignment (DisjointUnionHom Q R) K) {x y : W} (e : R x y) :
    f.restrictRight e = f (DisjointUnionHom.inr e) :=
  (rfl)

@[simp]
theorem restrictLeft_zero [Zero K] :
    (0 : Assignment (DisjointUnionHom Q R) K).restrictLeft = 0 :=
  (rfl)

@[simp]
theorem restrictRight_zero [Zero K] :
    (0 : Assignment (DisjointUnionHom Q R) K).restrictRight = 0 :=
  (rfl)

@[simp]
theorem disjointUnion_inl (f : Assignment Q K) (g : Assignment R K) {x y : V} (e : Q x y) :
    f.disjointUnion g (DisjointUnionHom.inl e) = f e :=
  (rfl)

@[simp]
theorem disjointUnion_inr (f : Assignment Q K) (g : Assignment R K) {x y : W} (e : R x y) :
    f.disjointUnion g (DisjointUnionHom.inr e) = g e :=
  (rfl)

@[simp]
theorem restrictLeft_disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    (f.disjointUnion g).restrictLeft = f :=
  (rfl)

@[simp]
theorem restrictRight_disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    (f.disjointUnion g).restrictRight = g :=
  (rfl)

/-- An assignment on a disjoint union is determined by its restrictions to the two summands. -/
@[simp]
theorem disjointUnion_restrictLeft_restrictRight
    (f : Assignment (DisjointUnionHom Q R) K) :
    f.restrictLeft.disjointUnion f.restrictRight = f := by
  funext x y e
  rcases x with x | x <;> rcases y with y | y
  · rfl
  · exact e.elim
  · exact e.elim
  · rfl

/-- Assignments on a disjoint union are equivalent to pairs of assignments on its summands. -/
def disjointUnionEquiv :
    Assignment Q K × Assignment R K ≃ Assignment (DisjointUnionHom Q R) K where
  toFun f := f.1.disjointUnion f.2
  invFun f := (f.restrictLeft, f.restrictRight)
  left_inv f := by ext <;> rfl
  right_inv := disjointUnion_restrictLeft_restrictRight

@[simp]
theorem disjointUnionEquiv_apply (f : Assignment Q K) (g : Assignment R K) :
    disjointUnionEquiv (f, g) = f.disjointUnion g :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply (f : Assignment (DisjointUnionHom Q R) K) :
    disjointUnionEquiv.symm f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

/-- Assignments on a disjoint union are ordered componentwise. -/
theorem le_iff_restrictLeft_le_restrictRight [LE K]
    {f g : Assignment (DisjointUnionHom Q R) K} :
    f ≤ g ↔ f.restrictLeft ≤ g.restrictLeft ∧ f.restrictRight ≤ g.restrictRight := by
  simp only [Pi.le_def]
  constructor
  · intro h
    exact ⟨fun _ _ e ↦ h _ _ (DisjointUnionHom.inl e),
      fun _ _ e ↦ h _ _ (DisjointUnionHom.inr e)⟩
  · rintro ⟨hf, hg⟩ (x | x) (y | y) e
    · exact hf _ _ e
    · exact e.elim
    · exact e.elim
    · exact hg _ _ e

/-- Disjoint-union assignments built from two pairs are ordered componentwise. -/
@[simp]
theorem disjointUnion_le_disjointUnion [LE K] {f f' : Assignment Q K}
    {g g' : Assignment R K} :
    f.disjointUnion g ≤ f'.disjointUnion g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [le_iff_restrictLeft_le_restrictRight, restrictLeft_disjointUnion,
    restrictRight_disjointUnion]

/-- Arbitrary bounds on a disjoint-union assignment hold exactly when their restrictions hold. -/
theorem mem_Icc_iff_restrictLeft_restrictRight [Preorder K]
    (f lo hi : Assignment (DisjointUnionHom Q R) K) :
    f ∈ Set.Icc lo hi ↔
      f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft ∧
        f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight := by
  simp only [Set.mem_Icc, le_iff_restrictLeft_le_restrictRight, and_and_and_comm]

/-- Bounds assembled on a disjoint union hold exactly when they hold on both summands. -/
theorem disjointUnion_mem_Icc [Preorder K]
    (f lo hi : Assignment Q K) (g lo' hi' : Assignment R K) :
    f.disjointUnion g ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi') ↔
      f ∈ Set.Icc lo hi ∧ g ∈ Set.Icc lo' hi' := by
  simpa only [restrictLeft_disjointUnion, restrictRight_disjointUnion] using
    mem_Icc_iff_restrictLeft_restrictRight (f.disjointUnion g)
      (lo.disjointUnion lo') (hi.disjointUnion hi')

end Assignment

section Excess

variable [Fintype V] [Fintype W] [∀ x y, Fintype (Q x y)]
variable [∀ x y, Fintype (R x y)] [AddCommGroup K]

@[simp]
theorem excessAt_disjointUnion_inl (f : Assignment Q K) (g : Assignment R K) (x : V) :
    excessAt (f.disjointUnion g) (.inl x) = excessAt f x := by
  have hin (y : W) :
      (∑ e : DisjointUnionHom Q R (.inr y) (.inl x), f.disjointUnion g e) = 0 :=
    Fintype.sum_empty _
  have hout (y : W) :
      (∑ e : DisjointUnionHom Q R (.inl x) (.inr y), f.disjointUnion g e) = 0 :=
    Fintype.sum_empty _
  have hin' : (∑ y : W, ∑ e : DisjointUnionHom Q R (.inr y) (.inl x),
      f.disjointUnion g e) = 0 := by
    simp only [hin, Finset.sum_const_zero]
  have hout' : (∑ y : W, ∑ e : DisjointUnionHom Q R (.inl x) (.inr y),
      f.disjointUnion g e) = 0 := by
    simp only [hout, Finset.sum_const_zero]
  rw [excessAt_def, excessAt_def, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hin', hout']
  simp only [Assignment.disjointUnion, add_zero]
  congr 1

@[simp]
theorem excessAt_disjointUnion_inr (f : Assignment Q K) (g : Assignment R K) (x : W) :
    excessAt (f.disjointUnion g) (.inr x) = excessAt g x := by
  have hin (y : V) :
      (∑ e : DisjointUnionHom Q R (.inl y) (.inr x), f.disjointUnion g e) = 0 :=
    Fintype.sum_empty _
  have hout (y : V) :
      (∑ e : DisjointUnionHom Q R (.inr x) (.inl y), f.disjointUnion g e) = 0 :=
    Fintype.sum_empty _
  have hin' : (∑ y : V, ∑ e : DisjointUnionHom Q R (.inl y) (.inr x),
      f.disjointUnion g e) = 0 := by
    simp only [hin, Finset.sum_const_zero]
  have hout' : (∑ y : V, ∑ e : DisjointUnionHom Q R (.inr x) (.inl y),
      f.disjointUnion g e) = 0 := by
    simp only [hout, Finset.sum_const_zero]
  rw [excessAt_def, excessAt_def, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hin', hout']
  simp only [Assignment.disjointUnion, zero_add]
  congr 1

@[simp]
theorem excessAt_restrictLeft (f : Assignment (DisjointUnionHom Q R) K) (x : V) :
    excessAt f.restrictLeft x = excessAt f (.inl x) := by
  conv_rhs => rw [← f.disjointUnion_restrictLeft_restrictRight]
  exact (excessAt_disjointUnion_inl _ _ x).symm

@[simp]
theorem excessAt_restrictRight (f : Assignment (DisjointUnionHom Q R) K) (x : W) :
    excessAt f.restrictRight x = excessAt f (.inr x) := by
  conv_rhs => rw [← f.disjointUnion_restrictLeft_restrictRight]
  exact (excessAt_disjointUnion_inr _ _ x).symm

end Excess

namespace Network

/-- The disjoint union of two bounded networks. It has no arrows between the two vertex
summands, and inherits all bounds inside each summand. -/
@[expose, reducible]
def disjointUnion [LE K] (N : Network K V) (M : Network K W) : Network K (V ⊕ W) where
  Hom := DisjointUnionHom N.Hom M.Hom
  lower := N.lower.disjointUnion M.lower
  upper := N.upper.disjointUnion M.upper
  lower_le_upper := by
    rintro (x | x) (y | y) e
    · exact N.lower_le_upper e
    · exact e.elim
    · exact e.elim
    · exact M.lower_le_upper e

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

section Feasible

variable [Fintype V] [Fintype W] [∀ x y, Fintype (Q x y)]
variable [∀ x y, Fintype (R x y)] [AddCommGroup K] [Preorder K]

namespace ExcessFlow

variable {lo hi : Assignment Q K} {lo' hi' : Assignment R K}
variable {b : V → K} {b' : W → K}

/-- Combine exact-excess assignments on two arrow families into an assignment on their disjoint
union. -/
def disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b') :=
  ⟨f.val.disjointUnion g.val, (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2
    ⟨f.mem_Icc, g.mem_Icc⟩, by
      funext x
      rcases x with x | x <;> simp⟩

@[simp]
theorem disjointUnion_val (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

theorem disjointUnion_apply_inl (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b')
    {x y : V} (e : Q x y) : (f.disjointUnion g).val (DisjointUnionHom.inl e) = f.val e :=
  (rfl)

theorem disjointUnion_apply_inr (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b')
    {x y : W} (e : R x y) : (f.disjointUnion g).val (DisjointUnionHom.inr e) = g.val e :=
  (rfl)

/-- Restrict an exact-excess assignment on a disjoint union to its left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) :=
  ⟨f.val.restrictLeft,
    (Assignment.mem_Icc_iff_restrictLeft_restrictRight f.val lo hi).1 f.mem_Icc |>.1,
    funext fun x ↦ by
      simpa only [excessAt_restrictLeft, Function.comp_apply] using f.excessAt_eq (.inl x)⟩

/-- Restrict an exact-excess assignment on a disjoint union to its right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) :=
  ⟨f.val.restrictRight,
    (Assignment.mem_Icc_iff_restrictLeft_restrictRight f.val lo hi).1 f.mem_Icc |>.2,
    funext fun x ↦ by
      simpa only [excessAt_restrictRight, Function.comp_apply] using f.excessAt_eq (.inr x)⟩

@[simp]
theorem restrictLeft_val {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) : f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) : f.restrictRight.val = f.val.restrictRight :=
  (rfl)

theorem restrictLeft_apply {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) {x y : V} (e : Q x y) :
    f.restrictLeft.val e = f.val (DisjointUnionHom.inl e) :=
  (rfl)

theorem restrictRight_apply {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) {x y : W} (e : R x y) :
    f.restrictRight.val e = f.val (DisjointUnionHom.inr e) :=
  (rfl)

@[simp]
theorem restrictLeft_disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).restrictLeft = f := by
  ext
  rfl

@[simp]
theorem restrictRight_disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).restrictRight = g := by
  ext
  rfl

/-- An exact-excess assignment on arbitrary disjoint-union bounds is equivalent to its two
restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K) (b : V ⊕ W → K) :
    ExcessFlow lo hi b ≃
      ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
        ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun f :=
    ⟨f.1.val.disjointUnion f.2.val,
      (Assignment.mem_Icc_iff_restrictLeft_restrictRight _ lo hi).2 (by
        simpa only [Assignment.restrictLeft_disjointUnion,
          Assignment.restrictRight_disjointUnion] using ⟨f.1.mem_Icc, f.2.mem_Icc⟩),
      by
        funext x
        rcases x with x | x
        · simpa only [excessAt_disjointUnion_inl, Function.comp_apply] using f.1.excessAt_eq x
        · simpa only [excessAt_disjointUnion_inr, Function.comp_apply] using
            f.2.excessAt_eq x⟩
  left_inv f := Subtype.ext f.val.disjointUnion_restrictLeft_restrictRight
  right_inv f := by ext <;> rfl

@[simp]
theorem disjointUnion_restrictLeft_restrictRight
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b')) :
    f.restrictLeft.disjointUnion f.restrictRight = f :=
  Subtype.ext f.val.disjointUnion_restrictLeft_restrictRight

/-- Exact-excess assignments on a disjoint union are equivalent to pairs of exact-excess
assignments on its summands. -/
def disjointUnionEquiv :
    ExcessFlow lo hi b × ExcessFlow lo' hi' b' ≃
      ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b') :=
  (restrictEquiv (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b')).symm

@[simp]
theorem disjointUnionEquiv_apply (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    disjointUnionEquiv (f, g) = f.disjointUnion g :=
  Subtype.ext rfl

@[simp]
theorem disjointUnionEquiv_symm_apply
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b')) :
    disjointUnionEquiv.symm f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

variable {lo hi : Assignment Q K} {lo' hi' : Assignment R K}
variable {a b : V → K} {a' b' : W → K}

/-- Combine interval-excess assignments on two arrow families into an assignment on their
disjoint union. -/
def disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b') :=
  ⟨f.val.disjointUnion g.val, (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2
    ⟨f.mem_Icc, g.mem_Icc⟩, by
      constructor
      · rintro (x | x)
        · simpa only [Sum.elim_inl, excessAt_disjointUnion_inl] using
            f.excessAt_mem_Icc.1 x
        · simpa only [Sum.elim_inr, excessAt_disjointUnion_inr] using
            g.excessAt_mem_Icc.1 x
      · rintro (x | x)
        · simpa only [Sum.elim_inl, excessAt_disjointUnion_inl] using
            f.excessAt_mem_Icc.2 x
        · simpa only [Sum.elim_inr, excessAt_disjointUnion_inr] using
            g.excessAt_mem_Icc.2 x⟩

@[simp]
theorem disjointUnion_val (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

theorem disjointUnion_apply_inl (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') {x y : V} (e : Q x y) :
    (f.disjointUnion g).val (DisjointUnionHom.inl e) = f.val e :=
  (rfl)

theorem disjointUnion_apply_inr (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') {x y : W} (e : R x y) :
    (f.disjointUnion g).val (DisjointUnionHom.inr e) = g.val e :=
  (rfl)

/-- Restrict an interval-excess assignment on a disjoint union to its left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) :=
  ⟨f.val.restrictLeft,
    (Assignment.mem_Icc_iff_restrictLeft_restrictRight f.val lo hi).1 f.mem_Icc |>.1,
    ⟨fun x ↦ by
        simpa only [excessAt_restrictLeft, Function.comp_apply] using f.excessAt_mem_Icc.1 (.inl x),
      fun x ↦ by
        simpa only [excessAt_restrictLeft, Function.comp_apply] using
          f.excessAt_mem_Icc.2 (.inl x)⟩⟩

/-- Restrict an interval-excess assignment on a disjoint union to its right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictRight hi.restrictRight (a ∘ Sum.inr) (b ∘ Sum.inr) :=
  ⟨f.val.restrictRight,
    (Assignment.mem_Icc_iff_restrictLeft_restrictRight f.val lo hi).1 f.mem_Icc |>.2,
    ⟨fun x ↦ by
        simpa only [excessAt_restrictRight, Function.comp_apply] using
          f.excessAt_mem_Icc.1 (.inr x),
      fun x ↦ by
        simpa only [excessAt_restrictRight, Function.comp_apply] using
          f.excessAt_mem_Icc.2 (.inr x)⟩⟩

@[simp]
theorem restrictLeft_val {lo hi : Assignment (DisjointUnionHom Q R) K}
    {a b : V ⊕ W → K} (f : ExcessIntervalFlow lo hi a b) :
    f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val {lo hi : Assignment (DisjointUnionHom Q R) K}
    {a b : V ⊕ W → K} (f : ExcessIntervalFlow lo hi a b) :
    f.restrictRight.val = f.val.restrictRight :=
  (rfl)

theorem restrictLeft_apply {lo hi : Assignment (DisjointUnionHom Q R) K}
    {a b : V ⊕ W → K} (f : ExcessIntervalFlow lo hi a b) {x y : V} (e : Q x y) :
    f.restrictLeft.val e = f.val (DisjointUnionHom.inl e) :=
  (rfl)

theorem restrictRight_apply {lo hi : Assignment (DisjointUnionHom Q R) K}
    {a b : V ⊕ W → K} (f : ExcessIntervalFlow lo hi a b) {x y : W} (e : R x y) :
    f.restrictRight.val e = f.val (DisjointUnionHom.inr e) :=
  (rfl)

@[simp]
theorem restrictLeft_disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).restrictLeft = f := by
  ext
  rfl

@[simp]
theorem restrictRight_disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).restrictRight = g := by
  ext
  rfl

/-- An interval-excess assignment on arbitrary disjoint-union bounds is equivalent to its two
restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K) (a b : V ⊕ W → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
        ExcessIntervalFlow lo.restrictRight hi.restrictRight
          (a ∘ Sum.inr) (b ∘ Sum.inr) where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun f :=
    ⟨f.1.val.disjointUnion f.2.val, by
      apply (Assignment.mem_Icc_iff_restrictLeft_restrictRight _ lo hi).2
      simpa only [Assignment.restrictLeft_disjointUnion,
        Assignment.restrictRight_disjointUnion] using ⟨f.1.mem_Icc, f.2.mem_Icc⟩,
      ⟨fun x ↦ by
          rcases x with x | x
          · simpa only [excessAt_disjointUnion_inl, Function.comp_apply] using
              f.1.excessAt_mem_Icc.1 x
          · simpa only [excessAt_disjointUnion_inr, Function.comp_apply] using
              f.2.excessAt_mem_Icc.1 x,
        fun x ↦ by
          rcases x with x | x
          · simpa only [excessAt_disjointUnion_inl, Function.comp_apply] using
              f.1.excessAt_mem_Icc.2 x
          · simpa only [excessAt_disjointUnion_inr, Function.comp_apply] using
              f.2.excessAt_mem_Icc.2 x⟩⟩
  left_inv f := Subtype.ext f.val.disjointUnion_restrictLeft_restrictRight
  right_inv f := by ext <;> rfl

@[simp]
theorem disjointUnion_restrictLeft_restrictRight
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    f.restrictLeft.disjointUnion f.restrictRight = f :=
  Subtype.ext f.val.disjointUnion_restrictLeft_restrictRight

/-- Interval-excess assignments on a disjoint union are equivalent to pairs of interval-excess
assignments on its summands. -/
def disjointUnionEquiv :
    ExcessIntervalFlow lo hi a b × ExcessIntervalFlow lo' hi' a' b' ≃
      ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
        (Sum.elim a a') (Sum.elim b b') :=
  (restrictEquiv (lo.disjointUnion lo') (hi.disjointUnion hi')
    (Sum.elim a a') (Sum.elim b b')).symm

@[simp]
theorem disjointUnionEquiv_apply (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    disjointUnionEquiv (f, g) = f.disjointUnion g :=
  Subtype.ext rfl

@[simp]
theorem disjointUnionEquiv_symm_apply
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    disjointUnionEquiv.symm f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

end ExcessIntervalFlow

end Feasible

end TauCeti
