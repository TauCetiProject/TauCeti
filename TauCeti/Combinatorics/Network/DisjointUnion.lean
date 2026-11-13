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

@[simp]
theorem disjointUnion_zero [Zero K] :
    (0 : Assignment Q K).disjointUnion (0 : Assignment R K) = 0 := by
  simpa only [restrictLeft_zero, restrictRight_zero] using
    disjointUnion_restrictLeft_restrictRight (Q := Q) (R := R)
      (0 : Assignment (DisjointUnionHom Q R) K)

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
theorem le_iff_restrictLeft_restrictRight [LE K]
    {f g : Assignment (DisjointUnionHom Q R) K} :
    f ≤ g ↔ f.restrictLeft ≤ g.restrictLeft ∧ f.restrictRight ≤ g.restrictRight := by
  simp only [Pi.le_def, DisjointUnionHom.forall_iff, restrictLeft_apply,
    restrictRight_apply]

/-- Disjoint-union assignments built from two pairs are ordered componentwise. -/
@[simp]
theorem disjointUnion_le_disjointUnion [LE K] {f f' : Assignment Q K}
    {g g' : Assignment R K} :
    f.disjointUnion g ≤ f'.disjointUnion g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [le_iff_restrictLeft_restrictRight, restrictLeft_disjointUnion,
    restrictRight_disjointUnion]

/-- Arbitrary bounds on a disjoint-union assignment hold exactly when their restrictions hold. -/
theorem mem_Icc_iff_restrictLeft_restrictRight [Preorder K]
    (f lo hi : Assignment (DisjointUnionHom Q R) K) :
    f ∈ Set.Icc lo hi ↔
      f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft ∧
        f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight := by
  simp only [Set.mem_Icc, le_iff_restrictLeft_restrictRight, and_and_and_comm]

/-- Bounds assembled on a disjoint union hold exactly when they hold on both summands. -/
theorem disjointUnion_mem_Icc [Preorder K]
    (f lo hi : Assignment Q K) (g lo' hi' : Assignment R K) :
    f.disjointUnion g ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi') ↔
      f ∈ Set.Icc lo hi ∧ g ∈ Set.Icc lo' hi' := by
  simpa only [restrictLeft_disjointUnion, restrictRight_disjointUnion] using
    mem_Icc_iff_restrictLeft_restrictRight (f.disjointUnion g)
      (lo.disjointUnion lo') (hi.disjointUnion hi')

end Assignment

section Sums

variable [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommMonoid K]

/-- A sum over the arrows between two left-summand vertices is a sum over the original arrows. -/
theorem DisjointUnionHom.sum_inl {x y : V}
    (g : DisjointUnionHom Q R (.inl x) (.inl y) → K) :
    ∑ e, g e = ∑ e : Q x y, g (DisjointUnionHom.inl e) :=
  (Fintype.sum_equiv DisjointUnionHom.inlEquiv _ _ fun _ ↦ rfl).symm

/-- A sum over the arrows between two right-summand vertices is a sum over the original arrows. -/
theorem DisjointUnionHom.sum_inr {x y : W}
    (g : DisjointUnionHom Q R (.inr x) (.inr y) → K) :
    ∑ e, g e = ∑ e : R x y, g (DisjointUnionHom.inr e) :=
  (Fintype.sum_equiv DisjointUnionHom.inrEquiv _ _ fun _ ↦ rfl).symm

end Sums

section Excess

variable [Fintype V] [Fintype W] [∀ x y, Fintype (Q x y)]
variable [∀ x y, Fintype (R x y)] [AddCommGroup K]

@[simp]
theorem excessAt_disjointUnion_inl (f : Assignment Q K) (g : Assignment R K) (x : V) :
    excessAt (f.disjointUnion g) (.inl x) = excessAt f x := by
  simp only [excessAt_def, Fintype.sum_sum_type, DisjointUnionHom.sum_inl,
    Fintype.sum_empty, Finset.sum_const_zero, Assignment.disjointUnion_inl, add_zero]

@[simp]
theorem excessAt_disjointUnion_inr (f : Assignment Q K) (g : Assignment R K) (x : W) :
    excessAt (f.disjointUnion g) (.inr x) = excessAt g x := by
  simp only [excessAt_def, Fintype.sum_sum_type, DisjointUnionHom.sum_inr,
    Fintype.sum_empty, Finset.sum_const_zero, Assignment.disjointUnion_inr, zero_add]

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

/-- Prescribed excess on a disjoint union is equivalent to the two restricted prescriptions. -/
theorem excessAt_eq_iff_restrictLeft_restrictRight
    (f : Assignment (DisjointUnionHom Q R) K) (b : V ⊕ W → K) :
    excessAt f = b ↔
      excessAt f.restrictLeft = b ∘ Sum.inl ∧
        excessAt f.restrictRight = b ∘ Sum.inr := by
  simp only [funext_iff, Sum.forall, excessAt_restrictLeft, excessAt_restrictRight,
    Function.comp_apply]

/-- Interval excess bounds on a disjoint union are equivalent to their two restrictions. -/
theorem excessAt_mem_Icc_iff_restrictLeft_restrictRight
    [Preorder K]
    (f : Assignment (DisjointUnionHom Q R) K) (a b : V ⊕ W → K) :
    excessAt f ∈ Set.Icc a b ↔
      excessAt f.restrictLeft ∈ Set.Icc (a ∘ Sum.inl) (b ∘ Sum.inl) ∧
        excessAt f.restrictRight ∈ Set.Icc (a ∘ Sum.inr) (b ∘ Sum.inr) := by
  simp only [Set.mem_Icc, Pi.le_def, Sum.forall, excessAt_restrictLeft,
    excessAt_restrictRight, Function.comp_apply, and_and_and_comm]

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
    have h : N.lower.disjointUnion M.lower ≤ N.upper.disjointUnion M.upper :=
      Assignment.disjointUnion_le_disjointUnion.2
        ⟨fun _ _ e ↦ N.lower_le_upper e, fun _ _ e ↦ M.lower_le_upper e⟩
    exact fun _ _ e ↦ h _ _ e

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

/-- An exact-excess assignment on arbitrary disjoint-union bounds is equivalent to its two
restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K) (b : V ⊕ W → K) :
    ExcessFlow lo hi b ≃
      ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
        ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) :=
  ((Assignment.disjointUnionEquiv (Q := Q) (R := R) (K := K)).symm.subtypeEquiv fun f ↦ by
    simp only [Assignment.disjointUnionEquiv_symm_apply,
      Assignment.mem_Icc_iff_restrictLeft_restrictRight,
      excessAt_eq_iff_restrictLeft_restrictRight, and_and_and_comm]).trans
    Equiv.subtypeProdEquivProd

/-- Restrict an exact-excess assignment on a disjoint union to its left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) :=
  (restrictEquiv lo hi b f).1

/-- Restrict an exact-excess assignment on a disjoint union to its right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) :=
  (restrictEquiv lo hi b f).2

/-- Combine exact-excess assignments on two arrow families into an assignment on their disjoint
union. -/
def disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b') :=
  (restrictEquiv (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b')).symm (f, g)

@[simp]
theorem restrictEquiv_apply {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) : restrictEquiv lo hi b f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem restrictEquiv_symm_apply_val (lo hi : Assignment (DisjointUnionHom Q R) K)
    (b : V ⊕ W → K)
    (p : ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
      ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi b).symm p).val = p.1.val.disjointUnion p.2.val :=
  (rfl)

@[simp]
theorem restrictEquiv_symm_restrictLeft_restrictRight
    {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) :
    (restrictEquiv lo hi b).symm (f.restrictLeft, f.restrictRight) = f :=
  (restrictEquiv lo hi b).symm_apply_apply f

@[simp]
theorem restrictLeft_restrictEquiv_symm (lo hi : Assignment (DisjointUnionHom Q R) K)
    (b : V ⊕ W → K)
    (p : ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
      ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi b).symm p).restrictLeft = p.1 :=
  congrArg Prod.fst ((restrictEquiv lo hi b).apply_symm_apply p)

@[simp]
theorem restrictRight_restrictEquiv_symm (lo hi : Assignment (DisjointUnionHom Q R) K)
    (b : V ⊕ W → K)
    (p : ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
      ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi b).symm p).restrictRight = p.2 :=
  congrArg Prod.snd ((restrictEquiv lo hi b).apply_symm_apply p)

@[simp]
theorem disjointUnion_val (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

@[simp]
theorem restrictLeft_val {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) : f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val {lo hi : Assignment (DisjointUnionHom Q R) K} {b : V ⊕ W → K}
    (f : ExcessFlow lo hi b) : f.restrictRight.val = f.val.restrictRight :=
  (rfl)

@[simp]
theorem restrictLeft_disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).restrictLeft = f :=
  Subtype.ext rfl

@[simp]
theorem restrictRight_disjointUnion (f : ExcessFlow lo hi b) (g : ExcessFlow lo' hi' b') :
    (f.disjointUnion g).restrictRight = g :=
  Subtype.ext rfl

@[simp]
theorem disjointUnion_restrictLeft_restrictRight
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim b b')) :
    f.restrictLeft.disjointUnion f.restrictRight = f :=
  restrictEquiv_symm_restrictLeft_restrictRight f

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

/-- An interval-excess assignment on arbitrary disjoint-union bounds is equivalent to its two
restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K) (a b : V ⊕ W → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
        ExcessIntervalFlow lo.restrictRight hi.restrictRight
          (a ∘ Sum.inr) (b ∘ Sum.inr) :=
  ((Assignment.disjointUnionEquiv (Q := Q) (R := R) (K := K)).symm.subtypeEquiv fun f ↦ by
    simp only [Assignment.disjointUnionEquiv_symm_apply,
      Assignment.mem_Icc_iff_restrictLeft_restrictRight,
      excessAt_mem_Icc_iff_restrictLeft_restrictRight, and_and_and_comm]).trans
    Equiv.subtypeProdEquivProd

/-- Restrict an interval-excess assignment on a disjoint union to its left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) :=
  (restrictEquiv lo hi a b f).1

/-- Restrict an interval-excess assignment on a disjoint union to its right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictRight hi.restrictRight (a ∘ Sum.inr) (b ∘ Sum.inr) :=
  (restrictEquiv lo hi a b f).2

/-- Combine interval-excess assignments on two arrow families into an assignment on their
disjoint union. -/
def disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b') :=
  (restrictEquiv (lo.disjointUnion lo') (hi.disjointUnion hi')
    (Sum.elim a a') (Sum.elim b b')).symm (f, g)

@[simp]
theorem restrictEquiv_apply {lo hi : Assignment (DisjointUnionHom Q R) K}
    {a b : V ⊕ W → K} (f : ExcessIntervalFlow lo hi a b) :
    restrictEquiv lo hi a b f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem restrictEquiv_symm_apply_val (lo hi : Assignment (DisjointUnionHom Q R) K)
    (a b : V ⊕ W → K)
    (p : ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
      ExcessIntervalFlow lo.restrictRight hi.restrictRight
        (a ∘ Sum.inr) (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi a b).symm p).val = p.1.val.disjointUnion p.2.val :=
  (rfl)

@[simp]
theorem restrictEquiv_symm_restrictLeft_restrictRight
    {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    (restrictEquiv lo hi a b).symm (f.restrictLeft, f.restrictRight) = f :=
  (restrictEquiv lo hi a b).symm_apply_apply f

@[simp]
theorem restrictLeft_restrictEquiv_symm (lo hi : Assignment (DisjointUnionHom Q R) K)
    (a b : V ⊕ W → K)
    (p : ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
      ExcessIntervalFlow lo.restrictRight hi.restrictRight
        (a ∘ Sum.inr) (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi a b).symm p).restrictLeft = p.1 :=
  congrArg Prod.fst ((restrictEquiv lo hi a b).apply_symm_apply p)

@[simp]
theorem restrictRight_restrictEquiv_symm (lo hi : Assignment (DisjointUnionHom Q R) K)
    (a b : V ⊕ W → K)
    (p : ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
      ExcessIntervalFlow lo.restrictRight hi.restrictRight
        (a ∘ Sum.inr) (b ∘ Sum.inr)) :
    ((restrictEquiv lo hi a b).symm p).restrictRight = p.2 :=
  congrArg Prod.snd ((restrictEquiv lo hi a b).apply_symm_apply p)

@[simp]
theorem disjointUnion_val (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

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

@[simp]
theorem restrictLeft_disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).restrictLeft = f :=
  Subtype.ext rfl

@[simp]
theorem restrictRight_disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).restrictRight = g :=
  Subtype.ext rfl

@[simp]
theorem disjointUnion_restrictLeft_restrictRight
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    f.restrictLeft.disjointUnion f.restrictRight = f :=
  restrictEquiv_symm_restrictLeft_restrictRight f

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
