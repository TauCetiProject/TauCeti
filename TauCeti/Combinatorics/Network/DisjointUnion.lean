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

/-- The left inclusion of arrows is injective. -/
theorem inl_injective {x y : V} : Function.Injective (@inl V W Q R x y) :=
  fun _ _ h ↦ congrArg ULift.down h

@[simp]
theorem inl_inj {x y : V} {e e' : Q x y} :
    inl (R := R) e = inl e' ↔ e = e' :=
  inl_injective.eq_iff

/-- The right inclusion of arrows is injective. -/
theorem inr_injective {x y : W} : Function.Injective (@inr V W Q R x y) :=
  fun _ _ h ↦ congrArg ULift.down h

@[simp]
theorem inr_inj {x y : W} {e e' : R x y} :
    inr (Q := Q) e = inr e' ↔ e = e' :=
  inr_injective.eq_iff

/-- Define a dependent function on disjoint-union arrows by defining it on each summand. -/
def rec {P : ∀ {x y}, DisjointUnionHom Q R x y → Sort*}
    (hQ : ∀ {x y} (e : Q x y), P (inl e))
    (hR : ∀ {x y} (e : R x y), P (inr e)) :
    ∀ {x y} (e : DisjointUnionHom Q R x y), P e
  | .inl _, .inl _, ⟨e⟩ => hQ e
  | .inl _, .inr _, e => PEmpty.elim e
  | .inr _, .inl _, e => PEmpty.elim e
  | .inr _, .inr _, ⟨e⟩ => hR e

@[simp]
theorem rec_inl {P : ∀ {x y}, DisjointUnionHom Q R x y → Sort*}
    (hQ : ∀ {x y} (e : Q x y), P (inl e))
    (hR : ∀ {x y} (e : R x y), P (inr e)) {x y : V} (e : Q x y) :
    rec hQ hR (inl e) = hQ e :=
  (rfl)

@[simp]
theorem rec_inr {P : ∀ {x y}, DisjointUnionHom Q R x y → Sort*}
    (hQ : ∀ {x y} (e : Q x y), P (inl e))
    (hR : ∀ {x y} (e : R x y), P (inr e)) {x y : W} (e : R x y) :
    rec hQ hR (inr e) = hR e :=
  (rfl)

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

instance instFinite [∀ x y, Finite (Q x y)] [∀ x y, Finite (R x y)] :
    ∀ x y, Finite (DisjointUnionHom Q R x y)
  | .inl x, .inl y => Finite.of_equiv (Q x y) (inlEquiv x y)
  | .inr x, .inr y => Finite.of_equiv (R x y) (inrEquiv x y)
  | .inl _, .inr _ => inferInstanceAs (Finite PEmpty)
  | .inr _, .inl _ => inferInstanceAs (Finite PEmpty)

instance instDecidableEq [∀ x y, DecidableEq (Q x y)] [∀ x y, DecidableEq (R x y)] :
    ∀ x y, DecidableEq (DisjointUnionHom Q R x y)
  | .inl x, .inl y => (inlEquiv x y).symm.decidableEq
  | .inr x, .inr y => (inrEquiv x y).symm.decidableEq
  | .inl _, .inr _ => fun e ↦ isEmptyElim e
  | .inr _, .inl _ => fun e ↦ isEmptyElim e

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
def disjointUnionEquiv (Q : V → V → Type v) (R : W → W → Type v') (K : Type w) :
    Assignment Q K × Assignment R K ≃ Assignment (DisjointUnionHom Q R) K where
  toFun f := f.1.disjointUnion f.2
  invFun f := ⟨f.restrictLeft, f.restrictRight⟩
  left_inv _ := rfl
  right_inv f := restrictLeft_disjointUnion_restrictRight f

@[simp]
theorem disjointUnionEquiv_apply (f : Assignment Q K × Assignment R K) :
    disjointUnionEquiv Q R K f = f.1.disjointUnion f.2 :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply (f : Assignment (DisjointUnionHom Q R) K) :
    (disjointUnionEquiv Q R K).symm f = ⟨f.restrictLeft, f.restrictRight⟩ :=
  (rfl)

@[simp]
theorem disjointUnion_inj {f f' : Assignment Q K} {g g' : Assignment R K} :
    f.disjointUnion g = f'.disjointUnion g' ↔ f = f' ∧ g = g' := by
  constructor
  · intro h
    have hp : (f, g) = (f', g') :=
      (disjointUnionEquiv Q R K).injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem disjointUnion_le_disjointUnion_iff [LE K]
    {f f' : Assignment Q K} {g g' : Assignment R K} :
    f.disjointUnion g ≤ f'.disjointUnion g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [Pi.le_def, DisjointUnionHom.forall_iff, disjointUnion_inl, disjointUnion_inr]

/-- Pointwise comparison on a disjoint union is equivalent to comparison on both restrictions. -/
theorem le_iff_restrictLeft_and_restrictRight [LE K]
    {f g : Assignment (DisjointUnionHom Q R) K} :
    f ≤ g ↔ f.restrictLeft ≤ g.restrictLeft ∧ f.restrictRight ≤ g.restrictRight := by
  simp only [Pi.le_def, DisjointUnionHom.forall_iff, restrictLeft_apply, restrictRight_apply]

@[simp]
theorem restrictLeft_map {L : Type*} (f : Assignment (DisjointUnionHom Q R) K) (φ : K → L) :
    (f.map φ).restrictLeft = f.restrictLeft.map φ :=
  (rfl)

@[simp]
theorem restrictRight_map {L : Type*} (f : Assignment (DisjointUnionHom Q R) K) (φ : K → L) :
    (f.map φ).restrictRight = f.restrictRight.map φ :=
  (rfl)

@[simp]
theorem map_disjointUnion {L : Type*} (f : Assignment Q K) (g : Assignment R K) (φ : K → L) :
    (f.disjointUnion g).map φ = (f.map φ).disjointUnion (g.map φ) := by
  rw [← restrictLeft_disjointUnion_restrictRight ((f.disjointUnion g).map φ)]
  rfl

@[simp]
theorem restrictLeft_add [Add K] (f g : Assignment (DisjointUnionHom Q R) K) :
    (f + g).restrictLeft = f.restrictLeft + g.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_add [Add K] (f g : Assignment (DisjointUnionHom Q R) K) :
    (f + g).restrictRight = f.restrictRight + g.restrictRight :=
  (rfl)

@[simp]
theorem disjointUnion_add [Add K] (f f' : Assignment Q K) (g g' : Assignment R K) :
    (f + f').disjointUnion (g + g') = f.disjointUnion g + f'.disjointUnion g' := by
  rw [← restrictLeft_disjointUnion_restrictRight
    (f.disjointUnion g + f'.disjointUnion g')]
  rfl

@[simp]
theorem restrictLeft_neg [Neg K] (f : Assignment (DisjointUnionHom Q R) K) :
    (-f).restrictLeft = -f.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_neg [Neg K] (f : Assignment (DisjointUnionHom Q R) K) :
    (-f).restrictRight = -f.restrictRight :=
  (rfl)

@[simp]
theorem disjointUnion_neg [Neg K] (f : Assignment Q K) (g : Assignment R K) :
    (-f).disjointUnion (-g) = -(f.disjointUnion g) := by
  rw [← restrictLeft_disjointUnion_restrictRight (-(f.disjointUnion g))]
  rfl

@[simp]
theorem restrictLeft_sub [Sub K] (f g : Assignment (DisjointUnionHom Q R) K) :
    (f - g).restrictLeft = f.restrictLeft - g.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_sub [Sub K] (f g : Assignment (DisjointUnionHom Q R) K) :
    (f - g).restrictRight = f.restrictRight - g.restrictRight :=
  (rfl)

@[simp]
theorem disjointUnion_sub [Sub K] (f f' : Assignment Q K) (g g' : Assignment R K) :
    (f - f').disjointUnion (g - g') = f.disjointUnion g - f'.disjointUnion g' := by
  rw [← restrictLeft_disjointUnion_restrictRight
    (f.disjointUnion g - f'.disjointUnion g')]
  rfl

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
theorem mem_Icc_iff_restrictLeft_and_restrictRight [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} :
    f ∈ Set.Icc lo hi ↔
      f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft ∧
        f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight := by
  simp only [Set.mem_Icc, Pi.le_def, DisjointUnionHom.forall_iff,
    restrictLeft_apply, restrictRight_apply]
  tauto

/-- Combining two assignments respects combined pointwise bounds exactly when each assignment
respects the bounds on its summand. -/
theorem disjointUnion_mem_Icc [Preorder K]
    (f lo hi : Assignment Q K) (g lo' hi' : Assignment R K) :
    f.disjointUnion g ∈ Set.Icc (lo.disjointUnion lo') (hi.disjointUnion hi') ↔
      f ∈ Set.Icc lo hi ∧ g ∈ Set.Icc lo' hi' := by
  rw [mem_Icc_iff_restrictLeft_and_restrictRight]
  simp

/-- Restricting a bounded assignment on a disjoint union preserves the left arrow bounds. -/
theorem restrictLeft_mem_Icc [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} (hf : f ∈ Set.Icc lo hi) :
    f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft :=
  mem_Icc_iff_restrictLeft_and_restrictRight.mp hf |>.1

/-- Restricting a bounded assignment on a disjoint union preserves the right arrow bounds. -/
theorem restrictRight_mem_Icc [Preorder K]
    {f lo hi : Assignment (DisjointUnionHom Q R) K} (hf : f ∈ Set.Icc lo hi) :
    f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight :=
  mem_Icc_iff_restrictLeft_and_restrictRight.mp hf |>.2

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

/-- An arrow sum on a disjoint union splits into the sums of both restrictions. -/
theorem arrowSum_eq_restrictLeft_add_restrictRight
    (f : Assignment (DisjointUnionHom Q R) K) (S T : Finset (V ⊕ W)) :
    arrowSum f S T =
      arrowSum f.restrictLeft S.toLeft T.toLeft +
        arrowSum f.restrictRight S.toRight T.toRight := by
  rw [← Assignment.restrictLeft_disjointUnion_restrictRight f]
  exact arrowSum_disjointUnion _ _ _ _

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

/-- Excess of a combined assignment is the function obtained by combining both excesses. -/
@[simp]
theorem excessAt_disjointUnion (f : Assignment Q K) (g : Assignment R K) :
    excessAt (f.disjointUnion g) = Sum.elim (excessAt f) (excessAt g) := by
  funext x
  cases x <;> simp

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

/-- An assignment on a disjoint union is a circulation exactly when both restrictions are. -/
theorem isCirculation_iff_restrictLeft_and_restrictRight
    (f : Assignment (DisjointUnionHom Q R) K) :
    IsCirculation f ↔ IsCirculation f.restrictLeft ∧ IsCirculation f.restrictRight := by
  have hrecover := Assignment.restrictLeft_disjointUnion_restrictRight f
  constructor
  · intro hf
    apply (isCirculation_disjointUnion_iff _ _).mp
    simpa only [hrecover] using hf
  · intro hf
    have := (isCirculation_disjointUnion_iff _ _).mpr hf
    simpa only [hrecover] using this

section Bounded

variable [Preorder K]
variable {lo hi : Assignment Q K} {lo' hi' : Assignment R K}
variable {a b d : V → K} {a' b' d' : W → K}

namespace ExcessFlow

/-- Restrict a prescribed-excess assignment to the left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {d : V ⊕ W → K}
    (f : ExcessFlow lo hi d) :
    ExcessFlow lo.restrictLeft hi.restrictLeft (d ∘ Sum.inl) :=
  ⟨f.val.restrictLeft, Assignment.restrictLeft_mem_Icc f.mem_Icc,
    funext fun x ↦ by simp [f.excessAt_eq]⟩

@[simp]
theorem restrictLeft_val {lo hi : Assignment (DisjointUnionHom Q R) K} {d : V ⊕ W → K}
    (f : ExcessFlow lo hi d) : f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

/-- Restrict a prescribed-excess assignment to the right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {d : V ⊕ W → K}
    (f : ExcessFlow lo hi d) :
    ExcessFlow lo.restrictRight hi.restrictRight (d ∘ Sum.inr) :=
  ⟨f.val.restrictRight, Assignment.restrictRight_mem_Icc f.mem_Icc,
    funext fun x ↦ by simp [f.excessAt_eq]⟩

@[simp]
theorem restrictRight_val {lo hi : Assignment (DisjointUnionHom Q R) K} {d : V ⊕ W → K}
    (f : ExcessFlow lo hi d) : f.restrictRight.val = f.val.restrictRight :=
  (rfl)

/-- Combine prescribed-excess assignments on both summands. -/
def disjointUnion (f : ExcessFlow lo hi d) (g : ExcessFlow lo' hi' d') :
    ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d') :=
  ⟨f.val.disjointUnion g.val, (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2
      ⟨f.mem_Icc, g.mem_Icc⟩,
    funext fun x ↦ by cases x <;> simp⟩

@[simp]
theorem disjointUnion_val (f : ExcessFlow lo hi d) (g : ExcessFlow lo' hi' d') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

/-- Prescribed-excess assignments on a disjoint union are equivalently pairs of
prescribed-excess assignments on its two summands. -/
def disjointUnionEquiv (lo hi : Assignment Q K) (d : V → K)
    (lo' hi' : Assignment R K) (d' : W → K) :
    ExcessFlow lo hi d × ExcessFlow lo' hi' d' ≃
      ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d') :=
  Equiv.subtypeProdEquivProd.symm.trans <|
    (Assignment.disjointUnionEquiv Q R K).subtypeEquiv fun ⟨f, g⟩ ↦ by
      simp only [Assignment.disjointUnionEquiv_apply, Assignment.disjointUnion_mem_Icc,
        funext_iff, Sum.forall, excessAt_disjointUnion_inl, excessAt_disjointUnion_inr,
        Sum.elim_inl, Sum.elim_inr]
      tauto

@[simp]
theorem disjointUnionEquiv_apply_val (f : ExcessFlow lo hi d × ExcessFlow lo' hi' d') :
    (disjointUnionEquiv lo hi d lo' hi' d' f).val =
      f.1.val.disjointUnion f.2.val :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_fst_val
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d')) :
    ((disjointUnionEquiv lo hi d lo' hi' d').symm f).1.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_snd_val
    (f : ExcessFlow (lo.disjointUnion lo') (hi.disjointUnion hi') (Sum.elim d d')) :
    ((disjointUnionEquiv lo hi d lo' hi' d').symm f).2.val = f.val.restrictRight :=
  (rfl)

/-- Prescribed-excess assignments with arbitrary bounds on a disjoint union are equivalent to
their two restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K) (d : V ⊕ W → K) :
    ExcessFlow lo hi d ≃
      ExcessFlow lo.restrictLeft hi.restrictLeft (d ∘ Sum.inl) ×
        ExcessFlow lo.restrictRight hi.restrictRight (d ∘ Sum.inr) where
  toFun f := ⟨f.restrictLeft, f.restrictRight⟩
  invFun f :=
    ⟨f.1.val.disjointUnion f.2.val,
      Assignment.mem_Icc_iff_restrictLeft_and_restrictRight.2 ⟨by simpa using f.1.mem_Icc,
        by simpa using f.2.mem_Icc⟩,
      funext fun x ↦ by cases x <;> simp⟩
  left_inv f := Subtype.ext (Assignment.restrictLeft_disjointUnion_restrictRight f.val)
  right_inv f := by
    ext <;> rfl

@[simp]
theorem restrictEquiv_apply_fst_val
    (lo hi : Assignment (DisjointUnionHom Q R) K) (d : V ⊕ W → K)
    (f : ExcessFlow lo hi d) : (restrictEquiv lo hi d f).1.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictEquiv_apply_snd_val
    (lo hi : Assignment (DisjointUnionHom Q R) K) (d : V ⊕ W → K)
    (f : ExcessFlow lo hi d) : (restrictEquiv lo hi d f).2.val = f.val.restrictRight :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

/-- Restrict an interval-excess assignment to the left summand. -/
def restrictLeft {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) :=
  ⟨f.val.restrictLeft, Assignment.restrictLeft_mem_Icc f.mem_Icc,
    ⟨fun x ↦ by simpa only [excessAt_restrictLeft, Function.comp_apply] using
        f.excessAt_mem_Icc.1 (.inl x),
      fun x ↦ by simpa only [excessAt_restrictLeft, Function.comp_apply] using
        f.excessAt_mem_Icc.2 (.inl x)⟩⟩

@[simp]
theorem restrictLeft_val {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) : f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

/-- Restrict an interval-excess assignment to the right summand. -/
def restrictRight {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictRight hi.restrictRight (a ∘ Sum.inr) (b ∘ Sum.inr) :=
  ⟨f.val.restrictRight, Assignment.restrictRight_mem_Icc f.mem_Icc,
    ⟨fun x ↦ by simpa only [excessAt_restrictRight, Function.comp_apply] using
        f.excessAt_mem_Icc.1 (.inr x),
      fun x ↦ by simpa only [excessAt_restrictRight, Function.comp_apply] using
        f.excessAt_mem_Icc.2 (.inr x)⟩⟩

@[simp]
theorem restrictRight_val {lo hi : Assignment (DisjointUnionHom Q R) K} {a b : V ⊕ W → K}
    (f : ExcessIntervalFlow lo hi a b) : f.restrictRight.val = f.val.restrictRight :=
  (rfl)

/-- Combine interval-excess assignments on both summands. -/
def disjointUnion (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b') :=
  ⟨f.val.disjointUnion g.val, (Assignment.disjointUnion_mem_Icc _ _ _ _ _ _).2
      ⟨f.mem_Icc, g.mem_Icc⟩,
    ⟨fun x ↦ by
        cases x with
        | inl x => simpa only [Sum.elim_inl, excessAt_disjointUnion_inl] using
            f.excessAt_mem_Icc.1 x
        | inr x => simpa only [Sum.elim_inr, excessAt_disjointUnion_inr] using
            g.excessAt_mem_Icc.1 x,
      fun x ↦ by
        cases x with
        | inl x => simpa only [Sum.elim_inl, excessAt_disjointUnion_inl] using
            f.excessAt_mem_Icc.2 x
        | inr x => simpa only [Sum.elim_inr, excessAt_disjointUnion_inr] using
            g.excessAt_mem_Icc.2 x⟩⟩

@[simp]
theorem disjointUnion_val (f : ExcessIntervalFlow lo hi a b)
    (g : ExcessIntervalFlow lo' hi' a' b') :
    (f.disjointUnion g).val = f.val.disjointUnion g.val :=
  (rfl)

/-- Interval-excess assignments on a disjoint union are equivalently pairs of interval-excess
assignments on its two summands. -/
def disjointUnionEquiv (lo hi : Assignment Q K) (a b : V → K)
    (lo' hi' : Assignment R K) (a' b' : W → K) :
    ExcessIntervalFlow lo hi a b × ExcessIntervalFlow lo' hi' a' b' ≃
      ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
        (Sum.elim a a') (Sum.elim b b') :=
  Equiv.subtypeProdEquivProd.symm.trans <|
    (Assignment.disjointUnionEquiv Q R K).subtypeEquiv fun ⟨f, g⟩ ↦ by
      rw [Assignment.disjointUnionEquiv_apply, Assignment.disjointUnion_mem_Icc]
      simp only [Set.mem_Icc, Pi.le_def, Sum.forall, excessAt_disjointUnion_inl,
        excessAt_disjointUnion_inr, Sum.elim_inl, Sum.elim_inr]
      tauto

@[simp]
theorem disjointUnionEquiv_apply_val
    (f : ExcessIntervalFlow lo hi a b × ExcessIntervalFlow lo' hi' a' b') :
    (disjointUnionEquiv lo hi a b lo' hi' a' b' f).val =
      f.1.val.disjointUnion f.2.val :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_fst_val
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    ((disjointUnionEquiv lo hi a b lo' hi' a' b').symm f).1.val =
      f.val.restrictLeft :=
  (rfl)

@[simp]
theorem disjointUnionEquiv_symm_apply_snd_val
    (f : ExcessIntervalFlow (lo.disjointUnion lo') (hi.disjointUnion hi')
      (Sum.elim a a') (Sum.elim b b')) :
    ((disjointUnionEquiv lo hi a b lo' hi' a' b').symm f).2.val =
      f.val.restrictRight :=
  (rfl)

/-- Interval-excess assignments with arbitrary bounds on a disjoint union are equivalent to
their two restrictions. -/
def restrictEquiv (lo hi : Assignment (DisjointUnionHom Q R) K)
    (a b : V ⊕ W → K) :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
        ExcessIntervalFlow lo.restrictRight hi.restrictRight
          (a ∘ Sum.inr) (b ∘ Sum.inr) where
  toFun f := ⟨f.restrictLeft, f.restrictRight⟩
  invFun f :=
    ⟨f.1.val.disjointUnion f.2.val,
      Assignment.mem_Icc_iff_restrictLeft_and_restrictRight.2 ⟨by simpa using f.1.mem_Icc,
        by simpa using f.2.mem_Icc⟩,
      ⟨fun x ↦ by
          cases x with
          | inl x => simpa only [excessAt_disjointUnion_inl, Function.comp_apply] using
              f.1.excessAt_mem_Icc.1 x
          | inr x => simpa only [excessAt_disjointUnion_inr, Function.comp_apply] using
              f.2.excessAt_mem_Icc.1 x,
        fun x ↦ by
          cases x with
          | inl x => simpa only [excessAt_disjointUnion_inl, Function.comp_apply] using
              f.1.excessAt_mem_Icc.2 x
          | inr x => simpa only [excessAt_disjointUnion_inr, Function.comp_apply] using
              f.2.excessAt_mem_Icc.2 x⟩⟩
  left_inv f := Subtype.ext (Assignment.restrictLeft_disjointUnion_restrictRight f.val)
  right_inv f := by
    ext <;> rfl

@[simp]
theorem restrictEquiv_apply_fst_val
    (lo hi : Assignment (DisjointUnionHom Q R) K) (a b : V ⊕ W → K)
    (f : ExcessIntervalFlow lo hi a b) :
    (restrictEquiv lo hi a b f).1.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictEquiv_apply_snd_val
    (lo hi : Assignment (DisjointUnionHom Q R) K) (a b : V ⊕ W → K)
    (f : ExcessIntervalFlow lo hi a b) :
    (restrictEquiv lo hi a b f).2.val = f.val.restrictRight :=
  (rfl)

end ExcessIntervalFlow

end Bounded

end Excess

end TauCeti
