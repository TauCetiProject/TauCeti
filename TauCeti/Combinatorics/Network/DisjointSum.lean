/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Shift

/-!
# Disjoint sums of networks

The disjoint sum of two arrow families has the sum of their vertex types and retains the arrows
inside each summand, with no arrows between the summands. Assignments on this arrow family are
equivalent to pairs of assignments on the two original families. Under this equivalence, excess
is computed independently on each summand.

The same construction combines bounded networks and their feasible assignments. In particular,
an assignment with prescribed excess on a disjoint sum is exactly a pair of prescribed-excess
assignments, and the analogous statement holds when vertex excess is constrained to intervals.
These equivalences provide the componentwise composition operation used for circulation
feasibility.

## Main definitions

* `TauCeti.DisjointSumHom`: the disjoint sum of two arrow families.
* `TauCeti.Assignment.disjointSumEquiv`: assignments on a disjoint sum are pairs of assignments.
* `TauCeti.Network.disjointSum`: the disjoint sum of two bounded networks.
* `TauCeti.ExcessFlow.disjointSumEquiv`: prescribed-excess assignments split componentwise.
* `TauCeti.ExcessIntervalFlow.disjointSumEquiv`: interval-excess assignments split componentwise.
-/

public section

namespace TauCeti

universe u u' v v' w

variable {V : Type u} {W : Type u'} (Q : V → V → Type v) (R : W → W → Type v')

/-- The disjoint sum of two arrow families. It retains arrows within each summand and has no
arrows between distinct summands. -/
abbrev DisjointSumHom : V ⊕ W → V ⊕ W → Type (max v v')
  | .inl x, .inl y => ULift.{max v v'} (Q x y)
  | .inr x, .inr y => ULift.{max v v'} (R x y)
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl _ => PEmpty

instance DisjointSumHom.instFintype [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] :
    ∀ x y, Fintype (DisjointSumHom Q R x y)
  | .inl _, .inl _ => inferInstance
  | .inr _, .inr _ => inferInstance
  | .inl _, .inr _ => inferInstance
  | .inr _, .inl _ => inferInstance

namespace DisjointSumHom

variable {Q R}

/-- An arrow of the left family as an arrow of the disjoint sum. -/
def inl {x y : V} (e : Q x y) : DisjointSumHom Q R (.inl x) (.inl y) :=
  ULift.up e

/-- An arrow of the right family as an arrow of the disjoint sum. -/
def inr {x y : W} (e : R x y) : DisjointSumHom Q R (.inr x) (.inr y) :=
  ULift.up e

section Sum

variable [AddCommMonoid K]

/-- A sum over the left arrows of a disjoint sum is a sum over the original left arrows. -/
theorem sum_inl_inl [∀ x y, Fintype (Q x y)] {x y : V}
    (f : DisjointSumHom Q R (.inl x) (.inl y) → K) :
    ∑ e, f e = ∑ e : Q x y, f (inl e) :=
  Fintype.sum_equiv Equiv.ulift f (fun e ↦ f (inl e)) fun _ ↦ rfl

/-- A sum over the right arrows of a disjoint sum is a sum over the original right arrows. -/
theorem sum_inr_inr [∀ x y, Fintype (R x y)] {x y : W}
    (f : DisjointSumHom Q R (.inr x) (.inr y) → K) :
    ∑ e, f e = ∑ e : R x y, f (inr e) :=
  Fintype.sum_equiv Equiv.ulift f (fun e ↦ f (inr e)) fun _ ↦ rfl

end Sum

end DisjointSumHom

namespace Assignment

variable {Q R} {K : Type w}

/-- Combine two assignments into an assignment on the disjoint sum of their arrow families. -/
def disjointSum (f : Assignment Q K) (g : Assignment R K) :
    Assignment (DisjointSumHom Q R) K
  | .inl _, .inl _, e => f e.down
  | .inr _, .inr _, e => g e.down
  | .inl _, .inr _, e => e.elim
  | .inr _, .inl _, e => e.elim

/-- Restrict an assignment on a disjoint sum to its left summand. -/
def restrictLeft (f : Assignment (DisjointSumHom Q R) K) : Assignment Q K :=
  fun _ _ e ↦ f (DisjointSumHom.inl e)

/-- Restrict an assignment on a disjoint sum to its right summand. -/
def restrictRight (f : Assignment (DisjointSumHom Q R) K) : Assignment R K :=
  fun _ _ e ↦ f (DisjointSumHom.inr e)

@[simp]
theorem disjointSum_inl (f : Assignment Q K) (g : Assignment R K) {x y : V} (e : Q x y) :
    disjointSum f g (DisjointSumHom.inl e) = f e :=
  (rfl)

@[simp]
theorem disjointSum_inr (f : Assignment Q K) (g : Assignment R K) {x y : W} (e : R x y) :
    disjointSum f g (DisjointSumHom.inr e) = g e :=
  (rfl)

@[simp]
theorem restrictLeft_disjointSum (f : Assignment Q K) (g : Assignment R K) :
    restrictLeft (disjointSum f g) = f :=
  (rfl)

@[simp]
theorem restrictRight_disjointSum (f : Assignment Q K) (g : Assignment R K) :
    restrictRight (disjointSum f g) = g :=
  (rfl)

/-- An assignment on a disjoint sum is reconstructed from its two restrictions. -/
@[simp]
theorem disjointSum_restrict (f : Assignment (DisjointSumHom Q R) K) :
    disjointSum f.restrictLeft f.restrictRight = f := by
  funext x y e
  rcases x with x | x <;> rcases y with y | y
  · rfl
  · exact e.elim
  · exact e.elim
  · rfl

/-- Assignments on a disjoint sum are equivalent to pairs of assignments on its summands. -/
def disjointSumEquiv : Assignment (DisjointSumHom Q R) K ≃ Assignment Q K × Assignment R K where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun p := disjointSum p.1 p.2
  left_inv := disjointSum_restrict
  right_inv p := by rcases p with ⟨f, g⟩; rfl

@[simp]
theorem disjointSumEquiv_apply (f : Assignment (DisjointSumHom Q R) K) :
    disjointSumEquiv f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem disjointSumEquiv_symm_apply (p : Assignment Q K × Assignment R K) :
    disjointSumEquiv.symm p = disjointSum p.1 p.2 :=
  (rfl)

end Assignment

namespace Network

variable {K : Type w} [LE K]

/-- The disjoint sum of two bounded networks, with bounds inherited on each summand.

This definition is reducible because its dependent arrow family must reduce when assignments on
the resulting network are elaborated. -/
@[expose, reducible]
def disjointSum (N : Network K V) (M : Network K W) : Network K (V ⊕ W) where
  Hom := DisjointSumHom N.Hom M.Hom
  lower := N.lower.disjointSum M.lower
  upper := N.upper.disjointSum M.upper
  lower_le_upper := fun {x y} e ↦ by
    rcases x with x | x <;> rcases y with y | y
    · exact N.lower_le_upper e.down
    · exact e.elim
    · exact e.elim
    · exact M.lower_le_upper e.down

@[simp]
theorem disjointSum_Hom (N : Network K V) (M : Network K W) :
    (N.disjointSum M).Hom = DisjointSumHom N.Hom M.Hom :=
  (rfl)

/-- An arrow of the left network as an arrow of the disjoint-sum network. -/
def disjointSumInl (N : Network K V) (M : Network K W) {x y : V} (e : N.Hom x y) :
    (N.disjointSum M).Hom (.inl x) (.inl y) :=
  ULift.up e

/-- An arrow of the right network as an arrow of the disjoint-sum network. -/
def disjointSumInr (N : Network K V) (M : Network K W) {x y : W} (e : M.Hom x y) :
    (N.disjointSum M).Hom (.inr x) (.inr y) :=
  ULift.up e

@[simp]
theorem disjointSum_lower_inl (N : Network K V) (M : Network K W) {x y : V}
    (e : N.Hom x y) :
    (N.disjointSum M).lower (disjointSumInl N M e) = N.lower e :=
  (rfl)

@[simp]
theorem disjointSum_lower_inr (N : Network K V) (M : Network K W) {x y : W}
    (e : M.Hom x y) :
    (N.disjointSum M).lower (disjointSumInr N M e) = M.lower e :=
  (rfl)

@[simp]
theorem disjointSum_upper_inl (N : Network K V) (M : Network K W) {x y : V}
    (e : N.Hom x y) :
    (N.disjointSum M).upper (disjointSumInl N M e) = N.upper e :=
  (rfl)

@[simp]
theorem disjointSum_upper_inr (N : Network K V) (M : Network K W) {x y : W}
    (e : M.Hom x y) :
    (N.disjointSum M).upper (disjointSumInr N M e) = M.upper e :=
  (rfl)

end Network

section Excess

variable {Q R} {K : Type w} [Fintype V] [Fintype W]
  [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommGroup K]

@[simp]
theorem excessAt_disjointSum_inl (f : Assignment Q K) (g : Assignment R K) (x : V) :
    excessAt (f.disjointSum g) (.inl x) = excessAt f x := by
  have hin :
      (∑ y : V, ∑ e : DisjointSumHom Q R (.inl y) (.inl x), f.disjointSum g e) =
        ∑ y : V, ∑ e : Q y x, f e := by
    apply Fintype.sum_congr _ _
    intro y
    rw [DisjointSumHom.sum_inl_inl]
    rfl
  have hout :
      (∑ y : V, ∑ e : DisjointSumHom Q R (.inl x) (.inl y), f.disjointSum g e) =
        ∑ y : V, ∑ e : Q x y, f e := by
    apply Fintype.sum_congr _ _
    intro y
    rw [DisjointSumHom.sum_inl_inl]
    rfl
  rw [excessAt_def, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [hin, hout, excessAt_def]

@[simp]
theorem excessAt_disjointSum_inr (f : Assignment Q K) (g : Assignment R K) (x : W) :
    excessAt (f.disjointSum g) (.inr x) = excessAt g x := by
  have hin :
      (∑ y : W, ∑ e : DisjointSumHom Q R (.inr y) (.inr x), f.disjointSum g e) =
        ∑ y : W, ∑ e : R y x, g e := by
    apply Fintype.sum_congr _ _
    intro y
    rw [DisjointSumHom.sum_inr_inr]
    rfl
  have hout :
      (∑ y : W, ∑ e : DisjointSumHom Q R (.inr x) (.inr y), f.disjointSum g e) =
        ∑ y : W, ∑ e : R x y, g e := by
    apply Fintype.sum_congr _ _
    intro y
    rw [DisjointSumHom.sum_inr_inr]
    rfl
  rw [excessAt_def, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [hin, hout, excessAt_def]

@[simp]
theorem excessAt_restrictLeft (f : Assignment (DisjointSumHom Q R) K) (x : V) :
    excessAt f.restrictLeft x = excessAt f (.inl x) := by
  calc
    excessAt f.restrictLeft x =
        excessAt (f.restrictLeft.disjointSum f.restrictRight) (.inl x) :=
      (excessAt_disjointSum_inl _ _ _).symm
    _ = excessAt f (.inl x) := congrArg (fun g ↦ excessAt g (.inl x)) f.disjointSum_restrict

@[simp]
theorem excessAt_restrictRight (f : Assignment (DisjointSumHom Q R) K) (x : W) :
    excessAt f.restrictRight x = excessAt f (.inr x) := by
  calc
    excessAt f.restrictRight x =
        excessAt (f.restrictLeft.disjointSum f.restrictRight) (.inr x) :=
      (excessAt_disjointSum_inr _ _ _).symm
    _ = excessAt f (.inr x) := congrArg (fun g ↦ excessAt g (.inr x)) f.disjointSum_restrict

namespace ExcessFlow

variable [Preorder K]
  {lo₁ hi₁ : Assignment Q K} {lo₂ hi₂ : Assignment R K} {b₁ : V → K} {b₂ : W → K}

/-- Restrict a prescribed-excess assignment on a disjoint sum to its left summand. -/
def restrictLeft
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    ExcessFlow lo₁ hi₁ b₁ :=
  ⟨f.val.restrictLeft, ⟨fun _ _ e ↦ f.mem_Icc.1 _ _ (DisjointSumHom.inl e),
    fun _ _ e ↦ f.mem_Icc.2 _ _ (DisjointSumHom.inl e)⟩,
    funext fun x ↦ by simp [congrFun f.property.2 (.inl x)]⟩

/-- Restrict a prescribed-excess assignment on a disjoint sum to its right summand. -/
def restrictRight
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    ExcessFlow lo₂ hi₂ b₂ :=
  ⟨f.val.restrictRight, ⟨fun _ _ e ↦ f.mem_Icc.1 _ _ (DisjointSumHom.inr e),
    fun _ _ e ↦ f.mem_Icc.2 _ _ (DisjointSumHom.inr e)⟩,
    funext fun x ↦ by simp [congrFun f.property.2 (.inr x)]⟩

/-- Combine prescribed-excess assignments on two arrow families with no arrows between them. -/
def disjointSum (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂) :=
  ⟨f.val.disjointSum g.val, ⟨fun x y e ↦ by
      rcases x with x | x <;> rcases y with y | y
      · exact f.mem_Icc.1 _ _ e.down
      · exact e.elim
      · exact e.elim
      · exact g.mem_Icc.1 _ _ e.down,
    fun x y e ↦ by
      rcases x with x | x <;> rcases y with y | y
      · exact f.mem_Icc.2 _ _ e.down
      · exact e.elim
      · exact e.elim
      · exact g.mem_Icc.2 _ _ e.down⟩,
    funext fun x ↦ by rcases x with x | x <;> simp⟩

@[simp]
theorem disjointSum_val (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    (f.disjointSum g).val = f.val.disjointSum g.val :=
  (rfl)

@[simp]
theorem restrictLeft_val
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    f.restrictRight.val = f.val.restrictRight :=
  (rfl)

/-- Prescribed-excess assignments on a disjoint sum are exactly pairs of such assignments on its
two summands. -/
def disjointSumEquiv :
    ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂) ≃
      ExcessFlow lo₁ hi₁ b₁ × ExcessFlow lo₂ hi₂ b₂ where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun p := p.1.disjointSum p.2
  left_inv f := Subtype.ext f.val.disjointSum_restrict
  right_inv p := by rcases p with ⟨f, g⟩; apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp]
theorem disjointSumEquiv_apply
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    disjointSumEquiv f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem disjointSumEquiv_symm_apply (p : ExcessFlow lo₁ hi₁ b₁ × ExcessFlow lo₂ hi₂ b₂) :
    disjointSumEquiv.symm p = p.1.disjointSum p.2 :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

variable [Preorder K]
  {lo₁ hi₁ : Assignment Q K} {lo₂ hi₂ : Assignment R K}
  {a₁ b₁ : V → K} {a₂ b₂ : W → K}

/-- Restrict an interval-excess assignment on a disjoint sum to its left summand. -/
def restrictLeft (f : ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
    (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) : ExcessIntervalFlow lo₁ hi₁ a₁ b₁ :=
  ⟨f.val.restrictLeft, ⟨fun _ _ e ↦ f.mem_Icc.1 _ _ (DisjointSumHom.inl e),
    fun _ _ e ↦ f.mem_Icc.2 _ _ (DisjointSumHom.inl e)⟩,
    ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inl x),
      fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inl x)⟩⟩

/-- Restrict an interval-excess assignment on a disjoint sum to its right summand. -/
def restrictRight (f : ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
    (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) : ExcessIntervalFlow lo₂ hi₂ a₂ b₂ :=
  ⟨f.val.restrictRight, ⟨fun _ _ e ↦ f.mem_Icc.1 _ _ (DisjointSumHom.inr e),
    fun _ _ e ↦ f.mem_Icc.2 _ _ (DisjointSumHom.inr e)⟩,
    ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inr x),
      fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inr x)⟩⟩

/-- Combine interval-excess assignments on two arrow families with no arrows between them. -/
def disjointSum (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
      (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) :=
  ⟨f.val.disjointSum g.val, ⟨fun x y e ↦ by
      rcases x with x | x <;> rcases y with y | y
      · exact f.mem_Icc.1 _ _ e.down
      · exact e.elim
      · exact e.elim
      · exact g.mem_Icc.1 _ _ e.down,
    fun x y e ↦ by
      rcases x with x | x <;> rcases y with y | y
      · exact f.mem_Icc.2 _ _ e.down
      · exact e.elim
      · exact e.elim
      · exact g.mem_Icc.2 _ _ e.down⟩,
    ⟨fun x ↦ by
        rcases x with x | x
        · simpa using f.excessAt_mem_Icc.1 x
        · simpa using g.excessAt_mem_Icc.1 x,
      fun x ↦ by
        rcases x with x | x
        · simpa using f.excessAt_mem_Icc.2 x
        · simpa using g.excessAt_mem_Icc.2 x⟩⟩

@[simp]
theorem disjointSum_val (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    (f.disjointSum g).val = f.val.disjointSum g.val :=
  (rfl)

@[simp]
theorem restrictLeft_val (f : ExcessIntervalFlow (lo₁.disjointSum lo₂)
    (hi₁.disjointSum hi₂) (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) :
    f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val (f : ExcessIntervalFlow (lo₁.disjointSum lo₂)
    (hi₁.disjointSum hi₂) (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) :
    f.restrictRight.val = f.val.restrictRight :=
  (rfl)

/-- Interval-excess assignments on a disjoint sum are exactly pairs of such assignments on its
two summands. -/
def disjointSumEquiv :
    ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
        (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) ≃
      ExcessIntervalFlow lo₁ hi₁ a₁ b₁ × ExcessIntervalFlow lo₂ hi₂ a₂ b₂ where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun p := p.1.disjointSum p.2
  left_inv f := Subtype.ext f.val.disjointSum_restrict
  right_inv p := by rcases p with ⟨f, g⟩; apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp]
theorem disjointSumEquiv_apply (f : ExcessIntervalFlow (lo₁.disjointSum lo₂)
    (hi₁.disjointSum hi₂) (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) :
    disjointSumEquiv f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem disjointSumEquiv_symm_apply
    (p : ExcessIntervalFlow lo₁ hi₁ a₁ b₁ × ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    disjointSumEquiv.symm p = p.1.disjointSum p.2 :=
  (rfl)

end ExcessIntervalFlow

end Excess

end TauCeti
