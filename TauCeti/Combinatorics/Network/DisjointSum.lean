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
@[expose] def DisjointSumHom : V ⊕ W → V ⊕ W → Type (max v v')
  | .inl x, .inl y => ULift.{max v v'} (Q x y)
  | .inr x, .inr y => ULift.{max v v'} (R x y)
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl _ => PEmpty

instance DisjointSumHom.instFintypeInlInl {x y : V} [Fintype (Q x y)] :
    Fintype (DisjointSumHom Q R (.inl x) (.inl y)) := by
  change Fintype (ULift.{max v v'} (Q x y))
  infer_instance

instance DisjointSumHom.instFintypeInrInr {x y : W} [Fintype (R x y)] :
    Fintype (DisjointSumHom Q R (.inr x) (.inr y)) := by
  change Fintype (ULift.{max v v'} (R x y))
  infer_instance

instance DisjointSumHom.instFintypeInlInr {x : V} {y : W} :
    Fintype (DisjointSumHom Q R (.inl x) (.inr y)) := by
  change Fintype PEmpty
  infer_instance

instance DisjointSumHom.instFintypeInrInl {x : W} {y : V} :
    Fintype (DisjointSumHom Q R (.inr x) (.inl y)) := by
  change Fintype PEmpty
  infer_instance

instance DisjointSumHom.instFintype [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] :
    ∀ x y, Fintype (DisjointSumHom Q R x y)
  | .inl _, .inl _ => inferInstance
  | .inr _, .inr _ => inferInstance
  | .inl _, .inr _ => inferInstance
  | .inr _, .inl _ => inferInstance

instance DisjointSumHom.instIsEmptyInlInr (x : V) (y : W) :
    IsEmpty (DisjointSumHom Q R (.inl x) (.inr y)) :=
  inferInstanceAs (IsEmpty PEmpty)

instance DisjointSumHom.instIsEmptyInrInl (x : W) (y : V) :
    IsEmpty (DisjointSumHom Q R (.inr x) (.inl y)) :=
  inferInstanceAs (IsEmpty PEmpty)

namespace DisjointSumHom

variable {Q R}

/-- An arrow of the left family as an arrow of the disjoint sum. -/
@[expose] def inl {x y : V} (e : Q x y) : DisjointSumHom Q R (.inl x) (.inl y) :=
  ULift.up e

/-- An arrow of the right family as an arrow of the disjoint sum. -/
@[expose] def inr {x y : W} (e : R x y) : DisjointSumHom Q R (.inr x) (.inr y) :=
  ULift.up e

@[simp]
theorem inl_inj {x y : V} {e e' : Q x y} :
    (inl e : DisjointSumHom Q R (.inl x) (.inl y)) = inl e' ↔ e = e' :=
  ⟨congrArg ULift.down, congrArg _⟩

@[simp]
theorem inr_inj {x y : W} {e e' : R x y} :
    (inr e : DisjointSumHom Q R (.inr x) (.inr y)) = inr e' ↔ e = e' :=
  ⟨congrArg ULift.down, congrArg _⟩

/-- A property holds for every arrow of a disjoint sum exactly when it holds for the arrows of
both summands. -/
theorem forall_iff {P : ∀ ⦃a b : V ⊕ W⦄, DisjointSumHom Q R a b → Prop} :
    (∀ ⦃a b⦄ (e : DisjointSumHom Q R a b), P e) ↔
      (∀ ⦃x y : V⦄ (e : Q x y), P (inl e)) ∧ ∀ ⦃x y : W⦄ (e : R x y), P (inr e) := by
  refine ⟨fun h ↦ ⟨fun _ _ e ↦ h (inl e), fun _ _ e ↦ h (inr e)⟩, fun ⟨hl, hr⟩ a b e ↦ ?_⟩
  rcases a with x | x <;> rcases b with y | y
  · exact hl e.down
  · exact e.elim
  · exact e.elim
  · exact hr e.down

variable (Q R) in
/-- The arrows of the left family between two vertices are the corresponding arrows of the
disjoint sum. -/
def inlEquiv (x y : V) : Q x y ≃ DisjointSumHom Q R (.inl x) (.inl y) :=
  Equiv.ulift.symm

variable (Q R) in
/-- The arrows of the right family between two vertices are the corresponding arrows of the
disjoint sum. -/
def inrEquiv (x y : W) : R x y ≃ DisjointSumHom Q R (.inr x) (.inr y) :=
  Equiv.ulift.symm

@[simp]
theorem inlEquiv_apply {x y : V} (e : Q x y) : inlEquiv Q R x y e = inl e :=
  (rfl)

@[simp]
theorem inrEquiv_apply {x y : W} (e : R x y) : inrEquiv Q R x y e = inr e :=
  (rfl)

@[simp]
theorem inlEquiv_symm_inl {x y : V} (e : Q x y) : (inlEquiv Q R x y).symm (inl e) = e :=
  (rfl)

@[simp]
theorem inrEquiv_symm_inr {x y : W} (e : R x y) : (inrEquiv Q R x y).symm (inr e) = e :=
  (rfl)

@[simp]
theorem inl_inlEquiv_symm {x y : V} (e : DisjointSumHom Q R (.inl x) (.inl y)) :
    inl ((inlEquiv Q R x y).symm e) = e :=
  (rfl)

@[simp]
theorem inr_inrEquiv_symm {x y : W} (e : DisjointSumHom Q R (.inr x) (.inr y)) :
    inr ((inrEquiv Q R x y).symm e) = e :=
  (rfl)

section Sum

variable [AddCommMonoid K]

/-- A sum over the left arrows of a disjoint sum is a sum over the original left arrows. -/
theorem sum_inl_inl {x y : V} [Fintype (Q x y)]
    (f : DisjointSumHom Q R (.inl x) (.inl y) → K) :
    ∑ e, f e = ∑ e : Q x y, f (inl e) :=
  (Fintype.sum_equiv (inlEquiv Q R x y) _ f fun _ ↦ rfl).symm

/-- A sum over the right arrows of a disjoint sum is a sum over the original right arrows. -/
theorem sum_inr_inr {x y : W} [Fintype (R x y)]
    (f : DisjointSumHom Q R (.inr x) (.inr y) → K) :
    ∑ e, f e = ∑ e : R x y, f (inr e) :=
  (Fintype.sum_equiv (inrEquiv Q R x y) _ f fun _ ↦ rfl).symm

end Sum

end DisjointSumHom

namespace Assignment

variable {Q R} {K : Type w}

/-- Combine two assignments into an assignment on the disjoint sum of their arrow families. -/
@[expose] def disjointSum (f : Assignment Q K) (g : Assignment R K) :
    Assignment (DisjointSumHom Q R) K
  | .inl _, .inl _, e => f e.down
  | .inr _, .inr _, e => g e.down
  | .inl _, .inr _, e => e.elim
  | .inr _, .inl _, e => e.elim

/-- Restrict an assignment on a disjoint sum to its left summand. -/
@[expose] def restrictLeft (f : Assignment (DisjointSumHom Q R) K) : Assignment Q K :=
  fun _ _ e ↦ f (DisjointSumHom.inl e)

/-- Restrict an assignment on a disjoint sum to its right summand. -/
@[expose] def restrictRight (f : Assignment (DisjointSumHom Q R) K) : Assignment R K :=
  fun _ _ e ↦ f (DisjointSumHom.inr e)

@[simp]
theorem restrictLeft_apply (f : Assignment (DisjointSumHom Q R) K) {x y : V} (e : Q x y) :
    f.restrictLeft e = f (DisjointSumHom.inl e) :=
  (rfl)

@[simp]
theorem restrictRight_apply (f : Assignment (DisjointSumHom Q R) K) {x y : W} (e : R x y) :
    f.restrictRight e = f (DisjointSumHom.inr e) :=
  (rfl)

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
  funext _ _ e
  exact (DisjointSumHom.forall_iff
    (P := fun _ _ e ↦ disjointSum f.restrictLeft f.restrictRight e = f e)).2
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩ e

/-- Assignments on a disjoint sum agree when their restrictions to both summands agree. -/
theorem ext_restrict {f g : Assignment (DisjointSumHom Q R) K}
    (hl : f.restrictLeft = g.restrictLeft) (hr : f.restrictRight = g.restrictRight) : f = g := by
  rw [← f.disjointSum_restrict, ← g.disjointSum_restrict, hl, hr]

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

section Algebra

@[simp]
theorem disjointSum_zero [Zero K] : disjointSum (0 : Assignment Q K) (0 : Assignment R K) = 0 :=
  ext_restrict rfl rfl

@[simp]
theorem restrictLeft_zero [Zero K] : (0 : Assignment (DisjointSumHom Q R) K).restrictLeft = 0 :=
  (rfl)

@[simp]
theorem restrictRight_zero [Zero K] : (0 : Assignment (DisjointSumHom Q R) K).restrictRight = 0 :=
  (rfl)

theorem disjointSum_add [Add K] (f₁ f₂ : Assignment Q K) (g₁ g₂ : Assignment R K) :
    disjointSum (f₁ + f₂) (g₁ + g₂) = disjointSum f₁ g₁ + disjointSum f₂ g₂ :=
  ext_restrict rfl rfl

@[simp]
theorem restrictLeft_add [Add K] (f g : Assignment (DisjointSumHom Q R) K) :
    (f + g).restrictLeft = f.restrictLeft + g.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_add [Add K] (f g : Assignment (DisjointSumHom Q R) K) :
    (f + g).restrictRight = f.restrictRight + g.restrictRight :=
  (rfl)

theorem disjointSum_neg [Neg K] (f : Assignment Q K) (g : Assignment R K) :
    disjointSum (-f) (-g) = -disjointSum f g :=
  ext_restrict rfl rfl

@[simp]
theorem restrictLeft_neg [Neg K] (f : Assignment (DisjointSumHom Q R) K) :
    (-f).restrictLeft = -f.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_neg [Neg K] (f : Assignment (DisjointSumHom Q R) K) :
    (-f).restrictRight = -f.restrictRight :=
  (rfl)

theorem disjointSum_sub [Sub K] (f₁ f₂ : Assignment Q K) (g₁ g₂ : Assignment R K) :
    disjointSum (f₁ - f₂) (g₁ - g₂) = disjointSum f₁ g₁ - disjointSum f₂ g₂ :=
  ext_restrict rfl rfl

@[simp]
theorem restrictLeft_sub [Sub K] (f g : Assignment (DisjointSumHom Q R) K) :
    (f - g).restrictLeft = f.restrictLeft - g.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_sub [Sub K] (f g : Assignment (DisjointSumHom Q R) K) :
    (f - g).restrictRight = f.restrictRight - g.restrictRight :=
  (rfl)

theorem map_disjointSum {L : Type*} (f : Assignment Q K) (g : Assignment R K) (φ : K → L) :
    (disjointSum f g).map φ = disjointSum (f.map φ) (g.map φ) :=
  ext_restrict rfl rfl

@[simp]
theorem restrictLeft_map {L : Type*} (f : Assignment (DisjointSumHom Q R) K) (φ : K → L) :
    (f.map φ).restrictLeft = f.restrictLeft.map φ :=
  (rfl)

@[simp]
theorem restrictRight_map {L : Type*} (f : Assignment (DisjointSumHom Q R) K) (φ : K → L) :
    (f.map φ).restrictRight = f.restrictRight.map φ :=
  (rfl)

end Algebra

section Order

/-- The pointwise order on a disjoint sum is the order on both restrictions. -/
theorem le_iff_restrict [LE K] {f g : Assignment (DisjointSumHom Q R) K} :
    f ≤ g ↔ f.restrictLeft ≤ g.restrictLeft ∧ f.restrictRight ≤ g.restrictRight :=
  DisjointSumHom.forall_iff (P := fun _ _ e ↦ f e ≤ g e)

@[simp]
theorem disjointSum_le_disjointSum_iff [LE K] {f₁ f₂ : Assignment Q K}
    {g₁ g₂ : Assignment R K} :
    disjointSum f₁ g₁ ≤ disjointSum f₂ g₂ ↔ f₁ ≤ f₂ ∧ g₁ ≤ g₂ :=
  le_iff_restrict

variable [Preorder K] {lo₁ hi₁ : Assignment Q K} {lo₂ hi₂ : Assignment R K}

/-- An assignment on a disjoint sum respects arbitrary bounds exactly when both restrictions
respect the restricted bounds. -/
theorem mem_Icc_iff_restrict {lo hi f : Assignment (DisjointSumHom Q R) K} :
    f ∈ Set.Icc lo hi ↔ f.restrictLeft ∈ Set.Icc lo.restrictLeft hi.restrictLeft ∧
      f.restrictRight ∈ Set.Icc lo.restrictRight hi.restrictRight := by
  simp only [Set.mem_Icc, le_iff_restrict, and_and_and_comm]

/-- An assignment on a disjoint sum respects combined bounds exactly when both of its
restrictions respect the corresponding bounds. -/
theorem mem_Icc_disjointSum_iff {f : Assignment (DisjointSumHom Q R) K} :
    f ∈ Set.Icc (disjointSum lo₁ lo₂) (disjointSum hi₁ hi₂) ↔
      f.restrictLeft ∈ Set.Icc lo₁ hi₁ ∧ f.restrictRight ∈ Set.Icc lo₂ hi₂ := by
  simpa using (mem_Icc_iff_restrict (lo := disjointSum lo₁ lo₂)
    (hi := disjointSum hi₁ hi₂) (f := f))

theorem disjointSum_mem_Icc_iff {f : Assignment Q K} {g : Assignment R K} :
    disjointSum f g ∈ Set.Icc (disjointSum lo₁ lo₂) (disjointSum hi₁ hi₂) ↔
      f ∈ Set.Icc lo₁ hi₁ ∧ g ∈ Set.Icc lo₂ hi₂ :=
  mem_Icc_disjointSum_iff

end Order

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
  lower_le_upper := fun {_ _} e ↦
    Assignment.disjointSum_le_disjointSum_iff.2
      ⟨fun _ _ ↦ N.lower_le_upper, fun _ _ ↦ M.lower_le_upper⟩ _ _ e

@[simp]
theorem disjointSum_Hom (N : Network K V) (M : Network K W) :
    (N.disjointSum M).Hom = DisjointSumHom N.Hom M.Hom :=
  (rfl)

@[simp]
theorem disjointSum_lower (N : Network K V) (M : Network K W) :
    (N.disjointSum M).lower = N.lower.disjointSum M.lower :=
  (rfl)

@[simp]
theorem disjointSum_upper (N : Network K V) (M : Network K W) :
    (N.disjointSum M).upper = N.upper.disjointSum M.upper :=
  (rfl)

end Network

section ArrowSum

variable {Q R} {K : Type w} [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)]
  [AddCommMonoid K]

/-- An arrow sum on a disjoint sum splits into arrow sums of the restrictions to its two
summands. -/
theorem arrowSum_eq_restrict_add (f : Assignment (DisjointSumHom Q R) K)
    (S T : Finset (V ⊕ W)) :
    arrowSum f S T = arrowSum f.restrictLeft S.toLeft T.toLeft +
      arrowSum f.restrictRight S.toRight T.toRight := by
  simp only [arrowSum_def, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight,
    Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, add_zero, zero_add]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  · exact DisjointSumHom.sum_inl_inl _
  · exact DisjointSumHom.sum_inr_inr _

/-- An arrow sum of combined assignments splits into the corresponding summand arrow sums. -/
theorem arrowSum_disjointSum (f : Assignment Q K) (g : Assignment R K)
    (S T : Finset (V ⊕ W)) :
    arrowSum (f.disjointSum g) S T =
      arrowSum f S.toLeft T.toLeft + arrowSum g S.toRight T.toRight := by
  simpa using arrowSum_eq_restrict_add (f.disjointSum g) S T

end ArrowSum

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

theorem excessAt_disjointSum (f : Assignment Q K) (g : Assignment R K) :
    excessAt (f.disjointSum g) = Sum.elim (excessAt f) (excessAt g) :=
  funext fun x ↦ by rcases x with x | x <;> simp

@[simp]
theorem isCirculation_disjointSum_iff {f : Assignment Q K} {g : Assignment R K} :
    IsCirculation (f.disjointSum g) ↔ IsCirculation f ∧ IsCirculation g := by
  simp [isCirculation_iff, Sum.forall]

/-- An assignment on a disjoint sum is a circulation exactly when both restrictions are
circulations. -/
theorem isCirculation_iff_restrict {f : Assignment (DisjointSumHom Q R) K} :
    IsCirculation f ↔ IsCirculation f.restrictLeft ∧ IsCirculation f.restrictRight := by
  simp only [isCirculation_iff]
  constructor
  · exact fun hf ↦ ⟨fun x ↦ by simpa using hf (.inl x), fun x ↦ by simpa using hf (.inr x)⟩
  · rintro ⟨hl, hr⟩ (x | x)
    · simpa using hl x
    · simpa using hr x

theorem IsCirculation.restrictLeft {f : Assignment (DisjointSumHom Q R) K}
    (hf : IsCirculation f) : IsCirculation f.restrictLeft :=
  (isCirculation_iff_restrict.1 hf).1

theorem IsCirculation.restrictRight {f : Assignment (DisjointSumHom Q R) K}
    (hf : IsCirculation f) : IsCirculation f.restrictRight :=
  (isCirculation_iff_restrict.1 hf).2

namespace ExcessFlow

variable [Preorder K]
  {lo hi : Assignment (DisjointSumHom Q R) K} {b : V ⊕ W → K}
  {lo₁ hi₁ : Assignment Q K} {lo₂ hi₂ : Assignment R K} {b₁ : V → K} {b₂ : W → K}

/-- Restrict a prescribed-excess assignment on a disjoint sum to its left summand. -/
def restrictLeft (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) :=
  ⟨f.val.restrictLeft, (Assignment.mem_Icc_iff_restrict.1 f.mem_Icc).1,
    funext fun x ↦ by simp [congrFun f.property.2 (.inl x)]⟩

/-- Restrict a prescribed-excess assignment on a disjoint sum to its right summand. -/
def restrictRight (f : ExcessFlow lo hi b) :
    ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) :=
  ⟨f.val.restrictRight, (Assignment.mem_Icc_iff_restrict.1 f.mem_Icc).2,
    funext fun x ↦ by simp [congrFun f.property.2 (.inr x)]⟩

/-- Combine prescribed-excess assignments on two arrow families with no arrows between them. -/
def disjointSum (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂) :=
  ⟨f.val.disjointSum g.val, Assignment.disjointSum_mem_Icc_iff.2 ⟨f.mem_Icc, g.mem_Icc⟩, by
    rw [excessAt_disjointSum, f.property.2, g.property.2]⟩

@[simp]
theorem disjointSum_val (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    (f.disjointSum g).val = f.val.disjointSum g.val :=
  (rfl)

@[simp]
theorem restrictLeft_val (f : ExcessFlow lo hi b) :
    f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val (f : ExcessFlow lo hi b) :
    f.restrictRight.val = f.val.restrictRight :=
  (rfl)

@[simp]
theorem restrictLeft_disjointSum (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    (f.disjointSum g).restrictLeft = f :=
  (rfl)

@[simp]
theorem restrictRight_disjointSum (f : ExcessFlow lo₁ hi₁ b₁) (g : ExcessFlow lo₂ hi₂ b₂) :
    (f.disjointSum g).restrictRight = g :=
  (rfl)

/-- A prescribed-excess assignment on a disjoint sum is reconstructed from its two
restrictions. -/
@[simp]
theorem disjointSum_restrict
    (f : ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂)) :
    f.restrictLeft.disjointSum f.restrictRight = f :=
  Subtype.ext f.val.disjointSum_restrict

/-- Prescribed-excess assignments on a disjoint sum are exactly pairs of such assignments on its
two summands. -/
def disjointSumEquiv :
    ExcessFlow lo hi b ≃
      ExcessFlow lo.restrictLeft hi.restrictLeft (b ∘ Sum.inl) ×
        ExcessFlow lo.restrictRight hi.restrictRight (b ∘ Sum.inr) where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun p :=
    ⟨p.1.val.disjointSum p.2.val, Assignment.mem_Icc_iff_restrict.2
      ⟨by simpa using p.1.mem_Icc, by simpa using p.2.mem_Icc⟩, by
        rw [excessAt_disjointSum, p.1.property.2, p.2.property.2]
        ext x
        rcases x with x | x <;> rfl⟩
  left_inv f := Subtype.ext f.val.disjointSum_restrict
  right_inv p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp]
theorem disjointSumEquiv_apply (f : ExcessFlow lo hi b) :
    disjointSumEquiv f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem disjointSumEquiv_symm_apply (p : ExcessFlow lo₁ hi₁ b₁ × ExcessFlow lo₂ hi₂ b₂) :
    (@Equiv.symm
      (ExcessFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂) (Sum.elim b₁ b₂))
      (ExcessFlow (lo₁.disjointSum lo₂).restrictLeft
          (hi₁.disjointSum hi₂).restrictLeft b₁ ×
        ExcessFlow (lo₁.disjointSum lo₂).restrictRight
          (hi₁.disjointSum hi₂).restrictRight b₂)
      disjointSumEquiv) p = p.1.disjointSum p.2 :=
  (rfl)

end ExcessFlow

namespace ExcessIntervalFlow

variable [Preorder K]
  {lo hi : Assignment (DisjointSumHom Q R) K} {a b : V ⊕ W → K}
  {lo₁ hi₁ : Assignment Q K} {lo₂ hi₂ : Assignment R K}
  {a₁ b₁ : V → K} {a₂ b₂ : W → K}

/-- Restrict an interval-excess assignment on a disjoint sum to its left summand. -/
def restrictLeft (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) :=
  ⟨f.val.restrictLeft, (Assignment.mem_Icc_iff_restrict.1 f.mem_Icc).1,
    ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inl x),
      fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inl x)⟩⟩

/-- Restrict an interval-excess assignment on a disjoint sum to its right summand. -/
def restrictRight (f : ExcessIntervalFlow lo hi a b) :
    ExcessIntervalFlow lo.restrictRight hi.restrictRight (a ∘ Sum.inr) (b ∘ Sum.inr) :=
  ⟨f.val.restrictRight, (Assignment.mem_Icc_iff_restrict.1 f.mem_Icc).2,
    ⟨fun x ↦ by simpa using f.excessAt_mem_Icc.1 (.inr x),
      fun x ↦ by simpa using f.excessAt_mem_Icc.2 (.inr x)⟩⟩

/-- Combine interval-excess assignments on two arrow families with no arrows between them. -/
def disjointSum (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
      (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) :=
  ⟨f.val.disjointSum g.val, Assignment.disjointSum_mem_Icc_iff.2 ⟨f.mem_Icc, g.mem_Icc⟩, by
    rw [excessAt_disjointSum]
    exact ⟨Sum.elim_le_elim_iff.2 ⟨f.excessAt_mem_Icc.1, g.excessAt_mem_Icc.1⟩,
      Sum.elim_le_elim_iff.2 ⟨f.excessAt_mem_Icc.2, g.excessAt_mem_Icc.2⟩⟩⟩

@[simp]
theorem disjointSum_val (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    (f.disjointSum g).val = f.val.disjointSum g.val :=
  (rfl)

@[simp]
theorem restrictLeft_val (f : ExcessIntervalFlow lo hi a b) :
    f.restrictLeft.val = f.val.restrictLeft :=
  (rfl)

@[simp]
theorem restrictRight_val (f : ExcessIntervalFlow lo hi a b) :
    f.restrictRight.val = f.val.restrictRight :=
  (rfl)

@[simp]
theorem restrictLeft_disjointSum (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    (f.disjointSum g).restrictLeft = f :=
  (rfl)

@[simp]
theorem restrictRight_disjointSum (f : ExcessIntervalFlow lo₁ hi₁ a₁ b₁)
    (g : ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    (f.disjointSum g).restrictRight = g :=
  (rfl)

/-- An interval-excess assignment on a disjoint sum is reconstructed from its two
restrictions. -/
@[simp]
theorem disjointSum_restrict (f : ExcessIntervalFlow (lo₁.disjointSum lo₂)
    (hi₁.disjointSum hi₂) (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)) :
    f.restrictLeft.disjointSum f.restrictRight = f :=
  Subtype.ext f.val.disjointSum_restrict

/-- Interval-excess assignments on a disjoint sum are exactly pairs of such assignments on its
two summands. -/
def disjointSumEquiv :
    ExcessIntervalFlow lo hi a b ≃
      ExcessIntervalFlow lo.restrictLeft hi.restrictLeft (a ∘ Sum.inl) (b ∘ Sum.inl) ×
        ExcessIntervalFlow lo.restrictRight hi.restrictRight (a ∘ Sum.inr) (b ∘ Sum.inr) where
  toFun f := (f.restrictLeft, f.restrictRight)
  invFun p :=
    ⟨p.1.val.disjointSum p.2.val, Assignment.mem_Icc_iff_restrict.2
      ⟨by simpa using p.1.mem_Icc, by simpa using p.2.mem_Icc⟩,
      ⟨fun x ↦ by
          rcases x with x | x
          · simpa using p.1.excessAt_mem_Icc.1 x
          · simpa using p.2.excessAt_mem_Icc.1 x,
        fun x ↦ by
          rcases x with x | x
          · simpa using p.1.excessAt_mem_Icc.2 x
          · simpa using p.2.excessAt_mem_Icc.2 x⟩⟩
  left_inv f := Subtype.ext f.val.disjointSum_restrict
  right_inv p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp]
theorem disjointSumEquiv_apply (f : ExcessIntervalFlow lo hi a b) :
    disjointSumEquiv f = (f.restrictLeft, f.restrictRight) :=
  (rfl)

@[simp]
theorem disjointSumEquiv_symm_apply
    (p : ExcessIntervalFlow lo₁ hi₁ a₁ b₁ × ExcessIntervalFlow lo₂ hi₂ a₂ b₂) :
    (@Equiv.symm
      (ExcessIntervalFlow (lo₁.disjointSum lo₂) (hi₁.disjointSum hi₂)
        (Sum.elim a₁ a₂) (Sum.elim b₁ b₂))
      (ExcessIntervalFlow (lo₁.disjointSum lo₂).restrictLeft
          (hi₁.disjointSum hi₂).restrictLeft a₁ b₁ ×
        ExcessIntervalFlow (lo₁.disjointSum lo₂).restrictRight
          (hi₁.disjointSum hi₂).restrictRight a₂ b₂)
      disjointSumEquiv) p = p.1.disjointSum p.2 :=
  (rfl)

end ExcessIntervalFlow

end Excess

end TauCeti
