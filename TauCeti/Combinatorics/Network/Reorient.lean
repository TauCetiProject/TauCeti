/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Excess
public import TauCeti.Combinatorics.Quiver.Reorient

/-!
# Reorienting network arrows

A Boolean label on an explicit arrow family specifies which arrows to reverse.  Values on reversed
arrows are negated, so an interval of allowed values `[l, u]` becomes `[-u, -l]`.  This operation
preserves both feasibility and excess at every vertex.  It therefore lets bounded-network
arguments choose convenient arrow directions without changing their supply and demand data.

`TauCeti.ReorientedHom` is the explicit-arrow-family form of the hom sets of
`TauCeti.Reorient`.  In particular, parallel arrows remain distinct, and reversing a loop retains
it as a loop.

## Main definitions

* `TauCeti.ReorientedHom`: the arrow family obtained by reversing the selected arrows.
* `TauCeti.reorientAssignmentEquiv`: the additive equivalence which negates reversed values.
* `TauCeti.reorientLower` and `TauCeti.reorientUpper`: the transported bounds.
* `TauCeti.Network.reorient`: a network with selected arrows reversed.

## Main results

* `TauCeti.reorientAssignment_mem_Icc_iff`: reorientation preserves feasibility.
* `TauCeti.excessAt_reorientAssignment`: reorientation preserves excess at every vertex.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- The explicit arrow family obtained from `Q` by reversing exactly the arrows on which `σ` is
true.  This is the hom family of `TauCeti.Reorient` with its quiver argument made explicit. -/
abbrev ReorientedHom (Q : V → V → Type v)
    (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (x y : V) : Type v :=
  {e : Q x y // ¬ σ e} ⊕ {e : Q y x // σ e}

/-- The explicit reoriented arrow family is the hom family of `TauCeti.Reorient` after packaging
`Q` as a quiver. -/
def reorientedHomEquivQuiver (Q : V → V → Type v)
    (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (x y : V) :
    ReorientedHom Q σ x y ≃
      @Quiver.Hom (@Reorient V ⟨Q⟩ σ) (@reorientQuiver V ⟨Q⟩ σ) x y :=
  Equiv.refl _

namespace ReorientedHom

/-- An arrow which is not selected keeps its direction in the reoriented family. -/
def keep (σ : ∀ ⦃x y : V⦄, Q x y → Bool) {x y : V} (e : Q x y) (h : ¬ σ e) :
    ReorientedHom Q σ x y :=
  Sum.inl ⟨e, h⟩

/-- A selected arrow appears with its direction reversed in the reoriented family. -/
def flip (σ : ∀ ⦃x y : V⦄, Q x y → Bool) {x y : V} (e : Q x y) (h : σ e) :
    ReorientedHom Q σ y x :=
  Sum.inr ⟨e, h⟩

end ReorientedHom

section Neg

variable [Neg K]

/-- Transport an assignment across a reorientation, negating the value on every reversed arrow. -/
def reorientAssignment (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (f : Assignment Q K) :
    Assignment (ReorientedHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ f e.1) (fun e ↦ -f e.1) e

/-- Recover an assignment on the original arrows from an assignment on the reoriented arrows. -/
def unreorientAssignment (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment (ReorientedHom Q σ) K) : Assignment Q K :=
  fun {_ _} e ↦ if h : σ e then -f (ReorientedHom.flip σ e h)
    else f (ReorientedHom.keep σ e h)

@[simp]
theorem reorientAssignment_keep (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment Q K) {x y : V} (e : Q x y) (h : ¬ σ e) :
    reorientAssignment σ f (ReorientedHom.keep σ e h) = f e :=
  (rfl)

@[simp]
theorem reorientAssignment_flip (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment Q K) {x y : V} (e : Q x y) (h : σ e) :
    reorientAssignment σ f (ReorientedHom.flip σ e h) = -f e :=
  (rfl)

@[simp]
theorem unreorientAssignment_keep (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment (ReorientedHom Q σ) K) {x y : V} (e : Q x y) (h : ¬ σ e) :
    unreorientAssignment σ f e = f (ReorientedHom.keep σ e h) := by
  simp [unreorientAssignment, h]

@[simp]
theorem unreorientAssignment_flip (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment (ReorientedHom Q σ) K) {x y : V} (e : Q x y) (h : σ e) :
    unreorientAssignment σ f e = -f (ReorientedHom.flip σ e h) := by
  simp [unreorientAssignment, h]

/-- The lower bound after reorientation: a reversed interval `[l, u]` has lower endpoint `-u`. -/
def reorientLower (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K) :
    Assignment (ReorientedHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ lo e.1) (fun e ↦ -hi e.1) e

/-- The upper bound after reorientation: a reversed interval `[l, u]` has upper endpoint `-l`. -/
def reorientUpper (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K) :
    Assignment (ReorientedHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ hi e.1) (fun e ↦ -lo e.1) e

@[simp]
theorem reorientLower_keep (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K)
    {x y : V} (e : Q x y) (h : ¬ σ e) :
    reorientLower σ lo hi (ReorientedHom.keep σ e h) = lo e :=
  (rfl)

@[simp]
theorem reorientLower_flip (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K)
    {x y : V} (e : Q x y) (h : σ e) :
    reorientLower σ lo hi (ReorientedHom.flip σ e h) = -hi e :=
  (rfl)

@[simp]
theorem reorientUpper_keep (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K)
    {x y : V} (e : Q x y) (h : ¬ σ e) :
    reorientUpper σ lo hi (ReorientedHom.keep σ e h) = hi e :=
  (rfl)

@[simp]
theorem reorientUpper_flip (σ : ∀ ⦃x y : V⦄, Q x y → Bool) (lo hi : Assignment Q K)
    {x y : V} (e : Q x y) (h : σ e) :
    reorientUpper σ lo hi (ReorientedHom.flip σ e h) = -lo e :=
  (rfl)

end Neg

section InvolutiveNeg

variable [InvolutiveNeg K]

/-- Recovering an assignment after reorienting it returns the original assignment. -/
@[simp]
theorem unreorientAssignment_reorientAssignment (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment Q K) : unreorientAssignment σ (reorientAssignment σ f) = f := by
  funext x y e
  by_cases h : σ e
  · simp [unreorientAssignment, reorientAssignment, ReorientedHom.flip, h]
  · simp [unreorientAssignment, reorientAssignment, ReorientedHom.keep, h]

/-- Reorienting a recovered assignment returns the original reoriented assignment. -/
@[simp]
theorem reorientAssignment_unreorientAssignment (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment (ReorientedHom Q σ) K) :
    reorientAssignment σ (unreorientAssignment σ f) = f := by
  funext x y e
  obtain e | e := e
  · simp [unreorientAssignment, reorientAssignment, ReorientedHom.keep, e.2]
  · simp [unreorientAssignment, reorientAssignment, ReorientedHom.flip, e.2]

end InvolutiveNeg

section SubtractionCommMonoid

variable [SubtractionCommMonoid K]

/-- Reorienting assignments is an additive equivalence.  Its inverse uses the same selected
arrows and negates their values again. -/
def reorientAssignmentEquiv (σ : ∀ ⦃x y : V⦄, Q x y → Bool) :
    Assignment Q K ≃+ Assignment (ReorientedHom Q σ) K where
  toFun := reorientAssignment σ
  invFun := unreorientAssignment σ
  left_inv := unreorientAssignment_reorientAssignment σ
  right_inv := reorientAssignment_unreorientAssignment σ
  map_add' f g := by
    funext x y e
    obtain e | e := e <;> simp [reorientAssignment, add_comm]

@[simp]
theorem reorientAssignmentEquiv_apply (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment Q K) : reorientAssignmentEquiv σ f = reorientAssignment σ f :=
  (rfl)

@[simp]
theorem reorientAssignmentEquiv_symm_apply (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment (ReorientedHom Q σ) K) :
    (reorientAssignmentEquiv σ).symm f = unreorientAssignment σ f :=
  (rfl)

end SubtractionCommMonoid

section AddCommGroup

variable [AddCommGroup K]

section Order

variable [Preorder K] [AddLeftMono K]

/-- Reorienting selected arrows and negating their values preserves membership in the pointwise
interval between the lower and upper bounds. -/
@[simp]
theorem reorientAssignment_mem_Icc_iff (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (lo hi f : Assignment Q K) :
    reorientLower σ lo hi ≤ reorientAssignment σ f ∧
        reorientAssignment σ f ≤ reorientUpper σ lo hi ↔
      f ∈ Set.Icc lo hi := by
  constructor
  · intro hf
    constructor <;> intro x y e
    · by_cases h : σ e
      · exact neg_le_neg_iff.mp (hf.2 y x (ReorientedHom.flip σ e h))
      · exact hf.1 x y (ReorientedHom.keep σ e h)
    · by_cases h : σ e
      · exact neg_le_neg_iff.mp (hf.1 y x (ReorientedHom.flip σ e h))
      · exact hf.2 x y (ReorientedHom.keep σ e h)
  · intro hf
    constructor <;> intro x y e
    · obtain e | e := e
      · exact hf.1 _ _ e.1
      · exact neg_le_neg_iff.mpr (hf.2 _ _ e.1)
    · obtain e | e := e
      · exact hf.2 _ _ e.1
      · exact neg_le_neg_iff.mpr (hf.1 _ _ e.1)

end Order

section Excess

variable [Fintype V] [∀ x y, Fintype (Q x y)]

/-- Reversing selected arrows and negating their values preserves excess at every vertex. -/
@[simp]
theorem excessAt_reorientAssignment (σ : ∀ ⦃x y : V⦄, Q x y → Bool)
    (f : Assignment Q K) (v : V) : excessAt (reorientAssignment σ f) v = excessAt f v := by
  have hin :
      (∑ x, ∑ e : {e : Q x v // ¬ σ e}, f e.1) +
          ∑ x, ∑ e : {e : Q x v // σ e}, f e.1 = ∑ x, ∑ e : Q x v, f e := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by
      rw [add_comm]
      exact Fintype.sum_subtype_add_sum_subtype _ _
  have hout :
      (∑ y, ∑ e : {e : Q v y // ¬ σ e}, f e.1) +
          ∑ y, ∑ e : {e : Q v y // σ e}, f e.1 = ∑ y, ∑ e : Q v y, f e := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by
      rw [add_comm]
      exact Fintype.sum_subtype_add_sum_subtype _ _
  simp only [excessAt_def, Fintype.sum_sum_type, reorientAssignment, Sum.elim_inl,
    Sum.elim_inr, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← hin, ← hout]
  abel

end Excess

end AddCommGroup

namespace Network

variable [AddCommGroup K]

section LE

variable [LE K] [AddLeftMono K]

/-- Reverse the selected arrows of a network, negate their values, and replace every reversed
interval `[l, u]` by `[-u, -l]`. The body is exposed because the dependent arrow family occurs in
the types of the projection lemmas below. -/
@[expose]
def reorient (N : Network K V) (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool) : Network K V where
  Hom := ReorientedHom N.Hom σ
  lower := reorientLower σ N.lower N.upper
  upper := reorientUpper σ N.lower N.upper
  lower_le_upper e := by
    obtain e | e := e
    · exact N.lower_le_upper e.1
    · exact neg_le_neg_iff.mpr (N.lower_le_upper e.1)

@[simp]
theorem reorient_lower_keep (N : Network K V) (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool)
    {x y : V} (e : N.Hom x y) (h : ¬ σ e) :
    (N.reorient σ).lower (ReorientedHom.keep σ e h) = N.lower e :=
  (rfl)

@[simp]
theorem reorient_lower_flip (N : Network K V) (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool)
    {x y : V} (e : N.Hom x y) (h : σ e) :
    (N.reorient σ).lower (ReorientedHom.flip σ e h) = -N.upper e :=
  (rfl)

@[simp]
theorem reorient_upper_keep (N : Network K V) (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool)
    {x y : V} (e : N.Hom x y) (h : ¬ σ e) :
    (N.reorient σ).upper (ReorientedHom.keep σ e h) = N.upper e :=
  (rfl)

@[simp]
theorem reorient_upper_flip (N : Network K V) (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool)
    {x y : V} (e : N.Hom x y) (h : σ e) :
    (N.reorient σ).upper (ReorientedHom.flip σ e h) = -N.lower e :=
  (rfl)

end LE

/-- An assignment is feasible for a network exactly when its reorientation is feasible for the
reoriented network. -/
@[simp]
theorem reorientAssignment_mem_Icc_reorient_iff [Preorder K] [AddLeftMono K] (N : Network K V)
    (σ : ∀ ⦃x y : V⦄, N.Hom x y → Bool) (f : N.Assignment K) :
    reorientAssignment σ f ∈ Set.Icc (N.reorient σ).lower (N.reorient σ).upper ↔
      f ∈ Set.Icc N.lower N.upper :=
  reorientAssignment_mem_Icc_iff σ N.lower N.upper f

end Network

end TauCeti
