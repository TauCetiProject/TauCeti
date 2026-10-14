/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.EReal.Quantale
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic

/-!
# Infimal transforms for extended costs

For an extended cost `c : X × Y → EReal`, `cTransformExtended c φ` is the largest partner
`ψ` satisfying `φ x + ψ y ≤ c (x, y)`. Its infimum uses Mathlib's additive residuation,
rather than ordinary subtraction. Thus a forbidden pair with cost `⊤` imposes no restriction,
including when the potential is itself infinite. At finite costs this transform agrees with
`TauCeti.cTransform`. Extended nonnegative costs enter by coercion to `EReal`.

The symmetric transform, the antitone Galois connection, double- and triple-transform laws,
and improvement of feasible pairs need no topology. Analytic strict sublevels and completion
measurability are treated in `TauCeti.MeasureTheory.OptimalTransport.CTransform.Analytic`.

Two exact formulas exercise the infinite-cost convention: the everywhere-infinite cost has
everywhere-infinite transform, and a diagonal barrier with zero diagonal has transform `-φ`.
The latter permits arbitrary extended potentials and nonconstant finite potentials.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 5.

The safe arithmetic is Mathlib's `AddQuantale.rightAddResiduation`; the transform identities
use its adjunction and Mathlib's `GaloisConnection` API.
-/

public section

noncomputable section

namespace TauCeti

variable {X Y : Type*}

/-- The infimal transform for an extended cost, using the largest `b` satisfying
`φ x + b ≤ c (x, y)` in place of unsafe extended subtraction. -/
def cTransformExtended (c : X × Y → EReal) (φ : X → EReal) (y : Y) : EReal :=
  ⨅ x, AddQuantale.rightAddResiduation (φ x) (c (x, y))

/-- The symmetric infimal transform for an extended cost. -/
def cTransformSymmExtended (c : X × Y → EReal) (ψ : Y → EReal) (x : X) : EReal :=
  ⨅ y, AddQuantale.rightAddResiduation (ψ y) (c (x, y))

variable {c d : X × Y → EReal} {φ : X → EReal} {ψ : Y → EReal} {a : EReal}
  {x : X} {y : Y}

/-- The defining infimum for the extended-cost transform. -/
theorem cTransformExtended_apply (c : X × Y → EReal) (φ : X → EReal) (y : Y) :
    cTransformExtended c φ y = ⨅ x, AddQuantale.rightAddResiduation (φ x) (c (x, y)) := (rfl)

/-- The defining infimum for the symmetric extended-cost transform. -/
theorem cTransformSymmExtended_apply (c : X × Y → EReal) (ψ : Y → EReal) (x : X) :
    cTransformSymmExtended c ψ x = ⨅ y, AddQuantale.rightAddResiduation (ψ y) (c (x, y)) := (rfl)

/-- The symmetric transform is the transform of the transposed cost. -/
theorem cTransformSymmExtended_eq_cTransformExtended (c : X × Y → EReal) (ψ : Y → EReal) :
    cTransformSymmExtended c ψ = cTransformExtended (fun z : Y × X ↦ c (z.2, z.1)) ψ := (rfl)

/-- Each source point bounds the extended-cost transform at each target point. -/
theorem cTransformExtended_le (c : X × Y → EReal) (φ : X → EReal) (x : X) (y : Y) :
    cTransformExtended c φ y ≤ AddQuantale.rightAddResiduation (φ x) (c (x, y)) :=
  iInf_le _ x

/-- Each target point bounds the symmetric extended-cost transform at each source point. -/
theorem cTransformSymmExtended_le (c : X × Y → EReal) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymmExtended c ψ x ≤ AddQuantale.rightAddResiduation (ψ y) (c (x, y)) :=
  iInf_le _ y

/-- A lower bound for the transform is exactly a feasible constant partner at this target point. -/
theorem le_cTransformExtended_apply_iff :
    a ≤ cTransformExtended c φ y ↔ ∀ x, φ x + a ≤ c (x, y) := by
  simp only [cTransformExtended_apply, le_iInf_iff,
    AddQuantale.rightAddResiduation_le_iff_add_le]

/-- A lower bound for the symmetric transform is exactly a feasible partner at this source point. -/
theorem le_cTransformSymmExtended_apply_iff :
    a ≤ cTransformSymmExtended c ψ x ↔ ∀ y, a + ψ y ≤ c (x, y) := by
  simp only [cTransformSymmExtended_apply, le_iInf_iff,
    AddQuantale.rightAddResiduation_le_iff_add_le, add_comm a]

/-- The extended-cost transform of `φ` is the largest target potential dual feasible against `φ`. -/
theorem le_cTransformExtended_iff :
    ψ ≤ cTransformExtended c φ ↔ ∀ x y, φ x + ψ y ≤ c (x, y) := by
  simp only [Pi.le_def, le_cTransformExtended_apply_iff]
  exact forall_comm

/-- The symmetric extended-cost transform of `ψ` is the largest source potential dual feasible
against `ψ`. -/
theorem le_cTransformSymmExtended_iff :
    φ ≤ cTransformSymmExtended c ψ ↔ ∀ x y, φ x + ψ y ≤ c (x, y) := by
  simp only [Pi.le_def, le_cTransformSymmExtended_apply_iff]

/-- A potential and its extended-cost transform satisfy the dual constraint everywhere. -/
theorem add_cTransformExtended_le (c : X × Y → EReal) (φ : X → EReal) (x : X) (y : Y) :
    φ x + cTransformExtended c φ y ≤ c (x, y) :=
  le_cTransformExtended_apply_iff.mp le_rfl x

/-- The symmetric transform satisfies the dual constraint everywhere. -/
theorem cTransformSymmExtended_add_le (c : X × Y → EReal) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymmExtended c ψ x + ψ y ≤ c (x, y) :=
  le_cTransformSymmExtended_apply_iff.mp le_rfl y

/-- The two transforms form an antitone Galois connection, including infinite costs and
potentials, without any side conditions on extended arithmetic. -/
theorem cTransformExtended_galoisConnection (c : X × Y → EReal) :
    GaloisConnection (fun φ : X → EReal ↦ OrderDual.toDual (cTransformExtended c φ))
      (fun ψ : (Y → EReal)ᵒᵈ ↦ cTransformSymmExtended c (OrderDual.ofDual ψ)) := fun _ _ ↦
  le_cTransformExtended_iff.trans le_cTransformSymmExtended_iff.symm

/-- The extended-cost transform reverses the order of potentials. -/
theorem cTransformExtended_antitone (c : X × Y → EReal) : Antitone (cTransformExtended c) :=
  (cTransformExtended_galoisConnection c).monotone_l

/-- The symmetric extended-cost transform reverses the order of potentials. -/
theorem cTransformSymmExtended_antitone (c : X × Y → EReal) :
    Antitone (cTransformSymmExtended c) :=
  fun _ _ h ↦ (cTransformExtended_galoisConnection c).monotone_u h

/-- A potential is dominated by its double transform, including for the everywhere-infinite cost. -/
theorem le_cTransformSymmExtended_cTransformExtended (c : X × Y → EReal) (φ : X → EReal) :
    φ ≤ cTransformSymmExtended c (cTransformExtended c φ) :=
  (cTransformExtended_galoisConnection c).le_u_l φ

/-- A target potential is dominated by its double transform. -/
theorem le_cTransformExtended_cTransformSymmExtended (c : X × Y → EReal) (ψ : Y → EReal) :
    ψ ≤ cTransformExtended c (cTransformSymmExtended c ψ) :=
  (cTransformExtended_galoisConnection c).l_u_le ψ

/-- Three extended-cost transforms equal one. -/
@[simp]
theorem cTransformExtended_cTransformSymmExtended_cTransformExtended
    (c : X × Y → EReal) (φ : X → EReal) :
    cTransformExtended c (cTransformSymmExtended c (cTransformExtended c φ)) =
      cTransformExtended c φ :=
  (cTransformExtended_galoisConnection c).l_u_l_eq_l φ

/-- Three symmetric extended-cost transforms equal one. -/
@[simp]
theorem cTransformSymmExtended_cTransformExtended_cTransformSymmExtended
    (c : X × Y → EReal) (ψ : Y → EReal) :
    cTransformSymmExtended c (cTransformExtended c (cTransformSymmExtended c ψ)) =
      cTransformSymmExtended c ψ :=
  (cTransformExtended_galoisConnection c).u_l_u_eq_u ψ

/-- Increasing the cost increases its transform. -/
theorem cTransformExtended_mono_cost (h : c ≤ d) (φ : X → EReal) :
    cTransformExtended c φ ≤ cTransformExtended d φ := fun y ↦
  le_cTransformExtended_apply_iff.mpr fun x ↦ (add_cTransformExtended_le c φ x y).trans (h (x, y))

/-- Increasing the cost increases its symmetric transform. -/
theorem cTransformSymmExtended_mono_cost (h : c ≤ d) (ψ : Y → EReal) :
    cTransformSymmExtended c ψ ≤ cTransformSymmExtended d ψ := fun x ↦
  le_cTransformSymmExtended_apply_iff.mpr fun y ↦
    (cTransformSymmExtended_add_le c ψ x y).trans (h (x, y))

/-- Shifting a potential by a real constant shifts its extended-cost transform by the
opposite constant, preserving the normalization freedom of dual potentials. -/
theorem cTransformExtended_add_const (c : X × Y → EReal) (φ : X → EReal) (r : ℝ) (y : Y) :
    cTransformExtended c (fun x ↦ φ x + (r : EReal)) y =
      cTransformExtended c φ y - (r : EReal) := by
  simp only [cTransformExtended_apply, EReal.rightAddResiduation_add_coe, EReal.iInf_sub_coe]

/-- Shifting a target potential by a real constant shifts its symmetric transform oppositely. -/
theorem cTransformSymmExtended_add_const (c : X × Y → EReal) (ψ : Y → EReal)
    (r : ℝ) (x : X) :
    cTransformSymmExtended c (fun y ↦ ψ y + (r : EReal)) x =
      cTransformSymmExtended c ψ x - (r : EReal) := by
  simp only [cTransformSymmExtended_eq_cTransformExtended, cTransformExtended_add_const]

/-- The extended-cost transform agrees with the existing transform for a finite real cost. -/
@[simp]
theorem cTransformExtended_coe (c : X × Y → ℝ) (φ : X → EReal) :
    cTransformExtended (fun z ↦ (c z : EReal)) φ = cTransform c φ := by
  funext y
  simp only [cTransformExtended_apply, EReal.rightAddResiduation_coe, cTransform_apply]

/-- The symmetric extended-cost transform agrees with the finite-real transform. -/
@[simp]
theorem cTransformSymmExtended_coe (c : X × Y → ℝ) (ψ : Y → EReal) :
    cTransformSymmExtended (fun z ↦ (c z : EReal)) ψ = cTransformSymm c ψ := by
  funext x
  simp only [cTransformSymmExtended_apply, EReal.rightAddResiduation_coe, cTransformSymm_apply]

/-- A transform over an empty source has value `⊤`. -/
@[simp]
theorem cTransformExtended_of_isEmpty [IsEmpty X] (c : X × Y → EReal) (φ : X → EReal) (y : Y) :
    cTransformExtended c φ y = ⊤ := by
  simp [cTransformExtended_apply]

/-- A symmetric transform over an empty target has value `⊤`. -/
@[simp]
theorem cTransformSymmExtended_of_isEmpty [IsEmpty Y] (c : X × Y → EReal)
    (ψ : Y → EReal) (x : X) : cTransformSymmExtended c ψ x = ⊤ := by
  simp [cTransformSymmExtended_apply]

/-- A completely forbidden target fiber imposes no restriction, so its transform is `⊤`. -/
theorem cTransformExtended_eq_top (h : ∀ x, c (x, y) = ⊤) (φ : X → EReal) :
    cTransformExtended c φ y = ⊤ := by
  simp [cTransformExtended_apply, h]

/-- A completely forbidden source fiber has symmetric transform `⊤`. -/
theorem cTransformSymmExtended_eq_top (h : ∀ y, c (x, y) = ⊤) (ψ : Y → EReal) :
    cTransformSymmExtended c ψ x = ⊤ := by
  simp [cTransformSymmExtended_apply, h]

/-- An everywhere-infinite cost has everywhere-infinite transform for every potential. -/
@[simp]
theorem cTransformExtended_top (φ : X → EReal) :
    cTransformExtended (fun _ : X × Y ↦ ⊤) φ = fun _ ↦ ⊤ :=
  funext fun _ ↦ cTransformExtended_eq_top (fun _ ↦ rfl) φ

/-- The symmetric transform of an everywhere-infinite cost is everywhere infinite. -/
@[simp]
theorem cTransformSymmExtended_top (ψ : Y → EReal) :
    cTransformSymmExtended (fun _ : X × Y ↦ ⊤) ψ = fun _ ↦ ⊤ :=
  funext fun _ ↦ cTransformSymmExtended_eq_top (fun _ ↦ rfl) ψ

open scoped Classical in
/-- The zero-diagonal, infinite-off-diagonal barrier transforms every potential to its negative. -/
theorem cTransformExtended_diagonal (φ : X → EReal) :
    cTransformExtended (fun z : X × X ↦ if z.1 = z.2 then 0 else ⊤) φ = fun x ↦ -φ x := by
  classical
  funext x
  apply le_antisymm
  · exact (iInf_le _ x).trans_eq
      (by simp +contextual [EReal.rightAddResiduation_eq, sub_eq_add_neg])
  · refine le_iInf fun y ↦ ?_
    by_cases h : y = x
    · subst y
      by_cases hx : φ x = ⊥ <;> simp [EReal.rightAddResiduation_eq, hx, sub_eq_add_neg]
    · simp [h]

end TauCeti
