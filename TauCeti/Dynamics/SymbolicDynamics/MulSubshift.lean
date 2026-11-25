/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import Mathlib.Dynamics.SymbolicDynamics.Basic

/-!
# Subshifts of a group acting on itself are Mathlib's subshifts

When the index set is the group `Γ` itself, acting by left multiplication, a subshift
`TauCeti.Subshift Γ Γ S` is the same as Mathlib's `SymbolicDynamics.FullShift.MulSubshift S Γ`,
a closed set of configurations invariant under the shifts
`SymbolicDynamics.FullShift.mulShift g ω = fun h => ω (g * h)`. The two invariance conditions
match through `g • ω = mulShift g⁻¹ ω` (`TauCeti.Subshift.coe_smul_eq_mulShift`), and as `g` runs
over `Γ` so does `g⁻¹`. The identification is `TauCeti.Subshift.equivMulSubshift`.
-/

public section

open Set SymbolicDynamics.FullShift

namespace TauCeti.Subshift

variable {Γ S : Type*} [Group Γ] [TopologicalSpace S]

/-- For `Γ` acting on itself by left multiplication, the action on a subshift is Mathlib's shift
by the inverse: `g • ω = mulShift g⁻¹ ω`. -/
theorem coe_smul_eq_mulShift {X : Subshift Γ Γ S} (g : Γ) (ω : X) :
    ((g • ω : X) : Γ → S) = mulShift g⁻¹ (ω : Γ → S) :=
  (rfl)

/-- A subshift of `Γ` acting on itself as one of Mathlib's subshifts: the carrier is invariant
under every `mulShift g`, which is the action of `g⁻¹`. -/
def toMulSubshift (X : Subshift Γ Γ S) : MulSubshift S Γ where
  carrier := X
  isClosed := X.isClosed
  mapsTo g ω hω := by
    have h : mulShift g ω = fun i => ω (g⁻¹⁻¹ • i) := funext fun i => by
      rw [mulShift_apply, inv_inv, smul_eq_mul]
    change mulShift g ω ∈ X
    rw [h]
    exact X.smul_mem g⁻¹ hω

/-- One of Mathlib's subshifts as a subshift of `Γ` acting on itself: the action of `g` is
`mulShift g⁻¹`. -/
def ofMulSubshift (Y : MulSubshift S Γ) : Subshift Γ Γ S where
  carrier := Y.carrier
  isClosed := Y.isClosed
  smul_mem' g _ hω := Y.mapsTo g⁻¹ hω

/-- The carrier of the Mathlib subshift attached to a subshift. -/
@[simp]
theorem toMulSubshift_carrier (X : Subshift Γ Γ S) :
    X.toMulSubshift.carrier = (X : Set (Γ → S)) :=
  (rfl)

/-- The configurations of the subshift attached to a Mathlib subshift. -/
@[simp]
theorem mem_ofMulSubshift {Y : MulSubshift S Γ} {ω : Γ → S} :
    ω ∈ ofMulSubshift Y ↔ ω ∈ Y.carrier :=
  Iff.rfl

/-- **Subshifts of a group acting on itself are Mathlib's subshifts.** For `Γ` acting on itself by
left multiplication, `TauCeti.Subshift Γ Γ S` and `SymbolicDynamics.FullShift.MulSubshift S Γ` are
the same closed invariant sets of configurations. -/
def equivMulSubshift : Subshift Γ Γ S ≃ MulSubshift S Γ where
  toFun := toMulSubshift
  invFun := ofMulSubshift
  left_inv _ := ext fun _ => Iff.rfl
  right_inv _ := rfl

/-- The full shift corresponds to Mathlib's full shift. -/
@[simp]
theorem toMulSubshift_top : (⊤ : Subshift Γ Γ S).toMulSubshift = mulFullShift S Γ :=
  (rfl)

end TauCeti.Subshift
