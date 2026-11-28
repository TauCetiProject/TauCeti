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

namespace SymbolicDynamics.FullShift

/-- Mathlib's shift by `g` is precomposition with the action of `g` on `G` by left
multiplication: `mulShift g ω = fun i => ω (g • i)`. -/
theorem mulShift_eq_fun_smul {G S : Type*} [Monoid G] (g : G) (ω : G → S) :
    mulShift g ω = fun i => ω (g • i) :=
  (rfl)

end SymbolicDynamics.FullShift

namespace TauCeti.Subshift

variable {Γ S : Type*} [Group Γ] [TopologicalSpace S]

/-- For `Γ` acting on itself by left multiplication, the action on a subshift is Mathlib's shift
by the inverse: `g • ω = mulShift g⁻¹ ω`. -/
theorem coe_smul_eq_mulShift {X : Subshift Γ Γ S} (g : Γ) (ω : X) :
    ((g • ω : X) : Γ → S) = mulShift g⁻¹ (ω : Γ → S) :=
  (coe_smul g ω).trans (mulShift_eq_fun_smul g⁻¹ (ω : Γ → S)).symm

/-- A subshift of `Γ` acting on itself as one of Mathlib's subshifts: the carrier is invariant
under every `mulShift g`, which is the action of `g⁻¹`. -/
def toMulSubshift (X : Subshift Γ Γ S) : MulSubshift S Γ where
  carrier := X
  isClosed := X.isClosed
  mapsTo g ω hω := by
    rw [SetLike.mem_coe, mulShift_eq_fun_smul, ← inv_inv g]
    exact X.smul_mem g⁻¹ hω

/-- One of Mathlib's subshifts as a subshift of `Γ` acting on itself: the action of `g` is
`mulShift g⁻¹`. -/
def ofMulSubshift (Y : MulSubshift S Γ) : Subshift Γ Γ S where
  carrier := Y.carrier
  isClosed := Y.isClosed
  smul_mem' g ω hω := mulShift_eq_fun_smul g⁻¹ ω ▸ Y.mapsTo g⁻¹ hω

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

/-- The set of configurations of the subshift attached to a Mathlib subshift. -/
@[simp]
theorem coe_ofMulSubshift (Y : MulSubshift S Γ) :
    ((ofMulSubshift Y : Subshift Γ Γ S) : Set (Γ → S)) = Y.carrier :=
  (rfl)

/-- Going to Mathlib's subshifts and back gives the original subshift. -/
@[simp]
theorem ofMulSubshift_toMulSubshift (X : Subshift Γ Γ S) : ofMulSubshift X.toMulSubshift = X :=
  ext fun _ => Iff.rfl

/-- Going from Mathlib's subshifts and back gives the original Mathlib subshift. -/
@[simp]
theorem toMulSubshift_ofMulSubshift (Y : MulSubshift S Γ) : (ofMulSubshift Y).toMulSubshift = Y :=
  (rfl)

/-- **Subshifts of a group acting on itself are Mathlib's subshifts.** For `Γ` acting on itself by
left multiplication, `TauCeti.Subshift Γ Γ S` and `SymbolicDynamics.FullShift.MulSubshift S Γ` are
the same closed invariant sets of configurations. -/
def equivMulSubshift : Subshift Γ Γ S ≃ MulSubshift S Γ where
  toFun := toMulSubshift
  invFun := ofMulSubshift
  left_inv := ofMulSubshift_toMulSubshift
  right_inv := toMulSubshift_ofMulSubshift

/-- The equivalence sends a subshift to its Mathlib subshift `toMulSubshift`. -/
@[simp]
theorem equivMulSubshift_apply (X : Subshift Γ Γ S) : equivMulSubshift X = X.toMulSubshift :=
  (rfl)

/-- The inverse equivalence sends a Mathlib subshift to `ofMulSubshift` of it. -/
@[simp]
theorem equivMulSubshift_symm_apply (Y : MulSubshift S Γ) :
    equivMulSubshift.symm Y = ofMulSubshift Y :=
  (rfl)

/-- The full shift corresponds to Mathlib's full shift. -/
@[simp]
theorem toMulSubshift_top : (⊤ : Subshift Γ Γ S).toMulSubshift = mulFullShift S Γ :=
  (rfl)

/-- Mathlib's full shift corresponds to the full shift. -/
@[simp]
theorem ofMulSubshift_mulFullShift : ofMulSubshift (mulFullShift S Γ) = ⊤ :=
  ext fun ω => iff_of_true (mem_univ ω) (mem_top ω)

end TauCeti.Subshift
