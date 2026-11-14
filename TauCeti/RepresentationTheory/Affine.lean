/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Affine actions associated to cocycles

A representation `ρ` and a one-cocycle `b` define the affine action
`g • v = ρ g v + b g`. This construction retains the original module as its carrier;
install `Representation.affineMulAction` locally to avoid conflicting with the linear action.
Differences transform by `ρ`, and adding a coboundary conjugates the action by a translation.
These facts apply, in particular, to the nonequivariance cocycle of a moment map.
-/

public section

namespace Representation

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (b : G → V)
  (hb : ∀ g h, b (g * h) = ρ g (b h) + b g)

/-- The affine action with linear part `ρ` and translation cocycle `b`.
This is not a global instance: a different cocycle gives a different action on the same carrier. -/
@[instance_reducible]
def affineMulAction : MulAction G V where
  smul g v := ρ g v + b g
  one_smul v := by
    have h : b 1 = b 1 + b 1 := by simpa using hb 1 1
    have hzero : b 1 = 0 := by simpa using h.symm
    -- The action under construction has no evaluation lemma until this definition is complete.
    change ρ 1 v + b 1 = v
    simp [hzero]
  mul_smul g h v := by
    -- Expand the action being constructed; its public evaluation lemma is given below.
    change ρ (g * h) v + b (g * h) = ρ g (ρ h v + b h) + b g
    simp [hb, map_mul, mul_apply_eq_comp, add_assoc]

/-- Evaluation of the affine action. -/
@[simp]
theorem affineMulAction_smul (g : G) (v : V) :
    letI := ρ.affineMulAction b hb
    g • v = ρ g v + b g :=
  (rfl)

/-- The difference of two points transforms by the linear part of the affine action. -/
theorem affineMulAction_smul_sub_smul (g : G) (v w : V) :
    letI := ρ.affineMulAction b hb
    g • v - g • w = ρ g (v - w) := by
  simp [map_sub]

/-- A point is fixed by an affine transformation exactly when its translation is the
corresponding coboundary. -/
theorem affineMulAction_smul_eq_self_iff (g : G) (v : V) :
    letI := ρ.affineMulAction b hb
    g • v = v ↔ b g = v - ρ g v := by
  simp only [affineMulAction_smul, eq_sub_iff_add_eq, add_comm]

/-- Changing a cocycle by `c - ρ g c` conjugates its affine action by translation by `c`. -/
theorem affineMulAction_smul_add {b' : G → V}
    (hb' : ∀ g h, b' (g * h) = ρ g (b' h) + b' g) {c : V} {g : G}
    (hc : b' g = b g + c - ρ g c) (v : V) :
    (letI := ρ.affineMulAction b' hb'; g • (v + c)) =
      (letI := ρ.affineMulAction b hb; g • v) + c := by
  simp only [affineMulAction_smul, hc, map_add]
  abel

end Representation
