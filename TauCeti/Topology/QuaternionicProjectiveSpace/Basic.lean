/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Analysis.Quaternion
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Quaternionic projective space as a quotient of a sphere

Quaternionic projective `n`-space `HPⁿ` is modelled as the quotient of the unit sphere `S⁴ⁿ⁺³`
of the quaternionic coordinate space `ℍⁿ⁺¹ = PiLp 2 (fun _ : Fin (n + 1) ↦ ℍ)` by right
multiplication by the unit quaternions `S³ ⊆ ℍ`: two unit vectors define the same point exactly
when one is a right multiple of the other by a unit quaternion
(`TauCeti.QuaternionicProjectiveSpace.mk_eq_mk_iff`). Every right quaternionic line through the
origin meets the unit sphere in exactly one such orbit, so this models the space of quaternionic
lines in `ℍⁿ⁺¹`. Scalars act on the right so that quaternionic matrices, acting on the left, act
on `HPⁿ`.

The unit quaternions form a compact group, so their action on the sphere is proper
(`TauCeti.properSMul_of_compactSpace`) and the quotient is Hausdorff. It is compact and path
connected as a continuous image of the sphere, and the projection is an open quotient map.

## Main declarations

* `TauCeti.QuaternionicProjectiveSpace`: quaternionic projective `n`-space as a quotient of
  `S⁴ⁿ⁺³` by the unit quaternions.
* `TauCeti.QuaternionicProjectiveSpace.mk`: the projection from the unit sphere.
* `TauCeti.QuaternionicProjectiveSpace.lift`: functions on the sphere invariant under right
  multiplication by unit quaternions descend to `HPⁿ`.
* `TauCeti.QuaternionicProjectiveSpace.mk_eq_mk_iff`: two unit vectors define the same point
  exactly when they differ by a unit quaternion on the right.
* `TauCeti.QuaternionicProjectiveSpace.isOpenQuotientMap_mk`: the projection is an open quotient
  map.
* `TauCeti.QuaternionicProjectiveSpace.instT2Space`, `instCompactSpace`,
  `instPathConnectedSpace`: `HPⁿ` is a compact, path-connected Hausdorff space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6.
* The quotient model and its API follow Tau Ceti's complex projective space in
  `TauCeti/Topology/ComplexProjectiveSpace/Basic.lean`.
-/

public section

namespace TauCeti

open Metric MulOpposite
open scoped RightActions Quaternion

noncomputable section

/-- Quaternionic projective `n`-space, modelled as the orbit quotient of the unit sphere of
`PiLp 2 (fun _ : Fin (n + 1) ↦ ℍ)` under right multiplication by unit quaternions. -/
def QuaternionicProjectiveSpace (n : ℕ) : Type :=
  Quotient (MulAction.orbitRel (sphere (0 : ℍ) 1)ᵐᵒᵖ
    (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1))

namespace QuaternionicProjectiveSpace

variable (n : ℕ)

/-- The quotient topology on quaternionic projective space. -/
instance instTopologicalSpace : TopologicalSpace (QuaternionicProjectiveSpace n) :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel (sphere (0 : ℍ) 1)ᵐᵒᵖ
    (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1))))

/-- Quaternionic projective space is compact as a quotient of the compact unit sphere. -/
instance instCompactSpace : CompactSpace (QuaternionicProjectiveSpace n) :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel (sphere (0 : ℍ) 1)ᵐᵒᵖ
    (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1))))

/-- Quaternionic projective space is Hausdorff: the compact group of unit quaternions acts
properly on the unit sphere. -/
instance instT2Space : T2Space (QuaternionicProjectiveSpace n) :=
  have := properSMul_of_compactSpace (sphere (0 : ℍ) 1)ᵐᵒᵖ
    (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel (sphere (0 : ℍ) 1)ᵐᵒᵖ
    (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1))))

/-- The projection from the unit sphere onto quaternionic projective space. -/
def mk : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 → QuaternionicProjectiveSpace n :=
  Quotient.mk _

/-- Every point of quaternionic projective space has a unit-vector representative. -/
theorem mk_surjective : Function.Surjective (mk n) :=
  Quotient.mk_surjective

/-- To prove a property of every point of quaternionic projective space, it suffices to prove it
on the image of every unit vector. -/
@[elab_as_elim]
protected theorem inductionOn {motive : QuaternionicProjectiveSpace n → Prop}
    (x : QuaternionicProjectiveSpace n)
    (h : ∀ y : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1, motive (mk n y)) : motive x :=
  Quotient.inductionOn' x h

/-- Two unit vectors define the same point of quaternionic projective space exactly when they
differ by a unit quaternion acting on the right. -/
@[simp]
theorem mk_eq_mk_iff (x y : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    mk n x = mk n y ↔ ∃ q : sphere (0 : ℍ) 1, y <• q = x := by
  unfold mk QuaternionicProjectiveSpace
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨unop q, hq⟩, fun ⟨q, hq⟩ ↦ ⟨op q, hq⟩⟩

/-- Right multiples of a unit vector by unit quaternions define the same point of quaternionic
projective space. -/
@[simp]
theorem mk_op_smul (q : sphere (0 : ℍ) 1) (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    mk n (x <• q) = mk n x :=
  (mk_eq_mk_iff n _ _).2 ⟨q, rfl⟩

/-- A function on the unit sphere invariant under right multiplication by unit quaternions
descends to quaternionic projective space. -/
protected def lift {α : Sort*} (f : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 → α)
    (h : ∀ (q : sphere (0 : ℍ) 1) x, f (x <• q) = f x) : QuaternionicProjectiveSpace n → α :=
  Quotient.lift f fun x y hxy => by
    obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    exact h (unop q) y

/-- Lifting an invariant function and applying it to a representative recovers the function. -/
@[simp]
protected theorem lift_mk {α : Sort*} (f : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 → α)
    (h : ∀ (q : sphere (0 : ℍ) 1) x, f (x <• q) = f x)
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    QuaternionicProjectiveSpace.lift n f h (mk n x) = f x :=
  (rfl)

/-- The projection from the unit sphere onto quaternionic projective space is an open quotient
map. -/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk n) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The projection from the unit sphere onto quaternionic projective space is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk n) :=
  (isOpenQuotientMap_mk n).continuous

/-- The lift of an invariant function is continuous at the class of every unit vector at which
the function is continuous, because the projection is an open quotient map. -/
theorem continuousAt_lift {α : Type*} [TopologicalSpace α]
    {f : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 → α}
    (h : ∀ (q : sphere (0 : ℍ) 1) x, f (x <• q) = f x)
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1} (hf : ContinuousAt f x) :
    ContinuousAt (QuaternionicProjectiveSpace.lift n f h) (mk n x) :=
  (isOpenQuotientMap_mk n).continuousAt_comp_iff.1 hf

/-- Quaternionic projective space is nonempty. -/
instance instNonempty : Nonempty (QuaternionicProjectiveSpace n) :=
  ⟨mk n ⟨WithLp.toLp 2 (Pi.single 0 1), by simp⟩⟩

/-- Quaternionic projective space is path connected, as a continuous image of the unit sphere of
the real vector space underlying `ℍⁿ⁺¹`, of real dimension `4n + 4 > 1`. -/
instance instPathConnectedSpace : PathConnectedSpace (QuaternionicProjectiveSpace n) := by
  have hrank : 1 < Module.rank ℝ (PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
    rw [← Module.finrank_eq_rank, finrank_piLp_quaternion, Fintype.card_fin]
    norm_cast
    omega
  have := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere hrank (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) zero_le_one)
  exact Quotient.instPathConnectedSpace

end QuaternionicProjectiveSpace

end

end TauCeti
