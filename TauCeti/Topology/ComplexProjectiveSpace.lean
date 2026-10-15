/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Complex projective space as a quotient of an odd sphere

Complex projective `n`-space `CPⁿ` is modelled as the quotient of the unit sphere `S²ⁿ⁺¹` of
`EuclideanSpace ℂ (Fin (n + 1))` by the action of the unit complex numbers `S¹ ⊆ ℂ` by scalar
multiplication: two unit vectors define the same point exactly when one is a unit complex multiple
of the other (`TauCeti.ComplexProjectiveSpace.mk_eq_mk_iff`). Every complex line through the origin
meets the unit sphere in exactly one such orbit, so this models the space of complex lines in
`ℂⁿ⁺¹`.

The circle is compact, so its action on the sphere is proper
(`TauCeti.properSMul_of_compactSpace`) and the quotient is Hausdorff. It is compact and path
connected as a continuous image of the sphere, and the projection is an open quotient map.

## Main declarations

* `TauCeti.ComplexProjectiveSpace`: complex projective `n`-space as a circle quotient of `S²ⁿ⁺¹`.
* `TauCeti.ComplexProjectiveSpace.mk`: the projection from the unit sphere.
* `TauCeti.ComplexProjectiveSpace.lift`: functions on the sphere invariant under unit complex
  scalars descend to `CPⁿ`.
* `TauCeti.ComplexProjectiveSpace.mk_eq_mk_iff`: two unit vectors define the same point exactly
  when they differ by a unit complex scalar.
* `TauCeti.ComplexProjectiveSpace.isOpenQuotientMap_mk`: the projection is an open quotient map.
* `TauCeti.ComplexProjectiveSpace.instT2Space`, `instCompactSpace`, `instPathConnectedSpace`:
  `CPⁿ` is a compact, path-connected Hausdorff space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6.
* The quotient model and its API adapt Tau Ceti's real projective space in
  `TauCeti/AlgebraicTopology/UniversalCover/RealProjective/Basic.lean`.
-/

public section

namespace TauCeti

open Metric

noncomputable section

/-- Complex projective `n`-space, modelled as the orbit quotient of the unit sphere of
`EuclideanSpace ℂ (Fin (n + 1))` under scalar multiplication by unit complex numbers. -/
def ComplexProjectiveSpace (n : ℕ) : Type :=
  Quotient (MulAction.orbitRel (sphere (0 : ℂ) 1)
    (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))

namespace ComplexProjectiveSpace

variable (n : ℕ)

/-- The quotient topology on complex projective space. -/
instance instTopologicalSpace : TopologicalSpace (ComplexProjectiveSpace n) :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel (sphere (0 : ℂ) 1)
    (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))))

/-- Complex projective space is compact as a quotient of the compact unit sphere. -/
instance instCompactSpace : CompactSpace (ComplexProjectiveSpace n) :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel (sphere (0 : ℂ) 1)
    (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))))

/-- Complex projective space is Hausdorff: the compact circle acts properly on the unit sphere. -/
instance instT2Space : T2Space (ComplexProjectiveSpace n) :=
  have := properSMul_of_compactSpace (sphere (0 : ℂ) 1)
    (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel (sphere (0 : ℂ) 1)
    (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))))

/-- The projection from the unit sphere onto complex projective space. -/
def mk : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → ComplexProjectiveSpace n :=
  Quotient.mk _

/-- Every point of complex projective space has a unit-vector representative. -/
theorem mk_surjective : Function.Surjective (mk n) :=
  Quotient.mk_surjective

/-- To prove a property of every point of complex projective space, it suffices to prove it on
the image of every unit vector. -/
@[elab_as_elim]
protected theorem inductionOn {motive : ComplexProjectiveSpace n → Prop}
    (x : ComplexProjectiveSpace n)
    (h : ∀ y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1, motive (mk n y)) : motive x :=
  Quotient.inductionOn' x h

/-- Two unit vectors define the same point of complex projective space exactly when they differ
by a unit complex scalar. -/
@[simp]
theorem mk_eq_mk_iff (x y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    mk n x = mk n y ↔ ∃ c : sphere (0 : ℂ) 1, c • y = x := by
  unfold mk ComplexProjectiveSpace
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- Unit complex multiples of a unit vector define the same point of complex projective space. -/
@[simp]
theorem mk_smul (c : sphere (0 : ℂ) 1) (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    mk n (c • x) = mk n x :=
  (mk_eq_mk_iff n _ _).2 ⟨c, rfl⟩

/-- A function on the unit sphere invariant under unit complex scalars descends to complex
projective space. -/
protected def lift {α : Sort*} (f : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → α)
    (h : ∀ (c : sphere (0 : ℂ) 1) x, f (c • x) = f x) : ComplexProjectiveSpace n → α :=
  Quotient.lift f fun x y hxy => by
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy)
    exact h c y

/-- Lifting an invariant function and applying it to a representative recovers the function. -/
@[simp]
protected theorem lift_mk {α : Sort*} (f : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → α)
    (h : ∀ (c : sphere (0 : ℂ) 1) x, f (c • x) = f x)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ComplexProjectiveSpace.lift n f h (mk n x) = f x :=
  (rfl)

/-- The projection from the unit sphere onto complex projective space is an open quotient map. -/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk n) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The projection from the unit sphere onto complex projective space is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk n) :=
  (isOpenQuotientMap_mk n).continuous

/-- The lift of an invariant function is continuous at the class of every unit vector at which the
function is continuous, because the projection is an open quotient map. -/
theorem continuousAt_lift {α : Type*} [TopologicalSpace α]
    {f : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → α}
    (h : ∀ (c : sphere (0 : ℂ) 1) x, f (c • x) = f x)
    {x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} (hf : ContinuousAt f x) :
    ContinuousAt (ComplexProjectiveSpace.lift n f h) (mk n x) :=
  (isOpenQuotientMap_mk n).continuousAt_comp_iff.1 hf

/-- Complex projective space is nonempty. -/
instance instNonempty : Nonempty (ComplexProjectiveSpace n) :=
  ⟨mk n ⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- Complex projective space is path connected, as a continuous image of the unit sphere of the
real vector space underlying `ℂⁿ⁺¹`, of real dimension `2n + 2 > 1`. -/
instance instPathConnectedSpace : PathConnectedSpace (ComplexProjectiveSpace n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℂ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_real_of_complex, finrank_euclideanSpace_fin]
    norm_cast
    omega
  have := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere hrank (0 : EuclideanSpace ℂ (Fin (n + 1))) zero_le_one)
  exact Quotient.instPathConnectedSpace

end ComplexProjectiveSpace

end

end TauCeti
