/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.Path

/-!
# The class of a Moore loop in the fundamental group

The class `loopClass γ` of a Moore loop `γ` at `x` in `π₁(X, x)` is the homotopy class of its
reparametrization on the unit interval.  It is constant on the path components of the Moore loop
space, and separates them (`loopClass_eq_iff`), and every class is the class of a Moore loop
(`loopClass_surjective`).  So the set of path components of `Ω_x X` is `π₁(X, x)`.

Concatenation of Moore loops `γ * δ` runs through `γ` first, while the product of
`FundamentalGroup X x` is composition in the fundamental groupoid, which runs through the second
factor first.  So `loopClass` is multiplicative into the *opposite* order (`loopClass_mul`).

## Main definitions

* `TauCeti.MooreLoopSpace.loopClass`: the class of a Moore loop in `π₁(X, x)`.

## Main results

* `TauCeti.MooreLoopSpace.loopClass_eq_iff`: two Moore loops have the same class if and only if
  they are joined by a path of Moore loops.
* `TauCeti.MooreLoopSpace.loopClass_one`, `TauCeti.MooreLoopSpace.loopClass_mul`: the unit and the
  product.
* `TauCeti.MooreLoopSpace.loopClass_surjective`: every class is hit.
-/

public section

open unitInterval

namespace TauCeti

namespace MooreLoopSpace

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The class in `π₁(X, x)` of a Moore loop: the homotopy class of the loop on the unit
interval. -/
def loopClass (γ : MooreLoopSpace X x) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk γ.toPath

theorem loopClass_eq_iff_homotopic {γ δ : MooreLoopSpace X x} :
    loopClass γ = loopClass δ ↔ γ.toPath.Homotopic δ.toPath :=
  Path.Homotopic.Quotient.eq

/-- **Two Moore loops have the same class in `π₁(X, x)` if and only if they lie in the same path
component of the Moore loop space.** -/
theorem loopClass_eq_iff {γ δ : MooreLoopSpace X x} : loopClass γ = loopClass δ ↔ Joined γ δ := by
  rw [loopClass_eq_iff_homotopic]
  constructor
  · rintro ⟨F⟩
    have h : Joined γ.toPath.toMooreLoop δ.toPath.toMooreLoop :=
      ⟨{ toFun := fun s ↦ (F.eval s).toMooreLoop
         continuous_toFun := Path.continuous_toMooreLoop.comp
           (Path.continuous_uncurry_iff.1 F.continuous)
         source' := by simp
         target' := by simp }⟩
    exact (joined_toPath_toMooreLoop γ).trans (h.trans (joined_toPath_toMooreLoop δ).symm)
  · rintro ⟨P⟩
    exact Path.Homotopic.of_continuous
      ⟨fun s ↦ (P s).toPath, continuous_toPath.comp P.continuous⟩ (by simp) (by simp)

/-- The class of the constant loop is trivial. -/
@[simp]
theorem loopClass_one : loopClass (1 : MooreLoopSpace X x) = 1 := by
  rw [loopClass, toPath_one, FundamentalGroup.one_def, Path.Homotopic.Quotient.mk_refl]

/-- **The class of a product of Moore loops** is the product of the classes in the opposite
order: concatenation runs through the first factor first, composition in the fundamental groupoid
through the second factor first. -/
theorem loopClass_mul (γ δ : MooreLoopSpace X x) :
    loopClass (γ * δ) = loopClass δ * loopClass γ := by
  rw [FundamentalGroup.mul_def]
  have h : (γ.toPath.trans δ.toPath).Homotopic (γ * δ).toPath :=
    Path.Homotopic.of_continuous
      ⟨fun s ↦ mulToPathHomotopy x (s, (γ, δ)), by fun_prop⟩ (by simp) (by simp)
  exact (Path.Homotopic.Quotient.eq.2 h.symm).trans
    (Path.Homotopic.Quotient.mk_trans γ.toPath δ.toPath)

/-- Every class in `π₁(X, x)` is the class of a Moore loop. -/
theorem loopClass_surjective : Function.Surjective (loopClass : MooreLoopSpace X x → _) := by
  intro g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  exact ⟨p.toMooreLoop, by rw [loopClass, Path.toPath_toMooreLoop]⟩

end MooreLoopSpace

end TauCeti
