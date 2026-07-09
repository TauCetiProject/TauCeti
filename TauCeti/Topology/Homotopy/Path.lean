/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Path
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Path homotopy helpers

Small path and path-homotopy quotient lemmas used by the universal-cover construction. The
quotient subpath identities are adapted from Kim Morrison's Mathlib universal-cover drafts,
especially [#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
-/

public section

open scoped unitInterval
open Topology Set

namespace Path
variable {X : Type*} [TopologicalSpace X]

/-- Restrict a path whose image lies in a subset to a path in the corresponding subtype.
The source and target are the given subtype endpoints, and coercing the restricted path back to
`X` recovers the original path pointwise. -/
irreducible_def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) (t : I) :
    (γ.codRestrict hmem t : X) = γ t := by
  simp [codRestrict_def]

@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) :
    (γ.codRestrict hmem).map continuous_subtype_val = γ := by
  ext t
  simp

end Path

/-- A partition of the unit interval `[0, 1]` into `n` segments.
This bundles a monotone sequence `0 = t 0 ≤ ... ≤ t (Fin.last n) = 1`. -/
structure IntervalPartition (n : ℕ) where
  /-- The partition points. -/
  t : Fin (n + 1) → unitInterval
  /-- The partition points are monotone. -/
  mono : Monotone t
  /-- The first partition point is `0`. -/
  t_zero : t 0 = 0
  /-- The last partition point is `1`. -/
  t_last : t (Fin.last n) = 1

namespace IntervalPartition

attribute [simp, grind =] t_zero t_last

/-- `IntervalPartition 0` is empty: a single partition point cannot be simultaneously
`0` and `1`. -/
instance : IsEmpty (IntervalPartition 0) where
  false part := by
    have h0 : part.t 0 = 0 := part.t_zero
    have h1 : part.t 0 = 1 := part.t_last
    exact zero_ne_one (h0.symm.trans h1)

end IntervalPartition

namespace Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient

/-- In the path-homotopy quotient, concatenating adjacent subpaths of `p` gives the larger
subpath from the first endpoint to the last endpoint. -/
@[simp]
theorem subpath_trans {x y : X} (p : Path x y)
    (a b c : unitInterval) (_hab : a ≤ b) (_hbc : b ≤ c) :
    trans (mk (p.subpath a b)) (mk (p.subpath b c)) =
      mk (p.subpath a c) := by
  simp only [← mk_trans, eq]
  exact ⟨Path.Homotopy.subpathTransSubpath p a b c⟩

/-- A degenerate subpath represents the reflexivity class at its endpoint. -/
@[simp]
theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]

/-- The full `[0,1]` subpath represents the original path, up to the endpoint casts inserted by
`Path.subpath`. -/
@[simp]
theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient

end Path

namespace Path.Homotopic
variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- Composing on the left with a null-homotopic loop does not change the homotopy class. -/
theorem trans_left_of_nullhomotopic {γ₀ : Path x₀ x₀} {γ₁ : Path x₀ x₁}
    (hγ₀ : γ₀.Homotopic (Path.refl x₀)) : (γ₀.trans γ₁).Homotopic γ₁ :=
  (hcomp hγ₀ (.refl γ₁)).trans (refl_trans γ₁)

/-- Composing on the right with a null-homotopic loop does not change the homotopy class. -/
theorem trans_right_of_nullhomotopic {γ₀ : Path x₀ x₁} {γ₁ : Path x₁ x₁}
    (hγ₁ : γ₁.Homotopic (Path.refl x₁)) : (γ₀.trans γ₁).Homotopic γ₀ :=
  (hcomp (.refl γ₀) hγ₁).trans (trans_refl γ₀)

/-- If `γ.trans γ'.symm` is nullhomotopic, then `γ` and `γ'` are homotopic.
This is the path-homotopy analogue of `a * b⁻¹ = 1 → a = b`. -/
theorem of_trans_symm {γ γ' : Path x₀ x₁}
    (h : (γ.trans γ'.symm).Homotopic (Path.refl x₀)) : γ.Homotopic γ' :=
  (trans_refl γ).symm |>.trans <|
  (hcomp (.refl γ) (symm_trans γ').symm) |>.trans <|
  (trans_assoc γ γ'.symm γ').symm |>.trans <|
  (hcomp h (.refl γ')) |>.trans <|
  refl_trans γ'

namespace Quotient
variable {x₀ x₁ : X}

@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (refl x).cast h h = refl y := by
  cases h; rfl

/-- If `trans γ (symm γ') = refl`, then `γ = γ'`.
This is the quotient analogue of `a * b⁻¹ = 1 → a = b`. -/
theorem of_trans_symm {γ γ' : Homotopic.Quotient x₀ x₁}
    (h : trans γ (symm γ') = refl x₀) : γ = γ' := by
  induction γ using Quotient.ind with | mk γ =>
  induction γ' using Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic
