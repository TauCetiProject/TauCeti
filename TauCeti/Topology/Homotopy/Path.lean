/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Subpath

/-!
# Path homotopy helpers

Small path and path-homotopy quotient lemmas used by the universal-cover construction. The
quotient subpath identities are adapted from Kim Morrison's Mathlib universal-cover drafts,
especially [#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292), following the earlier
Tau Ceti work in [#42](https://github.com/TauCetiProject/TauCeti/pull/42).
-/

public section

open scoped unitInterval
open Topology Set

namespace Path
variable {X : Type*} [TopologicalSpace X]

/-- Restrict a path whose image lies in a subset to a path in the corresponding subtype.
The source and target are the given subtype endpoints, and coercing the restricted path back to
`X` recovers the original path pointwise. -/
def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- The underlying point of `γ.codRestrict hmem` at time `t` is just `γ t`, viewed in `X`. -/
@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) (t : I) :
    (γ.codRestrict hmem t : X) = γ t := by
  rfl

/-- Mapping `γ.codRestrict hmem` back along the subtype inclusion recovers `γ`. -/
@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val)
    (hmem : ∀ t, γ t ∈ s) :
    (γ.codRestrict hmem).map continuous_subtype_val = γ := by
  ext t
  simp

/-- If the extended path stays inside `U` throughout `[t₀, t₁]`, then the truncated subpath has
range in `U`. -/
theorem truncateOfLE_range_subset_preimage {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

/-- The family of initial segments of `γ : Path a b`: at parameter `t : I`, the path
`s ↦ γ.extend (min s t)` from `a` to `γ t` (`initialSegmentFamily_apply`). At `t = 0` this is
the constant path at `a` (`initialSegmentFamily_zero`); at `t = 1` it is `γ` itself, up to a
trivial right-endpoint cast (`initialSegmentFamily_one`). The property consumers actually need
is joint continuity in `(t, s)`, recorded as `continuous_initialSegmentFamily_uncurry`. -/
noncomputable def initialSegmentFamily {a b : X} (γ : Path a b) (t : I) :
    Path a (γ t) :=
  (γ.truncate 0 t).cast (by rw [min_eq_left t.2.1, γ.extend_zero]) (γ.extend_apply t.2).symm

theorem continuous_initialSegmentFamily_uncurry {a b : X} (γ : Path a b) :
    Continuous ↿(initialSegmentFamily γ) := by
  have hincl : Continuous (fun ts : I × I ↦ ((ts.1 : ℝ), ts.2) : I × I → ℝ × I) := by fun_prop
  have htrunc : Continuous (fun ts : I × I ↦ γ.truncate 0 ts.1 ts.2 : I × I → X) :=
    (γ.truncate_const_continuous_family 0).comp hincl
  simpa [initialSegmentFamily] using! htrunc

@[simp] private theorem initialSegmentFamily_apply {a b : X} (γ : Path a b) (t s : I) :
    initialSegmentFamily γ t s = γ.extend (min (s : ℝ) t) := by
  simp [initialSegmentFamily, Path.truncate, max_eq_left s.2.1]

@[simp] theorem initialSegmentFamily_zero {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 0 = (Path.refl a).cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, γ.extend_zero, Path.refl, min_eq_right s.2.1]

@[simp] theorem initialSegmentFamily_one {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 1 = γ.cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, min_eq_left s.2.2, γ.extend_apply s.2]

end Path

namespace Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient

/-- The quotient topology on path-homotopy classes. This instance is load-bearing:
`Path.Homotopic.Quotient` is a `def` over `Quotient`, and instance search does not unfold it to
find the generic `TopologicalSpace (Quotient _)`. -/
instance instTopologicalSpace (x₀ x : X) :
    TopologicalSpace (Path.Homotopic.Quotient x₀ x) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- A set of path-homotopy classes is open exactly when its preimage under quotient
construction is open. -/
theorem isOpen_iff_preimage_mk {x₀ x₁ : X} {S : Set (Path.Homotopic.Quotient x₀ x₁)} :
    IsOpen S ↔ IsOpen ((Path.Homotopic.Quotient.mk : Path x₀ x₁ →
      Path.Homotopic.Quotient x₀ x₁) ⁻¹' S) :=
  -- `Iff.rfl` is valid because `instTopologicalSpace` above is by definition the quotient
  -- topology (`inferInstanceAs`), so `IsOpen S` unfolds to openness of the `mk`-preimage.
  Iff.rfl

/-- In the path-homotopy quotient, concatenating adjacent subpaths of `p` gives the larger
subpath from the first endpoint to the last endpoint. -/
@[simp]
theorem subpath_trans {x y : X} (p : Path x y) (a b c : unitInterval) :
    trans (mk (p.subpath a b)) (mk (p.subpath b c)) =
      mk (p.subpath a c) := by
  simp only [← mk_trans, eq]
  exact ⟨Path.Homotopy.subpathTransSubpath p a b c⟩

/-- A degenerate subpath represents the reflexivity class at its endpoint. -/
theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]

/-- The full `[0,1]` subpath represents the original path, up to the endpoint casts inserted by
`Path.subpath`. -/
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

/-- Casting the reflexivity class at `x` along `h : y = x` gives the reflexivity class at `y`. -/
@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (refl x).cast h h = refl y := by
  -- After `cases h` the cast is along `rfl`, and `Quotient.cast` on a literal `refl` class
  -- reduces definitionally, so `rfl` closes the goal.
  cases h; rfl

/-- If `trans γ (symm γ') = refl`, then `γ = γ'`.
This is the quotient analogue of `eq_of_div_eq_one : a / b = 1 → a = b`. -/
theorem eq_of_trans_symm {γ γ' : Homotopic.Quotient x₀ x₁}
    (h : trans γ (symm γ') = refl x₀) : γ = γ' := by
  induction γ using Quotient.ind with | mk γ =>
  induction γ' using Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic
