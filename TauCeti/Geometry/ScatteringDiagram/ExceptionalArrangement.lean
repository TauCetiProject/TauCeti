/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Generic
public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Point exceptions and lines through exceptional arrangements

The common generic locus of infinitely many exceptional arrangements need not be open, and a
common generic point need not have a generic neighbourhood: `ExceptionalArrangement.point` for the
points `1 / (j + 1)` of the real line gives a family of single-point arrangements whose common
generic locus is not open. This contrasts with the open generic locus of one arrangement.

A line starting at a generic point meets an arrangement at only finitely many parameters.

## Attribution

Adapted from `Mei/Geometry/Affine/Generic/Line.lean` and `Mei/Geometry/Affine/Generic/Examples.lean`
in Mei at commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit
are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Affine/Generic/Examples.lean
-/

public section

namespace TauCeti

namespace ExceptionalArrangement

section Point

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [Nontrivial V]

/-- The arrangement whose only exception is a point, in a nontrivial space. -/
noncomputable def point (p : P) : ExceptionalArrangement k P :=
  ⟨{({p} : AffineSubspace k P)}, fun S hS htop => by
    obtain rfl := Finset.mem_singleton.mp hS
    have : Nontrivial P := (vadd_right_injective p).nontrivial
    exact AffineSubspace.singleton_ne_top k V p htop⟩

/-- The only exception of `point p` is the subspace `{p}`. -/
@[simp]
theorem exceptions_point (p : P) :
    (point p : ExceptionalArrangement k P).exceptions = {({p} : AffineSubspace k P)} := (rfl)

/-- A point is generic for `point p` exactly when it differs from `p`. -/
@[simp]
theorem isGeneric_point_iff {p x : P} :
    (point p : ExceptionalArrangement k P).IsGeneric x ↔ x ≠ p := by
  simp [isGeneric_iff]

end Point

section Line

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A line starting at a generic point meets an arrangement at finitely many parameter values.
No transversality or distinctness assumption on its second endpoint is required. -/
theorem finite_setOf_not_isGeneric_lineMap (E : ExceptionalArrangement k P)
    {x : P} (hx : E.IsGeneric x) (y : P) :
    {t : k | ¬ E.IsGeneric (AffineMap.lineMap x y t)}.Finite := by
  have hS (S : AffineSubspace k P) (hS : S ∈ E.exceptions) :
      {t : k | AffineMap.lineMap x y t ∈ S}.Subsingleton :=
    S.subsingleton_preimage_of_notMem (AffineMap.lineMap x y)
      (t₀ := 0) (by simpa only [AffineMap.lineMap_apply_zero] using isGeneric_iff.mp hx S hS)
  have he : {t : k | ¬ E.IsGeneric (AffineMap.lineMap x y t)} =
      ⋃ S ∈ E.exceptions, {t : k | AffineMap.lineMap x y t ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq, isGeneric_iff, not_forall, not_not, Set.mem_iUnion,
      exists_prop]
  rw [he]
  exact E.exceptions.finite_toSet.biUnion fun S hmem => (hS S hmem).finite

end Line

/-- The common generic locus of the arrangements `point (1 / (j + 1))` of the real line is not
open: the exceptional points `1 / (j + 1)` accumulate at `0`, which is a common generic point.
This contrasts with the finite case `isOpen_isGeneric`. -/
theorem not_isOpen_setOf_forall_isGeneric_point :
    ¬ IsOpen {x : ℝ | ∀ j : ℕ,
      (point (1 / ((j : ℝ) + 1)) : ExceptionalArrangement ℝ ℝ).IsGeneric x} := by
  intro hopen
  have h0 : (0 : ℝ) ∈
      {x : ℝ | ∀ j : ℕ, (point (1 / ((j : ℝ) + 1)) : ExceptionalArrangement ℝ ℝ).IsGeneric x} := by
    intro j
    rw [isGeneric_point_iff]
    positivity
  obtain ⟨j, hj⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (hopen.mem_nhds h0)).exists
  exact isGeneric_point_iff.mp (hj j) rfl

end ExceptionalArrangement

end TauCeti
