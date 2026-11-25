/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RepresentationTheory.Smooth.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Smoothness is not closed under extensions

The unipotent representation `ρ(t) = [[1, t], [0, 1]]` of `G = (ℤ_2, +)` on `ℚ_2²` is an extension
of two smooth representations: the line spanned by `e₁` and the quotient line both carry the
trivial action. It is not smooth: the stabilizer of `(x, y)` with `y ≠ 0` is `{0}`, which is not
open in `ℤ_2`. Its smooth part is exactly the line spanned by `e₁`, of dimension `1`, not `2`. So
a definition of smooth representations closed under extensions would be wrong
(SmoothRepresentationsOfLocalGroups SR.0.2, *smooth-rep-abelian*, first Check).
-/

@[expose] public section

open Representation Module

namespace TauCeti.UnipotentSmoothCheck

/-- The unipotent representation `t ↦ [[1, t], [0, 1]]` of `(ℤ_2, +)`, written multiplicatively,
on `ℚ_2 × ℚ_2`: `t • (x, y) = (x + t y, y)`. -/
noncomputable def unipotentRep : Representation ℚ_[2] (Multiplicative ℤ_[2]) (ℚ_[2] × ℚ_[2]) where
  toFun t :=
    { toFun v := (v.1 + ((Multiplicative.toAdd t : ℤ_[2]) : ℚ_[2]) * v.2, v.2)
      map_add' v w := by ext <;> simp; ring
      map_smul' a v := by ext <;> simp; ring }
  map_one' := by ext <;> simp
  map_mul' s t := by ext <;> simp; ring

/-- The unipotent representation acts by `(x, y) ↦ (x + t y, y)`. -/
theorem unipotentRep_apply (t : Multiplicative ℤ_[2]) (v : ℚ_[2] × ℚ_[2]) :
    unipotentRep t v = (v.1 + ((Multiplicative.toAdd t : ℤ_[2]) : ℚ_[2]) * v.2, v.2) :=
  rfl

/-- A vector `(x, y)` is smooth for the unipotent representation exactly when `y = 0`. -/
theorem mem_smoothVectors_unipotentRep_iff {v : ℚ_[2] × ℚ_[2]} :
    v ∈ unipotentRep.smoothVectors ↔ v.2 = 0 := by
  rw [mem_smoothVectors_iff]
  by_cases hv : v.2 = 0
  · refine iff_of_true ?_ hv
    convert isOpen_univ
    ext t
    simp [mem_stabilizer, unipotentRep_apply, hv, Prod.ext_iff]
  · refine iff_of_false ?_ hv
    convert PadicInt.not_isOpen_singleton_one_multiplicative (p := 2)
    ext t
    simp [mem_stabilizer, unipotentRep_apply, hv, Prod.ext_iff]

/-- The line spanned by `e₁` carries the trivial action. -/
theorem unipotentRep_apply_inl (t : Multiplicative ℤ_[2]) (x : ℚ_[2]) :
    unipotentRep t (x, 0) = (x, 0) := by
  simp [unipotentRep_apply]

/-- The quotient by the line spanned by `e₁`, read through the second coordinate, carries the
trivial action. -/
theorem snd_unipotentRep_apply (t : Multiplicative ℤ_[2]) (v : ℚ_[2] × ℚ_[2]) :
    (unipotentRep t v).2 = v.2 :=
  rfl

/-- The smooth part of the unipotent representation is the line spanned by `e₁`. -/
theorem toSubmodule_smoothVectors_unipotentRep :
    unipotentRep.smoothVectors.toSubmodule = LinearMap.ker (LinearMap.snd ℚ_[2] ℚ_[2] ℚ_[2]) := by
  ext v
  exact mem_smoothVectors_unipotentRep_iff

/-- The smooth part of the unipotent representation has dimension `1`, not `2`. -/
theorem finrank_smoothVectors_unipotentRep :
    finrank ℚ_[2] unipotentRep.smoothVectors.toSubmodule = 1 := by
  rw [toSubmodule_smoothVectors_unipotentRep, LinearMap.ker_snd,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective, finrank_self]

/-- **The unipotent representation is not smooth**, although it is an extension of two smooth
(trivial) representations: the vector `e₂` has stabilizer `{0}`. -/
theorem not_isSmooth_unipotentRep : ¬ IsSmooth unipotentRep := fun _ ↦ by
  simpa using (mem_smoothVectors_unipotentRep_iff (v := (0, 1))).1
    (IsSmooth.mem_smoothVectors _)

end TauCeti.UnipotentSmoothCheck
