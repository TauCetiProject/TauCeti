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

Fix a prime `p` (for instance `p = 2`). The unipotent representation `ρ(t) = [[1, t], [0, 1]]` of
`G = (ℤ_p, +)` on `ℚ_p²` is an extension of two smooth representations: the line spanned by `e₁`
and the quotient line both carry the trivial action. It is not smooth: the stabilizer of `(x, y)`
with `y ≠ 0` is `{0}`, which is not open in `ℤ_p`. Its smooth part is exactly the line spanned by
`e₁`, of dimension `1`, not `2`. So a definition of smooth representations closed under extensions
would be wrong.
-/

public section

open Representation Module

namespace TauCeti.UnipotentSmoothCheck

variable (p : ℕ) [Fact p.Prime]

/-- The unipotent representation `t ↦ [[1, t], [0, 1]]` of `(ℤ_p, +)`, written multiplicatively,
on `ℚ_p × ℚ_p`: `t • (x, y) = (x + t y, y)`. -/
noncomputable def unipotentRep : Representation ℚ_[p] (Multiplicative ℤ_[p]) (ℚ_[p] × ℚ_[p]) where
  toFun t :=
    { toFun v := (v.1 + ((Multiplicative.toAdd t : ℤ_[p]) : ℚ_[p]) * v.2, v.2)
      map_add' v w := by ext <;> simp; ring
      map_smul' a v := by ext <;> simp; ring }
  map_one' := by ext <;> simp
  map_mul' s t := by ext <;> simp; ring

variable {p}

/-- The unipotent representation acts by `(x, y) ↦ (x + t y, y)`. -/
@[simp]
theorem unipotentRep_apply (t : Multiplicative ℤ_[p]) (v : ℚ_[p] × ℚ_[p]) :
    unipotentRep p t v = (v.1 + ((Multiplicative.toAdd t : ℤ_[p]) : ℚ_[p]) * v.2, v.2) :=
  (rfl)

/-- A vector `(x, y)` is smooth for the unipotent representation exactly when `y = 0`. -/
theorem mem_smoothVectors_unipotentRep_iff {v : ℚ_[p] × ℚ_[p]} :
    v ∈ (unipotentRep p).smoothVectors ↔ v.2 = 0 := by
  rw [mem_smoothVectors_iff]
  by_cases hv : v.2 = 0
  · refine iff_of_true ?_ hv
    convert isOpen_univ
    ext t
    simp [mem_stabilizer, hv, Prod.ext_iff]
  · refine iff_of_false ?_ hv
    convert PadicInt.not_isOpen_singleton_one_multiplicative (p := p)
    ext t
    simp [mem_stabilizer, hv, Prod.ext_iff]

/-- The line spanned by `e₁` carries the trivial action. -/
theorem unipotentRep_apply_inl (t : Multiplicative ℤ_[p]) (x : ℚ_[p]) :
    unipotentRep p t (x, 0) = (x, 0) := by
  simp

/-- The quotient by the line spanned by `e₁`, read through the second coordinate, carries the
trivial action. -/
theorem snd_unipotentRep_apply (t : Multiplicative ℤ_[p]) (v : ℚ_[p] × ℚ_[p]) :
    (unipotentRep p t v).2 = v.2 :=
  (rfl)

/-- The smooth part of the unipotent representation is the line spanned by `e₁`. -/
theorem toSubmodule_smoothVectors_unipotentRep :
    (unipotentRep p).smoothVectors.toSubmodule =
      LinearMap.ker (LinearMap.snd ℚ_[p] ℚ_[p] ℚ_[p]) := by
  ext v
  rw [Subrepresentation.mem_toSubmodule, LinearMap.mem_ker, LinearMap.snd_apply]
  exact mem_smoothVectors_unipotentRep_iff

/-- The smooth part of the unipotent representation has dimension `1`, not `2`. -/
theorem finrank_smoothVectors_unipotentRep :
    finrank ℚ_[p] (unipotentRep p).smoothVectors.toSubmodule = 1 := by
  rw [toSubmodule_smoothVectors_unipotentRep, LinearMap.ker_snd,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective, finrank_self]

/-- **The unipotent representation is not smooth**, although it is an extension of two smooth
(trivial) representations: the vector `e₂` has stabilizer `{0}`. -/
theorem not_isSmooth_unipotentRep : ¬ IsSmooth (unipotentRep p) := fun _ ↦ by
  simpa using (mem_smoothVectors_unipotentRep_iff (p := p) (v := (0, 1))).1
    (IsSmooth.mem_smoothVectors _)

end TauCeti.UnipotentSmoothCheck
