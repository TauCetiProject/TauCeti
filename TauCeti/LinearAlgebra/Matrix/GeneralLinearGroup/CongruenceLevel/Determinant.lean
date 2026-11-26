/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2K0` and `TauCeti.GL2K1` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Determinants of the congruence levels of `GL₂`

For a commutative ring `A` and an ideal `I`, the diagonal matrix `diag(u, 1)` of a unit `u` lies
in `K₁(I) ⊆ K₀(I)` and has determinant `u`, so the determinants of `K₀(I)` and `K₁(I)` fill `Aˣ`.

## Main results

* `TauCeti.GL2K1.diagGL_mem`, `TauCeti.GL2K0.diagGL_mem`: `diag(u, 1) ∈ K₁(I) ⊆ K₀(I)`.
* `TauCeti.GL2K1.map_det`, `TauCeti.GL2K0.map_det`: the determinants of `K₁(I)` and `K₀(I)` are
  all of `Aˣ`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13,
  p. 57.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The matrix `diag(u, 1)` lies in `K₁(I)`. -/
theorem GL2K1.diagGL_mem (u : Aˣ) : diagGL ![u, 1] ∈ GL2K1 I := by
  rw [GL2K1.mem_iff]
  simp

/-- The matrix `diag(u, 1)` lies in `K₀(I)`. -/
theorem GL2K0.diagGL_mem (u : Aˣ) : diagGL ![u, 1] ∈ GL2K0 I :=
  GL2K1.le_GL2K0 I (GL2K1.diagGL_mem I u)

/-- **The determinants of `K₁(I)` are all of `Aˣ`.** -/
theorem GL2K1.map_det : (GL2K1 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ ⟨_, GL2K1.diagGL_mem I u, by simp⟩

/-- **The determinants of `K₀(I)` are all of `Aˣ`.** -/
theorem GL2K0.map_det : (GL2K0 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr ((GL2K1.map_det I).ge.trans (Subgroup.map_mono (GL2K1.le_GL2K0 I)))

end TauCeti
