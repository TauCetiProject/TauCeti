/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Unit representatives in algebraic `K₁`

Bass's surjective stability bound at size one gives representatives by units of the ring,
in particular for semilocal rings. See Weibel, *The K-book*, Chapter III, Remark 1.2.5.
-/

public section

namespace TauCeti.AlgebraicK1

/-- Over a ring of Bass stable range at most one, every algebraic `K₁` class comes from a unit. -/
theorem ofUnits_surjective {R : Type*} [Ring R] (hR : HasStableRangeLE R 1) :
    Function.Surjective (ofUnits R) := by
  intro x
  obtain ⟨g, hg⟩ := mk_surjective hR (n := 1) le_rfl x
  let e := Matrix.uniqueRingEquiv (m := Fin 1) (A := R)
  refine ⟨Units.map e.toMonoidHom g, ?_⟩
  rw [ofUnits_apply, ← hg]
  congr 1
  apply Units.ext
  ext i j
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  simp only [hi, hj, Matrix.GeneralLinearGroup.coe_scalar, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Matrix.scalar_apply]
  exact Matrix.uniqueRingEquiv_apply _

end TauCeti.AlgebraicK1
