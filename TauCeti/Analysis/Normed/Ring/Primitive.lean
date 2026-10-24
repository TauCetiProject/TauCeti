/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import TauCeti.RingTheory.Ideal.Primitive

/-!
# Closedness of primitive ideals

Primitive ideals of a normed ring with summable geometric series are closed. In
particular this applies to unital Banach algebras, without commutativity or a
normalization of the identity's norm. Together with the primitive-ideal
description of the radical, this realizes the radical as an intersection of
closed two-sided ideals.

The annihilator of the quotient by a maximal left ideal `J` consists of those
`a` for which every right multiple `a * x` lies in `J`. Mathlib's
`Submodule.annihilator_quotient` identifies this with a colon ideal, and
`Ideal.IsMaximal.isClosed` gives the closedness of `J`.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
-/

public section

namespace Ideal

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- Primitive ideals in a normed ring with summable geometric series are closed.
In particular, primitive ideals of a unital Banach algebra are closed. -/
theorem IsPrimitive.isClosed {I : Ideal R} (hI : I.IsPrimitive) :
    IsClosed (I : Set R) := by
  obtain ⟨J, hJ, rfl⟩ := (isPrimitive_iff_exists_isMaximal I).mp hI
  have : J.IsMaximal := hJ
  rw [Submodule.annihilator_quotient]
  have hcolon : (J.colon Set.univ : Set R) =
      ⋂ x : R, (fun a : R ↦ a * x) ⁻¹' (J : Set R) := by
    ext a
    simp [Submodule.mem_colon]
  rw [hcolon]
  exact isClosed_iInter fun x ↦ Ideal.IsMaximal.isClosed.preimage (continuous_id.mul_const x)

end Ideal
