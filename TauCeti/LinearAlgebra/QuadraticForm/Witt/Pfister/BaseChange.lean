/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Basic

/-!
# Base change of Pfister classes

Scalar extension carries a Pfister class to the class with mapped parameters.

## Main result

* `TauCeti.WittRing.baseChange_pfisterClass`: compatibility with Pfister generators.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §1.
-/

public section
noncomputable section

namespace TauCeti

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- Scalar extension carries a Pfister class to the class with mapped parameters. -/
@[simp]
theorem WittRing.baseChange_pfisterClass {n : ℕ} (a : Fin n → Kˣ) :
    WittRing.baseChange (L := L) (pfisterClass a) =
      pfisterClass (fun i ↦ Units.map (algebraMap K L).toMonoidHom (a i)) := by
  simp only [pfisterClass_eq_prod, map_prod, WittRing.baseChange_oneFoldPfisterClass]

end TauCeti
