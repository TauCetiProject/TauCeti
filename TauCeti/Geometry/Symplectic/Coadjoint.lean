/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# Coadjoint tangent spaces are symplectic

For a real Lie algebra `L` and `ν ∈ L*`, the Kirillov–Kostant–Souriau form
`ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through
`ν` (`Module.Dual.kksForm`) is alternating and nondegenerate. This file packages it as a linear
`TauCeti.SymplecticForm` (`Module.Dual.kksSymplecticForm ν`). When `L` is the Lie algebra of a Lie
group whose coadjoint orbit through `ν` is a smooth homogeneous space, this is the pointwise value
at `ν` of the symplectic form of the orbit. When `L ⧸ L_ν` is finite-dimensional, its dimension is
even (`Module.Dual.even_finrank_quotient_lieAnnihilator`).

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open Module TauCeti

namespace Module.Dual

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (ν : Dual ℝ L)

/-- The Kirillov–Kostant–Souriau form `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` on the algebraic tangent model
`L ⧸ L_ν` of the coadjoint orbit through `ν`, as a linear symplectic form. -/
noncomputable def kksSymplecticForm : SymplecticForm (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule) where
  toBilinForm := ν.kksForm
  isAlt := ν.isAlt_kksForm
  nondegenerate := ν.kksForm_nondegenerate

@[simp]
theorem kksSymplecticForm_toBilinForm : ν.kksSymplecticForm.toBilinForm = ν.kksForm :=
  (rfl)

/-- The algebraic tangent model `L ⧸ L_ν` of a coadjoint orbit of a real Lie algebra, when
finite-dimensional, has even dimension, since it carries the symplectic form `ω_ν`. -/
theorem even_finrank_quotient_lieAnnihilator
    [FiniteDimensional ℝ (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule)] :
    Even (finrank ℝ (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule)) :=
  ν.kksSymplecticForm.even_finrank

end Module.Dual
