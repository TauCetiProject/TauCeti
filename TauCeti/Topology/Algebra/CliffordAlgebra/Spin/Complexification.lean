/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Complexification
public import TauCeti.Topology.Algebra.CliffordAlgebra.BaseChange

/-!
# The unitary part of a complex Spin group

For a real quadratic form `Q`, the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` carries the
conjugate-linear anti-involution `g† = complexConj (reverse g)`, and the unitary part of the
complex Spin group is `{g | g† * g = 1}`. When `Q` is positive definite, `†` is the adjoint for a
positive inner product, and in the polar decomposition `g = (g (g† g)^(-1/2)) (g† g)^(1/2)` of a
complex Spin element the unitary part is the factor onto which the whole group retracts. For
indefinite `Q` no such retraction exists in general: for signature `(1, 1)` the real Spin group is
disconnected, while the complex Spin group of `Q_ℂ` is connected.

This file identifies the unitary part, as a topological space, with the real Spin group of `Q`.
For a nondegenerate form on a finite-dimensional space, extension of scalars is a closed embedding
of Spin groups (`CliffordAlgebra.isClosedEmbedding_spinGroupBaseChange`), and its image is exactly
the unitary part (`CliffordAlgebra.mem_range_spinGroupBaseChange_iff`). For the positive-definite
form on `ℝⁿ` this is the compact group `Spin(n)`, so topological properties of compact Spin, such
as simple connectivity for `n ≥ 3`, transfer to the unitary part of the complex Spin group.

## Main definitions

* `CliffordAlgebra.spinGroupHomeomorphUnitary`: the homeomorphism from the real Spin group of `Q`
  to the unitary part `{g | g† * g = 1}` of the complex Spin group of `Q_ℂ`, given by extension of
  scalars.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V}

/-- **The real Spin group is the unitary part of the complex Spin group.** For a nondegenerate
real quadratic form on a finite-dimensional space, extension of scalars is a homeomorphism from
the Spin group of `Q` onto the Spin elements `g` of `Q_ℂ` with `g† * g = 1`, where
`g† = complexConj (reverse g)`. -/
noncomputable def spinGroupHomeomorphUnitary (hQ : Q.Nondegenerate) :
    spinGroup Q ≃ₜ {g : spinGroup (Q.baseChange ℂ) //
      complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1} :=
  (isClosedEmbedding_spinGroupBaseChange (L := ℂ) Q hQ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (t := {g : spinGroup (Q.baseChange ℂ) |
        complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1}) <|
      Set.ext fun g => MonoidHom.mem_range.symm.trans (mem_range_spinGroupBaseChange_iff hQ g))

/-- The homeomorphism `CliffordAlgebra.spinGroupHomeomorphUnitary` is extension of scalars. -/
@[simp]
theorem coe_spinGroupHomeomorphUnitary_apply (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    (spinGroupHomeomorphUnitary hQ x : spinGroup (Q.baseChange ℂ)) =
      spinGroupBaseChange (A := ℂ) Q x :=
  (rfl)

end CliffordAlgebra
