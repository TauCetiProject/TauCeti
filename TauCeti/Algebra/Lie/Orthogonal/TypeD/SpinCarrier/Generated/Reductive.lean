/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Connected
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.UnipotentRadical
import Mathlib.RingTheory.Etale.Descent

/-!
# Reductivity of the generated type-D spin subgroup

For `4 ≤ n`, the closed subgroup of `GL_(2^n)` generated over a field by the numbered
type-`Dₙ` spin root subgroups and the weight torus is reductive. Its geometric fibre is
the subgroup generated over an algebraic closure. That subgroup is smooth and connected,
and its faithful completely reducible spin representation forces its unipotent radical
to be trivial.

This concerns the subgroup generated over the field. Its comparison with the specialization
of the integral spin carrier, and with the pinned simply connected type-`Dₙ` group scheme,
requires further identifications.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 19.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.

The geometric-fibre descent follows
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Reductive`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.TypeDSpinCarrier

universe u

variable (n : ℕ) (hn : 4 ≤ n) (k : Type u) [Field k]

/-- The subgroup generated over `k` by the numbered type-`Dₙ` spin root subgroups and weight
torus is smooth and geometrically connected, with trivial geometric unipotent radical. -/
theorem reductiveCommHopfAlgProperty_generatedCoordinateHopfAlgebra :
    reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (generatedCoordinateHopfAlgebra n hn k)) := by
  let K := AlgebraicClosure k
  let e := generatedCoordinateHopfAlgebraBaseChangeIso.{u, u} n hn k K
  have hsmooth : smoothCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n hn k)) :=
    (smoothCommHopfAlgProperty K).prop_of_iso e.symm
      (smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra n hn K)
  -- The bundled base change has underlying algebra `K ⊗[k] O(G)`.
  let _ : Algebra.Smooth K (K ⊗[k] generatedCoordinateHopfAlgebra n hn k) := by
    simpa only [CommHopfAlgCat.baseChange, _root_.CommHopfAlgCat.coe_of] using
      (smoothCommHopfAlgProperty_iff _).mp hsmooth
  exact reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
    (FiniteTypeCommHopfAlgCat.of K (generatedCoordinateHopfAlgebra n hn K))
    (Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
      (R := k) (S := generatedCoordinateHopfAlgebra n hn k) K)
    (geometricallyConnectedCommHopfAlgProperty.of_baseChange k K _
      ((geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e.symm
        (geometricallyConnectedCommHopfAlgProperty_generatedCoordinateHopfAlgebra n hn K)))
    (ObjectProperty.isoMk _ e)
    (eq_augmentation_generated_of_isNormal_of_smoothUnipotent n hn K)

end TauCeti.TypeDSpinCarrier
