/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Exterior
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.ExteriorPower
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Transport
import TauCeti.Algebra.AlgebraicGroup.Representation.TensorProduct.Basic

/-!
# Base-point action on exterior flag spaces

When `H` is a commutative Hopf algebra over a commutative ring `R`, the exterior flag space
`TauCeti.exteriorPower.FlagSpace R M d` carries the comodule structure
`TauCeti.Comodule.exteriorFlag R H M d`. This file shows that a base-valued point `g` acts on
`FlagSpace R M d` via `TauCeti.exteriorPower.exteriorFlagMap d`.

## Main results

* `TauCeti.Comodule.basePointsRepresentation_exteriorFlag`: base-valued points act on `FlagSpace`
  by `exteriorPower.exteriorFlagMap`.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

variable {R H M : Type*} [CommRing R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- Base-valued points act on `exteriorPower.FlagSpace R M d` by
`exteriorPower.exteriorFlagMap d`. -/
theorem basePointsRepresentation_exteriorFlag (d : ℕ) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H (exteriorPower.FlagSpace R M d) := exteriorFlag R H M d
     basePointsRepresentation (R := R) (H := H) (exteriorPower.FlagSpace R M d) g) =
      exteriorPower.exteriorFlagMap d (basePointsRepresentation (R := R) (H := H) M g) := by
  induction d with
  | zero =>
    let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
    rw [exteriorFlag_zero, basePointsRepresentation_transport,
      basePointsRepresentation_exteriorPower, exteriorPower.exteriorFlagMap_zero,
      LinearEquiv.symm_symm]
  | succ r ih =>
    let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag R H M r
    let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
    let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
      tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
    rw [exteriorFlag_succ, basePointsRepresentation_transport, exteriorPower.exteriorFlagMap_succ,
      LinearEquiv.symm_symm]
    congr 2
    exact TensorProduct.ext' fun x y ↦ by
      rw [basePointsRepresentation_tensor_tmul, ih, basePointsRepresentation_exteriorPower,
        TensorProduct.map_tmul]

end TauCeti.Comodule
