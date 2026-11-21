/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Basic
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Conjugation under base change

Let `H` be a commutative Hopf algebra over `R` and `S` a commutative `R`-algebra. The coordinate
map of left conjugation of the base-changed Hopf algebra `S ⊗[R] H` over `S` is the scalar
extension of the coordinate map of conjugation of `H`, once the target
`(S ⊗[R] H) ⊗[S] (S ⊗[R] H)` is identified with `S ⊗[R] (H ⊗[R] H)`. Geometrically, the
conjugation action of `G_S` on itself is the base change of the conjugation action of `G`.

The comparison is made on points: `S`-algebra maps out of `S ⊗[R] H` are `R`-algebra maps out of
`H`, compatibly with convolution (`TauCeti.AlgHom.baseChangePointsMulEquiv`), and both sides
are the conjugate of the second universal tensor-factor point by the first.

## Main results

* `TauCeti.HopfAlgebra.baseChangeTensorAlgEquiv_symm_comp_conjugationAlgHom`: conjugation
  commutes with base change.
-/

public section

open TensorProduct WithConv
open TauCeti.Algebra.TensorProduct (baseChangeTensorAlgEquiv)

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {S : Type w} {H : Type v}
variable [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring H] [_root_.HopfAlgebra R H]

/-- **Conjugation commutes with base change.** Under the identification
`(S ⊗[R] H) ⊗[S] (S ⊗[R] H) ≃ S ⊗[R] (H ⊗[R] H)`, the coordinate map of conjugation of the
base-changed Hopf algebra `S ⊗[R] H` is the scalar extension of that of `H`. -/
theorem baseChangeTensorAlgEquiv_symm_comp_conjugationAlgHom :
    (baseChangeTensorAlgEquiv R S H H).symm.toAlgHom.comp
        (conjugationAlgHom (R := S) (H := S ⊗[R] H)) =
      Algebra.TensorProduct.map (AlgHom.id S S) (conjugationAlgHom (R := R) (H := H)) := by
  -- Compare the two maps as points of `S ⊗[R] H` over `S ⊗[R] (H ⊗[R] H)`, through the
  -- convolution isomorphism with points of `H` over the same algebra. There each side is the
  -- conjugate of the second universal tensor-factor point by the first.
  let e := AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := S ⊗[R] (H ⊗[R] H))
  have hleft : e.symm (toConv ((baseChangeTensorAlgEquiv R S H H).symm.toAlgHom.comp
      Algebra.TensorProduct.includeLeft)) =
        toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft) := by
    ext h
    simp [e, Algebra.TensorProduct.one_def]
  have hright : e.symm (toConv ((baseChangeTensorAlgEquiv R S H H).symm.toAlgHom.comp
      Algebra.TensorProduct.includeRight)) =
        toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight) := by
    ext h
    simp [e, Algebra.TensorProduct.one_def]
  have hmap : e.symm (toConv (Algebra.TensorProduct.map (AlgHom.id S S)
      (conjugationAlgHom (R := R) (H := H)))) =
        toConv (Algebra.TensorProduct.includeRight.comp (conjugationAlgHom (R := R) (H := H))) := by
    ext h
    simp [e]
  refine toConv_injective (e.symm.injective ?_)
  rw [hmap, comp_conjugationAlgHom, comp_conjugationAlgHom]
  simp only [toConv_ofConv, map_mul, hleft, hright]
  rw [map_inv e.symm, hleft]

end HopfAlgebra

end TauCeti
