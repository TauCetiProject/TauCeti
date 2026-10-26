/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.Product
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism

/-!
# Products of semisimple affine groups

The direct product of two semisimple affine groups over any field is semisimple.
Smoothness and geometric connectedness are stable under products. After extending scalars
to an algebraic closure, the solvable radical of each factor is trivial; the direct-product
radical calculation therefore gives semisimplicity of the product.

This permits semisimple factors to be assembled without restrictions on the characteristic
or on splitting over the ground field. The proof uses the geometric radical criterion from
`Solvable.Radical.Semisimple` and the base-change tensor comparison from `FiniteType.BaseChange`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 21.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
-/

public section

open CategoryTheory

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k]

/-- The direct product of two semisimple finite-type affine groups is semisimple over any field.
The tensor product is the coordinate Hopf algebra of the direct product of groups. -/
theorem tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K) :
    semisimpleCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨?_, geometricallyConnectedCommHopfAlgProperty.tensorProduct H.obj K.obj
    hH.geometricallyConnected hK.geometricallyConnected, ?_⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp <|
      smoothCommHopfAlgProperty.tensorProduct H.obj K.obj
        ((smoothCommHopfAlgProperty_iff _).mpr hH.smooth)
        ((smoothCommHopfAlgProperty_iff _).mpr hK.smooth)
  · let e := FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K
    have hrad := FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_tensorProduct_eq_augmentation
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) K)
      ((semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
        k H).mp hH).2.2
      ((semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
        k K).mp hK).2.2
    rw [← FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal e, hrad]
    exact HopfIdeal.comapOfSurjective_augmentation _ _

end TauCeti.semisimpleCommHopfAlgProperty
