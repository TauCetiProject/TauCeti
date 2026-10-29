/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.NormalSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Normal closed subgroups of reductive groups

A smooth geometrically connected normal closed subgroup of a reductive affine group is
reductive, over any field and in every characteristic. After extension to an algebraic closure,
the subgroup's unipotent radical is normal in the ambient group, and hence lies in its trivial
unipotent radical. The quotient base-change isomorphism then identifies this with the geometric
radical of the original subgroup.

Smoothness and geometric connectedness of the subgroup remain explicit: normal subgroups of
reductive groups can be non-smooth or disconnected. The theorem applies in particular to the
derived subgroup once its smoothness and geometric connectedness have been established, supplying
the reductivity step toward its semisimplicity.

## References

* A. Borel, *Linear Algebraic Groups*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §19.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A smooth geometrically connected normal closed subgroup of a reductive affine group is
reductive. The quotient of coordinate Hopf algebras represents the closed subgroup. -/
theorem quotient_of_isNormal (hH : reductiveCommHopfAlgProperty k H)
    (I : HopfIdeal k H) (hI : I.IsNormal)
    (hsmooth : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I))
    (hconnected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let J := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let N := FiniteTypeCommHopfAlgCat.quotient G J
  let e : N ≅ FiniteTypeCommHopfAlgCat.baseChange (K := K) Q :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso (K := K) I)
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : IsReduced G := isReduced_of_smooth K (K ⊗[k] H)
  have hrad :=
    (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH |>.2.2
  have hN :=
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_quotient_eq_augmentation_of_isNormal
      G J (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI) hrad
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hsmooth, hconnected, ?_⟩
  rw [← HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff
    (FiniteTypeCommHopfAlgCat.toBialgHom e.hom) (ConcreteCategory.bijective_of_isIso e.hom).2,
    FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal,
    HopfIdeal.comapOfSurjective_augmentation]
  exact hN

end TauCeti.reductiveCommHopfAlgProperty
