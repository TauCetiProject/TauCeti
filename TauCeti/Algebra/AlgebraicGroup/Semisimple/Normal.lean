/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Normal
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Normal closed subgroups of semisimple affine groups

A smooth geometrically connected normal closed subgroup of a semisimple affine group is
semisimple, over every field and in every characteristic. Closed subgroups are represented by
Hopf quotients; `CommHopfAlgCat.quotientBaseChangeIso` identifies their geometric fibres with
quotients of the base-changed ambient Hopf algebra.

Smoothness and geometric connectedness of the subgroup are explicit: normal closed subgroups of
semisimple groups can be disconnected or infinitesimal. No perfection of the ground field is
assumed. The theorem recognizes the connected normal factors appearing in decompositions of
semisimple groups, and applies to the derived subgroup once its smoothness and geometric
connectedness have been established.

## References

* A. Borel, *Linear Algebraic Groups*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §21.
-/

public section

open CategoryTheory

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

noncomputable section

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A smooth geometrically connected normal closed subgroup of a semisimple affine group is
semisimple. Hopf quotients represent closed subgroups, so the conclusion is on `H ⧸ I`. -/
theorem quotient_of_isNormal (hH : semisimpleCommHopfAlgProperty k H)
    (I : HopfIdeal k H) (hI : I.IsNormal)
    (hsmooth : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I))
    (hconnected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    semisimpleCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hsmooth, hconnected, ?_⟩
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let J := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let N := FiniteTypeCommHopfAlgCat.quotient G J
  let e : FiniteTypeCommHopfAlgCat.baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient H I) ≅ N :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso (K := K) I).symm
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.Smooth K G := inferInstance
  let _ : IsReduced G := isReduced_of_smooth K G
  have hG :=
    ((semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH).2.2
  have hN :=
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_quotient_eq_augmentation_of_isNormal
      G (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI) hG
  rw [← FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal e, hN]
  exact HopfIdeal.comapOfSurjective_augmentation _ _

end

end TauCeti.semisimpleCommHopfAlgProperty
