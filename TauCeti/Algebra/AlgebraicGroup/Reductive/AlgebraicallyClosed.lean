/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent

/-!
# Reductivity over an algebraically closed field

Over an algebraically closed field, reductivity can be tested by the unipotent radical over
the ground field. An algebraic closure of an algebraically closed field is a trivial extension,
so its Hopf ideals descend, together with normality, connectedness and smooth unipotence.
Consequently the geometric fibre of a reductive group is itself reductive. This lets results
over algebraically closed fields be applied to the geometric fibre and then descended.

The subgroup descent uses `CommHopfAlgCat.baseChangeHopfIdeal_surjective` and the existing
normality and geometric-connectedness descent APIs.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 19.
-/

public section

namespace TauCeti

universe u

/-- Over an algebraically closed field, reductivity is equivalent to smoothness, geometric
connectedness and triviality of the unipotent radical over the ground field. -/
theorem reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation
    (k : Type u) [Field k] [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    reductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
            HopfIdeal.augmentation k H := by
  constructor
  · intro hH
    exact ⟨hH.smooth, hH.geometricallyConnected,
      hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩
  · rintro ⟨hsmooth, hconnected, hradical⟩
    rw [reductiveCommHopfAlgProperty_iff]
    refine ⟨hsmooth, hconnected, ?_⟩
    intro I hnormal hconn hu
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := k) (K := AlgebraicClosure k)).2
    obtain ⟨J, rfl⟩ := CommHopfAlgCat.baseChangeHopfIdeal_surjective (H := H.obj) hsurj I
    let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure k) J
    have hJconn : geometricallyConnectedCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient H J).obj :=
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k (AlgebraicClosure k) _
        ((geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso qIso hconn)
    have hJu : smoothUnipotentCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient H J) :=
      smoothUnipotentCommHopfAlgProperty.of_baseChange_of_surjective _ hsurj
        ((smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
          (CategoryTheory.ObjectProperty.isoMk _ qIso) hu)
    have hJ : J = HopfIdeal.augmentation k H :=
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff H).mp
        hradical J (.mk (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hnormal) hJconn hJu)
    rw [hJ, CommHopfAlgCat.baseChangeHopfIdeal_augmentation]

/-- The geometric fibre of a reductive affine group is reductive. -/
theorem reductiveCommHopfAlgProperty.algebraicClosureBaseChange
    {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : reductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation]
  let _ : Algebra.Smooth k H := hH.smooth
  exact ⟨inferInstance,
    geometricallyConnectedCommHopfAlgProperty.baseChange k (AlgebraicClosure k) H.obj
      hH.geometricallyConnected,
    ((reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH).2.2⟩

end TauCeti
