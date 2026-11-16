/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Base change and descent of pseudo-reductivity

Let `H` be the coordinate Hopf algebra of a finite-type affine group `G` over a field `k`.
Pseudo-reductivity descends along every field extension `K / k`: smoothness descends by faithfully
flat descent, geometric connectedness descends along arbitrary field extensions, and triviality of
the unipotent radical descends by faithful-flat reflection of Hopf ideals.

In the forward direction, pseudo-reductivity is preserved by every separable algebraic extension
`K / k` (finite or infinite), because formation of the unipotent radical commutes with separable
algebraic base change
(`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`). Over an
inseparable extension pseudo-reductivity can fail to persist, and indeed a pseudo-reductive group
over an arbitrary field `k` is reductive if and only if its geometric unipotent radical descends
to `k`.

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty.of_baseChange`: pseudo-reductivity descends along an
  arbitrary field extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange`: pseudo-reductivity is preserved by
  every separable algebraic extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange_iff`: pseudo-reductivity is invariant
  under separable algebraic extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.
    reductive_iff_baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_eq`:
  a pseudo-reductive group is reductive iff its geometric unipotent radical equals the base change
  of its `k`-unipotent radical.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.
    reductive_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal`:
  a pseudo-reductive group is reductive iff its geometric unipotent radical descends to `k`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9.
* J. S. Milne, *Algebraic Groups* (2017), §§6.47–6.48 and Proposition 19.9.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

namespace pseudoReductiveCommHopfAlgProperty

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

open FiniteTypeCommHopfAlgCat in
/-- Pseudo-reductivity descends along an arbitrary extension of the ground field. -/
theorem of_baseChange
    (hH : pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    pseudoReductiveCommHopfAlgProperty k H := by
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) := hH.smooth
  exact (pseudoReductiveCommHopfAlgProperty_iff k H).mpr
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K,
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hH.geometricallyConnected,
      unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation (K := K)
        hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

/-- Pseudo-reductivity is preserved by every separable algebraic extension of the ground field
(finite or infinite). -/
theorem baseChange [Algebra.IsSeparable k K]
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  let _ : Algebra.Smooth k H := hH.smooth
  exact (pseudoReductiveCommHopfAlgProperty_iff K _).mpr
    ⟨inferInstance,
      geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hH.geometricallyConnected,
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff
        (K := K) H).mpr hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

/-- Pseudo-reductivity is invariant under every separable algebraic extension of the ground field
(finite or infinite). -/
theorem baseChange_iff [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      pseudoReductiveCommHopfAlgProperty k H :=
  ⟨of_baseChange, baseChange⟩

/-- **Descent obstruction to reductivity.** A pseudo-reductive group over an arbitrary field `k`
is reductive if and only if the geometric unipotent radical equals the base change of the
`k`-unipotent radical. -/
theorem reductive_iff_baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_eq
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H ↔
      CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) =
        FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation,
    hH.unipotentRadicalDefiningIdeal_eq_augmentation,
    CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact ⟨fun ⟨_, _, h⟩ ↦ h.symm, fun h ↦ ⟨hH.smooth, hH.geometricallyConnected, h.symm⟩⟩

/-- **A pseudo-reductive group is reductive iff its geometric unipotent radical descends.** Over an
arbitrary field `k`, a pseudo-reductive group is reductive if and only if the defining Hopf ideal
of its geometric unipotent radical is the base change of a Hopf ideal over `k`. -/
theorem reductive_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H ↔
      ∃ J : HopfIdeal k H,
        CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) J =
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [FiniteTypeCommHopfAlgCat.exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff,
    hH.reductive_iff_baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_eq]

end pseudoReductiveCommHopfAlgProperty

end TauCeti
