/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent

/-!
# Base change and descent of pseudo-reductive affine groups

Let `G` be a finite-type affine group over a field `k` with coordinate Hopf algebra `H`, and let
`K / k` be a field extension.

* **Descent along arbitrary field extensions.** Smoothness, geometric connectedness, and triviality
  of the unipotent radical are all reflected by arbitrary field extensions `K / k`, so
  pseudo-reductivity of `G_K` over `K` implies pseudo-reductivity of `G` over `k`.
* **Invariance along separable algebraic field extensions.** When `K / k` is separable algebraic,
  the `k`-unipotent radical commutes with scalar extension to `K`
  (`FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`), so
  pseudo-reductivity is preserved as well as reflected by `K / k`.

The separability hypothesis in the forward direction cannot be omitted: for a nontrivial finite
purely inseparable extension `K / k`, the Weil restriction `Res_{K/k} 𝔾ₘ` is pseudo-reductive over
`k` (`TauCeti.Algebra.WeilRestriction.pseudoReductive_multiplicativeGroup`), whereas its base
change to `AlgebraicClosure k` fails to be pseudo-reductive
(`WeilRestriction.not_pseudoReductive_baseChange_multiplicativeGroup_of_isPurelyInseparable`).

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty.of_baseChange`: pseudo-reductivity descends along
  arbitrary field extensions.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange`: pseudo-reductivity is preserved along
  separable algebraic field extensions.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange_iff`: pseudo-reductivity is invariant
  under separable algebraic field extensions.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9(1).
* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9 and §19.b.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

namespace pseudoReductiveCommHopfAlgProperty

section ArbitraryExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Pseudo-reductivity descends along arbitrary extensions of the ground field. -/
theorem of_baseChange
    (hH : pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    pseudoReductiveCommHopfAlgProperty k H := by
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) :=
    FiniteTypeCommHopfAlgCat.smooth_baseChange_obj hH.smooth
  open FiniteTypeCommHopfAlgCat in
  exact (pseudoReductiveCommHopfAlgProperty_iff k H).mpr
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K,
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hH.geometricallyConnected,
      unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
        hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

end ArbitraryExtension

section Separable

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- Pseudo-reductivity is preserved by separable algebraic extensions of the ground field. -/
theorem baseChange {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  let _ : Algebra.Smooth k H := hH.smooth
  exact (pseudoReductiveCommHopfAlgProperty_iff K _).mpr
    ⟨inferInstance,
      geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hH.geometricallyConnected,
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff
        (K := K) H).mpr hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

-- The defining simp lemma `pseudoReductiveCommHopfAlgProperty_iff` already simplifies the
-- left-hand side, so adding `baseChange_iff` to the simp set would violate `simpNF`.
/-- Pseudo-reductivity of a finite-type affine group is invariant under separable algebraic
extension of the ground field. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      pseudoReductiveCommHopfAlgProperty k H :=
  ⟨of_baseChange, baseChange⟩

end Separable

end pseudoReductiveCommHopfAlgProperty

end TauCeti
