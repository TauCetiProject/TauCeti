/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent

/-!
# Pseudo-reductivity under field extensions

Let `H` be a finite-type commutative Hopf algebra over a field `k` and let `K / k` be a field
extension.

* **Descent along arbitrary field extensions:** if `K ⊗[k] H` is pseudo-reductive over `K`, then `H`
  is pseudo-reductive over `k`. Smoothness descends by faithfully flat descent, geometric
  connectedness descends along field extensions, and triviality of the unipotent radical descends
  because `(R_{u,k}(G))_K` is contained in `R_{u,K}(G_K)`.
* **Preservation along separable algebraic extensions:** when `K / k` is separable algebraic,
  formation of the unipotent radical commutes with scalar extension
  (`FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`), so
  pseudo-reductivity is preserved and reflected by `K / k`.

Pseudo-reductivity need not survive an inseparable extension `K / k`, such as when `G` is the Weil
restriction `Res_{K/k} 𝔾ₘ` along a nontrivial finite purely inseparable extension.

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty.of_baseChange`: pseudo-reductivity descends along any
  field extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange`: pseudo-reductivity is preserved by
  separable algebraic field extensions.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange_iff`: along a separable algebraic field
  extension, `G_K` is pseudo-reductive if and only if `G` is pseudo-reductive.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9(1).
* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.pseudoReductiveCommHopfAlgProperty

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

open FiniteTypeCommHopfAlgCat in
/-- Pseudo-reductivity descends along an arbitrary field extension: no smoothness, connectedness,
or separability hypothesis on the base group or extension is needed. -/
theorem of_baseChange
    (hH : pseudoReductiveCommHopfAlgProperty K (baseChange (K := K) H)) :
    pseudoReductiveCommHopfAlgProperty k H := by
  let _ : Algebra.Smooth K (K ⊗[k] H) := hH.smooth
  exact (pseudoReductiveCommHopfAlgProperty_iff k H).mpr
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K,
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hH.geometricallyConnected,
      unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
        hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

open FiniteTypeCommHopfAlgCat in
/-- **Pseudo-reductivity is preserved by separable algebraic field extensions.** -/
theorem baseChange [Algebra.IsSeparable k K]
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K (baseChange (K := K) H) := by
  let _ : Algebra.Smooth k H := hH.smooth
  exact (pseudoReductiveCommHopfAlgProperty_iff K _).mpr
    ⟨Algebra.Smooth.baseChange k H K,
      geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hH.geometricallyConnected,
      (unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff H).mpr
        hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

-- The defining simp lemma `pseudoReductiveCommHopfAlgProperty_iff` already expands the left-hand
-- side, so adding this equivalence to the simp set would violate `simpNF`.
/-- Along a separable algebraic field extension, a finite-type affine group is pseudo-reductive
after base change if and only if it is pseudo-reductive over the ground field. -/
theorem baseChange_iff [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      pseudoReductiveCommHopfAlgProperty k H :=
  ⟨of_baseChange, baseChange⟩

end TauCeti.pseudoReductiveCommHopfAlgProperty
