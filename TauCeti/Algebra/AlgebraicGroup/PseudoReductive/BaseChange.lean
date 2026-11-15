/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent
import Mathlib.RingTheory.Etale.Descent

/-!
# Base change of pseudo-reductive affine groups

Let `H` be a finite-type commutative Hopf algebra over a field `k`, and let `K / k` be a field
extension.

* **Reflection along arbitrary field extensions:** if `K ⊗[k] H` is pseudo-reductive over `K`,
  then `H` is pseudo-reductive over `k`. Smoothness and geometric connectedness descend along
  `k → K`, while the base-changed `k`-unipotent radical is contained in the `K`-unipotent radical,
  so triviality over `K` forces triviality over `k`.
* **Invariance along separable algebraic extensions:** if `K / k` is separable algebraic, formation
  of the unipotent radical commutes with scalar extension (`K / k`), so `K ⊗[k] H` is
  pseudo-reductive over `K` if and only if `H` is pseudo-reductive over `k`.

Over an imperfect base field `k`, preservation can fail for inseparable extensions; indeed, base
changing a non-reductive pseudo-reductive group to `AlgebraicClosure k` uncovers its nontrivial
geometric unipotent radical.

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty.of_baseChange`: pseudo-reductivity descends along
  arbitrary field extensions.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange_of_isSeparable`: separable algebraic field
  extensions preserve pseudo-reductivity.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange_iff_of_isSeparable`: pseudo-reductivity is
  invariant under separable algebraic field extensions.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9, p. 399.
-/

public section

open TauCeti.FiniteTypeCommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.pseudoReductiveCommHopfAlgProperty

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Pseudo-reductivity is reflected by arbitrary extension of the ground field. -/
theorem of_baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    pseudoReductiveCommHopfAlgProperty k H := by
  obtain ⟨hsmooth, hconnected, hradical⟩ := (pseudoReductiveCommHopfAlgProperty_iff K _).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) := hsmooth
  rw [pseudoReductiveCommHopfAlgProperty_iff]
  exact ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K,
    geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hconnected,
    unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation (K := K) hradical⟩

/-- Pseudo-reductivity is preserved by separable algebraic field extensions
(Conrad–Gabber–Prasad, Proposition 1.1.9). -/
theorem baseChange_of_isSeparable [Algebra.IsSeparable k K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  obtain ⟨hsmooth, hconnected, hradical⟩ := (pseudoReductiveCommHopfAlgProperty_iff k H).mp hH
  let _ : Algebra.Smooth k H := hsmooth
  rw [pseudoReductiveCommHopfAlgProperty_iff]
  exact ⟨inferInstance,
    geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hconnected,
    (unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff_of_isSeparable (K := K) H).mpr
      hradical⟩

/-- Along a separable algebraic field extension, pseudo-reductivity is invariant under scalar
extension. -/
theorem baseChange_iff_of_isSeparable [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      pseudoReductiveCommHopfAlgProperty k H :=
  ⟨of_baseChange H, baseChange_of_isSeparable⟩

end TauCeti.pseudoReductiveCommHopfAlgProperty
