/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Separable base change and descent obstruction for pseudo-reductive groups

Pseudo-reductivity of a finite-type affine group over a field `k` is reflected by every field
extension `K / k` and preserved by every separable algebraic extension `K / k`. In particular,
pseudo-reductivity over `k` is equivalent to triviality of the unipotent radical after scalar
extension to `SeparableClosure k`, matching the characterization of reductivity by triviality of the
unipotent radical over `AlgebraicClosure k`
(`reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`).

Over an arbitrary field extension `K / k`, a pseudo-reductive group over `k` remains
pseudo-reductive after scalar extension to `K` if and only if the `K`-unipotent radical of
`K ⊗[k] H` descends to a Hopf ideal over `k`. Taking `K = AlgebraicClosure k`, a pseudo-reductive
group over `k` is reductive if and only if its geometric unipotent radical descends to `k`: failure
of descent of the geometric unipotent radical is the exact obstruction separating pseudo-reductive
groups from reductive groups over imperfect fields.

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty.of_baseChange`: pseudo-reductivity descends along an
  arbitrary field extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange` and `.baseChange_iff`: pseudo-reductivity
  is preserved by and invariant under every separable algebraic field extension.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.
    iff_unipotentRadicalDefiningIdeal_separableClosure_eq_augmentation`:
  pseudo-reductivity is equivalent to smoothness, geometric connectedness, and triviality of the
  unipotent radical over `SeparableClosure k`.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.
    baseChange_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal`:
  a pseudo-reductive group remains pseudo-reductive over `K / k` iff the `K`-unipotent radical
  descends to `k`.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.
    reductive_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal`:
  a pseudo-reductive group over `k` is reductive iff its geometric unipotent radical descends to
  `k`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1 and
  Proposition 1.1.9.
* J. S. Milne, *Algebraic Groups* (2017), §§6.46–6.48 and Propositions 19.9–19.11.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace pseudoReductiveCommHopfAlgProperty

section ArbitraryExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

open FiniteTypeCommHopfAlgCat in
/-- Pseudo-reductivity descends along an arbitrary field extension: if `K ⊗[k] H` is
pseudo-reductive over `K`, then `H` is pseudo-reductive over `k`. -/
theorem of_baseChange
    (hH : pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    pseudoReductiveCommHopfAlgProperty k H := by
  obtain ⟨hsmooth, hconnected, hradical⟩ :=
    (pseudoReductiveCommHopfAlgProperty_iff K _).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) := hsmooth
  rw [pseudoReductiveCommHopfAlgProperty_iff]
  exact ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K,
    geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hconnected,
    unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation hradical⟩

/-- Along an arbitrary field extension `K / k`, a pseudo-reductive group over `k` remains
pseudo-reductive over `K` if and only if the `K`-unipotent radical of `K ⊗[k] H` descends to a Hopf
ideal over `k`. -/
theorem baseChange_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      ∃ J : HopfIdeal k H,
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) J =
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
            (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  rw [FiniteTypeCommHopfAlgCat.exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff,
    hH.unipotentRadicalDefiningIdeal_eq_augmentation,
    CommHopfAlgCat.baseChangeHopfIdeal_augmentation,
    pseudoReductiveCommHopfAlgProperty_iff]
  refine ⟨fun h ↦ h.2.2.symm, fun h ↦
    ⟨@Algebra.Smooth.baseChange k _ H K _ _ _ _ hH.smooth,
      geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hH.geometricallyConnected,
      h.symm⟩⟩

/-- **Descent obstruction for pseudo-reductive groups.** A pseudo-reductive group over `k` is
reductive if and only if its geometric unipotent radical over `AlgebraicClosure k` descends to
`k`. -/
theorem reductive_iff_exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H ↔
      ∃ J : HopfIdeal k H,
        CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) J =
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [FiniteTypeCommHopfAlgCat.exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff,
    hH.unipotentRadicalDefiningIdeal_eq_augmentation,
    CommHopfAlgCat.baseChangeHopfIdeal_augmentation,
    reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation]
  exact ⟨fun h ↦ h.2.2.symm, fun h ↦ ⟨hH.smooth, hH.geometricallyConnected, h.symm⟩⟩

end ArbitraryExtension

section Separable

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- **Pseudo-reductivity is preserved by separable algebraic field extensions**
(Conrad–Gabber–Prasad, Proposition 1.1.9(1)). -/
theorem baseChange {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    pseudoReductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  obtain ⟨hsmooth, hconnected, hradical⟩ :=
    (pseudoReductiveCommHopfAlgProperty_iff k H).mp hH
  rw [pseudoReductiveCommHopfAlgProperty_iff]
  refine ⟨@Algebra.Smooth.baseChange k _ H K _ _ _ _ hsmooth,
    geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hconnected, ?_⟩
  rwa [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff]

-- The defining simp lemma `pseudoReductiveCommHopfAlgProperty_iff` already expands the left-hand
-- side, so adding this equivalence to the simp set would violate simpNF.
/-- Pseudo-reductivity is invariant under every separable algebraic field extension. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      pseudoReductiveCommHopfAlgProperty k H :=
  ⟨of_baseChange, baseChange⟩

/-- **Separable-closure characterization of pseudo-reductivity.**

A finite-type affine group over a field `k` is pseudo-reductive if and only if it is smooth and
geometrically connected and its unipotent radical after base change to `SeparableClosure k` is
trivial. Replacing `SeparableClosure k` by `AlgebraicClosure k` recovers reductivity
(`reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`). -/
theorem iff_unipotentRadicalDefiningIdeal_separableClosure_eq_augmentation
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
              (FiniteTypeCommHopfAlgCat.baseChange (K := SeparableClosure k) H) =
            HopfIdeal.augmentation (SeparableClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := SeparableClosure k) H) := by
  rw [pseudoReductiveCommHopfAlgProperty_iff,
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff]

end Separable

end pseudoReductiveCommHopfAlgProperty

end

end TauCeti
