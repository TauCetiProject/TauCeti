/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Base change of the unipotent radical

Let `H` be a finite-type commutative Hopf algebra over a field `k`. Extension to a field `K`
sends every connected normal smooth unipotent closed subgroup of the affine group represented by
`H` to another such subgroup. In particular, the base change of the unipotent radical is contained
in the unipotent radical formed after base change.

In coordinate rings, closed-subgroup containment reverses the order on defining ideals, so the
conclusion is

```text
  unipotentRadicalDefiningIdeal (K ⊗[k] H) ≤
    baseChangeHopfIdeal (unipotentRadicalDefiningIdeal H).
```

Normality and geometric connectedness survive base change directly. The quotient by a
base-changed ideal is identified with the base change of the original quotient, where smooth
geometric unipotence follows from the universal coefficient-matrix argument.

Triviality of the radical after a field extension descends to the ground field by faithful-flat
reflection of equality of Hopf ideals. The same reflection descends the triviality of all normal
smooth unipotent closed subgroups, which is how the generated Chevalley subgroups over a field are
reduced to an algebraic closure.

Equality requires descent of an arbitrary radical candidate over `K` and is not asserted here.

## Main declarations

* `TauCeti.smoothUnipotentCommHopfAlgProperty.quotient_baseChangeHopfIdeal`: scalar extension
  preserves smooth unipotence of the quotient by a Hopf ideal.
* `TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_baseChange`: triviality of
  normal smooth unipotent closed subgroups descends from a field extension to the ground field.
* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.baseChange`: scalar extension preserves
  unipotent-radical candidates.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_le`: the
  base-changed unipotent radical is contained in the radical after base change.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation`:
  triviality of the unipotent radical after a field extension descends to the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace smoothUnipotentCommHopfAlgProperty

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Base change of a closed subgroup with smooth unipotent quotient again has smooth unipotent
quotient: the quotient by the base-changed Hopf ideal is the base change of the original
quotient. -/
theorem quotient_baseChangeHopfIdeal
    (hI : smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :=
  (smoothUnipotentCommHopfAlgProperty K).prop_of_iso
    (CategoryTheory.ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K)
      (CommHopfAlgCat.quotientBaseChangeIso (K := K) I).symm)
    (baseChange (K := K) (FiniteTypeCommHopfAlgCat.quotient H I) hI)

end smoothUnipotentCommHopfAlgProperty

namespace HopfIdeal

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Triviality of normal smooth unipotent closed subgroups descends along a field extension.**
If every normal smooth unipotent closed subgroup of the base change of `H` to `K` is trivial, then
so is every normal smooth unipotent closed subgroup of `H`. Base change preserves normality and
smooth unipotence of the quotient, and faithfully flat base change reflects equality of Hopf
ideals.

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent_of_baseChange
    (h : ∀ J : HopfIdeal K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H), J.IsNormal →
      smoothUnipotentCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) J) →
      J = augmentation K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H))
    (I : HopfIdeal k H) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    I = augmentation k H := by
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact h _ (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI)
    (smoothUnipotentCommHopfAlgProperty.quotient_baseChangeHopfIdeal hU)

end HopfIdeal

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Base change of a unipotent-radical candidate is again a unipotent-radical candidate. -/
theorem baseChange (hI : IsUnipotentRadicalCandidate H I) :
    IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) := by
  refine IsUnipotentRadicalCandidate.mk
    (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI.isNormal) ?_
    hI.smoothUnipotent.quotient_baseChangeHopfIdeal
  apply (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) I).symm
  exact geometricallyConnectedCommHopfAlgProperty.baseChange k K _ hI.geometricallyConnected

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The unipotent radical after base change contains the base change of the original unipotent
radical.

The displayed inequality is between defining Hopf ideals, hence has the opposite direction from
the corresponding inclusion of represented closed subgroups. -/
theorem unipotentRadicalDefiningIdeal_baseChange_le
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) ≤
      CommHopfAlgCat.baseChangeHopfIdeal (K := K)
        (unipotentRadicalDefiningIdeal H) :=
  unipotentRadicalDefiningIdeal_le _ _
    (HopfIdeal.IsUnipotentRadicalCandidate.baseChange
      (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H))

/-- Triviality of the unipotent radical after base change to a field extension descends to the
ground field. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hgeometric :
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) =
        HopfIdeal.augmentation K
          (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      HopfIdeal.augmentation k H := by
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  apply le_antisymm
  · exact HopfIdeal.le_augmentation K _ _
  · rw [← hgeometric]
    exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_le H

end FiniteTypeCommHopfAlgCat

end

end TauCeti
