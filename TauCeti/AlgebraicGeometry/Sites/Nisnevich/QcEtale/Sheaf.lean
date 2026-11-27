/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.QcEtale

/-!
# Sheaves on the quasi-compact small Nisnevich site

Let `X` be a quasi-separated scheme. Every étale `X`-scheme has a small Nisnevich covering by
objects of `X.QcEtale`, and the small étale site has fibre products, so the inclusion
`X.QcEtale ⥤ X.Etale` is `1`-hypercover dense. Restriction along it is therefore an equivalence
between sheaves on the small Nisnevich site and sheaves on the quasi-compact small Nisnevich site
(Stacks, Lemma 7.29.1 (03A0)), whose underlying functor is restriction
(`AlgebraicGeometry.Scheme.QcEtale.nisnevichSheafEquiv_inverse`).

The small Nisnevich topology is subcanonical
(`AlgebraicGeometry.Scheme.smallNisnevichTopology_subcanonical`), and so is the induced topology
on `X.QcEtale`: every representable presheaf on the basis is a sheaf.

## Main declarations

* `AlgebraicGeometry.Scheme.QcEtale.nisnevichSheafEquiv X A`: for quasi-separated `X`, the
  equivalence `Sheaf X.qcNisnevichTopology A ≌ Sheaf X.smallNisnevichTopology A`.
* `AlgebraicGeometry.Scheme.qcNisnevichTopology_subcanonical`: for quasi-separated `X`, the
  quasi-compact small Nisnevich topology is subcanonical.

## References

* [Stacks: Lemma 7.29.1](https://stacks.math.columbia.edu/tag/03A0)
-/

public noncomputable section

universe v' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [QuasiSeparatedSpace X]

instance QcEtale.isOneHypercoverDense_qcNisnevichTopology :
    Functor.IsOneHypercoverDense.{u} (QcEtale.ι X) X.qcNisnevichTopology
      X.smallNisnevichTopology :=
  Functor.IsOneHypercoverDense.of_hasPullbacks QcEtale.exists_mem_smallNisnevichTopology

/-- Representable presheaves on the quasi-compact small étale site of a quasi-separated scheme are
sheaves for the quasi-compact small Nisnevich topology. -/
instance qcNisnevichTopology_subcanonical : X.qcNisnevichTopology.Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (QcEtale.ι X) _ X.smallNisnevichTopology

section

variable (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A]

instance QcEtale.isEquivalence_sheafPushforwardContinuous_nisnevich :
    ((QcEtale.ι X).sheafPushforwardContinuous A X.qcNisnevichTopology
      X.smallNisnevichTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _

/-- **Sheaves on the quasi-compact small Nisnevich site** (Stacks, Lemma 7.29.1 (03A0)): for a
quasi-separated scheme `X`, the category of sheaves on `X.QcEtale` for the quasi-compact small
Nisnevich topology is equivalent to the category of sheaves on the small Nisnevich site of `X`.
The inverse is restriction along the inclusion `X.QcEtale ⥤ X.Etale`
(`QcEtale.nisnevichSheafEquiv_inverse`). -/
def QcEtale.nisnevichSheafEquiv :
    Sheaf X.qcNisnevichTopology A ≌ Sheaf X.smallNisnevichTopology A :=
  ((QcEtale.ι X).sheafPushforwardContinuous A X.qcNisnevichTopology
    X.smallNisnevichTopology).asEquivalence.symm

/-- The inverse of `QcEtale.nisnevichSheafEquiv` restricts a small Nisnevich sheaf to the
quasi-compact small étale site. -/
@[simp]
theorem QcEtale.nisnevichSheafEquiv_inverse :
    (QcEtale.nisnevichSheafEquiv X A).inverse =
      (QcEtale.ι X).sheafPushforwardContinuous A X.qcNisnevichTopology
        X.smallNisnevichTopology :=
  (rfl)

/-- The value of the restriction of a small Nisnevich sheaf `F` at an object `U` of `X.QcEtale` is
the value of `F` at the underlying étale `X`-scheme. -/
theorem QcEtale.nisnevichSheafEquiv_inverse_obj_obj (F : Sheaf X.smallNisnevichTopology A)
    (U : X.QcEtale) :
    ((QcEtale.nisnevichSheafEquiv X A).inverse.obj F).obj.obj (Opposite.op U) =
      F.obj.obj (Opposite.op ((QcEtale.ι X).obj U)) :=
  (rfl)

end

end AlgebraicGeometry.Scheme
