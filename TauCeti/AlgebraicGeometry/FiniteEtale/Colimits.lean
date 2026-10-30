/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.RingTheory.Etale.Limits

/-!
# Finite colimits of finite étale schemes over an affine base

Finite étale schemes over an affine scheme `Spec R` have all finite colimits. In particular they
have quotients by finite groups, the half of Lenstra's axiom (G2) for a Galois category that
`TauCeti.AlgebraicGeometry.FiniteEtale.Limits` leaves open, here over an affine base.

Finite étale schemes over `Spec R` are anti-equivalent to finite étale `R`-algebras
(`TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme`), and finite étale
`R`-algebras are closed under finite products and equalizers in commutative `R`-algebras
(`TauCeti.RingTheory.Etale.Limits`). Finite colimits of finite étale `Spec R`-schemes are
therefore computed on coordinate algebras: the global-sections functor `AlgebraicGeometry.algΓ R`
sends them to the corresponding finite limits of commutative `R`-algebras. For instance, the
coequalizer of two morphisms `Spec B ⇉ Spec A` has coordinate algebra the equalizer of the
corresponding algebra maps `A ⇉ B`, and the quotient of `Spec A` by a finite group acting on it
has coordinate algebra the limit of the action diagram, the subalgebra of invariants.

## Main results

* `HasFiniteColimits (FiniteEtaleScheme (Spec R))`: finite étale schemes over an affine base have
  finite colimits.
* `PreservesFiniteColimits ((finiteEtaleSchemeProperty (Spec R)).ι ⋙ algΓ R)`: global sections
  send these finite colimits to finite limits of coordinate algebras.
* `HasColimitsOfShape (SingleObj M) (FiniteEtaleScheme (Spec R))` for a finite monoid `M` in any
  universe: quotients of finite étale schemes over an affine base by finite monoid actions, in
  particular by finite group actions.

## References

* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti

namespace FiniteEtaleScheme

variable (R : CommRingCat.{u})

/-- **Finite étale schemes over an affine base have finite colimits.** They are the opposites of
the finite limits of finite étale algebras. -/
instance : HasFiniteColimits (FiniteEtaleScheme (Spec R)) :=
  ⟨fun _ _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme R).inverse⟩

/-- **Finite colimits of finite étale schemes over `Spec R` are computed on coordinate algebras.**
The global-sections functor `algΓ R` sends a finite colimit of finite étale `Spec R`-schemes to the
finite limit of their coordinate algebras in commutative `R`-algebras. -/
instance : PreservesFiniteColimits ((finiteEtaleSchemeProperty (Spec R)).ι ⋙ algΓ R) :=
  have := preservesFiniteColimits_op (CommAlgCat.finiteEtale.{u} R).ι
  preservesFiniteColimits_of_natIso
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleSchemeInverseCompInclusionIso R)

/-- **Finite étale schemes over an affine base have quotients by finite monoids**, in any
universe. For a finite group this is the quotient required by Lenstra's axiom (G2) for a Galois
category. -/
instance {M : Type*} [Monoid M] [Finite M] :
    HasColimitsOfShape (SingleObj M) (FiniteEtaleScheme (Spec R)) := by
  -- `SingleObj M` is a finite category only for `M : Type`, so transfer to `Fin n`.
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin M
  let := e.symm.monoid
  exact hasColimitsOfShape_of_equivalence e.symm.mulEquiv.toSingleObjEquiv

end FiniteEtaleScheme

end TauCeti
