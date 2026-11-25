/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Neron.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.RingHom.Etale

/-!
# Unramified base change of Néron models

Let `R → R'` be a finite unramified extension of Dedekind domains, for instance an unramified
extension of discrete valuation rings. Then `R'` is torsion-free, hence flat, over `R`, and finitely
presented since `R` is noetherian, so `R'` is étale over `R` and `Spec R' ⟶ Spec R` is étale,
hence smooth (`TauCeti.AlgebraicGeometry.Neron.etale_specMap_of_formallyUnramified`). The smooth
base change of Néron models `TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange` therefore
applies to it: the base change to `R'` of a Néron model over `R` is a Néron model over `R'`.

## Main results

* `TauCeti.AlgebraicGeometry.Neron.etale_of_formallyUnramified`: a finite, torsion-free, formally
  unramified algebra over a Dedekind domain is étale.
* `TauCeti.AlgebraicGeometry.Neron.etale_specMap_of_formallyUnramified`: its `Spec` is étale.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Proposition 2(c).
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [IsDedekindDomain R]
  [Module.IsTorsionFree R R'] [Module.Finite R R'] [Algebra.FormallyUnramified R R']

/-- **A finite unramified extension of a Dedekind domain is étale**: a finite, torsion-free,
formally unramified algebra over a Dedekind domain is flat (torsion-free over a Dedekind domain)
and finitely presented (finite over a noetherian ring), hence étale. -/
theorem etale_of_formallyUnramified : Algebra.Etale R R' :=
  have : Algebra.FinitePresentation R R' :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  Algebra.Etale.of_formallyUnramified_of_flat

/-- **Unramified base change is étale**: for a finite, torsion-free, formally unramified algebra
`R'` over a Dedekind domain `R`, for instance an unramified extension of discrete valuation rings,
`Spec R' ⟶ Spec R` is étale, hence smooth, so the smooth base change of Néron models
(`TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange`) applies along it. -/
instance etale_specMap_of_formallyUnramified :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  have := etale_of_formallyUnramified R R'
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)

end TauCeti.AlgebraicGeometry.Neron
