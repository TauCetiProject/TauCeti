/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Flat unramified algebras of finite type over a noetherian ring are étale

Let `R` be a noetherian ring and `S` a flat, formally unramified `R`-algebra of finite type. Then
`S` is finitely presented over `R`, since `R` is noetherian, and hence étale over `R` by Mathlib's
`Algebra.Etale.of_formallyUnramified_of_flat`.

The result is a theorem rather than an instance: `Algebra.Etale` already implies flatness and
formal unramifiedness through Mathlib instances, so an instance would create a cycle. A typical
application is a finite, torsion-free, formally unramified algebra `S` over a Dedekind domain `R`,
for instance a finite unramified extension of discrete valuation rings, where flatness comes from
Mathlib's instance that torsion-free modules over a Dedekind domain are flat. The existing instance
`TauCeti.AlgebraicGeometry.etale_specAlgebraMap` then makes `Spec S ⟶ Spec R` étale, hence smooth,
so the smooth base change of Néron models `TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange`
applies along it. Unramified extensions of discrete valuation rings that are not of finite type,
such as the completion or the strict henselization, are not covered.

## Main results

* `TauCeti.Algebra.Etale.of_formallyUnramified_of_flat_of_isNoetherianRing`: a flat, formally
  unramified algebra of finite type over a noetherian ring is étale.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*, Quatrième partie,
  Publ. Math. IHÉS 32 (1967), Théorème 17.6.1: a morphism locally of finite presentation is étale
  if and only if it is flat and unramified.
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Proposition 2(c), for the application to Néron
  models along unramified base change.
-/

public section

namespace TauCeti.Algebra.Etale

/-- A flat, formally unramified algebra of finite type over a noetherian ring is étale. -/
theorem of_formallyUnramified_of_flat_of_isNoetherianRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    [Algebra.FormallyUnramified R S] : Algebra.Etale R S :=
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  Algebra.Etale.of_formallyUnramified_of_flat

end TauCeti.Algebra.Etale
