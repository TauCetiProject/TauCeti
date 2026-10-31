/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Etale
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Adjoining a root of a polynomial with irreducible reduction to a discrete valuation ring

Let `R` be a discrete valuation ring with residue field `k`, and let `g : R[X]` be a monic
polynomial whose reduction `g₀ : k[X]` is irreducible. Then `R[X] ⧸ (g)` is again a discrete
valuation ring. The maximal ideal of `R` generates its maximal ideal
(`AdjoinRoot.maximalIdeal_eq_map`), so every uniformizer of `R` stays a uniformizer
(`TauCeti.IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq`), and the residue
field is `k[X] ⧸ (g₀)`.

No separability of `g₀` is assumed. When `g₀` is separable the extension is étale, and this is
`TauCeti.IsDiscreteValuationRing.exists_isDiscreteValuationRing_of_etale`. When `g₀` is
inseparable, the extension has ramification index one but a residue extension that is not
separable, so it is not unramified in the classical sense: this is how extensions of discrete
valuation rings with inseparable residue field extension, such as the fierce ones, are built.

## Main results

* `Polynomial.Monic.isDomain_adjoinRoot`: `R[X] ⧸ (g)` is a domain.
* `Polynomial.Monic.isDiscreteValuationRing_adjoinRoot`: `R[X] ⧸ (g)` is a discrete valuation ring.

The proof goes through regular local rings: `R[X] ⧸ (g)` is free over `R`, Noetherian and local,
and the maximal ideal of `R` generates its maximal ideal, so it is regular of dimension one.
-/

public section

open Polynomial IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {g : R[X]}

namespace Polynomial.Monic

/-- **Adjoining a root of a monic polynomial with irreducible reduction to a discrete valuation
ring gives a domain.** The reduction need not be separable. -/
theorem isDomain_adjoinRoot (hg : g.Monic) (hirr : Irreducible (g.map (residue R))) :
    IsDomain (AdjoinRoot g) :=
  have : IsLocalRing (AdjoinRoot g) := hg.isLocalRing_adjoinRoot hirr
  have := hg.free_adjoinRoot
  have := hg.finite_adjoinRoot
  have : IsNoetherianRing (AdjoinRoot g) := .of_finite R _
  have : _root_.IsRegularLocalRing (AdjoinRoot g) :=
    TauCeti.IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq
      (AdjoinRoot.maximalIdeal_eq_map hirr).symm
  inferInstance

/-- **Adjoining a root of a monic polynomial with irreducible reduction to a discrete valuation
ring gives a discrete valuation ring.** The reduction need not be separable. -/
theorem isDiscreteValuationRing_adjoinRoot (hg : g.Monic) (hirr : Irreducible (g.map (residue R)))
    [IsDomain (AdjoinRoot g)] : IsDiscreteValuationRing (AdjoinRoot g) :=
  have : IsLocalRing (AdjoinRoot g) := hg.isLocalRing_adjoinRoot hirr
  have := hg.free_adjoinRoot
  have := hg.finite_adjoinRoot
  have : IsNoetherianRing (AdjoinRoot g) := .of_finite R _
  TauCeti.IsDiscreteValuationRing.of_flat_of_map_maximalIdeal_eq
    (AdjoinRoot.maximalIdeal_eq_map hirr).symm

end Polynomial.Monic
