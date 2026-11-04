/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.Henselization.Quotient
import TauCeti.RingTheory.AdicCompletion.Flat
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Etale.Weakly
import TauCeti.RingTheory.Flat.Noetherian
import TauCeti.RingTheory.Henselization.Henselian
import TauCeti.RingTheory.Henselization.IndEtale

/-!
# Noetherianity of the henselization of a pair

Let `R^h` be the henselization of a pair `(R, I)`, with extended ideal `I^h`. If `R` is
Noetherian then so is `R^h`, for every ideal `I`. The completion of `R^h` along `I^h` is the
`I`-adic completion `R^∧` of `R` (`TauCeti.Henselization.completionEquiv`), and the map
`R^h → R^∧` is faithfully flat. Conversely, when `I` lies in the Jacobson radical of `R`, the
map `R → R^h` is faithfully flat (`TauCeti.Henselization.faithfullyFlat_of_le_jacobson`), so
`R` is Noetherian as soon as `R^h` is. This applies to the henselization of a local ring along
its maximal ideal.

Faithful flatness of `R^h → R^∧` comes in two steps. The completion `R^∧` is flat over `R`, and
`R^h` is weakly étale over `R`, so flatness passes to `R^h`. The ideal `I^h` lies in the
Jacobson radical of the henselian pair `(R^h, I^h)`, and `R^∧` has the same closed fibre as
`R^h`, so every maximal ideal of `R^h` stays proper in `R^∧`. Noetherianity then descends from
the Noetherian ring `R^∧`.

## Main results

* `TauCeti.Henselization.faithfullyFlat_adicCompletion`: for `R` Noetherian, the completion of
  the henselization along the extended ideal is faithfully flat over it.
* `TauCeti.Henselization.isNoetherianRing`: the henselization of a Noetherian ring along any
  ideal is Noetherian.
* `TauCeti.Henselization.isNoetherianRing_iff_of_le_jacobson`: when `I` lies in the Jacobson
  radical of `R`, the henselization is Noetherian exactly when `R` is.

## References

* [Stacks Project, Lemma 15.12.4](https://stacks.math.columbia.edu/tag/0AGV), Noetherianity of
  the henselization of a pair.
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ),
  Noetherianity of the henselization of a local ring.
-/

public section

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- For `R` Noetherian, the completion of the henselization of `(R, I)` along the extended
ideal is faithfully flat over the henselization. This completion is the `I`-adic completion of
`R`, by `completionEquiv`. -/
instance faithfullyFlat_adicCompletion [IsNoetherianRing R] :
    Module.FaithfullyFlat (algebra I) (AdicCompletion (extended I) (algebra I)) := by
  have : Module.Flat R (AdicCompletion (extended I) (algebra I)) :=
    .of_linearEquiv (completionEquiv I).symm.toLinearEquiv
  have : Module.Flat (algebra I) (AdicCompletion (extended I) (algebra I)) :=
    Algebra.WeaklyEtale.flat_iff.mpr this
  exact AdicCompletion.faithfullyFlat_of_le_jacobson ((henselian I).jac.trans Ideal.jacobson_bot.ge)

/-- The henselization of a Noetherian ring along any ideal is Noetherian. -/
@[stacks 0AGV "Noetherianity of the henselization"]
instance isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing (algebra I) := by
  have : IsNoetherianRing (AdicCompletion (extended I) (algebra I)) :=
    isNoetherianRing_of_ringEquiv _ (completionEquiv I).toRingEquiv
  exact .of_faithfullyFlat (AdicCompletion (extended I) (algebra I))

/-- When `I` lies in the Jacobson radical of `R`, the henselization of `(R, I)` is Noetherian
exactly when `R` is. This applies to a local ring and its maximal ideal. -/
@[stacks 06LJ "henselization of a local ring"]
theorem isNoetherianRing_iff_of_le_jacobson (hI : I ≤ (⊥ : Ideal R).jacobson) :
    IsNoetherianRing (algebra I) ↔ IsNoetherianRing R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have := faithfullyFlat_of_le_jacobson I hI
  exact .of_faithfullyFlat (algebra I)

end TauCeti.Henselization
