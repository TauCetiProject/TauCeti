/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Flat.Tower
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Flat.Jacobson
import TauCeti.RingTheory.Flat.LocalCriterion

/-!
# Flatness of adic completions

For an algebra `S` over a commutative ring `R`, with `S` Noetherian and local,
flatness over `R` is equivalent to flatness of the maximal-ideal completion of `S`
over `R`. Only the target is completed: `R` need not be local or Noetherian.

This criterion allows one to establish flatness of a local analytic algebra over
its base by identifying its completion with a flat formal algebra. The formal
presentation is a separate input; no analytic-to-formal comparison is assumed here.

More generally, an adic completion of a ring along an ideal in its Jacobson radical
is faithfully flat as soon as it is flat, which Mathlib supplies for Noetherian rings.
The completion has the same quotient by the ideal as the ring, so every maximal ideal
extends to a proper ideal of the completion. The flatness hypothesis is kept separate
because it can hold without Noetherianity of the ring itself: for instance, the
completion of a henselization is flat over it before the henselization is known to be
Noetherian.

In the opposite direction, if `R` is a Noetherian commutative ring, `S` is a flat `R`-algebra,
`I.map (algebraMap R S) = J`, and `S ⧸ J` is Noetherian — without assuming that `S` itself is
Noetherian — then `J` is finitely generated, `AdicCompletion J S` is Noetherian
(`Ideal.isNoetherianRing_adicCompletion_of_fg`), and modulo `I ^ n` it agrees with
`S ⧸ J ^ n = S ⧸ I ^ n S`, which is flat over `R ⧸ I ^ n`. By the infinitesimal local criterion
for flatness (`Module.Flat.of_forall_flat_quotient_pow`), `AdicCompletion J S` is flat over `R`.

## Main results

* `AdicCompletion.faithfullyFlat_of_le_jacobson`: a flat adic completion along an ideal
  in the Jacobson radical is faithfully flat.
* `AdicCompletion.faithfullyFlat_of_isLocalRing`: the maximal-ideal completion of a
  Noetherian local ring is faithfully flat.
* `AdicCompletion.flat_iff_of_isLocalRing`: completing a Noetherian local target detects
  flatness over any base.
* `TauCeti.AdicCompletion.flat_of_map_eq`: if `R` is Noetherian, `S` is flat over `R`,
  `I.map (algebraMap R S) = J`, and `S ⧸ J` is Noetherian, then `AdicCompletion J S` is flat
  over `R`.

## References

* Stacks Project, Lemma 10.39.10, Tag 039V (flatness in a faithfully flat tower).
* [Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK).
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ).
* Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10
  (completion of Noetherian local rings).
* H. Matsumura, *Commutative Ring Theory*, Theorem 22.3 (the local criterion for flatness).
-/

public section

namespace AdicCompletion

/-- An adic completion along an ideal in the Jacobson radical is faithfully flat once it is
flat, for instance over a Noetherian ring. -/
theorem faithfullyFlat_of_le_jacobson {S : Type*} [CommRing S] {J : Ideal S}
    [Module.Flat S (AdicCompletion J S)] (hJ : J ≤ (⊥ : Ideal S).jacobson) :
    Module.FaithfullyFlat S (AdicCompletion J S) :=
  .of_le_jacobson_of_algHom ((Ideal.pow_le_self one_ne_zero).trans hJ) (evalₐ J 1)

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing S] [IsLocalRing S]

/-- The maximal-ideal completion of a Noetherian local ring is faithfully flat over it. -/
instance faithfullyFlat_of_isLocalRing :
    Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
  faithfullyFlat_of_le_jacobson (IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- Completing a Noetherian local target detects flatness over any base ring.
The base is unchanged, and need not be local or Noetherian. -/
theorem flat_iff_of_isLocalRing :
    Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal S) S) ↔ Module.Flat R S :=
  (Module.Flat.iff_of_faithfullyFlat R S _).symm

end AdicCompletion

namespace TauCeti.AdicCompletion

/-- If `R` is a Noetherian ring, `S` is a flat `R`-algebra, `I.map (algebraMap R S) = J`, and
`S ⧸ J` is Noetherian, then `AdicCompletion J S` is flat over `R`, without assuming `S` itself is
Noetherian. -/
theorem flat_of_map_eq {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {I : Ideal R} {J : Ideal S} [IsNoetherianRing (S ⧸ J)]
    (h : I.map (algebraMap R S) = J) :
    Module.Flat R (_root_.AdicCompletion J S) := by
  set C := _root_.AdicCompletion J S
  have hfg : J.FG := h ▸ I.fg_of_isNoetherianRing.map _
  have : IsNoetherianRing C := Ideal.isNoetherianRing_adicCompletion_of_fg J hfg
  refine Module.Flat.of_forall_flat_quotient_pow (S := C) (I := I) ?_ fun n ↦ ?_
  · have := _root_.AdicCompletion.isAdicComplete_self J hfg
    rw [IsScalarTower.algebraMap_eq R S C, ← Ideal.map_map, h, Ideal.jacobson_bot]
    exact IsAdicComplete.le_jacobson _
  · set P := I ^ n
    have hPC : (P • ⊤ : Submodule R C) = ((J ^ n).map (algebraMap S C)).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, IsScalarTower.algebraMap_eq R S C, ← Ideal.map_map,
        Ideal.map_pow, h]
    have hPS : (P • ⊤ : Submodule R S) = (J ^ n).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, Ideal.map_pow, h]
    let e : (C ⧸ (P • ⊤ : Submodule R C)) ≃ₗ[R] S ⧸ (P • ⊤ : Submodule R S) :=
      (Submodule.quotEquivOfEq _ _ hPC ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _ ≪≫ₗ
        (_root_.AdicCompletion.quotientMapPowAlgEquiv hfg n).toLinearEquiv.restrictScalars R) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hPS ≪≫ₗ
        Submodule.Quotient.restrictScalarsEquiv R _).symm
    exact .of_linearEquiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)

end TauCeti.AdicCompletion
