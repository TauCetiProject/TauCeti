/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.IndEtale
public import TauCeti.RingTheory.StrictHenselization.MaximalIdeal
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Flat.Basic
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Etale.Weakly
import TauCeti.RingTheory.Flat.LocalCriterion
import TauCeti.RingTheory.Flat.Noetherian

/-!
# Noetherianity of the strict henselization

Let `R` be a local ring with maximal ideal `𝔪`, and let `R^{sh}` be the colimit of the étale
neighbourhoods of `R` pointed in a field `Ω` through a local map `R → Ω`. For a separable closure
`Ω` of the residue field this is the strict henselization of `R`. This file shows that `R^{sh}` is
Noetherian exactly when `R` is.

One direction is descent: `R → R^{sh}` is flat and local, hence faithfully flat. For the other,
let `R` be Noetherian and let `(R^{sh})^∧` be the completion of `R^{sh}` along its maximal ideal
`𝔪 R^{sh}`. Unlike for the ordinary henselization, this completion is not the completion of `R`
(for `R = ℤ_(p)` and `Ω` a separable closure of `𝔽_p` it is the ring of Witt vectors `W(Ω)`), so
it is studied directly.

* `(R^{sh})^∧` is Noetherian: it is complete along the finitely generated ideal `𝔪 (R^{sh})^∧`,
  modulo which it is a field.
* `(R^{sh})^∧` is flat over `R`, by the infinitesimal form of the local criterion for flatness
  (`Module.Flat.of_forall_flat_quotient_pow`): modulo `𝔪 ^ n` it is `R^{sh} ⧸ 𝔪 ^ n R^{sh}`, which
  is flat over `R ⧸ 𝔪 ^ n` because `R^{sh}` is flat over `R`.
* `(R^{sh})^∧` is therefore flat over `R^{sh}`, which is weakly étale over `R`. As a completion
  along the maximal ideal of the local ring `R^{sh}`, it is even faithfully flat, and
  Noetherianity descends to `R^{sh}`.

## Main results

* `TauCeti.StrictHenselization.isNoetherianRing_algebra_iff`: the pointed étale colimit is
  Noetherian if and only if `R` is.
* `TauCeti.StrictHenselization.isNoetherianRing`: the strict henselization of a Noetherian local
  ring is Noetherian.

## References

* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ), Noetherianity of the
  strict henselization.
* H. Matsumura, *Commutative Ring Theory*, Theorem 22.3, the local criterion for flatness.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
  [IsLocalHom (algebraMap R Ω)]

/-- For a Noetherian local ring `R`, the maximal ideal of the pointed étale colimit is finitely
generated, being the extension of the maximal ideal of `R`. -/
private theorem fg_maximalIdeal [IsNoetherianRing R] : (maximalIdeal (algebra R Ω)).FG := by
  rw [maximalIdeal_eq_map R Ω]
  exact (maximalIdeal R).fg_of_isNoetherianRing.map _

/-- For a Noetherian local ring `R`, the completion of the pointed étale colimit along its maximal
ideal is Noetherian: it is complete along a finitely generated ideal, modulo which it is a field. -/
private theorem isNoetherianRing_adicCompletion [IsNoetherianRing R] :
    IsNoetherianRing (AdicCompletion (maximalIdeal (algebra R Ω)) (algebra R Ω)) := by
  -- The quotient by the maximal ideal is a field, hence Noetherian.
  let _ := Ideal.Quotient.field (maximalIdeal (algebra R Ω))
  exact Ideal.isNoetherianRing_adicCompletion_of_fg _ (fg_maximalIdeal R Ω)

/-- For a Noetherian local ring `R`, the completion of the pointed étale colimit `S` along its
maximal ideal is flat over `R`. Modulo `𝔪 ^ n` the completion is `S ⧸ 𝔪 ^ n S`, which is flat over
`R ⧸ 𝔪 ^ n`. -/
private theorem flat_adicCompletion [IsNoetherianRing R] :
    Module.Flat R (AdicCompletion (maximalIdeal (algebra R Ω)) (algebra R Ω)) := by
  set S := algebra R Ω
  set J := maximalIdeal S
  set C := AdicCompletion J S
  have hJ : J = (maximalIdeal R).map (algebraMap R S) := maximalIdeal_eq_map R Ω
  have hfg : J.FG := fg_maximalIdeal R Ω
  have : IsNoetherianRing C := isNoetherianRing_adicCompletion R Ω
  refine Module.Flat.of_forall_flat_quotient_pow (S := C) (I := maximalIdeal R) ?_ fun n ↦ ?_
  · -- The extension of `𝔪` to the completion is the extension of `J`, which lies in the Jacobson
    -- radical of the `J`-adically complete ring `C`.
    have := AdicCompletion.isAdicComplete_self J hfg
    rw [IsScalarTower.algebraMap_eq R S C, ← Ideal.map_map, ← hJ, Ideal.jacobson_bot]
    exact IsAdicComplete.le_jacobson _
  · -- `C ⧸ 𝔪 ^ n C ≃ S ⧸ 𝔪 ^ n S`, since both are the quotients by `J ^ n` and `C ⧸ J ^ n C` is
    -- `S ⧸ J ^ n`.
    set P := maximalIdeal R ^ n
    have hP {T : Type u} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
        (P • ⊤ : Submodule R T) = ((J ^ n).map (algebraMap S T)).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, hJ, ← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    let e : (C ⧸ (P • ⊤ : Submodule R C)) ≃ₗ[R] S ⧸ (P • ⊤ : Submodule R S) :=
      (Submodule.quotEquivOfEq _ _ hP ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _ ≪≫ₗ
        (AdicCompletion.quotientMapPowAlgEquiv hfg n).toLinearEquiv.restrictScalars R) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ (by rw [hP, Algebra.algebraMap_self, Ideal.map_id]) ≪≫ₗ
        Submodule.Quotient.restrictScalarsEquiv R _).symm
    exact .of_linearEquiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)

/-- The colimit of the étale neighbourhoods of a local ring `R` pointed in a field `Ω`, through a
local map `R → Ω`, is Noetherian if and only if `R` is. For a separable closure `Ω` of the residue
field of `R`, this says that the strict henselization of `R` is Noetherian exactly when `R` is. -/
@[stacks 06LJ "strict henselization"]
theorem isNoetherianRing_algebra_iff : IsNoetherianRing (algebra R Ω) ↔ IsNoetherianRing R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : Module.FaithfullyFlat R (algebra R Ω) := .of_flat_of_isLocalHom
    exact .of_faithfullyFlat (algebra R Ω)
  · set S := algebra R Ω
    set J := maximalIdeal S
    have := isNoetherianRing_adicCompletion R Ω
    have := flat_adicCompletion R Ω
    have : Module.Flat S (AdicCompletion J S) := Algebra.WeaklyEtale.flat_iff.mpr this
    have := AdicCompletion.faithfullyFlat_of_le_jacobson (maximalIdeal_le_jacobson (⊥ : Ideal S))
    exact .of_faithfullyFlat (AdicCompletion J S)

/-- The colimit of the étale neighbourhoods of a Noetherian local ring pointed in a field, through
a local map, is Noetherian. In particular the strict henselization of a Noetherian local ring is
Noetherian. -/
instance isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing (algebra R Ω) :=
  (isNoetherianRing_algebra_iff R Ω).mpr ‹_›

end TauCeti.StrictHenselization
