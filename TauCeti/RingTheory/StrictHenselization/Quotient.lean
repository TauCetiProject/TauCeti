/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Map
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Over
import TauCeti.RingTheory.Henselian.Quotient
import TauCeti.RingTheory.StrictHenselization.Etale
import TauCeti.RingTheory.StrictHenselization.Henselian
import TauCeti.RingTheory.StrictHenselization.Lift

/-!
# The strict henselization of a quotient

Let `R` be a local ring, `I` an ideal of `R`, and `Ω` a separable algebraic extension of the
residue field of `R` which is also an `R ⧸ I`-algebra compatibly with `R`. Then the strict
henselization of `R ⧸ I` with respect to `Ω` is the quotient of the strict henselization of `R`
by the extended ideal: `R^{sh} ⧸ I R^{sh} ≃ (R ⧸ I)^{sh}`. Since `R ⧸ I` has the same residue
field as `R`, taking `Ω` a separable closure of this common residue field gives Stacks,
Lemma 10.156.4 (05WS).

The comparison `quotientAlgEquiv` is induced by the functoriality map `map` along `R → R ⧸ I`,
which kills `I R^{sh}`. Its inverse comes from the universal property `lift` of `(R ⧸ I)^{sh}`:
the quotient `R^{sh} ⧸ I R^{sh}` is henselian local, being a nontrivial quotient of a henselian
local ring, and its residue field is `Ω`, because `toTarget` is surjective
(`toTarget_surjective`) with kernel the maximal ideal. Both composites are identities by the
uniqueness statements `map_unique` and `eq_lift`.

## Main results

* `TauCeti.StrictHenselization.quotientAlgEquiv`: the isomorphism
  `algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω)) ≃ₐ[R ⧸ I] algebra (R ⧸ I) Ω`.
* `TauCeti.StrictHenselization.quotientAlgEquiv_mk`: it is induced by `map`, so it is
  compatible with the points of the two colimits (`toTarget_map`).

## References

* [Stacks Project, Lemma 10.156.4](https://stacks.math.columbia.edu/tag/05WS).
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

section Map

variable (R : Type u) [CommRing R] (I : Ideal R) (Ω : Type u) [CommRing Ω] [Algebra R Ω]
  [Algebra (R ⧸ I) Ω] [IsScalarTower R (R ⧸ I) Ω]

/-- The quotient map `R → R ⧸ I` and the identity of `Ω` form a commuting square of pointed
rings. -/
theorem id_comp_algebraMap_eq_comp_mk :
    (RingHom.id Ω).comp (algebraMap R Ω) = (algebraMap (R ⧸ I) Ω).comp (Ideal.Quotient.mk I) := by
  rw [RingHom.id_comp, IsScalarTower.algebraMap_eq R (R ⧸ I) Ω, Ideal.Quotient.algebraMap_eq]

/-- The map of pointed étale colimits along `R → R ⧸ I` kills the extension of `I`. -/
private theorem map_le_ker_map_mk :
    I.map (algebraMap R (algebra R Ω)) ≤
      RingHom.ker (map (Ideal.Quotient.mk I) (RingHom.id Ω)
        (id_comp_algebraMap_eq_comp_mk R I Ω)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hi]

/-- The point of the colimit vanishes on the extension of `I`. -/
private theorem map_le_ker_toTarget :
    I.map (algebraMap R (algebra R Ω)) ≤ RingHom.ker (toTarget R Ω).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  simp [IsScalarTower.algebraMap_apply R (R ⧸ I) Ω, Ideal.Quotient.eq_zero_iff_mem.mpr hi]

/-- The comparison map from the quotient of the colimit over `R` to the colimit over `R ⧸ I`. -/
private noncomputable def quotientHom :
    (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) →ₐ[R ⧸ I] algebra (R ⧸ I) Ω where
  toRingHom := Ideal.Quotient.lift _ _ fun _ ha ↦ map_le_ker_map_mk R I Ω ha
  commutes' r := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact map_algebraMap _ _ _ r

private theorem quotientHom_mk (x : algebra R Ω) :
    quotientHom R I Ω (Ideal.Quotient.mk _ x) =
      map (Ideal.Quotient.mk I) (RingHom.id Ω) (id_comp_algebraMap_eq_comp_mk R I Ω) x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The point of the quotient of the colimit over `R`. -/
private noncomputable def quotientToTarget :
    (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) →+* Ω :=
  Ideal.Quotient.lift _ (toTarget R Ω).toRingHom fun _ ha ↦ map_le_ker_toTarget R I Ω ha

private theorem quotientToTarget_mk (x : algebra R Ω) :
    quotientToTarget R I Ω (Ideal.Quotient.mk _ x) = toTarget R Ω x :=
  Ideal.Quotient.lift_mk _ _ _

private theorem quotientToTarget_algebraMap (r : R) :
    quotientToTarget R I Ω (algebraMap R _ r) = algebraMap R Ω r := by
  rw [← Ideal.Quotient.mk_algebraMap, quotientToTarget_mk,
    AlgHom.commutes]

private theorem toTarget_quotientHom (x : algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) :
    toTarget (R ⧸ I) Ω (quotientHom R I Ω x) = quotientToTarget R I Ω x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact toTarget_map _ _ _ x

end Map

section Field

variable (R : Type u) [CommRing R] (I : Ideal R) (Ω : Type u) [Field Ω]
  [Algebra R Ω] [Algebra (R ⧸ I) Ω] [IsScalarTower R (R ⧸ I) Ω]

/-- The quotient of the colimit over `R` is henselian local. -/
private theorem henselianLocalRing_quotient :
    HenselianLocalRing (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) :=
  have := (quotientToTarget R I Ω).domain_nontrivial
  (Ideal.Quotient.mk _).henselianLocalRing_of_surjective Ideal.Quotient.mk_surjective

attribute [local instance] henselianLocalRing_quotient

variable [IsLocalRing R] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

private theorem quotientToTarget_surjective : Function.Surjective (quotientToTarget R I Ω) :=
  fun ω ↦ (toTarget_surjective R Ω ω).elim fun x hx ↦ ⟨Ideal.Quotient.mk _ x, hx⟩

private theorem isLocalHom_quotientToTarget : IsLocalHom (quotientToTarget R I Ω) :=
  .of_surjective _ (quotientToTarget_surjective R I Ω)

attribute [local instance] isLocalHom_quotientToTarget

private theorem bijective_lift_quotientToTarget :
    Function.Bijective (ResidueField.lift (quotientToTarget R I Ω)) :=
  ⟨RingHom.injective _, fun ω ↦
    (quotientToTarget_surjective R I Ω ω).elim fun x hx ↦ ⟨residue _ x, hx⟩⟩

/-- The residue field of the quotient of the colimit over `R` is `Ω`. -/
private noncomputable def quotientResidueFieldEquiv :
    ResidueField (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) ≃ₐ[R ⧸ I] Ω :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ (bijective_lift_quotientToTarget R I Ω))
    fun r ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [IsScalarTower.algebraMap_apply (R ⧸ I) (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω)))
        (ResidueField (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))))]
      simp [quotientToTarget_algebraMap, IsScalarTower.algebraMap_apply R (R ⧸ I) Ω]

private theorem quotientResidueFieldEquiv_residue
    (x : algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) :
    quotientResidueFieldEquiv R I Ω (residue _ x) = quotientToTarget R I Ω x := by
  rw [quotientResidueFieldEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.ofBijective_apply,
    ResidueField.lift_residue_apply]

private theorem quotientToTarget_lift (b : algebra (R ⧸ I) Ω) :
    quotientToTarget R I Ω (lift (R ⧸ I) Ω (quotientResidueFieldEquiv R I Ω).symm.toAlgHom b) =
      toTarget (R ⧸ I) Ω b := by
  rw [← quotientResidueFieldEquiv_residue, residue_lift]
  exact (quotientResidueFieldEquiv R I Ω).apply_symm_apply _

/-- **The strict henselization of a quotient.** For a local ring `R`, an ideal `I`, and a
separable algebraic extension `Ω` of the residue field of `R` that is an `R ⧸ I`-algebra
compatibly with `R`, the quotient of the colimit of pointed étale neighbourhoods of `(R, Ω)` by
the extension of `I` is the colimit for `(R ⧸ I, Ω)`. For a separable closure `Ω`, this
identifies `R^{sh} ⧸ I R^{sh}` with the strict henselization of `R ⧸ I`. -/
@[stacks 05WS]
noncomputable def quotientAlgEquiv :
    (algebra R Ω ⧸ I.map (algebraMap R (algebra R Ω))) ≃ₐ[R ⧸ I] algebra (R ⧸ I) Ω :=
  AlgEquiv.ofAlgHom (quotientHom R I Ω)
    (lift (R ⧸ I) Ω (quotientResidueFieldEquiv R I Ω).symm.toAlgHom)
    (by
      -- An endomorphism of the colimit over `R ⧸ I` fixing the base and the point is the
      -- identity.
      apply AlgHom.toRingHom_injective
      have h := map_unique (RingHom.id (R ⧸ I)) (RingHom.id Ω) (by simp)
        ((quotientHom R I Ω).comp
          (lift (R ⧸ I) Ω (quotientResidueFieldEquiv R I Ω).symm.toAlgHom) : _ →+* _)
        (by ext r; simp) (by ext b; simp [toTarget_quotientHom, quotientToTarget_lift])
      rw [h, map_id, AlgHom.id_toRingHom])
    (by
      -- After composing with the quotient map, both sides are lifts of the same point to the
      -- henselian local quotient.
      apply AlgHom.toRingHom_injective
      apply Ideal.Quotient.ringHom_ext
      let point := (quotientResidueFieldEquiv R I Ω).symm.toAlgHom.restrictScalars R
      have hcomp := eq_lift R Ω point
        (f := (((lift (R ⧸ I) Ω (quotientResidueFieldEquiv R I Ω).symm.toAlgHom).comp
          (quotientHom R I Ω)).restrictScalars R).comp (Ideal.Quotient.mkₐ R _)) <|
        AlgHom.ext fun x ↦ by
          simp [point, residue_lift, toTarget_quotientHom, quotientToTarget_mk]
      have hid := eq_lift R Ω point (f := Ideal.Quotient.mkₐ R _) <|
        AlgHom.ext fun x ↦ (quotientResidueFieldEquiv R I Ω).injective <| by
          simp [point, quotientResidueFieldEquiv_residue, quotientToTarget_mk]
      exact congrArg AlgHom.toRingHom (hcomp.trans hid.symm))

/-- The comparison `quotientAlgEquiv` is induced by the map of colimits along `R → R ⧸ I`. -/
@[simp]
theorem quotientAlgEquiv_mk (x : algebra R Ω) :
    quotientAlgEquiv R I Ω (Ideal.Quotient.mk _ x) =
      map (Ideal.Quotient.mk I) (RingHom.id Ω) (id_comp_algebraMap_eq_comp_mk R I Ω) x := by
  rw [quotientAlgEquiv, AlgEquiv.ofAlgHom_apply, quotientHom_mk]

end Field

end TauCeti.StrictHenselization
