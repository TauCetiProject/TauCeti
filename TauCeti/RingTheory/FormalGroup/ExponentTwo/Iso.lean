/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Basic
public import TauCeti.RingTheory.FormalGroup.Hom
public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# The normalized strict isomorphism for exponent-two formal groups

For a commutative formal group `F` with `[2]_F = 0`, the normalized logarithm gives a
strict isomorphism from `F` to the additive formal group. Its inverse homomorphism is the
exponential: it carries addition to `F`, not the other way around. Both series commute
with coefficient-ring homomorphisms, including noninjective ones.

`TauCeti.FormalGroupIso.exponentTwoLog` bundles this isomorphism using the existing
normalized series `FormalGroup.exponentTwoLog` and Mathlib's compositional inverse.
`TauCeti.FormalGroupIso.eq_exponentTwoLog_iff` characterizes it among all isomorphisms to
the additive group by strictness and the vanishing of the power-of-two coefficients of
the forward series. The inverse laws and the action on substitutable power-series points
are supplied by the general `FormalGroupIso` API.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*,
  Bull. Amer. Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

namespace TauCeti.FormalGroupIso

open MvPowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]
variable (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0)

private noncomputable def logHom : FormalGroupHom F FormalGroup.𝔾ₐ where
  toPowerSeries := F.exponentTwoLog hF
  zero_constantCoeff := F.constantCoeff_exponentTwoLog hF
  hom := (FormalGroupHom.hom_additive_iff (F.constantCoeff_exponentTwoLog hF)).2
    (F.subst_toPowerSeries_exponentTwoLog hF)

private theorem isUnit_coeff_log : IsUnit (PowerSeries.coeff 1 (F.exponentTwoLog hF)) := by
  simp

/-- The normalized strict logarithm `F ≅ 𝔾ₐ` of a commutative formal group with `[2]_F = 0`.
Its inverse homomorphism is the strict exponential `𝔾ₐ → F`. -/
noncomputable def exponentTwoLog : FormalGroupIso F FormalGroup.𝔾ₐ :=
  let f := logHom F hF
  let hu : IsUnit (PowerSeries.coeff 1 f.toPowerSeries) := isUnit_coeff_log F hF
  let e := f.toPowerSeries.substInvOfIsUnit hu
  let he₀ := PowerSeries.constantCoeff_substInvOfIsUnit f.toPowerSeries hu
  let hge := PowerSeries.subst_substInvOfIsUnit_right f.toPowerSeries f.zero_constantCoeff hu
  let heg := PowerSeries.subst_substInvOfIsUnit_left f.toPowerSeries f.zero_constantCoeff hu
  .ofSubstEqX f (f.ofInverse e he₀ hge heg)
    (by rw [FormalGroupHom.ofInverse_toPowerSeries]; exact hge)
    (by rw [FormalGroupHom.ofInverse_toPowerSeries]; exact heg)

/-- The forward series of the bundled isomorphism is the normalized logarithm. -/
@[simp]
theorem exponentTwoLog_toHom_toPowerSeries :
    (exponentTwoLog F hF).toHom.toPowerSeries = F.exponentTwoLog hF := by
  simp only [exponentTwoLog, ofSubstEqX_toHom, logHom]

/-- The normalized logarithm is a strict formal group isomorphism. -/
instance : (exponentTwoLog F hF).IsStrict where
  coeff_one := by simp

/-- Among isomorphisms `F ≅ 𝔾ₐ`, the normalized logarithm is characterized by strictness
and the vanishing of its coefficients of degree `2^k`, `k > 0`. -/
theorem eq_exponentTwoLog_iff (f : FormalGroupIso F FormalGroup.𝔾ₐ) :
    f = exponentTwoLog F hF ↔ f.IsStrict ∧
      ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) f.toHom.toPowerSeries = 0 := by
  constructor
  · rintro rfl
    exact ⟨inferInstance, fun _ hk ↦ by simp [F.coeff_two_pow_exponentTwoLog hF hk]⟩
  · rintro ⟨hf, hp⟩
    apply FormalGroupIso.ext
    apply FormalGroupHom.ext
    rw [exponentTwoLog_toHom_toPowerSeries]
    exact F.eq_exponentTwoLog hF f.toHom.zero_constantCoeff hf.coeff_one hp
      ((FormalGroupHom.hom_additive_iff f.toHom.zero_constantCoeff).1 f.toHom.hom)

/-- Applying a coefficient-ring homomorphism to the normalized logarithm gives the
normalized logarithm of the base-changed formal group. The exponent-two proof in the
target ring may be any proof; it follows from `FormalGroup.map_nsmulSeries`. -/
theorem map_exponentTwoLog_toHom (f : R →+* S)
    (hF' : (F.map f).nsmulSeries 2 = 0 := by rw [← F.map_nsmulSeries, hF, map_zero]) :
    PowerSeries.map f (exponentTwoLog F hF).toHom.toPowerSeries =
      (exponentTwoLog (F.map f) hF').toHom.toPowerSeries := by
  simp only [exponentTwoLog_toHom_toPowerSeries]
  apply (F.map f).eq_exponentTwoLog hF'
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_exponentTwoLog, map_zero]
  · simp
  · intro k hk
    simp [F.coeff_two_pow_exponentTwoLog hF hk]
  · have h := congrArg (MvPowerSeries.map f) (F.subst_toPowerSeries_exponentTwoLog hF)
    simpa only [PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff), map_add,
      PowerSeries.map_subst (PowerSeries.HasSubst.X _), map_X,
      FormalGroup.map_toPowerSeries] using h

/-- Applying a coefficient-ring homomorphism to the normalized exponential gives the
normalized exponential of the base-changed formal group. -/
theorem map_exponentTwoLog_invHom (f : R →+* S)
    (hF' : (F.map f).nsmulSeries 2 = 0 := by rw [← F.map_nsmulSeries, hF, map_zero]) :
    PowerSeries.map f (exponentTwoLog F hF).invHom.toPowerSeries =
      (exponentTwoLog (F.map f) hF').invHom.toPowerSeries := by
  let g := exponentTwoLog F hF
  let g' := exponentTwoLog (F.map f) hF'
  have he : PowerSeries.HasSubst (PowerSeries.map f g.invHom.toPowerSeries) :=
    .of_constantCoeff_zero' (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, g.invHom.zero_constantCoeff, map_zero])
  have hge : PowerSeries.subst (PowerSeries.map f g.invHom.toPowerSeries)
      g'.toHom.toPowerSeries = PowerSeries.X := by
    have hm : PowerSeries.map f g.toHom.toPowerSeries = g'.toHom.toPowerSeries :=
      map_exponentTwoLog_toHom F hF f hF'
    rw [← hm]
    calc
      _ = PowerSeries.map f
          (PowerSeries.subst g.invHom.toPowerSeries g.toHom.toPowerSeries) := by
        -- Univariate coefficient maps are multivariate coefficient maps on `Unit`.
        simpa only [PowerSeries.map] using
          (PowerSeries.map_subst g.invHom.hasSubst (h := f) g.toHom.toPowerSeries).symm
      _ = PowerSeries.X := by rw [g.subst_invHom_toHom, PowerSeries.map_X]
  have hu : IsUnit (PowerSeries.coeff 1 g'.toHom.toPowerSeries) := by
    simp only [IsStrict.coeff_one, isUnit_one]
  exact (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X g'.toHom.toPowerSeries
    g'.toHom.zero_constantCoeff hu he hge).trans
      (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X g'.toHom.toPowerSeries
        g'.toHom.zero_constantCoeff hu g'.invHom.hasSubst g'.subst_invHom_toHom).symm

end TauCeti.FormalGroupIso
