/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Basic
import TauCeti.RingTheory.FormalGroup.AdditiveSeries
import TauCeti.RingTheory.FormalGroup.Hom
import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# All strict logarithms of a formal group law of exponent two

For a commutative formal group law `F` with `[2]_F = 0`, the normalized logarithm
`FormalGroup.exponentTwoLog` is one strict coordinate identifying `F` with the additive group.
Every other strict logarithm is uniquely `a ∘ exponentTwoLog`, where `a` is a strict additive
automorphism. Such an `a` has linear coefficient one and coefficients supported on the powers
of two. Thus the classification is valid over arbitrary commutative rings, including rings with
nilpotents and the zero ring.

`FormalGroup.subst_toPowerSeries_eq_add_iff_existsUnique_subst_exponentTwoLog` gives this
classification entirely in terms of power series and their coefficients. A series occurring as
the factor `a` has zero constant coefficient by its support condition, and hence has a
compositional inverse because its linear coefficient is one.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPowerSeries TauCeti

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm]

/-- A strict series `g` is additive along an exponent-two formal group law exactly when it is
the composite of its normalized logarithm with a unique strict additive automorphism. The
automorphism is characterized by its coefficients: only powers of two can occur, and its linear
coefficient is one. No reducedness or field hypothesis on the coefficient ring is needed. -/
theorem subst_toPowerSeries_eq_add_iff_existsUnique_subst_exponentTwoLog
    (hF : F.nsmulSeries 2 = 0) {g : PowerSeries R}
    (h₀ : PowerSeries.constantCoeff g = 0) (h₁ : PowerSeries.coeff 1 g = 1) :
    PowerSeries.subst F.toPowerSeries g =
        PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g ↔
      ∃! a : PowerSeries R, PowerSeries.coeff 1 a = 1 ∧
        (∀ n, (∀ k, n ≠ 2 ^ k) → PowerSeries.coeff n a = 0) ∧
        g = PowerSeries.subst (F.exponentTwoLog hF) a := by
  have h2 : (2 : R) = 0 := by
    exact_mod_cast F.natCast_eq_zero_of_nsmulSeries_eq_zero hF
  -- Use the generic inverse-coordinate and inverse-homomorphism constructions locally.
  let l : FormalCoordinate R :=
    ⟨F.exponentTwoLog hF, F.constantCoeff_exponentTwoLog hF,
      (F.coeff_one_exponentTwoLog hF).symm ▸ isUnit_one⟩
  have hl : l.toPowerSeries = F.exponentTwoLog hF := rfl
  let f : FormalGroupHom F (𝔾ₐ (R := R)) :=
    ⟨F.exponentTwoLog hF, F.constantCoeff_exponentTwoLog hF,
      (FormalGroupHom.hom_additive_iff (F.constantCoeff_exponentTwoLog hF)).2
        (F.subst_toPowerSeries_exponentTwoLog hF)⟩
  have hf : f.toPowerSeries = l.toPowerSeries := rfl
  have hli : PowerSeries.subst l⁻¹.toPowerSeries f.toPowerSeries = PowerSeries.X := by
    simpa only [FormalCoordinate.toPowerSeries_mul, hf] using l.toPowerSeries_mul_inv
  have hil : PowerSeries.subst f.toPowerSeries l⁻¹.toPowerSeries = PowerSeries.X := by
    simpa only [FormalCoordinate.toPowerSeries_mul, hf] using l.toPowerSeries_inv_mul
  let e := f.ofInverse l⁻¹.toPowerSeries l⁻¹.constantCoeff_toPowerSeries hli hil
  have he : e.toPowerSeries = l⁻¹.toPowerSeries :=
    FormalGroupHom.ofInverse_toPowerSeries _ _ _ _ _
  have hie : PowerSeries.subst f.toPowerSeries e.toPowerSeries = PowerSeries.X := by
    rw [he]
    exact hil
  have he₁ : PowerSeries.coeff 1 e.toPowerSeries = 1 := by
    have hu : l.isUnit_coeff_one.unit = 1 :=
      Units.ext (by
        simpa only [IsUnit.unit_spec, Units.val_one, hl] using F.coeff_one_exponentTwoLog hF)
    rw [he, FormalCoordinate.toPowerSeries_inv, PowerSeries.coeff_one_substInvOfIsUnit,
      hu, inv_one, Units.val_one]
  constructor
  · intro hg
    -- Composing any logarithm with the inverse normalized coordinate gives the additive factor.
    let q : FormalGroupHom F (𝔾ₐ (R := R)) :=
      ⟨g, h₀, (FormalGroupHom.hom_additive_iff h₀).2 hg⟩
    let a := q.comp e
    have ha : a.toPowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) R) =
        a.toPowerSeries.subst (X 0) + a.toPowerSeries.subst (X 1) := by
      simpa only [𝔾ₐ_toPowerSeries] using
        (FormalGroupHom.hom_additive_iff a.zero_constantCoeff).1 a.hom
    have hga : g = PowerSeries.subst (F.exponentTwoLog hF) a.toPowerSeries := by
      rw [FormalGroupHom.comp_toPowerSeries,
        PowerSeries.subst_comp_subst_apply e.hasSubst f.hasSubst, hie,
        PowerSeries.X_subst]
    refine ⟨a.toPowerSeries, ⟨?_, ?_, hga⟩, ?_⟩
    · rw [FormalGroupHom.coeff_one_comp, h₁, he₁, one_mul]
    · exact (PowerSeries.subst_X_add_X_eq_add_iff_of_natCast_eq_zero Nat.prime_two h2 _).1 ha
    · intro b hb
      -- Uniqueness is cancellation of substitution by an invertible coordinate.
      exact l.substAlgEquiv.injective (by
        simp only [FormalCoordinate.substAlgEquiv_apply, hl]
        exact hb.2.2.symm.trans hga)
  · rintro ⟨a, ⟨-, ha, hga⟩, -⟩
    -- Conversely, composing additive series with the normalized logarithm preserves additivity.
    have ha' :=
      (PowerSeries.subst_X_add_X_eq_add_iff_of_natCast_eq_zero Nat.prime_two h2 a).2 ha
    rw [hga, PowerSeries.subst_comp_subst_apply l.hasSubst
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      F.subst_toPowerSeries_exponentTwoLog hF,
      PowerSeries.subst_add_of_subst_X_add_X_eq_add ha'
        (l.hasSubst_subst (PowerSeries.HasSubst.X 0))
        (l.hasSubst_subst (PowerSeries.HasSubst.X 1)),
      PowerSeries.subst_comp_subst_apply l.hasSubst (PowerSeries.HasSubst.X 0),
      PowerSeries.subst_comp_subst_apply l.hasSubst (PowerSeries.HasSubst.X 1)]

end FormalGroup
