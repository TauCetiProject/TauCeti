/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Basic
import TauCeti.RingTheory.FormalGroup.AdditiveSeries
import TauCeti.RingTheory.FormalGroup.ExponentTwo.Iso
import TauCeti.RingTheory.FormalGroup.Hom
import TauCeti.RingTheory.FormalGroup.ZSMul
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

In particular, a formal group law of exponent two is the transport `g⁻¹ • 𝔾ₐ` of the additive
formal group law along the inverse of its normalized logarithm `g`
(`FormalGroup.inv_smul_𝔾ₐ_eq`). Conversely, if `2 = 0`, transporting the additive law along any
coordinate gives a law of exponent two (`FormalGroup.nsmulSeries_smul_𝔾ₐ_eq_zero`), and the
normalized logarithm of `g⁻¹ • 𝔾ₐ` is `g` when `g` is strict without terms of degree `2ᵏ`,
`k ≥ 1` (`FormalGroup.exponentTwoLog_inv_smul_𝔾ₐ`).

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

/-- **A formal group law of exponent two is determined by its normalized logarithm**: if the
formal coordinate `φ` has series the normalized logarithm `g` of `F`, then
`F(X, Y) = g⁻¹(g(X) + g(Y))`, that is, `F` is the transport `φ⁻¹ • 𝔾ₐ` of the additive formal
group law. -/
theorem inv_smul_𝔾ₐ_eq (hF : F.nsmulSeries 2 = 0) {φ : FormalCoordinate R}
    (hφ : φ.toPowerSeries = F.exponentTwoLog hF) :
    φ⁻¹ • 𝔾ₐ = F := by
  rw [← (F.exponentTwoLogHom hF).smul_eq ((F.exponentTwoLogHom_toPowerSeries hF).trans hφ.symm),
    inv_smul_smul]

variable (φ : FormalCoordinate R)

/-- **Transporting the additive formal group law kills `n` when `n = 0`**: if `n = 0` in `R`, then
`[n](X) = 0` for the formal group law `φ • 𝔾ₐ = φ(φ⁻¹(X) + φ⁻¹(Y))`. This is a converse of
`FormalGroup.natCast_eq_zero_of_nsmulSeries_eq_zero`. -/
theorem nsmulSeries_smul_𝔾ₐ_eq_zero {n : ℕ} (hn : (n : R) = 0) :
    (φ • (𝔾ₐ : FormalGroup R)).nsmulSeries n = 0 := by
  -- Transport `[n]_{𝔾ₐ}(X) = n X = 0` along the isomorphism `φ : 𝔾ₐ → φ • 𝔾ₐ`.
  have h := (smulIso φ (𝔾ₐ (R := R))).zsmulSeries_eq_subst n
  have hn' : (n : PowerSeries R) = 0 := by rw [← map_natCast PowerSeries.C, hn, map_zero]
  rw [zsmulSeries_natCast, zsmulSeries_natCast, nsmulSeries_𝔾ₐ, hn', zero_mul] at h
  rw [h, PowerSeries.subst_zero_of_constantCoeff_zero (smulIso φ 𝔾ₐ).toHom.zero_constantCoeff,
    PowerSeries.subst_zero]

/-- **The normalized logarithm of a transported additive formal group law**: if `2 = 0` in `R` and
`φ = X + ⋯` has no term of degree `2ᵏ` for `k ≥ 1`, then `φ` is the normalized logarithm of
`φ⁻¹ • 𝔾ₐ = φ⁻¹(φ(X) + φ(Y))`. -/
theorem exponentTwoLog_inv_smul_𝔾ₐ (h2 : (2 : R) = 0) (h₁ : PowerSeries.coeff 1 φ.toPowerSeries = 1)
    (hp : ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) φ.toPowerSeries = 0) :
    (φ⁻¹ • (𝔾ₐ : FormalGroup R)).exponentTwoLog
        (nsmulSeries_smul_𝔾ₐ_eq_zero φ⁻¹ (Nat.cast_ofNat.trans h2)) =
      φ.toPowerSeries := by
  -- `φ` is the series of the inverse of the isomorphism `φ⁻¹ : 𝔾ₐ → φ⁻¹ • 𝔾ₐ`.
  have hφ := (smulIso φ⁻¹ (𝔾ₐ (R := R))).invHom.hom
  rw [smulIso_invHom_toPowerSeries, inv_inv] at hφ
  exact ((φ⁻¹ • 𝔾ₐ).eq_exponentTwoLog _ φ.constantCoeff_toPowerSeries h₁ hp
    ((FormalGroupHom.hom_additive_iff φ.constantCoeff_toPowerSeries).mp hφ)).symm

end FormalGroup
