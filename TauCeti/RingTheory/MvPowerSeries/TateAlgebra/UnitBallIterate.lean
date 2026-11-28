/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# Iteration of Gauss unit balls in one separated variable

For an ultrametric normed commutative ring `R` with `‖1‖ = 1`, separating the variable
`none : Option σ` identifies `R⟨X, Y⟩ = R{T / 1}` with univariate unit-radius restricted power
series over `R⟨X⟩` via `MvPowerSeries.restrictedOptionEquiv`. Restricting to Gauss unit balls
embeds `R⟨X⟩°` into `R⟨X, Y⟩°` as series constant in the separated variable `none`
(`TauCeti.MvPowerSeries.optionEmbedHom`), and parameterizes series in `R⟨X, Y⟩°` of degree `< s`
in `none` as an `R⟨X⟩°`-semilinear map from `Fin s → R⟨X⟩°`
(`TauCeti.MvPowerSeries.optionTruncHom`).

## Main definitions

* `TauCeti.MvPowerSeries.optionEmbedHom`: the embedding `R⟨X⟩° →+* R⟨X, Y⟩°` sending a series to
  the corresponding constant series in the separated variable `X none`.
* `TauCeti.MvPowerSeries.optionTruncHom`: the `optionEmbedHom`-semilinear map from
  `Fin s → R⟨X⟩°` to `R⟨X, Y⟩°` assembling a truncated series of degree `< s` in `X none`.

## Main results

* `TauCeti.MvPowerSeries.restrictedOptionEquiv_optionEmbedHom`: `restrictedOptionEquiv` sends
  `optionEmbedHom σ b` to the constant univariate series `algebraMap (R⟨X⟩) _ b`.
* `TauCeti.MvPowerSeries.optionEmbedHom_coeff`: `optionEmbedHom` sends constant series
  `unitClosedBallC c` to `unitClosedBallC c`.
* `TauCeti.MvPowerSeries.coeff_restrictedOptionEquiv_optionTruncHom`: the `m`-th slice of
  `optionTruncHom σ s u` under `restrictedOptionEquiv` is `u m` for `m < s` and `0` otherwise.
* `TauCeti.MvPowerSeries.exists_optionTruncHom_eq`: any series in `R⟨X, Y⟩°` whose monomials have
  exponent `< s` in `none` lies in the range of `optionTruncHom σ s`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.1.
* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
-/

public section

open _root_.MvPowerSeries

namespace TauCeti.MvPowerSeries

section UnitBallIterate

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

local notation "Tate " τ:max => IsRestricted.subring (R := R) (fun _ : τ ↦ 1)

/-- Embed `R⟨X⟩°` into `R⟨X, Y⟩°` as series constant in the separated variable `X none`. -/
noncomputable def optionEmbedHom (σ : Type*) :
    Subring.unitClosedBall (Tate σ) →+* Subring.unitClosedBall (Tate (Option σ)) :=
  ((restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).symm.toRingHom.comp
    (algebraMap (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1))).restrict _ _
    fun b hb ↦ Subring.mem_unitClosedBall.mpr <| by
      have ha : algebraMap (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1) b =
          ⟨PowerSeries.C b, PowerSeries.isRestricted_C 1 b⟩ := Subtype.ext (by simp)
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toRingEquiv, ← norm_restrictedOptionEquiv (c := fun _ ↦ 1),
        AlgEquiv.apply_symm_apply, ha, TauCeti.PowerSeries.norm_C]
      exact Subring.mem_unitClosedBall.mp hb

/-- `restrictedOptionEquiv` sends `optionEmbedHom σ b` to the constant univariate series at `b`. -/
@[simp]
theorem restrictedOptionEquiv_optionEmbedHom {σ : Type*}
    (b : Subring.unitClosedBall (Tate σ)) :
    restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)
        (optionEmbedHom σ b : Tate (Option σ)) =
      algebraMap (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1) b := by
  simp [optionEmbedHom]

/-- `optionEmbedHom` sends constant series in `R⟨X⟩°` to constant series in `R⟨X, Y⟩°`. -/
@[simp]
theorem optionEmbedHom_coeff (σ : Type*) (c : Subring.unitClosedBall R) :
    optionEmbedHom σ (unitClosedBallC c) = unitClosedBallC c := by
  apply Subtype.ext
  apply (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).injective
  rw [restrictedOptionEquiv_optionEmbedHom, coe_unitClosedBallC, coe_unitClosedBallC,
    AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply R (Tate σ)
    (PowerSeries.IsRestricted.subring (R := Tate σ) 1) (c : R)).symm

private noncomputable def optionTruncFun (σ : Type*) (s : ℕ)
    (u : Fin s → Subring.unitClosedBall (Tate σ)) :
    Subring.unitClosedBall (Tate (Option σ)) :=
  let p : PowerSeries (Tate σ) :=
    PowerSeries.mk fun m ↦ if hm : m < s then (u ⟨m, hm⟩ : Tate σ) else 0
  have hp : PowerSeries.IsRestricted 1 p :=
    TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero (n := s) fun m hm ↦ by
      rw [PowerSeries.coeff_mk]
      split_ifs with h
      · exact absurd h (not_lt.mpr hm)
      · rfl
  ⟨(restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).symm ⟨p, hp⟩,
    Subring.mem_unitClosedBall.mpr <| by
      rw [← norm_restrictedOptionEquiv (c := fun _ ↦ 1), AlgEquiv.apply_symm_apply,
        TauCeti.PowerSeries.norm_le_iff]
      intro m
      simp only [p, PowerSeries.coeff_mk, one_pow, mul_one]
      split_ifs with hm
      · exact Subring.mem_unitClosedBall.mp (u ⟨m, hm⟩).property
      · simp⟩

private theorem coeff_restrictedOptionEquiv_optionTruncFun (σ : Type*) (s : ℕ)
    (u : Fin s → Subring.unitClosedBall (Tate σ)) (m : ℕ) :
    PowerSeries.coeff m
        (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)
            (optionTruncFun σ s u : Tate (Option σ)) :
          PowerSeries (Tate σ)) =
      if hm : m < s then (u ⟨m, hm⟩ : Tate σ) else 0 := by
  simp [optionTruncFun]

/-- Parameterize series in `R⟨X, Y⟩°` of degree `< s` in `X none` by `Fin s → R⟨X⟩°`,
semilinearly over `optionEmbedHom σ`. -/
noncomputable def optionTruncHom (σ : Type*) (s : ℕ) :
    (Fin s → Subring.unitClosedBall (Tate σ)) →ₛₗ[optionEmbedHom (R := R) σ]
      Subring.unitClosedBall (Tate (Option σ)) where
  toFun := optionTruncFun σ s
  map_add' u₁ u₂ := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).injective <| Subtype.ext <|
      PowerSeries.ext fun m ↦ by
        simp only [AddMemClass.coe_add, map_add, coeff_restrictedOptionEquiv_optionTruncFun,
          Pi.add_apply]
        split_ifs <;> simp
  map_smul' b u := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).injective <| Subtype.ext <|
      PowerSeries.ext fun m ↦ by
        simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul,
          restrictedOptionEquiv_optionEmbedHom,
          TauCeti.PowerSeries.coe_algebraMap_isRestrictedSubring,
          PowerSeries.coeff_C_mul, coeff_restrictedOptionEquiv_optionTruncFun, Pi.smul_apply]
        split_ifs <;> simp

/-- Under `restrictedOptionEquiv`, the `m`-th coefficient slice of `optionTruncHom σ s u` is `u m`
for `m < s` and `0` otherwise. -/
@[simp]
theorem coeff_restrictedOptionEquiv_optionTruncHom {σ : Type*} {s : ℕ}
    (u : Fin s → Subring.unitClosedBall (Tate σ)) (m : ℕ) :
    PowerSeries.coeff m
        (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)
            (optionTruncHom σ s u : Tate (Option σ)) :
          PowerSeries (Tate σ)) =
      if hm : m < s then (u ⟨m, hm⟩ : Tate σ) else 0 :=
  coeff_restrictedOptionEquiv_optionTruncFun σ s u m

/-- Any series in `R⟨X, Y⟩°` whose monomials all have exponent `< s` in `none` lies in the range
of `optionTruncHom σ s`. -/
theorem exists_optionTruncHom_eq {σ : Type*} {s : ℕ}
    (rd : Subring.unitClosedBall (Tate (Option σ)))
    (hrd : ∀ t : Option σ →₀ ℕ,
      s ≤ t none → coeff t ((rd : Tate (Option σ)) : MvPowerSeries (Option σ) R) = 0) :
    ∃ u : Fin s → Subring.unitClosedBall (Tate σ), optionTruncHom σ s u = rd := by
  let Riter := restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1) (rd : Tate (Option σ))
  have hzero := (forall_coeff_restrictedOptionEquiv_eq_zero_iff (rd : Tate (Option σ)) s).mpr hrd
  refine ⟨fun k ↦ ⟨PowerSeries.coeff (k : ℕ) (Riter : PowerSeries _),
    Subring.mem_unitClosedBall.mpr <| by
      have hle := TauCeti.PowerSeries.norm_coeff_mul_pow_le Riter (k : ℕ)
      rw [one_pow, mul_one, norm_restrictedOptionEquiv] at hle
      exact hle.trans (Subring.mem_unitClosedBall.mp rd.property)⟩, ?_⟩
  apply Subtype.ext
  apply (restrictedOptionEquiv (σ := σ) (R := R) (c := fun _ ↦ 1)).injective
  apply Subtype.ext
  refine PowerSeries.ext fun m ↦ ?_
  rw [coeff_restrictedOptionEquiv_optionTruncHom]
  split_ifs with hm
  · rfl
  · exact (hzero m (not_lt.mp hm)).symm

end UnitBallIterate

end TauCeti.MvPowerSeries
