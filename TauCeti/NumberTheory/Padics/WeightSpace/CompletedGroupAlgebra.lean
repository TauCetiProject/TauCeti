/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Splitting
public import TauCeti.Algebra.MonoidAlgebra.LocalRing
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.CoordinateTopology
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The completed group algebra `ℤ_p[[ℤ_pˣ]]` in weight coordinates

Put `q = p ^ TauCeti.padicUnitsDepth p` (`q = p` for odd `p`, `q = 4` for `p = 2`), `Δ = (ℤ/qℤ)ˣ`,
`ω = TauCeti.padicUnitsSection p : Δ →* ℤ_pˣ`, and `γ = TauCeti.padicUnitsGenerator p = exp q`.

Transporting `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate` along
`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* Δ × ℤ_p` gives the topological `ℤ_p`-algebra
homeomorphism `TauCeti.padicUnitsCoordinate p : (ℤ_[p][Δ])⟦X⟧ ≃ₐ[ℤ_[p]] ℤ_[p][[ℤ_[p]ˣ]]` sending
`X ↦ [γ] - 1` and `[δ] ↦ [ω(δ)]`, with inverse `[x] ↦ [x mod q] · (1 + X) ^ (log(x / ω(x mod q)) /
q)`. Replacing `γ` by `γ ^ u = exp(q u)` (`u ∈ ℤ_pˣ`) gives `TauCeti.padicUnitsCoordinateAt p u`,
related by `X ↦ (1 + X) ^ u - 1`.

* For every prime `p`, `ℤ_p` has enough roots of unity of exponent `exp(Δ)` via `ω`
  (`TauCeti.hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth`).
* When `p ≠ 2`, `#Δ = p - 1` is a unit in `ℤ_p`, splitting `ℤ_p[Δ]` and `ℤ_p[[ℤ_pˣ]]` integrally
  along characters (`TauCeti.padicUnitsCompletedGroupAlgebraSplitting`).
* When `p = 2`, `ℤ_2[(ℤ/4ℤ)ˣ]` and `ℤ_2[[ℤ_2ˣ]]` are local with maximal ideals `(2, [-1] - 1)` and
  `(X, 2, [-1] - 1)` in power-series coordinates, so `ℤ_2[[ℤ_2ˣ]]` has no nontrivial idempotents
  (`TauCeti.isIdempotentElem_completedGroupAlgebra_dyadicUnits_iff`), while `ℚ_2[(ℤ/4ℤ)ˣ]` splits
  rationally (`TauCeti.dyadicRationalFiniteGroupRingEquiv`).

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §7.1.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.3 and 4.
-/

public section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti

section Coordinate

variable (p : ℕ) [Fact p.Prime]

/-- **The weight power-series coordinate of `ℤ_p[[ℤ_pˣ]]`.** Writing `q = p ^ padicUnitsDepth p`
and `Δ = (ℤ/qℤ)ˣ`, `ℤ_pˣ ≃ₜ* Δ × ℤ_p` identifies `ℤ_p[[ℤ_pˣ]]` with `(ℤ_p[Δ])⟦X⟧`, sending `X` to
`[γ] - 1` (`γ = exp q`) and `[δ]` to `[ω(δ)]`. -/
noncomputable def padicUnitsCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ :=
  (completedGroupAlgebra.prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
    (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p)).trans
    (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm)

theorem padicUnitsCoordinate_def :
    padicUnitsCoordinate p =
      (completedGroupAlgebra.prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
        (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p)).trans
        (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm) :=
  (rfl)

/-- `padicUnitsCoordinate` sends `X` to `[γ] - 1`, where `γ = padicUnitsGenerator p`. -/
@[simp]
theorem padicUnitsCoordinate_X :
    padicUnitsCoordinate p PowerSeries.X =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1 := by
  have hγ : (padicIntUnitsEquivZModUnitsProd p).symm (1, Multiplicative.ofAdd 1) =
      padicUnitsGenerator p :=
    (padicIntUnitsEquivZModUnitsProd p).symm_apply_eq.mpr
      padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator.symm
  rw [padicUnitsCoordinate, AlgEquiv.trans_apply,
    completedGroupAlgebra.prodPowerSeriesCoordinate_X, map_sub,
    map_one (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm),
    completedGroupAlgebra.domCongr_of, hγ]

/-- `padicUnitsCoordinate` sends `1 + X` to `[γ]`. -/
@[simp]
theorem padicUnitsCoordinate_one_add_X :
    padicUnitsCoordinate p (1 + PowerSeries.X) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) := by
  rw [map_add, map_one, padicUnitsCoordinate_X, add_sub_cancel]

/-- `padicUnitsCoordinate` sends the constant `a · [δ]` of `ℤ_p[Δ]` to `a · [ω(δ)]`. -/
@[simp]
theorem padicUnitsCoordinate_C_single (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a *
        completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinate, AlgEquiv.trans_apply,
    completedGroupAlgebra.prodPowerSeriesCoordinate_C_single, map_mul, AlgEquiv.commutes,
    completedGroupAlgebra.domCongr_of, padicIntUnitsEquivZModUnitsProd_symm_apply, map_one,
    OneMemClass.coe_one, mul_one]

/-- `padicUnitsCoordinate` sends `[δ]` in `ℤ_p[Δ]` to `[ω(δ)]`. -/
theorem padicUnitsCoordinate_C_single_one (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ 1)) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinate_C_single, map_one, one_mul]

/-- `padicUnitsCoordinate` sends the binomial series `(1 + X) ^ s` to `[exp(q s)]`. -/
@[simp]
theorem padicUnitsCoordinate_binomialSeries (s : ℤ_[p]) :
    padicUnitsCoordinate p
      (PowerSeries.binomialSeries
        (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) s) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ ((unitsPrincipalLogEquiv p).symm (.ofAdd s)) := by
  set C := (ZMod (p ^ padicUnitsDepth p))ˣ
  let φ := PowerSeries.binomialSeries ℤ_[p] s
  have hmap : PowerSeries.binomialSeries (MonoidAlgebra ℤ_[p] C) s =
      PowerSeries.map (MonoidAlgebra.singleOneRingHom : ℤ_[p] →+* MonoidAlgebra ℤ_[p] C) φ := by
    ext n; simp [φ, PowerSeries.binomialSeries_coeff, MonoidAlgebra.one_def]
  have h1 : (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] C).symm
      (PowerSeries.map (MonoidAlgebra.singleOneRingHom : ℤ_[p] →+* MonoidAlgebra ℤ_[p] C) φ) =
      MonoidAlgebra.single 1 φ :=
    (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] C).symm_apply_eq.mpr
      (by rw [MonoidAlgebra.coe_powerSeriesAlgEquiv, MonoidAlgebra.toPowerSeries_single_one])
  have h2 : MonoidAlgebra.mapAlgEquiv ℤ_[p] C
      (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p)) (MonoidAlgebra.single 1 φ) =
      MonoidAlgebra.single 1 (completedGroupAlgebra.powerSeriesCoordinate
        (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_one_padicInt p) φ) :=
    MonoidAlgebra.mapAlgHom_single _ 1 φ
  rw [hmap, padicUnitsCoordinate, AlgEquiv.trans_apply,
    completedGroupAlgebra.prodPowerSeriesCoordinate_def, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, h1, h2, completedGroupAlgebra.coe_monoidAlgebraProdEquiv,
    completedGroupAlgebra.monoidAlgebraProdHom_single_one,
    completedGroupAlgebra.powerSeriesCoordinate_binomialSeries,
    IsProP.padicPow_ofAdd_one_padicInt, completedGroupAlgebra.map_of, MonoidHom.inr_apply,
    completedGroupAlgebra.domCongr_of, padicIntUnitsEquivZModUnitsProd_symm_apply, map_one, one_mul]

/-- **Expansion of group elements in weight coordinates.** The inverse of `padicUnitsCoordinate`
sends `[x]` (`x ∈ ℤ_pˣ`) to `[x mod q] · (1 + X) ^ (log (x / ω(x mod q)) / q)`. -/
theorem padicUnitsCoordinate_symm_of (x : ℤ_[p]ˣ) :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      PowerSeries.C (MonoidAlgebra.single (padicIntUnitsEquivZModUnitsProd p x).1 1) *
        PowerSeries.binomialSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)
          (padicIntUnitsEquivZModUnitsProd p x).2.toAdd := by
  apply (padicUnitsCoordinate p).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, padicUnitsCoordinate_C_single_one,
    padicUnitsCoordinate_binomialSeries, ← map_mul, ofAdd_toAdd,
    ← padicIntUnitsEquivZModUnitsProd_symm_apply, ContinuousMulEquiv.symm_apply_apply]

@[simp]
theorem padicUnitsCoordinate_symm_of_padicUnitsSection (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) =
      PowerSeries.C (MonoidAlgebra.single δ 1) :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_C_single_one p δ).symm

@[simp]
theorem padicUnitsCoordinate_symm_of_padicUnitsGenerator :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) =
      1 + PowerSeries.X :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_one_add_X p).symm

section GeneratorChange

private theorem topologicallyGenerates_ofAdd_unit (u : ℤ_[p]ˣ) :
    (Subgroup.closure ({Multiplicative.ofAdd (u : ℤ_[p])} :
      Set (Multiplicative ℤ_[p]))).topologicalClosure = ⊤ := by
  rw [← IsProP.padicPow_ofAdd_one_padicInt p (u : ℤ_[p]),
    (isProP_multiplicative_padicInt p).topologicalClosure_closure_padicPow_eq_top_iff
      (topologicallyGenerates_ofAdd_one_padicInt p)]
  exact u.isUnit

/-- **The weight power-series coordinate at a changed generator `γ ^ u = exp(q u)`.** For
`u ∈ ℤ_pˣ`, this sends `X` to `[exp(q u)] - 1` while keeping `[δ] ↦ [ω(δ)]` on `Δ`. -/
noncomputable def padicUnitsCoordinateAt (u : ℤ_[p]ˣ) :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ :=
  (completedGroupAlgebra.prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
    (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_unit p u)).trans
    (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm)

@[simp]
theorem padicUnitsCoordinateAt_X (u : ℤ_[p]ˣ) :
    padicUnitsCoordinateAt p u PowerSeries.X =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ
        ((unitsPrincipalLogEquiv p).symm (.ofAdd (u : ℤ_[p]))) - 1 := by
  rw [padicUnitsCoordinateAt, AlgEquiv.trans_apply,
    completedGroupAlgebra.prodPowerSeriesCoordinate_X, map_sub,
    map_one (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm),
    completedGroupAlgebra.domCongr_of, padicIntUnitsEquivZModUnitsProd_symm_apply, map_one, one_mul]

@[simp]
theorem padicUnitsCoordinateAt_C_single (u : ℤ_[p]ˣ) (δ : (ZMod (p ^ padicUnitsDepth p))ˣ)
    (a : ℤ_[p]) :
    padicUnitsCoordinateAt p u (PowerSeries.C (MonoidAlgebra.single δ a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a *
        completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinateAt, AlgEquiv.trans_apply,
    completedGroupAlgebra.prodPowerSeriesCoordinate_C_single, map_mul, AlgEquiv.commutes,
    completedGroupAlgebra.domCongr_of, padicIntUnitsEquivZModUnitsProd_symm_apply, map_one,
    OneMemClass.coe_one, mul_one]

/-- **Change of principal generator in `ℤ_p[[ℤ_pˣ]]`.** Replacing `γ` by `γ ^ u = exp(q u)` changes
the power-series coordinate by the substitution `X ↦ (1 + X) ^ u - 1`. -/
theorem padicUnitsCoordinateAt_apply (u : ℤ_[p]ˣ)
    (ψ : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    padicUnitsCoordinateAt p u ψ =
      padicUnitsCoordinate p
        (ψ.subst (PowerSeries.binomialSeries
          (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) (u : ℤ_[p]) - 1)) := by
  let R := MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ
  let g : PowerSeries R := PowerSeries.binomialSeries R (u : ℤ_[p]) - 1
  have hC (r : R) : padicUnitsCoordinateAt p u (PowerSeries.C r) =
      padicUnitsCoordinate p (PowerSeries.C r) := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | single δ a => rw [padicUnitsCoordinateAt_C_single, padicUnitsCoordinate_C_single]
  let σ : PowerSeries R →ₐ[R] PowerSeries R :=
    { ((padicUnitsCoordinate p).symm.toRingEquiv.toRingHom).comp
        (padicUnitsCoordinateAt p u).toRingEquiv.toRingHom with
      commutes' r := (padicUnitsCoordinate p).symm_apply_eq.mpr (hC r) }
  have hσX : σ PowerSeries.X = g := (padicUnitsCoordinate p).symm_apply_eq.mpr <| by
    change padicUnitsCoordinateAt p u PowerSeries.X = _
    rw [padicUnitsCoordinateAt_X, map_sub, map_one, padicUnitsCoordinate_binomialSeries]
  have hg : PowerSeries.HasSubst (σ PowerSeries.X) := by
    rw [hσX]
    exact PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [g])
  have hsub := congr($(PowerSeries.algHom_eq_substAlgHom (σ := σ) hg) ψ)
  rw [PowerSeries.coe_substAlgHom, hσX] at hsub
  exact (padicUnitsCoordinate p).symm_apply_eq.mp hsub

@[simp]
theorem padicUnitsCoordinateAt_one :
    padicUnitsCoordinateAt p 1 = padicUnitsCoordinate p := by
  refine AlgEquiv.ext fun ψ ↦ ?_
  have hb : PowerSeries.binomialSeries
      (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) (1 : ℤ_[p]) = 1 + PowerSeries.X := by
    simpa using PowerSeries.binomialSeries_nat
      (A := MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) (R := ℤ_[p]) 1
  rw [padicUnitsCoordinateAt_apply, Units.val_one, hb, add_sub_cancel_left, PowerSeries.X_subst]

end GeneratorChange

section Topology

variable [TopologicalSpace (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]
  [IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]

/-- `padicUnitsCoordinateAt p u` is continuous for every unit `u ∈ ℤ_pˣ`. -/
theorem continuous_padicUnitsCoordinateAt (u : ℤ_[p]ˣ) :
    Continuous (padicUnitsCoordinateAt p u) := by
  rw [padicUnitsCoordinateAt, AlgEquiv.coe_trans, completedGroupAlgebra.coe_domCongr]
  exact (completedGroupAlgebra.continuous_map ℤ_[p]
    ((padicIntUnitsEquivZModUnitsProd p).symm : _ →* ℤ_[p]ˣ)
    (padicIntUnitsEquivZModUnitsProd p).symm.continuous).comp
    (completedGroupAlgebra.continuous_prodPowerSeriesCoordinate
      (ZMod (p ^ padicUnitsDepth p))ˣ
      (isProP_multiplicative_padicInt p)
      (topologicallyGenerates_ofAdd_unit p u))

/-- The inverse of `padicUnitsCoordinateAt p u` is continuous. -/
theorem continuous_padicUnitsCoordinateAt_symm (u : ℤ_[p]ˣ) :
    Continuous (padicUnitsCoordinateAt p u).symm := by
  refine ((completedGroupAlgebra.continuous_prodPowerSeriesCoordinate_symm
    (ZMod (p ^ padicUnitsDepth p))ˣ (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_unit p u)).comp
    (completedGroupAlgebra.continuous_map ℤ_[p]
      (padicIntUnitsEquivZModUnitsProd p : ℤ_[p]ˣ →* _)
      (padicIntUnitsEquivZModUnitsProd p).continuous)).congr fun z ↦ ?_
  simp [padicUnitsCoordinateAt, ← completedGroupAlgebra.coe_domCongr,
    completedGroupAlgebra.domCongr_symm]

/-- `padicUnitsCoordinate` is continuous for the module topology on `ℤ_p[Δ]`, the coefficientwise
topology on `(ℤ_p[Δ])⟦X⟧`, and the inverse-limit topology on `ℤ_p[[ℤ_pˣ]]`. -/
theorem continuous_padicUnitsCoordinate : Continuous (padicUnitsCoordinate p) :=
  padicUnitsCoordinateAt_one p ▸ continuous_padicUnitsCoordinateAt p 1

/-- The inverse of `padicUnitsCoordinate` is continuous, so `padicUnitsCoordinate` is a
homeomorphism between `(ℤ_p[Δ])⟦X⟧` and `ℤ_p[[ℤ_pˣ]]`. -/
theorem continuous_padicUnitsCoordinate_symm : Continuous (padicUnitsCoordinate p).symm :=
  padicUnitsCoordinateAt_one p ▸ continuous_padicUnitsCoordinateAt_symm p 1

end Topology

end Coordinate

section RootsOfUnity

variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative section `ω : (ℤ/qℤ)ˣ →* ℤ_pˣ` is injective. -/
theorem padicUnitsSection_injective : Function.Injective (padicUnitsSection p) :=
  Function.LeftInverse.injective unitsToZModPow_padicUnitsSection

/-- For every prime `p`, `ℤ_p` contains enough roots of unity of exponent `exp((ℤ/qℤ)ˣ)`, supplied
by `TauCeti.padicUnitsSection p`. -/
theorem hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth :
    HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (ZMod (p ^ padicUnitsDepth p))ˣ) := by
  set G := (ZMod (p ^ padicUnitsDepth p))ˣ
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let ι : G → rootsOfUnity (Nat.card G) ℤ_[p] := fun δ ↦
    ⟨padicUnitsSection p δ, by rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hcard : HasEnoughRootsOfUnity ℤ_[p] (Nat.card G) := HasEnoughRootsOfUnity.of_card_le <|
    Nat.card_le_card_of_injective ι fun _ _ h ↦ padicUnitsSection_injective p (Subtype.mk.inj h)
  exact HasEnoughRootsOfUnity.of_dvd ℤ_[p] Group.exponent_dvd_nat_card

end RootsOfUnity

section OddPrime

variable {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
include hp

/-- For an odd prime `p`, the order `p - 1` of `(ℤ/pℤ)ˣ` is a unit in `ℤ_p`. -/
theorem isUnit_card_zmodUnits_padicUnitsDepth :
    IsUnit (Nat.card (ZMod (p ^ padicUnitsDepth p))ˣ : ℤ_[p]) := by
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le hp.symm
  rw [padicUnitsDepth_of_ne_two hp, pow_one, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime Fact.out]
  exact PadicInt.isUnit_natCast_of_coprime <| (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    fun hdvd ↦ by have := Nat.le_of_dvd (by omega : 0 < p - 1) hdvd; omega

/-- **Integral character splitting of `ℤ_p[(ℤ/pℤ)ˣ]` for odd `p`.** -/
noncomputable def padicUnitsFiniteGroupRingEquiv :
    MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → ℤ_[p]) :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  MonoidAlgebra.charEvalEquiv (isUnit_card_zmodUnits_padicUnitsDepth hp)

@[simp]
theorem padicUnitsFiniteGroupRingEquiv_apply
    (x : MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)
    (ψ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsFiniteGroupRingEquiv hp x ψ = ψ.charEval x :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  MonoidAlgebra.charEvalEquiv_apply (isUnit_card_zmodUnits_padicUnitsDepth hp) x ψ

@[simp]
theorem padicUnitsFiniteGroupRingEquiv_charIdempotent
    [DecidableEq ((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ)]
    (χ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsFiniteGroupRingEquiv hp (charIdempotent χ) = Pi.single χ 1 :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  MonoidAlgebra.charEvalEquiv_charIdempotent (isUnit_card_zmodUnits_padicUnitsDepth hp) χ

/-- **Integral character splitting of `(ℤ_p[(ℤ/pℤ)ˣ])⟦X⟧` for odd `p`.** -/
noncomputable def padicUnitsPowerSeriesSplitting :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → PowerSeries ℤ_[p]) :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  MonoidAlgebra.powerSeriesCharEvalEquiv (isUnit_card_zmodUnits_padicUnitsDepth hp)

@[simp]
theorem padicUnitsPowerSeriesSplitting_apply
    (φ : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ))
    (ψ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsPowerSeriesSplitting hp φ ψ = PowerSeries.map ψ.charEval.toRingHom φ :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  MonoidAlgebra.powerSeriesCharEvalEquiv_apply (isUnit_card_zmodUnits_padicUnitsDepth hp) φ ψ

/-- **Integral splitting of `ℤ_p[[ℤ_pˣ]]` into character branches for odd `p`.** -/
noncomputable def padicUnitsCompletedGroupAlgebraSplitting :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → PowerSeries ℤ_[p]) :=
  (padicUnitsCoordinate p).symm.trans (padicUnitsPowerSeriesSplitting hp)

@[simp]
theorem padicUnitsCompletedGroupAlgebraSplitting_of_padicUnitsGenerator :
    padicUnitsCompletedGroupAlgebraSplitting hp
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) =
      fun _ ↦ 1 + PowerSeries.X := by
  ext; simp [padicUnitsCompletedGroupAlgebraSplitting]

@[simp]
theorem padicUnitsCompletedGroupAlgebraSplitting_of_padicUnitsSection
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsCompletedGroupAlgebraSplitting hp
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) =
      fun ψ ↦ PowerSeries.C (ψ δ : ℤ_[p]) := by
  ext; simp [padicUnitsCompletedGroupAlgebraSplitting]

/-- Under `padicUnitsCompletedGroupAlgebraSplitting`, the constant idempotent
`padicUnitsCoordinate p (C (charIdempotent χ))` is `Pi.single χ 1`. -/
@[simp]
theorem padicUnitsCompletedGroupAlgebraSplitting_padicUnitsCoordinate_C_charIdempotent
    [DecidableEq ((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ)]
    (χ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsCompletedGroupAlgebraSplitting hp
        (padicUnitsCoordinate p (PowerSeries.C (charIdempotent χ))) =
      Pi.single χ 1 := by
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  ext ψ n
  simp [padicUnitsCompletedGroupAlgebraSplitting, Pi.single_apply, eq_comm,
    MonoidHom.charEval_charIdempotent (isUnit_card_zmodUnits_padicUnitsDepth hp)]

end OddPrime

section Dyadic

/-- `(ℤ/4ℤ)ˣ` is a `2`-group of order `2`. -/
theorem isPGroup_zmodFourUnits : IsPGroup 2 (ZMod 4)ˣ :=
  IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_eq_fintype_card]; decide⟩

/-- **At `p = 2`, the finite group ring `ℤ_2[(ℤ/4ℤ)ˣ]` is a local ring.** -/
instance isLocalRing_monoidAlgebra_zmodFourUnits : IsLocalRing (MonoidAlgebra ℤ_[2] (ZMod 4)ˣ) :=
  TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup PadicInt.p_nonunit isPGroup_zmodFourUnits

/-- The maximal ideal of `ℤ_2[(ℤ/4ℤ)ˣ]` is generated by `2` and `[-1] - 1`. -/
theorem maximalIdeal_monoidAlgebra_zmodFourUnits :
    IsLocalRing.maximalIdeal (MonoidAlgebra ℤ_[2] (ZMod 4)ˣ) =
      Ideal.span {(2 : MonoidAlgebra ℤ_[2] (ZMod 4)ˣ),
        MonoidAlgebra.single (-1 : (ZMod 4)ˣ) 1 - 1} := by
  have hS : Ideal.span {(2 : ℤ_[2])} = IsLocalRing.maximalIdeal ℤ_[2] := by
    simpa only [Nat.cast_ofNat] using (PadicInt.maximalIdeal_eq_span_p (p := 2)).symm
  have hT : Subgroup.closure ({(-1 : (ZMod 4)ˣ)} : Set (ZMod 4)ˣ) = ⊤ := by
    have hall : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1 := by decide
    refine eq_top_iff.mpr fun u _ ↦ ?_
    rcases hall u with rfl | rfl
    exacts [Subgroup.one_mem _, Subgroup.subset_closure rfl]
  simpa only [Set.image_singleton, Set.singleton_union, map_ofNat] using
    TauCeti.MonoidAlgebra.maximalIdeal_eq_span_of_closure_eq_top hS hT

/-- The maximal ideal of `(ℤ_2[(ℤ/4ℤ)ˣ])⟦X⟧` is generated by `X`, `2`, and `[-1] - 1`. -/
theorem maximalIdeal_powerSeries_monoidAlgebra_zmodFourUnits :
    IsLocalRing.maximalIdeal (PowerSeries (MonoidAlgebra ℤ_[2] (ZMod 4)ˣ)) =
      Ideal.span {PowerSeries.X, (2 : PowerSeries (MonoidAlgebra ℤ_[2] (ZMod 4)ˣ)),
        PowerSeries.C (MonoidAlgebra.single (-1 : (ZMod 4)ˣ) 1 - 1)} := by
  simpa only [Set.image_pair, map_ofNat] using
    TauCeti.PowerSeries.maximalIdeal_eq_span_insert_X maximalIdeal_monoidAlgebra_zmodFourUnits.symm

/-- **At `p = 2`, the completed group algebra `ℤ_2[[ℤ_2ˣ]]` is a local ring.** -/
instance isLocalRing_completedGroupAlgebra_dyadicUnits :
    IsLocalRing (completedGroupAlgebra ℤ_[2] ℤ_[2]ˣ) := by
  have : IsLocalRing (MonoidAlgebra ℤ_[2] (ZMod (2 ^ padicUnitsDepth 2))ˣ) := by
    rw [padicUnitsDepth_two]; exact isLocalRing_monoidAlgebra_zmodFourUnits
  exact (padicUnitsCoordinate 2).toRingEquiv.isLocalRing

/-- Because `ℤ_2[[ℤ_2ˣ]]` is local, its only idempotents are `0` and `1`. -/
theorem isIdempotentElem_completedGroupAlgebra_dyadicUnits_iff
    {e : completedGroupAlgebra ℤ_[2] ℤ_[2]ˣ} :
    IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  refine ⟨fun he ↦ ?_, by rintro (rfl | rfl) <;> simp [IsIdempotentElem]⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · exact Or.inr (sub_eq_zero.mp (hu.mul_right_eq_zero.mp he.mul_one_sub_self)).symm
  · exact Or.inl (hu.mul_right_eq_zero.mp he.one_sub_mul_self)

/-- After inverting `2`, `ℚ_2[(ℤ/4ℤ)ˣ]` splits along the two `ℚ_2ˣ`-valued characters of
`(ℤ/4ℤ)ˣ`. -/
noncomputable def dyadicRationalFiniteGroupRingEquiv :
    MonoidAlgebra ℚ_[2] (ZMod 4)ˣ ≃ₐ[ℚ_[2]] (((ZMod 4)ˣ →* ℚ_[2]ˣ) → ℚ_[2]) := by
  have hcard : Nat.card (ZMod 4)ˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
  have h2 : HasEnoughRootsOfUnity ℚ_[2] 2 := by
    let f : Bool → rootsOfUnity 2 ℚ_[2] := fun b ↦
      if b then ⟨1, by simp⟩ else ⟨-1, by rw [mem_rootsOfUnity]; ext; norm_num⟩
    have hf : Function.Injective f := by
      rintro (_ | _) (_ | _) h <;> first | rfl |
        exact absurd (congrArg (fun u : rootsOfUnity 2 ℚ_[2] ↦ ((u : ℚ_[2]ˣ) : ℚ_[2])) h)
          (by norm_num [f])
    exact HasEnoughRootsOfUnity.of_card_le (by simpa using Nat.card_le_card_of_injective f hf)
  have : HasEnoughRootsOfUnity ℚ_[2] (Monoid.exponent (ZMod 4)ˣ) :=
    HasEnoughRootsOfUnity.of_dvd ℚ_[2] (hcard ▸ Group.exponent_dvd_nat_card)
  exact MonoidAlgebra.charEvalEquiv
    (by rw [hcard, Nat.cast_ofNat]; exact isUnit_iff_ne_zero.mpr (by norm_num))

end Dyadic

end TauCeti
