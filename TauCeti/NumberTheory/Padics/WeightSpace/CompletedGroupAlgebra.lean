/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
Presenting `ℤ_p[[ℤ_pˣ]]` in power-series weight coordinates reduces continuous specialisation on
`WeightSpace` to power-series evaluation at `X = [γ] - 1` and contrasts odd-prime integral branch
splittings with the local dyadic algebra.

Transporting `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate` along
`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* Δ × ℤ_p` gives the `ℤ_p`-algebra equivalence
`TauCeti.padicUnitsCoordinate p : (ℤ_[p][Δ])⟦X⟧ ≃ₐ[ℤ_[p]] ℤ_[p][[ℤ_[p]ˣ]]`, sending `X ↦ [γ] - 1`
and `[δ] ↦ [ω(δ)]`, with inverse `[x] ↦ [x mod q] · (1 + X) ^ (log(x / ω(x mod q)) / q)`. It
becomes a homeomorphism via `TauCeti.continuous_padicUnitsCoordinate` and
`TauCeti.continuous_padicUnitsCoordinate_symm` when `ℤ_p[Δ]` carries `IsModuleTopology ℤ_[p]` and
`(ℤ_p[Δ])⟦X⟧` carries `PowerSeries.WithPiTopology`. Replacing `γ` by `γ ^ u = exp(q u)`
(`u ∈ ℤ_pˣ`) gives `TauCeti.padicUnitsCoordinateAt p u`, related by `X ↦ (1 + X) ^ u - 1`.

* When `p ≠ 2`, `#Δ = p - 1` is a unit in `ℤ_p`, splitting `ℤ_p[Δ]` and `ℤ_p[[ℤ_pˣ]]` integrally
  along characters (`TauCeti.padicUnitsCompletedGroupAlgebraSplitting`, a homeomorphism for the
  coefficientwise product topology on branches).
* When `p = 2`, `ℤ_2[(ℤ/4ℤ)ˣ]` and `ℤ_2[[ℤ_2ˣ]]` are local
  (`TauCeti.isLocalRing_completedGroupAlgebra_dyadicUnits`, so `ℤ_2[[ℤ_2ˣ]]` has no nontrivial
  idempotents) with maximal ideals `(2, [-1] - 1)` and `(X, 2, [-1] - 1)` in power-series
  coordinates, while `ℚ_2[(ℤ/4ℤ)ˣ]` splits rationally
  (`TauCeti.dyadicRationalFiniteGroupRingEquiv`).

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

/-- **The weight power-series coordinate at a changed generator `γ ^ u = exp(q u)`.** For
`u ∈ ℤ_pˣ`, this sends `X` to `[exp(q u)] - 1` while keeping `[δ] ↦ [ω(δ)]` on `Δ`. -/
noncomputable def padicUnitsCoordinateAt (u : ℤ_[p]ˣ) :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ :=
  (completedGroupAlgebra.prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
    (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_unit_padicInt p u)).trans
    (completedGroupAlgebra.domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm)

@[simp] theorem padicUnitsCoordinateAt_X (u : ℤ_[p]ˣ) :
    padicUnitsCoordinateAt p u PowerSeries.X = completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ
      ((unitsPrincipalLogEquiv p).symm (.ofAdd (u : ℤ_[p]))) - 1 := by
  simp [padicUnitsCoordinateAt]
@[simp] theorem padicUnitsCoordinateAt_C_single (u : ℤ_[p]ˣ) (δ : (ZMod (p ^ padicUnitsDepth p))ˣ)
    (a : ℤ_[p]) :
    padicUnitsCoordinateAt p u (PowerSeries.C (MonoidAlgebra.single δ a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a *
        completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  simp [padicUnitsCoordinateAt]

/-- **The weight power-series coordinate of `ℤ_p[[ℤ_pˣ]]`.** Writing `q = p ^ padicUnitsDepth p`
and `Δ = (ℤ/qℤ)ˣ`, `ℤ_pˣ ≃ₜ* Δ × ℤ_p` identifies `ℤ_p[[ℤ_pˣ]]` with `(ℤ_p[Δ])⟦X⟧`, sending `X` to
`[γ] - 1` (`γ = exp q`) and `[δ]` to `[ω(δ)]`. -/
noncomputable def padicUnitsCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ :=
  padicUnitsCoordinateAt p 1

@[simp] theorem padicUnitsCoordinateAt_one :
    padicUnitsCoordinateAt p 1 = padicUnitsCoordinate p := (rfl)
@[simp] theorem padicUnitsCoordinate_X :
    padicUnitsCoordinate p PowerSeries.X =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1 := by
  rw [← padicUnitsCoordinateAt_one, padicUnitsCoordinateAt_X, Units.val_one,
    ← unitsPrincipalLogEquiv_padicUnitsGenerator, ContinuousMulEquiv.symm_apply_apply]
@[simp] theorem padicUnitsCoordinate_one_add_X :
    padicUnitsCoordinate p (1 + PowerSeries.X) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) := by
  rw [map_add, map_one, padicUnitsCoordinate_X, add_sub_cancel]
@[simp] theorem padicUnitsCoordinate_C_single (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a *
        completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) :=
  padicUnitsCoordinateAt_C_single p 1 δ a
theorem padicUnitsCoordinate_C_single_one (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ 1)) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinate_C_single, map_one, one_mul]

/-- `padicUnitsCoordinate` sends the binomial series `(1 + X) ^ s` to `[exp(q s)]`. -/
@[simp] theorem padicUnitsCoordinate_binomialSeries (s : ℤ_[p]) :
    padicUnitsCoordinate p
        (PowerSeries.binomialSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) s) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ ((unitsPrincipalLogEquiv p).symm (.ofAdd s)) := by
  simp [padicUnitsCoordinate, padicUnitsCoordinateAt, IsProP.padicPow_ofAdd_one_padicInt,
    completedGroupAlgebra.domCongr_of]

/-- **Expansion of group elements in weight coordinates.** The inverse of `padicUnitsCoordinate`
sends `[x]` (`x ∈ ℤ_pˣ`) to `[x mod q] · (1 + X) ^ (log (x / ω(x mod q)) / q)`. -/
theorem padicUnitsCoordinate_symm_of (x : ℤ_[p]ˣ) :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      PowerSeries.C (MonoidAlgebra.single (padicIntUnitsEquivZModUnitsProd p x).1 1) *
        PowerSeries.binomialSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)
          (padicIntUnitsEquivZModUnitsProd p x).2.toAdd := by
  apply (padicUnitsCoordinate p).injective
  simp only [AlgEquiv.apply_symm_apply, map_mul, padicUnitsCoordinate_C_single_one,
    padicUnitsCoordinate_binomialSeries, ofAdd_toAdd]
  rw [← map_mul, ← padicIntUnitsEquivZModUnitsProd_symm_apply,
    ContinuousMulEquiv.symm_apply_apply]
@[simp] theorem padicUnitsCoordinate_symm_of_padicUnitsSection
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) =
      PowerSeries.C (MonoidAlgebra.single δ 1) :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_C_single_one p δ).symm
@[simp] theorem padicUnitsCoordinate_symm_of_padicUnitsGenerator :
    (padicUnitsCoordinate p).symm (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) =
      1 + PowerSeries.X :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_one_add_X p).symm

section GeneratorChange

/-- **Change of principal generator in `ℤ_p[[ℤ_pˣ]]`.** Replacing `γ` by `γ ^ u = exp(q u)` changes
the power-series coordinate by the substitution `X ↦ (1 + X) ^ u - 1`. -/
theorem padicUnitsCoordinateAt_apply (u : ℤ_[p]ˣ)
    (ψ : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    padicUnitsCoordinateAt p u ψ = padicUnitsCoordinate p
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
  have hσX : σ PowerSeries.X = g := by
    simp [σ, g, R, AlgEquiv.symm_apply_eq, padicUnitsCoordinate_binomialSeries]
  have hg : PowerSeries.HasSubst (σ PowerSeries.X) :=
    hσX ▸ PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [g])
  have hsub := congr($(PowerSeries.algHom_eq_substAlgHom (σ := σ) hg) ψ)
  rw [PowerSeries.coe_substAlgHom, hσX] at hsub
  exact (padicUnitsCoordinate p).symm_apply_eq.mp hsub

end GeneratorChange

section Topology

variable [TopologicalSpace (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]
  [IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]

/-- `padicUnitsCoordinateAt p u` and its inverse are continuous (a homeomorphism for the module
topology on `ℤ_p[Δ]`, coefficientwise topology on `(ℤ_p[Δ])⟦X⟧`, and inverse-limit topology). -/
theorem continuous_padicUnitsCoordinateAt (u : ℤ_[p]ˣ) :
    Continuous (padicUnitsCoordinateAt p u) := by
  rw [padicUnitsCoordinateAt, AlgEquiv.coe_trans, completedGroupAlgebra.coe_domCongr]
  exact (completedGroupAlgebra.continuous_map ℤ_[p]
    (padicIntUnitsEquivZModUnitsProd p).symm.toMonoidHom
    (padicIntUnitsEquivZModUnitsProd p).symm.continuous).comp
    (completedGroupAlgebra.continuous_prodPowerSeriesCoordinate _
      (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_unit_padicInt p u))
theorem continuous_padicUnitsCoordinateAt_symm (u : ℤ_[p]ˣ) :
    Continuous (padicUnitsCoordinateAt p u).symm :=
  ((completedGroupAlgebra.continuous_prodPowerSeriesCoordinate_symm _
    (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_unit_padicInt p u)).comp
    (completedGroupAlgebra.continuous_map ℤ_[p] (padicIntUnitsEquivZModUnitsProd p : ℤ_[p]ˣ →* _)
      (padicIntUnitsEquivZModUnitsProd p).continuous)).congr fun _ ↦ by
    simp [padicUnitsCoordinateAt, completedGroupAlgebra.domCongr_symm,
      completedGroupAlgebra.coe_domCongr]
theorem continuous_padicUnitsCoordinate : Continuous (padicUnitsCoordinate p) :=
  continuous_padicUnitsCoordinateAt p 1
theorem continuous_padicUnitsCoordinate_symm : Continuous (padicUnitsCoordinate p).symm :=
  continuous_padicUnitsCoordinateAt_symm p 1

end Topology

end Coordinate

namespace PadicUnitsModuleTopology

/-- Scoped `ℤ_p`-module topology on `ℤ_p[(ℤ/qℤ)ˣ]`. -/
noncomputable scoped instance instTopologicalSpaceMonoidAlgebraZModUnits (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) :=
  moduleTopology ℤ_[p] _

/-- Under the scoped topology `TauCeti.PadicUnitsModuleTopology`, `ℤ_p[(ℤ/qℤ)ˣ]` carries the
`ℤ_p`-module topology. -/
scoped instance instIsModuleTopologyMonoidAlgebraZModUnits (p : ℕ) [Fact p.Prime] :
    IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) := ⟨rfl⟩

end PadicUnitsModuleTopology

section OddPrime

variable {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
include hp

/-- **Integral character splitting of `ℤ_p[(ℤ/pℤ)ˣ]` for odd `p`.** -/
noncomputable def padicUnitsFiniteGroupRingEquiv :
    MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → ℤ_[p]) :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  charEvalEquiv (isUnit_card_zmodUnits_padicUnitsDepth hp)

@[simp] theorem padicUnitsFiniteGroupRingEquiv_apply
    (x : MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)
    (ψ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsFiniteGroupRingEquiv hp x ψ = ψ.charEval x :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  charEvalEquiv_apply (isUnit_card_zmodUnits_padicUnitsDepth hp) x ψ
@[simp] theorem padicUnitsFiniteGroupRingEquiv_charIdempotent
    [DecidableEq ((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ)]
    (χ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsFiniteGroupRingEquiv hp (charIdempotent χ) = Pi.single χ 1 :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  charEvalEquiv_charIdempotent (isUnit_card_zmodUnits_padicUnitsDepth hp) χ

/-- **Integral character splitting of `(ℤ_p[(ℤ/pℤ)ˣ])⟦X⟧` for odd `p`.** -/
noncomputable def padicUnitsPowerSeriesSplitting :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → PowerSeries ℤ_[p]) :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  powerSeriesCharEvalEquiv (isUnit_card_zmodUnits_padicUnitsDepth hp)

@[simp] theorem padicUnitsPowerSeriesSplitting_apply
    (φ : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ))
    (ψ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsPowerSeriesSplitting hp φ ψ = PowerSeries.map ψ.charEval.toRingHom φ :=
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  powerSeriesCharEvalEquiv_apply (isUnit_card_zmodUnits_padicUnitsDepth hp) φ ψ

/-- **Integral splitting of `ℤ_p[[ℤ_pˣ]]` into character branches for odd `p`.** -/
noncomputable def padicUnitsCompletedGroupAlgebraSplitting :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ ≃ₐ[ℤ_[p]]
      (((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) → PowerSeries ℤ_[p]) :=
  (padicUnitsCoordinate p).symm.trans (padicUnitsPowerSeriesSplitting hp)

theorem padicUnitsCompletedGroupAlgebraSplitting_def :
    padicUnitsCompletedGroupAlgebraSplitting hp =
      (padicUnitsCoordinate p).symm.trans (padicUnitsPowerSeriesSplitting hp) := (rfl)
@[simp] theorem padicUnitsCompletedGroupAlgebraSplitting_padicUnitsCoordinate
    (φ : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    padicUnitsCompletedGroupAlgebraSplitting hp (padicUnitsCoordinate p φ) =
      padicUnitsPowerSeriesSplitting hp φ := by
  rw [padicUnitsCompletedGroupAlgebraSplitting, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
@[simp] theorem padicUnitsCompletedGroupAlgebraSplitting_of_padicUnitsGenerator :
    padicUnitsCompletedGroupAlgebraSplitting hp
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) =
      fun _ ↦ 1 + PowerSeries.X := by ext; simp [padicUnitsCompletedGroupAlgebraSplitting]
@[simp] theorem padicUnitsCompletedGroupAlgebraSplitting_of_padicUnitsSection
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsCompletedGroupAlgebraSplitting hp
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) =
      fun ψ ↦ PowerSeries.C (ψ δ : ℤ_[p]) := by ext; simp [padicUnitsCompletedGroupAlgebraSplitting]
theorem padicUnitsCompletedGroupAlgebraSplitting_padicUnitsCoordinate_C_charIdempotent
    [DecidableEq ((ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ)]
    (χ : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ) :
    padicUnitsCompletedGroupAlgebraSplitting hp
      (padicUnitsCoordinate p (PowerSeries.C (charIdempotent χ))) = Pi.single χ 1 := by
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  ext ψ n
  simp [padicUnitsCompletedGroupAlgebraSplitting, Pi.single_apply, eq_comm,
    MonoidHom.charEval_charIdempotent _ _ (isUnit_card_zmodUnits_padicUnitsDepth hp)]

section
open scoped PadicUnitsModuleTopology

/-- The odd-prime splitting `padicUnitsCompletedGroupAlgebraSplitting` is continuous. -/
theorem continuous_padicUnitsCompletedGroupAlgebraSplitting :
    Continuous (padicUnitsCompletedGroupAlgebraSplitting hp) := by
  refine continuous_pi fun ψ ↦
    ((continuous_iff_continuousAt.mpr fun φ ↦
      (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ_[p] _ _ _).mpr fun n ↦ by
        simpa only [PowerSeries.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ContinuousAt,
          Function.comp_def, AlgHom.coe_toLinearMap] using
            ((IsModuleTopology.continuous_of_linearMap ψ.charEval.toLinearMap).comp
              (PowerSeries.WithPiTopology.continuous_coeff _ n)).continuousAt).comp
      (continuous_padicUnitsCoordinate_symm p)).congr fun z ↦
        (padicUnitsPowerSeriesSplitting_apply hp _ ψ).symm

/-- The inverse of `padicUnitsCompletedGroupAlgebraSplitting` is continuous. -/
theorem continuous_padicUnitsCompletedGroupAlgebraSplitting_symm :
    Continuous (padicUnitsCompletedGroupAlgebraSplitting hp).symm := by
  let Δ := (ZMod (p ^ padicUnitsDepth p))ˣ
  have : ContinuousAdd (MonoidAlgebra ℤ_[p] Δ) := IsModuleTopology.toContinuousAdd ℤ_[p] _
  have : ContinuousSMul ℤ_[p] (MonoidAlgebra ℤ_[p] Δ) := IsModuleTopology.toContinuousSMul ℤ_[p] _
  have := hasEnoughRootsOfUnity_zmodUnits_padicUnitsDepth p
  let _ : Fintype (Δ →* ℤ_[p]ˣ) := Fintype.ofFinite _
  refine ((continuous_padicUnitsCoordinate p).comp
    (continuous_iff_continuousAt (f := (padicUnitsPowerSeriesSplitting hp).symm).mpr fun F ↦
      (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_)).congr
        fun F ↦ by simp [padicUnitsCompletedGroupAlgebraSplitting, AlgEquiv.symm_trans_apply]
  refine ((continuous_finsetSum (s := Finset.univ)
    (f := fun (χ : Δ →* ℤ_[p]ˣ) (G : (Δ →* ℤ_[p]ˣ) → ℤ_[p]⟦X⟧) ↦ (G χ).coeff n • charIdempotent χ)
    fun χ _ ↦ ((PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] n).comp
      (continuous_apply χ)).smul continuous_const).congr fun G ↦ ?_).continuousAt
  rw [padicUnitsPowerSeriesSplitting, coeff_powerSeriesCharEvalEquiv_symm, charEvalEquiv_symm_apply]

end

end OddPrime

section Dyadic

private theorem card_zmodFourUnits : Nat.card (ZMod 4)ˣ = 2 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- `(ℤ/4ℤ)ˣ` is a `2`-group of order `2`. -/
theorem isPGroup_zmodFourUnits : IsPGroup 2 (ZMod 4)ˣ :=
  IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, card_zmodFourUnits]⟩

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
  have hu : ∀ v : (ZMod 4)ˣ, v = 1 ∨ v = -1 := by decide
  have hT : Subgroup.closure ({(-1 : (ZMod 4)ˣ)} : Set (ZMod 4)ˣ) = ⊤ := eq_top_iff.mpr fun u _ ↦ by
    rcases hu u with rfl | rfl
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
    IsLocalRing (completedGroupAlgebra ℤ_[2] ℤ_[2]ˣ) :=
  have : IsLocalRing (MonoidAlgebra ℤ_[2] (ZMod (2 ^ padicUnitsDepth 2))ˣ) := by
    rw [padicUnitsDepth_two]; exact isLocalRing_monoidAlgebra_zmodFourUnits
  (padicUnitsCoordinate 2).toRingEquiv.isLocalRing

/-- `ℚ_2` contains enough roots of unity for `(ℤ/4ℤ)ˣ`, witnessed by `-1`. -/
theorem hasEnoughRootsOfUnity_zmodFourUnits_padic :
    HasEnoughRootsOfUnity ℚ_[2] (Monoid.exponent (ZMod 4)ˣ) :=
  have : HasEnoughRootsOfUnity ℚ_[2] 2 :=
    ⟨⟨-1, IsPrimitiveRoot.neg_one 0 two_ne_zero.symm⟩, inferInstance⟩
  HasEnoughRootsOfUnity.of_dvd ℚ_[2] (card_zmodFourUnits ▸ Group.exponent_dvd_nat_card)

private theorem isUnit_card_zmodFourUnits_padic : IsUnit (Nat.card (ZMod 4)ˣ : ℚ_[2]) := by
  rw [card_zmodFourUnits, Nat.cast_ofNat]; exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- After inverting `2`, `ℚ_2[(ℤ/4ℤ)ˣ]` splits along the two `ℚ_2ˣ`-valued characters of
`(ℤ/4ℤ)ˣ`. -/
noncomputable def dyadicRationalFiniteGroupRingEquiv :
    MonoidAlgebra ℚ_[2] (ZMod 4)ˣ ≃ₐ[ℚ_[2]] (((ZMod 4)ˣ →* ℚ_[2]ˣ) → ℚ_[2]) :=
  have := hasEnoughRootsOfUnity_zmodFourUnits_padic; charEvalEquiv isUnit_card_zmodFourUnits_padic

@[simp] theorem dyadicRationalFiniteGroupRingEquiv_apply (x : MonoidAlgebra ℚ_[2] (ZMod 4)ˣ)
    (ψ : (ZMod 4)ˣ →* ℚ_[2]ˣ) : dyadicRationalFiniteGroupRingEquiv x ψ = ψ.charEval x :=
  have := hasEnoughRootsOfUnity_zmodFourUnits_padic
  charEvalEquiv_apply isUnit_card_zmodFourUnits_padic x ψ
@[simp] theorem dyadicRationalFiniteGroupRingEquiv_charIdempotent
    [DecidableEq ((ZMod 4)ˣ →* ℚ_[2]ˣ)] (χ : (ZMod 4)ˣ →* ℚ_[2]ˣ) :
    dyadicRationalFiniteGroupRingEquiv (charIdempotent χ) = Pi.single χ 1 :=
  have := hasEnoughRootsOfUnity_zmodFourUnits_padic
  charEvalEquiv_charIdempotent isUnit_card_zmodFourUnits_padic χ

end Dyadic

end TauCeti
