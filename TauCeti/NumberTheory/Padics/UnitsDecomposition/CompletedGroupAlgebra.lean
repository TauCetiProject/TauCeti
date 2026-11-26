/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.CoordinateTopology
import TauCeti.Algebra.MonoidAlgebra.LocalRing
import TauCeti.Data.ZMod.PrincipalUnits

/-!
# The completed group algebra `ℤ_p[[ℤ_pˣ]]` as `ℤ_p[Δ]⟦T⟧`

Put `q = p` for odd `p` and `q = 4` for `p = 2` (`q = p ^ TauCeti.padicUnitsDepth p`),
`Δ = (ℤ/qℤ)ˣ` and `γ = exp q` (`TauCeti.padicUnitsGenerator p`). The decomposition
`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* Δ × ℤ_p`,
`x ↦ (r(x), s(x))` with `r(x) = x mod q` and `s(x) = log (x / ω(r(x))) / q`, where `ω` is the
multiplicative section `TauCeti.padicUnitsSection p` of reduction modulo `q`, turns the
power-series coordinate of `ℤ_p[[Δ × ℤ_p]]` into an isomorphism of `ℤ_p`-algebras

```text
ℤ_p[Δ]⟦T⟧ ≃ₐ[ℤ_p] Λ = ℤ_p[[ℤ_pˣ]],   T ↦ [γ] - 1,   δ ↦ [ω(δ)],
```

`TauCeti.completedGroupAlgebra.padicUnitsCoordinate p`. Through it the group element `[x]` of a
unit `x` is the product of the group element `r(x)` of `ℤ_p[Δ]` with the binomial series
`(1 + T) ^ s(x)`:

```text
[x] = [r(x)] (1 + T) ^ (log (x / ω(r(x))) / q)
```

(`TauCeti.completedGroupAlgebra.padicUnitsCoordinate_symm_of`). In particular `[γ] = 1 + T`, and
more generally `[exp (q u)] = (1 + T) ^ u` for `u ∈ ℤ_p`. The coordinate is a homeomorphism for the
coefficientwise topology on `ℤ_p[Δ]⟦T⟧` and the inverse-limit topology on `Λ`.

Measures on `ℤ_pˣ` are elements of `Λ` through `AbstractMeasure.completedGroupAlgebraEquiv`, so the
coordinate writes them as power series in `T` over the group ring of the finite part `Δ`. The
identification depends on the chosen generator `γ`. At `p = 2` the factor `Δ = {±1}` cannot be
absorbed into the series variable, since `-1` has order two, and the coefficient ring `ℤ_2[Δ]` is
local; at odd `p` the order `p - 1` of `Δ` is prime to `p` and `ℤ_p[Δ]` is not local. So `Λ` is a
local ring exactly when `p = 2`.

## Main definitions

* `TauCeti.completedGroupAlgebra.padicUnitsCoordinate p`: the isomorphism
  `ℤ_p[Δ]⟦T⟧ ≃ₐ[ℤ_p] ℤ_p[[ℤ_pˣ]]`.

## Main results

* `TauCeti.completedGroupAlgebra.padicUnitsCoordinate_X`,
  `TauCeti.completedGroupAlgebra.padicUnitsCoordinate_C_single`: `T ↦ [γ] - 1` and
  `a δ ↦ a [ω(δ)]`.
* `TauCeti.completedGroupAlgebra.padicUnitsCoordinate_map_binomialSeries`: the binomial series
  `(1 + T) ^ u` goes to the group element `exp (q u)`.
* `TauCeti.completedGroupAlgebra.padicUnitsCoordinate_symm_of`: `[x] = [r(x)] (1 + T) ^ s(x)`.
* `TauCeti.completedGroupAlgebra.continuous_padicUnitsCoordinate`,
  `TauCeti.completedGroupAlgebra.continuous_padicUnitsCoordinate_symm`: the coordinate is a
  homeomorphism.
* `TauCeti.completedGroupAlgebra.isLocalRing_monoidAlgebra_units_zmod_iff`,
  `TauCeti.completedGroupAlgebra.isLocalRing_completedGroupAlgebra_padicIntUnits_iff`: `ℤ_p[Δ]`
  and `ℤ_p[[ℤ_pˣ]]` are local rings exactly when `p = 2`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), Notation 2.1, with `q = 4` at `p = 2` as in §1.14.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3 and
  Remark 3.47, for odd `p`.
-/

public section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.completedGroupAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- **The completed group algebra of `ℤ_pˣ` as a power-series ring.** With `q = p` for odd `p`,
`q = 4` for `p = 2`, `Δ = (ℤ/qℤ)ˣ` and `γ = exp q`, the completed group algebra `ℤ_p[[ℤ_pˣ]]` is the
power-series ring over the group ring `ℤ_p[Δ]`, with `T ↦ [γ] - 1` and the group element `δ` of
`Δ` going to `[ω(δ)]`, for the section `ω = TauCeti.padicUnitsSection p` of reduction modulo `q`.
It is the power-series coordinate of `ℤ_p[[Δ × ℤ_p]]` transported along the decomposition
`TauCeti.padicIntUnitsEquivZModUnitsProd p`. -/
noncomputable def padicUnitsCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ≃ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ :=
  (prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p)).trans
      (domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm)

/-- The coordinate of `ℤ_p[[ℤ_pˣ]]` transports the product coordinate of `ℤ_p[[Δ × ℤ_p]]` along
the decomposition `ℤ_pˣ ≃ₜ* Δ × ℤ_p`. -/
theorem padicUnitsCoordinate_def :
    padicUnitsCoordinate p =
      (prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
        (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_one_padicInt p)).trans
        (domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p).symm) :=
  (rfl)

/-- The coordinate sends `T` to `[γ] - 1`, for the generator `γ = exp q`. -/
@[simp]
theorem padicUnitsCoordinate_X :
    padicUnitsCoordinate p X = of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1 := by
  rw [padicUnitsCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_X, map_sub,
    map_one (domCongr ℤ_[p] _), domCongr_of, ← padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator,
    ContinuousMulEquiv.symm_apply_apply]

/-- The coordinate sends `1 + T` to the group element `γ = exp q`. -/
@[simp]
theorem padicUnitsCoordinate_one_add_X :
    padicUnitsCoordinate p (1 + X) = of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) := by
  rw [map_add, map_one, padicUnitsCoordinate_X, add_sub_cancel]

/-- The coordinate sends the constant `a · δ` of the group ring `ℤ_p[Δ]` to `a` times the group
element `ω(δ)`. -/
@[simp]
theorem padicUnitsCoordinate_C_single (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    padicUnitsCoordinate p (C (MonoidAlgebra.single δ a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a *
        of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_C_single, map_mul,
    AlgEquiv.commutes, domCongr_of, ← padicIntUnitsEquivZModUnitsProd_padicUnitsSection,
    ContinuousMulEquiv.symm_apply_apply]

/-- The coordinate sends the group element `δ` of `ℤ_p[Δ]` to the group element `ω(δ)`. -/
theorem padicUnitsCoordinate_C_single_one (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsCoordinate p (C (MonoidAlgebra.single δ 1)) =
      of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [padicUnitsCoordinate_C_single, map_one, one_mul]

/-- **Group elements in the coordinate.** The product of the group element `δ` of `ℤ_p[Δ]` with
the binomial series `(1 + T) ^ u` goes to the group element `ω(δ) exp (q u)`. -/
theorem padicUnitsCoordinate_C_single_mul_map_binomialSeries
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (u : ℤ_[p]) :
    padicUnitsCoordinate p (C (MonoidAlgebra.single δ 1) *
        PowerSeries.map MonoidAlgebra.singleOneRingHom (binomialSeries ℤ_[p] u)) =
      of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ * (unitsPrincipalLogEquiv p).symm (.ofAdd u)) := by
  rw [padicUnitsCoordinate, AlgEquiv.trans_apply,
    prodPowerSeriesCoordinate_C_single_mul_map_binomialSeries, IsProP.padicPow_ofAdd_one_padicInt,
    domCongr_of, padicIntUnitsEquivZModUnitsProd_symm_apply]

/-- **`p`-adic powers of the generator.** The binomial series `(1 + T) ^ u`, with coefficients in
`ℤ_p`, goes to the group element `γ ^ u = exp (q u)`. -/
@[simp]
theorem padicUnitsCoordinate_map_binomialSeries (u : ℤ_[p]) :
    padicUnitsCoordinate p
        (PowerSeries.map MonoidAlgebra.singleOneRingHom (binomialSeries ℤ_[p] u)) =
      of ℤ_[p] ℤ_[p]ˣ ((unitsPrincipalLogEquiv p).symm (.ofAdd u)) := by
  -- This is the case `δ = 1`, where the group element `1` of `ℤ_p[Δ]` is the unit.
  have h := padicUnitsCoordinate_C_single_mul_map_binomialSeries p 1 u
  simp only [← MonoidAlgebra.one_def, map_one, one_mul] at h
  exact h

/-- **The group element of a unit in the coordinate.** For `x ∈ ℤ_pˣ` with residue
`r(x) = x mod q` and `s(x) = log (x / ω(r(x))) / q`, the group element `[x]` is the group element
`r(x)` of `ℤ_p[Δ]` times the binomial series `(1 + T) ^ s(x)`: `[x] = [r(x)] (1 + T) ^ s(x)`. -/
theorem padicUnitsCoordinate_symm_of (x : ℤ_[p]ˣ) :
    (padicUnitsCoordinate p).symm (of ℤ_[p] ℤ_[p]ˣ x) =
      C (MonoidAlgebra.single (PadicInt.unitsToZModPow (padicUnitsDepth p) x) 1) *
        PowerSeries.map MonoidAlgebra.singleOneRingHom
          (binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd) := by
  refine (padicUnitsCoordinate p).symm_apply_eq.mpr ?_
  rw [padicUnitsCoordinate_C_single_mul_map_binomialSeries, ofAdd_toAdd,
    ← padicIntUnitsEquivZModUnitsProd_apply_fst, ← padicIntUnitsEquivZModUnitsProd_symm_apply,
    ContinuousMulEquiv.symm_apply_apply]

/-- The inverse coordinate sends the generator `γ = exp q` to `1 + T`. -/
@[simp]
theorem padicUnitsCoordinate_symm_of_padicUnitsGenerator :
    (padicUnitsCoordinate p).symm (of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) = 1 + X :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_one_add_X p).symm

/-- The inverse coordinate sends `ω(δ)` to the group element `δ` of `ℤ_p[Δ]`. -/
@[simp]
theorem padicUnitsCoordinate_symm_of_padicUnitsSection (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    (padicUnitsCoordinate p).symm (of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) =
      C (MonoidAlgebra.single δ 1) :=
  (padicUnitsCoordinate p).symm_apply_eq.mpr (padicUnitsCoordinate_C_single_one p δ).symm

section IsLocalRing

/-- **The coefficient ring `ℤ_p[Δ]` is local exactly for `p = 2`.** At `p = 2` the group
`Δ = (ℤ/4ℤ)ˣ = {±1}` is a `2`-group, so `ℤ_2[Δ]` is local; at odd `p` the group `Δ = (ℤ/pℤ)ˣ`
has order `p - 1` prime to `p`, and `ℤ_p[Δ]` is not local. -/
theorem isLocalRing_monoidAlgebra_units_zmod_iff :
    IsLocalRing (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) ↔ p = 2 := by
  rw [TauCeti.MonoidAlgebra.isLocalRing_iff_isPGroup (mem_nonunits_iff.mp PadicInt.p_nonunit),
    ZMod.isPGroup_units_prime_pow_iff (padicUnitsDepth_pos p).ne']

/-- **`ℤ_p[[ℤ_pˣ]]` is local exactly for `p = 2`.** Through the coordinate it is the power-series
ring over `ℤ_p[Δ]`, which is local exactly when `ℤ_p[Δ]` is
(`isLocalRing_monoidAlgebra_units_zmod_iff`). -/
theorem isLocalRing_completedGroupAlgebra_padicIntUnits_iff :
    IsLocalRing (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) ↔ p = 2 := by
  rw [← isLocalRing_monoidAlgebra_units_zmod_iff]
  set e := padicUnitsCoordinate p
  constructor
  · intro
    -- The constant coefficient of the series coordinate maps `Λ` onto `ℤ_p[Δ]`.
    exact IsLocalRing.of_surjective' ((constantCoeff (R := MonoidAlgebra ℤ_[p] _)).comp
      e.symm.toRingEquiv.toRingHom)
      fun a ↦ ⟨e (C a), by simp⟩
  · intro
    have : IsLocalRing (PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :=
      inferInstanceAs (IsLocalRing (MvPowerSeries Unit _))
    exact IsLocalRing.of_surjective' e.toRingEquiv.toRingHom e.surjective

end IsLocalRing

section Topology

variable [TopologicalSpace (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]
  [IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)]

/-- The coordinate is continuous for the module topology on `ℤ_p[Δ]`, the coefficientwise topology
on `ℤ_p[Δ]⟦T⟧` and the inverse-limit topology on `ℤ_p[[ℤ_pˣ]]`. -/
theorem continuous_padicUnitsCoordinate : Continuous (padicUnitsCoordinate p) := by
  rw [padicUnitsCoordinate_def, AlgEquiv.coe_trans, coe_domCongr]
  exact (continuous_map ℤ_[p] _ (map_continuous (padicIntUnitsEquivZModUnitsProd p).symm)).comp
    (continuous_prodPowerSeriesCoordinate _ _ _)

/-- The inverse coordinate is continuous, so the coordinate is a homeomorphism. -/
theorem continuous_padicUnitsCoordinate_symm : Continuous (padicUnitsCoordinate p).symm := by
  have h : ⇑(padicUnitsCoordinate p).symm =
      (prodPowerSeriesCoordinate (ZMod (p ^ padicUnitsDepth p))ˣ
        (isProP_multiplicative_padicInt p) (topologicallyGenerates_ofAdd_one_padicInt p)).symm ∘
        domCongr ℤ_[p] (padicIntUnitsEquivZModUnitsProd p) :=
    funext fun x ↦ by rw [padicUnitsCoordinate_def, AlgEquiv.symm_trans_apply, domCongr_symm,
      ContinuousMulEquiv.symm_symm, Function.comp_apply]
  rw [h, coe_domCongr]
  exact (continuous_prodPowerSeriesCoordinate_symm _ _ _).comp
    (continuous_map ℤ_[p] _ (map_continuous (padicIntUnitsEquivZModUnitsProd p)))

end Topology

end TauCeti.completedGroupAlgebra
