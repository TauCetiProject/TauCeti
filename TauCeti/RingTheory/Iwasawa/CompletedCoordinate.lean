/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.LevelCoordinate
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Tower

/-!
# The Iwasawa algebra `O⟦T⟧` as the completed group algebra `O[[ℤ_p]]`

Let `p` be a prime and let `O` be a local ring, complete for its maximal ideal `𝔪`, in which `p`
is not a unit (`hp : (p : O) ∈ 𝔪`); the integers of a finite extension of `ℚ_p` are the example to
keep in mind. The level coordinates `O⟦T⟧ → O[ℤ/pⁿ]`, `T ↦ [1] - 1`
(`TauCeti.Iwasawa.levelCoordinate`), are compatible with the reductions `ℤ/pⁿ → ℤ/pᵐ`, and the
congruence tower `ℤ_p → ℤ/pⁿ` is cofinal among the finite quotients of `ℤ_p`. So they assemble into
an `O`-algebra map into the completed group algebra of `ℤ_p` (written multiplicatively),

  `completedCoordinate hp : O⟦T⟧ →ₐ[O] O[[ℤ_p]]`,  `T ↦ γ - 1`,  `1 + T ↦ γ`,

where `γ` is the topological generator `1 ∈ ℤ_p`. Its projection onto `O[ℤ/pⁿ]` is the level
coordinate. Like the level coordinates, it is the only `O`-algebra map sending `T` to `γ - 1`, with
no continuity assumption: its projections to the finite levels are pinned down by the uniqueness
of the level coordinates.

Over a noetherian `O` it is an isomorphism, `completedCoordinateEquiv hp : O⟦T⟧ ≃ₐ[O] O[[ℤ_p]]`.
It is injective because the level coordinates separate points, `⋂ₙ (ω_n) = 0`, and surjective
because every compatible family of elements of the levels `O[ℤ/pⁿ]` comes from a series
(`TauCeti.Iwasawa.range_iwasawaCoordinate`). For `O = ℤ_p` it is the power-series coordinate
`TauCeti.completedGroupAlgebra.powerSeriesCoordinate` attached to `γ`, constructed there by
evaluating power series at the topologically nilpotent element `γ - 1`; the construction here
needs no topology on `O`. A change of generator `γ ↦ γ ^ u` is the substitution
`T ↦ (1 + T) ^ u - 1` (`TauCeti.completedGroupAlgebra.powerSeriesCoordinate_padicPow_apply`).

## Main definitions

* `TauCeti.Iwasawa.completedCoordinate hp`: the `O`-algebra map `O⟦T⟧ →ₐ[O] O[[ℤ_p]]` with
  `T ↦ γ - 1`.
* `TauCeti.Iwasawa.completedCoordinateEquiv hp`: over a noetherian `O`, the `O`-algebra
  isomorphism `O⟦T⟧ ≃ₐ[O] O[[ℤ_p]]`.

## Main results

* `TauCeti.Iwasawa.towerProj_of_ofAdd`: the projection onto `O[ℤ/pⁿ]` sends a group element
  `a ∈ ℤ_p` to its reduction modulo `pⁿ`.
* `TauCeti.Iwasawa.towerProj_completedCoordinate`: the projection onto `O[ℤ/pⁿ]` is the level
  coordinate.
* `TauCeti.Iwasawa.completedCoordinate_X`, `TauCeti.Iwasawa.completedCoordinate_one_add_X`,
  `TauCeti.Iwasawa.completedCoordinate_one_add_X_pow`: `T ↦ γ - 1`, `1 + T ↦ γ` and
  `(1 + T) ^ k ↦ γ ^ k`.
* `TauCeti.Iwasawa.completedCoordinate_unique`: an `O`-algebra map `O⟦T⟧ → O[[ℤ_p]]` sending `T`
  to `γ - 1` is the completed coordinate.
* `TauCeti.Iwasawa.completedCoordinate_injective`,
  `TauCeti.Iwasawa.completedCoordinate_surjective`: over a noetherian `O` the completed
  coordinate is bijective.
* `TauCeti.Iwasawa.completedCoordinate_eq_powerSeriesCoordinate`,
  `TauCeti.Iwasawa.completedCoordinateEquiv_eq_powerSeriesCoordinate`: over `ℤ_p` it is the
  power-series coordinate attached to `γ`, as a map and as an isomorphism.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Proposition
  (5.3.5), pp. 290–291.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Theorem 7.1.
-/

public section

open IsLocalRing PowerSeries

namespace TauCeti.Iwasawa

open completedGroupAlgebra (of towerProj)

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsLocalRing O]
  (hp : (p : O) ∈ maximalIdeal O) [IsAdicComplete (maximalIdeal O) O]

/-- **The Iwasawa coordinate on the completed group algebra of `ℤ_p`.** For a local ring `O`,
complete for its maximal ideal, in which `p` is not a unit, the `O`-algebra map
`O⟦T⟧ →ₐ[O] O[[ℤ_p]]` assembled from the level coordinates `O⟦T⟧ → O[ℤ/pⁿ]` along the congruence
tower of `ℤ_p`. It sends `T` to `γ - 1` for the topological generator `γ = 1` of `ℤ_p`
(`completedCoordinate_X`), and is the unique `O`-algebra map doing so
(`completedCoordinate_unique`). -/
noncomputable def completedCoordinate :
    O⟦X⟧ →ₐ[O] completedGroupAlgebra O (Multiplicative ℤ_[p]) :=
  completedGroupAlgebra.towerLift (FiniteQuotientTower.padicTower p) (levelCoordinate hp)
    fun _ _ h F ↦ by rw [← levelTransition_apply, levelTransition_levelCoordinate]

omit [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] in
/-- The projection of `O[[ℤ_p]]` onto `O[ℤ/pⁿ]` sends a group element `a ∈ ℤ_p` to its
reduction modulo `pⁿ`. This is the simp normal form, reached through
`completedGroupAlgebra.towerProj_of` and `FiniteQuotientTower.padicTower_q_ofAdd`. -/
theorem towerProj_of_ofAdd (n : ℕ) (a : ℤ_[p]) :
    towerProj O (FiniteQuotientTower.padicTower p) n
        (of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd a)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (PadicInt.toZModPow n a)) 1 := by
  rw [completedGroupAlgebra.towerProj_of, FiniteQuotientTower.padicTower_q_ofAdd]

/-- **The finite levels of the completed coordinate**: its projection onto `O[ℤ/pⁿ]` is the
level coordinate. -/
@[simp]
theorem towerProj_completedCoordinate (n : ℕ) (F : O⟦X⟧) :
    towerProj O (FiniteQuotientTower.padicTower p) n (completedCoordinate hp F) =
      levelCoordinate hp n F :=
  completedGroupAlgebra.towerProj_towerLift _ n F

/-- The completed coordinate sends `T` to `γ - 1`, for the topological generator `γ = 1` of
`ℤ_p`. -/
@[simp]
theorem completedCoordinate_X :
    completedCoordinate hp X = of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd 1) - 1 :=
  completedGroupAlgebra.ext_towerProj (T := FiniteQuotientTower.padicTower p) fun n ↦ by simp

/-- The completed coordinate sends `1 + T` to the topological generator `γ = [1]` of `ℤ_p`. -/
@[simp]
theorem completedCoordinate_one_add_X :
    completedCoordinate hp (1 + X) = of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd 1) := by
  rw [map_add, map_one, completedCoordinate_X, add_sub_cancel]

/-- The completed coordinate sends `(1 + T) ^ k` to the group element `γ ^ k = [k]`. -/
@[simp]
theorem completedCoordinate_one_add_X_pow (k : ℕ) :
    completedCoordinate hp ((1 + X) ^ k) =
      of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd (k : ℤ_[p])) := by
  rw [map_pow, completedCoordinate_one_add_X, ← map_pow, ← ofAdd_nsmul, nsmul_one]

/-- **Uniqueness of the completed coordinate.** An `O`-algebra map `O⟦T⟧ → O[[ℤ_p]]` sending `T`
to `γ - 1` is the completed coordinate; no continuity is assumed. -/
theorem completedCoordinate_unique
    {φ : O⟦X⟧ →ₐ[O] completedGroupAlgebra O (Multiplicative ℤ_[p])}
    (hφ : φ X = of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd 1) - 1) :
    φ = completedCoordinate hp := by
  refine completedGroupAlgebra.algHom_ext_towerProj (T := FiniteQuotientTower.padicTower p) fun n ↦
    (levelCoordinate_unique hp n ?_).trans (levelCoordinate_unique hp n ?_).symm
  all_goals rw [AlgHom.comp_apply, ← levelCoordinate_X hp n, ← towerProj_completedCoordinate]
  rw [hφ, completedCoordinate_X]

/-- Over a noetherian `O`, the completed coordinate is injective: the level coordinates separate
the points of `O⟦T⟧`. -/
theorem completedCoordinate_injective [IsNoetherianRing O] :
    Function.Injective (completedCoordinate hp) := fun F G h ↦
  iwasawaCoordinate_injective hp <| funext fun n ↦ by
    simpa using congrArg (towerProj O (FiniteQuotientTower.padicTower p) n) h

/-- Over a noetherian `O`, the completed coordinate is surjective: the projections of an element
of `O[[ℤ_p]]` to the levels `O[ℤ/pⁿ]` form a compatible family, which comes from a series. -/
theorem completedCoordinate_surjective [IsNoetherianRing O] :
    Function.Surjective (completedCoordinate hp) := fun x ↦ by
  obtain ⟨F, hF⟩ : ∃ F, iwasawaCoordinate hp F =
      fun n ↦ towerProj O (FiniteQuotientTower.padicTower p) n x := by
    rw [← AlgHom.mem_range, range_iwasawaCoordinate, mem_levelLimit]
    exact fun m n h ↦ by rw [levelTransition_apply, completedGroupAlgebra.mapDomain_t_towerProj]
  refine ⟨F, completedGroupAlgebra.ext_towerProj (T := FiniteQuotientTower.padicTower p) fun n ↦ ?_⟩
  rw [towerProj_completedCoordinate, ← iwasawaCoordinate_apply, hF]

/-- **The Iwasawa algebra is the completed group algebra of `ℤ_p`.** For a noetherian local ring
`O`, complete for its maximal ideal, in which `p` is not a unit, the `O`-algebra isomorphism
`O⟦T⟧ ≃ₐ[O] O[[ℤ_p]]` sending `T` to `γ - 1`, for the topological generator `γ = 1` of `ℤ_p`. -/
noncomputable def completedCoordinateEquiv [IsNoetherianRing O] :
    O⟦X⟧ ≃ₐ[O] completedGroupAlgebra O (Multiplicative ℤ_[p]) :=
  AlgEquiv.ofBijective (completedCoordinate hp)
    ⟨completedCoordinate_injective hp, completedCoordinate_surjective hp⟩

/-- The isomorphism `completedCoordinateEquiv hp` is the completed coordinate. -/
@[simp]
theorem coe_completedCoordinateEquiv [IsNoetherianRing O] :
    ⇑(completedCoordinateEquiv hp) = completedCoordinate hp :=
  AlgEquiv.coe_ofBijective _ _

/-- The inverse of the completed coordinate sends the group element `γ ^ k = [k]` to
`(1 + T) ^ k`. -/
@[simp]
theorem completedCoordinateEquiv_symm_of_ofAdd_natCast [IsNoetherianRing O] (k : ℕ) :
    (completedCoordinateEquiv hp).symm
        (of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd (k : ℤ_[p]))) = (1 + X) ^ k := by
  rw [AlgEquiv.symm_apply_eq, coe_completedCoordinateEquiv, completedCoordinate_one_add_X_pow]

/-- The inverse of the completed coordinate sends the topological generator `γ = [1]` to
`1 + T`. -/
@[simp]
theorem completedCoordinateEquiv_symm_of_ofAdd_one [IsNoetherianRing O] :
    (completedCoordinateEquiv hp).symm (of O (Multiplicative ℤ_[p]) (Multiplicative.ofAdd 1)) =
      1 + X := by
  rw [AlgEquiv.symm_apply_eq, coe_completedCoordinateEquiv, completedCoordinate_one_add_X]

/-- **Comparison with the power-series coordinate.** Over `O = ℤ_p`, the completed coordinate is
the power-series coordinate `ℤ_p⟦T⟧ ≃ₐ[ℤ_p] ℤ_p[[ℤ_p]]` attached to the topological generator
`γ = 1` of `ℤ_p`, defined by evaluating power series at `γ - 1`. -/
theorem completedCoordinate_eq_powerSeriesCoordinate (hp : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p]) :
    completedCoordinate hp =
      (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p)).toAlgHom :=
  (completedCoordinate_unique hp (by simp)).symm

/-- **Comparison with the power-series coordinate, as isomorphisms.** Over `O = ℤ_p`, the
isomorphism `completedCoordinateEquiv hp` is the power-series coordinate attached to the
topological generator `γ = 1` of `ℤ_p`. -/
theorem completedCoordinateEquiv_eq_powerSeriesCoordinate
    (hp : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p]) :
    completedCoordinateEquiv hp =
      completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p) :=
  AlgEquiv.coe_toAlgHom_injective <| by
    rw [← completedCoordinate_eq_powerSeriesCoordinate hp]
    exact AlgHom.coe_fn_injective (coe_completedCoordinateEquiv hp)

end TauCeti.Iwasawa
