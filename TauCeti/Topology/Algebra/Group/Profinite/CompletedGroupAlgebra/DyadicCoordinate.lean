/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.ProductCoordinate

/-!
# The dyadic coordinate `ℤ₂[C₂]⟦X⟧ ≃ₐ ℤ₂[[Γ]]` for `Γ ≅ C₂ × ℤ₂`

For a group `Γ` with a topological isomorphism `e : Γ ≃ₜ* C₂ × ℤ₂`, where `C₂ = Multiplicative
(ZMod 2)` and `ℤ₂ = Multiplicative ℤ_[2]`, the completed group algebra `ℤ₂[[Γ]]` is the
power-series ring over the group ring `ℤ₂[C₂]`:

```text
ℤ₂[C₂]⟦X⟧ ≃ₐ[ℤ₂] ℤ₂[[Γ]],   X ↦ γ - 1,   σ ↦ e.symm (σ, 1),
```

for the topological generator `γ = e.symm (1, Multiplicative.ofAdd 1)` of the `ℤ₂`-factor. This
is the **dyadic coordinate** `TauCeti.completedGroupAlgebra.dyadicCoordinate e`, the power-series
coordinate `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate` of `ℤ₂[[C₂ × ℤ₂]]`
transported along `e`. Like the procyclic coordinate it depends on the chosen generator, here
through `e`.

`Γ ≅ C₂ × ℤ₂` is the shape of the image `{±1} × (1 + 2^f ℤ₂)` of the canonical character of an
even-rank Demushkin group with `q = 2`, over which Labute's argument for that case runs (Labute,
§4, p. 122), and `ℤ₂[C₂]` is its coefficient ring. Here `Multiplicative (ZMod 2)` is a genuine
cyclic group of order two, not `ZMod 2` read as a multiplicative monoid, whose monoid algebra
would be a different ring.

## Main definitions

* `TauCeti.completedGroupAlgebra.dyadicCoordinate e`: the isomorphism
  `ℤ₂[C₂]⟦X⟧ ≃ₐ[ℤ₂] ℤ₂[[Γ]]` for `e : Γ ≃ₜ* C₂ × ℤ₂`, with `dyadicCoordinate_X` and
  `dyadicCoordinate_C_single` as its values on `X` and on the group ring, and
  `dyadicCoordinate_symm_of_inl` and `dyadicCoordinate_symm_of_inr` as the values of its inverse
  on the group elements `e.symm (σ, 1)` and `γ`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

open PowerSeries

namespace TauCeti.completedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  (e : Γ ≃ₜ* Multiplicative (ZMod 2) × Multiplicative ℤ_[2])

/-- **The dyadic coordinate.** For a group `Γ ≅ C₂ × ℤ₂`, with `C₂ = Multiplicative (ZMod 2)`,
the completed group algebra `ℤ₂[[Γ]]` is the power-series ring over the group ring `ℤ₂[C₂]`,
with `X ↦ γ - 1` for the topological generator `γ = e.symm (1, Multiplicative.ofAdd 1)` of the
`ℤ₂`-factor and the group element `σ` of `C₂` going to `e.symm (σ, 1)`. This is the coefficient
ring of Labute's treatment of the even-rank Demushkin groups with `q = 2` whose canonical
character has image `{±1} × (1 + 2^f ℤ₂)`. -/
noncomputable def dyadicCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))) ≃ₐ[ℤ_[2]]
      completedGroupAlgebra ℤ_[2] Γ :=
  (prodPowerSeriesCoordinate (Multiplicative (ZMod 2)) (isProP_multiplicative_padicInt 2)
    (topologicallyGenerates_ofAdd_one_padicInt 2)).trans (domCongr ℤ_[2] e.symm)

/-- The dyadic coordinate sends `X` to `γ - 1`, for the generator
`γ = e.symm (1, Multiplicative.ofAdd 1)` of the `ℤ₂`-factor. -/
@[simp]
theorem dyadicCoordinate_X :
    dyadicCoordinate e PowerSeries.X = of ℤ_[2] Γ (e.symm (1, Multiplicative.ofAdd 1)) - 1 := by
  rw [dyadicCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_X, map_sub,
    map_one (domCongr ℤ_[2] e.symm), domCongr_of]

/-- The dyadic coordinate sends `1 + X` to the generator `γ = e.symm (1, Multiplicative.ofAdd 1)`
of the `ℤ₂`-factor. -/
@[simp]
theorem dyadicCoordinate_one_add_X :
    dyadicCoordinate e (1 + PowerSeries.X) = of ℤ_[2] Γ (e.symm (1, Multiplicative.ofAdd 1)) := by
  rw [map_add, map_one, dyadicCoordinate_X, add_sub_cancel]

/-- The dyadic coordinate sends the constant `a · σ` of the group ring `ℤ₂[C₂]` to `a` times the
group element `e.symm (σ, 1)`. -/
@[simp]
theorem dyadicCoordinate_C_single (σ : Multiplicative (ZMod 2)) (a : ℤ_[2]) :
    dyadicCoordinate e (PowerSeries.C (MonoidAlgebra.single σ a)) =
      algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] Γ) a * of ℤ_[2] Γ (e.symm (σ, 1)) := by
  rw [dyadicCoordinate, AlgEquiv.trans_apply, prodPowerSeriesCoordinate_C_single, map_mul,
    AlgEquiv.commutes, domCongr_of]

/-- The dyadic coordinate sends the group element `σ` of the group ring `ℤ₂[C₂]` to the group
element `e.symm (σ, 1)`. -/
theorem dyadicCoordinate_C_single_one (σ : Multiplicative (ZMod 2)) :
    dyadicCoordinate e (PowerSeries.C (MonoidAlgebra.single σ 1)) = of ℤ_[2] Γ (e.symm (σ, 1)) := by
  rw [dyadicCoordinate_C_single, map_one, one_mul]

/-- The inverse dyadic coordinate sends the group element `e.symm (σ, 1)` to the group element
`σ` of the group ring `ℤ₂[C₂]`. -/
@[simp]
theorem dyadicCoordinate_symm_of_inl (σ : Multiplicative (ZMod 2)) :
    (dyadicCoordinate e).symm (of ℤ_[2] Γ (e.symm (σ, 1))) =
      PowerSeries.C (MonoidAlgebra.single σ 1) :=
  (dyadicCoordinate e).symm_apply_eq.mpr (dyadicCoordinate_C_single_one e σ).symm

/-- The inverse dyadic coordinate sends the generator `γ = e.symm (1, Multiplicative.ofAdd 1)` of
the `ℤ₂`-factor to `1 + X`. -/
@[simp]
theorem dyadicCoordinate_symm_of_inr :
    (dyadicCoordinate e).symm (of ℤ_[2] Γ (e.symm (1, Multiplicative.ofAdd 1))) =
      1 + PowerSeries.X :=
  (dyadicCoordinate e).symm_apply_eq.mpr (dyadicCoordinate_one_add_X e).symm

end TauCeti.completedGroupAlgebra
