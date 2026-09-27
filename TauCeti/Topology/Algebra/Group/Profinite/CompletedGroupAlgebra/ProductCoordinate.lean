/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.Algebra.MonoidAlgebra.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Prod

/-!
# The power-series coordinate of `ℤ_p[[C × Γ]]`

For a finite discrete group `C` and an infinite procyclic pro-`p` group `Γ` with topological
generator `γ`, so that `Γ ≅ ℤ_p`, the completed group algebra `ℤ_p[[C × Γ]]` is the power-series
ring over the group ring `ℤ_p[C]`:

```text
ℤ_p[C]⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[C × Γ]],   X ↦ (1, γ) - 1,   c ↦ (c, 1).
```

This is `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate`, the composite of three
isomorphisms: `ℤ_p[C]⟦X⟧ ≅ ℤ_p⟦X⟧[C]` (`MonoidAlgebra.powerSeriesAlgEquiv`, `C` finite),
the power-series coordinate `ℤ_p⟦X⟧ ≅ ℤ_p[[Γ]]` of the Iwasawa algebra applied to the
coefficients (`TauCeti.completedGroupAlgebra.powerSeriesCoordinate`), and
`ℤ_p[[Γ]][C] ≅ ℤ_p[[C × Γ]]` (`TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv`). As for
the procyclic coordinate, it depends on the generator `γ`.

The case `p = 2`, `C = C₂ = Multiplicative (ZMod 2)` and `Γ = ℤ₂`, transported along a topological
isomorphism `Γ' ≃ₜ* C₂ × ℤ₂`, is the dyadic coordinate of
`TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.DyadicCoordinate`; it is the
coordinate over which Labute's argument for the even-rank Demushkin groups with `q = 2` runs
(Labute, §4, p. 122).

## Main definitions

* `TauCeti.completedGroupAlgebra.prodPowerSeriesCoordinate C hΓ hγ`: the isomorphism
  `ℤ_p[C]⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[C × Γ]]`, with `prodPowerSeriesCoordinate_X` and
  `prodPowerSeriesCoordinate_C_single` as its values on `X` and on the group ring, and
  `prodPowerSeriesCoordinate_symm_of_inl` and `prodPowerSeriesCoordinate_symm_of_inr` as the
  values of its inverse on the group elements `(c, 1)` and `(1, γ)`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

open PowerSeries

namespace TauCeti.completedGroupAlgebra

section ProdPowerSeries

variable {p : ℕ} [Fact p.Prime] (C : Type*) [Group C] [TopologicalSpace C] [DiscreteTopology C]
  [Finite C] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [IsMulCommutative Γ] [TotallyDisconnectedSpace Γ] [Infinite Γ] (hΓ : IsProP p Γ) {γ : Γ}
  (hγ : (Subgroup.closure ({γ} : Set Γ)).topologicalClosure = ⊤)

/-- **The power-series coordinate of `ℤ_p[[C × Γ]]`.** For a finite discrete group `C` and a
topological generator `γ` of the infinite commutative pro-`p` group `Γ` (so that `Γ ≅ ℤ_p`), the
completed group algebra of `C × Γ` is the power-series ring over the group ring `ℤ_p[C]`, with
`X ↦ (1, γ) - 1` and the group element `c` going to `(c, 1)`. The coordinate depends on `γ`. -/
noncomputable def prodPowerSeriesCoordinate :
    PowerSeries (MonoidAlgebra ℤ_[p] C) ≃ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] (C × Γ) :=
  (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] C).symm.trans
    ((MonoidAlgebra.mapAlgEquiv ℤ_[p] C (powerSeriesCoordinate hΓ hγ)).trans
      (monoidAlgebraProdEquiv ℤ_[p] C Γ))

/-- The coordinate sends `X` to `(1, γ) - 1`. -/
@[simp]
theorem prodPowerSeriesCoordinate_X :
    prodPowerSeriesCoordinate C hΓ hγ PowerSeries.X = of ℤ_[p] (C × Γ) (1, γ) - 1 := by
  -- `mapAlgEquiv` is `mapAlgHom` on the underlying map, so Mathlib's `mapAlgHom_single` applies.
  have h : MonoidAlgebra.mapAlgEquiv ℤ_[p] C (powerSeriesCoordinate hΓ hγ)
      (MonoidAlgebra.single 1 PowerSeries.X) =
        MonoidAlgebra.single 1 (powerSeriesCoordinate hΓ hγ PowerSeries.X) :=
    MonoidAlgebra.mapAlgHom_single (powerSeriesCoordinate hΓ hγ).toAlgHom 1 PowerSeries.X
  rw [prodPowerSeriesCoordinate, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    MonoidAlgebra.powerSeriesAlgEquiv_symm_X, h, powerSeriesCoordinate_X,
    coe_monoidAlgebraProdEquiv, monoidAlgebraProdHom_single_one, map_sub, map_of, map_one,
    MonoidHom.inr_apply]

/-- The coordinate sends `1 + X` to the group element `(1, γ)`. -/
@[simp]
theorem prodPowerSeriesCoordinate_one_add_X :
    prodPowerSeriesCoordinate C hΓ hγ (1 + PowerSeries.X) = of ℤ_[p] (C × Γ) (1, γ) := by
  rw [map_add, map_one, prodPowerSeriesCoordinate_X, add_sub_cancel]

/-- The coordinate sends the constant `a · c` of the group ring to `a` times the group element
`(c, 1)`. -/
@[simp]
theorem prodPowerSeriesCoordinate_C_single (c : C) (a : ℤ_[p]) :
    prodPowerSeriesCoordinate C hΓ hγ (PowerSeries.C (MonoidAlgebra.single c a)) =
      algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] (C × Γ)) a * of ℤ_[p] (C × Γ) (c, 1) := by
  have h : MonoidAlgebra.mapAlgEquiv ℤ_[p] C (powerSeriesCoordinate hΓ hγ)
      (MonoidAlgebra.single c (PowerSeries.C a)) =
        MonoidAlgebra.single c (powerSeriesCoordinate hΓ hγ (PowerSeries.C a)) :=
    MonoidAlgebra.mapAlgHom_single (powerSeriesCoordinate hΓ hγ).toAlgHom c (PowerSeries.C a)
  rw [prodPowerSeriesCoordinate, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single, h, PowerSeries.C_eq_algebraMap,
    AlgEquiv.commutes, coe_monoidAlgebraProdEquiv, monoidAlgebraProdHom_single, AlgHom.commutes]

/-- The coordinate sends the group element `c` of the group ring to the group element `(c, 1)`. -/
theorem prodPowerSeriesCoordinate_C_single_one (c : C) :
    prodPowerSeriesCoordinate C hΓ hγ (PowerSeries.C (MonoidAlgebra.single c 1)) =
      of ℤ_[p] (C × Γ) (c, 1) := by
  rw [prodPowerSeriesCoordinate_C_single, map_one, one_mul]

/-- The inverse coordinate sends the group element `(c, 1)` to the group element `c` of the
group ring. -/
@[simp]
theorem prodPowerSeriesCoordinate_symm_of_inl (c : C) :
    (prodPowerSeriesCoordinate C hΓ hγ).symm (of ℤ_[p] (C × Γ) (c, 1)) =
      PowerSeries.C (MonoidAlgebra.single c 1) :=
  (prodPowerSeriesCoordinate C hΓ hγ).symm_apply_eq.mpr
    (prodPowerSeriesCoordinate_C_single_one C hΓ hγ c).symm

/-- The inverse coordinate sends the group element `(1, γ)` to `1 + X`. -/
@[simp]
theorem prodPowerSeriesCoordinate_symm_of_inr :
    (prodPowerSeriesCoordinate C hΓ hγ).symm (of ℤ_[p] (C × Γ) (1, γ)) = 1 + PowerSeries.X :=
  (prodPowerSeriesCoordinate C hΓ hγ).symm_apply_eq.mpr
    (prodPowerSeriesCoordinate_one_add_X C hΓ hγ).symm

end ProdPowerSeries

end TauCeti.completedGroupAlgebra
