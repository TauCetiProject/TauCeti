/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.DyadicCoordinate
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Topology of the power-series coordinates with finite group-ring coefficients

For a finite discrete group `C` and an infinite procyclic pro-`p` group `Γ`, the coordinate
`ℤ_p[C]⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[C × Γ]]` is a homeomorphism. Give the finite free coefficient module
`ℤ_p[C]` its module topology and the power-series ring its coefficientwise topology. These are
identified with the inverse-limit topology on the completed group algebra. No commutativity
assumption on `C` is needed.

The dyadic coordinate for a group topologically isomorphic to `C₂ × ℤ₂` has the same property.
This permits transport of compact modules between the completed group algebra and the
power-series model over `ℤ₂[C₂]`, retaining their topology as well as their algebraic structure.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

open scoped PowerSeries.WithPiTopology

namespace TauCeti.completedGroupAlgebra

section Product

variable {p : ℕ} [Fact p.Prime] (C : Type*) [Group C] [TopologicalSpace C] [DiscreteTopology C]
  [Finite C] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [IsMulCommutative Γ] [TotallyDisconnectedSpace Γ] [Infinite Γ] (hΓ : IsProP p Γ) {γ : Γ}
  (hγ : (Subgroup.closure ({γ} : Set Γ)).topologicalClosure = ⊤)
  [TopologicalSpace (MonoidAlgebra ℤ_[p] C)] [IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] C)]

/-- The product power-series coordinate is continuous for the module topology on `ℤ_p[C]`, the
coefficientwise topology on its power series, and the inverse-limit topology on `ℤ_p[[C × Γ]]`.
The finite group `C` may be noncommutative. -/
theorem continuous_prodPowerSeriesCoordinate :
    Continuous (prodPowerSeriesCoordinate C hΓ hγ) := by
  classical
  let := Fintype.ofFinite C
  let s := (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] C).symm
  have hc (c : C) : Continuous fun ψ : PowerSeries (MonoidAlgebra ℤ_[p] C) ↦
      (s ψ).coeff c := by
    rw [continuous_iff_continuousAt]
    intro ψ
    apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ_[p] _ _ _).mpr
    intro n
    let l : MonoidAlgebra ℤ_[p] C →ₗ[ℤ_[p]] ℤ_[p] :=
      (Finsupp.lapply c).comp (MonoidAlgebra.coeffLinearEquiv ℤ_[p]).toLinearMap
    have hl (a : MonoidAlgebra ℤ_[p] C) : l a = a.coeff c := rfl
    simpa only [s, MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, ContinuousAt,
      Function.comp_def, hl] using
      ((IsModuleTopology.continuous_of_linearMap l).comp
        (PowerSeries.WithPiTopology.continuous_coeff (MonoidAlgebra ℤ_[p] C) n)).continuousAt
  have hs (ψ : PowerSeries (MonoidAlgebra ℤ_[p] C)) :
      s ψ = ∑ c : C, MonoidAlgebra.single c ((s ψ).coeff c) := by
    rw [← Finsupp.sum_fintype _ _ (fun c ↦ MonoidAlgebra.single_zero c),
      MonoidAlgebra.sum_coeff_single]
  have he (ψ : PowerSeries (MonoidAlgebra ℤ_[p] C)) :
      prodPowerSeriesCoordinate C hΓ hγ ψ =
        ∑ c : C, map ℤ_[p] (MonoidHom.inr C Γ) (continuous_inr C Γ)
          (powerSeriesCoordinate hΓ hγ ((s ψ).coeff c)) * of ℤ_[p] (C × Γ) (c, 1) := by
    rw [prodPowerSeriesCoordinate_def, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    conv_lhs => rw [hs ψ, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    -- The coefficient algebra equivalence uses `mapAlgHom` on its underlying map.
    have hm : MonoidAlgebra.mapAlgEquiv ℤ_[p] C (powerSeriesCoordinate hΓ hγ)
        (MonoidAlgebra.single c ((s ψ).coeff c)) =
        MonoidAlgebra.single c (powerSeriesCoordinate hΓ hγ ((s ψ).coeff c)) :=
      MonoidAlgebra.mapAlgHom_single (powerSeriesCoordinate hΓ hγ).toAlgHom c ((s ψ).coeff c)
    rw [hm, coe_monoidAlgebraProdEquiv, monoidAlgebraProdHom_single]
  have hcont : Continuous fun ψ : PowerSeries (MonoidAlgebra ℤ_[p] C) ↦
      ∑ c : C, map ℤ_[p] (MonoidHom.inr C Γ) (continuous_inr C Γ)
        (powerSeriesCoordinate hΓ hγ ((s ψ).coeff c)) * of ℤ_[p] (C × Γ) (c, 1) :=
    continuous_finsetSum _ fun c _ ↦
      ((continuous_map ℤ_[p] (MonoidHom.inr C Γ) (continuous_inr C Γ)).comp
        ((continuous_powerSeriesCoordinate hΓ hγ).comp (hc c))).mul continuous_const
  exact hcont.congr fun ψ ↦ (he ψ).symm

/-- The inverse product coordinate is continuous. Thus the algebraic identification with power
series over the finite group ring is a homeomorphism for the coefficientwise topology. -/
theorem continuous_prodPowerSeriesCoordinate_symm :
    Continuous (prodPowerSeriesCoordinate C hΓ hγ).symm := by
  have : CompactSpace (MonoidAlgebra ℤ_[p] C) :=
    (TauCeti.ModuleTopology.equivFunHomeomorph (MonoidAlgebra.basis C ℤ_[p])).symm.compactSpace
  have : CompactSpace (PowerSeries (MonoidAlgebra ℤ_[p] C)) :=
    inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → MonoidAlgebra ℤ_[p] C))
  exact (Continuous.homeoOfEquivCompactToT2 (f := (prodPowerSeriesCoordinate C hΓ hγ).toEquiv)
    (continuous_prodPowerSeriesCoordinate C hΓ hγ)).symm.continuous

end Product

section Dyadic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  (e : Γ ≃ₜ* Multiplicative (ZMod 2) × Multiplicative ℤ_[2])
  [TopologicalSpace (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2)))]
  [IsModuleTopology ℤ_[2] (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2)))]

/-- The dyadic coordinate is continuous for the module topology on `ℤ₂[C₂]`, the
coefficientwise topology on `ℤ₂[C₂]⟦X⟧`, and the inverse-limit topology on `ℤ₂[[Γ]]`. -/
theorem continuous_dyadicCoordinate : Continuous (dyadicCoordinate e) := by
  rw [dyadicCoordinate_def, AlgEquiv.coe_trans, coe_domCongr]
  exact (continuous_map ℤ_[2] (e.symm : _ →* Γ) e.symm.continuous).comp
    (continuous_prodPowerSeriesCoordinate (Multiplicative (ZMod 2))
      (isProP_multiplicative_padicInt 2) (topologicallyGenerates_ofAdd_one_padicInt 2))

/-- The inverse dyadic coordinate is continuous, completing its identification of
`ℤ₂[[Γ]]` with the topological power-series algebra `ℤ₂[C₂]⟦X⟧`. -/
theorem continuous_dyadicCoordinate_symm : Continuous (dyadicCoordinate e).symm := by
  have : CompactSpace (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))) :=
    (TauCeti.ModuleTopology.equivFunHomeomorph
      (MonoidAlgebra.basis (Multiplicative (ZMod 2)) ℤ_[2])).symm.compactSpace
  have : CompactSpace (PowerSeries (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2)))) :=
    inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))))
  exact (Continuous.homeoOfEquivCompactToT2 (f := (dyadicCoordinate e).toEquiv)
    (continuous_dyadicCoordinate e)).symm.continuous

end Dyadic

end TauCeti.completedGroupAlgebra
