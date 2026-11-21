/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import TauCeti.Analysis.Normed.Module.Dual.Bounded
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.PurelyInseparable

/-!
# Characteristic-free weak stability of Gauss-normed Tate fraction fields

Let `K` be a complete ultrametric normed field of arbitrary characteristic (trivially or
nontrivially normed), `σ` a countable variable type, and `c : σ → ℝ` a positive polyradius. This
file proves that the Gauss-normed fraction field `GaussFractionField σ K c` of the
restricted-series algebra `K{X / c}` is weakly stable
(`TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`): on every finite extension
`L / GaussFractionField σ K c`, every linear functional is bounded by `spectralNorm`.

With no variables (`[IsEmpty σ]`), `GaussFractionField σ K c` is isometrically `K`-isomorphic to
`K`, so its spectral norms and weak stability coincide with those of `K` even without completeness
of `K`.

## Proof outline

By `TauCeti.IsWeaklyStable.of_isPurelyInseparable`, it suffices to prove boundedness of linear
functionals on every finite purely inseparable extension `M` of `F := GaussFractionField σ K c`.
By `TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable`, every nonzero
vector `x₀ : M` is separated from `0` by an `F`-linear functional bounded by `spectralNorm F M`,
which implies boundedness of every linear functional on `M` by
`Module.Dual.exists_bound_of_forall_exists_ne_zero`.

## Main results

* `TauCeti.MvPowerSeries.spectralNorm_gaussFractionField_of_isEmpty` and
  `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField_iff_of_isEmpty`: zero-variable agreement
  with extensions of `K`.
* `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`: characteristic-free weak stability of
  `GaussFractionField σ K c` for `[Countable σ]` over any complete ultrametric normed field.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§3.5.3 and 5.3.1, Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

section Empty

variable (σ K : Type*) [NormedField K] [IsUltrametricDist K] [IsEmpty σ]
  (c : σ → ℝ) [∀ i, Fact (0 < c i)]

/-- With no variables, the spectral norm of an extension over `GaussFractionField σ K c` coincides
with its spectral norm over `K`. -/
@[simp]
theorem spectralNorm_gaussFractionField_of_isEmpty (L : Type*) [Field L]
    [Algebra K L] [Algebra (GaussFractionField σ K c) L]
    [IsScalarTower K (GaussFractionField σ K c) L] (y : L) :
    spectralNorm (GaussFractionField σ K c) L y = spectralNorm K L y := by
  refine ((gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.spectralNorm_eq_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c) (RingEquiv.refl L) ?_ y).symm
  ext z
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    RingHom.coe_coe, RingEquiv.refl_apply]
  rw [IsScalarTower.algebraMap_apply K (GaussFractionField σ K c) L,
    ← gaussFractionFieldIsEmptyAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]

/-- With no variables, `GaussFractionField σ K c` is weakly stable if and only if `K` is weakly
stable. -/
@[simp]
theorem isWeaklyStable_gaussFractionField_iff_of_isEmpty :
    IsWeaklyStable (GaussFractionField σ K c) ↔ IsWeaklyStable K :=
  (gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.isWeaklyStable_iff_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c)

end Empty

section WeaklyStable

/-- **Characteristic-free weak stability of Gauss-normed Tate fraction fields.**
For any complete ultrametric normed field `K` (of arbitrary characteristic, trivially or
nontrivially normed), countable variable type `σ`, and positive polyradius `c : σ → ℝ`, the
Gauss-normed fraction field `GaussFractionField σ K c` is weakly stable
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.1, Theorem 1). -/
theorem isWeaklyStable_gaussFractionField (σ K : Type*) [Countable σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    IsWeaklyStable (GaussFractionField σ K c) := by
  refine IsWeaklyStable.of_isPurelyInseparable fun M _ _ _ _ ψ ↦ ?_
  refine Module.Dual.exists_bound_of_forall_exists_ne_zero ψ (spectralNorm _ M) fun x₀ hx₀ ↦ ?_
  obtain ⟨φ, C, -, hφ_bound, -, hφ_ne⟩ :=
    exists_dual_norm_le_spectralNorm_of_isPurelyInseparable (K := K) (c := c) M hx₀
  exact ⟨φ, ⟨C, hφ_bound⟩, hφ_ne⟩

end WeaklyStable

end TauCeti.MvPowerSeries
