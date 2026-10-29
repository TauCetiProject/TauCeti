/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Convergence
public import TauCeti.RingTheory.LaurentSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# The valuation topology on formal power series

The scope `TauCeti.PowerSeries.WithValuationTopology` gives `K⟦X⟧` the subspace topology
from the valued field `K⸨X⸩`. No topology on the coefficient field is used. Convergence means
eventual agreement of each coefficient, or equivalently eventual agreement modulo every
power of `X`. These are the finite-jet neighbourhoods of a formal coordinate.

Substitution by a series with zero constant coefficient is continuous, including substitution
by zero. Consequently every algebra endomorphism of `K⟦X⟧` is automatically continuous, and
formal coordinate substitutions are homeomorphisms. This scope is independent of
`PowerSeries.WithPiTopology`, which uses a supplied topology on the coefficients.
-/

public section

open Filter Topology
open scoped PowerSeries LaurentSeries

namespace TauCeti.PowerSeries.WithValuationTopology

variable {K : Type*} [Field K]

/-- The topology induced by the inclusion of power series into the Laurent-series field. -/
noncomputable scoped instance instTopologicalSpace : TopologicalSpace K⟦X⟧ :=
  TopologicalSpace.induced (fun f : K⟦X⟧ ↦ (f : K⸨X⸩)) inferInstance

/-- The power-series topology is induced by the Laurent-series inclusion. -/
theorem isInducing_coe : IsInducing (fun f : K⟦X⟧ ↦ (f : K⸨X⸩)) :=
  .induced _

/-- The Laurent-series inclusion is a topological embedding. -/
theorem isEmbedding_coe : IsEmbedding (fun f : K⟦X⟧ ↦ (f : K⸨X⸩)) :=
  ⟨isInducing_coe, HahnSeries.ofPowerSeries_injective⟩

/-- Power series converge in the valuation topology exactly when every coefficient eventually
agrees with the corresponding coefficient of the limit. -/
theorem tendsto_iff_coeff {ι : Type*} {l : Filter ι} (f : ι → K⟦X⟧) (g : K⟦X⟧) :
    Tendsto f l (𝓝 g) ↔
      ∀ n : ℕ, ∀ᶠ i in l, _root_.PowerSeries.coeff n (f i) = _root_.PowerSeries.coeff n g := by
  rw [isInducing_coe.tendsto_nhds_iff, tendsto_laurentSeries_iff_coeff]
  constructor
  · intro h n
    simpa using h.2 (n : ℤ)
  · intro h
    refine ⟨⟨0, .of_forall fun i z hz ↦ ?_⟩, fun z ↦ ?_⟩
    · simp [_root_.PowerSeries.coeff_coe, hz]
    · cases z with
      | ofNat n => simpa using h n
      | negSucc n => exact .of_forall (by simp [_root_.PowerSeries.coeff_coe])

/-- The induced topology is Hausdorff. -/
scoped instance : T2Space K⟦X⟧ := isEmbedding_coe.t2Space

/-- Addition, negation and multiplication are continuous for the valuation topology. -/
scoped instance : IsTopologicalRing K⟦X⟧ := by
  let := isInducing_coe.isTopologicalAddGroup (HahnSeries.ofPowerSeries ℤ K).toAddMonoidHom
  let := isInducing_coe.continuousMul (HahnSeries.ofPowerSeries ℤ K)
  exact
    { toContinuousAdd := inferInstance
      toContinuousMul := inferInstance
      toContinuousNeg := inferInstance }

/-- Convergence is equivalently eventual agreement modulo each power of `X`. -/
theorem tendsto_iff_X_pow_dvd {ι : Type*} {l : Filter ι} (f : ι → K⟦X⟧) (g : K⟦X⟧) :
    Tendsto f l (𝓝 g) ↔
      ∀ n : ℕ, ∀ᶠ i in l, _root_.PowerSeries.X ^ n ∣ f i - g := by
  rw [tendsto_iff_coeff]
  constructor
  · intro h n
    have he : ∀ᶠ i in l, ∀ m ∈ Finset.range n,
        _root_.PowerSeries.coeff m (f i) = _root_.PowerSeries.coeff m g :=
      (Filter.eventually_all_finset _).mpr fun m _ ↦ h m
    filter_upwards [he] with i hi
    simpa [_root_.PowerSeries.X_pow_dvd_iff, sub_eq_zero] using hi
  · intro h n
    filter_upwards [h (n + 1)] with i hi
    simpa only [map_sub, sub_eq_zero] using
      (_root_.PowerSeries.X_pow_dvd_iff.mp hi) n (Nat.lt_succ_self n)

/-- The congruence classes modulo powers of `X` form a neighbourhood basis. -/
theorem hasBasis_nhds (g : K⟦X⟧) :
    (𝓝 g).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {f : K⟦X⟧ | _root_.PowerSeries.X ^ n ∣ f - g}) := by
  have heq : 𝓝 g = ⨅ n : ℕ,
      𝓟 {f : K⟦X⟧ | _root_.PowerSeries.X ^ n ∣ f - g} := by
    apply le_antisymm
    · refine le_iInf fun n ↦ ?_
      rw [Filter.le_principal_iff]
      exact (tendsto_iff_X_pow_dvd _ g).mp tendsto_id n
    · exact (tendsto_iff_X_pow_dvd (fun f ↦ f) g).mpr fun n ↦
        Filter.mem_iInf_of_mem n (Filter.mem_principal_self _)
  rw [heq]
  refine Filter.hasBasis_iInf_principal fun m n ↦ ⟨max m n, ?_, ?_⟩
  · exact fun f hf ↦ dvd_trans (pow_dvd_pow _ (le_max_left m n)) hf
  · exact fun f hf ↦ dvd_trans (pow_dvd_pow _ (le_max_right m n)) hf

/-- Substitution by a series with zero constant coefficient is continuous in the valuation
topology, even when the substituting series is zero. -/
theorem continuous_subst {φ : K⟦X⟧} (hφ : _root_.PowerSeries.constantCoeff φ = 0) :
    Continuous (fun f : K⟦X⟧ ↦ f.subst φ) := by
  rcases eq_or_ne φ 0 with rfl | hφ₀
  · rw [continuous_iff_continuousAt]
    intro g
    apply (tendsto_iff_coeff _ _).mpr
    intro n
    filter_upwards [(tendsto_iff_coeff _ _).mp (tendsto_id : Tendsto
      (fun f : K⟦X⟧ ↦ f) (𝓝 g) (𝓝 g)) 0] with f hf
    have hc : _root_.PowerSeries.constantCoeff f = _root_.PowerSeries.constantCoeff g := by
      simpa using hf
    rw [_root_.PowerSeries.subst_zero_eq_C_constantCoeff,
      _root_.PowerSeries.subst_zero_eq_C_constantCoeff, hc]
  · apply isInducing_coe.continuous_iff.mpr
    simpa only [Function.comp_def, LaurentSeries.substAlgHom_coe] using
      (LaurentSeries.continuous_substAlgHom hφ hφ₀).comp isInducing_coe.continuous

/-- Every algebra endomorphism of formal power series over a field is automatically continuous
for the valuation topology. -/
theorem continuous_algHom (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) : Continuous σ := by
  convert continuous_subst σ.constantCoeff_apply_X using 1
  exact funext σ.apply_eq_subst

end TauCeti.PowerSeries.WithValuationTopology

namespace TauCeti.FormalCoordinate

open scoped TauCeti.PowerSeries.WithValuationTopology

variable {K : Type*} [Field K]

/-- The substitution of a formal coordinate, as a homeomorphism for the valuation topology. -/
noncomputable def substHomeomorph (φ : FormalCoordinate K) : K⟦X⟧ ≃ₜ K⟦X⟧ where
  toEquiv := φ.substAlgEquiv.toEquiv
  continuous_toFun := PowerSeries.WithValuationTopology.continuous_algHom φ.substAlgEquiv.toAlgHom
  continuous_invFun :=
    PowerSeries.WithValuationTopology.continuous_algHom φ.substAlgEquiv.symm.toAlgHom

/-- The coordinate homeomorphism acts by substitution. -/
@[simp]
theorem substHomeomorph_apply (φ : FormalCoordinate K) (f : K⟦X⟧) :
    φ.substHomeomorph f = f.subst φ.toPowerSeries := φ.substAlgEquiv_apply f

/-- Inverting a coordinate inverts its substitution homeomorphism. -/
@[simp]
theorem substHomeomorph_symm (φ : FormalCoordinate K) :
    φ.substHomeomorph.symm = φ⁻¹.substHomeomorph :=
  Homeomorph.ext fun f ↦ congr($(φ.substAlgEquiv_symm) f)

/-- Coordinate multiplication reverses the order of substitution homeomorphisms. -/
@[simp]
theorem substHomeomorph_mul (φ ψ : FormalCoordinate K) :
    (φ * ψ).substHomeomorph = φ.substHomeomorph.trans ψ.substHomeomorph :=
  Homeomorph.ext fun f ↦ by simp [subst_subst]

/-- The identity coordinate acts as the identity homeomorphism. -/
@[simp]
theorem substHomeomorph_one :
    (1 : FormalCoordinate K).substHomeomorph = Homeomorph.refl K⟦X⟧ :=
  Homeomorph.ext fun f ↦ by simp

end TauCeti.FormalCoordinate
