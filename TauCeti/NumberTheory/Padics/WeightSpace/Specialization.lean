/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.DualNumber
public import TauCeti.NumberTheory.Padics.WeightSpace.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.WeightSpace.GeneratorChange
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Universal characters and specialisation of `ℤ_p[[ℤ_pˣ]]`

Let `p` be a prime, put `q = p ^ TauCeti.padicUnitsDepth p` (`q = p` for odd `p` and `q = 4` for
`p = 2`), let `Δ = (ℤ/qℤ)ˣ`, let `ω : Δ →* ℤ_pˣ` be `TauCeti.padicUnitsSection p`, and let
`γ = exp q` be `TauCeti.padicUnitsGenerator p`.

The group-element embedding `x ↦ [x]` defines the *universal weight*
`TauCeti.WeightSpace.universal p : WeightSpace p (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)`, with finite
part `δ ↦ [ω(δ)]` and coordinate `[γ] - 1`. Every continuous ring homomorphism out of
`ℤ_p[[ℤ_pˣ]]` restricts along `universal p` to a weight (`TauCeti.WeightSpace.ofContinuousRingHom`),
and two continuous ring homomorphisms into a Hausdorff topological ring that agree on the group
elements are equal (`TauCeti.completedGroupAlgebra_ringHom_ext`).

Conversely, weights integrate to continuous algebra homomorphisms out of `ℤ_p[[ℤ_pˣ]]` in both
topological regimes:

* **Adic specialisation (`TauCeti.WeightSpace.adicSpecialize`).** Over a complete separated
  linearly topologised commutative `ℤ_p`-algebra `S` (including `ℤ_p` and `ℤ_p[[ℤ_pˣ]]` itself), a
  weight `κ : WeightSpace p S` extends uniquely to a continuous `ℤ_p`-algebra homomorphism
  `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S`, packaged as the bijection `TauCeti.WeightSpace.adicSpecializeEquiv`.
* **Normed specialisation (`TauCeti.WeightSpace.normedSpecialize`).** Over a complete ultrametric
  normed commutative `ℤ_p`-algebra `R` with contractive `ℤ_p`-action (including `ℚ_p`, `ℂ_p`, and
  nonreduced Banach rings such as `TauCeti.MaxDualNumber ℚ_[p]`), evaluation of integral power
  series at a topologically nilpotent element `t` (`TauCeti.padicPowerSeriesEval`) lifts any weight
  `κ : WeightSpace p R` to a unique continuous `ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R`,
  packaged as `TauCeti.WeightSpace.normedSpecializeEquiv`, with explicit convergent power-series
  expansion `TauCeti.WeightSpace.hasSum_normedSpecialize_padicUnitsCoordinate`.
* **Normed `ℚ_p`-algebras (`TauCeti.WeightSpace.specializeRingHom`).** For a complete ultrametric
  normed commutative `ℚ_p`-algebra `K` without a pre-installed `ℤ_p`-algebra instance,
  `specializeRingHom` provides the unique continuous ring homomorphism `ℤ_p[[ℤ_pˣ]] →+* K`
  extending `κ`.
* **Compatibility (`TauCeti.WeightSpace.adicSpecialize_eq_normedSpecialize`).** When the target
  carries both structures (for instance `ℤ_p`), the adic and normed specialisations coincide.

## Main definitions

* `TauCeti.WeightSpace.universal p`: the universal weight `ℤ_pˣ →ₜ* (ℤ_p[[ℤ_pˣ]])ˣ`.
* `TauCeti.WeightSpace.ofContinuousRingHom`: restriction of a continuous ring homomorphism out of
  `ℤ_p[[ℤ_pˣ]]` to a weight.
* `TauCeti.WeightSpace.adicSpecialize`, `TauCeti.WeightSpace.adicSpecializeEquiv`: adic
  specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight.
* `TauCeti.padicPowerSeriesEval`: continuous evaluation of `ℤ_p⟦X⟧` at a topologically nilpotent
  element of a complete ultrametric normed `ℤ_p`-algebra.
* `TauCeti.WeightSpace.normedSpecialize`, `TauCeti.WeightSpace.normedSpecializeEquiv`: normed
  specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight.
* `TauCeti.WeightSpace.specializeRingHom`: normed specialisation for complete ultrametric normed
  `ℚ_p`-algebras.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.6 and 4.
-/

public section

open Filter Topology
open scoped PowerSeries.WithPiTopology

namespace TauCeti

section Uniqueness

variable {p : ℕ} [Fact p.Prime]

/-- Two continuous ring homomorphisms from `ℤ_p[[ℤ_pˣ]]` into a Hausdorff space with ring structure
that agree on all group elements `[x]` (`x ∈ ℤ_pˣ`) are equal: they agree on `ℕ`, hence on `ℤ_p` by
density of `ℕ`, hence on the `ℤ_p`-span of the group elements, which is dense in `ℤ_p[[ℤ_pˣ]]`. -/
theorem completedGroupAlgebra_ringHom_ext {R : Type*} [Ring R] [TopologicalSpace R] [T2Space R]
    {φ ψ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      ψ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x)) :
    φ = ψ := by
  have halg_cont : Continuous (algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)) := by
    have halg_eq : (algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) : ℤ_[p] → _) =
        fun a : ℤ_[p] ↦ a • (1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :=
      funext Algebra.algebraMap_eq_smul_one
    rw [halg_eq]
    exact continuous_id.smul continuous_const
  have halg : ∀ a : ℤ_[p], φ (algebraMap ℤ_[p] _ a) = ψ (algebraMap ℤ_[p] _ a) :=
    congrFun (PadicInt.denseRange_natCast.equalizer (hφ.comp halg_cont) (hψ.comp halg_cont)
      (funext fun n ↦ by simp))
  have hspan : ∀ z ∈ Submodule.span ℤ_[p]
      (Set.range (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ)), φ z = ψ z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact h x
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, halg a, hx]
  have hclosed : IsClosed {z | φ z = ψ z} := isClosed_eq hφ hψ
  have htop : ∀ z, z ∈ ({z | φ z = ψ z} : Set _) := fun z ↦
    hclosed.closure_subset_iff.mpr hspan
      ((completedGroupAlgebra.dense_span_range_of ℤ_[p] ℤ_[p]ˣ) z)
  exact RingHom.ext htop

/-- Two continuous `ℤ_p`-algebra homomorphisms from `ℤ_p[[ℤ_pˣ]]` into a Hausdorff `ℤ_p`-algebra
that agree on all group elements `[x]` (`x ∈ ℤ_pˣ`) are equal. -/
theorem completedGroupAlgebra_algHom_ext {R : Type*} [Ring R] [TopologicalSpace R] [T2Space R]
    [Algebra ℤ_[p] R]
    {φ ψ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R}
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      ψ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x)) :
    φ = ψ :=
  AlgHom.ext <| RingHom.congr_fun
    (completedGroupAlgebra_ringHom_ext (φ := φ.toRingHom) (ψ := ψ.toRingHom) hφ hψ h)

end Uniqueness

section LiftHelper

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [Algebra ℤ_[p] B]

/-- Common algebraic lift of a power-series evaluation `ε : ℤ_p⟦X⟧ →ₐ[ℤ_p] B` and a finite
character `η : Δ →* Bˣ` across `padicUnitsCoordinate p : (ℤ_p[Δ])⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[ℤ_pˣ]]`. -/
private noncomputable def liftPowerSeriesAndFiniteChar
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] B :=
  ((MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) fun _ _ ↦ Commute.all _ _).comp
    (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p]
      (ZMod (p ^ padicUnitsDepth p))ˣ).symm.toAlgHom).comp
    (padicUnitsCoordinate p).symm.toAlgHom

private theorem liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_X
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ) :
    liftPowerSeriesAndFiniteChar ε η (padicUnitsCoordinate p PowerSeries.X) =
      ε PowerSeries.X := by
  simp [liftPowerSeriesAndFiniteChar]

private theorem liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_C_single
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ)
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    liftPowerSeriesAndFiniteChar ε η
        (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))) =
      algebraMap ℤ_[p] B a * η δ := by
  rw [liftPowerSeriesAndFiniteChar, AlgHom.comp_apply, AlgHom.comp_apply]
  change MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) _
    ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ).symm
      ((padicUnitsCoordinate p).symm
        (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))))) = _
  rw [(padicUnitsCoordinate p).symm_apply_apply, MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single,
    MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single]
  simp [PowerSeries.C_eq_algebraMap]

private theorem liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_map_singleOneRingHom
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ)
    (φ : PowerSeries ℤ_[p]) :
    liftPowerSeriesAndFiniteChar ε η
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      ε φ := by
  rw [liftPowerSeriesAndFiniteChar, AlgHom.comp_apply, AlgHom.comp_apply]
  change MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) _
    ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ).symm
      ((padicUnitsCoordinate p).symm
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)))) = _
  rw [(padicUnitsCoordinate p).symm_apply_apply,
    ← MonoidAlgebra.toPowerSeries_single_one ℤ_[p] ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ,
    ← MonoidAlgebra.coe_powerSeriesAlgEquiv, AlgEquiv.symm_apply_apply,
    MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single]
  simp

private theorem liftPowerSeriesAndFiniteChar_of
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ)
    (x : ℤ_[p]ˣ) :
    liftPowerSeriesAndFiniteChar ε η (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      η (padicIntUnitsEquivZModUnitsProd p x).1 *
        ε (PowerSeries.binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd) := by
  have hmap (s : ℤ_[p]) :
      PowerSeries.binomialSeries
        (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) s =
      PowerSeries.map MonoidAlgebra.singleOneRingHom (PowerSeries.binomialSeries ℤ_[p] s) := by
    ext n
    simp [PowerSeries.binomialSeries_coeff, MonoidAlgebra.one_def]
  have hx : completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x =
      padicUnitsCoordinate p
        (PowerSeries.C (MonoidAlgebra.single (padicIntUnitsEquivZModUnitsProd p x).1 1) *
          PowerSeries.map MonoidAlgebra.singleOneRingHom
            (PowerSeries.binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd)) := by
    rw [← hmap, ← padicUnitsCoordinate_symm_of, AlgEquiv.apply_symm_apply]
  rw [hx, map_mul, map_mul, liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_C_single,
    liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_map_singleOneRingHom, map_one, one_mul]

private theorem continuous_coeff_powerSeriesAlgEquiv_symm {Δ : Type*} [CommGroup Δ] [Finite Δ]
    [TopologicalSpace (MonoidAlgebra ℤ_[p] Δ)] [IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] Δ)]
    (δ : Δ) :
    Continuous fun ψ : PowerSeries (MonoidAlgebra ℤ_[p] Δ) ↦
      ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm ψ).coeff δ := by
  rw [continuous_iff_continuousAt]
  intro ψ
  refine (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ_[p] _ _ _).mpr fun n ↦ ?_
  let l : MonoidAlgebra ℤ_[p] Δ →ₗ[ℤ_[p]] ℤ_[p] :=
    (Finsupp.lapply δ).comp (MonoidAlgebra.coeffLinearEquiv ℤ_[p]).toLinearMap
  have hl (a : MonoidAlgebra ℤ_[p] Δ) : l a = a.coeff δ := rfl
  simpa only [MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, ContinuousAt,
    Function.comp_def, hl] using
    ((IsModuleTopology.continuous_of_linearMap l).comp
      (PowerSeries.WithPiTopology.continuous_coeff (MonoidAlgebra ℤ_[p] Δ) n)).continuousAt

private theorem liftNCAlgHom_powerSeriesAlgEquiv_symm_apply {Δ : Type*} [CommGroup Δ] [Fintype Δ]
    (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : Δ →* Bˣ)
    (ψ : PowerSeries (MonoidAlgebra ℤ_[p] Δ)) :
    MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) (fun _ _ ↦ Commute.all _ _)
        ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm ψ) =
      ∑ δ : Δ,
        ε (((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm ψ).coeff δ) * η δ := by
  classical
  let s := (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm
  have hs : s ψ = ∑ δ : Δ, MonoidAlgebra.single δ ((s ψ).coeff δ) := by
    rw [← Finsupp.sum_fintype _ _ (fun δ ↦ MonoidAlgebra.single_zero δ),
      MonoidAlgebra.sum_coeff_single]
  change MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) _ (s ψ) = _
  rw [hs, map_sum]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  simp

private theorem continuous_liftPowerSeriesAndFiniteChar [TopologicalSpace B] [IsTopologicalRing B]
    {ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B} (hε : Continuous ε)
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ) :
    Continuous (liftPowerSeriesAndFiniteChar ε η) := by
  let Δ := (ZMod (p ^ padicUnitsDepth p))ˣ
  let : TopologicalSpace (MonoidAlgebra ℤ_[p] Δ) := moduleTopology ℤ_[p] _
  have : IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] Δ) := ⟨rfl⟩
  have hcont : Continuous fun z : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ ↦
      ∑ δ : Δ, ε (((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm
        ((padicUnitsCoordinate p).symm z)).coeff δ) * η δ :=
    continuous_finsetSum _ fun δ _ ↦
      (hε.comp ((continuous_coeff_powerSeriesAlgEquiv_symm δ).comp
        (continuous_padicUnitsCoordinate_symm p))).mul continuous_const
  refine hcont.congr fun z ↦ ?_
  simpa only [liftPowerSeriesAndFiniteChar, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
    (liftNCAlgHom_powerSeriesAlgEquiv_symm_apply ε η ((padicUnitsCoordinate p).symm z)).symm

end LiftHelper

/-! ### Continuous evaluation of `ℤ_p⟦X⟧` in ultrametric normed algebras -/

section PadicPowerSeriesEval

variable (p : ℕ) [Fact p.Prime] {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R]
  [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R]

/-- For a topologically nilpotent element `t` of an ultrametric normed `ℤ_p`-algebra `R` with
contractive scalar action, the monomial series `∑ n, φ.coeff n • t ^ n` of any `φ ∈ ℤ_p⟦X⟧` is
summable when `R` is complete. -/
theorem summable_coeff_smul_pow [CompleteSpace R] {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) :
    Summable fun n : ℕ ↦ φ.coeff n • t ^ n := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (tendsto_zero_iff_norm_tendsto_zero.mp ht)
  calc ‖φ.coeff n • t ^ n‖
      ≤ ‖φ.coeff n‖ * ‖t ^ n‖ := norm_smul_le _ _
    _ ≤ 1 * ‖t ^ n‖ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖t ^ n‖ := one_mul _

variable [CompleteSpace R]

private theorem padicPowerSeriesEval_fun_continuous {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    Continuous fun φ : PowerSeries ℤ_[p] ↦ ∑' n : ℕ, φ.coeff n • t ^ n := by
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (half_pos hε)
  refine ⟨fun φ ↦ ∑ n ∈ Finset.range N, φ.coeff n • t ^ n,
    continuous_finsetSum _ fun n _ ↦
      ((PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] n).smul continuous_const),
    fun φ ↦ hεu ?_⟩
  rw [dist_eq_norm, ← (summable_coeff_smul_pow p ht φ).sum_add_tsum_nat_add N,
    add_sub_cancel_left]
  refine (IsUltrametricDist.norm_tsum_le_of_forall_le (C := ε / 2) fun k ↦ ?_).trans_lt
    (half_lt_self hε)
  refine le_of_lt <| lt_of_le_of_lt ?_
    (by simpa [dist_zero_right] using hN (k + N) (Nat.le_add_left N k))
  calc ‖φ.coeff (k + N) • t ^ (k + N)‖
      ≤ ‖φ.coeff (k + N)‖ * ‖t ^ (k + N)‖ := norm_smul_le _ _
    _ ≤ 1 * ‖t ^ (k + N)‖ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖t ^ (k + N)‖ := one_mul _

omit [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R] in
private theorem padicPowerSeriesEval_fun_coe {t : R} (P : Polynomial ℤ_[p]) :
    (∑' n : ℕ, (P : PowerSeries ℤ_[p]).coeff n • t ^ n) = Polynomial.aeval t P := by
  rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)), Polynomial.aeval_eq_sum_range]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Polynomial.coeff_coe]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_coe, P.coeff_eq_zero_of_natDegree_lt hn, zero_smul]

/-- **Evaluation of integral power series at a topologically nilpotent element** of a complete
ultrametric normed commutative `ℤ_p`-algebra `R` with contractive scalar action:
`φ ↦ ∑' n, φ.coeff n • t ^ n` as a `ℤ_p`-algebra homomorphism `ℤ_p⟦X⟧ →ₐ[ℤ_p] R`. -/
noncomputable def padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    PowerSeries ℤ_[p] →ₐ[ℤ_[p]] R where
  toFun φ := ∑' n : ℕ, φ.coeff n • t ^ n
  map_one' := by
    simpa only [Polynomial.coe_one, map_one] using padicPowerSeriesEval_fun_coe p (t := t) 1
  map_mul' := by
    have hcont := padicPowerSeriesEval_fun_continuous p ht
    have hmul : (fun q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] ↦
        ∑' n : ℕ, (q.1 * q.2).coeff n • t ^ n) =
        fun q ↦ (∑' n : ℕ, q.1.coeff n • t ^ n) * (∑' n : ℕ, q.2.coeff n • t ^ n) :=
      ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).prodMap
        (PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p])).equalizer
        (hcont.comp continuous_mul)
        ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd))
        (funext fun ⟨P, Q⟩ ↦ by
          simp only [Function.comp_apply, Prod.map_apply, ← Polynomial.coe_mul,
            padicPowerSeriesEval_fun_coe p (t := t), map_mul])
    exact fun φ ψ ↦ congrFun hmul (φ, ψ)
  map_zero' := by simp
  map_add' φ ψ := by
    simp only [map_add, add_smul]
    exact (summable_coeff_smul_pow p ht φ).tsum_add (summable_coeff_smul_pow p ht ψ)
  commutes' a := by
    rw [← PowerSeries.C_eq_algebraMap, ← Polynomial.coe_C, padicPowerSeriesEval_fun_coe p,
      Polynomial.aeval_C]

theorem padicPowerSeriesEval_apply {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) :
    padicPowerSeriesEval p ht φ = ∑' n : ℕ, φ.coeff n • t ^ n :=
  (rfl)

theorem hasSum_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ φ.coeff n • t ^ n) (padicPowerSeriesEval p ht φ) :=
  (summable_coeff_smul_pow p ht φ).hasSum

/-- `padicPowerSeriesEval p ht` is continuous from the coefficientwise `p`-adic topology on
`ℤ_p⟦X⟧` to the norm topology on `R`. -/
theorem continuous_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    Continuous (padicPowerSeriesEval p ht) :=
  padicPowerSeriesEval_fun_continuous p ht

@[simp]
theorem padicPowerSeriesEval_X {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    padicPowerSeriesEval p ht PowerSeries.X = t := by
  rw [padicPowerSeriesEval_apply]
  simpa only [Polynomial.coe_X, Polynomial.aeval_X] using
    padicPowerSeriesEval_fun_coe p (t := t) Polynomial.X

@[simp]
theorem padicPowerSeriesEval_C {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) (a : ℤ_[p]) :
    padicPowerSeriesEval p ht (PowerSeries.C a) = algebraMap ℤ_[p] R a := by
  rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes]

/-- Evaluating the binomial series `(1 + X) ^ s` (`s ∈ ℤ_p`) at a topologically nilpotent element
`t` recovers Mathlib's continuous binomial character `PadicInt.addChar_of_value_at_one t ht s`. -/
@[simp]
theorem padicPowerSeriesEval_binomialSeries {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (s : ℤ_[p]) :
    padicPowerSeriesEval p ht (PowerSeries.binomialSeries ℤ_[p] s) =
      PadicInt.addChar_of_value_at_one t ht s := by
  rw [padicPowerSeriesEval_apply, PadicInt.coe_addChar_of_value_at_one,
    PadicInt.mahlerSeries_apply ht]
  refine tsum_congr fun n ↦ ?_
  rw [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, mahler_apply]

end PadicPowerSeriesEval

namespace WeightSpace

variable {p : ℕ} [Fact p.Prime]

section Universal

variable (p) in
/-- **The universal weight of `ℤ_pˣ`.** It sends `x ∈ ℤ_pˣ` to the unit `[x]` in the completed
group algebra `ℤ_p[[ℤ_pˣ]]`. -/
noncomputable def universal : WeightSpace p (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) where
  toMonoidHom := (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ).toHomUnits
  continuous_toFun := by
    let f := (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ).toHomUnits
    have hf : Continuous fun x : ℤ_[p]ˣ ↦ (f x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :=
      completedGroupAlgebra.continuous_of ℤ_[p] ℤ_[p]ˣ
    exact Units.continuous_iff.mpr
      ⟨hf, (hf.comp continuous_inv).congr fun x ↦ congrArg Units.val (map_inv f x)⟩

@[simp]
theorem coe_universal_apply (x : ℤ_[p]ˣ) :
    (universal p x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x :=
  (rfl)

theorem coe_universal_finiteChar_apply (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    ((universal p).finiteChar δ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [finiteChar_apply, coe_universal_apply]

@[simp]
theorem universal_coord :
    (universal p).coord =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1 := by
  rw [coord_def, coe_universal_apply]

@[simp]
theorem universal_coordAt (u : ℤ_[p]ˣ) :
    (universal p).coordAt u =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ
        ((unitsPrincipalLogEquiv p).symm (.ofAdd (u : ℤ_[p]))) - 1 := by
  rw [coordAt_eq_principalChar_sub_one, principalChar_apply, coe_universal_apply]

/-- Every continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` restricts along the universal weight
to a weight in the target ring. -/
noncomputable def ofContinuousRingHom {R : Type*} [Ring R] [TopologicalSpace R]
    (φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) (hφ : Continuous φ) :
    WeightSpace p R where
  toMonoidHom := (Units.map φ.toMonoidHom).comp (universal p).toMonoidHom
  continuous_toFun := (Continuous.units_map _ hφ).comp (universal p).continuous

@[simp]
theorem coe_ofContinuousRingHom_apply {R : Type*} [Ring R] [TopologicalSpace R]
    (φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) (hφ : Continuous φ) (x : ℤ_[p]ˣ) :
    (ofContinuousRingHom φ hφ x : R) = φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) :=
  (rfl)

theorem coe_ofContinuousRingHom_finiteChar_apply {R : Type*} [Ring R] [TopologicalSpace R]
    (φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) (hφ : Continuous φ)
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    ((ofContinuousRingHom φ hφ).finiteChar δ : R) =
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) := by
  rw [finiteChar_apply, coe_ofContinuousRingHom_apply]

@[simp]
theorem ofContinuousRingHom_coord {R : Type*} [Ring R] [TopologicalSpace R]
    (φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) (hφ : Continuous φ) :
    (ofContinuousRingHom φ hφ).coord =
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) := by
  rw [coord_def, coe_ofContinuousRingHom_apply, map_sub, map_one]

/-- Over an ultrametric normed `ℤ_p`-algebra with contractive action, no continuous ring
homomorphism out of `ℤ_p[[ℤ_pˣ]]` can send `[γ] - 1` to an element whose powers do not tend to
zero. -/
theorem not_exists_continuous_ringHom_of_not_tendsto_pow {R : Type*} [NormedRing R]
    [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] {z : R}
    (hz : ¬Tendsto (z ^ ·) atTop (𝓝 0)) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  rintro ⟨φ, hφ, hφz⟩
  rw [← hφz, ← ofContinuousRingHom_coord φ hφ] at hz
  exact hz (ofContinuousRingHom φ hφ).tendsto_coord_pow

/-- Over a normed division `ℚ_p`-algebra `K`, no continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]`
can send `[γ] - 1` to an element of norm at least `1`. -/
theorem not_exists_continuous_ringHom_of_one_le_norm {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] {z : K} (hz : 1 ≤ ‖z‖) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  rintro ⟨φ, hφ, hφz⟩
  rw [← hφz, ← ofContinuousRingHom_coord φ hφ] at hz
  exact not_lt_of_ge hz (norm_coord_lt_one_of_normedAlgebra (ofContinuousRingHom φ hφ))

end Universal

/-! ### Adic specialisation into complete linearly topologised `ℤ_p`-algebras -/

section Adic

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [Algebra ℤ_[p] S]
  [ContinuousSMul ℤ_[p] S]

/-- **Adic specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight.** Over a complete separated linearly
topologised commutative `ℤ_p`-algebra `S`, a weight `κ : WeightSpace p S` extends to a continuous
`ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S` via `PowerSeries.aeval κ.hasEval_coord` on the
principal factor and `κ.finiteChar` on `Δ`. -/
noncomputable def adicSpecialize (κ : WeightSpace p S) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S :=
  liftPowerSeriesAndFiniteChar (PowerSeries.aeval κ.hasEval_coord) κ.finiteChar

/-- `adicSpecialize κ` is continuous from the inverse-limit topology on `ℤ_p[[ℤ_pˣ]]` to `S`. -/
theorem continuous_adicSpecialize (κ : WeightSpace p S) : Continuous κ.adicSpecialize :=
  continuous_liftPowerSeriesAndFiniteChar (PowerSeries.continuous_aeval κ.hasEval_coord)
    κ.finiteChar

@[simp]
theorem adicSpecialize_of (κ : WeightSpace p S) (x : ℤ_[p]ˣ) :
    κ.adicSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
  rw [adicSpecialize, liftPowerSeriesAndFiniteChar_of,
    ← κ.apply_eq_finiteChar_mul_aeval_binomialSeries]

@[simp]
theorem adicSpecialize_coord (κ : WeightSpace p S) :
    κ.adicSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by
  rw [map_sub, map_one, adicSpecialize_of, coord_def]

theorem adicSpecialize_padicUnitsCoordinate_X (κ : WeightSpace p S) :
    κ.adicSpecialize (padicUnitsCoordinate p PowerSeries.X) = κ.coord := by
  rw [adicSpecialize, liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_X, PowerSeries.aeval_X]

theorem adicSpecialize_padicUnitsCoordinate_C_single (κ : WeightSpace p S)
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    κ.adicSpecialize (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))) =
      algebraMap ℤ_[p] S a * κ.finiteChar δ :=
  liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_C_single _ _ δ a

theorem adicSpecialize_padicUnitsCoordinate_map_singleOneRingHom (κ : WeightSpace p S)
    (φ : PowerSeries ℤ_[p]) :
    κ.adicSpecialize
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      PowerSeries.aeval κ.hasEval_coord φ :=
  liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_map_singleOneRingHom _ _ φ

@[simp]
theorem ofContinuousRingHom_adicSpecialize (κ : WeightSpace p S) :
    ofContinuousRingHom (κ.adicSpecialize : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S)
        κ.continuous_adicSpecialize = κ := by
  ext x
  exact κ.adicSpecialize_of x

/-- Any continuous `ℤ_p`-algebra homomorphism `φ : ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S` agreeing with `κ` on
`ℤ_pˣ` equals `κ.adicSpecialize`. -/
theorem eq_adicSpecialize_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S}
    (hφ : Continuous φ) (κ : WeightSpace p S)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.adicSpecialize :=
  completedGroupAlgebra_algHom_ext hφ κ.continuous_adicSpecialize fun x ↦
    (h x).trans (κ.adicSpecialize_of x).symm

/-- **The adic universal property of `ℤ_p[[ℤ_pˣ]]`.** Weights in a complete separated linearly
topologised commutative `ℤ_p`-algebra `S` correspond bijectively to continuous `ℤ_p`-algebra
homomorphisms `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S`. -/
noncomputable def adicSpecializeEquiv :
    WeightSpace p S ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S // Continuous φ} where
  toFun κ := ⟨κ.adicSpecialize, κ.continuous_adicSpecialize⟩
  invFun φ := ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S) φ.2
  left_inv κ := κ.ofContinuousRingHom_adicSpecialize
  right_inv φ := Subtype.ext <| (eq_adicSpecialize_of_continuous φ.2 _ fun _ ↦ rfl).symm

/-- Over a complete separated linearly topologised commutative `ℤ_p`-algebra `S`, every finite
character `η : Δ →* Sˣ` and evaluable element `z ∈ S` determine a unique continuous `ℤ_p`-algebra
homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ z`. -/
theorem existsUnique_continuous_algHom_of_hasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ)
    {z : S} (hz : PowerSeries.HasEval z) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S,
      Continuous φ ∧
        (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
        φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  refine ⟨(ofHasEval η hz).adicSpecialize, ⟨(ofHasEval η hz).continuous_adicSpecialize, ?_, ?_⟩,
    fun φ ⟨hφ, hη, hz'⟩ ↦ ?_⟩
  · intro δ
    rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval]
  · rw [adicSpecialize_coord, coord_ofHasEval]
  · have hκ : ofContinuousRingHom φ.toRingHom hφ = ofHasEval η hz := by
      refine ext_finiteChar_coord ?_ ?_
      · ext δ
        simpa using hη δ
      · simpa using hz'
    exact eq_adicSpecialize_of_continuous hφ (ofHasEval η hz) fun x ↦ by
      rw [← hκ, coe_ofContinuousRingHom_apply]
      rfl

/-- Adic specialisation at the universal weight is the identity on `ℤ_p[[ℤ_pˣ]]`. -/
@[simp]
theorem adicSpecialize_universal :
    (universal p).adicSpecialize = AlgHom.id ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :=
  (eq_adicSpecialize_of_continuous (φ := AlgHom.id ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ))
    continuous_id (universal p) fun x ↦ (coe_universal_apply x).symm).symm

end Adic

/-! ### Normed specialisation into complete ultrametric normed `ℤ_p`-algebras -/

section Normed

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- **Normed specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight.** Over a complete ultrametric normed
commutative `ℤ_p`-algebra `R` with contractive scalar action, a weight `κ : WeightSpace p R`
extends to a continuous `ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R` via
`TauCeti.padicPowerSeriesEval p κ.tendsto_coord_pow` on the principal factor and `κ.finiteChar` on
`Δ`. -/
noncomputable def normedSpecialize (κ : WeightSpace p R) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R :=
  liftPowerSeriesAndFiniteChar (padicPowerSeriesEval p κ.tendsto_coord_pow) κ.finiteChar

/-- `normedSpecialize κ` is continuous from the inverse-limit topology on `ℤ_p[[ℤ_pˣ]]` to the
norm topology on `R`. -/
theorem continuous_normedSpecialize (κ : WeightSpace p R) : Continuous κ.normedSpecialize :=
  continuous_liftPowerSeriesAndFiniteChar (continuous_padicPowerSeriesEval p κ.tendsto_coord_pow)
    κ.finiteChar

@[simp]
theorem normedSpecialize_of (κ : WeightSpace p R) (x : ℤ_[p]ˣ) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
  rw [normedSpecialize, liftPowerSeriesAndFiniteChar_of, padicPowerSeriesEval_binomialSeries,
    ← κ.principalChar_eq_addChar_of_value_at_one, ← κ.apply_eq_finiteChar_mul_principalChar]

@[simp]
theorem normedSpecialize_coord (κ : WeightSpace p R) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by
  rw [map_sub, map_one, normedSpecialize_of, coord_def]

theorem normedSpecialize_padicUnitsCoordinate_X (κ : WeightSpace p R) :
    κ.normedSpecialize (padicUnitsCoordinate p PowerSeries.X) = κ.coord := by
  rw [normedSpecialize, liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_X,
    padicPowerSeriesEval_X]

theorem normedSpecialize_padicUnitsCoordinate_C_single (κ : WeightSpace p R)
    (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    κ.normedSpecialize (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))) =
      algebraMap ℤ_[p] R a * κ.finiteChar δ :=
  liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_C_single _ _ δ a

theorem normedSpecialize_padicUnitsCoordinate_map_singleOneRingHom (κ : WeightSpace p R)
    (φ : PowerSeries ℤ_[p]) :
    κ.normedSpecialize
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      padicPowerSeriesEval p κ.tendsto_coord_pow φ :=
  liftPowerSeriesAndFiniteChar_padicUnitsCoordinate_map_singleOneRingHom _ _ φ

private theorem hasSum_liftNCAlgHom_padicPowerSeriesEval
    {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp η) (F.coeff n) * t ^ n)
      (MonoidAlgebra.liftNCAlgHom (padicPowerSeriesEval p ht) ((Units.coeHom R).comp η)
        (fun _ _ ↦ Commute.all _ _)
        ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p]
          (ZMod (p ^ padicUnitsDepth p))ˣ).symm F)) := by
  rw [liftNCAlgHom_powerSeriesAlgEquiv_symm_apply]
  refine (hasSum_sum fun δ _ ↦
    (hasSum_padicPowerSeriesEval p ht _).mul_right (η δ : R)).congr_fun fun n ↦ ?_
  rw [MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (fun δ ↦ zero_smul ℤ_[p] (((Units.coeHom R).comp η) δ)),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  rw [MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, MonoidHom.comp_apply,
    Units.coeHom_apply, Algebra.smul_def, Algebra.smul_def, mul_right_comm]

/-- **Power-series expansion of normed specialisation.** In weight coordinates
`padicUnitsCoordinate p : (ℤ_p[Δ])⟦X⟧ ≃ₐ[ℤ_p] ℤ_p[[ℤ_pˣ]]`, specialising `F = ∑ n, c_n X^n` at `κ`
is the convergent series `∑ n, κ_Δ(c_n) · T_κ ^ n`. -/
theorem hasSum_normedSpecialize_padicUnitsCoordinate (κ : WeightSpace p R)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n)
      (κ.normedSpecialize (padicUnitsCoordinate p F)) := by
  simpa only [normedSpecialize, liftPowerSeriesAndFiniteChar, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    hasSum_liftNCAlgHom_padicPowerSeriesEval κ.tendsto_coord_pow κ.finiteChar F

theorem normedSpecialize_padicUnitsCoordinate_eq_tsum (κ : WeightSpace p R)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    κ.normedSpecialize (padicUnitsCoordinate p F) = ∑' n : ℕ,
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n :=
  (κ.hasSum_normedSpecialize_padicUnitsCoordinate F).tsum_eq.symm

@[simp]
theorem ofContinuousRingHom_normedSpecialize (κ : WeightSpace p R) :
    ofContinuousRingHom (κ.normedSpecialize : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R)
        κ.continuous_normedSpecialize = κ := by
  ext x
  exact κ.normedSpecialize_of x

/-- Any continuous `ℤ_p`-algebra homomorphism `φ : ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R` agreeing with `κ` on
`ℤ_pˣ` equals `κ.normedSpecialize`. -/
theorem eq_normedSpecialize_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R}
    (hφ : Continuous φ) (κ : WeightSpace p R)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.normedSpecialize :=
  completedGroupAlgebra_algHom_ext hφ κ.continuous_normedSpecialize fun x ↦
    (h x).trans (κ.normedSpecialize_of x).symm

/-- **The normed universal property of `ℤ_p[[ℤ_pˣ]]`.** Weights in a complete ultrametric normed
commutative `ℤ_p`-algebra `R` with contractive scalar action correspond bijectively to continuous
`ℤ_p`-algebra homomorphisms `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R`. -/
noncomputable def normedSpecializeEquiv :
    WeightSpace p R ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R // Continuous φ} where
  toFun κ := ⟨κ.normedSpecialize, κ.continuous_normedSpecialize⟩
  invFun φ := ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) φ.2
  left_inv κ := κ.ofContinuousRingHom_normedSpecialize
  right_inv φ := Subtype.ext <| (eq_normedSpecialize_of_continuous φ.2 _ fun _ ↦ rfl).symm

/-- Over a complete ultrametric normed commutative `ℤ_p`-algebra `R` with contractive scalar
action, every finite character `η : Δ →* Rˣ` and topologically nilpotent element `t ∈ R` determine
a unique continuous `ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R` sending `[ω(δ)] ↦ η(δ)` and
`[γ] - 1 ↦ t`. -/
theorem existsUnique_continuous_algHom_of_tendsto_pow
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R,
      Continuous φ ∧
        (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
        φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t := by
  refine ⟨(ofCoord η t ht).normedSpecialize, ⟨(ofCoord η t ht).continuous_normedSpecialize, ?_, ?_⟩,
    fun φ ⟨hφ, hη, ht'⟩ ↦ ?_⟩
  · intro δ
    rw [normedSpecialize_of, ← finiteChar_apply, finiteChar_ofCoord]
  · rw [normedSpecialize_coord, coord_ofCoord]
  · have hκ : ofContinuousRingHom φ.toRingHom hφ = ofCoord η t ht := by
      refine ext_finiteChar_coord ?_ ?_
      · ext δ
        simpa using hη δ
      · simpa using ht'
    exact eq_normedSpecialize_of_continuous hφ (ofCoord η t ht) fun x ↦ by
      rw [← hκ, coe_ofContinuousRingHom_apply]
      rfl

/-- When `‖t‖ < 1` (the open unit disc condition over normed fields), `t` is automatically
topologically nilpotent, so `η` and `t` determine a unique continuous `ℤ_p`-algebra homomorphism
out of `ℤ_p[[ℤ_pˣ]]`. -/
theorem existsUnique_continuous_algHom_of_norm_lt_one
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) {t : R} (ht : ‖t‖ < 1) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R,
      Continuous φ ∧
        (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
        φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t :=
  existsUnique_continuous_algHom_of_tendsto_pow η (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)

/-! #### Generator-change compatibility and concrete specialisations -/

theorem normedSpecialize_padicUnitsCoordinateAt_X (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.normedSpecialize (padicUnitsCoordinateAt p u PowerSeries.X) = κ.coordAt u := by
  rw [padicUnitsCoordinateAt_X, map_sub, map_one, normedSpecialize_of,
    κ.coordAt_eq_principalChar_sub_one, principalChar_apply]

/-- Substituting `(1 + X) ^ u - 1` before evaluating at `κ.coord` equals evaluating directly at the
changed coordinate `κ.coordAt u = (1 + κ.coord) ^ u - 1`. -/
theorem padicPowerSeriesEval_subst_binomialSeries_sub_one (κ : WeightSpace p R) (u : ℤ_[p]ˣ)
    (φ : PowerSeries ℤ_[p]) :
    padicPowerSeriesEval p κ.tendsto_coord_pow
        (φ.subst (PowerSeries.binomialSeries ℤ_[p] (u : ℤ_[p]) - 1)) =
      padicPowerSeriesEval p (κ.tendsto_coordAt_pow u) φ := by
  let b : PowerSeries ℤ_[p] := PowerSeries.binomialSeries ℤ_[p] (u : ℤ_[p]) - 1
  have hb : PowerSeries.HasSubst b := hasSubst_binomialSeries_sub_one (S := ℤ_[p]) (u : ℤ_[p])
  let L : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] R :=
    (padicPowerSeriesEval p κ.tendsto_coord_pow).comp (PowerSeries.substAlgHom hb)
  have hL_cont : Continuous L :=
    ((continuous_padicPowerSeriesEval p κ.tendsto_coord_pow).comp <|
      continuous_id.powerSeries_subst_binomialSeries_sub_one
        (continuous_const : Continuous fun _ : PowerSeries ℤ_[p] ↦ (u : ℤ_[p]))).congr
      fun ψ ↦ by simp [L, b, PowerSeries.coe_substAlgHom]
  have hLX : L PowerSeries.X = κ.coordAt u := by
    dsimp only [L, b]
    rw [AlgHom.comp_apply, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hb, map_sub, map_one,
      padicPowerSeriesEval_binomialSeries, κ.coordAt_eq_weightCoordChangeEquiv u,
      coe_weightCoordChangeEquiv_apply]
  have heq : ⇑L = ⇑(padicPowerSeriesEval p (κ.tendsto_coordAt_pow u)) :=
    (PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer hL_cont
      (continuous_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u)) <| funext fun P ↦ by
        simp only [Function.comp_apply]
        rw [PowerSeries.algHom_coe_eq_aeval, PowerSeries.algHom_coe_eq_aeval, hLX,
          padicPowerSeriesEval_X]
  simpa [L, b, PowerSeries.coe_substAlgHom] using congrFun heq φ

/-- **Generator-change series expansion.** Specialising `padicUnitsCoordinateAt p u F` at `κ`
evaluates the same finite-part coefficients against powers of the new coordinate `κ.coordAt u`. -/
theorem hasSum_normedSpecialize_padicUnitsCoordinateAt (κ : WeightSpace p R) (u : ℤ_[p]ˣ)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coordAt u ^ n)
      (κ.normedSpecialize (padicUnitsCoordinateAt p u F)) := by
  let Δ := (ZMod (p ^ padicUnitsDepth p))ˣ
  let : TopologicalSpace (MonoidAlgebra ℤ_[p] Δ) := moduleTopology ℤ_[p] _
  have : IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] Δ) := ⟨rfl⟩
  let s := (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm
  let L₁ : PowerSeries (MonoidAlgebra ℤ_[p] Δ) →ₐ[ℤ_[p]] R :=
    κ.normedSpecialize.comp (padicUnitsCoordinateAt p u).toAlgHom
  let L₂ : PowerSeries (MonoidAlgebra ℤ_[p] Δ) →ₐ[ℤ_[p]] R :=
    (MonoidAlgebra.liftNCAlgHom (padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
      ((Units.coeHom R).comp κ.finiteChar) fun _ _ ↦ Commute.all _ _).comp s.toAlgHom
  have hL₂_cont : Continuous L₂ := by
    have hcont : Continuous fun ψ : PowerSeries (MonoidAlgebra ℤ_[p] Δ) ↦
        ∑ δ : Δ, padicPowerSeriesEval p (κ.tendsto_coordAt_pow u) ((s ψ).coeff δ) *
          κ.finiteChar δ :=
      continuous_finsetSum _ fun δ _ ↦
        ((continuous_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u)).comp
          (continuous_coeff_powerSeriesAlgEquiv_symm δ)).mul continuous_const
    refine hcont.congr fun ψ ↦ ?_
    simpa only [L₂, s, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
      (liftNCAlgHom_powerSeriesAlgEquiv_symm_apply
        (padicPowerSeriesEval p (κ.tendsto_coordAt_pow u)) κ.finiteChar ψ).symm
  have hL_eq : ⇑L₁ = ⇑L₂ := by
    refine (PowerSeries.WithPiTopology.denseRange_toPowerSeries (MonoidAlgebra ℤ_[p] Δ)).equalizer
      (κ.continuous_normedSpecialize.comp (continuous_padicUnitsCoordinateAt p u)) hL₂_cont
      (funext fun P ↦ ?_)
    simp only [Function.comp_apply]
    induction P using Polynomial.induction_on' with
    | add f g hf hg => simp [Polynomial.coe_add, map_add, hf, hg]
    | monomial n r =>
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_mul,
        map_pow, map_pow]
      congr 1
      · induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add x y hx hy => simp [map_add, hx, hy]
        | single δ a =>
          dsimp only [L₁, L₂, s]
          rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, padicUnitsCoordinateAt_C_single,
            map_mul, AlgHom.commutes, normedSpecialize_of, ← finiteChar_apply,
            AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
            MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single,
            MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single]
          simp [PowerSeries.C_eq_algebraMap]
      · congr 1
        dsimp only [L₁, L₂, s]
        rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, normedSpecialize_padicUnitsCoordinateAt_X,
          AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MonoidAlgebra.powerSeriesAlgEquiv_symm_X,
          MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single]
        simp
  have hval : κ.normedSpecialize (padicUnitsCoordinateAt p u F) = L₂ F := congrFun hL_eq F
  simpa only [hval, L₂, s, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
    hasSum_liftNCAlgHom_padicPowerSeriesEval (κ.tendsto_coordAt_pow u) κ.finiteChar F

/-- Specialising at the trivial weight `1` is the augmentation map: on weight coordinates it
augments the constant term of `F` and kills all positive powers of `X`. -/
theorem normedSpecialize_one_padicUnitsCoordinate
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    (1 : WeightSpace p R).normedSpecialize (padicUnitsCoordinate p F) =
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ 1
        (PowerSeries.constantCoeff F) := by
  rw [normedSpecialize_padicUnitsCoordinate_eq_tsum, coord_one,
    tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  have h1 : ((Units.coeHom R).comp (1 : WeightSpace p R).finiteChar) = 1 := by
    ext δ
    simp
  rw [h1, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]

end Normed

/-! ### Adic and normed agreement -/

section AdicNormed

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [IsLinearTopology S S] [Algebra ℤ_[p] S] [IsBoundedSMul ℤ_[p] S]

/-- **Agreement of adic and normed specialisations.** When `S` is a complete ultrametric normed
commutative `ℤ_p`-algebra whose topology is also linear (for instance `ℤ_p`), `adicSpecialize` and
`normedSpecialize` agree on all of `ℤ_p[[ℤ_pˣ]]`. -/
theorem adicSpecialize_eq_normedSpecialize (κ : WeightSpace p S) :
    κ.adicSpecialize = κ.normedSpecialize :=
  completedGroupAlgebra_algHom_ext κ.continuous_adicSpecialize κ.continuous_normedSpecialize
    fun x ↦ (κ.adicSpecialize_of x).trans (κ.normedSpecialize_of x).symm

end AdicNormed

/-! ### Specialisation for ultrametric normed `ℚ_p`-algebras -/

section NormedPadicAlgebra

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight in a complete ultrametric normed commutative
`ℚ_p`-algebra `K`** (such as `ℚ_p`, `ℂ_p`, or `TauCeti.MaxDualNumber ℚ_[p]`), bundled as a ring
homomorphism so no `Algebra ℤ_[p] K` instance is required in the signature. -/
noncomputable def specializeRingHom (κ : WeightSpace p K) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K :=
  let : Algebra ℤ_[p] K := Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
  have : IsBoundedSMul ℤ_[p] K := .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x
  κ.normedSpecialize.toRingHom

theorem continuous_specializeRingHom (κ : WeightSpace p K) : Continuous κ.specializeRingHom := by
  let : Algebra ℤ_[p] K := Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
  have : IsBoundedSMul ℤ_[p] K := .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x
  exact κ.continuous_normedSpecialize

@[simp]
theorem specializeRingHom_of (κ : WeightSpace p K) (x : ℤ_[p]ˣ) :
    κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
  let : Algebra ℤ_[p] K := Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
  have : IsBoundedSMul ℤ_[p] K := .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x
  exact κ.normedSpecialize_of x

@[simp]
theorem specializeRingHom_algebraMap (κ : WeightSpace p K) (a : ℤ_[p]) :
    κ.specializeRingHom (algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a) =
      padicIntAlgebraMap p K a := by
  let : Algebra ℤ_[p] K := Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
  have : IsBoundedSMul ℤ_[p] K := .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x
  change κ.normedSpecialize (algebraMap ℤ_[p] _ a) = padicIntAlgebraMap p K a
  rw [κ.normedSpecialize.commutes, Algebra.compHom_algebraMap_apply, padicIntAlgebraMap_apply]
  simp [PadicInt.algebraMap_eq_coe_ringHom]

@[simp]
theorem specializeRingHom_coord (κ : WeightSpace p K) :
    κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by
  rw [map_sub, map_one, specializeRingHom_of, coord_def]

@[simp]
theorem ofContinuousRingHom_specializeRingHom (κ : WeightSpace p K) :
    ofContinuousRingHom κ.specializeRingHom κ.continuous_specializeRingHom = κ := by
  ext x
  exact κ.specializeRingHom_of x

/-- Any continuous ring homomorphism `φ : ℤ_p[[ℤ_pˣ]] →+* K` agreeing with `κ` on `ℤ_pˣ` equals
`κ.specializeRingHom`. -/
theorem eq_specializeRingHom_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K}
    (hφ : Continuous φ) (κ : WeightSpace p K)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.specializeRingHom :=
  completedGroupAlgebra_ringHom_ext hφ κ.continuous_specializeRingHom fun x ↦
    (h x).trans (κ.specializeRingHom_of x).symm

/-- When `K` also carries a contractive `ℤ_p`-algebra structure, `normedSpecialize` and
`specializeRingHom` agree as ring homomorphisms on all of `ℤ_p[[ℤ_pˣ]]` (with no scalar-tower
assumption needed, since `ℕ` is dense in `ℤ_p`). -/
theorem coe_normedSpecialize_eq_specializeRingHom [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
    (κ : WeightSpace p K) :
    κ.normedSpecialize.toRingHom = κ.specializeRingHom :=
  eq_specializeRingHom_of_continuous κ.continuous_normedSpecialize κ κ.normedSpecialize_of

/-- Specialising `[x]` at the algebraic weight `inclusion K ^ k` gives `x ^ k` in `K`. -/
theorem specializeRingHom_inclusion_pow_of (k : ℕ) (x : ℤ_[p]ˣ) :
    ((inclusion (p := p) K ^ k).specializeRingHom)
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      padicIntAlgebraMap p K x ^ k := by
  simp [ContinuousMonoidHom.pow_apply]

end NormedPadicAlgebra

/-! ### Concrete checks: infinite series, nilpotents of norm `1`, and `p = 2` -/

section Checks

/-- The inverse of `1 + X` in `ℤ_p⟦X⟧` is not in the image of `Polynomial ℤ_p`: `1 + X` has no
polynomial inverse, whereas `[γ⁻¹] = padicUnitsCoordinate p (1 + X)⁻¹` specialises at every weight
`κ` to `(1 + κ.coord)⁻¹`. -/
theorem not_exists_polynomial_one_add_X_mul_eq_one :
    ¬∃ P : Polynomial ℤ_[p],
      (1 + PowerSeries.X : PowerSeries ℤ_[p]) * (P : PowerSeries ℤ_[p]) = 1 := by
  rintro ⟨P, hP⟩
  by_cases hP0 : P = 0
  · subst hP0
    have h0 := congrArg (PowerSeries.coeff 0) hP
    simp at h0
  · have hd := congrArg (PowerSeries.coeff (P.natDegree + 1)) hP
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, Polynomial.coeff_coe,
      Polynomial.coeff_coe, P.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_add,
      Polynomial.coeff_natDegree] at hd
    simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hd
    exact Polynomial.leadingCoeff_ne_zero.mpr hP0 hd

/-- Specialising `[γ⁻¹]` at any weight `κ` evaluates the non-polynomial series `(1 + X)⁻¹` to the
unit `(κ γ)⁻¹` with value `(1 + κ.coord)⁻¹`. -/
theorem normedSpecialize_of_padicUnitsGenerator_inv {R : Type*} [NormedCommRing R]
    [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (κ : WeightSpace p R) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)⁻¹) *
        (1 + κ.coord) = 1 := by
  have h1 : 1 + κ.coord = κ.normedSpecialize
      (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)) := by
    rw [normedSpecialize_of, coord_def, add_sub_cancel]
  rw [h1, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

/-- In the nonreduced ultrametric Banach algebra `MaxDualNumber ℚ_[p]`, the nilpotent generator
`ε` has norm `1` (`‖ε‖ = 1`), yet its powers vanish from degree `2` onwards, so `ofCoord 1 ε _` is
a genuine weight whose specialisation truncates every series `φ ∈ ℤ_p⟦X⟧` to its first-order Taylor
jet `φ(0) + φ'(0) ε`. -/
theorem normedSpecialize_maxDualNumber_eps (φ : PowerSeries ℤ_[p]) :
    have hε : Tendsto ((MaxDualNumber.eps : MaxDualNumber ℚ_[p]) ^ ·) atTop (𝓝 0) :=
      tendsto_atTop_of_eventually_const (i₀ := 2) fun n hn ↦ by
        obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := Nat.exists_eq_add_of_le hn
        rw [pow_add, sq, MaxDualNumber.eps_mul_eps, zero_mul]
    (ofCoord (p := p) 1 MaxDualNumber.eps hε).normedSpecialize
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      algebraMap ℤ_[p] (MaxDualNumber ℚ_[p]) (φ.coeff 0) +
        φ.coeff 1 • (MaxDualNumber.eps : MaxDualNumber ℚ_[p]) := by
  intro hε
  rw [normedSpecialize_padicUnitsCoordinate_map_singleOneRingHom]
  have hc : (ofCoord (p := p) 1 MaxDualNumber.eps hε).coord = MaxDualNumber.eps :=
    coord_ofCoord _ _ _
  rw [padicPowerSeriesEval_apply, tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, hc, pow_zero, pow_one,
      Algebra.algebraMap_eq_smul_one]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := Nat.exists_eq_add_of_le hn
    rw [hc, pow_add, sq, MaxDualNumber.eps_mul_eps, zero_mul, smul_zero]

/-- Comparing adic specialisation into `ℤ_p` at `p` with normed specialisation into `ℚ_p` at `p`:
applying `algebraMap ℤ_[p] ℚ_[p]` to the adic specialisation at `(p : ℤ_[p])` agrees with the
normed specialisation at `(p : ℚ_[p])`. -/
theorem algebraMap_adicSpecialize_padic_eq_normedSpecialize
    (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :
    have hpZ : PowerSeries.HasEval (p : ℤ_[p]) :=
      Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr dvd_rfl
    have hpQ : Tendsto (((p : ℚ_[p]) ^ ·)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one)
    algebraMap ℤ_[p] ℚ_[p] ((ofHasEval (p := p) 1 hpZ).adicSpecialize x) =
      (ofCoord (p := p) 1 (p : ℚ_[p]) hpQ).normedSpecialize x := by
  intro hpZ hpQ
  let φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] ℚ_[p] :=
    (Algebra.ofId ℤ_[p] ℚ_[p]).comp (ofHasEval (p := p) 1 hpZ).adicSpecialize
  have hφ_cont : Continuous φ :=
    (PadicInt.isEmbedding_coe_ringHom.continuous.comp
      (ofHasEval (p := p) 1 hpZ).continuous_adicSpecialize).congr fun z ↦ by
        simp [φ, PadicInt.algebraMap_eq_coe_ringHom]
  have heq : φ = (ofCoord (p := p) 1 (p : ℚ_[p]) hpQ).normedSpecialize := by
    refine (existsUnique_continuous_algHom_of_tendsto_pow (p := p) (R := ℚ_[p]) 1 hpQ).unique
      ⟨hφ_cont, ?_, ?_⟩
      ⟨(ofCoord (p := p) 1 (p : ℚ_[p]) hpQ).continuous_normedSpecialize,
        fun δ ↦ by rw [normedSpecialize_of, ← finiteChar_apply, finiteChar_ofCoord],
        by rw [normedSpecialize_coord, coord_ofCoord]⟩
    · intro δ
      simp [φ, adicSpecialize_of, ← finiteChar_apply]
    · simp [φ, adicSpecialize_coord]
  exact AlgHom.congr_fun heq x

/-- For `p = 2`, the nontrivial finite character `padicUnitsSection 2 : (ℤ/4ℤ)ˣ →* ℤ_2ˣ` sends the
nontrivial class `-1` to `-1 ∈ ℤ_2ˣ`, so the two dyadic sign weights separate `[ω(-1)]` even though
`ℤ_2[[ℤ_2ˣ]]` is local and does not split integrally. -/
theorem dyadic_sign_specializations_separate :
    have h0 : PowerSeries.HasEval (0 : ℤ_[2]) := isTopologicallyNilpotent_zero
    (ofHasEval (p := 2) 1 h0).adicSpecialize
        (completedGroupAlgebra.of ℤ_[2] ℤ_[2]ˣ
          (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ))) = 1 ∧
      (ofHasEval (p := 2) (padicUnitsSection 2) h0).adicSpecialize
        (completedGroupAlgebra.of ℤ_[2] ℤ_[2]ˣ
          (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ))) = -1 := by
  intro h0
  refine ⟨?_, ?_⟩
  · rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval, MonoidHom.one_apply,
      Units.val_one]
  · rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval]
    have hsq : (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ) : ℤ_[2]) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have hneg1 : (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ) ^ 2 = 1 := by
        rw [padicUnitsDepth_two]
        decide
      rw [hneg1, map_one, Units.val_one]
    have hne1 : (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ) : ℤ_[2]) ≠ 1 := by
      intro h1
      apply (padicUnitsSection_injective 2).ne (a₁ := (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ))
        (a₂ := 1) (by rw [padicUnitsDepth_two]; decide)
      exact (Units.ext h1).trans (map_one (padicUnitsSection 2)).symm
    exact (sq_eq_one_iff.mp hsq).resolve_left hne1

end Checks

end WeightSpace

end TauCeti
