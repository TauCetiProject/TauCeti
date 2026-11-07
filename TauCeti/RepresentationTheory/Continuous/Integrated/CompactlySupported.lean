/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import TauCeti.MeasureTheory.Group.Integral
public import TauCeti.RepresentationTheory.Continuous.Integrated.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Integrated forms of strongly continuous unitary representations on `C_c(G, ℂ)`

For a strongly continuous unitary representation `U : ContRepresentation ℂ G H` of a topological
group `G` on a complex inner product space `H` and a measure `μ` finite on compact sets, each
`f : C_c(G, ℂ)` integrates to `ContRepresentation.IsUnitary.integratedOperator hU hcont μ f` via
`U(f) v = ∫ g, f g • U g v ∂μ`, with `‖U(f)‖ ≤ ∫ g, ‖f g‖ ∂μ` and no inner-regularity,
σ-finiteness, or separability hypotheses.

When `G` is locally compact and `R₁` and `μ` charges nonempty open sets, the integrated ranges span
a dense subspace of `H`. When `μ` is inner regular for compact sets on finite-measure sets,
`integratedOperator` agrees with `ContRepresentation.integratedOperatorL1` on `Additive G`, and the
integrated left regular representation on `L²(G, ℂ)` is injective.

## Main definitions

* `ContRepresentation.IsUnitary.integratedOperator`: `C_c(G, ℂ) →ₗ[ℂ] H →L[ℂ] H`.

## Main statements

* `ContRepresentation.IsUnitary.norm_integratedOperator_le`: `‖U(f)‖ ≤ ∫ g, ‖f g‖ ∂μ`.
* `ContRepresentation.IsUnitary.inner_integratedOperator_apply`: matrix coefficients of `U(f)`.
* `ContRepresentation.IsUnitary.dense_span_integratedOperator`: density of spanned ranges of `U(f)`.
* `ContRepresentation.IsUnitary.integratedOperator_eq_integratedOperatorL1`: agreement with
  `ContRepresentation.integratedOperatorL1` on inner-regular measures.
* `ContRepresentation.IsUnitary.integratedOperator_eq_haarScalarFactor_smul`: scaling under change
  of left-invariant measure.
* `ContRepresentation.IsUnitary.commute_integratedOperator` and
  `ContRepresentation.IsUnitary.integratedOperator_commute`: commutativity over abelian groups.
* `MeasureTheory.Measure.injective_integratedOperator_leftRegular`: injectivity of the integrated
  left regular representation on `L²(G, ℂ)`.

## References

* Jacques Dixmier, *C*-Algebras*, §13.9.
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5 and §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped CompactlySupported ENNReal InnerProductSpace

namespace ContRepresentation

section Integrand

variable {G H : Type*} [Monoid G] [TopologicalSpace G] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The vector integrand `g ↦ f g • U g v` of an integrated representation is continuous. -/
@[fun_prop] theorem continuous_integrand (U : ContRepresentation ℂ G H)
    (hcont : ∀ v, Continuous fun g => U g v) (f : C_c(G, ℂ)) (v : H) :
    Continuous fun g => f g • U g v := f.continuous.smul (hcont v)

/-- The vector integrand `g ↦ f g • U g v` vanishes outside the compact support of `f`. -/
theorem hasCompactSupport_integrand (U : ContRepresentation ℂ G H) (f : C_c(G, ℂ)) (v : H) :
    HasCompactSupport fun g => f g • U g v := f.hasCompactSupport.smul_right

/-- Compact support makes every vector integrand `g ↦ f g • U g v` Bochner integrable. -/
theorem integrable_integrand [MeasurableSpace G] [OpensMeasurableSpace G]
    (U : ContRepresentation ℂ G H) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) (v : H) :
    Integrable (fun g => f g • U g v) μ :=
  (U.continuous_integrand hcont f v).integrable_of_hasCompactSupport
    (U.hasCompactSupport_integrand f v)

end Integrand
end ContRepresentation

namespace ContRepresentation.IsUnitary

section FiniteMeasure

variable {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem norm_integral_integrand_le {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) (v : H) :
    ‖∫ g, f g • U g v ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ :=
  (norm_integral_le_of_norm_le (f.integrable.norm.mul_const _)
    (.of_forall fun g => by rw [norm_smul, hU.norm_map])).trans_eq (integral_mul_const _ _)

/-- The integrated form of a strongly continuous unitary representation on `C_c(G, ℂ)`, given by
`U(f) v = ∫ g, f g • U g v ∂μ`. -/
def integratedOperator {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    C_c(G, ℂ) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ g, f g • U g v ∂μ
      map_add' v w := by
        simp_rw [map_add, smul_add]
        exact integral_add (U.integrable_integrand hcont μ f v) (U.integrable_integrand hcont μ f w)
      map_smul' c v := by simp_rw [map_smul, smul_comm _ c]; exact integral_smul c _ }
    (∫ g, ‖f g‖ ∂μ) (hU.norm_integral_integrand_le μ f)
  map_add' f g := ContinuousLinearMap.ext fun v => by
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, add_smul,
      add_apply]
    exact integral_add (U.integrable_integrand hcont μ f v) (U.integrable_integrand hcont μ g v)
  map_smul' c f := ContinuousLinearMap.ext fun v => by
    simpa [mul_smul] using integral_smul c (fun g => f g • U g v)

/-- Defining vector-integral formula for `integratedOperator`. -/
theorem integratedOperator_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) (v : H) : hU.integratedOperator hcont μ f v = ∫ g, f g • U g v ∂μ := (rfl)

/-- The integrated operator `U(f)` is bounded in operator norm by the `L¹(μ)` norm of `f`. -/
theorem norm_integratedOperator_le {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) : ‖hU.integratedOperator hcont μ f‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    (hU.norm_integral_integrand_le μ f)

variable [CompleteSpace H]

/-- Matrix coefficients of `U(f)` are integrals of scalar matrix coefficients of `U`. -/
theorem inner_integratedOperator_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) (w v : H) :
    ⟪w, hU.integratedOperator hcont μ f v⟫_ℂ = ∫ g, f g * ⟪w, U g v⟫_ℂ ∂μ := by
  rw [integratedOperator_apply, ← integral_inner (U.integrable_integrand hcont μ f v) w]
  simp_rw [inner_smul_right]

/-- The ranges of `U(f)` for `f ∈ C_c(G, ℂ)` span a dense subspace of `H`. -/
theorem dense_span_integratedOperator [LocallyCompactSpace G] [R1Space G]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    Dense (Submodule.span ℂ (⋃ f : C_c(G, ℂ), Set.range (hU.integratedOperator hcont μ f)) :
      Set H) := by
  refine Metric.dense_iff.2 fun v ε hε => ?_
  have hV : {g : G | ‖U g v - v‖ ≤ ε / 2} ∈ 𝓝 (1 : G) := by
    simpa [Set.preimage, dist_eq_norm] using
      (hcont v).tendsto 1 (Metric.closedBall_mem_nhds (U 1 v) (half_pos hε))
  obtain ⟨φ, hφ0, hφV, hφ1⟩ := TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ hV
  let f : C_c(G, ℂ) := φ.compLeft Complex.ofRealCLM
  have hf_apply (g : G) : f g = φ g := by
    dsimp only [f]; rw [CompactlySupportedContinuousMap.compLeft_apply] <;> simp
  let fL1 : G →₁[μ] ℂ := f.integrable.toL1 f
  have hfL1 : fL1 =ᵐ[μ] f := f.integrable.coeFn_toL1
  have hf_int : ∫ g, fL1 g ∂μ = 1 := by
    rw [integral_congr_ae hfL1]
    simpa [hf_apply, hφ1] using Complex.ofRealCLM.integral_comp_comm (φ.integrable (μ := μ))
  have hf_norm : ‖fL1‖ = 1 := by
    rw [L1.norm_eq_integral_norm, integral_congr_ae (hfL1.mono fun g hg => congrArg norm hg)]
    refine (integral_congr_ae (.of_forall fun g => ?_)).trans hφ1
    simp [hf_apply, abs_of_nonneg (hφ0 g)]
  have hf_supp : ∀ᵐ g ∂μ, g ∉ {g : G | ‖U g v - v‖ ≤ ε / 2} → fL1 g = 0 := by
    filter_upwards [hfL1] with g hg hgV
    simp [hg, hf_apply, image_eq_zero_of_notMem_tsupport fun h => hgV (hφV h)]
  have hle := TauCeti.norm_integral_smul_sub_le hf_int hf_supp
    ((U.integrable_integrand hcont μ f v).aestronglyMeasurable.congr
      (hfL1.symm.mono fun g hg => congrArg (· • U g v) hg)) (fun _ hg => hg)
  have heq : ∫ g, fL1 g • U g v ∂μ = hU.integratedOperator hcont μ f v :=
    integral_congr_ae (hfL1.mono fun g hg => congrArg (· • U g v) hg)
  refine ⟨hU.integratedOperator hcont μ f v, ?_,
    Submodule.subset_span (Set.mem_iUnion.2 ⟨f, v, rfl⟩)⟩
  rw [Metric.mem_ball, dist_eq_norm]; rw [heq, hf_norm, mul_one] at hle; linarith

end FiniteMeasure

section ScalarComparison

variable {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Transfer the measurable structure on `G` to `Additive G` for `L¹` scalar comparison. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›
local instance {μ : Measure G} [μ.InnerRegularCompactLTTop] :
    Measure.InnerRegularCompactLTTop (α := Additive G) μ := ‹μ.InnerRegularCompactLTTop›

/-- On inner-regular measures, `integratedOperator` agrees with `integratedOperatorL1` on
`Additive G`. -/
theorem integratedOperator_eq_integratedOperatorL1 {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ f =
      (U.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
        (G := Additive G) (fun v => hcont v)
        (hU.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
        (μ : Measure (Additive G))
        (Integrable.toL1 (α := Additive G) (f : Additive G → ℂ) f.integrable) :=
  ContinuousLinearMap.ext fun v =>
    (ContRepresentation.integratedOperatorL1_toL1 (G := Additive G)
      (π := U.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom) (hcont := fun v => hcont v)
      (hbdd := (hU.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le)
      (μ := (μ : Measure (Additive G))) (f := (f : Additive G → ℂ)) f.integrable v).symm

end ScalarComparison

section HaarScalarFactor

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Rescaling a left-invariant measure scales `integratedOperator` by `Measure.haarScalarFactor`. -/
theorem integratedOperator_eq_haarScalarFactor_smul {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant]
    (ν : Measure G) [ν.IsHaarMeasure] (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ' f =
      (Measure.haarScalarFactor μ' ν : ℝ) • hU.integratedOperator hcont ν f :=
  ContinuousLinearMap.ext fun v => TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul
    μ' ν (U.continuous_integrand hcont f v) (U.hasCompactSupport_integrand f v)

end HaarScalarFactor

section CommGroup

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Over a commutative group, `U r` commutes with every integrated operator `U(f)`. -/
theorem commute_integratedOperator [OpensMeasurableSpace G] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (r : G) (f : C_c(G, ℂ)) :
    Commute (U r) (hU.integratedOperator hcont μ f) := by
  ext v
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, integratedOperator_apply,
    ← (U r).integral_comp_comm (U.integrable_integrand hcont μ f v)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only; rw [map_smul]
  exact congrArg (f g • ·)
    (congr($(map_mul U r g) v).symm.trans <| by rw [mul_comm r g, map_mul]; rfl)

/-- Over a commutative group, integrated operators commute with one another. -/
theorem integratedOperator_commute [OpensMeasurableSpace G] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g : C_c(G, ℂ)) :
    Commute (hU.integratedOperator hcont μ f) (hU.integratedOperator hcont μ g) := by
  ext v
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    integratedOperator_apply hU hcont μ g,
    ← (hU.integratedOperator hcont μ f).integral_comp_comm (U.integrable_integrand hcont μ g v)]
  refine integral_congr_ae (.of_forall fun r => ?_)
  dsimp only; rw [map_smul]
  exact congrArg (g r • ·) congr($((hU.commute_integratedOperator hcont μ r f).symm.eq) v)

end CommGroup
end ContRepresentation.IsUnitary

namespace MeasureTheory.Measure

/-- The integrated left regular representation of `G` on `L²(G, ℂ)` is injective on `C_c(G, ℂ)`. -/
theorem injective_integratedOperator_leftRegular {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] :
    Function.Injective
      ((μ.isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)).integratedOperator
        (μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top) μ) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  -- Test `λ(f)` on `φ x = conj (f x⁻¹)` against `g r = ∫ s, φ (s⁻¹ * r) * f s ∂μ`.
  set φ : G → ℂ := fun x => starRingEnd ℂ (f x⁻¹)
  have hφc : Continuous φ := by fun_prop
  have hφs : HasCompactSupport φ :=
    (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left
      (g := starRingEnd ℂ) (map_zero _)
  set K : G → G → ℂ := fun r s => φ (s⁻¹ * r) * f s
  have hKs (r s : G) (h : K r s ≠ 0) : s ∈ tsupport f ∧ s⁻¹ * r ∈ tsupport φ :=
    ⟨subset_tsupport _ fun h0 => h (by simp [K, h0]),
      subset_tsupport _ fun h0 => h (by simp [K, h0])⟩
  set g : G → ℂ := fun r => ∫ s, K r s ∂μ
  have hgc : Continuous g :=
    TauCeti.continuous_integral_of_compact_support μ f.hasCompactSupport
      (by simp only [K, Function.uncurry_def]; fun_prop) fun r s h => (hKs r s h).1
  have hgs : HasCompactSupport g :=
    TauCeti.hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport hφs hKs
  have hξ : MemLp φ 2 μ := hφc.memLp_of_hasCompactSupport hφs
  have hη : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport hgs
  set F : G → G → ℂ := fun s r => starRingEnd ℂ (g r) * (φ (s⁻¹ * r) * f s)
  have hFc : Continuous (Function.uncurry F) := by
    simp only [F, Function.uncurry_def]; fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) :=
    (f.hasCompactSupport.prod hgs).closure_of_subset fun p hp =>
      ⟨subset_tsupport _ fun h0 => hp (by simp [F, Function.uncurry_def, h0]),
        subset_tsupport _ fun h0 => hp (by simp [F, Function.uncurry_def, h0])⟩
  let hU : (μ.leftRegular ℂ ℂ 2).IsUnitary := μ.isUnitary_leftRegular
  let hcont : ∀ ξ : Lp ℂ 2 μ, Continuous fun r => μ.leftRegular ℂ ℂ 2 r ξ :=
    μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top
  have hg0 : ∫ r, starRingEnd ℂ (g r) * g r ∂μ = 0 := by
    have hinner :
        ⟪hη.toLp g, hU.integratedOperator hcont μ f (hξ.toLp φ)⟫_ℂ =
          ∫ r, starRingEnd ℂ (g r) * g r ∂μ := by
      calc ⟪hη.toLp g, hU.integratedOperator hcont μ f (hξ.toLp φ)⟫_ℂ
          = ∫ s, ∫ r, F s r ∂μ ∂μ := by
            rw [hU.inner_integratedOperator_apply]
            simp_rw [L2.inner_def, ← integral_const_mul]
            congr 1 with s
            refine integral_congr_ae ?_
            filter_upwards [hη.coeFn_toLp, μ.coeFn_leftRegular (𝕜 := ℂ) 2 s (hξ.toLp φ),
              (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving.ae_eq_comp hξ.coeFn_toLp]
              with r h₁ h₂ h₃
            simp only [Function.comp_apply] at h₃
            simp only [F, h₁, h₂, h₃, RCLike.inner_apply]
            ring
        _ = ∫ r, ∫ s, F s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hFc hFs
        _ = ∫ r, starRingEnd ℂ (g r) * g r ∂μ := by simp only [F, K, g, integral_const_mul]
    have hzero : hU.integratedOperator hcont μ f = 0 := hf
    simpa [hzero] using hinner.symm
  have hg1 := congrFun (hgc.eq_zero_of_integral_conj_mul_self_eq_zero hη hg0) 1
  ext x
  refine congrFun (f.continuous.eq_zero_of_integral_conj_mul_self_eq_zero
    (f.continuous.memLp_of_hasCompactSupport (μ := μ) f.hasCompactSupport) ?_) x
  simpa [g, K, φ] using hg1

end MeasureTheory.Measure

end
