/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Analysis.Contour.Cycle.Basic

import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Analysis.Contour.Cycle.Residue
import TauCeti.MeasureTheory.Integral.RiemannSum

/-!
# Cauchy–Riemann sum approximation of holomorphic functions

For a null-homologous cycle `Γ` in an open domain `U ⊆ ℂ` and an open set `V ⊆ U` disjoint from
`Cycle.trace Γ` on which `Γ` has winding number `1`, every `f : holomorphicFunctions U` restricts
on `V` to an element in the compact-open closure of the linear span of the Cauchy kernels
`z ↦ (w - z)⁻¹` indexed by points `w ∈ Cycle.trace Γ`.

On each compact subset `K₀ ⊆ V`, the integrand `t ↦ (z ↦ f(γ(t)) / (γ(t) - z))` takes values in
the Banach space `C(K₀, ℂ)` and is continuous along each curve `γ` in the support of `Γ`. Applying
uniform Bochner–Riemann sum approximation (`TotallyBounded.exists_norm_setIntegral_smul_sub_sum_le`)
simultaneously at all points of `K₀` approximates Cauchy's integral formula uniformly on `K₀` by
finite linear combinations of Cauchy kernels.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped Real Interval

namespace TauCeti.HolomorphicFunctions

open Contour

/-- Fix the inherited additive group before forming submodules of `holomorphicFunctions`. -/
local instance instAddCommGroupCauchyRiemannSum (U : Opens ℂ) :
    AddCommGroup (holomorphicFunctions U) := inferInstance

/-- Linear spans use the additive monoid projection of the inherited additive group. -/
local instance instAddCommMonoidCauchyRiemannSum (U : Opens ℂ) :
    AddCommMonoid (holomorphicFunctions U) :=
  (inferInstance : AddCommGroup (holomorphicFunctions U)).toAddCommMonoid

section CauchyKernel

variable {V : Opens ℂ} {w : ℂ}

private theorem differentiableOn_cauchyKernel (hw : w ∉ (V : Set ℂ)) :
    DifferentiableOn ℂ (fun z : ℂ ↦ (w - z)⁻¹) V :=
  (differentiableOn_const w).sub differentiableOn_id |>.inv
    fun _ hz ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw).symm

/-- The Cauchy kernel `z ↦ (w - z)⁻¹` as a holomorphic function on an open set `V` omitting `w`. -/
def cauchyKernel (hw : w ∉ (V : Set ℂ)) : holomorphicFunctions V :=
  of V (fun z ↦ (w - z)⁻¹) (differentiableOn_cauchyKernel hw)

@[simp]
theorem cauchyKernel_apply (hw : w ∉ (V : Set ℂ)) (z : V) :
    (cauchyKernel hw).val z = (w - (z : ℂ))⁻¹ :=
  of_apply _ _ z

/-- On an open set omitting `w`, `w - z` is a left inverse to the Cauchy kernel `z ↦ (w - z)⁻¹`. -/
@[simp]
theorem sub_id_mul_cauchyKernel (hw : w ∉ (V : Set ℂ)) :
    (algebraMap ℂ (holomorphicFunctions V) w - of V id differentiableOn_id) * cauchyKernel hw =
      1 := by
  ext z
  have hne : w - (z : ℂ) ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem z.property hw).symm
  simp [Subalgebra.coe_mul, mul_inv_cancel₀ hne]

/-- On an open set omitting `w`, the Cauchy kernel `z ↦ (w - z)⁻¹` is a left inverse to `w - z`. -/
@[simp]
theorem cauchyKernel_mul_sub_id (hw : w ∉ (V : Set ℂ)) :
    cauchyKernel hw * (algebraMap ℂ (holomorphicFunctions V) w - of V id differentiableOn_id) =
      1 := by
  rw [mul_comm, sub_id_mul_cauchyKernel]

/-- Restricting a Cauchy kernel to a smaller open set gives the Cauchy kernel on the smaller set. -/
@[simp]
theorem restrict_cauchyKernel {W : Opens ℂ} (hWV : W ≤ V) (hw : w ∉ (V : Set ℂ)) :
    restrict hWV (cauchyKernel hw) = cauchyKernel (fun h ↦ hw (hWV h)) := by
  ext z
  simp

end CauchyKernel

section Approximation

variable {U V : Opens ℂ}

/-- Uniformly approximate a single curve's Cauchy-type integral on a compact subset `K₀` of `V`
by a finite linear combination of Cauchy kernels along the curve. -/
private theorem exists_curve_riemann_approx (f : holomorphicFunctions U)
    (γ : PiecewiseC1ClosedCurve) (hγU : ∀ t ∈ uIcc γ.a γ.b, γ t ∈ (U : Set ℂ))
    (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ))
    {K₀ : Set V} (hK₀ : IsCompact K₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → ℂ) (_ : ∀ i, w i ∈ γ '' uIcc γ.a γ.b) (c : Fin N → ℂ),
      ∀ z ∈ K₀,
        ‖(∫ t in γ.a..γ.b, deriv γ t * (extend f (γ t) / (γ t - (z : ℂ)))) -
          ∑ i, c i * (w i - (z : ℂ))⁻¹‖ < ε := by
  classical
  let : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀
  -- Bundle the two-variable Cauchy integrand `(t, z) ↦ f(γ(t)) * (γ(t) - z)⁻¹` on the product.
  let γU : C(uIcc γ.a γ.b, U) :=
    ⟨fun t ↦ ⟨γ t.val, hγU t.val t.property⟩,
      (continuousOn_iff_continuous_domRestrict.mp γ.continuousOn).subtype_mk
        fun t ↦ hγU t.val t.property⟩
  have hγU_apply (t : uIcc γ.a γ.b) : γU t = ⟨γ t.val, hγU t.val t.property⟩ := rfl
  have hsub_cont : Continuous (fun p : uIcc γ.a γ.b × K₀ ↦ (γU p.1 : ℂ) - (p.2.val : ℂ)) :=
    (continuous_subtype_val.comp (γU.continuous.comp continuous_fst)).sub
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hsub_ne : ∀ p : uIcc γ.a γ.b × K₀, (γU p.1 : ℂ) - (p.2.val : ℂ) ≠ 0 := fun p ↦
    sub_ne_zero.mpr (ne_of_mem_of_not_mem p.2.val.property (hγV p.1.val p.1.property)).symm
  let Ψ : C(uIcc γ.a γ.b × K₀, ℂ) :=
    ⟨fun p ↦ f.val (γU p.1) * ((γU p.1 : ℂ) - (p.2.val : ℂ))⁻¹,
      (f.val.continuous.comp (γU.continuous.comp continuous_fst)).mul (hsub_cont.inv₀ hsub_ne)⟩
  let φ : ℝ → C(K₀, ℂ) := fun t ↦
    if ht : t ∈ uIcc γ.a γ.b then Ψ.curry ⟨t, ht⟩ else 0
  have hφ_eq : ∀ t (ht : t ∈ uIcc γ.a γ.b), φ t = Ψ.curry ⟨t, ht⟩ := by
    intro t ht
    simp [φ, ht]
  have hφ_cont : ContinuousOn φ (uIcc γ.a γ.b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Ψ.curry.continuous.congr fun t ↦ (hφ_eq t.val t.property).symm
  have hderiv_int : IntegrableOn (deriv γ) (Ι γ.a γ.b) volume :=
    intervalIntegrable_iff.mp γ.isPiecewiseC1On.intervalIntegrable_deriv
  have hφ_int : IntegrableOn (fun t ↦ deriv γ t • φ t) (Ι γ.a γ.b) volume :=
    intervalIntegrable_iff.mp (γ.isPiecewiseC1On.intervalIntegrable_deriv.smul_continuousOn hφ_cont)
  -- Choose an oscillation tolerance `η` small relative to the curve length `L + 1`.
  let L : ℝ := ∫ t in Ι γ.a γ.b, ‖deriv γ t‖
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  let η : ℝ := ε / (2 * (L + 1))
  have hη_pos : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ_pos, hδ_osc⟩ :=
    Metric.uniformContinuousOn_iff.mp (isCompact_uIcc.uniformContinuousOn_of_continuous hφ_cont)
      η hη_pos
  obtain ⟨N, ζ, c₀, hζ, -, happrox⟩ :=
    (isCompact_uIcc.totallyBounded.subset uIoc_subset_uIcc).exists_norm_setIntegral_smul_sub_sum_le
      measurableSet_uIoc hderiv_int hδ_pos
  have hbound : ‖(∫ t in Ι γ.a γ.b, deriv γ t • φ t) - ∑ i, c₀ i • φ (ζ i)‖ < ε := by
    have hle := happrox φ η hφ_int fun x hx y hy hxy ↦
      (dist_eq_norm (φ x) (φ y)).symm.trans_le
        (hδ_osc x (uIoc_subset_uIcc hx) y (uIoc_subset_uIcc hy) hxy).le
    have hηL : η * L < ε := by
      calc η * L ≤ η * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hη_pos.le
        _ = ε / 2 := by
          dsimp [η]
          field_simp
        _ < ε := half_lt_self hε
    exact hle.trans_lt hηL
  -- Evaluate the `C(K₀, ℂ)`-valued integral and Riemann sum pointwise at `z ∈ K₀`.
  let sgn : ℝ := if γ.a ≤ γ.b then 1 else -1
  have hsgn_norm : ‖(sgn : ℂ)‖ = 1 := by
    dsimp [sgn]
    split_ifs <;> simp
  refine ⟨N, fun i ↦ γ (ζ i), fun i ↦ ⟨ζ i, uIoc_subset_uIcc (hζ i), rfl⟩,
    fun i ↦ (sgn : ℂ) * c₀ i * extend f (γ (ζ i)), ?_⟩
  intro z hzK
  let ev : C(K₀, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨z, hzK⟩
  have heval_int :
      ∫ t in γ.a..γ.b, deriv γ t * (extend f (γ t) / (γ t - (z : ℂ))) =
        (sgn : ℂ) * ev (∫ t in Ι γ.a γ.b, deriv γ t • φ t) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, ← ev.integral_comp_comm hφ_int]
    have hcongr : EqOn (fun t ↦ deriv γ t * (extend f (γ t) / (γ t - (z : ℂ))))
        (fun t ↦ ev (deriv γ t • φ t)) (Ι γ.a γ.b) := by
      intro t ht
      have htu : t ∈ uIcc γ.a γ.b := uIoc_subset_uIcc ht
      simp only [ev, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, hφ_eq t htu,
        ContinuousMap.curry_apply, Ψ, ContinuousMap.coe_mk, hγU_apply, smul_eq_mul, div_eq_mul_inv]
      rw [extend_apply f ⟨γ t, hγU t htu⟩]
    rw [setIntegral_congr_fun measurableSet_uIoc hcongr, Complex.real_smul]
  have heval_sum :
      ∑ i, (sgn : ℂ) * c₀ i * extend f (γ (ζ i)) * (γ (ζ i) - (z : ℂ))⁻¹ =
        (sgn : ℂ) * ev (∑ i, c₀ i • φ (ζ i)) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have htu : ζ i ∈ uIcc γ.a γ.b := uIoc_subset_uIcc (hζ i)
    simp only [ev, map_smul, ContinuousMap.evalCLM_apply, hφ_eq (ζ i) htu,
      ContinuousMap.curry_apply, Ψ, ContinuousMap.coe_mk, hγU_apply, smul_eq_mul]
    rw [extend_apply f ⟨γ (ζ i), hγU (ζ i) htu⟩]
    ring
  rw [heval_int, heval_sum, ← mul_sub, ← map_sub, norm_mul, hsgn_norm, one_mul]
  exact (ContinuousMap.norm_coe_le_norm _ ⟨z, hzK⟩).trans_lt hbound

/-- **Uniform Cauchy–Riemann sum approximation on compact sets.** Let `Γ` be a null-homologous
cycle in `U` and `V ≤ U` an open subset disjoint from `Cycle.trace Γ` on which `Γ` has winding
number `1`. On every compact subset `K₀` of `V`, `restrict hVU f` is uniformly approximated within
any `ε > 0` by a finite linear combination of Cauchy kernels along `Cycle.trace Γ`. -/
theorem exists_norm_sub_sum_cauchyKernel_lt (hVU : V ≤ U) (f : holomorphicFunctions U)
    (Γ : Cycle) (hΓU : Γ.IsIn U) (hn : Γ.IsNullHomologous U)
    (hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1)
    {K₀ : Set V} (hK₀ : IsCompact K₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : holomorphicFunctions V),
      k ∈ Submodule.span ℂ
        {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)} ∧
      ∀ z ∈ K₀, ‖k.val z - (restrict hVU f).val z‖ < ε := by
  classical
  let S : Submodule ℂ (holomorphicFunctions V) :=
    Submodule.span ℂ
      {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)}
  -- Approximate each curve in `Γ.support` within a tolerance proportional to `1 / (#support + 1)`.
  let M : ℝ := ((FreeAbelianGroup.support Γ).card : ℝ) + 1
  have hM_pos : 0 < M := by positivity
  have hcurve (γ : {γ // γ ∈ FreeAbelianGroup.support Γ}) :
      ∃ (k : holomorphicFunctions V), k ∈ S ∧
        ∀ z ∈ K₀,
          ‖k.val z - (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ) *
            (∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ))))‖ < ε / M := by
    have hγ_trace : ∀ t ∈ uIcc γ.val.a γ.val.b, γ.val t ∈ Cycle.trace Γ := fun t ht ↦
      Cycle.mem_trace_iff.mpr ⟨γ.val, γ.property, t, ht, rfl⟩
    have hγU : ∀ t ∈ uIcc γ.val.a γ.val.b, γ.val t ∈ (U : Set ℂ) := fun t ht ↦
      Cycle.isIn_iff.mp hΓU (hγ_trace t ht)
    have hγV : ∀ t ∈ uIcc γ.val.a γ.val.b, γ.val t ∉ (V : Set ℂ) := fun t ht ↦
      hVΓ.notMem_of_mem_right (hγ_trace t ht)
    let α : ℂ := (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ)
    have hα_pos : 0 < ‖α‖ + 1 := by positivity
    obtain ⟨N, w, hw_img, c, happrox⟩ :=
      exists_curve_riemann_approx f γ.val hγU hγV hK₀ (div_pos (div_pos hε hM_pos) hα_pos)
    have hw_trace (i : Fin N) : w i ∈ Cycle.trace Γ := by
      obtain ⟨t, ht, htw⟩ := hw_img i
      exact htw ▸ hγ_trace t ht
    refine ⟨∑ i, (α * c i) • cauchyKernel (V := V) (hVΓ.notMem_of_mem_right (hw_trace i)),
      Submodule.sum_mem S fun i _ ↦
        S.smul_mem _ (Submodule.subset_span ⟨w i, hw_trace i, rfl⟩),
      fun z hz ↦ ?_⟩
    have hval : (∑ i, (α * c i) • cauchyKernel (V := V)
        (hVΓ.notMem_of_mem_right (hw_trace i))).val z =
        α * ∑ i, c i * (w i - (z : ℂ))⁻¹ := by
      simp [Finset.mul_sum, mul_assoc]
    rw [hval, ← mul_sub, norm_mul, mul_comm ‖α‖]
    calc ‖(∑ i, c i * (w i - (z : ℂ))⁻¹) -
            ∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ)))‖ * ‖α‖
        = ‖(∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ)))) -
            ∑ i, c i * (w i - (z : ℂ))⁻¹‖ * ‖α‖ := by rw [norm_sub_rev]
      _ ≤ ‖(∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ)))) -
            ∑ i, c i * (w i - (z : ℂ))⁻¹‖ * (‖α‖ + 1) := by gcongr; linarith
      _ < (ε / M / (‖α‖ + 1)) * (‖α‖ + 1) := by gcongr; exact happrox z hz
      _ = ε / M := div_mul_cancel₀ _ hα_pos.ne'
  choose k hkS hk_approx using hcurve
  refine ⟨∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, k γ,
    Submodule.sum_mem S fun γ _ ↦ hkS γ, fun z hz ↦ ?_⟩
  -- Express `(restrict hVU f).val z` via Cauchy's integral formula over the cycle `Γ`.
  have hcauchy : (restrict hVU f).val z =
      ∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ},
        (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ) *
          ∫ t in γ.val.a..γ.val.b,
            deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ))) := by
    have hz_off : (z : ℂ) ∉ Cycle.trace Γ := hVΓ.notMem_of_mem_left z.property
    have hcif := Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f)
      hΓU hn hz_off
    rw [hw z z.property, mul_one] at hcif
    have hfz : extend f z = (2 * π * I)⁻¹ * Cycle.integral (fun w ↦ extend f w / (w - z)) Γ := by
      rw [hcif, inv_mul_cancel_left₀ two_pi_I_ne_zero]
    rw [restrict_apply, ← extend_apply f ⟨z, hVU z.property⟩, hfz,
      Cycle.integral_eq_sum_support, Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    simp only [zsmul_eq_mul, smul_eq_mul]
    ring
  have hsum_val : (∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, k γ).val z =
      ∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, (k γ).val z := by
    simp
  rw [hsum_val, hcauchy, ← Finset.sum_sub_distrib]
  calc ‖∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ},
          ((k γ).val z - (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ) *
            ∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ))))‖
      ≤ ∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ},
          ‖(k γ).val z - (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ) *
            ∫ t in γ.val.a..γ.val.b,
              deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, (ε / M) :=
        Finset.sum_le_sum fun γ _ ↦ (hk_approx γ z hz).le
    _ = ((FreeAbelianGroup.support Γ).card : ℝ) * (ε / M) := by simp
    _ = ((FreeAbelianGroup.support Γ).card : ℝ) / M * ε := by ring
    _ < 1 * ε := by
        gcongr
        rw [div_lt_one hM_pos]
        dsimp [M]
        linarith
    _ = ε := one_mul ε

/-- **Cauchy–Riemann approximation in `holomorphicFunctions V`.** Under the hypotheses of
Cauchy's integral formula on `V ≤ U`, the restriction `restrict hVU f` belongs to the compact-open
closure of the linear span of the Cauchy kernels indexed by `Cycle.trace Γ`. -/
theorem restrict_mem_closure_span_cauchyKernel (hVU : V ≤ U) (f : holomorphicFunctions U)
    (Γ : Cycle) (hΓU : Γ.IsIn U) (hn : Γ.IsNullHomologous U)
    (hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1) :
    restrict hVU f ∈ closure (Submodule.span ℂ
      {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) |
        (w : ℂ) (hm : w ∈ Cycle.trace Γ)} : Set (holomorphicFunctions V)) := by
  -- Index a directed net by compact subsets `K₀ ⊆ V` and tolerances `ε > 0` (`OrderDual`).
  let ι := {K₀ : Set V // IsCompact K₀} × (OrderDual {ε : ℝ // 0 < ε})
  let : Nonempty {K₀ : Set V // IsCompact K₀} := ⟨⟨∅, isCompact_empty⟩⟩
  let : SemilatticeSup {K₀ : Set V // IsCompact K₀} :=
    { (inferInstance : PartialOrder {K₀ : Set V // IsCompact K₀}) with
      sup K₁ K₂ := ⟨K₁.1 ∪ K₂.1, K₁.2.union K₂.2⟩
      le_sup_left _ _ := subset_union_left
      le_sup_right _ _ := subset_union_right
      sup_le _ _ _ := union_subset }
  let : SemilatticeInf {ε : ℝ // 0 < ε} :=
    { (inferInstance : PartialOrder {ε : ℝ // 0 < ε}) with
      inf e₁ e₂ := ⟨min e₁.1 e₂.1, lt_min e₁.2 e₂.2⟩
      inf_le_left _ _ := min_le_left _ _
      inf_le_right _ _ := min_le_right _ _
      le_inf _ _ _ := le_min }
  let : Nonempty (OrderDual {ε : ℝ // 0 < ε}) := ⟨OrderDual.toDual ⟨1, zero_lt_one⟩⟩
  have hchoice (i : ι) := exists_norm_sub_sum_cauchyKernel_lt hVU f Γ hΓU hn hVΓ hw
    i.1.2 (OrderDual.ofDual i.2).2
  choose g hg_mem hg_bound using hchoice
  refine mem_closure_of_tendsto (b := (atTop : Filter ι)) ?_ (Eventually.of_forall hg_mem)
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K₀ hK₀
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (⟨⟨K₀, hK₀⟩, OrderDual.toDual ⟨ε, hε⟩⟩ : ι)]
    with i hi z hz
  rw [dist_comm, dist_eq_norm]
  exact (hg_bound i z (hi.1 hz)).trans_le hi.2

end Approximation

end TauCeti.HolomorphicFunctions
