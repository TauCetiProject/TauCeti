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

Because every unital algebra homomorphism sending the coordinate function on `V` to `a` sends each
Cauchy kernel `z ↦ (w - z)⁻¹` (`w ∉ V`) to `resolvent a w`, this compact-open density reduces
uniqueness of the holomorphic functional calculus (`TauCeti.holomorphicCalculus_unique`) on open
domains to agreement on resolvents.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped Real Interval

namespace TauCeti.HolomorphicFunctions

open Contour

section Approximation

variable {U V : Opens ℂ}

/-- Approximate a Banach-space-valued curve integral `∫ t in γ.a..γ.b, deriv γ t • φ t` within
any `ε > 0` by a finite complex linear combination of values of `φ` on `uIcc γ.a γ.b`. -/
private theorem exists_intervalIntegral_smul_sub_sum_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (γ : PiecewiseC1ClosedCurve) {φ : ℝ → E} (hφ : ContinuousOn φ (uIcc γ.a γ.b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℝ) (_ : ∀ i, ζ i ∈ uIcc γ.a γ.b) (c : Fin N → ℂ),
      ‖(∫ t in γ.a..γ.b, deriv γ t • φ t) - ∑ i, c i • φ (ζ i)‖ < ε := by
  have hderiv_int : IntegrableOn (deriv γ) (Ι γ.a γ.b) volume :=
    intervalIntegrable_iff.mp γ.isPiecewiseC1On.intervalIntegrable_deriv
  have hφ_int : IntegrableOn (fun t ↦ deriv γ t • φ t) (Ι γ.a γ.b) volume :=
    intervalIntegrable_iff.mp (γ.isPiecewiseC1On.intervalIntegrable_deriv.smul_continuousOn hφ)
  let L : ℝ := ∫ t in Ι γ.a γ.b, ‖deriv γ t‖
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  let η : ℝ := ε / (2 * (L + 1))
  have hη_pos : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ_pos, hδ_osc⟩ :=
    Metric.uniformContinuousOn_iff.mp (isCompact_uIcc.uniformContinuousOn_of_continuous hφ) η hη_pos
  obtain ⟨N, ζ, c₀, hζ, -, happrox⟩ :=
    (isCompact_uIcc.totallyBounded.subset uIoc_subset_uIcc).exists_norm_setIntegral_smul_sub_sum_le
      measurableSet_uIoc hderiv_int hδ_pos
  have hbound : ‖(∫ t in Ι γ.a γ.b, deriv γ t • φ t) - ∑ i, c₀ i • φ (ζ i)‖ < ε := by
    have hle := happrox φ η hφ_int fun x hx y hy hxy ↦
      (dist_eq_norm (φ x) (φ y)).symm.trans_le
        (hδ_osc x (uIoc_subset_uIcc hx) y (uIoc_subset_uIcc hy) hxy).le
    have hηL : η * L < ε := by
      calc η * L ≤ η * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hη_pos.le
        _ = ε / 2 := by dsimp [η]; field_simp
        _ < ε := half_lt_self hε
    exact hle.trans_lt hηL
  let sgn : ℝ := if γ.a ≤ γ.b then 1 else -1
  have hsgn_norm : ‖sgn‖ = 1 := by
    dsimp [sgn]
    split_ifs <;> simp
  refine ⟨N, ζ, fun i ↦ uIoc_subset_uIcc (hζ i), fun i ↦ (sgn : ℂ) * c₀ i, ?_⟩
  have hsum : ∑ i, ((sgn : ℂ) * c₀ i) • φ (ζ i) = sgn • ∑ i, c₀ i • φ (ζ i) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul, Complex.coe_smul]
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, hsum, ← smul_sub, norm_smul, hsgn_norm,
    one_mul]
  exact hbound

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
  let γU : C(uIcc γ.a γ.b, U) :=
    ⟨fun t ↦ ⟨γ t.val, hγU t.val t.property⟩,
      (continuousOn_iff_continuous_domRestrict.mp γ.continuousOn).subtype_mk _⟩
  have hγU_apply (t : uIcc γ.a γ.b) : γU t = ⟨γ t.val, hγU t.val t.property⟩ :=
    congrFun (ContinuousMap.coe_mk _ _) t
  have hsub_ne : ∀ p : uIcc γ.a γ.b × K₀, (γU p.1 : ℂ) - (p.2.val : ℂ) ≠ 0 := fun p ↦
    sub_ne_zero.mpr (ne_of_mem_of_not_mem p.2.val.property (hγV p.1.val p.1.property)).symm
  let Ψ : C(uIcc γ.a γ.b × K₀, ℂ) :=
    ⟨fun p ↦ f.val (γU p.1) * ((γU p.1 : ℂ) - (p.2.val : ℂ))⁻¹,
      by fun_prop (disch := exact hsub_ne)⟩
  let φ : ℝ → C(K₀, ℂ) := fun t ↦
    if ht : t ∈ uIcc γ.a γ.b then Ψ.curry ⟨t, ht⟩ else 0
  have hφ_eq (t : ℝ) (ht : t ∈ uIcc γ.a γ.b) : φ t = Ψ.curry ⟨t, ht⟩ := by simp [φ, ht]
  have hφ_cont : ContinuousOn φ (uIcc γ.a γ.b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact Ψ.curry.continuous.congr fun t ↦ (hφ_eq t.val t.property).symm
  have hφ_eval (t : ℝ) (ht : t ∈ uIcc γ.a γ.b) (z : K₀) :
      φ t z = extend f (γ t) * (γ t - (z.val : ℂ))⁻¹ := by
    simp only [hφ_eq t ht, ContinuousMap.curry_apply, Ψ, ContinuousMap.coe_mk, hγU_apply]
    rw [extend_apply f ⟨γ t, hγU t ht⟩]
  obtain ⟨N, ζ, hζ, c, hbound⟩ := exists_intervalIntegral_smul_sub_sum_lt γ hφ_cont hε
  refine ⟨N, fun i ↦ γ (ζ i), fun i ↦ ⟨ζ i, hζ i, rfl⟩,
    fun i ↦ c i * extend f (γ (ζ i)), fun z hzK ↦ ?_⟩
  let ev : C(K₀, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨z, hzK⟩
  have heval_int :
      ∫ t in γ.a..γ.b, deriv γ t * (extend f (γ t) / (γ t - (z : ℂ))) =
        ev (∫ t in γ.a..γ.b, deriv γ t • φ t) := by
    rw [← ev.intervalIntegral_comp_comm
      (γ.isPiecewiseC1On.intervalIntegrable_deriv.smul_continuousOn hφ_cont)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    simp only [ev, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, hφ_eval t ht ⟨z, hzK⟩,
      smul_eq_mul, div_eq_mul_inv]
  have heval_sum :
      ∑ i, c i * extend f (γ (ζ i)) * (γ (ζ i) - (z : ℂ))⁻¹ =
        ev (∑ i, c i • φ (ζ i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ev, map_smul, ContinuousMap.evalCLM_apply, hφ_eval (ζ i) (hζ i) ⟨z, hzK⟩,
      smul_eq_mul, mul_assoc]
  rw [heval_int, heval_sum, ← map_sub]
  simpa only [ev, ContinuousMap.evalCLM_apply] using
    (ContinuousMap.norm_coe_le_norm _ ⟨z, hzK⟩).trans_lt hbound

/-- Uniformly approximate the weighted Cauchy-type integral along one generator of `Γ.support`
within `δ > 0` on `K₀` by an element of the span of Cauchy kernels along `Cycle.trace Γ`. -/
private theorem exists_mem_span_cauchyKernel_curve_approx (f : holomorphicFunctions U)
    (Γ : Cycle) (hΓU : Γ.IsIn U) (hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    {γ : PiecewiseC1ClosedCurve} (hγ : γ ∈ FreeAbelianGroup.support Γ)
    {K₀ : Set V} (hK₀ : IsCompact K₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k ∈ Submodule.span ℂ
        {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)},
      ∀ z ∈ K₀,
        ‖k.val z - (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ Γ : ℂ) *
          ∫ t in γ.a..γ.b, deriv γ t * (extend f (γ t) / (γ t - (z : ℂ)))‖ < δ := by
  let S : Submodule ℂ (holomorphicFunctions V) :=
    Submodule.span ℂ
      {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)}
  have hγ_trace : ∀ t ∈ uIcc γ.a γ.b, γ t ∈ Cycle.trace Γ := fun t ht ↦
    Cycle.mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩
  have hγU : ∀ t ∈ uIcc γ.a γ.b, γ t ∈ (U : Set ℂ) := fun t ht ↦
    Cycle.isIn_iff.mp hΓU (hγ_trace t ht)
  have hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ) := fun t ht ↦
    hVΓ.notMem_of_mem_right (hγ_trace t ht)
  set α : ℂ := (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ Γ : ℂ)
  have hα_pos : 0 < ‖α‖ + 1 := by positivity
  obtain ⟨N, w, hw_img, c, happrox⟩ :=
    exists_curve_riemann_approx f γ hγU hγV hK₀ (div_pos hδ hα_pos)
  have hw_trace (i : Fin N) : w i ∈ Cycle.trace Γ := by
    obtain ⟨t, ht, htw⟩ := hw_img i
    exact htw ▸ hγ_trace t ht
  refine ⟨∑ i, (α * c i) • cauchyKernel (V := V) (hVΓ.notMem_of_mem_right (hw_trace i)),
    Submodule.sum_mem S fun i _ ↦ S.smul_mem _ (Submodule.subset_span ⟨w i, hw_trace i, rfl⟩),
    fun z hz ↦ ?_⟩
  have hval : (∑ i, (α * c i) • cauchyKernel (V := V)
      (hVΓ.notMem_of_mem_right (hw_trace i))).val z =
      α * ∑ i, c i * (w i - (z : ℂ))⁻¹ := by
    simp [Finset.mul_sum, mul_assoc]
  set Iγ : ℂ := ∫ t in γ.a..γ.b, deriv γ t * (extend f (γ t) / (γ t - (z : ℂ)))
  rw [hval, ← mul_sub, norm_mul, mul_comm ‖α‖, norm_sub_rev]
  calc ‖Iγ - ∑ i, c i * (w i - (z : ℂ))⁻¹‖ * ‖α‖
      ≤ ‖Iγ - ∑ i, c i * (w i - (z : ℂ))⁻¹‖ * (‖α‖ + 1) := by gcongr; linarith
    _ < (δ / (‖α‖ + 1)) * (‖α‖ + 1) := by gcongr; exact happrox z hz
    _ = δ := div_mul_cancel₀ _ hα_pos.ne'

/-- Expand `(restrict hVU f).val z` via Cauchy's integral formula over the generators of `Γ`. -/
private theorem restrict_apply_eq_sum_support_integral (hVU : V ≤ U) (f : holomorphicFunctions U)
    (Γ : Cycle) (hΓU : Γ.IsIn U) (hn : Γ.IsNullHomologous U)
    (hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1) (z : V) :
    (restrict hVU f).val z =
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

/-- **Uniform Cauchy–Riemann sum approximation on compact sets.** Let `Γ` be a null-homologous
cycle in `U` and `V ≤ U` an open subset disjoint from `Cycle.trace Γ` on which `Γ` has winding
number `1`. On every compact subset `K₀` of `V`, `restrict hVU f` is uniformly approximated within
any `ε > 0` by an element in the linear span of the Cauchy kernels along `Cycle.trace Γ`. -/
theorem exists_mem_span_cauchyKernel_norm_sub_lt (hVU : V ≤ U) (f : holomorphicFunctions U)
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
  let M : ℝ := ((FreeAbelianGroup.support Γ).card : ℝ) + 1
  have hM_pos : 0 < M := by positivity
  have hcurve (γ : {γ // γ ∈ FreeAbelianGroup.support Γ}) :=
    exists_mem_span_cauchyKernel_curve_approx f Γ hΓU hVΓ γ.property hK₀ (div_pos hε hM_pos)
  choose k hkS hk_approx using hcurve
  refine ⟨∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, k γ,
    Submodule.sum_mem S fun γ _ ↦ hkS γ, fun z hz ↦ ?_⟩
  let term (γ : {γ // γ ∈ FreeAbelianGroup.support Γ}) : ℂ :=
    (2 * π * I)⁻¹ * (FreeAbelianGroup.coeff γ.val Γ : ℂ) *
      ∫ t in γ.val.a..γ.val.b, deriv γ.val t * (extend f (γ.val t) / (γ.val t - (z : ℂ)))
  have hcauchy : (restrict hVU f).val z = ∑ γ, term γ :=
    restrict_apply_eq_sum_support_integral hVU f Γ hΓU hn hVΓ hw z
  have hsum_val : (∑ γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, k γ).val z = ∑ γ, (k γ).val z := by
    simp
  rw [hsum_val, hcauchy, ← Finset.sum_sub_distrib]
  calc ‖∑ γ, ((k γ).val z - term γ)‖
      ≤ ∑ γ, ‖(k γ).val z - term γ‖ := norm_sum_le _ _
    _ ≤ ∑ _γ : {γ // γ ∈ FreeAbelianGroup.support Γ}, (ε / M) :=
        Finset.sum_le_sum fun γ _ ↦ (hk_approx γ z hz).le
    _ = ((FreeAbelianGroup.support Γ).card : ℝ) / M * ε := by simp [div_eq_mul_inv]; ring
    _ < 1 * ε := by
        gcongr
        rw [div_lt_one hM_pos]
        dsimp [M]
        linarith
    _ = ε := one_mul ε

/-- **Cauchy–Riemann approximation in `holomorphicFunctions V`.** Let `Γ` be a null-homologous
cycle in `U` and `V ≤ U` an open subset disjoint from `Cycle.trace Γ` on which `Γ` has winding
number `1` at every point of `V`. Then `restrict hVU f` belongs to the compact-open closure of the
linear span of the Cauchy kernels indexed by `Cycle.trace Γ`. -/
theorem restrict_mem_closure_span_cauchyKernel (hVU : V ≤ U) (f : holomorphicFunctions U)
    (Γ : Cycle) (hΓU : Γ.IsIn U) (hn : Γ.IsNullHomologous U)
    (hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1) :
    restrict hVU f ∈ closure (Submodule.span ℂ
      {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) |
        (w : ℂ) (hm : w ∈ Cycle.trace Γ)} : Set (holomorphicFunctions V)) := by
  rw [closure_subtype, mem_closure_iff_nhds_basis
    (nhds_basis_uniformity ContinuousMap.hasBasis_compactConvergenceUniformity)]
  rintro ⟨K₀, U₀⟩ ⟨hK₀, hU₀⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU₀
  obtain ⟨k, hk, hbound⟩ :=
    exists_mem_span_cauchyKernel_norm_sub_lt hVU f Γ hΓU hn hVΓ hw hK₀ hε
  exact ⟨k.val, ⟨k, hk, rfl⟩, fun z hz ↦
    hεU (by simpa only [dist_eq_norm, norm_sub_rev] using hbound z hz)⟩

end Approximation

end TauCeti.HolomorphicFunctions
