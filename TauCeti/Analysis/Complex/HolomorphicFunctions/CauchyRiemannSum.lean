/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ
public import TauCeti.Analysis.Contour.Cycle.Grid
import TauCeti.Analysis.Contour.Cycle.Residue
import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.MeasureTheory.Integral.IntervalIntegral.RiemannSum

/-!
# Cauchy kernels and Cauchy Riemann sums for holomorphic functions

Given an open subset `V ⊆ ℂ` and `w ∉ V`, the Cauchy kernel
`HolomorphicFunctions.cauchyKernel V w hw` represents `z ↦ (w - z)⁻¹` as an element of
`holomorphicFunctions V`. Given a finite family `E` of oriented segments disjoint from `V` and a
holomorphic function `f : holomorphicFunctions U`, the `n`-point left-endpoint Cauchy Riemann sum
`HolomorphicFunctions.cauchyRiemannSum hEV f n` is a finite linear combination of Cauchy kernels
approximating `(2πi)⁻¹ ∫ f(w) (w - z)⁻¹ dw` along `E`.

When `E` is a balanced family of segments in `U` disjoint from `V ≤ U` whose cycle
`Cycle.ofBalancedSegments hbal` is null-homologous in `U` and winds once around every point of `V`,
the Cauchy Riemann sums converge to `restrict hVU f` in the compact-open topology on
`holomorphicFunctions V` (`HolomorphicFunctions.tendsto_cauchyRiemannSum`). Around any compact
subset `K ⊆ U`, such an open neighbourhood `V ≤ U` and segment family `E` exist
(`IsCompact.exists_opens_tendsto_cauchyRiemannSum`), providing the compact-open approximation by
rational functions with poles outside `V` needed to establish uniqueness of the holomorphic
functional calculus.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter Metric Set TopologicalSpace Topology
open scoped Finset Real

namespace TauCeti

open Contour

namespace HolomorphicFunctions

/-! ### Cauchy kernels -/

/-- For `w ∉ V`, the Cauchy kernel `z ↦ (w - z)⁻¹` as an element of `holomorphicFunctions V`. -/
def cauchyKernel (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) : holomorphicFunctions V :=
  of V (fun z => (w - z)⁻¹)
    (((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz =>
      sub_ne_zero.mpr fun h => by dsimp at h; exact hw (h ▸ hz))

/-- Pointwise evaluation of `cauchyKernel V w hw`. -/
@[simp]
theorem cauchyKernel_apply (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) (z : V) :
    (cauchyKernel V w hw).val z = (w - z)⁻¹ :=
  of_apply _ _ z

/-- Restricting a Cauchy kernel to a smaller open domain yields the Cauchy kernel on that
domain. -/
@[simp]
theorem restrict_cauchyKernel {U V : Opens ℂ} (hVU : V ≤ U) (w : ℂ) (hw : w ∉ (U : Set ℂ)) :
    restrict hVU (cauchyKernel U w hw) = cauchyKernel V w (fun h => hw (hVU h)) :=
  Subtype.ext (by ext z; simp)

/-- The germ of a Cauchy kernel is represented by `z ↦ (w - z)⁻¹`. -/
@[simp]
theorem toGerm_cauchyKernel {s : Set ℂ} {V : Opens ℂ} (hs : s ⊆ V) (w : ℂ)
    (hw : w ∉ (V : Set ℂ)) :
    toGerm hs (cauchyKernel V w hw) =
      holomorphicGerms.ofFun (fun z => (w - z)⁻¹)
        (((analyticOnNhd_const (v := w)).fun_sub analyticOnNhd_id).fun_inv
          fun _ hz => sub_ne_zero.mpr fun h => hw (hs (h ▸ hz))) := by
  rw [cauchyKernel, toGerm_of]

/-! ### Cauchy Riemann sums -/

private theorem lineMap_div_mem_biUnion_segment {E : Finset (ℂ × ℂ)} (e : E) {n : ℕ} (k : Fin n) :
    AffineMap.lineMap e.1.1 e.1.2 ((k : ℝ) / (n : ℝ)) ∈ ⋃ pq ∈ E, segment ℝ pq.1 pq.2 := by
  refine mem_biUnion e.2 ?_; rw [segment_eq_image_lineMap]
  exact mem_image_of_mem _ ⟨div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n),
    div_le_one_of_le₀ (Nat.cast_le.mpr k.isLt.le) (Nat.cast_nonneg n)⟩

/-- **Cauchy Riemann sum** in `holomorphicFunctions V` associated to `f : holomorphicFunctions U`
along a finite family `E` of oriented segments disjoint from `V`: the `n`-point left-endpoint
Riemann sum of `(2πi)⁻¹ ∫ f(w) (w - z)⁻¹ dw` summed over the segments of `E`. -/
def cauchyRiemannSum {U V : Opens ℂ} {E : Finset (ℂ × ℂ)}
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (f : holomorphicFunctions U) (n : ℕ) : holomorphicFunctions V :=
  algebraMap ℂ (holomorphicFunctions V) ((2 * π * I)⁻¹ * (n : ℂ)⁻¹) *
    ∑ e ∈ E.attach, ∑ k : Fin n,
      algebraMap ℂ (holomorphicFunctions V)
        (extend f (AffineMap.lineMap e.1.1 e.1.2 ((k : ℝ) / (n : ℝ))) * (e.1.2 - e.1.1)) *
        cauchyKernel V (AffineMap.lineMap e.1.1 e.1.2 ((k : ℝ) / (n : ℝ)))
          (Set.disjoint_left.mp hEV (lineMap_div_mem_biUnion_segment e k))

/-- Any unital complex-algebra homomorphism `Ψ : holomorphicFunctions V → A` maps
`cauchyRiemannSum` to the corresponding finite linear combination of images of `cauchyKernel`. -/
theorem map_cauchyRiemannSum {A F : Type*} [Semiring A] [Algebra ℂ A]
    {U V : Opens ℂ} [FunLike F (holomorphicFunctions V) A]
    [AlgHomClass F ℂ (holomorphicFunctions V) A] (Ψ : F) {E : Finset (ℂ × ℂ)}
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (f : holomorphicFunctions U) (n : ℕ) {g : ℂ → A}
    (hΨ : ∀ (w : ℂ) (hw : w ∉ (V : Set ℂ)), Ψ (cauchyKernel V w hw) = g w) :
    Ψ (cauchyRiemannSum hEV f n) =
      ((2 * π * I)⁻¹ * (n : ℂ)⁻¹) •
        ∑ e ∈ E, ∑ k ∈ Finset.range n,
          (extend f (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) * (e.2 - e.1)) •
            g (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) := by
  simp only [cauchyRiemannSum, map_mul, AlgHomClass.commutes, map_sum, Algebra.smul_def]
  congr 1; rw [← Finset.sum_attach E]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => by rw [hΨ]

/-- Pointwise formula for `cauchyRiemannSum` at `z : V`. -/
@[simp]
theorem cauchyRiemannSum_apply {U V : Opens ℂ} {E : Finset (ℂ × ℂ)}
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (f : holomorphicFunctions U) (n : ℕ) (z : V) :
    (cauchyRiemannSum hEV f n).val z =
      ((2 * π * I)⁻¹ * (n : ℂ)⁻¹) *
        ∑ e ∈ E, ∑ k ∈ Finset.range n,
          (extend f (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) * (e.2 - e.1)) *
            (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ)) - (z : ℂ))⁻¹ := by
  simpa only [AlgHom.comp_apply, Subalgebra.val_apply, ContinuousMap.evalAlgHom_apply,
    smul_eq_mul] using
    map_cauchyRiemannSum ((ContinuousMap.evalAlgHom ℂ ℂ z).comp (holomorphicFunctions V).val)
      hEV f n (g := fun w => (w - (z : ℂ))⁻¹) fun w hw => by simp

private def cauchySegmentIntegrand {U : Opens ℂ} (f : holomorphicFunctions U)
    (e : ℂ × ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  (2 * π * I)⁻¹ *
    ((e.2 - e.1) * (extend f (AffineMap.lineMap e.1 e.2 t) / (AffineMap.lineMap e.1 e.2 t - z)))

private theorem continuousOn_cauchySegmentIntegrand {U : Opens ℂ} {E : Finset (ℂ × ℂ)}
    (hEU : (⋃ pq ∈ E, segment ℝ pq.1 pq.2) ⊆ U) (f : holomorphicFunctions U)
    {e : ℂ × ℂ} (he : e ∈ E) {L : Set ℂ}
    (hEL : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) L) :
    ContinuousOn (Function.uncurry (cauchySegmentIntegrand f e)) (L ×ˢ Icc (0 : ℝ) 1) := by
  let φ : ℂ × ℝ → ℂ := fun p => AffineMap.lineMap e.1 e.2 p.2
  have hφ_cont : Continuous φ := AffineMap.lineMap_continuous.comp continuous_snd
  have hφ_mem : ∀ p ∈ L ×ˢ Icc (0 : ℝ) 1, φ p ∈ ⋃ pq ∈ E, segment ℝ pq.1 pq.2 := fun p hp =>
    mem_biUnion he (by rw [segment_eq_image_lineMap]; exact mem_image_of_mem _ hp.2)
  refine continuousOn_const.mul (continuousOn_const.mul ?_)
  exact (((differentiableOn_extend f).continuousOn.mono hEU).comp hφ_cont.continuousOn
    hφ_mem).div (hφ_cont.sub continuous_fst).continuousOn fun p hp =>
      sub_ne_zero.mpr fun h => Set.disjoint_right.mp hEL hp.1 (h ▸ hφ_mem p hp)

private theorem extend_eq_integral_sum_ofBalancedSegments {U : Opens ℂ} {E : Finset (ℂ × ℂ)}
    (hbal : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (hEU : (⋃ pq ∈ E, segment ℝ pq.1 pq.2) ⊆ U)
    (hnull : (Cycle.ofBalancedSegments hbal).IsNullHomologous U)
    (f : holomorphicFunctions U) {z : ℂ} (hzS : z ∉ ⋃ pq ∈ E, segment ℝ pq.1 pq.2)
    (hwz : Cycle.windingNumber z (Cycle.ofBalancedSegments hbal) = 1) :
    extend f z = ∫ t in (0 : ℝ)..1, ∑ e ∈ E, cauchySegmentIntegrand f e z t := by
  have hΓU : (Cycle.ofBalancedSegments hbal).IsIn U :=
    Cycle.isIn_iff.mpr ((Cycle.trace_ofBalancedSegments_subset hbal).trans hEU)
  have hzΓ : z ∉ Cycle.trace (Cycle.ofBalancedSegments hbal) :=
    fun ht => hzS (Cycle.trace_ofBalancedSegments_subset hbal ht)
  have hcif := Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f)
    hΓU hnull hzΓ
  rw [hwz, mul_one] at hcif
  have hseg := Cycle.integral_ofBalancedSegments hbal (f := fun w => extend f w / (w - z)) <|
    ((differentiableOn_extend f).continuousOn.mono hEU).div
      (continuousOn_id.sub continuousOn_const) fun w hw => sub_ne_zero.mpr fun h => hzS (h ▸ hw)
  have hint : ∀ e ∈ E, IntervalIntegrable (cauchySegmentIntegrand f e z) MeasureTheory.volume 0 1 :=
    fun e he => ContinuousOn.intervalIntegrable <| by
      rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
      exact ((continuousOn_cauchySegmentIntegrand hEU f he
        (Set.disjoint_singleton_right.mpr hzS)).comp
          (continuous_const.prodMk continuous_id).continuousOn
          fun t ht => ⟨rfl, ht⟩).congr fun _ _ => rfl
  rw [_root_.intervalIntegral.integral_finsetSum hint,
    ← inv_mul_cancel_left₀ two_pi_I_ne_zero (extend f z), ← hcif, hseg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp [cauchySegmentIntegrand]
  rw [_root_.intervalIntegral.integral_const_mul, _root_.intervalIntegral.integral_const_mul]

/-- If `E` is a balanced family of segments in `U` disjoint from `V ≤ U` whose cycle is
null-homologous in `U` and winds once around every point of `V`, then for every
`f : holomorphicFunctions U`, the Cauchy Riemann sums `cauchyRiemannSum hEV f n` converge to
`restrict hVU f` in `holomorphicFunctions V`. -/
theorem tendsto_cauchyRiemannSum {U V : Opens ℂ} (hVU : V ≤ U) {E : Finset (ℂ × ℂ)}
    (hbal : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (hEU : (⋃ pq ∈ E, segment ℝ pq.1 pq.2) ⊆ U)
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (hnull : (Cycle.ofBalancedSegments hbal).IsNullHomologous U)
    (hwV : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z (Cycle.ofBalancedSegments hbal) = 1)
    (f : holomorphicFunctions U) :
    Tendsto (cauchyRiemannSum hEV f) atTop (𝓝 (restrict hVU f)) := by
  rw [tendsto_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact V.isOpen]
  intro L hLV hL
  have hcont : ContinuousOn (Function.uncurry fun z t => ∑ e ∈ E, cauchySegmentIntegrand f e z t)
      (L ×ˢ Icc (0 : ℝ) 1) := by
    rw [Function.uncurry_def]
    exact continuousOn_finsetSum E fun e he =>
      continuousOn_cauchySegmentIntegrand hEU f he (hEV.mono_right hLV)
  refine ((TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum_unitInterval hL hcont).congr
    ?_).congr_right fun z hzL => ?_
  · refine Eventually.of_forall fun n z hzL => ?_
    dsimp only
    rw [Finset.sum_comm, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Finset.mul_sum, extend_apply _ ⟨z, hLV hzL⟩, cauchyRiemannSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      dsimp [cauchySegmentIntegrand]; rw [div_eq_mul_inv]; ring
  · dsimp only
    rw [← extend_eq_integral_sum_ofBalancedSegments hbal hEU hnull f
        (Set.disjoint_right.mp hEV (hLV hzL)) (hwV z (hLV hzL)),
      extend_apply _ ⟨z, hLV hzL⟩, restrict_apply, ← extend_apply f ⟨z, hVU (hLV hzL)⟩]

end HolomorphicFunctions

end TauCeti

section CauchyRiemannSum

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

/-- Around any compact subset `K` of an open set `U ⊆ ℂ`, there exist a smaller open neighbourhood
`V ≤ U` of `K` and a finite family `E` of oriented segments disjoint from `V` such that for every
`f : holomorphicFunctions U`, the Cauchy Riemann sums `cauchyRiemannSum hEV f n` converge in
`holomorphicFunctions V` to `restrict hVU f`. -/
theorem IsCompact.exists_opens_tendsto_cauchyRiemannSum {K : Set ℂ} (hK : IsCompact K)
    {U : Opens ℂ} (hKU : K ⊆ U) :
    ∃ (V : Opens ℂ) (_ : K ⊆ V) (hVU : V ≤ U) (E : Finset (ℂ × ℂ))
      (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ)),
      ∀ f : holomorphicFunctions U,
        Tendsto (cauchyRiemannSum hEV f) atTop (𝓝 (restrict hVU f)) := by
  obtain ⟨E, hbal, hsub, hnull, hwK⟩ := hK.exists_balancedSegments_windingNumber_eq_one U.isOpen hKU
  set S : Set ℂ := ⋃ pq ∈ E, segment ℝ pq.1 pq.2
  set Γ : Cycle := Cycle.ofBalancedSegments hbal
  have hS_compact : IsCompact S := E.finite_toSet.isCompact_biUnion fun pq _ => by
    rw [segment_eq_image_lineMap]; exact isCompact_Icc.image AffineMap.lineMap_continuous
  let W : Set ℂ :=
    Subtype.val '' {z : {z : ℂ // z ∉ Cycle.trace Γ} | Cycle.windingNumber z Γ = 1}
  have hW_open : IsOpen W := (Cycle.isCompact_trace Γ).isClosed.isOpen_compl.isOpenMap_subtype_val _
    ((Cycle.isLocallyConstant_windingNumber Γ).isOpen_fiber 1)
  let V : Opens ℂ := ⟨((U : Set ℂ) \ S) ∩ W, (U.isOpen.sdiff hS_compact.isClosed).inter hW_open⟩
  have hKV : K ⊆ V := fun z hzK =>
    have hzS : z ∉ S := fun hzS => (hsub hzS).2 hzK
    ⟨⟨hKU hzK, hzS⟩, ⟨⟨z, fun ht => hzS (Cycle.trace_ofBalancedSegments_subset hbal ht)⟩,
      hwK z hzK, rfl⟩⟩
  have hVU : V ≤ U := fun _ hz => hz.1.1
  have hEV : Disjoint S (V : Set ℂ) := Set.disjoint_left.mpr fun _ hzS hzV => hzV.1.2 hzS
  exact ⟨V, hKV, hVU, E, hEV,
    tendsto_cauchyRiemannSum hVU hbal (hsub.trans sdiff_subset) hEV hnull
      (by rintro z ⟨-, ⟨w, hw, rfl⟩⟩; exact hw)⟩

end CauchyRiemannSum
