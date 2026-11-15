/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Composition
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.SpectralMapping
import TauCeti.MeasureTheory.Integral.IntervalIntegral.RiemannSum

/-!
# Uniqueness and composition for the holomorphic functional calculus

This file proves the uniqueness characterization of `holomorphicCalculus a` and deduces the
composition theorem `g(f(a)) = (g ∘ f)(a)` for an element `a` of a complex Banach algebra `A`.

* **Cauchy Riemann sums:** given a compact subset `K` of an open set `U ⊆ ℂ` and a smaller open
  neighbourhood `V ≤ U` of `K` disjoint from a balanced family `E` of oriented segments in `U`
  whose cycle winds once around `V`, the `n`-point left-endpoint sums
  `HolomorphicFunctions.cauchyRiemannSum hEV f n` are finite linear combinations of Cauchy kernels
  `z ↦ (w - z)⁻¹` (`w ∈ U \ V`) converging to `restrict hVU f` in `holomorphicFunctions V`.
* **Uniqueness:** `holomorphicCalculus a` is the unique unital complex-algebra homomorphism
  `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a` whose
  restriction `Φ.comp (toGerm ha)` to `holomorphicFunctions U` is continuous for every open
  neighbourhood `U` of `spectrum ℂ a`.
* **Composition:** for `φ : holomorphicGerms (spectrum ℂ a)` and
  `ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))`,
  `holomorphicCalculus (holomorphicCalculus a φ) ψ` equals
  `holomorphicCalculus a (φ.compAlgHom _ ψ)`, with corresponding statements for analytic
  representatives (`holomorphicCalculus_ofFun_comp`) and open neighbourhoods
  (`holomorphicCalculusOn_comp`).

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

/-! ### Cauchy kernels and Cauchy Riemann sums -/

private def evalOpenAlgHom {V : Opens ℂ} (z : V) : holomorphicFunctions V →ₐ[ℂ] ℂ where
  toFun h := h.val z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem evalOpenAlgHom_apply {V : Opens ℂ} (z : V) (h : holomorphicFunctions V) :
    evalOpenAlgHom z h = h.val z := rfl

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

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` maps the germ of `cauchyKernel V w hw` to `resolvent a w`. -/
theorem algHom_toGerm_cauchyKernel {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
    {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {V : Opens ℂ} (ha : spectrum ℂ a ⊆ V) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    Φ (toGerm ha (cauchyKernel V w hw)) = resolvent a w := by
  rw [cauchyKernel, toGerm_of]
  exact algHom_ofFun_sub_inv_left hΦ (spectrum.notMem_iff.mp fun h => hw (ha h))

private theorem lineMap_div_mem_biUnion_segment {E : Finset (ℂ × ℂ)} (e : E) {n : ℕ}
    (k : Fin n) :
    AffineMap.lineMap e.1.1 e.1.2 ((k : ℝ) / (n : ℝ)) ∈ ⋃ pq ∈ E, segment ℝ pq.1 pq.2 := by
  refine mem_biUnion e.2 ?_
  rw [segment_eq_image_lineMap]
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
  rw [← evalOpenAlgHom_apply]
  simp only [cauchyRiemannSum, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    map_sum, evalOpenAlgHom_apply, cauchyKernel_apply]
  congr 1
  rw [← Finset.sum_attach E]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` maps each Cauchy Riemann sum to the corresponding Riemann sum of
resolvents in `A`. -/
theorem algHom_toGerm_cauchyRiemannSum {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
    {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {U V : Opens ℂ} (ha : spectrum ℂ a ⊆ V) {E : Finset (ℂ × ℂ)}
    (hEV : Disjoint (⋃ pq ∈ E, segment ℝ pq.1 pq.2) (V : Set ℂ))
    (f : holomorphicFunctions U) (n : ℕ) :
    Φ (toGerm ha (cauchyRiemannSum hEV f n)) =
      ((2 * π * I)⁻¹ * (n : ℂ)⁻¹) •
        ∑ e ∈ E, ∑ k ∈ Finset.range n,
          (extend f (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) * (e.2 - e.1)) •
            resolvent a (AffineMap.lineMap e.1 e.2 ((k : ℝ) / (n : ℝ))) := by
  rw [← AlgHom.comp_apply]
  simp only [cauchyRiemannSum, map_mul, AlgHom.commutes, map_sum, Algebra.smul_def]
  congr 1
  rw [← Finset.sum_attach E]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact algHom_toGerm_cauchyKernel hΦ ha _

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
  have hφ_mem : ∀ p ∈ L ×ˢ Icc (0 : ℝ) 1, φ p ∈ ⋃ pq ∈ E, segment ℝ pq.1 pq.2 := fun p hp => by
    refine mem_biUnion he ?_
    rw [segment_eq_image_lineMap]
    exact mem_image_of_mem _ hp.2
  refine continuousOn_const.mul (continuousOn_const.mul ?_)
  refine (((differentiableOn_extend f).continuousOn.mono hEU).comp hφ_cont.continuousOn
    fun p hp => hφ_mem p hp).div ((hφ_cont.sub continuous_fst).continuousOn) fun p hp => ?_
  exact sub_ne_zero.mpr fun h => Set.disjoint_right.mp hEL hp.1 (h ▸ hφ_mem p hp)

private theorem extend_eq_integral_sum_ofBalancedSegments {U : Opens ℂ} {E : Finset (ℂ × ℂ)}
    (hbal : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (hEU : (⋃ pq ∈ E, segment ℝ pq.1 pq.2) ⊆ U)
    (hnull : (Cycle.ofBalancedSegments hbal).IsNullHomologous U)
    (f : holomorphicFunctions U) {z : ℂ}
    (hzS : z ∉ ⋃ pq ∈ E, segment ℝ pq.1 pq.2)
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
    fun e he => by
      have hpair : Continuous fun t : ℝ => (z, t) := continuous_const.prodMk continuous_id
      have hcz : ContinuousOn (cauchySegmentIntegrand f e z) (uIcc 0 1) := by
        rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
        exact ((continuousOn_cauchySegmentIntegrand hEU f he
          (Set.disjoint_singleton_right.mpr hzS)).comp hpair.continuousOn
            fun t ht => ⟨rfl, ht⟩).congr fun _ _ => rfl
      exact hcz.intervalIntegrable
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
  have hcont :
      ContinuousOn (Function.uncurry fun z t => ∑ e ∈ E, cauchySegmentIntegrand f e z t)
        (L ×ˢ Icc (0 : ℝ) 1) := by
    rw [Function.uncurry_def]
    exact continuousOn_finsetSum E fun e he =>
      continuousOn_cauchySegmentIntegrand hEU f he (hEV.mono_right hLV)
  have hriem := TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum_unitInterval hL hcont
  refine (hriem.congr ?_).congr_right ?_
  · refine Eventually.of_forall fun n z hzL => ?_
    have hzV : z ∈ V := hLV hzL
    dsimp only
    rw [Finset.sum_comm, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Finset.mul_sum, extend_apply _ ⟨z, hzV⟩, cauchyRiemannSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [cauchySegmentIntegrand]
    rw [div_eq_mul_inv]
    ring
  · intro z hzL
    have hzV : z ∈ V := hLV hzL
    dsimp only
    rw [← extend_eq_integral_sum_ofBalancedSegments hbal hEU hnull f
        (Set.disjoint_right.mp hEV hzV) (hwV z hzV),
      extend_apply _ ⟨z, hzV⟩, restrict_apply, ← extend_apply f ⟨z, hVU hzV⟩]

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
  have hS_compact : IsCompact S :=
    E.finite_toSet.isCompact_biUnion fun pq _ => by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
  let W : Set ℂ :=
    Subtype.val '' {z : {z : ℂ // z ∉ Cycle.trace Γ} | Cycle.windingNumber z Γ = 1}
  have hW_open : IsOpen W :=
    (Cycle.isCompact_trace Γ).isClosed.isOpen_compl.isOpenMap_subtype_val _
      ((Cycle.isLocallyConstant_windingNumber Γ).isOpen_fiber 1)
  let V : Opens ℂ := ⟨((U : Set ℂ) \ S) ∩ W, (U.isOpen.sdiff hS_compact.isClosed).inter hW_open⟩
  have hKV : K ⊆ V := by
    intro z hzK
    have hzS : z ∉ S := fun hzS => (hsub hzS).2 hzK
    have hzΓ : z ∉ Cycle.trace Γ := fun ht => hzS (Cycle.trace_ofBalancedSegments_subset hbal ht)
    exact ⟨⟨hKU hzK, hzS⟩, ⟨⟨z, hzΓ⟩, hwK z hzK, rfl⟩⟩
  have hVU : V ≤ U := fun _ hz => hz.1.1
  have hEV : Disjoint S (V : Set ℂ) := Set.disjoint_left.mpr fun _ hzS hzV => hzV.1.2 hzS
  have hwV : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1 := by
    rintro z ⟨-, ⟨w, hw, rfl⟩⟩
    exact hw
  exact ⟨V, hKV, hVU, E, hEV,
    tendsto_cauchyRiemannSum hVU hbal (hsub.trans sdiff_subset) hEV hnull hwV⟩

end CauchyRiemannSum

namespace TauCeti

/-! ### Uniqueness of the holomorphic functional calculus -/

section Uniqueness

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Any unital complex-algebra homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending
the coordinate germ to `a` whose restrictions to open neighbourhoods of `spectrum ℂ a` are
continuous agrees with `holomorphicCalculusOn a U ha` on every open neighbourhood `U`. -/
theorem eq_holomorphicCalculusOn (a : A) {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (V : Opens ℂ) (ha : spectrum ℂ a ⊆ V), Continuous (Φ.comp (toGerm ha)))
    (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Φ (toGerm ha f) = holomorphicCalculusOn a U ha f := by
  obtain ⟨V, hKV, hVU, E, hEV, hconv⟩ :=
    (spectrum.isCompact (𝕜 := ℂ) a).exists_opens_tendsto_cauchyRiemannSum ha
  have h₁ :
      Tendsto (fun n => Φ (toGerm hKV (cauchyRiemannSum hEV f n))) atTop
        (𝓝 (Φ (toGerm hKV (restrict hVU f)))) :=
    ((hΦ_cont V hKV).tendsto (restrict hVU f)).comp (hconv f)
  have h₂ :
      Tendsto (fun n => holomorphicCalculusOn a V hKV (cauchyRiemannSum hEV f n)) atTop
        (𝓝 (holomorphicCalculusOn a V hKV (restrict hVU f))) :=
    ((continuous_holomorphicCalculusOn a V hKV).tendsto (restrict hVU f)).comp (hconv f)
  have heq :
      (fun n => Φ (toGerm hKV (cauchyRiemannSum hEV f n))) =
        fun n => holomorphicCalculusOn a V hKV (cauchyRiemannSum hEV f n) := by
    ext n
    rw [← holomorphicCalculus_toGerm, algHom_toGerm_cauchyRiemannSum hΦ_id,
      algHom_toGerm_cauchyRiemannSum (holomorphicCalculus_id a)]
  have hlim : Φ (toGerm hKV (restrict hVU f)) = holomorphicCalculusOn a V hKV (restrict hVU f) :=
    tendsto_nhds_unique h₁ (heq ▸ h₂)
  rwa [toGerm_restrict hKV hVU f, holomorphicCalculusOn_restrict a hKV hVU f] at hlim

/-- **Uniqueness of the holomorphic functional calculus.** Any unital complex-algebra homomorphism
on `holomorphicGerms (spectrum ℂ a)` sending the coordinate germ to `a` whose restrictions to all
open neighbourhoods of `spectrum ℂ a` are continuous equals `holomorphicCalculus a`. -/
theorem eq_holomorphicCalculus (a : A) {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha))) :
    Φ = holomorphicCalculus a := by
  apply holomorphicGerms.algHom_ext
  intro U ha f
  rw [holomorphicCalculus_toGerm]
  exact eq_holomorphicCalculusOn a hΦ_id hΦ_cont U ha f

/-- Existence and uniqueness characterization of `holomorphicCalculus a`. -/
theorem holomorphicCalculus_unique (a : A) :
    ∃! Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A,
      Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha)) :=
  ⟨holomorphicCalculus a,
    ⟨holomorphicCalculus_id a, fun U ha => by
      have h : (holomorphicCalculus a).comp (toGerm ha) = holomorphicCalculusOn a U ha := by
        ext f
        exact holomorphicCalculus_toGerm a U ha f
      rw [h]
      exact continuous_holomorphicCalculusOn a U ha⟩,
    fun _ ⟨hΦ_id, hΦ_cont⟩ => eq_holomorphicCalculus a hΦ_id hΦ_cont⟩

end Uniqueness

/-! ### Composition theorem -/

section Composition

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Evaluating a holomorphic germ `φ` at any spectral value of `a` produces a spectral value of
`holomorphicCalculus a φ`. -/
theorem eval_mem_spectrum_holomorphicCalculus (a : A) (φ : holomorphicGerms (spectrum ℂ a))
    (z : ℂ) (hz : z ∈ spectrum ℂ a) :
    holomorphicGerms.eval z hz φ ∈ spectrum ℂ (holomorphicCalculus a φ) := by
  rw [spectrum_holomorphicCalculus]
  exact ⟨z, hz, rfl⟩

/-- **Composition theorem for holomorphic germs:** `ψ(φ(a)) = (ψ ∘ φ)(a)` for any
`φ : holomorphicGerms (spectrum ℂ a)` and
`ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))`. -/
theorem holomorphicCalculus_comp (a : A) (φ : holomorphicGerms (spectrum ℂ a))
    (ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a φ))) :
    holomorphicCalculus (holomorphicCalculus a φ) ψ =
      holomorphicCalculus a
        (holomorphicGerms.compAlgHom φ (eval_mem_spectrum_holomorphicCalculus a φ) ψ) := by
  let b := holomorphicCalculus a φ
  have hφ := eval_mem_spectrum_holomorphicCalculus a φ
  let Ψ : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A :=
    (holomorphicCalculus a).comp (holomorphicGerms.compAlgHom φ hφ)
  have hΨ_id : Ψ (holomorphicGerms.ofFun id analyticOnNhd_id) = b := by
    simp [Ψ, b]
  have hΨ_cont : ∀ (V : Opens ℂ) (hb : spectrum ℂ b ⊆ V), Continuous (Ψ.comp (toGerm hb)) := by
    intro V hb
    obtain ⟨U, haU, f, hfφ⟩ := holomorphicGerms.exists_toGerm_eq φ
    obtain ⟨U', haU', hU'U, hfV⟩ := exists_opens_mapsTo haU f V fun z hz => by
      rw [← eval_toGerm haU z hz f, hfφ]
      exact hb (hφ z hz)
    have hcomp :
        Ψ.comp (toGerm hb) =
          (holomorphicCalculusOn a U' haU').comp (compAlgHom (restrict hU'U f) hfV) := by
      ext g
      simp only [Ψ, AlgHom.comp_apply]
      rw [holomorphicGerms.compAlgHom_toGerm φ hφ haU f hfφ hb g haU' hU'U hfV,
        holomorphicCalculus_toGerm]
    rw [hcomp]
    exact (continuous_holomorphicCalculusOn a U' haU').comp (continuous_compAlgHom _ hfV)
  have hΨ : Ψ = holomorphicCalculus b := eq_holomorphicCalculus b hΨ_id hΨ_cont
  exact (congrArg (fun H : holomorphicGerms (spectrum ℂ b) →ₐ[ℂ] A => H ψ) hΨ).symm

/-- **Composition theorem for analytic representatives:** if `f` is analytic near `spectrum ℂ a`
and maps `spectrum ℂ a` into `t`, and `g` is analytic near `t`, then `g(f(a)) = (g ∘ f)(a)`. -/
theorem holomorphicCalculus_ofFun_comp (a : A) {t : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hft : MapsTo f (spectrum ℂ a) t)
    (hg : AnalyticOnNhd ℂ g t) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
        (holomorphicGerms.ofFun g
          (hg.mono (by rw [spectrum_holomorphicCalculus_ofFun]; exact image_subset_iff.2 hft))) =
      holomorphicCalculus a (holomorphicGerms.ofFun (g ∘ f) (hg.comp hf hft)) := by
  rw [holomorphicCalculus_comp]
  congr 1
  exact holomorphicGerms.compAlgHom_ofFun f hf
    (by rw [spectrum_holomorphicCalculus_ofFun]; exact mapsTo_image f (spectrum ℂ a)) g
    (hg.mono (by rw [spectrum_holomorphicCalculus_ofFun]; exact image_subset_iff.2 hft))

/-- **Composition theorem on open neighbourhoods:** if `f ∈ O(U)` (`σ(a) ⊆ U`), `g ∈ O(V)`
(`σ(f(a)) ⊆ V`), and `U' ≤ U` is an open neighbourhood of `σ(a)` mapped by `f` into `V`, then
`holomorphicCalculusOn (holomorphicCalculusOn a U haU f) V hbV g` agrees with
`holomorphicCalculusOn a U' haU'` applied to `g ∘ (f|_{U'})`. -/
theorem holomorphicCalculusOn_comp (a : A) {U V U' : Opens ℂ} (haU : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hbV : spectrum ℂ (holomorphicCalculusOn a U haU f) ⊆ V)
    (g : holomorphicFunctions V) (haU' : spectrum ℂ a ⊆ U') (hU'U : U' ≤ U)
    (hfV : ∀ z : U', (restrict hU'U f).val z ∈ V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U haU f) V hbV g =
      holomorphicCalculusOn a U' haU' (compAlgHom (restrict hU'U f) hfV g) := by
  have key : ∀ (b : A) (hb : b = holomorphicCalculus a (toGerm haU f))
      (hbV : spectrum ℂ b ⊆ V),
      holomorphicCalculusOn b V hbV g =
        holomorphicCalculus a
          (holomorphicGerms.compAlgHom (toGerm haU f)
            (eval_mem_spectrum_holomorphicCalculus a (toGerm haU f))
            (toGerm (hb ▸ hbV) g)) := by
    rintro _ rfl hbV
    rw [← holomorphicCalculus_toGerm, holomorphicCalculus_comp]
  rw [key _ (holomorphicCalculus_toGerm a U haU f).symm hbV,
    holomorphicGerms.compAlgHom_toGerm (toGerm haU f)
      (eval_mem_spectrum_holomorphicCalculus a (toGerm haU f)) haU f rfl _ g haU' hU'U hfV,
    holomorphicCalculus_toGerm]

end Composition

end TauCeti
