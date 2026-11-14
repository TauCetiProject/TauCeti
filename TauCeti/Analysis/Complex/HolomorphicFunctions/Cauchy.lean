/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Analysis.Contour.Cycle.Grid
public import TauCeti.Analysis.Contour.Cycle.Residue
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Cauchy kernels and Cauchy Riemann sums in algebras of holomorphic functions

For a pole `w` outside an open set `V ⊆ ℂ`, `HolomorphicFunctions.cauchyKernel V w hw` is the
holomorphic function `z ↦ (w - z)⁻¹` on `V`. Given a finite family `E` of closed segments disjoint
from `V` and a scalar function `g : ℂ → ℂ`, `HolomorphicFunctions.cauchyRiemannSum V g E hEV N` is
the normalized `(N + 1)`-point left-endpoint Riemann sum of `w ↦ g w • cauchyKernel V w _` summed
over the segments of `E`.

When `V ≤ U`, `f : holomorphicFunctions U`, and `E` carries a cycle `Γ` in `U \ V` that is
null-homologous in `U`, winds once around every point of `V`, and integrates continuous functions as
the sum of their segment integrals over `E`, the sequence `cauchyRiemannSum V (extend f) E hEV`
converges to `restrict hVU f` in `holomorphicFunctions V` (uniformly on compact subsets of `V`).
Combined with `IsCompact.exists_segments_cycle_windingNumber_eq_one`, every compact subset `K ⊆ U`
admits a smaller open neighbourhood `V` of `K` with `V ≤ U` and a finite segment family `E` in
`U \ V` on which these rational Cauchy sums converge to `restrict hVU f`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
* L. Ahlfors, *Complex Analysis*, Ch. 4.
-/

public noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace Topology
open scoped Real

namespace TauCeti.HolomorphicFunctions

open Contour

/-- Uniform partition points `lineMap p q (k / (N + 1))` for `k ≤ N + 1` lie in `segment ℝ p q`. -/
theorem lineMap_div_mem_segment (p q : ℂ) {N k : ℕ} (hk : k ≤ N + 1) :
    AffineMap.lineMap (k := ℝ) p q ((k : ℝ) / (N + 1 : ℝ)) ∈ segment ℝ p q := by
  have hN1 : (0 : ℝ) < N + 1 := Nat.cast_add_one_pos N
  rw [segment_eq_image_lineMap]
  exact mem_image_of_mem _ ⟨div_nonneg k.cast_nonneg hN1.le,
    (div_le_one hN1).mpr (by exact_mod_cast hk)⟩

/-- Uniform partition points on a segment `e ∈ E` belong to `⋃ e ∈ E, segment ℝ e.1 e.2`. -/
theorem lineMap_div_mem_biUnion_segment {E : Finset (ℂ × ℂ)} {e : ℂ × ℂ} (he : e ∈ E)
    {N k : ℕ} (hk : k ≤ N + 1) :
    AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ)) ∈ ⋃ e ∈ E, segment ℝ e.1 e.2 :=
  mem_biUnion he (lineMap_div_mem_segment e.1 e.2 hk)

/-- The holomorphic Cauchy kernel `z ↦ (w - z)⁻¹` on an open set `V` avoiding `w`. -/
def cauchyKernel (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) : holomorphicFunctions V :=
  of V (fun z ↦ (w - z)⁻¹)
    (((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz ↦
      sub_ne_zero.mpr fun (h : w = _) ↦ hw (h ▸ hz))

/-- Express `cauchyKernel` as `HolomorphicFunctions.of` applied to `z ↦ (w - z)⁻¹`. -/
theorem cauchyKernel_def (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) :
    cauchyKernel V w hw = of V (fun z ↦ (w - z)⁻¹)
      (((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz ↦
        sub_ne_zero.mpr fun (h : w = _) ↦ hw (h ▸ hz)) := (rfl)

@[simp]
theorem cauchyKernel_apply (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) (z : V) :
    (cauchyKernel V w hw).val z = (w - z.val)⁻¹ := by
  rw [cauchyKernel_def, of_apply]

/-- Restricting the domain of a Cauchy kernel gives the Cauchy kernel on the smaller domain. -/
@[simp]
theorem restrict_cauchyKernel {V W : Opens ℂ} (hWV : W ≤ V) (w : ℂ) (hw : w ∉ (V : Set ℂ)) :
    restrict hWV (cauchyKernel V w hw) = cauchyKernel W w (fun hwW ↦ hw (hWV hwW)) := by
  rw [cauchyKernel_def, cauchyKernel_def, restrict_of]

/-- Normalized `(N + 1)`-point left-endpoint Riemann sum of `w ↦ g w • cauchyKernel V w _` over a
finite family `E` of segments disjoint from `V`. -/
def cauchyRiemannSum (V : Opens ℂ) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (N : ℕ) :
    holomorphicFunctions V :=
  (2 * π * I)⁻¹ • ∑ e ∈ E.attach, ((e.val.2 - e.val.1) / (N + 1 : ℂ)) •
    ∑ k ∈ (Finset.range (N + 1)).attach,
      g (AffineMap.lineMap (k := ℝ) e.val.1 e.val.2 ((k.val : ℝ) / (N + 1 : ℝ))) •
        cauchyKernel V (AffineMap.lineMap (k := ℝ) e.val.1 e.val.2 ((k.val : ℝ) / (N + 1 : ℝ)))
          (hEV.notMem_of_mem_left
            (lineMap_div_mem_biUnion_segment e.property (Finset.mem_range.mp k.property).le))

/-- Image of `cauchyRiemannSum` under any complex-algebra homomorphism `ψ` whose values on the
Cauchy kernels with poles on `E` are given by `r : ℂ → B`. -/
theorem map_cauchyRiemannSum {V : Opens ℂ} {B : Type*} [Semiring B] [Algebra ℂ B]
    (ψ : holomorphicFunctions V →ₐ[ℂ] B) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (r : ℂ → B)
    (hr : ∀ (w : ℂ) (hw : w ∈ ⋃ e ∈ E, segment ℝ e.1 e.2),
      ψ (cauchyKernel V w (hEV.notMem_of_mem_left hw)) = r w)
    (N : ℕ) :
    ψ (cauchyRiemannSum V g E hEV N) =
      (2 * π * I)⁻¹ • ∑ e ∈ E, ((e.2 - e.1) / (N + 1 : ℂ)) •
        ∑ k ∈ Finset.range (N + 1),
          g (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))) •
            r (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))) := by
  unfold cauchyRiemannSum
  rw [map_smul, map_sum]
  congr 1
  rw [← Finset.sum_attach E]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [map_smul, map_sum]
  congr 1
  rw [← Finset.sum_attach (Finset.range (N + 1))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, hr _
    (lineMap_div_mem_biUnion_segment e.property (Finset.mem_range.mp k.property).le)]

@[simp]
theorem cauchyRiemannSum_apply (V : Opens ℂ) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (N : ℕ) (z : V) :
    (cauchyRiemannSum V g E hEV N).val z =
      (2 * π * I)⁻¹ * ∑ e ∈ E, ((e.2 - e.1) / (N + 1 : ℂ)) *
        ∑ k ∈ Finset.range (N + 1),
          g (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ))) /
            (AffineMap.lineMap (k := ℝ) e.1 e.2 ((k : ℝ) / (N + 1 : ℝ)) - z.val) := by
  have h := map_cauchyRiemannSum
    ((ContinuousMap.evalAlgHom ℂ ℂ z).comp (holomorphicFunctions V).val)
    g E hEV (fun w ↦ (w - z.val)⁻¹) (fun _ _ ↦ cauchyKernel_apply _ _ _ _) N
  simpa only [AlgHom.comp_apply, Subalgebra.coe_val, ContinuousMap.evalAlgHom_apply, smul_eq_mul,
    div_eq_mul_inv] using h

private theorem continuousOn_segmentIntegrand {U V : Opens ℂ} (f : holomorphicFunctions U)
    {p q : ℂ} (hpqU : segment ℝ p q ⊆ (U : Set ℂ)) (hpqV : Disjoint (segment ℝ p q) (V : Set ℂ)) :
    ContinuousOn
      (fun x : ℝ × V ↦ (q - p) * (extend f (AffineMap.lineMap (k := ℝ) p q x.1) /
        (AffineMap.lineMap (k := ℝ) p q x.1 - x.2.val)))
      (Icc 0 1 ×ˢ univ) := by
  have hline : Continuous fun x : ℝ × V ↦ AffineMap.lineMap (k := ℝ) p q x.1 :=
    (AffineMap.lineMap_continuous (R := ℝ) (p := p) (q := q)).comp continuous_fst
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set V),
      AffineMap.lineMap (k := ℝ) p q x.1 ∈ segment ℝ p q := fun x hx ↦
    segment_eq_image_lineMap ℝ p q ▸ mem_image_of_mem _ hx.1
  have hnum : ContinuousOn (fun x : ℝ × V ↦ extend f (AffineMap.lineMap (k := ℝ) p q x.1))
      (Icc 0 1 ×ˢ univ) :=
    ((differentiableOn_extend f).continuousOn.mono hpqU).comp hline.continuousOn hmem
  have hden : ContinuousOn (fun x : ℝ × V ↦ AffineMap.lineMap (k := ℝ) p q x.1 - x.2.val)
      (Icc 0 1 ×ˢ univ) :=
    (hline.sub (continuous_subtype_val.comp continuous_snd)).continuousOn
  exact continuousOn_const.mul <| hnum.div hden fun x hx ↦
    sub_ne_zero.mpr fun h ↦ hpqV.notMem_of_mem_left (hmem x hx) (by rw [h]; exact x.2.property)

private theorem integral_segmentSum_eq_restrict {U V : Opens ℂ} (hVU : V ≤ U)
    (f : holomorphicFunctions U) (E : Finset (ℂ × ℂ))
    (hEU : (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (Γ : Cycle)
    (hΓ : Γ.IsIn (⋃ e ∈ E, segment ℝ e.1 e.2)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1)
    (hint : ∀ {g : ℂ → ℂ}, ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2) →
      Cycle.integral g Γ =
        ∑ e ∈ E, (e.2 - e.1) * ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t))
    (z : V) :
    (∫ t in (0 : ℝ)..1, (2 * π * I)⁻¹ * ∑ e ∈ E,
      (e.2 - e.1) * (extend f (AffineMap.lineMap (k := ℝ) e.1 e.2 t) /
        (AffineMap.lineMap (k := ℝ) e.1 e.2 t - z.val))) = (restrict hVU f).val z := by
  have hint_e : ∀ e ∈ E, IntervalIntegrable
      (fun t ↦ (e.2 - e.1) * (extend f (AffineMap.lineMap (k := ℝ) e.1 e.2 t) /
        (AffineMap.lineMap (k := ℝ) e.1 e.2 t - z.val))) volume 0 1 := fun e he ↦
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      ((continuousOn_segmentIntegrand f
        ((subset_biUnion_of_mem (u := fun x : ℂ × ℂ ↦ segment ℝ x.1 x.2) he).trans hEU)
        (hEV.mono_left (subset_biUnion_of_mem (u := fun x : ℂ × ℂ ↦ segment ℝ x.1 x.2) he))).comp
          (f := fun t : ℝ ↦ (t, z)) (continuous_id.prodMk continuous_const).continuousOn
          fun _ ht ↦ ⟨ht, trivial⟩)
  simp only [_root_.intervalIntegral.integral_const_mul,
    _root_.intervalIntegral.integral_finsetSum hint_e]
  have hcont : ContinuousOn (fun w ↦ extend f w / (w - z.val)) (⋃ e ∈ E, segment ℝ e.1 e.2) :=
    ((differentiableOn_extend f).continuousOn.mono hEU).div
      (continuousOn_id.sub continuousOn_const) fun _ hwS ↦
        sub_ne_zero.mpr fun h ↦ hEV.notMem_of_mem_left hwS (by rw [h]; exact z.property)
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr ((Cycle.isIn_iff.mp hΓ).trans hEU)
  have hoff : z.val ∉ Cycle.trace Γ := fun hzΓ ↦
    hEV.notMem_of_mem_left (Cycle.isIn_iff.mp hΓ hzΓ) z.property
  rw [← hint hcont,
    Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f) hΓU hn hoff,
    hw z.val z.property, mul_one, extend_apply f ⟨z.val, hVU z.property⟩,
    inv_mul_cancel_left₀ two_pi_I_ne_zero, restrict_apply]

/-- **Convergence of Cauchy Riemann sums in `holomorphicFunctions V`.** If `V ≤ U`, `f` is
holomorphic on `U`, and a finite segment family `E` in `U \ V` carries a cycle `Γ` that is
null-homologous in `U`, winds once around every point of `V`, and integrates continuous scalar
functions as the sum of their segment integrals over `E`, then `cauchyRiemannSum V (extend f) E hEV`
converges to `restrict hVU f` in `holomorphicFunctions V`. -/
theorem tendsto_cauchyRiemannSum {U V : Opens ℂ} (hVU : V ≤ U) (f : holomorphicFunctions U)
    (E : Finset (ℂ × ℂ)) (hEU : (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (Γ : Cycle)
    (hΓ : Γ.IsIn (⋃ e ∈ E, segment ℝ e.1 e.2)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1)
    (hint : ∀ {g : ℂ → ℂ}, ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2) →
      Cycle.integral g Γ =
        ∑ e ∈ E, (e.2 - e.1) * ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t)) :
    Tendsto (cauchyRiemannSum V (extend f) E hEV) atTop (𝓝 (restrict hVU f)) := by
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  let F : ℝ → V → ℂ := fun t z ↦ (2 * π * I)⁻¹ * ∑ e ∈ E,
    (e.2 - e.1) * (extend f (AffineMap.lineMap (k := ℝ) e.1 e.2 t) /
      (AffineMap.lineMap (k := ℝ) e.1 e.2 t - z.val))
  have hseg : ∀ e ∈ E, ContinuousOn
      (fun x : ℝ × V ↦ (e.2 - e.1) * (extend f (AffineMap.lineMap (k := ℝ) e.1 e.2 x.1) /
        (AffineMap.lineMap (k := ℝ) e.1 e.2 x.1 - x.2.val)))
      (Icc 0 1 ×ˢ univ) := fun e he ↦
    continuousOn_segmentIntegrand f
      ((subset_biUnion_of_mem (u := fun x : ℂ × ℂ ↦ segment ℝ x.1 x.2) he).trans hEU)
      (hEV.mono_left (subset_biUnion_of_mem (u := fun x : ℂ × ℂ ↦ segment ℝ x.1 x.2) he))
  have hF_cont : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ K) :=
    (continuousOn_const.mul (continuousOn_finsetSum E hseg)).mono
      (prod_mono Subset.rfl (subset_univ K))
  have hriem := TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum_zero_one hK hF_cont
  rw [Metric.tendstoUniformlyOn_iff] at hriem ⊢
  refine fun ε hε ↦ (hriem ε hε).mono fun N hN z hz ↦ ?_
  convert hN z hz using 2
  · exact (integral_segmentSum_eq_restrict hVU f E hEU hEV Γ hΓ hn hw hint z).symm
  · rw [cauchyRiemannSum_apply, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
    ring

end TauCeti.HolomorphicFunctions

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions in
/-- **Existence of an inner neighbourhood and polygonal cycle for Cauchy Riemann sums.** Given a
compact subset `K` of an open set `U ⊆ ℂ`, there exist an open neighbourhood `V` of `K` with
`V ≤ U`, a finite segment family `E` in `U \ V`, and a cycle `Γ` carried on `E` that is
null-homologous in `U`, winds once around every point of `V`, and integrates continuous
Banach-space-valued functions as the sum of their segment integrals over `E`. -/
theorem IsCompact.exists_open_segments_cycle_windingNumber_eq_one.{u} {K : Set ℂ}
    (hK : IsCompact K) (U : Opens ℂ) (hKU : K ⊆ U) :
    ∃ (V : Opens ℂ) (_ : K ⊆ V) (_ : V ≤ U) (E : Finset (ℂ × ℂ)) (Γ : Cycle),
      (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ) ∧
      Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ) ∧
      Γ.IsIn (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      Γ.IsNullHomologous U ∧
      (∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {g : ℂ → F},
        ContinuousOn g (⋃ e ∈ E, segment ℝ e.1 e.2) → Cycle.integral g Γ =
          ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, g (AffineMap.lineMap e.1 e.2 t) := by
  obtain ⟨E, Γ, hsub, hΓ, hn, hw, hint⟩ :=
    hK.exists_segments_cycle_windingNumber_eq_one.{u} U.isOpen hKU
  let S : Set ℂ := ⋃ e ∈ E, segment ℝ e.1 e.2
  have hS_closed : IsClosed S := isClosed_biUnion_finset fun e _ ↦ by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  let W₁ : Set ℂ := Subtype.val '' {z : {z : ℂ // z ∉ Cycle.trace Γ} | Cycle.windingNumber z Γ = 1}
  have hW₁_open : IsOpen W₁ :=
    (Cycle.isCompact_trace Γ).isClosed.isOpen_compl.isOpenMap_subtype_val _
      ((Cycle.isLocallyConstant_windingNumber Γ).isOpen_fiber 1)
  let V : Opens ℂ := ⟨(U : Set ℂ) ∩ Sᶜ ∩ W₁, (U.isOpen.inter hS_closed.isOpen_compl).inter hW₁_open⟩
  have hKV : K ⊆ V := fun z hz ↦
    ⟨⟨hKU hz, fun hzS ↦ (hsub hzS).2 hz⟩,
      ⟨⟨z, fun hzΓ ↦ (hsub (Cycle.isIn_iff.mp hΓ hzΓ)).2 hz⟩, hw z hz, rfl⟩⟩
  refine ⟨V, hKV, fun _ hz ↦ hz.1.1, E, Γ, hsub.trans sdiff_subset,
    Set.disjoint_left.mpr fun _ hzS hzV ↦ hzV.1.2 hzS, hΓ, hn, ?_, hint⟩
  rintro _ ⟨-, w, hw1, rfl⟩
  exact hw1

open TauCeti TauCeti.HolomorphicFunctions in
/-- **Cauchy Riemann sum approximation on a neighbourhood of a compact set.** For a compact subset
`K ⊆ U` and `f : holomorphicFunctions U`, there exist an open neighbourhood `V` of `K` with `V ≤ U`
and a finite segment family `E` in `U \ V` such that `cauchyRiemannSum V (extend f) E hEV` converges
to `restrict hVU f` in `holomorphicFunctions V`. -/
theorem IsCompact.exists_cauchyRiemannSum_tendsto {K : Set ℂ} (hK : IsCompact K) (U : Opens ℂ)
    (hKU : K ⊆ U) (f : holomorphicFunctions U) :
    ∃ (V : Opens ℂ) (_ : K ⊆ V) (hVU : V ≤ U) (E : Finset (ℂ × ℂ))
      (_ : (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ))
      (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)),
      Tendsto (cauchyRiemannSum V (extend f) E hEV) atTop (𝓝 (restrict hVU f)) := by
  obtain ⟨V, hKV, hVU, E, Γ, hEU, hEV, hΓ, hn, hw, hint⟩ :=
    hK.exists_open_segments_cycle_windingNumber_eq_one.{0} U hKU
  exact ⟨V, hKV, hVU, E, hEU, hEV, tendsto_cauchyRiemannSum hVU f E hEU hEV Γ hΓ hn hw hint⟩
