/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ
public import TauCeti.Analysis.Contour.Cycle.Grid
public import TauCeti.Analysis.Contour.Cycle.Residue
import TauCeti.Analysis.Convex.Segment
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Cauchy kernels and Cauchy Riemann sums in algebras of holomorphic functions

This file approximates holomorphic functions near a compact subset `K ⊆ U` on an inner open
neighbourhood `V` by finite complex-linear combinations of Cauchy kernels `(w - ·)⁻¹` in the
compact-open topology, without invoking Runge's theorem. Because any algebra homomorphism on
`holomorphicGerms K` sending the coordinate germ to an element `a` of a Banach algebra is forced to
send Cauchy kernels to resolvents, these approximations feed uniqueness of continuous algebra
homomorphisms on `holomorphicGerms K` (such as `holomorphicCalculus`).

For a pole `w` outside an open set `V ⊆ ℂ`, `HolomorphicFunctions.cauchyKernel V w hw` is the
holomorphic function `z ↦ (w - z)⁻¹` on `V`. Given a finite family `E` of closed segments disjoint
from `V` and a scalar function `g : ℂ → ℂ`, `HolomorphicFunctions.cauchyRiemannSum V g E hEV N` is
the normalized `(N + 1)`-point left-endpoint Riemann sum of `w ↦ g w • cauchyKernel V w _` summed
over the segments of `E`.

When `V ≤ U`, `f : holomorphicFunctions U`, and `E` carries a cycle `Γ` in `U \ V` that is
null-homologous in `U`, winds once around every point of `V`, and integrates continuous functions as
the sum of their segment integrals over `E`, the sequence `cauchyRiemannSum V (extend f) E hEV`
converges to `restrict hVU f` in `holomorphicFunctions V` (uniformly on compact subsets of `V`).
Combined with `IsCompact.exists_open_segments_cycle_windingNumber_eq_one`, every compact subset
`K ⊆ U` admits a smaller open neighbourhood `V` of `K` with `V ≤ U` and a finite segment family
`E` in `U \ V` on which these rational Cauchy sums converge to `restrict hVU f` for every
`f : holomorphicFunctions U`.

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

/-- The germ of a Cauchy kernel near `s ⊆ V` is represented by `z ↦ (w - z)⁻¹`. -/
@[simp]
theorem toGerm_cauchyKernel {s : Set ℂ} {V : Opens ℂ} (hs : s ⊆ V) (w : ℂ)
    (hw : w ∉ (V : Set ℂ)) :
    toGerm hs (cauchyKernel V w hw) =
      holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹)
        (((((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz ↦
          sub_ne_zero.mpr fun (h : w = _) ↦ hw (h ▸ hz)).analyticOnNhd V.isOpen).mono hs) := by
  rw [cauchyKernel_def, toGerm_of]

/-- Normalized `(N + 1)`-point left-endpoint Riemann sum of `w ↦ g w • cauchyKernel V w _` over a
finite family `E` of segments disjoint from `V`. -/
def cauchyRiemannSum (V : Opens ℂ) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
    (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (N : ℕ) :
    holomorphicFunctions V :=
  (2 * π * I)⁻¹ • ∑ e ∈ E.attach, ((e.val.2 - e.val.1) / (N + 1 : ℂ)) •
    ∑ k ∈ (Finset.range (N + 1)).attach,
      g (AffineMap.lineMap (k := ℝ) e.val.1 e.val.2 ((k.val : ℝ) / (N + 1 : ℝ))) •
        cauchyKernel V (AffineMap.lineMap (k := ℝ) e.val.1 e.val.2 ((k.val : ℝ) / (N + 1 : ℝ)))
          (hEV.notMem_of_mem_left <| mem_biUnion e.property <|
            TauCeti.lineMap_div_mem_segment (Nat.cast_nonneg _)
              (by exact_mod_cast (Finset.mem_range.mp k.property).le))

/-- Image of `cauchyRiemannSum` under any complex-linear map `ψ` whose values on the Cauchy kernels
with poles on `E` are given by `r : ℂ → B`. -/
theorem map_cauchyRiemannSum {V : Opens ℂ} {F B : Type*} [AddCommMonoid B] [Module ℂ B]
    [FunLike F (holomorphicFunctions V) B] [LinearMapClass F ℂ (holomorphicFunctions V) B]
    (ψ : F) (g : ℂ → ℂ) (E : Finset (ℂ × ℂ))
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
  rw [map_smul, hr _ (mem_biUnion e.property <|
    TauCeti.lineMap_div_mem_segment (Nat.cast_nonneg _)
      (by exact_mod_cast (Finset.mem_range.mp k.property).le))]

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

/-- Restricting the domain of a Cauchy Riemann sum gives the Cauchy Riemann sum on the smaller
domain. -/
@[simp]
theorem restrict_cauchyRiemannSum {V W : Opens ℂ} (hWV : W ≤ V) (g : ℂ → ℂ)
    (E : Finset (ℂ × ℂ)) (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)) (N : ℕ) :
    restrict hWV (cauchyRiemannSum V g E hEV N) =
      cauchyRiemannSum W g E (hEV.mono_right hWV) N := by
  apply Subtype.ext
  ext z
  simp

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
    (hline.sub (continuous_subtypeVal.comp continuous_snd)).continuousOn
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
  · rw [cauchyRiemannSum_apply, Complex.real_smul]
    push_cast
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
    ring

end TauCeti.HolomorphicFunctions

open TauCeti TauCeti.HolomorphicFunctions in
/-- **Cauchy Riemann sum approximation on a neighbourhood of a compact set.** For a compact subset
`K ⊆ U`, there exist an open neighbourhood `V` of `K` with `V ≤ U` and a finite segment family `E`
in `U \ V` such that `cauchyRiemannSum V (extend f) E hEV` converges to `restrict hVU f` in
`holomorphicFunctions V` for every `f : holomorphicFunctions U`. -/
theorem IsCompact.exists_cauchyRiemannSum_tendsto {K : Set ℂ} (hK : IsCompact K) (U : Opens ℂ)
    (hKU : K ⊆ U) :
    ∃ (V : Opens ℂ) (_ : K ⊆ V) (hVU : V ≤ U) (E : Finset (ℂ × ℂ))
      (_ : (⋃ e ∈ E, segment ℝ e.1 e.2) ⊆ (U : Set ℂ))
      (hEV : Disjoint (⋃ e ∈ E, segment ℝ e.1 e.2) (V : Set ℂ)),
      ∀ f : holomorphicFunctions U,
        Tendsto (cauchyRiemannSum V (extend f) E hEV) atTop (𝓝 (restrict hVU f)) := by
  obtain ⟨V, E, Γ, hV, hKV, hVU, hEU, hEV, hΓ, hn, hw, hint⟩ :=
    hK.exists_open_segments_cycle_windingNumber_eq_one.{0} U.isOpen hKU
  exact ⟨⟨V, hV⟩, hKV, hVU, E, hEU, hEV, fun f ↦
    tendsto_cauchyRiemannSum (V := ⟨V, hV⟩) hVU f E hEU hEV Γ hΓ hn hw hint⟩
