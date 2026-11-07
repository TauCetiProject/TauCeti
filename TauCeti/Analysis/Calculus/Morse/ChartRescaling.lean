/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.Calculus.FDeriv.Rescale
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Deformation

/-!
# Small-disk rescaling of Morse coordinate transitions

Suppose a coordinate transition `T`, fixing the origin, preserves the split expression
`Q(u,v) = -‖u‖² + ‖v‖²` near the origin. Its rescaling `T(s • y) / s` extends jointly
continuously at `s = 0` by `DT(0) y`, and preserves `Q` throughout the deformation.
One sufficiently small closed ball works for every `s ∈ [0,1]`: all rescaled images lie in
one controlled closed ball contained in any prescribed target neighborhood.

On the negative disk `y = (u,0)`, the equation is exactly `Q = -‖u‖²`. Thus the boundary
of a disk of radius `δ` remains at level `-δ²`, including the derivative endpoint. Composing
with the inverse of a second Morse chart gives the small-disk part of a comparison of
characteristic maps; no overlap of the original whole characteristic disks is required.

Only homogeneity of the squared norms is used, so the estimates work for arbitrary real
normed spaces. For Morse charts the spaces are the negative and positive Euclidean factors.

On real inner product spaces the rescaling is followed by two linear stages, which together
deform the small negative disk `u ↦ T (u, 0)` to `u ↦ (h u, 0)`, where `h` is the polar factor
of the negative block `A_uu` of `A = DT(0)`
(`HasFDerivAt.exists_negative_disk_homotopy_polarFactor`). First the positive component
`A_vu u` of the linearized disk `A (u, 0) = (A_uu u, A_vu u)` is contracted to zero, which does
not increase `Q`. Then `A_uu = h P` is deformed to `h` through `h P^(1-t)`
(`ContinuousLinearMap.polarDeformation`); since `A` preserves `Q`, the block `A_uu` expands
norms, and so does every stage of this deformation. Along the whole homotopy the point over `u`
stays in a prescribed neighborhood of the origin and satisfies `Q ≤ -‖u‖²`, so a boundary sphere
`‖u‖ = δ` never rises above the level `-δ²`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F} {U : Set (E × F)}

private theorem rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero (hT0 : T 0 = 0)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {s : ℝ} (hs : s ≠ 0) {y : E × F} (hy : s • y ∈ U) :
    -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
      -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  have h := hQ (s • y) hy
  rw [derivativeRescale_of_ne_zero T A hs, hT0, sub_zero]
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, norm_inv, mul_pow] at h ⊢
  have hnorm : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  field_simp
  nlinarith [h]

/-- Rescaling a transition that fixes the origin and preserves the split squared norm preserves
that expression even at scale zero. The input is required to stay in the original coordinate
domain only along its segment to the origin. -/
theorem _root_.HasFDerivAt.derivativeRescale_neg_norm_fst_sq_add_norm_snd_sq_eq
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {y : E × F} (hy : ∀ s ∈ Icc (0 : ℝ) 1, s • y ∈ U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
      -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  by_cases hs0 : s = 0
  · subst s
    -- Joint continuity supplies the missing endpoint; positive scales have the exact equation.
    have hc : ContinuousAt (fun t : ℝ ↦ derivativeRescale T A t y) 0 :=
      (hT.continuousAt_derivativeRescale_zero y).comp' (f := fun t : ℝ ↦ (t, y))
        (continuousAt_id.prodMk continuousAt_const)
    have hlim : Tendsto (fun t : ℝ ↦
        -‖(derivativeRescale T A t y).1‖ ^ 2 + ‖(derivativeRescale T A t y).2‖ ^ 2)
        (𝓝[>] 0) (𝓝 (-‖(derivativeRescale T A 0 y).1‖ ^ 2 +
          ‖(derivativeRescale T A 0 y).2‖ ^ 2)) :=
      ((hc.fst.norm.pow 2).neg.add (hc.snd.norm.pow 2)).tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    exact (rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero hT0 hQ ht.ne'
      (hy t ⟨ht.le, ht1.le⟩)).symm
  · exact rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero hT0 hQ hs0 (hy s hs)

/-- A single small disk admits the entire rescaling deformation of a split-quadratic coordinate
transition to its derivative. Both the original disk and the controlled image ball lie in the
prescribed coordinate neighborhoods. The norm bound and exact level equation hold uniformly
throughout, including at scale zero. -/
theorem _root_.HasFDerivAt.exists_small_disk_derivativeRescale
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U) (hc : ContinuousOn T U)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {V : Set (E × F)} (hV : V ∈ 𝓝 0) :
    ∃ L > 0, ‖A‖ ≤ L ∧ ∃ δ > 0,
      Metric.closedBall 0 δ ⊆ U ∧ Metric.closedBall 0 (L * δ) ⊆ V ∧
      ContinuousOn (fun p : ℝ × (E × F) ↦ derivativeRescale T A p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 δ) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : E × F) δ,
        ‖derivativeRescale T A s y‖ ≤ L * ‖y‖ ∧
        derivativeRescale T A s y ∈ V ∧
        -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
          -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  obtain ⟨L, hL, hA, δ, hδ, hδU, hδV, hb⟩ :=
    hT.exists_derivativeRescale_closedBall_subset (hU.mem_nhds h0U) hV
  have hscale {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {y : E × F}
      (hy : y ∈ Metric.closedBall 0 δ) : s • y ∈ Metric.closedBall 0 δ := by
    exact (convex_closedBall (0 : E × F) δ).smul_mem_of_zero_mem
      (Metric.mem_closedBall_self hδ.le) hy hs
  refine ⟨L, hL, hA, δ, hδ, hδU, hδV, ?_, fun s hs y hy ↦ ?_⟩
  · rintro ⟨s, y⟩ ⟨hs, hy⟩
    by_cases hs0 : s = 0
    · subst s
      exact (hT.continuousAt_derivativeRescale_zero y).continuousWithinAt
    · exact (continuousAt_derivativeRescale hs0
        (hc.continuousAt (hU.mem_nhds (hδU (hscale hs hy))))).continuousWithinAt
  · have hsnorm : ‖s‖ ≤ 1 := by simpa [Real.norm_of_nonneg hs.1] using hs.2
    have hynorm : ‖y‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hbound := hb s hsnorm y hynorm
    refine ⟨hbound, hδV ?_, hT.derivativeRescale_neg_norm_fst_sq_add_norm_snd_sq_eq hT0 hQ
      (fun t ht ↦ hδU (hscale ht hy)) hs⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hbound.trans (mul_le_mul_of_nonneg_left hynorm hL.le)

/-- **The small negative disks of two Morse coordinate systems are homotopic.** Let `T`, fixing
the origin and differentiable there with derivative `A`, preserve `Q(u,v) = -‖u‖² + ‖v‖²` near
the origin, and let `h` be the polar factor of the negative block `A_uu` of `A`. For small `δ`
there is a homotopy `H` from the negative disk `u ↦ T (u, 0)`, `‖u‖ ≤ δ`, to `u ↦ (h u, 0)`
which stays in a prescribed neighborhood `V` of the origin and satisfies `Q (H (t, u)) ≤ -‖u‖²`
throughout. The radius can be chosen so that the disk of radius `δ` lies in a prescribed
neighborhood `U` of the origin. -/
theorem _root_.HasFDerivAt.exists_negative_disk_homotopy_polarFactor
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F}
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0) (hc : ∀ᶠ z in 𝓝 0, ContinuousAt T z)
    (hQ : ∀ᶠ z in 𝓝 0, ‖(T z).1‖ ^ 2 - ‖(T z).2‖ ^ 2 = ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2)
    {U V : Set (E × F)} (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) :
    ∃ δ > 0, Metric.closedBall 0 δ ⊆ U ∧
      ∃ H : C(unitInterval × Metric.closedBall (0 : E) δ, E × F),
        (∀ u, H (0, u) = T ((u : E), 0)) ∧
        (∀ u, H (1, u) = (((ContinuousLinearMap.fst ℝ E F).comp
          (A.comp (ContinuousLinearMap.inl ℝ E F))).polarFactor u, 0)) ∧
        ∀ p, H p ∈ V ∧ -‖(H p).1‖ ^ 2 + ‖(H p).2‖ ^ 2 ≤ -‖(p.2 : E)‖ ^ 2 := by
  -- An open neighborhood of the origin inside `U` on which `T` is continuous and preserves `Q`.
  obtain ⟨W, hWsub, hWo, hW0⟩ := mem_nhds_iff.1 (inter_mem hU (hc.and hQ))
  have hWc : ContinuousOn T W := fun z hz ↦ (hWsub hz).2.1.continuousWithinAt
  have hWQ : ∀ z ∈ W, -‖(T z).1‖ ^ 2 + ‖(T z).2‖ ^ 2 = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 :=
    fun z hz ↦ by linarith [(hWsub hz).2.2]
  obtain ⟨L, hL, hA, δ, hδ, hδW, hδV, hcont, hbd⟩ :=
    hT.exists_small_disk_derivativeRescale hT0 hWo hW0 hWc hWQ hV
  -- The negative column of `A` pulls `Q` back to `-‖u‖²`, so its negative block expands norms.
  set C := A.comp (ContinuousLinearMap.inl ℝ E F)
  set B := (ContinuousLinearMap.fst ℝ E F).comp C
  have hcol (u : E) : ‖(C u).1‖ ^ 2 - ‖(C u).2‖ ^ 2 = ‖u‖ ^ 2 := by
    simpa [C, hT.fderiv] using hT.differentiableAt.norm_sq_sub_fderiv hT0 hQ (u, 0)
  have hexp : ∀ u, ‖u‖ ≤ ‖B u‖ := C.norm_le_norm_fst_of_norm_sq_sub hcol
  -- Points of the small disk and their images under `A` stay in the controlled balls.
  have hmem (u : Metric.closedBall (0 : E) δ) :
      ((u : E), (0 : F)) ∈ Metric.closedBall (0 : E × F) δ := by
    have hu := mem_closedBall_zero_iff.1 u.2
    rw [mem_closedBall_zero_iff]
    simpa using hu
  have hCV (u : Metric.closedBall (0 : E) δ) {z : E × F} (hz : ‖z‖ ≤ ‖C u‖) : z ∈ V := by
    refine hδV (mem_closedBall_zero_iff.2 (hz.trans ?_))
    calc ‖C u‖ ≤ ‖A‖ * ‖((u : E), (0 : F))‖ := A.le_opNorm _
      _ ≤ L * δ := mul_le_mul hA (mem_closedBall_zero_iff.1 (hmem u)) (norm_nonneg _) hL.le
  have hσ (t : unitInterval) : |(unitInterval.symm t : ℝ)| ≤ 1 :=
    abs_le.2 ⟨by linarith [(unitInterval.symm t).2.1], (unitInterval.symm t).2.2⟩
  -- The three stages, each keeping `Q` at or below `-‖u‖²` inside `V`.
  let P : C(Metric.closedBall (0 : E) δ, E × F) → Prop := fun g ↦
    ∀ u, g u ∈ V ∧ -‖(g u).1‖ ^ 2 + ‖(g u).2‖ ^ 2 ≤ -‖(u : E)‖ ^ 2
  let g₀ : C(Metric.closedBall (0 : E) δ, E × F) :=
    ⟨fun u ↦ T ((u : E), 0), hWc.comp_continuous (by fun_prop) fun u ↦ hδW (hmem u)⟩
  let g₁ : C(Metric.closedBall (0 : E) δ, E × F) := ⟨fun u ↦ C u, by fun_prop⟩
  let g₂ : C(Metric.closedBall (0 : E) δ, E × F) :=
    ⟨fun u ↦ (B u, 0), by fun_prop⟩
  let g₃ : C(Metric.closedBall (0 : E) δ, E × F) :=
    ⟨fun u ↦ (B.polarFactor u, 0), by fun_prop⟩
  -- Rescale the transition to its derivative.
  let F₁ : g₀.HomotopyWith g₁ P :=
    { toFun := fun p : unitInterval × Metric.closedBall (0 : E) δ ↦
        derivativeRescale T A (unitInterval.symm p.1 : ℝ) ((p.2 : E), 0)
      continuous_toFun := hcont.comp_continuous
        (by fun_prop : Continuous fun p : unitInterval × Metric.closedBall (0 : E) δ ↦
          ((unitInterval.symm p.1 : ℝ), ((p.2 : E), (0 : F))))
        fun p ↦ ⟨(unitInterval.symm p.1).2, hmem p.2⟩
      map_zero_left := fun u ↦ by simp [g₀, hT0]
      map_one_left := fun u ↦ by simp [g₁, C]
      prop' := fun t u ↦ by
        obtain ⟨-, hV', hQ'⟩ := hbd _ (unitInterval.symm t).2 _ (hmem u)
        simp only [ContinuousMap.coe_mk]
        refine ⟨hV', le_of_eq ?_⟩
        rw [hQ']
        simp }
  -- Contract the positive component of the linearized disk.
  let F₂ : g₁.HomotopyWith g₂ P :=
    { toFun := fun p : unitInterval × Metric.closedBall (0 : E) δ ↦
        ((C p.2).1, (unitInterval.symm p.1 : ℝ) • (C p.2).2)
      continuous_toFun := by fun_prop
      map_zero_left := fun u ↦ by simp [g₁]
      map_one_left := fun u ↦ by simp [g₂, B]
      prop' := fun t u ↦ by
        simp only [ContinuousMap.coe_mk]
        refine ⟨hCV u ?_, C.neg_norm_fst_sq_add_norm_smul_snd_sq_le_of_norm_sq_sub hcol
          (hσ t) u⟩
        rw [Prod.norm_def, Prod.norm_def, norm_smul, Real.norm_eq_abs]
        exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) (hσ t)) }
  -- Deform the negative block to its polar factor.
  let F₃ : g₂.HomotopyWith g₃ P :=
    { toFun := fun p : unitInterval × Metric.closedBall (0 : E) δ ↦
        (B.polarDeformation p.1 p.2, 0)
      continuous_toFun := by
        have := B.continuous_polarDeformation (B.isStrictlyPositive_modulus_of_forall_norm_le hexp)
        fun_prop
      map_zero_left := fun u ↦ by simp [g₂]
      map_one_left := fun u ↦ by simp [g₃]
      prop' := fun t u ↦ by
        obtain ⟨hlo, hhi⟩ := B.norm_le_norm_polarDeformation_apply_le hexp t.2 u
        simp only [ContinuousMap.coe_mk]
        refine ⟨hCV u ?_, ?_⟩
        · simpa [Prod.norm_def] using hhi.trans (norm_fst_le (C u))
        · simpa using pow_le_pow_left₀ (norm_nonneg _) hlo 2 }
  let F := (F₁.trans F₂).trans F₃
  refine ⟨δ, hδ, hδW.trans fun z hz ↦ (hWsub hz).1, F.toHomotopy.toContinuousMap,
    fun u ↦ F.apply_zero u, fun u ↦ F.apply_one u, fun p ↦ ?_⟩
  simpa using F.prop p.1 p.2

end TauCeti
