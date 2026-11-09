/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.Calculus.Morse.ChartRescaling
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Deformation

/-!
# Comparing small negative discs of two Morse coordinate systems

Let `T : E × F → E × F` be a local change of coordinates fixing the origin and preserving the
split quadratic form `Q(u, v) = -‖u‖² + ‖v‖²`, with derivative `A` at the origin. In Morse
theory `T` is the transition `φ₀ ∘ φ₁⁻¹` between two Morse charts at the same critical point, and
the negative discs `u ↦ (u, 0)` of the two charts are to be compared. The negative block
`N u = (A (u, 0)).1` of the derivative expands norms
(`ContinuousLinearMap.norm_le_norm_fst_of_norm_sq_sub`), so it is injective and has a polar
decomposition `N = h P` with `h` a linear isometry (`ContinuousLinearMap.polarFactor`) and `P ≥ 1`.
In finite dimension `h` is orthogonal (`LinearIsometry.toLinearIsometryEquiv`). Only completeness
of `E` is assumed.

This file shows that on every sufficiently small disc `‖u‖ ≤ δ` of `E`, the map `u ↦ T (u, 0)`
is homotopic to the linear map `u ↦ (h u, 0)` through maps `g` which stay in a prescribed
neighbourhood `V` of the origin and satisfy `Q (g u) ≤ -‖u‖²`
(`HasFDerivAt.exists_negativeDisc_homotopy`). The homotopy passes through three stages:

1. the rescaling `s ↦ T (s • (u, 0)) / s` from `T` to its derivative `A`, which keeps the exact
   value `Q = -‖u‖²` (`HasFDerivAt.exists_small_disk_derivativeRescale`);
2. the contraction `t ↦ ((A (u, 0)).1, (1 - t) • (A (u, 0)).2)` of the positive component, which
   only lowers `Q`;
3. the polar deformation `t ↦ (h P^(1-t) u, 0)` from `N` to `h`
   (`ContinuousLinearMap.polarDeformation`), along which `‖h P^(1-t) u‖ ≥ ‖u‖`.

In particular the boundary sphere `‖u‖ = δ` stays at `Q ≤ -δ²` throughout. Read through the inverse
of the chart `φ₀`, this compares the small characteristic discs of two Morse charts without any
assumption that their whole negative discs overlap.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Filter Set Metric Topology unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Linear

/-- The contraction of the positive component of a linear map `L : E → E × F`, from `L` to
`u ↦ ((L u).1, 0)`. -/
private noncomputable def positiveContraction (L : E →L[ℝ] E × F) :
    ContinuousMap.Homotopy (⟨L, L.continuous⟩ : C(E, E × F))
      ⟨fun u ↦ ((L u).1, 0), by fun_prop⟩ where
  toFun p := ((L p.2).1, (1 - (p.1 : ℝ)) • (L p.2).2)
  continuous_toFun := by fun_prop
  map_zero_left u := by simp
  map_one_left u := by simp

omit [CompleteSpace E] in
private theorem positiveContraction_apply (L : E →L[ℝ] E × F) (p : I × E) :
    positiveContraction L p = ((L p.2).1, (1 - (p.1 : ℝ)) • (L p.2).2) :=
  (rfl)

omit [CompleteSpace E] in
private theorem norm_positiveContraction_le (L : E →L[ℝ] E × F) (p : I × E) :
    ‖positiveContraction L p‖ ≤ ‖L p.2‖ := by
  rw [positiveContraction_apply]
  refine norm_prod_le_iff.2 ⟨norm_fst_le (L p.2), (norm_smul_le _ _).trans ?_⟩
  have ht : ‖1 - (p.1 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [p.1.2.1, p.1.2.2]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_snd_le _)

omit [CompleteSpace E] in
/-- Contracting the positive component keeps `Q` at most `-‖u‖²` when `L` pulls `Q` back to
`-‖u‖²`. -/
private theorem positiveContraction_neg_norm_sq_add_le (L : E →L[ℝ] E × F)
    (hL : ∀ u, ‖(L u).1‖ ^ 2 - ‖(L u).2‖ ^ 2 = ‖u‖ ^ 2) (p : I × E) :
    -‖(positiveContraction L p).1‖ ^ 2 + ‖(positiveContraction L p).2‖ ^ 2 ≤ -‖p.2‖ ^ 2 := by
  rw [positiveContraction_apply]
  exact L.neg_norm_fst_sq_add_norm_smul_snd_sq_le_of_norm_sq_sub hL
    (abs_le.mpr ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩) p.2

/-- The polar deformation `t ↦ (N.polarDeformation t u, 0)` of an expanding operator `N`, from
`u ↦ (N u, 0)` to `u ↦ (N.polarFactor u, 0)`. -/
private noncomputable def polarStage (N : E →L[ℝ] E) (hN : ∀ x, ‖x‖ ≤ ‖N x‖) :
    ContinuousMap.Homotopy (⟨fun u ↦ (N u, (0 : F)), by fun_prop⟩ : C(E, E × F))
      ⟨fun u ↦ (N.polarFactor u, 0), by fun_prop⟩ where
  toFun p := (N.polarDeformation p.1 p.2, 0)
  continuous_toFun := by
    have hc : Continuous fun t : I ↦ N.polarDeformation t :=
      (N.continuous_polarDeformation
        (N.isStrictlyPositive_modulus_of_forall_norm_le hN)).comp continuous_subtype_val
    exact ((hc.comp continuous_fst).clm_apply continuous_snd).prodMk continuous_const
  map_zero_left u := by simp
  map_one_left u := by simp

omit [InnerProductSpace ℝ F] in
private theorem polarStage_apply (N : E →L[ℝ] E) (hN : ∀ x, ‖x‖ ≤ ‖N x‖) (p : I × E) :
    polarStage (F := F) N hN p = (N.polarDeformation p.1 p.2, 0) :=
  (rfl)

omit [InnerProductSpace ℝ F] in
private theorem norm_polarStage_le (N : E →L[ℝ] E) (hN : ∀ x, ‖x‖ ≤ ‖N x‖) (p : I × E) :
    ‖polarStage (F := F) N hN p‖ ≤ ‖N p.2‖ := by
  rw [polarStage_apply]
  exact norm_prod_le_iff.2
    ⟨(N.norm_le_norm_polarDeformation_apply_le hN p.1.2 p.2).2, by simp⟩

omit [InnerProductSpace ℝ F] in
/-- The polar deformation of an expanding operator keeps `Q` at most `-‖u‖²`. -/
private theorem polarStage_neg_norm_sq_add_le (N : E →L[ℝ] E) (hN : ∀ x, ‖x‖ ≤ ‖N x‖)
    (p : I × E) :
    -‖(polarStage (F := F) N hN p).1‖ ^ 2 + ‖(polarStage (F := F) N hN p).2‖ ^ 2 ≤
      -‖p.2‖ ^ 2 := by
  rw [polarStage_apply]
  simpa using pow_le_pow_left₀ (norm_nonneg _)
    (N.norm_le_norm_polarDeformation_apply_le hN p.1.2 p.2).1 2

end Linear

variable {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F} {U V : Set (E × F)}

omit [CompleteSpace E] in
/-- The negative column `u ↦ A (u, 0)` of the derivative of a `Q`-preserving change of
coordinates pulls `Q` back to `-‖u‖²`. -/
private theorem norm_sq_sub_comp_inl (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) (u : E) :
    ‖(A.comp (ContinuousLinearMap.inl ℝ E F) u).1‖ ^ 2 -
      ‖(A.comp (ContinuousLinearMap.inl ℝ E F) u).2‖ ^ 2 = ‖u‖ ^ 2 := by
  have hQ' : ∀ᶠ z in 𝓝 (0 : E × F), ‖(T z).1‖ ^ 2 - ‖(T z).2‖ ^ 2 = ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 :=
    eventually_of_mem (hU.mem_nhds h0U) fun z hz ↦ by linarith [hQ z hz]
  simpa [hT.fderiv] using hT.differentiableAt.norm_sq_sub_fderiv hT0 hQ' (u, 0)

/-- **Small negative discs of two Morse coordinate systems.** Let `T` fix the origin, have
derivative `A` there, and preserve `Q(u, v) = -‖u‖² + ‖v‖²` on an open neighbourhood `U` of the
origin on which it is continuous. Let the linear isometry `h` be the polar factor of the negative
block `u ↦ (A (u, 0)).1`. Then for every small `δ > 0`, the disc `‖u‖ ≤ δ` of `E` lies in `U`, and
the map `u ↦ T (u, 0)` on it is homotopic to `u ↦ (h u, 0)` through maps `g` with values in the
prescribed neighbourhood `V` of the origin and with `Q (g u) ≤ -‖u‖²`. -/
theorem _root_.HasFDerivAt.exists_negativeDisc_homotopy
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U) (hc : ContinuousOn T U)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    (hV : V ∈ 𝓝 0) :
    ∃ h : E →ₗᵢ[ℝ] E, ⇑h = ((ContinuousLinearMap.fst ℝ E F).comp
        (A.comp (ContinuousLinearMap.inl ℝ E F))).polarFactor ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, (∀ w ∈ closedBall (0 : E) δ, (w, (0 : F)) ∈ U) ∧
        ∃ H : C(I × closedBall (0 : E) δ, E × F),
          (∀ w, H (0, w) = T ((w : E), 0)) ∧ (∀ w, H (1, w) = (h w, 0)) ∧
          ∀ t w, H (t, w) ∈ V ∧ -‖(H (t, w)).1‖ ^ 2 + ‖(H (t, w)).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 := by
  obtain ⟨L, hL, hAL, δ₀, hδ₀, hδU, hδV, hcont, hbound⟩ :=
    hT.exists_small_disk_derivativeRescale hT0 hU h0U hc hQ hV
  -- The negative column of `A` pulls `Q` back to `-‖u‖²`, so its negative block expands norms.
  let C : E →L[ℝ] E × F := A.comp (ContinuousLinearMap.inl ℝ E F)
  have hC (u : E) : ‖(C u).1‖ ^ 2 - ‖(C u).2‖ ^ 2 = ‖u‖ ^ 2 :=
    norm_sq_sub_comp_inl hT hT0 hU h0U hQ u
  let N : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E F).comp C
  have hN : ∀ u, ‖u‖ ≤ ‖N u‖ := C.norm_le_norm_fst_of_norm_sq_sub hC
  -- Its polar factor is a linear isometry.
  let h₀ : E →ₗᵢ[ℝ] E :=
    { toLinearMap := N.polarFactor
      norm_map' := N.norm_polarFactor_apply_of_injective
        (ContinuousLinearMap.injective_of_forall_norm_le (M := 1) fun x ↦ by simpa using hN x) }
  refine ⟨h₀, rfl, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  let ι : C(closedBall (0 : E) δ, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hw (w : closedBall (0 : E) δ) : ((w : E), (0 : F)) ∈ closedBall (0 : E × F) δ₀ := by
    have := mem_closedBall_zero_iff.mp w.2
    simpa [Prod.norm_def] using this.trans hδ.2
  have hCw (w : closedBall (0 : E) δ) : ‖C w‖ ≤ L * δ₀ := by
    have := mem_closedBall_zero_iff.mp (hw w)
    calc ‖C w‖ ≤ ‖A‖ * ‖((w : E), (0 : F))‖ := A.le_opNorm _
      _ ≤ L * δ₀ := mul_le_mul hAL this (norm_nonneg _) hL.le
  -- The three stages keep their values in `V` and `Q` at most `-‖u‖²`.
  let P : C(closedBall (0 : E) δ, E × F) → Prop := fun g ↦
    ∀ w, g w ∈ V ∧ -‖(g w).1‖ ^ 2 + ‖(g w).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2
  have hP {z : E × F} (w : closedBall (0 : E) δ) (hz : ‖z‖ ≤ ‖C w‖)
      (hq : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2) :
      z ∈ V ∧ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 :=
    ⟨hδV (mem_closedBall_zero_iff.mpr (hz.trans (hCw w))), hq⟩
  -- Stage 1: rescale `T` to its derivative.
  let H₁ : ContinuousMap.HomotopyWith
      ⟨fun w : closedBall (0 : E) δ ↦ T ((w : E), 0),
        hc.comp_continuous (by fun_prop) fun w ↦ hδU (hw w)⟩
      ((⟨C, C.continuous⟩ : C(E, E × F)).comp ι) P :=
    { toFun := fun p ↦ derivativeRescale T A (σ p.1 : ℝ) ((p.2 : E), 0)
      continuous_toFun := hcont.comp_continuous
        (f := fun p : I × closedBall (0 : E) δ ↦ ((σ p.1 : ℝ), ((p.2 : E), (0 : F))))
        (by fun_prop) fun p ↦
        ⟨⟨(σ p.1).2.1, (σ p.1).2.2⟩, hw p.2⟩
      map_zero_left := fun w ↦ by simp [derivativeRescale_one, hT0]
      map_one_left := fun w ↦ by simp [derivativeRescale_zero, C, ι]
      prop' := fun t w ↦ by
        obtain ⟨-, hV', hq⟩ := hbound _ ⟨(σ t).2.1, (σ t).2.2⟩ _ (hw w)
        exact ⟨hV', le_of_eq (by simpa using hq)⟩ }
  -- Stages 2 and 3: contract the positive component, then deform the negative block to its
  -- polar factor.
  let H₂ : ContinuousMap.HomotopyWith ((⟨C, C.continuous⟩ : C(E, E × F)).comp ι) _ P :=
    { toHomotopy := (positiveContraction C).compContinuousMap ι
      prop' := fun t w ↦ by
        simp only [ContinuousMap.Homotopy.compContinuousMap_apply, ContinuousMap.toFun_eq_coe,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.coe_mk, ι]
        exact hP w (norm_positiveContraction_le C (t, w))
          (positiveContraction_neg_norm_sq_add_le C hC (t, w)) }
  let H₃ : ContinuousMap.HomotopyWith _ _ P :=
    { toHomotopy := (polarStage N hN).compContinuousMap ι
      prop' := fun t w ↦ by
        simp only [ContinuousMap.Homotopy.compContinuousMap_apply, ContinuousMap.toFun_eq_coe,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.coe_mk, ι]
        exact hP w ((norm_polarStage_le N hN (t, w)).trans (norm_fst_le (C w)))
          (polarStage_neg_norm_sq_add_le N hN (t, w)) }
  let H := (H₁.trans H₂).trans H₃
  exact ⟨fun w hw' ↦ hδU (hw ⟨w, hw'⟩), H.toContinuousMap, fun w ↦ H.apply_zero w,
    fun w ↦ H.apply_one w, fun t w ↦ H.prop t w⟩

end TauCeti
