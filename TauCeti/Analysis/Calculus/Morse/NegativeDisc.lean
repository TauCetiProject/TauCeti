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
(`ContinuousLinearMap.norm_le_norm_fst_of_norm_sq_sub`), so in finite dimension it is invertible
and has a polar decomposition `N = h P` with `h` orthogonal (`ContinuousLinearMap.polarFactor`)
and `P ≥ 1`.

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

The same comparison works continuously in a parameter
(`TauCeti.exists_negativeDisc_homotopy_family`). For a family `T p` over a compact space `P`,
differentiable near the origin with derivatives jointly continuous in `p` and the point, the polar
factors `h p` depend continuously on `p`
(`ContinuousLinearMap.continuousOn_polarFactor`), and one radius `δ` and one homotopy,
continuous in `p`, serve the whole family. The rescaling stage uses the joint continuity and the
uniform linear bound of `TauCeti.continuousOn_derivativeRescale_family` and
`TauCeti.exists_forall_norm_derivativeRescale_le_family`; the polar stage uses the joint
continuity of the polar deformation (`ContinuousLinearMap.continuousOn_polarDeformation`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Filter Set Metric Topology unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

omit [FiniteDimensional ℝ E] in
private theorem positiveContraction_apply (L : E →L[ℝ] E × F) (p : I × E) :
    positiveContraction L p = ((L p.2).1, (1 - (p.1 : ℝ)) • (L p.2).2) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
private theorem norm_positiveContraction_le (L : E →L[ℝ] E × F) (p : I × E) :
    ‖positiveContraction L p‖ ≤ ‖L p.2‖ := by
  rw [positiveContraction_apply]
  refine norm_prod_le_iff.2 ⟨norm_fst_le (L p.2), (norm_smul_le _ _).trans ?_⟩
  have ht : ‖1 - (p.1 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [p.1.2.1, p.1.2.2]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_snd_le _)

omit [FiniteDimensional ℝ E] in
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
    have := FiniteDimensional.complete ℝ E
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
  have := FiniteDimensional.complete ℝ E
  rw [polarStage_apply]
  exact norm_prod_le_iff.2
    ⟨(N.norm_le_norm_polarDeformation_apply_le hN p.1.2 p.2).2, by simp⟩

omit [InnerProductSpace ℝ F] in
/-- The polar deformation of an expanding operator keeps `Q` at most `-‖u‖²`. -/
private theorem polarStage_neg_norm_sq_add_le (N : E →L[ℝ] E) (hN : ∀ x, ‖x‖ ≤ ‖N x‖)
    (p : I × E) :
    -‖(polarStage (F := F) N hN p).1‖ ^ 2 + ‖(polarStage (F := F) N hN p).2‖ ^ 2 ≤
      -‖p.2‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  rw [polarStage_apply]
  simpa using pow_le_pow_left₀ (norm_nonneg _)
    (N.norm_le_norm_polarDeformation_apply_le hN p.1.2 p.2).1 2

end Linear

variable {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F} {U V : Set (E × F)}

omit [FiniteDimensional ℝ E] in
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
    ∃ h : E ≃ₗᵢ[ℝ] E, ⇑h = ((ContinuousLinearMap.fst ℝ E F).comp
        (A.comp (ContinuousLinearMap.inl ℝ E F))).polarFactor ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, (∀ w ∈ closedBall (0 : E) δ, (w, (0 : F)) ∈ U) ∧
        ∃ H : C(I × closedBall (0 : E) δ, E × F),
          (∀ w, H (0, w) = T ((w : E), 0)) ∧ (∀ w, H (1, w) = (h w, 0)) ∧
          ∀ t w, H (t, w) ∈ V ∧ -‖(H (t, w)).1‖ ^ 2 + ‖(H (t, w)).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL, hAL, δ₀, hδ₀, hδU, hδV, hcont, hbound⟩ :=
    hT.exists_small_disk_derivativeRescale hT0 hU h0U hc hQ hV
  -- The negative column of `A` pulls `Q` back to `-‖u‖²`, so its negative block expands norms.
  let C : E →L[ℝ] E × F := A.comp (ContinuousLinearMap.inl ℝ E F)
  have hC (u : E) : ‖(C u).1‖ ^ 2 - ‖(C u).2‖ ^ 2 = ‖u‖ ^ 2 :=
    norm_sq_sub_comp_inl hT hT0 hU h0U hQ u
  let N : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E F).comp C
  have hN : ∀ u, ‖u‖ ≤ ‖N u‖ := C.norm_le_norm_fst_of_norm_sq_sub hC
  -- Its polar factor is a linear isometry equivalence.
  let h₀ : E →ₗᵢ[ℝ] E :=
    { toLinearMap := N.polarFactor
      norm_map' := N.norm_polarFactor_apply_of_injective
        (ContinuousLinearMap.injective_of_forall_norm_le (M := 1) fun x ↦ by simpa using hN x) }
  refine ⟨h₀.toLinearIsometryEquiv rfl, rfl, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
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

section Family

/-- The linear part of the comparison for a continuous family `C x` of negative columns over a
space `X`: contract the positive components, then deform the negative blocks
`N x = (C x ·).1` to their polar factors. Along the way the values are bounded by `‖C x u‖`
and `Q` stays at most `-‖u‖²`. -/
private noncomputable def negativeColumnHomotopy {X : Type*} [TopologicalSpace X]
    (C : X → E →L[ℝ] E × F) (hC : Continuous C)
    (hCQ : ∀ x u, ‖(C x u).1‖ ^ 2 - ‖(C x u).2‖ ^ 2 = ‖u‖ ^ 2)
    (hP : Continuous fun x ↦ ((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor) :
    ContinuousMap.HomotopyWith (⟨fun q : X × E ↦ C q.1 q.2, by fun_prop⟩ : C(X × E, E × F))
      ⟨fun q ↦ (((ContinuousLinearMap.fst ℝ E F).comp (C q.1)).polarFactor q.2, 0),
        ((hP.comp continuous_fst).clm_apply continuous_snd).prodMk continuous_const⟩
      fun g ↦ ∀ q, ‖g q‖ ≤ ‖C q.1 q.2‖ ∧ -‖(g q).1‖ ^ 2 + ‖(g q).2‖ ^ 2 ≤ -‖q.2‖ ^ 2 :=
  have := FiniteDimensional.complete ℝ E
  let N : X → E →L[ℝ] E := fun x ↦ (ContinuousLinearMap.fst ℝ E F).comp (C x)
  have hN (x : X) (u : E) : ‖u‖ ≤ ‖N x u‖ := (C x).norm_le_norm_fst_of_norm_sq_sub (hCQ x) u
  -- First contract the positive components, then deform the negative blocks.
  ContinuousMap.HomotopyWith.trans (f₁ := ⟨fun q : X × E ↦ ((C q.1 q.2).1, 0), by fun_prop⟩)
    { toFun := fun q ↦ ((C q.2.1 q.2.2).1, (1 - (q.1 : ℝ)) • (C q.2.1 q.2.2).2)
      continuous_toFun := by fun_prop
      map_zero_left := fun q ↦ by simp
      map_one_left := fun q ↦ by simp
      prop' := fun t q ↦ by
        simp only [ContinuousMap.coe_mk]
        rw [← positiveContraction_apply (C q.1) (t, q.2)]
        exact ⟨norm_positiveContraction_le (C q.1) (t, q.2),
          positiveContraction_neg_norm_sq_add_le (C q.1) (hCQ q.1) (t, q.2)⟩ }
    { toFun := fun q ↦ ((N q.2.1).polarDeformation q.1 q.2.2, 0)
      continuous_toFun := by
        have hc : Continuous fun q : I × (X × E) ↦ (N q.2.1).polarDeformation q.1 :=
          ContinuousLinearMap.continuousOn_polarDeformation.comp_continuous
            (f := fun q : I × (X × E) ↦ (N q.2.1, (q.1 : ℝ))) (by fun_prop)
            fun q ↦ mk_mem_prod ((N q.2.1).isStrictlyPositive_modulus_of_forall_norm_le
              (hN q.2.1)) (mem_univ _)
        exact (hc.clm_apply (by fun_prop)).prodMk continuous_const
      map_zero_left := fun q ↦ by simp [N]
      map_one_left := fun q ↦ by simp [N]
      prop' := fun t q ↦ by
        simp only [ContinuousMap.coe_mk]
        rw [← polarStage_apply (F := F) (N q.1) (hN q.1) (t, q.2)]
        exact ⟨(norm_polarStage_le (N q.1) (hN q.1) (t, q.2)).trans (norm_fst_le _),
          polarStage_neg_norm_sq_add_le (N q.1) (hN q.1) (t, q.2)⟩ }

variable {P : Type*} [TopologicalSpace P] [CompactSpace P] {T : P → E × F → E × F}
  {D : P → E × F → (E × F) →L[ℝ] E × F} {r : ℝ}

/-- **Small negative discs of a compact family of Morse coordinate systems.** Let `T p` be a
family of changes of coordinates over a compact parameter space `P`, each fixing the origin and
preserving `Q(u, v) = -‖u‖² + ‖v‖²` on the ball of radius `r`, where it is differentiable with
derivatives `D p y` jointly continuous in `p` and `y`; let `T` be jointly continuous there too.
Write `N p u = (D p 0 (u, 0)).1` for the negative block of the derivative at the origin. Its polar
factor depends continuously on `p`, and there is one `δ₀ > 0` such that for every `δ ≤ δ₀` the
maps `u ↦ T p (u, 0)` on the disc `‖u‖ ≤ δ` of `E` are homotopic to `u ↦ ((N p).polarFactor u, 0)`
by a single homotopy, continuous in `p`, through maps `g` with values in the prescribed
neighbourhood `V` of the origin and with `Q (g u) ≤ -‖u‖²`. -/
theorem exists_negativeDisc_homotopy_family (hr : 0 < r)
    (hT : ∀ p, ∀ y ∈ ball (0 : E × F) r, HasFDerivAt (T p) (D p y) y)
    (hTc : ContinuousOn (Function.uncurry T) (univ ×ˢ ball 0 r))
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r)) (hT0 : ∀ p, T p 0 = 0)
    (hQ : ∀ p, ∀ y ∈ ball (0 : E × F) r,
      -‖(T p y).1‖ ^ 2 + ‖(T p y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {V : Set (E × F)} (hV : V ∈ 𝓝 0) :
    Continuous (fun p ↦ ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, (∀ w ∈ closedBall (0 : E) δ, (w, (0 : F)) ∈ ball 0 r) ∧
        ∃ H : C(P × I × closedBall (0 : E) δ, E × F),
          (∀ p w, H (p, 0, w) = T p ((w : E), 0)) ∧
          (∀ p w, H (p, 1, w) = (((ContinuousLinearMap.fst ℝ E F).comp
            ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor w, 0)) ∧
          ∀ p t w, H (p, t, w) ∈ V ∧
            -‖(H (p, t, w)).1‖ ^ 2 + ‖(H (p, t, w)).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 := by
  -- The proof runs the three stages of `HasFDerivAt.exists_negativeDisc_homotopy` with the
  -- parameter `p` carried along. Compactness of `P` gives one linear bound `L` for all rescalings
  -- and one radius, so that a single `δ₀` keeps every stage inside `V`.
  have := FiniteDimensional.complete ℝ E
  have h0r : (0 : E × F) ∈ ball 0 r := mem_ball_self hr
  obtain ⟨L, hL, ρ, ⟨hρ, hρr⟩, hbound⟩ := exists_forall_norm_derivativeRescale_le_family hr hT hD
  obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp hV
  -- The negative columns `C p` of the derivatives pull `Q` back to `-‖u‖²`, so their negative
  -- blocks `N p` expand norms; both depend continuously on `p`.
  let C : P → E →L[ℝ] E × F := fun p ↦ (D p 0).comp (ContinuousLinearMap.inl ℝ E F)
  have hC (p : P) (u : E) : ‖(C p u).1‖ ^ 2 - ‖(C p u).2‖ ^ 2 = ‖u‖ ^ 2 :=
    norm_sq_sub_comp_inl (hT p 0 h0r) (hT0 p) isOpen_ball h0r (hQ p) u
  let N : P → E →L[ℝ] E := fun p ↦ (ContinuousLinearMap.fst ℝ E F).comp (C p)
  have hN (p : P) (u : E) : ‖u‖ ≤ ‖N p u‖ := (C p).norm_le_norm_fst_of_norm_sq_sub (hC p) u
  have hNpos (p : P) : IsStrictlyPositive (N p).modulus :=
    (N p).isStrictlyPositive_modulus_of_forall_norm_le (hN p)
  have hD0 : Continuous fun p ↦ D p 0 :=
    hD.comp_continuous (continuous_id.prodMk continuous_const) fun _ ↦ ⟨mem_univ _, h0r⟩
  have hCc : Continuous C := hD0.clm_comp continuous_const
  have hNc : Continuous N := continuous_const.clm_comp hCc
  have hPc : Continuous fun p ↦ (N p).polarFactor :=
    ContinuousLinearMap.continuousOn_polarFactor.comp_continuous hNc fun p ↦ (hNpos p).isUnit
  refine ⟨hPc, min (ρ / 2) (s / (2 * L)), lt_min (by positivity) (by positivity),
    fun δ hδ ↦ ?_⟩
  have hδρ : δ < ρ := hδ.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hδs : L * δ < s := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp (hδ.2.trans (min_le_right _ _))
    nlinarith [hδ.1]
  have hw (w : closedBall (0 : E) δ) : ‖((w : E), (0 : F))‖ ≤ δ := by
    simpa [Prod.norm_def] using mem_closedBall_zero_iff.mp w.2
  have hwr (w : closedBall (0 : E) δ) : ((w : E), (0 : F)) ∈ ball (0 : E × F) r :=
    mem_ball_zero_iff.mpr ((hw w).trans_lt (hδρ.trans_le hρr))
  have hCw (p : P) (w : closedBall (0 : E) δ) : ‖C p w‖ ≤ L * δ :=
    ((D p 0).le_opNorm _).trans (mul_le_mul (hbound p).1 (hw w) (norm_nonneg _) hL.le)
  -- Both homotopies below are of maps on `P × closedBall 0 δ` keeping their values in `V` and `Q`
  -- at most `-‖u‖²`.
  let R : C(P × closedBall (0 : E) δ, E × F) → Prop := fun g ↦
    ∀ x : P × closedBall (0 : E) δ, g x ∈ V ∧ -‖(g x).1‖ ^ 2 + ‖(g x).2‖ ^ 2 ≤ -‖(x.2 : E)‖ ^ 2
  have hR {z : E × F} (x : P × closedBall (0 : E) δ) (hz : ‖z‖ ≤ ‖C x.1 x.2‖)
      (hq : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖(x.2 : E)‖ ^ 2) :
      z ∈ V ∧ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖(x.2 : E)‖ ^ 2 :=
    ⟨hsV (mem_ball_zero_iff.mpr ((hz.trans (hCw x.1 x.2)).trans_lt hδs)), hq⟩
  have hσ (t : I) : (σ t : ℝ) ∈ closedBall (0 : ℝ) 1 := by
    rw [mem_closedBall_zero_iff, Real.norm_of_nonneg (σ t).2.1]
    exact (σ t).2.2
  -- The intermediate map `(p, u) ↦ C p u`.
  let gC : C(P × closedBall (0 : E) δ, E × F) := ⟨fun x ↦ C x.1 x.2, by fun_prop⟩
  -- Stage 1: rescale `T p` to its derivative, continuously in `p`.
  have hT₀ : Continuous fun x : P × closedBall (0 : E) δ ↦ T x.1 ((x.2 : E), 0) :=
    hTc.comp_continuous (f := fun x : P × closedBall (0 : E) δ ↦ (x.1, ((x.2 : E), (0 : F))))
      (by fun_prop) fun x ↦ ⟨mem_univ _, hwr x.2⟩
  have hres : Continuous fun q : I × (P × closedBall (0 : E) δ) ↦
      derivativeRescale (T q.2.1) (D q.2.1 0) (σ q.1 : ℝ) ((q.2.2 : E), 0) :=
    (continuousOn_derivativeRescale_family hT hTc hD).comp_continuous
      (f := fun q : I × (P × closedBall (0 : E) δ) ↦
        (q.2.1, (σ q.1 : ℝ), ((q.2.2 : E), (0 : F)))) (by fun_prop)
      fun q ↦ ⟨mem_univ _, hσ q.1, hwr q.2.2⟩
  let H₁ : ContinuousMap.HomotopyWith ⟨_, hT₀⟩ gC R :=
    { toFun := fun q ↦ derivativeRescale (T q.2.1) (D q.2.1 0) (σ q.1 : ℝ) ((q.2.2 : E), 0)
      continuous_toFun := hres
      map_zero_left := fun x ↦ by simp [derivativeRescale_one, hT0]
      map_one_left := fun x ↦ by simp [derivativeRescale_zero, gC, C]
      prop' := fun t x ↦ by
        have hb := (hbound x.1).2 _ (mem_closedBall_zero_iff.mp (hσ t)) _
          ((hw x.2).trans_lt hδρ)
        refine ⟨hsV (mem_ball_zero_iff.mpr ((hb.trans (mul_le_mul_of_nonneg_left (hw x.2)
          hL.le)).trans_lt hδs)), le_of_eq ?_⟩
        simpa using (hT x.1 0 h0r).derivativeRescale_neg_norm_fst_sq_add_norm_snd_sq_eq (hT0 x.1)
          (hQ x.1) (fun c hc ↦ (convex_ball (0 : E × F) r).smul_mem_of_zero_mem h0r (hwr x.2) hc)
          ⟨(σ t).2.1, (σ t).2.2⟩ }
  -- Stages 2 and 3: the linear part, read on the discs.
  let ι : C(P × closedBall (0 : E) δ, P × E) := ⟨fun x ↦ (x.1, x.2), by fun_prop⟩
  let G := negativeColumnHomotopy C hCc hC hPc
  let H₂ : ContinuousMap.HomotopyWith gC
      ⟨fun x : P × closedBall (0 : E) δ ↦ ((N x.1).polarFactor x.2, 0),
        ((hPc.comp continuous_fst).clm_apply (by fun_prop)).prodMk continuous_const⟩ R :=
    { toHomotopy := G.toHomotopy.compContinuousMap ι
      prop' := fun t x ↦ hR x (G.prop t (ι x)).1 (G.prop t (ι x)).2 }
  let H := H₁.trans H₂
  refine ⟨fun w hw' ↦ hwr ⟨w, hw'⟩,
    ⟨fun q ↦ H (q.2.1, (q.1, q.2.2)), H.continuous.comp (by fun_prop)⟩,
    fun p w ↦ H.apply_zero (p, w), fun p w ↦ H.apply_one (p, w), fun p t w ↦ H.prop t (p, w)⟩

end Family

end TauCeti
