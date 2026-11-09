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

The comparison also holds continuously in a parameter
(`TauCeti.exists_parametric_negativeDisc_homotopy`). For a family of transitions `T p` over a
compact space `P`, preserving `Q` on a common neighbourhood of the origin, with `T` and, at the
origin, its derivative jointly continuous in the parameter and the point, one radius `δ` serves
every `p`, the polar factors `h p` depend continuously on `p`, and the three stages assemble into
one homotopy `[0, 1] × P × {‖u‖ ≤ δ} → E × F`. Such families arise from Morse charts depending
continuously on a parameter, as in the comparison of cell attachments over a parameter space.

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

variable {X : Type*} [TopologicalSpace X]

/-- The contraction of the positive component of a continuous family of linear maps
`L x : E → E × F`, evaluated along `u`, from `x ↦ L x (u x)` to `x ↦ ((L x (u x)).1, 0)`. -/
private noncomputable def positiveContraction (L : C(X, E →L[ℝ] E × F)) (u : C(X, E)) :
    ContinuousMap.Homotopy (⟨fun x ↦ L x (u x), by fun_prop⟩ : C(X, E × F))
      ⟨fun x ↦ ((L x (u x)).1, 0), by fun_prop⟩ where
  toFun p := ((L p.2 (u p.2)).1, (1 - (p.1 : ℝ)) • (L p.2 (u p.2)).2)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

omit [FiniteDimensional ℝ E] in
private theorem positiveContraction_apply (L : C(X, E →L[ℝ] E × F)) (u : C(X, E))
    (p : I × X) :
    positiveContraction L u p = ((L p.2 (u p.2)).1, (1 - (p.1 : ℝ)) • (L p.2 (u p.2)).2) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
private theorem norm_positiveContraction_le (L : C(X, E →L[ℝ] E × F)) (u : C(X, E))
    (p : I × X) : ‖positiveContraction L u p‖ ≤ ‖L p.2 (u p.2)‖ := by
  rw [positiveContraction_apply]
  refine norm_prod_le_iff.2 ⟨norm_fst_le (L p.2 (u p.2)), (norm_smul_le _ _).trans ?_⟩
  have ht : ‖1 - (p.1 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [p.1.2.1, p.1.2.2]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_snd_le _)

omit [FiniteDimensional ℝ E] in
/-- Contracting the positive component keeps `Q` at most `-‖u‖²` when every `L x` pulls `Q` back
to `-‖u‖²`. -/
private theorem positiveContraction_neg_norm_sq_add_le (L : C(X, E →L[ℝ] E × F)) (u : C(X, E))
    (hL : ∀ x v, ‖(L x v).1‖ ^ 2 - ‖(L x v).2‖ ^ 2 = ‖v‖ ^ 2) (p : I × X) :
    -‖(positiveContraction L u p).1‖ ^ 2 + ‖(positiveContraction L u p).2‖ ^ 2 ≤
      -‖u p.2‖ ^ 2 := by
  rw [positiveContraction_apply]
  exact (L p.2).neg_norm_fst_sq_add_norm_smul_snd_sq_le_of_norm_sq_sub (hL p.2)
    (abs_le.mpr ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩) (u p.2)

/-- The polar factors of the negative blocks `(C x ·).1` of a continuous family of linear maps
`C x : E → E × F` depend continuously on `x` when the negative blocks expand norms. -/
private theorem continuous_polarFactor_fst_comp (C : C(X, E →L[ℝ] E × F))
    (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖) :
    Continuous fun x ↦ ((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor := by
  have := FiniteDimensional.complete ℝ E
  have hN : Continuous fun x ↦ (ContinuousLinearMap.fst ℝ E F).comp (C x) := by fun_prop
  exact continuous_iff_continuousAt.2 fun x ↦ (ContinuousLinearMap.continuousAt_polarFactor
    (ContinuousLinearMap.isStrictlyPositive_modulus_of_forall_norm_le _ (hC x)).isUnit).comp
      (f := fun x ↦ (ContinuousLinearMap.fst ℝ E F).comp (C x)) hN.continuousAt

/-- The polar deformation of the negative blocks `(C x ·).1` of a continuous family of linear maps
`C x : E → E × F`, all expanding norms, evaluated along `u`: from `x ↦ ((C x (u x)).1, 0)` to the
polar factors `x ↦ ((C x ·).1.polarFactor (u x), 0)`. -/
private noncomputable def polarStage (C : C(X, E →L[ℝ] E × F)) (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖)
    (u : C(X, E)) :
    ContinuousMap.Homotopy (⟨fun x ↦ ((C x (u x)).1, (0 : F)), by fun_prop⟩ : C(X, E × F))
      ⟨fun x ↦ (((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor (u x), 0), by
        have := continuous_polarFactor_fst_comp C hC
        fun_prop⟩ where
  toFun p := (((ContinuousLinearMap.fst ℝ E F).comp (C p.2)).polarDeformation p.1 (u p.2), 0)
  continuous_toFun := by
    have := FiniteDimensional.complete ℝ E
    have hc : Continuous fun p : I × X ↦
        ((ContinuousLinearMap.fst ℝ E F).comp (C p.2)).polarDeformation p.1 :=
      ContinuousLinearMap.continuousOn_polarDeformation.comp_continuous
        (f := fun p : I × X ↦ ((ContinuousLinearMap.fst ℝ E F).comp (C p.2), (p.1 : ℝ)))
        (by fun_prop) fun p ↦
          ⟨ContinuousLinearMap.isStrictlyPositive_modulus_of_forall_norm_le _ (hC p.2), trivial⟩
    exact (hc.clm_apply (u.continuous.comp continuous_snd)).prodMk continuous_const
  map_zero_left x := by simp
  map_one_left x := by simp

private theorem polarStage_apply (C : C(X, E →L[ℝ] E × F)) (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖)
    (u : C(X, E)) (p : I × X) :
    polarStage C hC u p =
      (((ContinuousLinearMap.fst ℝ E F).comp (C p.2)).polarDeformation p.1 (u p.2), 0) :=
  (rfl)

private theorem norm_polarStage_le (C : C(X, E →L[ℝ] E × F)) (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖)
    (u : C(X, E)) (p : I × X) : ‖polarStage C hC u p‖ ≤ ‖C p.2 (u p.2)‖ := by
  have := FiniteDimensional.complete ℝ E
  rw [polarStage_apply]
  refine norm_prod_le_iff.2 ⟨?_, by simp⟩
  exact (((ContinuousLinearMap.fst ℝ E F).comp (C p.2)).norm_le_norm_polarDeformation_apply_le
    (hC p.2) p.1.2 (u p.2)).2.trans (norm_fst_le _)

/-- The polar deformation of expanding negative blocks keeps `Q` at most `-‖u‖²`. -/
private theorem polarStage_neg_norm_sq_add_le (C : C(X, E →L[ℝ] E × F))
    (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖) (u : C(X, E)) (p : I × X) :
    -‖(polarStage C hC u p).1‖ ^ 2 + ‖(polarStage C hC u p).2‖ ^ 2 ≤ -‖u p.2‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  rw [polarStage_apply]
  simpa using pow_le_pow_left₀ (norm_nonneg _)
    (((ContinuousLinearMap.fst ℝ E F).comp (C p.2)).norm_le_norm_polarDeformation_apply_le
      (hC p.2) p.1.2 (u p.2)).1 2

/-- Stages 2 and 3 of the comparison, for a continuous family of linear maps `C x : E → E × F`
pulling `Q` back to `-‖u‖²`, evaluated along `u`: contract the positive components, then deform
the negative blocks `(C x ·).1` to their polar factors. If every `C x (u x)` lies in a closed ball
of radius `R` contained in `V`, all maps of the homotopy take values in `V` and keep `Q` at most
`-‖u‖²`. -/
private noncomputable def negativeDiscTail (C : C(X, E →L[ℝ] E × F)) (u : C(X, E))
    (hC : ∀ x v, ‖(C x v).1‖ ^ 2 - ‖(C x v).2‖ ^ 2 = ‖v‖ ^ 2) {V : Set (E × F)} {R : ℝ}
    (hRV : closedBall (0 : E × F) R ⊆ V) (hCR : ∀ x, ‖C x (u x)‖ ≤ R) :
    ContinuousMap.HomotopyWith (⟨fun x ↦ C x (u x), by fun_prop⟩ : C(X, E × F))
      ⟨fun x ↦ (((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor (u x), 0), by
        have := continuous_polarFactor_fst_comp C
          fun x ↦ (C x).norm_le_norm_fst_of_norm_sq_sub (hC x)
        fun_prop⟩
      fun g ↦ ∀ x, g x ∈ V ∧ -‖(g x).1‖ ^ 2 + ‖(g x).2‖ ^ 2 ≤ -‖u x‖ ^ 2 :=
  have hN (x : X) (v : E) : ‖v‖ ≤ ‖(C x v).1‖ := (C x).norm_le_norm_fst_of_norm_sq_sub (hC x) v
  have hP {z : E × F} (x : X) (hz : ‖z‖ ≤ ‖C x (u x)‖)
      (hq : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖u x‖ ^ 2) :
      z ∈ V ∧ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -‖u x‖ ^ 2 :=
    ⟨hRV (mem_closedBall_zero_iff.mpr (hz.trans (hCR x))), hq⟩
  ContinuousMap.HomotopyWith.trans
    { toHomotopy := positiveContraction C u
      prop' := fun t x ↦ by
        have h₁ := norm_positiveContraction_le C u (t, x)
        have h₂ := positiveContraction_neg_norm_sq_add_le C u hC (t, x)
        exact hP x h₁ h₂ }
    { toHomotopy := polarStage C hN u
      prop' := fun t x ↦ by
        have h₁ := norm_polarStage_le C hN u (t, x)
        have h₂ := polarStage_neg_norm_sq_add_le C hN u (t, x)
        exact hP x h₁ h₂ }

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
  -- Stage 1: rescale `T` to its derivative, keeping values in `V` and `Q = -‖u‖²`.
  let H₁ : ContinuousMap.HomotopyWith
      ⟨fun w : closedBall (0 : E) δ ↦ T ((w : E), 0),
        hc.comp_continuous (by fun_prop) fun w ↦ hδU (hw w)⟩
      ⟨fun w ↦ C w, by fun_prop⟩
      fun g ↦ ∀ w, g w ∈ V ∧ -‖(g w).1‖ ^ 2 + ‖(g w).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 :=
    { toFun := fun p ↦ derivativeRescale T A (σ p.1 : ℝ) ((p.2 : E), 0)
      continuous_toFun := hcont.comp_continuous
        (f := fun p : I × closedBall (0 : E) δ ↦ ((σ p.1 : ℝ), ((p.2 : E), (0 : F))))
        (by fun_prop) fun p ↦
        ⟨⟨(σ p.1).2.1, (σ p.1).2.2⟩, hw p.2⟩
      map_zero_left := fun w ↦ by simp [derivativeRescale_one, hT0]
      map_one_left := fun w ↦ by simp [derivativeRescale_zero, C]
      prop' := fun t w ↦ by
        obtain ⟨-, hV', hq⟩ := hbound _ ⟨(σ t).2.1, (σ t).2.2⟩ _ (hw w)
        exact ⟨hV', le_of_eq (by simpa using hq)⟩ }
  -- Stages 2 and 3: contract the positive component, then deform the negative block to its
  -- polar factor.
  let H := H₁.trans (negativeDiscTail (ContinuousMap.const _ C) ι (fun _ ↦ hC) hδV hCw)
  exact ⟨fun w hw' ↦ hδU (hw ⟨w, hw'⟩), H.toContinuousMap, fun w ↦ H.apply_zero w,
    fun w ↦ H.apply_one w, fun t w ↦ H.prop t w⟩

section Parametric

variable {P : Type*} [TopologicalSpace P] [CompactSpace P] {T : P → E × F → E × F}
  {D : P → E × F → (E × F) →L[ℝ] E × F}

/-- **Small negative discs of two Morse coordinate systems, continuously in a parameter.** Let
`T p` be a family of transitions over a compact parameter space `P`, each fixing the origin and
preserving `Q(u, v) = -‖u‖² + ‖v‖²` on a common open neighbourhood `U` of the origin, with `T`
jointly continuous on `P × U` and its derivative `D` jointly continuous at `P × {0}`. Let `h p` be
the polar factor of the negative block `u ↦ (D p 0 (u, 0)).1`; it depends continuously on `p`.
Then for every small `δ > 0`, the disc `‖u‖ ≤ δ` of `E` lies in `U`, and the maps
`u ↦ T p (u, 0)` on it are homotopic to `u ↦ (h p u, 0)` through maps `g` with values in the
prescribed neighbourhood `V` of the origin and with `Q (g u) ≤ -‖u‖²`, by one homotopy jointly
continuous in the parameter. -/
theorem exists_parametric_negativeDisc_homotopy
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U)
    (hT : ∀ p, ∀ y ∈ U, HasFDerivAt (T p) (D p y) y)
    (hTc : ContinuousOn (fun x : P × (E × F) ↦ T x.1 x.2) (univ ×ˢ U))
    (hD : ∀ p, ContinuousAt (fun x : P × (E × F) ↦ D x.1 x.2) (p, 0))
    (hT0 : ∀ p, T p 0 = 0)
    (hQ : ∀ p, ∀ y ∈ U, -‖(T p y).1‖ ^ 2 + ‖(T p y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    (hV : V ∈ 𝓝 0) :
    ∃ h : P → E ≃ₗᵢ[ℝ] E, (∀ p, ⇑(h p) = ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      Continuous (fun p ↦ ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, (∀ w ∈ closedBall (0 : E) δ, (w, (0 : F)) ∈ U) ∧
        ∃ H : C(I × (P × closedBall (0 : E) δ), E × F),
          (∀ p w, H (0, p, w) = T p ((w : E), 0)) ∧ (∀ p w, H (1, p, w) = (h p w, 0)) ∧
          ∀ t p w, H (t, p, w) ∈ V ∧
            -‖(H (t, p, w)).1‖ ^ 2 + ‖(H (t, p, w)).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL, hDL, δ₀, hδ₀, hδU, hδV, hcont, hbound⟩ :=
    exists_parametric_small_disk_derivativeRescale hU h0U hT hTc hD hT0 hQ hV
  -- The negative columns `C p` of the derivatives depend continuously on `p` and pull `Q` back to
  -- `-‖u‖²`, so their negative blocks expand norms.
  have hD₀ : Continuous fun p ↦ D p 0 :=
    continuous_iff_continuousAt.2 fun p ↦
      (hD p).comp_of_eq (continuous_id.prodMk continuous_const).continuousAt rfl
  let C : C(P, E →L[ℝ] E × F) :=
    ⟨fun p ↦ (D p 0).comp (ContinuousLinearMap.inl ℝ E F), by fun_prop⟩
  have hC (p : P) (u : E) : ‖(C p u).1‖ ^ 2 - ‖(C p u).2‖ ^ 2 = ‖u‖ ^ 2 :=
    norm_sq_sub_comp_inl (hT p 0 h0U) (hT0 p) hU h0U (hQ p) u
  have hN (p : P) (u : E) : ‖u‖ ≤ ‖(C p u).1‖ := (C p).norm_le_norm_fst_of_norm_sq_sub (hC p) u
  -- Their polar factors are linear isometry equivalences, continuous in `p`.
  let h₀ (p : P) : E →ₗᵢ[ℝ] E :=
    { toLinearMap := ((ContinuousLinearMap.fst ℝ E F).comp (C p)).polarFactor
      norm_map' := ((ContinuousLinearMap.fst ℝ E F).comp (C p)).norm_polarFactor_apply_of_injective
        (ContinuousLinearMap.injective_of_forall_norm_le (M := 1) fun x ↦ by simpa using hN p x) }
  refine ⟨fun p ↦ (h₀ p).toLinearIsometryEquiv rfl, fun p ↦ rfl,
    continuous_polarFactor_fst_comp C hN, δ₀, hδ₀,
    fun δ hδ ↦ ?_⟩
  let ι : C(P × closedBall (0 : E) δ, E) := ⟨fun x ↦ x.2, by fun_prop⟩
  let Cx : C(P × closedBall (0 : E) δ, E →L[ℝ] E × F) := C.comp ⟨Prod.fst, continuous_fst⟩
  have hw (w : closedBall (0 : E) δ) : ((w : E), (0 : F)) ∈ closedBall (0 : E × F) δ₀ := by
    have := mem_closedBall_zero_iff.mp w.2
    simpa [Prod.norm_def] using this.trans hδ.2
  have hCw (x : P × closedBall (0 : E) δ) : ‖Cx x (ι x)‖ ≤ L * δ₀ := by
    have := mem_closedBall_zero_iff.mp (hw x.2)
    calc ‖Cx x (ι x)‖ ≤ ‖D x.1 0‖ * ‖((x.2 : E), (0 : F))‖ := (D x.1 0).le_opNorm _
      _ ≤ L * δ₀ := mul_le_mul (hDL x.1) this (norm_nonneg _) hL.le
  -- Stage 1: rescale every `T p` to its derivative, keeping values in `V` and `Q = -‖u‖²`.
  let H₁ : ContinuousMap.HomotopyWith
      ⟨fun x : P × closedBall (0 : E) δ ↦ T x.1 ((x.2 : E), 0),
        hTc.comp_continuous (f := fun x : P × closedBall (0 : E) δ ↦ (x.1, ((x.2 : E), (0 : F))))
          (by fun_prop) fun x ↦ ⟨trivial, hδU (hw x.2)⟩⟩
      ⟨fun x ↦ Cx x (ι x), by fun_prop⟩
      fun g ↦ ∀ x, g x ∈ V ∧ -‖(g x).1‖ ^ 2 + ‖(g x).2‖ ^ 2 ≤ -‖ι x‖ ^ 2 :=
    { toFun := fun q ↦ derivativeRescale (T q.2.1) (D q.2.1 0) (σ q.1 : ℝ) ((q.2.2 : E), 0)
      continuous_toFun := hcont.comp_continuous
        (f := fun q : I × P × closedBall (0 : E) δ ↦ (q.2.1, (σ q.1 : ℝ), ((q.2.2 : E), (0 : F))))
        (by fun_prop) fun q ↦ ⟨trivial, ⟨(σ q.1).2.1, (σ q.1).2.2⟩, hw q.2.2⟩
      map_zero_left := fun x ↦ by simp [derivativeRescale_one, hT0]
      map_one_left := fun x ↦ by simp [derivativeRescale_zero, Cx, C, ι]
      prop' := fun t x ↦ by
        obtain ⟨-, hV', hq⟩ := hbound x.1 _ ⟨(σ t).2.1, (σ t).2.2⟩ _ (hw x.2)
        exact ⟨hV', le_of_eq (by simpa [ι] using hq)⟩ }
  -- Stages 2 and 3: contract the positive components, then deform the negative blocks to their
  -- polar factors.
  let H := H₁.trans (negativeDiscTail Cx ι (fun x ↦ hC x.1) hδV hCw)
  exact ⟨fun w hw' ↦ hδU (hw ⟨w, hw'⟩), H.toContinuousMap, fun p w ↦ H.apply_zero (p, w),
    fun p w ↦ H.apply_one (p, w), fun t p w ↦ H.prop t (p, w)⟩

end Parametric

end TauCeti
