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

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Linear

variable {X : Type*} [TopologicalSpace X]

/-- The polar factors of the negative blocks `(C x ·).1` of a continuous family of linear maps
`C x : E → E × F` depend continuously on `x` when the negative blocks expand norms. -/
private theorem continuous_polarFactor_fst_comp (C : C(X, E →L[ℝ] E × F))
    (hC : ∀ x v, ‖v‖ ≤ ‖(C x v).1‖) :
    Continuous fun x ↦ ((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor := by
  have hN : Continuous fun x ↦ (ContinuousLinearMap.fst ℝ E F).comp (C x) := by fun_prop
  exact continuous_iff_continuousAt.2 fun x ↦ (ContinuousLinearMap.continuousAt_polarFactor
    (ContinuousLinearMap.isStrictlyPositive_modulus_of_forall_norm_le _ (hC x)).isUnit).comp
      (f := fun x ↦ (ContinuousLinearMap.fst ℝ E F).comp (C x)) hN.continuousAt

end Linear

section Homotopy

variable {X : Type*} [TopologicalSpace X] {V : Set (E × F)}

omit [CompleteSpace E] in
/-- A transition evaluated along `u` is continuous when its rescalings are jointly continuous on
a ball containing every `(u x, 0)`: it is the rescaling at scale one. -/
private theorem continuous_rescaleStage_start (T : X → E × F → E × F)
    (A : C(X, (E × F) →L[ℝ] E × F)) (u : C(X, E)) (hT0 : ∀ x, T x 0 = 0) {δ : ℝ}
    (hcont : ContinuousOn
      (fun q : X × ℝ × (E × F) ↦ derivativeRescale (T q.1) (A q.1) q.2.1 q.2.2)
      (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall 0 δ)))
    (hu : ∀ x, ‖u x‖ ≤ δ) : Continuous fun x ↦ T x (u x, 0) := by
  refine (hcont.comp_continuous (f := fun x ↦ (x, (1 : ℝ), (u x, (0 : F)))) (by fun_prop)
    fun x ↦ ⟨trivial, ⟨zero_le_one, le_rfl⟩, by simpa [Prod.norm_def] using hu x⟩).congr
      fun x ↦ ?_
  simp [hT0]

/-- All three stages of the comparison, for a family of transitions `T x` with continuous
derivatives `A x` at the origin, evaluated along `u`: rescale `T x` to `A x`, contract the positive
components, then deform the negative blocks to their polar factors
(`ContinuousMap.exists_homotopy_polarFactor_of_norm_sq_sub`). The rescalings must be jointly
continuous and keep values in `V` and the exact value of `Q` on the ball of radius `δ`, which
contains every `(u x, 0)`, and the ball of radius `L * δ` must lie in `V` for a bound `L` on the
derivatives. -/
private theorem exists_negativeDiscHomotopy (T : X → E × F → E × F)
    (A : C(X, (E × F) →L[ℝ] E × F)) (u : C(X, E)) (hT0 : ∀ x, T x 0 = 0)
    (hC : ∀ x v, ‖((A x).comp (ContinuousLinearMap.inl ℝ E F) v).1‖ ^ 2 -
      ‖((A x).comp (ContinuousLinearMap.inl ℝ E F) v).2‖ ^ 2 = ‖v‖ ^ 2) {δ L : ℝ}
    (hcont : ContinuousOn
      (fun q : X × ℝ × (E × F) ↦ derivativeRescale (T q.1) (A q.1) q.2.1 q.2.2)
      (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall 0 δ)))
    (hbound : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall (0 : E × F) δ,
      derivativeRescale (T x) (A x) s y ∈ V ∧
        -‖(derivativeRescale (T x) (A x) s y).1‖ ^ 2 +
            ‖(derivativeRescale (T x) (A x) s y).2‖ ^ 2 =
          -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    (hu : ∀ x, ‖u x‖ ≤ δ) (hAL : ∀ x, ‖A x‖ ≤ L) (hL : 0 ≤ L)
    (hLV : closedBall (0 : E × F) (L * δ) ⊆ V) :
    ∃ H : C(I × X, E × F), (∀ x, H (0, x) = T x (u x, 0)) ∧
      (∀ x, H (1, x) = (((ContinuousLinearMap.fst ℝ E F).comp
        ((A x).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor (u x), 0)) ∧
      ∀ t x, H (t, x) ∈ V ∧ -‖(H (t, x)).1‖ ^ 2 + ‖(H (t, x)).2‖ ^ 2 ≤ -‖u x‖ ^ 2 := by
  have hw (x : X) : (u x, (0 : F)) ∈ closedBall (0 : E × F) δ := by
    simpa [Prod.norm_def] using hu x
  let C : C(X, E →L[ℝ] E × F) :=
    ⟨fun x ↦ (A x).comp (ContinuousLinearMap.inl ℝ E F), by fun_prop⟩
  have hCu (x : X) : ‖C x (u x)‖ ≤ L * δ :=
    calc ‖C x (u x)‖ ≤ ‖A x‖ * ‖(u x, (0 : F))‖ := (A x).le_opNorm _
      _ ≤ L * δ := mul_le_mul (hAL x) (mem_closedBall_zero_iff.mp (hw x)) (norm_nonneg _) hL
  obtain ⟨K, hK₀, hK₁, hK⟩ := C.exists_homotopy_polarFactor_of_norm_sq_sub u hC
  let P : C(X, E × F) → Prop :=
    fun g ↦ ∀ x, g x ∈ V ∧ -‖(g x).1‖ ^ 2 + ‖(g x).2‖ ^ 2 ≤ -‖u x‖ ^ 2
  let g₁ : C(X, E × F) := ⟨fun x ↦ C x (u x), by fun_prop⟩
  let g₂ : C(X, E × F) :=
    ⟨fun x ↦ (((ContinuousLinearMap.fst ℝ E F).comp (C x)).polarFactor (u x), 0),
      (K.continuous.comp (Continuous.prodMk_right (1 : I))).congr hK₁⟩
  -- Stage 1: rescale every `T x` to its derivative, keeping values in `V` and `Q = -‖u‖²`.
  let H₁ : ContinuousMap.HomotopyWith
      ⟨fun x ↦ T x (u x, 0), continuous_rescaleStage_start T A u hT0 hcont hu⟩ g₁ P :=
    { toFun := fun p ↦ derivativeRescale (T p.2) (A p.2) (σ p.1 : ℝ) (u p.2, 0)
      continuous_toFun := hcont.comp_continuous
        (f := fun p : I × X ↦ (p.2, (σ p.1 : ℝ), (u p.2, (0 : F)))) (by fun_prop) fun p ↦
          ⟨trivial, ⟨(σ p.1).2.1, (σ p.1).2.2⟩, hw p.2⟩
      map_zero_left := fun x ↦ by simp [hT0]
      map_one_left := fun x ↦ by simp [g₁, C]
      prop' := fun t x ↦ by
        obtain ⟨hV', hq⟩ := hbound x _ ⟨(σ t).2.1, (σ t).2.2⟩ _ (hw x)
        exact ⟨hV', le_of_eq (by simpa using hq)⟩ }
  -- Stages 2 and 3: contract the positive components, then deform the negative blocks to their
  -- polar factors.
  let H₂ : g₁.HomotopyWith g₂ P :=
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := hK₀
      map_one_left := hK₁
      prop' := fun t x ↦
        ⟨hLV (mem_closedBall_zero_iff.mpr ((hK (t, x)).1.trans (hCu x))), (hK (t, x)).2⟩ }
  let H := H₁.trans H₂
  exact ⟨H.toContinuousMap, fun x ↦ H.apply_zero x, fun x ↦ H.apply_one x, fun t x ↦ H.prop t x⟩

end Homotopy

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
  -- The negative column of `A` pulls `Q` back to `-‖u‖²`, so its negative block expands norms,
  -- and its polar factor is a linear isometry.
  have hC (u : E) := norm_sq_sub_comp_inl hT hT0 hU h0U hQ u
  have hN (u : E) := (A.comp (ContinuousLinearMap.inl ℝ E F)).norm_le_norm_fst_of_norm_sq_sub hC u
  have hinj : Function.Injective ((ContinuousLinearMap.fst ℝ E F).comp
      (A.comp (ContinuousLinearMap.inl ℝ E F))) :=
    ContinuousLinearMap.injective_of_forall_norm_le (M := 1) fun u ↦ by simpa using hN u
  refine ⟨ContinuousLinearMap.polarIsometry _ hinj,
    ContinuousLinearMap.coe_polarIsometry _ hinj, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  have hw {w : E} (hw : w ∈ closedBall (0 : E) δ) : (w, (0 : F)) ∈ closedBall (0 : E × F) δ₀ := by
    simpa [Prod.norm_def] using (mem_closedBall_zero_iff.mp hw).trans hδ.2
  let ι : C(closedBall (0 : E) δ, E) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨H, hH₀, hH₁, hH⟩ := exists_negativeDiscHomotopy (fun _ ↦ T) (ContinuousMap.const _ A)
    ι (fun _ ↦ hT0) (fun _ ↦ hC) (hcont.comp continuous_snd.continuousOn fun _ hq ↦ hq.2)
    (fun _ s hs y hy ↦ (hbound s hs y hy).2) (fun w ↦ (mem_closedBall_zero_iff.mp w.2).trans hδ.2)
    (fun _ ↦ hAL) hL.le hδV
  exact ⟨fun w hw' ↦ hδU (hw hw'), H, hH₀,
    fun w ↦ by rw [hH₁, ContinuousLinearMap.coe_polarIsometry]; rfl, hH⟩

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
    ∃ h : P → E →ₗᵢ[ℝ] E, (∀ p, ⇑(h p) = ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      Continuous (fun p ↦ ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, (∀ w ∈ closedBall (0 : E) δ, (w, (0 : F)) ∈ U) ∧
        ∃ H : C(I × (P × closedBall (0 : E) δ), E × F),
          (∀ p w, H (0, p, w) = T p ((w : E), 0)) ∧ (∀ p w, H (1, p, w) = (h p w, 0)) ∧
          ∀ t p w, H (t, p, w) ∈ V ∧
            -‖(H (t, p, w)).1‖ ^ 2 + ‖(H (t, p, w)).2‖ ^ 2 ≤ -‖(w : E)‖ ^ 2 := by
  obtain ⟨L, hL, hDL, δ₀, hδ₀, hδU, hδV, hcont, hbound⟩ :=
    exists_parametric_small_disk_derivativeRescale hU h0U hT hTc hD hT0 hQ hV
  -- The negative columns `C p` of the derivatives depend continuously on `p` and pull `Q` back to
  -- `-‖u‖²`, so their negative blocks expand norms, and their polar factors are linear isometries,
  -- continuous in `p`.
  have hD₀ : Continuous fun p ↦ D p 0 :=
    continuous_iff_continuousAt.2 fun p ↦ (hD p).comp₂ continuousAt_id continuousAt_const
  let C : C(P, E →L[ℝ] E × F) :=
    ⟨fun p ↦ (D p 0).comp (ContinuousLinearMap.inl ℝ E F), by fun_prop⟩
  have hC (p : P) (u : E) : ‖(C p u).1‖ ^ 2 - ‖(C p u).2‖ ^ 2 = ‖u‖ ^ 2 :=
    norm_sq_sub_comp_inl (hT p 0 h0U) (hT0 p) hU h0U (hQ p) u
  have hN (p : P) (u : E) : ‖u‖ ≤ ‖(C p u).1‖ := (C p).norm_le_norm_fst_of_norm_sq_sub (hC p) u
  have hinj (p : P) : Function.Injective ((ContinuousLinearMap.fst ℝ E F).comp (C p)) :=
    ContinuousLinearMap.injective_of_forall_norm_le (M := 1) fun u ↦ by simpa using hN p u
  refine ⟨fun p ↦ ContinuousLinearMap.polarIsometry _ (hinj p),
    fun p ↦ ContinuousLinearMap.coe_polarIsometry _ (hinj p), continuous_polarFactor_fst_comp C hN,
    δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  have hw {w : E} (hw : w ∈ closedBall (0 : E) δ) : (w, (0 : F)) ∈ closedBall (0 : E × F) δ₀ := by
    simpa [Prod.norm_def] using (mem_closedBall_zero_iff.mp hw).trans hδ.2
  let ι : C(P × closedBall (0 : E) δ, E) := ⟨fun x ↦ x.2, by fun_prop⟩
  let A : C(P × closedBall (0 : E) δ, (E × F) →L[ℝ] E × F) := ⟨fun x ↦ D x.1 0, by fun_prop⟩
  have hcont' : ContinuousOn (fun q : (P × closedBall (0 : E) δ) × ℝ × (E × F) ↦
      derivativeRescale (T q.1.1) (A q.1) q.2.1 q.2.2)
      (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall 0 δ₀)) :=
    hcont.comp (by fun_prop : Continuous fun q : (P × closedBall (0 : E) δ) × ℝ × (E × F) ↦
      (q.1.1, q.2)).continuousOn fun _ hq ↦ ⟨trivial, hq.2⟩
  obtain ⟨H, hH₀, hH₁, hH⟩ := exists_negativeDiscHomotopy (fun x ↦ T x.1) A ι (fun x ↦ hT0 x.1)
    (fun x ↦ hC x.1) hcont' (fun x s hs y hy ↦ (hbound x.1 s hs y hy).2)
    (fun x ↦ (mem_closedBall_zero_iff.mp x.2.2).trans hδ.2) (fun x ↦ hDL x.1) hL.le hδV
  exact ⟨fun w hw' ↦ hδU (hw hw'), H, fun p w ↦ hH₀ (p, w),
    fun p w ↦ by rw [hH₁, ContinuousLinearMap.coe_polarIsometry]; rfl, fun t p w ↦ hH t (p, w)⟩

end Parametric

end TauCeti
