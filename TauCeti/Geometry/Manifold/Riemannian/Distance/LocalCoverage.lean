/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.PathELength
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Topology.Order.Interval.Basic

/-!
# Quantitative ball coverage by local diffeomorphisms

A partial diffeomorphism defined on a closed source ball of radius `R` covers the open ball
of radius `r` centered at the image of the source center when its inverse differential is
bounded by a positive constant `C` and `C * r ≤ R`. The image of the closed source ball must
be closed; compactness of that ball is sufficient but is not required for the bundled results.
Neither manifold needs to be complete.

The same positive constant controls radial distances of the inverse inside that centered
target ball. A pointwise equivalence makes both estimates available from a lower bound on the
forward differential. For an ordinary map, local diffeomorphism and injectivity are required
only on a compact closed source ball; an injective open neighborhood is derived.

This is the local coverage argument used in pointed geometric convergence, adapted from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference.
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology NNReal

namespace PartialDiffeomorph

section DifferentialBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- At a source point of a partial diffeomorphism, an upper bound `C` for the inverse
differential is equivalent to the corresponding lower bound for the forward differential. -/
theorem norm_mfderiv_symm_le_iff
    (e : PartialDiffeomorph I J M N 1) {x : M} (hx : x ∈ e.source) {C : ℝ≥0} :
    (∀ v : TangentSpace J (e x), ‖mfderiv J I e.symm (e x) v‖ ≤ C * ‖v‖) ↔
      ∀ v : TangentSpace I x, ‖v‖ ≤ C * ‖mfderiv I J e x v‖ := by
  have hleft : e.symm (e x) = x := e.toPartialEquiv.left_inv hx
  constructor
  · intro h v
    have hv := h (mfderiv I J e x v)
    have hnorm := TauCeti.norm_tangentSpace_congr (I := I) hleft
      (e.mfderiv_symm_apply_mfderiv_apply one_ne_zero hx v)
    rwa [hnorm] at hv
  · intro h v
    obtain ⟨w, hw⟩ := (e.isInvertible_mfderiv one_ne_zero hx).surjective v
    calc
      ‖mfderiv J I e.symm (e x) v‖ = ‖w‖ :=
        TauCeti.norm_tangentSpace_congr (I := I) hleft (by
          rw [← hw]
          exact e.mfderiv_symm_apply_mfderiv_apply one_ne_zero hx w)
      _ ≤ C * ‖mfderiv I J e x w‖ := h w
      _ = C * ‖v‖ := by rw [hw]

end DifferentialBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

omit [IsRiemannianManifold J N] in
private theorem inverse_edist_le_mul_pathELength
    (e : PartialDiffeomorph I J M N 1) {p : M} {R : ℝ≥0∞}
    (hsource : Metric.closedEBall p R ⊆ e.source) {C : ℝ≥0}
    (hbound : ∀ x ∈ Metric.eball p R, ∀ v : TangentSpace J (e x),
      ‖mfderiv J I e.symm (e x) v‖ ≤ C * ‖v‖)
    {γ : ℝ → N} {t : ℝ} (ht : 0 ≤ t)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) J 1 γ (Icc 0 t))
    (h0 : γ 0 = e p)
    (hmaps : MapsTo γ (Icc 0 t) (e '' Metric.closedEBall p R))
    (hinterior : MapsTo γ (Ioo 0 t) (e '' Metric.eball p R)) :
    edist p (e.symm (γ t)) ≤ C * pathELength J γ 0 t := by
  have htarget : MapsTo γ (Icc (0 : ℝ) t) e.target :=
    hmaps.mono_right (e.toPartialEquiv.mapsTo.mono_left hsource).image_subset
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (e.symm ∘ γ) (Icc 0 t) :=
    e.symm.contMDiffOn.comp hγ htarget
  have hlen := TauCeti.Manifold.pathELength_comp_le_mul_of_norm_mfderiv_le
    ((hγ.mdifferentiableOn one_ne_zero).mono Ioo_subset_Icc_self)
    (fun s hs ↦ e.symm.mdifferentiableAt one_ne_zero (htarget ⟨hs.1.le, hs.2.le⟩))
    (C := C) (fun s hs ↦ by
      obtain ⟨x, hx, hxe⟩ := hinterior hs
      rw [← hxe]
      exact hbound x hx _)
  have hstart : (e.symm ∘ γ) 0 = p := by
    rw [Function.comp_apply, h0]
    exact e.toPartialEquiv.left_inv (hsource Metric.mem_closedEBall_self)
  have hd := TauCeti.IsRiemannianManifold.edist_le_pathELength hsmooth ht
  rw [hstart] at hd
  exact hd.trans hlen

/-- If the inverse differential is bounded by a positive constant `C` over the open source
ball of radius `R`, the open target ball of radius `r` centered at the image of the source center
is covered when `C * r ≤ R`. The closed source ball lies in the source and has closed image. -/
theorem eball_subset_image_eball_of_norm_mfderiv_symm_le
    (e : PartialDiffeomorph I J M N 1) {p : M} {R r : ℝ≥0∞} {C : ℝ≥0}
    (hC : C ≠ 0) (hclosed : IsClosed (e '' Metric.closedEBall p R))
    (hsource : Metric.closedEBall p R ⊆ e.source) (hr : (C : ℝ≥0∞) * r ≤ R)
    (hbound : ∀ x ∈ Metric.eball p R, ∀ v : TangentSpace J (e x),
      ‖mfderiv J I e.symm (e x) v‖ ≤ C * ‖v‖) :
    Metric.eball (e p) r ⊆ e '' Metric.eball p R := by
  intro y hy
  have hrpos : 0 < r := Metric.pos_of_mem_eball hy
  have hRpos : 0 < R := (ENNReal.mul_pos (by exact_mod_cast hC) hrpos.ne').trans_le hr
  have hV : IsOpen (e '' Metric.eball p R) :=
    e.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_eball
      (Metric.eball_subset_closedEBall.trans hsource)
  by_contra hyimage
  rw [Metric.mem_eball', IsRiemannianManifold.out (I := J)] at hy
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  obtain ⟨t, ht, htpos, htnot, htclosure, hbefore⟩ := hV.exists_first_exit hγ.continuousOn
    (by rw [h0]; exact mem_image_of_mem e (Metric.mem_eball_self hRpos))
    ⟨1, by norm_num, by simpa only [h1] using hyimage⟩
  have htK : γ t ∈ e '' Metric.closedEBall p R :=
    hclosed.closure_subset_iff.2 (image_mono Metric.eball_subset_closedEBall) htclosure
  have hmaps : MapsTo γ (Icc 0 t) (e '' Metric.closedEBall p R) := by
    intro s hs
    rcases hs.2.eq_or_lt with hst | hst
    · simpa only [hst] using htK
    · exact image_mono Metric.eball_subset_closedEBall (hbefore s ⟨hs.1, hst⟩)
  have hdist := e.inverse_edist_le_mul_pathELength hsource hbound htpos.le
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h0 hmaps
    (fun s hs ↦ hbefore s ⟨hs.1.le, hs.2⟩)
  have hsmall : e.symm (γ t) ∈ Metric.eball p R := by
    rw [Metric.mem_eball']
    refine hdist.trans_lt (lt_of_lt_of_le ?_ hr)
    simpa only [mul_comm] using
      ENNReal.mul_lt_mul_left (by exact_mod_cast hC) ENNReal.coe_ne_top
        ((Manifold.pathELength_mono le_rfl ht.2).trans_lt hlength)
  apply htnot
  rw [e.toPartialEquiv.image_eq_target_inter_inv_preimage
    (Metric.eball_subset_closedEBall.trans hsource)]
  exact ⟨(e.toPartialEquiv.mapsTo.mono_left hsource).image_subset htK, hsmall⟩

/-- On the covered open ball centered at the image of the source center, the inverse expands
radial extended distances from that center by at most the positive differential bound `C`.
The closed source ball lies in the source and has closed image, and `C * r ≤ R`. -/
theorem edist_symm_le_mul_of_norm_mfderiv_symm_le
    (e : PartialDiffeomorph I J M N 1) {p : M} {R r : ℝ≥0∞} {C : ℝ≥0}
    (hC : C ≠ 0) (hclosed : IsClosed (e '' Metric.closedEBall p R))
    (hsource : Metric.closedEBall p R ⊆ e.source) (hr : (C : ℝ≥0∞) * r ≤ R)
    (hbound : ∀ x ∈ Metric.eball p R, ∀ v : TangentSpace J (e x),
      ‖mfderiv J I e.symm (e x) v‖ ≤ C * ‖v‖) {y : N}
    (hy : y ∈ Metric.eball (e p) r) :
    edist p (e.symm y) ≤ C * edist (e p) y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hC
  have hcover := e.eball_subset_image_eball_of_norm_mfderiv_symm_le
    hC hclosed hsource hr hbound
  rw [← ENNReal.div_le_iff' hC0 ENNReal.coe_ne_top]
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  have hnear : Manifold.riemannianEDist J (e p) y < min c r := by
    rw [← IsRiemannianManifold.out (I := J)]
    exact lt_min hc (Metric.mem_eball'.1 hy)
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hnear
  have hmaps : MapsTo γ (Icc 0 1) (e '' Metric.eball p R) := by
    intro t ht
    apply hcover
    rw [Metric.mem_eball', ← h0]
    exact ((TauCeti.IsRiemannianManifold.edist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) ht.1).trans
      (Manifold.pathELength_mono le_rfl ht.2)).trans_lt
        (hlen.trans_le (min_le_right _ _))
  have hd := e.inverse_edist_le_mul_pathELength hsource hbound zero_le_one hγ h0
    (hmaps.mono_right (image_mono Metric.eball_subset_closedEBall))
    (hmaps.mono_left Ioo_subset_Icc_self)
  rw [h1] at hd
  have hmul : edist p (e.symm y) ≤ (C : ℝ≥0∞) * c :=
    hd.trans (by gcongr; exact hlen.le.trans (min_le_left _ _))
  exact (ENNReal.div_le_iff' hC0 ENNReal.coe_ne_top).2 hmul

/-- A positive constant `C` bounding the forward differential from below gives coverage of
the open target ball centered at the image of the source center when `C * r ≤ R`.
The closed source ball lies in the source and has closed image. -/
theorem eball_subset_image_eball_of_norm_le_mul_norm_mfderiv
    (e : PartialDiffeomorph I J M N 1) {p : M} {R r : ℝ≥0∞} {C : ℝ≥0}
    (hC : C ≠ 0) (hclosed : IsClosed (e '' Metric.closedEBall p R))
    (hsource : Metric.closedEBall p R ⊆ e.source) (hr : (C : ℝ≥0∞) * r ≤ R)
    (hbound : ∀ x ∈ Metric.eball p R, ∀ v : TangentSpace I x,
      ‖v‖ ≤ C * ‖mfderiv I J e x v‖) :
    Metric.eball (e p) r ⊆ e '' Metric.eball p R := by
  apply e.eball_subset_image_eball_of_norm_mfderiv_symm_le hC hclosed hsource hr
  exact fun x hx ↦ (e.norm_mfderiv_symm_le_iff
    (hsource (Metric.eball_subset_closedEBall hx))).mpr (hbound x hx)

end PartialDiffeomorph

namespace IsLocalDiffeomorphOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [PseudoEMetricSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

/-- A map locally diffeomorphic and injective on a compact closed source ball covers the
open target ball centered at the image of the source center when its forward differential
has lower bound `1 / C` on the open source ball, `C` is positive and `C * r ≤ R`. -/
theorem eball_subset_image_eball_of_norm_le_mul_norm_mfderiv {f : M → N}
    {p : M} {R r : ℝ≥0∞} {C : ℝ≥0}
    (hf : IsLocalDiffeomorphOn I J 1 f (Metric.closedEBall p R))
    (hinj : InjOn f (Metric.closedEBall p R)) (hC : C ≠ 0)
    (hcompact : IsCompact (Metric.closedEBall p R)) (hr : (C : ℝ≥0∞) * r ≤ R)
    (hbound : ∀ x ∈ Metric.eball p R, ∀ v : TangentSpace I x,
      ‖v‖ ≤ C * ‖mfderiv I J f x v‖) :
    Metric.eball (f p) r ⊆ f '' Metric.eball p R := by
  have : Nonempty M := ⟨p⟩
  -- Native manifold separation turns compact image sets into closed sets.
  let : T1Space N := J.t1Space N
  let : EMetricSpace N := .ofT0PseudoEMetricSpace N
  obtain ⟨U, hU, hKU, hInj, hLoc⟩ :=
    hinj.exists_isOpen_superset_isLocalDiffeomorphOn hcompact (fun x hx ↦ hf ⟨x, hx⟩)
  let e := hLoc.partialDiffeomorphOfInjOn hU hInj
  have he : (e : M → N) = f := hLoc.coe_partialDiffeomorphOfInjOn hU hInj
  have hs : Metric.closedEBall p R ⊆ e.source := by
    simpa only [e, partialDiffeomorphOfInjOn_source] using hKU
  have hclosed : IsClosed (e '' Metric.closedEBall p R) :=
    (hcompact.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hs)).isClosed
  have hb (x) (hx : x ∈ Metric.eball p R) (v : TangentSpace I x) :
      ‖v‖ ≤ C * ‖mfderiv I J e x v‖ := by
    rw [he]
    exact hbound x hx v
  simpa only [he] using e.eball_subset_image_eball_of_norm_le_mul_norm_mfderiv hC
    hclosed hs hr hb

end IsLocalDiffeomorphOn
