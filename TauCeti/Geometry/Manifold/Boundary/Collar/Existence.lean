/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth

import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Basic
import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Boundary.OutwardExistence
import TauCeti.Geometry.Manifold.ContMDiffMap.Radius

/-!
# The smooth collar theorem

The boundary of a smooth Hausdorff sigma-compact manifold modeled on a Euclidean half-space
admits a smooth collar. Flow the boundary along the negative of a smooth outward-pointing
field. The flow-out is injective on its forward domain and is a local diffeomorphism along the
zero section. Choose a positive smooth time bound on each boundary fibre so that the flow-out
remains a local diffeomorphism throughout the collar.

The construction uses `TauCeti.exists_isOutwardPointingField`,
`TauCeti.injOn_flowOut_boundary`, `TauCeti.isLocalDiffeomorphAt_flowOut_boundary` and
`TauCeti.exists_contMDiffMap_closedBall_subset`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public noncomputable section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

local notation "B" => ModelWithCorners.boundary (I := 𝓡∂ (n + 1)) M
local notation "J" => ModelWithCorners.prod (𝓡 n) (𝓡∂ 1)

/-- Rescale each boundary fibre by its positive flow time, preserving the zero section. -/
private def flowDepthDiffeomorph (δ : B → ℝ) (hδ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ δ)
    (hpos : ∀ x, 0 < δ x) : (B × EuclideanHalfSpace 1) ≃ₘ⟮J, J⟯ (B × EuclideanHalfSpace 1) := by
  let scale (r : B → ℝ) (p : B × EuclideanHalfSpace 1) := (p.1, normalRay (r p.1 * p.2.val 0))
  have hscale (r : B → ℝ) (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r) (hr₀ : ∀ x, 0 ≤ r x) :
      ContMDiff J J ∞ (scale r) := by
    have htime : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : EuclideanHalfSpace 1 ↦ t.val 0) :=
      (EuclideanSpace.proj (0 : Fin 1)).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff
    exact contMDiff_fst.prodMk <| ((hr.comp contMDiff_fst).mul (htime.comp contMDiff_snd)).normalRay
      fun p ↦ mul_nonneg (hr₀ p.1) p.2.property
  have hcoord (r : B → ℝ) (hr₀ : ∀ x, 0 ≤ r x) (p : B × EuclideanHalfSpace 1) :
      (scale r p).2.val 0 = r p.1 * p.2.val 0 :=
    (normalRay_coe_apply _).trans (max_eq_left (mul_nonneg (hr₀ _) p.2.property))
  let ρ : B → ℝ := fun x ↦ (δ x)⁻¹
  have hδ₀ (x : B) : 0 ≤ δ x := (hpos x).le
  have hρ₀ (x : B) : 0 ≤ ρ x := inv_nonneg.mpr (hδ₀ x)
  refine
    { toFun := scale δ
      invFun := scale ρ
      left_inv := fun p ↦ Prod.ext rfl ?_
      right_inv := fun p ↦ Prod.ext rfl ?_
      contMDiff_toFun := hscale δ hδ hδ₀
      contMDiff_invFun := hscale ρ (hδ.inv₀ fun x ↦ (hpos x).ne') hρ₀ }
  · calc
      (scale ρ (scale δ p)).2 = normalRay (ρ p.1 * (δ p.1 * p.2.val 0)) := by rw [← hcoord δ hδ₀ p]
      _ = p.2 := by simp [ρ, (hpos p.1).ne']
  · calc
      (scale δ (scale ρ p)).2 = normalRay (δ p.1 * (ρ p.1 * p.2.val 0)) := by rw [← hcoord ρ hρ₀ p]
      _ = p.2 := by simp [ρ, (hpos p.1).ne']

variable [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A forward flow that is locally invertible along the boundary has a positive smooth time bound
within which it stays in the flow domain and is locally invertible. -/
private theorem exists_flowOut_depth {W : Set (M × ℝ)}
    (hW : ∀ x : B, W ∈ 𝓝 ((x : M), (0 : ℝ))) {Φ : M → ℝ → M}
    (hΦ₀ : ∀ x : B, IsLocalDiffeomorphAt J (𝓡∂ (n + 1)) ∞
      (fun p : B × EuclideanHalfSpace 1 ↦ Φ p.1 (p.2.val 0)) (x, 0)) :
    ∃ δ : (let := isManifold_boundary (n := n) (k := ∞) M; C^∞⟮𝓡 n, B; 𝓘(ℝ), ℝ⟯),
      (∀ x, 0 < δ x) ∧ ∀ (x : B) (t : EuclideanHalfSpace 1), t.val 0 ≤ δ x →
        ((x : M), t.val 0) ∈ W ∧ IsLocalDiffeomorphAt J (𝓡∂ (n + 1)) ∞
          (fun p : B × EuclideanHalfSpace 1 ↦ Φ p.1 (p.2.val 0)) (x, t) := by
  let := isManifold_boundary (n := n) (k := ∞) M
  let : SigmaCompactSpace B :=
    ((𝓡∂ (n + 1)).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)).sigmaCompactSpace
  let F : B × EuclideanHalfSpace 1 → M := fun p ↦ Φ p.1 (p.2.val 0)
  let U : Set (B × ℝ) := {p | ((p.1 : M), p.2) ∈ W ∧
    IsLocalDiffeomorphAt J (𝓡∂ (n + 1)) ∞ F (p.1, normalRay p.2)}
  have hW' : Continuous (Prod.map (Subtype.val : B → M) (id : ℝ → ℝ)) :=
    continuous_subtypeVal.prodMap continuous_id
  have hRay : Continuous (Prod.map (id : B → B) normalRay) :=
    continuous_id.prodMap continuous_normalRay
  have hU (x : B) : U ∈ 𝓝 (x, 0) := by
    have hloc : IsLocalDiffeomorphAt J (𝓡∂ (n + 1)) ∞ F (x, normalRay 0) := by
      simpa only [normalRay_zero] using hΦ₀ x
    have hWₓ := hW'.continuousAt (x := (x, 0)) |>.preimage_mem_nhds (hW x)
    have hΦₓ := hRay.continuousAt (x := (x, 0)) |>.preimage_mem_nhds
      (t := {q | IsLocalDiffeomorphAt J (𝓡∂ (n + 1)) ∞ F q}) hloc.eventually
    exact inter_mem hWₓ hΦₓ
  obtain ⟨δ, hδ, -, hδU⟩ := exists_contMDiffMap_closedBall_subset (I := 𝓡 n) hU
    (ε := fun _ ↦ 1) lowerSemicontinuous_const (fun _ ↦ one_pos)
  refine ⟨δ, hδ, fun x t ht ↦ ?_⟩
  have htBall : t.val 0 ∈ Metric.closedBall (0 : ℝ) (δ x) := by
    simpa [Real.dist_eq, abs_of_nonneg t.property] using ht
  have hmem := hδU x (t.val 0) htBall
  exact ⟨hmem.1, by simpa only [normalRay_normalCoord] using hmem.2⟩

/-- **The smooth collar theorem.** A Hausdorff sigma-compact smooth manifold modeled on the
Euclidean half-space has a smooth collar of its whole boundary. This includes compact manifolds
and second-countable manifolds by local compactness. -/
theorem nonempty_smoothCollar : Nonempty (SmoothCollar n ∞ M) := by
  obtain ⟨V, hV⟩ := exists_isOutwardPointingField (n := n) (M := M)
  obtain ⟨W, hW, hW₀, Φ, -, hΦ⟩ := hV.exists_contMDiffOn_boundaryFlow
  have hWnhds (x : B) := hW.mem_nhds (hW₀ x x.property)
  have hΦ₀ (x : B) := isLocalDiffeomorphAt_flowOut_boundary (-V)
    (fun y ↦ (hV.contMDiff y).neg_section) (by simpa using hV.isOutwardPointing x.property)
    (hWnhds x) (Φ := Φ)
    (fun y _ t hyt ht ↦ ⟨(hΦ y t hyt ht).2.1, (hΦ y t hyt ht).2.2.1⟩)
  obtain ⟨δ, hδ, hdepth⟩ := exists_flowOut_depth hWnhds hΦ₀
  let e := flowDepthDiffeomorph δ δ.contMDiff hδ
  let ι : B × normalIioOpens 1 → B × EuclideanHalfSpace 1 := Prod.map id Subtype.val
  let F : B × EuclideanHalfSpace 1 → M := fun p ↦ Φ p.1 (p.2.val 0)
  have he (p : B × normalIioOpens 1) :
      e (ι p) = (p.1, normalRay (δ p.1 * p.2.val.val 0)) := rfl
  have htime (p : B × normalIioOpens 1) : (e (ι p)).2.val 0 = δ p.1 * p.2.val.val 0 := by
    rw [he, normalRay_coe_apply, max_eq_left (mul_nonneg (hδ _).le p.2.val.property)]
  have hgood (p : B × normalIioOpens 1) :=
    hdepth (e (ι p)).1 (e (ι p)).2 (by
      rw [htime, he]
      exact (mul_lt_of_lt_one_right (hδ p.1) (mem_normalIioOpens.1 p.2.property)).le)
  have hι : IsLocalDiffeomorph J J ∞ ι :=
    (Diffeomorph.refl (𝓡 n) B ∞).isLocalDiffeomorph.prodMap isLocalDiffeomorph_subtype_val
  have hΦinj := injOn_flowOut_boundary (v := -V)
    (fun x ↦ ((hV.contMDiff x).neg_section).of_le (by simp))
    (fun x _ t hxt ht ↦ hΦ x t hxt ht)
  refine ⟨⟨F ∘ e ∘ ι, fun p ↦ ((hι p).comp _ _ (e.isLocalDiffeomorph _)).comp _ _ (hgood p).2,
    ?_, ?_⟩⟩
  · intro p q hpq
    have hmem (r : B × normalIioOpens 1) :
        (((e (ι r)).1 : M), (e (ι r)).2.val 0) ∈ W ∩ (𝓡∂ (n + 1)).boundary M ×ˢ Ici 0 :=
      ⟨(hgood r).1, (e (ι r)).1.property, (e (ι r)).2.property⟩
    have h := hΦinj (hmem p) (hmem q) hpq
    have heq : e (ι p) = e (ι q) := Prod.ext (Subtype.ext (congrArg Prod.fst h)) (by
      simpa only [normalRay_normalCoord] using congrArg (fun z : M × ℝ ↦ normalRay z.2) h)
    exact (injective_id.prodMap Subtype.val_injective) (e.injective heq)
  · intro x
    have hz := hW₀ x x.property
    simpa only [comp_apply, F, he, coe_normalIioOpensZero, val_zero_apply,
      mul_zero, normalRay_zero] using (hΦ x 0 hz le_rfl).2.1

end TauCeti
