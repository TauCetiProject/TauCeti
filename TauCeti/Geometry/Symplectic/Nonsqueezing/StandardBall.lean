/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Manifold
public import TauCeti.Geometry.Symplectic.Nonsqueezing.Embedding
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The standard ball of a symplectic embedding into the cylinder

Gromov's nonsqueezing theorem concerns a smooth map `f` from the open ball `B(r) ⊆ ℂⁿ` into the
cylinder `{z ∈ ℂⁿ | |z₀| < R}` which is injective on `B(r)` and whose derivative preserves the
standard symplectic form `ω(v, w) = Im ⟪v, w⟫` at every point of `B(r)`. Its proof composes `f`
with the symplectic embedding `TauCeti.euclideanSphereTorusChart` of a bounded piece of the
cylinder into the closed symplectic manifold `S²(a) × T²ⁿ⁻²`, for `a ≥ π R²`, and needs the result
as a *standard ball* of `S²(a) × T`: a partial diffeomorphism from a ball of `ℂⁿ` pulling the
product form back to `ω`, as in `TauCeti.pi_mul_sq_le_integralTopForm_mpullback`. This file
constructs it.

A map which is `C¹` on an open set `s` and whose derivative preserves `ω` there is a local
diffeomorphism on `s` (`TauCeti.isLocalDiffeomorphOn_of_forall_im_inner_fderiv`). If it is
moreover injective on `s`, it is a partial diffeomorphism from `s` onto its open image
(`IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn`). Following it by the chart of `S²(a) × T`
gives the partial diffeomorphism `TauCeti.symplecticEmbeddingSphereTorusChart`, defined on the
points of `s` which `f` maps into the source of the chart. For `a > 0` it pulls the product form
`a • ω_FS ⊕ ω_T` back to `ω` at every point of its source
(`TauCeti.eval₂_mfderiv_symplecticEmbeddingSphereTorusChart`). Every compact subset `K` of `s`
which `f` maps into the cylinder of radius `R`, with `π R² ≤ a`, lies in its source once the
periods of the torus are large
(`TauCeti.exists_forall_subset_symplecticEmbeddingSphereTorusChart_source`). Applied to the
compact inner balls `K = closedBall 0 r'`, `r' < r`, of a symplectic embedding of `B(r)` into the
cylinder, this is the standard ball `B(r')` of `S²(a) × T` centred at the image of `f 0`.

## Main definitions

* `TauCeti.symplecticEmbeddingSphereTorusChart`: a symplectic embedding of an open set of
  `ℂᵐ⁺¹`, followed by the chart of `S²(a) × T`, as a partial diffeomorphism.

## Main results

* `TauCeti.eval₂_mfderiv_symplecticEmbeddingSphereTorusChart`: for `a > 0` the partial
  diffeomorphism pulls the product form back to `Im ⟪v, w⟫`.
* `TauCeti.exists_forall_subset_symplecticEmbeddingSphereTorusChart_source`: compact pieces of
  the domain mapped into the cylinder lie in its source for large periods.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T²ⁿ⁻²`).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 9.3.
-/

public section

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff InnerProductSpace TauCeti.ComplexManifold

namespace TauCeti

variable {m : ℕ} (a : ℝ) (p : Fin m ⊕ Fin m → ℝ) [∀ i, Fact (0 < p i)]
  {f : EuclideanSpace ℂ (Fin (m + 1)) → EuclideanSpace ℂ (Fin (m + 1))}
  {s : Set (EuclideanSpace ℂ (Fin (m + 1)))}

/-- **A symplectic embedding into the cylinder as a chart of `S²(a) × T`.** Let `f` be smooth and
injective on an open set `s ⊆ ℂᵐ⁺¹`, with derivative preserving `Im ⟪·, ·⟫` at every point of `s`.
This is `f`, as a partial diffeomorphism from `s` onto its image, followed by the symplectic
embedding `TauCeti.euclideanSphereTorusChart a p c hr` of a piece of the cylinder into
`S²(a) × T`. Its source is the set of points of `s` which `f` maps into the source of that chart
(`TauCeti.symplecticEmbeddingSphereTorusChart_source`), and for `a > 0` it pulls the product form
back to `Im ⟪·, ·⟫` (`TauCeti.eval₂_mfderiv_symplecticEmbeddingSphereTorusChart`). -/
def symplecticEmbeddingSphereTorusChart (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    (hinj : InjOn f s)
    (hω : ∀ x ∈ s, ∀ v w, (⟪fderiv ℝ f x v, fderiv ℝ f x w⟫_ℂ).im = (⟪v, w⟫_ℂ).im)
    (c : Fin m → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
      (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
      (EuclideanSpace ℂ (Fin (m + 1))) (OnePoint ℂ × ∀ i, AddCircle (p i)) ∞ :=
  ((isLocalDiffeomorphOn_of_forall_im_inner_fderiv hf hs (by exact_mod_cast le_top)
    hω).partialDiffeomorphOfInjOn hs hinj).trans (euclideanSphereTorusChart a p c hr)

variable {a p} (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s) (hinj : InjOn f s)
  (hω : ∀ x ∈ s, ∀ v w, (⟪fderiv ℝ f x v, fderiv ℝ f x w⟫_ℂ).im = (⟪v, w⟫_ℂ).im)
  (c : Fin m → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i)

/-- The chart is the chart of `S²(a) × T` composed with `f`. -/
@[simp]
theorem coe_symplecticEmbeddingSphereTorusChart :
    ⇑(symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr) =
      euclideanSphereTorusChart a p c hr ∘ f := by
  simp [symplecticEmbeddingSphereTorusChart]

/-- The source of the chart is the set of points of `s` which `f` maps into the source of the
chart of `S²(a) × T`. -/
@[simp]
theorem symplecticEmbeddingSphereTorusChart_source :
    (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr).source =
      s ∩ f ⁻¹' (euclideanSphereTorusChart a p c hr).source := by
  simp [symplecticEmbeddingSphereTorusChart]

/-- The target of the chart is the image under the chart of `S²(a) × T` of the points of `f '' s`
in its source. -/
@[simp]
theorem symplecticEmbeddingSphereTorusChart_target :
    (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr).target =
      euclideanSphereTorusChart a p c hr ''
        (f '' s ∩ (euclideanSphereTorusChart a p c hr).source) := by
  rw [← (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr).image_source_eq_target,
    symplecticEmbeddingSphereTorusChart_source, ← image_inter_preimage, ← image_comp]
  exact congrArg (· '' _) (coe_symplecticEmbeddingSphereTorusChart hf hs hinj hω c hr)

/-- The inverse of the chart is the inverse of `f` on `s` after the inverse of the chart of
`S²(a) × T`. -/
@[simp]
theorem coe_symplecticEmbeddingSphereTorusChart_symm :
    ⇑(symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr).toPartialEquiv.symm =
      invFunOn f s ∘ (euclideanSphereTorusChart a p c hr).toPartialEquiv.symm := by
  exact (PartialDiffeomorph.coe_trans_symm _ _).trans <| congrArg (· ∘ _)
    (funext (IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_symm_apply _ hs hinj))

/-- **The chart is symplectic.** For `a > 0`, at every point of its source the chart pulls the
product form `a • ω_FS ⊕ ω_T` of `S²(a) × T` back to the standard symplectic form `Im ⟪v, w⟫` of
`ℂᵐ⁺¹`. -/
theorem eval₂_mfderiv_symplecticEmbeddingSphereTorusChart (ha : 0 < a)
    {x : EuclideanSpace ℂ (Fin (m + 1))}
    (hx : x ∈ (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr).source)
    (v w : EuclideanSpace ℂ (Fin (m + 1))) :
    ((a • OnePoint.fubiniStudyForm).prod (torusSymplecticForm p)).eval₂
        (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr) x w) =
      (⟪v, w⟫_ℂ).im := by
  rw [symplecticEmbeddingSphereTorusChart_source] at hx
  obtain ⟨hxs, hfx⟩ := hx
  have hdf : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hxs)
  -- The chain rule through `f`, whose manifold derivative is its derivative.
  have hcomp (u : EuclideanSpace ℂ (Fin (m + 1))) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω c hr) x u =
        mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (euclideanSphereTorusChart a p c hr) (f x) (fderiv ℝ f x u) := by
    rw [coe_symplecticEmbeddingSphereTorusChart,
      mfderiv_comp x ((euclideanSphereTorusChart a p c hr).mdifferentiableAt (by simp) hfx)
        hdf.mdifferentiableAt, mfderiv_eq_fderiv]
    -- `rw` cannot use this lemma: the tangent spaces of `ℂᵐ⁺¹` as a manifold and as the model
    -- space are only definitionally equal.
    exact ContinuousLinearMap.comp_apply _ _ _
  rw [hcomp, hcomp, coe_symplecticEmbeddingSphereTorusChart, comp_apply,
    eval₂_mfderiv_euclideanSphereTorusChart c hr ha hfx, hω x hxs]

/-- **Compact pieces mapped into the cylinder lie in the source for large periods.** If `K ⊆ s`
is compact and `|f(x) 0| < R` for every `x ∈ K`, with `π R² ≤ a`, then there is a radius `ρ` such
that `K` lies in the source of `TauCeti.symplecticEmbeddingSphereTorusChart a p hf hs hinj hω 0 hρ`
for all periods `p i ≥ 2 ρ`. -/
theorem exists_forall_subset_symplecticEmbeddingSphereTorusChart_source
    {K : Set (EuclideanSpace ℂ (Fin (m + 1)))} (hK : IsCompact K) (hKs : K ⊆ s) {R : ℝ}
    (hR : Real.pi * R ^ 2 ≤ a) (hKR : ∀ x ∈ K, ‖f x 0‖ < R) :
    ∃ ρ : ℝ, ∀ (p : Fin m ⊕ Fin m → ℝ) [∀ i, Fact (0 < p i)] (hρ : ∀ i, 2 * ρ ≤ p i),
      K ⊆ (symplecticEmbeddingSphereTorusChart a p hf hs hinj hω 0 hρ).source := by
  obtain ⟨ρ, hρ⟩ := exists_forall_subset_euclideanSphereTorusChart_source
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded hR
    (forall_mem_image.2 hKR)
  refine ⟨ρ, fun p _ hp x hx ↦ ?_⟩
  rw [symplecticEmbeddingSphereTorusChart_source]
  exact ⟨hKs hx, hρ p hp (mem_image_of_mem f hx)⟩

end TauCeti
