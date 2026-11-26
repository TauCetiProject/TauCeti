/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Manifold.Flow.NormedSpace
public import TauCeti.Geometry.Manifold.IntegralCurve.Prod
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Symplectic.Liouville.Completion
public import TauCeti.Geometry.Symplectic.Liouville.Flow.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Manifold.Gluing

/-!
# The completion of a Liouville domain glued along its Liouville collar

Let `X` be a manifold, to be thought of as the interior of a compact manifold with boundary `W`,
with a one-form `α` whose exterior derivative is nondegenerate, and let `S` be a manifold, to be
thought of as `∂W`, with a one-form `β`. A **Liouville collar** is a partial diffeomorphism
`Φ : ℝ × S ⇀ X` with source `(-∞, 0) × S` that pulls `α` back to the symplectization form
`eᵗ β` (`TauCeti.SmoothForm.symplectization`). For a Liouville domain `W` it is
`(t, s) ↦ φ_t(s)`, the backward flow of the Liouville field from the boundary, in the coordinate
`t = log r` of the radial coordinate `r`.

Gluing `X` and the cylinder `ℝ × S` along `Φ` (`OpenPartialHomeomorph.glueData`) continues the
collar coordinate `t` to all of `ℝ`, and gives the manifold `M = W ∪ ([0, ∞) × S)`
(`OpenPartialHomeomorph.bijOn_glueInr_compl_source`). The forms `α` and `eᵗ β` glue to a smooth
one-form `α̂` on `M` (`PartialDiffeomorph.glueForm`), which is `r β` on the end in the radial
coordinate `r = eᵗ`. This file proves that `M` is the completion of the copy of `W` in it,
the complement of the open end `(0, ∞) × S`
(`PartialDiffeomorph.isLiouvilleCompletion_glueForm`), as soon as `S` is compact, `M` is
Hausdorff, and the part of `X` outside a collar `(c, 0) × S` is compact.

The boundary form `β` of a Liouville collar is automatically a contact form, since `d(eᵗ β)` is the
pullback of the nondegenerate form `dα`
(`PartialDiffeomorph.isContactForm_of_mpullback_eq_symplectization`), so the glued form `dα̂` is
nondegenerate (`PartialDiffeomorph.isNondegenerate_mextDerivₗ_glueForm`).

On the end, the Liouville field of `α̂`, the vector field `Z` with `ι_Z dα̂ = α̂`, is the unit
field `∂_t` (`PartialDiffeomorph.mfderiv_glueInr_apply_prodVectorField`), whose integral curves
are the lines `τ ↦ (t + τ, s)` (`PartialDiffeomorph.isMIntegralCurve_glueInr`). So the Liouville
flow on the end is translation of the collar coordinate (`PartialDiffeomorph.flowOf_glueInr`), and
a trajectory of `Z` that never meets the end stays in the compact complement of the cylinder.
Hence `Z` is complete (`PartialDiffeomorph.isCompleteVectorField_of_interior_glueForm`), and
carries every point into `W`. The function equal to `max t c` on the cylinder and to `c` elsewhere
is continuous on `M`, has the domain as its sublevel set `{≤ 0}`, and is the collar coordinate
near its level `0`, along which `Z` increases it at unit rate: so `Z` points strictly outwards
along the boundary `{0} × S`.

## Main results

* `PartialDiffeomorph.isContactForm_of_mpullback_eq_symplectization`: the boundary form of a
  Liouville collar is a contact form.
* `PartialDiffeomorph.isNondegenerate_mextDerivₗ_glueForm`: the glued two-form is nondegenerate.
* `PartialDiffeomorph.mfderiv_glueInr_apply_prodVectorField`: on the end, the Liouville field of
  the glued primitive is `∂_t`.
* `PartialDiffeomorph.isMIntegralCurve_glueInr`, `PartialDiffeomorph.flowOf_glueInr`: the
  Liouville flow on the end translates the collar coordinate.
* `PartialDiffeomorph.isCompleteVectorField_of_interior_glueForm`: the Liouville field of the
  glued primitive is complete.
* `PartialDiffeomorph.isLiouvilleCompletion_glueForm`: the glued manifold is a completion of the
  Liouville domain it contains.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (Liouville domains and their completions).
-/

public section

open Function Set TauCeti OpenPartialHomeomorph Manifold Filter
open scoped Manifold ContDiff Topology

namespace PartialDiffeomorph

universe u

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  {S X : Type u} [TopologicalSpace S] [ChartedSpace G S]
  [TopologicalSpace X] [ChartedSpace (ModelProd ℝ G) X]
  {Φ : PartialDiffeomorph (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (ℝ × S) X ∞}

/-! ### The domain inside the glued manifold -/

/-- The image of the end `(0, ∞) × S` of the cylinder is open in the glued manifold. -/
private theorem isOpen_image_glueInr_Ioi :
    IsOpen (Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ioi (0 : ℝ))) :=
  (isOpenEmbedding_glueInr _).isOpenMap _ (isOpen_Ioi.preimage continuous_fst)

/-- The complement of the open end `(0, ∞) × S` in the glued manifold is compact, when `S` is
compact and the part of `X` outside the collar `(c, 0) × S` is compact. -/
private theorem isCompact_compl_image_glueInr_Ioi [CompactSpace S]
    (hsource : Φ.source = Prod.fst ⁻¹' Iio 0) {c : ℝ} (hc : c < 0)
    (hK : IsCompact (Φ '' (Prod.fst ⁻¹' Ioo c 0))ᶜ) :
    IsCompact (Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ioi 0))ᶜ := by
  refine ((hK.image Φ.toOpenPartialHomeomorph.glueInl.continuous).union
    (((isCompact_Icc (a := c) (b := 0)).prod (isCompact_univ (X := S))).image
      Φ.toOpenPartialHomeomorph.glueInr.continuous)).of_isClosed_subset
    isOpen_image_glueInr_Ioi.isClosed_compl fun p hp ↦ ?_
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := exists_glueInl_eq_or_exists_glueInr_eq _ p
  · by_cases hx : x ∈ Φ '' (Prod.fst ⁻¹' Ioo c 0)
    · obtain ⟨y, hy, rfl⟩ := hx
      have hys : y ∈ Φ.source := by rw [hsource]; exact hy.2
      refine Or.inr ⟨y, ⟨⟨hy.1.le, hy.2.le⟩, mem_univ _⟩, ?_⟩
      exact (glueInl_apply_eq_glueInr hys).symm
    · exact Or.inl ⟨x, hx, rfl⟩
  · have hy0 : y.1 ≤ 0 := not_lt.1 fun h ↦ hp ⟨y, h, rfl⟩
    by_cases hyc : c ≤ y.1
    · exact Or.inr ⟨y, ⟨⟨hyc, hy0⟩, mem_univ _⟩, rfl⟩
    · -- Below the collar `(c, 0) × S`, the point lies in the image of `X`.
      have hys : y ∈ Φ.source := by
        rw [hsource]
        exact (lt_of_not_ge hyc).trans hc
      refine Or.inl ⟨Φ y, fun ⟨y', hy', hyy'⟩ ↦ hyc ?_, glueInl_apply_eq_glueInr hys⟩
      have hy's : y' ∈ Φ.source := by rw [hsource]; exact hy'.2
      rw [Φ.injOn hy's hys hyy'] at hy'
      exact hy'.1.le

/-- The function equal to `max t c` on the cylinder `ℝ × S` and to `c` on the rest of the glued
manifold is continuous, for `c ≤ 0`: it is constant outside the image of the closed half-cylinder
`[c, ∞) × S`. -/
private theorem continuous_extend_glueInr [CompactSpace S]
    [T2Space Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
    (hsource : Φ.source = Prod.fst ⁻¹' Iio 0) {c : ℝ} (hc : c ≤ 0) :
    Continuous (extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c)
      fun _ ↦ c) := by
  have hinj := (isOpenEmbedding_glueInr Φ.toOpenPartialHomeomorph).injective
  -- The image of the half-cylinder `[c, ∞) × S` is closed: it is the compact image of
  -- `[c, 0] × S` together with the complement of the image of `X`.
  have hC : IsClosed (Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ici c)) := by
    have h : (Prod.fst ⁻¹' Ici c : Set (ℝ × S)) =
        Icc c 0 ×ˢ univ ∪ Φ.toOpenPartialHomeomorph.sourceᶜ := by
      ext y
      simp only [toOpenPartialHomeomorph_source, hsource]
      grind
    rw [h, image_union, ← compl_range_glueInl]
    exact ((isCompact_Icc.prod isCompact_univ).image
      Φ.toOpenPartialHomeomorph.glueInr.continuous).isClosed.union
        (isOpenEmbedding_glueInl _).isOpen_range.isClosed_compl
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  by_cases hp : ∃ y, Φ.toOpenPartialHomeomorph.glueInr y = p
  · obtain ⟨y, rfl⟩ := hp
    rw [← (isOpenEmbedding_glueInr _).continuousAt_iff, extend_comp hinj]
    exact (continuous_fst.max continuous_const).continuousAt
  · have hpC : p ∉ Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ici c) :=
      fun ⟨y, _, hy⟩ ↦ hp ⟨y, hy⟩
    refine (continuousAt_const (y := c)).congr ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hpC] with q hq
    by_cases hq' : ∃ y, Φ.toOpenPartialHomeomorph.glueInr y = q
    · obtain ⟨y, rfl⟩ := hq'
      rw [hinj.extend_apply]
      exact (max_eq_right (not_le.1 fun h ↦ hq ⟨y, h, rfl⟩).le).symm
    · rw [extend_apply' _ _ _ hq']

/-- The collar may be shrunk to one of negative depth: if the part of `X` outside the image of
`(c, 0) × S` is compact, so is the part outside the image of `(c', 0) × S` for some `c' < 0`, a
closed subset of it. -/
private theorem exists_neg_isCompact_compl_image (hsource : Φ.source = Prod.fst ⁻¹' Iio 0)
    {c : ℝ} (hK : IsCompact (Φ '' (Prod.fst ⁻¹' Ioo c 0))ᶜ) :
    ∃ c' < 0, IsCompact (Φ '' (Prod.fst ⁻¹' Ioo c' 0))ᶜ := by
  refine ⟨min c (-1), (min_le_right _ _).trans_lt (by norm_num), hK.of_isClosed_subset ?_
    (compl_subset_compl.2 (image_mono (preimage_mono (Ioo_subset_Ioo_left
      (min_le_left _ _)))))⟩
  have hsub : (Prod.fst ⁻¹' Ioo (min c (-1)) 0 : Set (ℝ × S)) =
      Φ.toOpenPartialHomeomorph.source ∩ Prod.fst ⁻¹' Ioo (min c (-1)) 0 := by
    rw [toOpenPartialHomeomorph_source, hsource, ← preimage_inter, Iio_inter_Ioo, min_self]
  rw [hsub]
  exact (Φ.toOpenPartialHomeomorph.isOpen_image_source_inter
    (isOpen_Ioo.preimage continuous_fst)).isClosed_compl

/-- For `c ≤ 0`, the complement of the open end `(0, ∞) × S` is the sublevel set `{f ≤ 0}` of the
function `f` equal to `max t c` on the cylinder and to `c` elsewhere. -/
private theorem compl_image_glueInr_Ioi_eq_setOf_extend_le {c : ℝ} (hc : c ≤ 0) :
    (Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ioi 0))ᶜ =
      {p | extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c) (fun _ ↦ c) p ≤
        0} := by
  have hinj := (isOpenEmbedding_glueInr Φ.toOpenPartialHomeomorph).injective
  ext p
  simp only [mem_compl_iff, mem_ofPred_eq]
  by_cases hp : ∃ y, Φ.toOpenPartialHomeomorph.glueInr y = p
  · obtain ⟨y, rfl⟩ := hp
    rw [hinj.extend_apply, hinj.mem_set_image, mem_preimage, mem_Ioi, not_lt, max_le_iff]
    exact (and_iff_left hc).symm
  · rw [extend_apply' _ _ _ hp]
    exact iff_of_true (fun ⟨y, _, hy⟩ ↦ hp ⟨y, hy⟩) hc

variable [IsManifold J ∞ S] [IsManifold (𝓘(ℝ).prod J) ∞ X]
  {α : SmoothForm (𝓘(ℝ).prod J) X ℝ 1} {β : SmoothForm J S ℝ 1}

/-! ### The Liouville collar -/

/-- **The boundary form of a Liouville collar is a contact form.** If `Φ` pulls `α` back to the
symplectization form `eᵗ β` on its source, `dα` is nondegenerate, and the source meets every line
`ℝ × {s}`, then `β` is a contact form: at a point of the source, `d(eᵗ β)` is the pullback of the
nondegenerate form `dα` along a local diffeomorphism. -/
theorem isContactForm_of_mpullback_eq_symplectization
    (hα : SmoothTwoForm.IsNondegenerate (mextDerivₗ (𝓘(ℝ).prod J) 1 α))
    (hαβ : ∀ y ∈ Φ.source,
      mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ α.val y = β.symplectization.val y)
    (hs : ∀ s : S, ∃ t : ℝ, (t, s) ∈ Φ.source) : β.IsContactForm := by
  rw [SmoothForm.isContactForm_iff_forall_isContactFormAt]
  intro s
  obtain ⟨t, ht⟩ := hs s
  rw [← SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_symplectization_iff β (t, s),
    LinearMap.BilinForm.Nondegenerate,
    (SmoothForm.isAlt_bilinFormAt _ (t, s)).isRefl.nondegenerate_iff_separatingLeft]
  intro v hv
  have hinv := Φ.isInvertible_mfderiv (by simp) ht
  refine (injective_iff_map_eq_zero _).1 hinv.injective v
    (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hα (Φ (t, s)) _ fun w ↦ ?_)
  obtain ⟨u, rfl⟩ := hinv.surjective w
  -- `dα(dΦ v, dΦ u) = (Φ^* dα)(v, u) = d(eᵗ β)(v, u) = 0`.
  have hvu : (fun i ↦ mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ (t, s) (![v, u] i)) =
      ![mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ (t, s) v,
        mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ (t, s) u] := by
    ext i
    fin_cases i <;> rfl
  have h := hv u
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    ← Φ.mpullback_mextDerivₗ_apply hαβ ht, mpullback_apply, hvu] at h
  rwa [SmoothBundleForm.eval₂_apply]

variable [ChartedSpace (ModelProd ℝ G) Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
  [IsManifold (𝓘(ℝ).prod J) ∞ Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
  {hl : IsLocalDiffeomorph (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) ∞ Φ.toOpenPartialHomeomorph.glueInl}
  {hr : IsLocalDiffeomorph (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) ∞ Φ.toOpenPartialHomeomorph.glueInr}
  {hαβ : ∀ y ∈ Φ.source,
    mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ α.val y = β.symplectization.val y}
  {Z : (p : Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued) →
    TangentSpace (𝓘(ℝ).prod J) p}

/-! ### The Liouville field on the end -/

/-- **On the end, the Liouville field of the glued primitive is `∂_t`.** If the exterior
derivative of the glued primitive `α̂` is nondegenerate and `ι_Z dα̂ = α̂`, then the canonical map
of the cylinder `ℝ × S` carries the unit field `∂_t` along `ℝ` to `Z`: the symplectization form
`eᵗ β` has Liouville field `∂_t`. -/
theorem mfderiv_glueInr_apply_prodVectorField
    (hω : SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)))
    (hZ : RoughForm.interior Z
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)).val =
        (Φ.glueForm hl hr α β.symplectization hαβ).val)
    (y : ℝ × S) :
    mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) Φ.toOpenPartialHomeomorph.glueInr y
        (prodVectorField (constVectorField (1 : ℝ)) (0 : (s : S) → TangentSpace J s) y) =
      Z (Φ.toOpenPartialHomeomorph.glueInr y) := by
  refine hr.mfderiv_apply_eq_of_interior_eq (σ := mextDerivₗ (𝓘(ℝ).prod J) 1 β.symplectization)
    (α := β.symplectization.val) hω ?_ ?_ ?_ hZ y
  · rw [← SmoothForm.mextDerivₗ_mpullback _ hr.contMDiff, mpullback_glueInr_glueForm]
  · rw [← SmoothForm.coe_mpullback _ hr.contMDiff, mpullback_glueInr_glueForm]
  · rw [mextDerivₗ_apply]
    exact SmoothForm.interior_mextDeriv_symplectization β

/-- **The integral curves of the Liouville field on the end** are the lines `τ ↦ (t + τ, s)` of
the cylinder, read in the glued manifold. -/
theorem isMIntegralCurve_glueInr
    (hω : SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)))
    (hZ : RoughForm.interior Z
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)).val =
        (Φ.glueForm hl hr α β.symplectization hαβ).val)
    (y : ℝ × S) :
    IsMIntegralCurve (fun τ ↦ Φ.toOpenPartialHomeomorph.glueInr (y.1 + τ, y.2)) Z := by
  have hline : IsMIntegralCurve (fun τ : ℝ ↦ ((y.1 + τ, y.2) : ℝ × S))
      (prodVectorField (constVectorField (1 : ℝ)) (0 : (s : S) → TangentSpace J s)) := by
    refine isMIntegralCurve_prodVectorField_iff.2 ⟨?_, isMIntegralCurve_const rfl⟩
    rw [constVectorField_eq]
    simpa only [smul_eq_mul, mul_one] using isMIntegralCurve_translation (1 : ℝ) y.1
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hline ⊢
  exact hline.map_of_mfderiv_eq (fun _ _ ↦ (hr _).mdifferentiableAt (by simp))
    fun τ _ ↦ mfderiv_glueInr_apply_prodVectorField hω hZ _

/-- **The glued symplectic form is nondegenerate**: `dα̂` restricts to the nondegenerate `dα` on
`X` and to `d(eᵗ β)` on the cylinder, which is nondegenerate since `β` is a contact form
(`PartialDiffeomorph.isContactForm_of_mpullback_eq_symplectization`). -/
theorem isNondegenerate_mextDerivₗ_glueForm
    (hα : SmoothTwoForm.IsNondegenerate (mextDerivₗ (𝓘(ℝ).prod J) 1 α))
    (hs : ∀ s : S, ∃ t : ℝ, (t, s) ∈ Φ.source) :
    SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)) := by
  rw [mextDerivₗ_glueForm, isNondegenerate_glueForm_iff]
  exact ⟨hα, SmoothForm.isNondegenerate_mextDerivₗ_symplectization_iff.2
    (isContactForm_of_mpullback_eq_symplectization hα hαβ hs)⟩

/-- Near a point `(t, s)` of the cylinder with `t > c`, the function equal to `max t c` on the
cylinder and to `c` elsewhere is the collar coordinate `t`: it is smooth there, and the Liouville
field increases it at unit rate. -/
private theorem contMDiffAt_extend_glueInr_and_mvfderiv
    (hω : SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)))
    (hZ : RoughForm.interior Z
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)).val =
        (Φ.glueForm hl hr α β.symplectization hαβ).val)
    {c : ℝ} {y : ℝ × S} (hy : c < y.1) :
    ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ) ∞
        (extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c) fun _ ↦ c)
        (Φ.toOpenPartialHomeomorph.glueInr y) ∧
      mvfderiv (𝓘(ℝ).prod J)
        (extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c) fun _ ↦ c)
        (Φ.toOpenPartialHomeomorph.glueInr y) (Z (Φ.toOpenPartialHomeomorph.glueInr y)) = 1 := by
  have hinj := (isOpenEmbedding_glueInr Φ.toOpenPartialHomeomorph).injective
  -- Near `y`, the composite of `f` with the canonical map of the cylinder is the coordinate `t`.
  have heq : extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c) (fun _ ↦ c) ∘
      Φ.toOpenPartialHomeomorph.glueInr =ᶠ[𝓝 y] Prod.fst := by
    filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds
      (hy : y ∈ Prod.fst ⁻¹' Ioi c)] with y' hy'
    rw [comp_apply, hinj.extend_apply]
    exact max_eq_left (le_of_lt hy')
  have hcomp : ContMDiffAt (𝓘(ℝ).prod J) 𝓘(ℝ) ∞
      (extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c) (fun _ ↦ c) ∘
        Φ.toOpenPartialHomeomorph.glueInr) y :=
    contMDiffAt_fst.congr_of_eventuallyEq heq
  have hf := ((hr y).contMDiffAt_comp_iff le_rfl).1 hcomp
  refine ⟨hf, ?_⟩
  rw [← mfderiv_glueInr_apply_prodVectorField hω hZ y, ← mvfderiv_comp_apply y
    (hf.mdifferentiableAt (by simp)) ((hr y).mdifferentiableAt (by simp)), heq.mvfderiv_eq,
    mvfderiv_apply_eq_mfderiv_apply]
  have h₁ := congrArg (fun L ↦ L
      (prodVectorField (constVectorField (1 : ℝ)) (0 : (s : S) → TangentSpace J s) y))
    (mfderiv_fst (x := y) : mfderiv (𝓘(ℝ).prod J) 𝓘(ℝ) Prod.fst y = _)
  rw [h₁]
  -- The tangent space of `ℝ × S` is a product only up to unfolding `TangentSpace`, so
  -- `ContinuousLinearMap.coe_fst'` does not rewrite here; the projection `fst v = v.1` holds by
  -- unfolding, and `prodVectorField_fst` computes `v.1`.
  exact (prodVectorField_fst _ _ y).trans (congrFun (constVectorField_eq (1 : ℝ)) y.1)

variable [T2Space Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued] [J.Boundaryless]

/-- **The Liouville flow on the end translates the collar coordinate**:
`φ_τ (t, s) = (t + τ, s)` on the cylinder `ℝ × S`, read in the glued manifold. -/
theorem flowOf_glueInr
    (hω : SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)))
    (hZ : RoughForm.interior Z
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)).val =
        (Φ.glueForm hl hr α β.symplectization hαβ).val)
    (hZs : ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod J).tangent 1 (T% Z)) (y : ℝ × S) (τ : ℝ) :
    flowOf Z τ (Φ.toOpenPartialHomeomorph.glueInr y) =
      Φ.toOpenPartialHomeomorph.glueInr (y.1 + τ, y.2) := by
  have h := flowOf_eq_of_isMIntegralCurve hZs (isMIntegralCurve_glueInr hω hZ y) τ
  simpa only [add_zero] using h

/-! ### Completeness of the Liouville field -/

/-- **The Liouville field of the glued primitive is complete**, when the part of `X` outside the
image of the collar is compact. On the end its trajectories are the lines `τ ↦ (t + τ, s)`. A
trajectory through any other point never meets the cylinder, since it would then be one of these
lines, so it stays in the compact complement of the cylinder and is defined for all time. -/
theorem isCompleteVectorField_of_interior_glueForm [CompleteSpace F]
    (hω : SmoothTwoForm.IsNondegenerate
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)))
    (hZ : RoughForm.interior Z
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ)).val =
        (Φ.glueForm hl hr α β.symplectization hαβ).val)
    (hZs : ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod J).tangent 1 (T% Z))
    (hK : IsCompact Φ.targetᶜ) : IsCompleteVectorField Z := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  intro p
  by_cases hp : p ∈ range Φ.toOpenPartialHomeomorph.glueInr
  · obtain ⟨y, rfl⟩ := hp
    exact (isMIntegralCurve_glueInr hω hZ y).maximalIntegralCurveInterval_eq_univ (by simp)
  -- The trajectory through `p` stays outside the cylinder: a point `φ_τ p` on the cylinder would
  -- flow back to `p = φ_{-τ}(φ_τ p)` along a line of the cylinder.
  have hKc : IsCompact (range Φ.toOpenPartialHomeomorph.glueInr)ᶜ := by
    rw [compl_range_glueInr]
    exact hK.image Φ.toOpenPartialHomeomorph.glueInl.continuous
  refine maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hZs hKc
    fun τ hτ hmem ↦ hp ?_
  obtain ⟨y, hy⟩ := hmem
  have hτ' : (τ, p) ∈ flowDomain Z := mem_flowDomain.2 hτ
  have hτy : flowOf Z τ p = Φ.toOpenPartialHomeomorph.glueInr y := by
    rw [flowOf_apply]
    exact hy.symm
  rw [← flowOf_neg_flowOf hZs hτ', hτy, flowOf_glueInr hω hZ hZs]
  exact mem_range_self _

/-! ### The Liouville domain and its completion -/

/-- **The completion of a Liouville domain glued along its Liouville collar.** Let `Φ` be a
partial diffeomorphism from the cylinder `ℝ × S` to `X`, with source `(-∞, 0) × S`, pulling the
one-form `α` back to the symplectization form `eᵗ β`, where `dα` is nondegenerate, so that `β` is
a contact form (`PartialDiffeomorph.isContactForm_of_mpullback_eq_symplectization`). If `S` is
compact, the part of `X` outside the collar `(c, 0) × S` is compact for some `c`, and the gluing
`M` of `X` and `ℝ × S` along `Φ` is Hausdorff, then `M`, with the glued primitive `α̂` of `α` and
`eᵗ β`, is a completion of the complement of the open end `(0, ∞) × S` in `M`: this complement is
a Liouville domain for `dα̂` with primitive `α̂`, the Liouville field of `α̂` is complete, and its
flow carries every point into the domain. -/
theorem isLiouvilleCompletion_glueForm [FiniteDimensional ℝ F] [CompactSpace S]
    (hsource : Φ.source = Prod.fst ⁻¹' Iio 0)
    (hα : SmoothTwoForm.IsNondegenerate (mextDerivₗ (𝓘(ℝ).prod J) 1 α)) {c : ℝ}
    (hK : IsCompact (Φ '' (Prod.fst ⁻¹' Ioo c 0))ᶜ) :
    IsLiouvilleCompletion
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (Φ.glueForm hl hr α β.symplectization hαβ))
      (Φ.glueForm hl hr α β.symplectization hαβ)
      (Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ioi 0))ᶜ := by
  have hinj := (isOpenEmbedding_glueInr Φ.toOpenPartialHomeomorph).injective
  have hω := isNondegenerate_mextDerivₗ_glueForm (hl := hl) (hr := hr) (hαβ := hαβ) hα
    fun s ↦ ⟨-1, by rw [hsource]; exact neg_one_lt_zero⟩
  obtain ⟨c', hc', hK'⟩ := exists_neg_isCompact_compl_image hsource hK
  have hcompl : IsCompact Φ.targetᶜ := by
    refine hK'.of_isClosed_subset Φ.open_target.isClosed_compl (compl_subset_compl.2 ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact Φ.map_source (by rw [hsource]; exact hy.2)
  set Z := ⇑(hω.interiorEquiv.symm (Φ.glueForm hl hr α β.symplectization hαβ))
  have hZ := hω.interior_interiorEquiv_symm (Φ.glueForm hl hr α β.symplectization hαβ)
  have hZs : ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod J).tangent ∞ (T% Z) :=
    (hω.interiorEquiv.symm (Φ.glueForm hl hr α β.symplectization hαβ)).contMDiff
  refine
    { isNondegenerate := hω
      mextDeriv_eq := (mextDerivₗ_apply _ _ _).symm
      isCompact := isCompact_compl_image_glueInr_Ioi hsource hc' hK'
      subset_interior := by simp [ModelWithCorners.interior_eq_univ]
      exists_liouville_outward := ⟨Z, hZs, hZ,
        extend Φ.toOpenPartialHomeomorph.glueInr (fun y : ℝ × S ↦ max y.1 c') (fun _ ↦ c'), 0,
        continuous_extend_glueInr hsource hc'.le, compl_image_glueInr_Ioi_eq_setOf_extend_le hc'.le,
        ?_⟩
      exists_isCompleteVectorField := ⟨Z, hZ,
        isCompleteVectorField_of_interior_glueForm hω hZ (hZs.of_le (by simp)) hcompl, ?_⟩ }
  · -- Along the level `{f = 0}`, the boundary `{0} × S`, `f` is the collar coordinate.
    intro p hp
    by_cases hq : ∃ y, Φ.toOpenPartialHomeomorph.glueInr y = p
    · obtain ⟨y, rfl⟩ := hq
      rw [hinj.extend_apply] at hp
      have hy : c' < y.1 := lt_of_not_ge fun h ↦ hc'.ne (by rwa [max_eq_right h] at hp)
      obtain ⟨h₁, h₂⟩ := contMDiffAt_extend_glueInr_and_mvfderiv hω hZ hy
      exact ⟨h₁, h₂ ▸ one_pos⟩
    · rw [extend_apply' _ _ _ hq] at hp
      exact absurd hp hc'.ne
  · -- A point `(t, s)` of the open end flows back to the boundary point `(0, s)` in time `-t`.
    intro p
    by_cases hp : p ∈ Φ.toOpenPartialHomeomorph.glueInr '' (Prod.fst ⁻¹' Ioi 0)
    · obtain ⟨y, -, rfl⟩ := hp
      refine ⟨-y.1, ?_⟩
      rw [flowOf_glueInr hω hZ (hZs.of_le (by simp)), add_neg_cancel, mem_compl_iff,
        hinj.mem_set_image, mem_preimage, mem_Ioi]
      exact lt_irrefl 0
    · exact ⟨0, by rwa [flowOf_zero]⟩

end PartialDiffeomorph
