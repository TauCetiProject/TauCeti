/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Smul
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Star-convex shrinking and radial rescaling in a vector bundle

The radial core of a subset of a real vector bundle consists of those vectors whose whole
segment from zero lies in the subset. It is the largest fibrewise star-convex subset, and
it is open when the original subset is open. Thus every open neighbourhood of the zero
section contains an open fibrewise star-convex neighbourhood of that section, without any
metric, finite-dimensionality, or compactness assumption on the base or fibres.

This shrinking turns an arbitrary domain of injective tubular coordinates into a domain
preserved by radial contraction. Openness uses the closed projection from a product with
the compact interval, and joint continuity of fibrewise scalar multiplication.

In addition, for any continuous bundle isomorphism `Φ : E₁ ≃ E₂` between finite-rank real vector
bundles with continuous fibre norms, radial rescaling `v ↦ (‖v‖₁ / ‖Φ v‖₂) • Φ v` defines a
fibrewise norm-preserving homeomorphism `TauCeti.radialBundleHomeomorph` between the total
spaces (`TauCeti.radialBundleMap`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24,
  for star-convex domains in tubular neighbourhoods.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (radial rescaling).
-/

public section

open Bundle Set Topology

namespace TauCeti.VectorBundle

variable {B F : Type*} {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]

/-- The vectors whose radial segment from the zero vector stays in `U`. -/
def radialCore (U : Set (TotalSpace F E)) : Set (TotalSpace F E) :=
  {p | ∀ t ∈ Icc (0 : ℝ) 1, (⟨p.proj, t • p.snd⟩ : TotalSpace F E) ∈ U}

/-- Membership in the radial core is tested along the whole closed radial segment. -/
theorem mem_radialCore {U : Set (TotalSpace F E)} {p : TotalSpace F E} :
    p ∈ radialCore U ↔
      ∀ t ∈ Icc (0 : ℝ) 1, (⟨p.proj, t • p.snd⟩ : TotalSpace F E) ∈ U := Iff.rfl

/-- The radial core is contained in the original set. -/
theorem radialCore_subset (U : Set (TotalSpace F E)) : radialCore U ⊆ U := by
  intro p hp
  simpa using hp 1 ⟨zero_le_one, le_rfl⟩

/-- Enlarging a set enlarges its radial core. -/
theorem radialCore_mono {U W : Set (TotalSpace F E)} (h : U ⊆ W) :
    radialCore U ⊆ radialCore W := fun _ hp t ht => h (hp t ht)

/-- Taking the radial core preserves exactly the zero vectors in the original set. -/
@[simp] theorem zeroSection_mem_radialCore {U : Set (TotalSpace F E)} (x : B) :
    zeroSection F E x ∈ radialCore U ↔ zeroSection F E x ∈ U := by
  constructor
  · intro hx
    exact radialCore_subset U hx
  · intro hx t _
    have ht0 : t • (0 : E x) = 0 := smul_zero t
    exact (congrArg (fun v : E x => (⟨x, v⟩ : TotalSpace F E) ∈ U) ht0).mpr hx

/-- Every fibre slice of the radial core is star-convex at zero. -/
theorem starConvex_radialCore (U : Set (TotalSpace F E)) (x : B) :
    StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ radialCore U} := by
  intro v hv a b ha hb hab
  simp only [smul_zero, zero_add, mem_ofPred_eq, mem_radialCore]
  intro t ht
  simpa only [smul_smul] using hv (t * b) ⟨mul_nonneg ht.1 hb, by nlinarith [ht.2]⟩

/-- A fibrewise star-convex subset of `U` lies in its radial core. This characterizes the
radial core as the largest such subset. -/
theorem subset_radialCore {U W : Set (TotalSpace F E)} (hWU : W ⊆ U)
    (hW : ∀ x, StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ W}) :
    W ⊆ radialCore U := by
  intro p hp t ht
  exact hWU ((hW p.proj).smul_mem hp ht.1 ht.2)

/-- Taking the radial core leaves a fibrewise star-convex set unchanged. -/
theorem radialCore_eq_self {U : Set (TotalSpace F E)}
    (hU : ∀ x, StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ U}) :
    radialCore U = U :=
  subset_antisymm (radialCore_subset U) (subset_radialCore Subset.rfl hU)

section Topology

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The radial core of an open set is open. Compactness of the scalar interval gives one
neighbourhood on which all the radial segments remain in the original set. -/
theorem isOpen_radialCore {U : Set (TotalSpace F E)} (hU : IsOpen U) :
    IsOpen (radialCore U) := by
  let R : Icc (0 : ℝ) 1 × TotalSpace F E → TotalSpace F E :=
    fun p => ⟨p.2.proj, (p.1 : ℝ) • p.2.snd⟩
  have hR : Continuous R :=
    (continuous_subtypeVal.comp continuous_fst).smul_totalSpace continuous_snd
  have hclosed : IsClosed (Prod.snd '' (R ⁻¹' Uᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hU.isClosed_compl.preimage hR)
  convert hclosed.isOpen_compl using 1
  ext p
  simp only [mem_compl_iff, mem_image, mem_preimage, Prod.exists, R, mem_radialCore]
  simp

end Topology

end TauCeti.VectorBundle

namespace TauCeti

noncomputable section RadialMetricChange

open Filter Metric

section Algebraic

variable {B : Type*} (F₁ F₂ : Type*) {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]

/-- Radial rescaling of a family of fibrewise linear equivalences `Φ b : E₁ b ≃L[ℝ] E₂ b`: sends
`v` over `b` to `(‖v‖ / ‖Φ b v‖) • Φ b v` (which is `0` when `v = 0`). -/
def radialBundleMap (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) : TotalSpace F₂ E₂ :=
  TotalSpace.mk' F₂ v.proj ((‖v.snd‖ / ‖Φ v.proj v.snd‖) • Φ v.proj v.snd)

@[simp]
theorem radialBundleMap_mk (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (b : B) (u : E₁ b) :
    radialBundleMap F₁ F₂ Φ ⟨b, u⟩ = ⟨b, (‖u‖ / ‖Φ b u‖) • Φ b u⟩ :=
  (rfl)

@[simp]
theorem radialBundleMap_proj (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    (radialBundleMap F₁ F₂ Φ v).proj = v.proj :=
  (rfl)

theorem radialBundleMap_zero (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (b : B) :
    radialBundleMap F₁ F₂ Φ (TotalSpace.mk' F₁ b 0) = TotalSpace.mk' F₂ b 0 := by
  simp [TotalSpace.mk']

/-- Radial rescaling preserves the fibre norm identically. -/
@[simp]
theorem norm_radialBundleMap (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    ‖(radialBundleMap F₁ F₂ Φ v).snd‖ = ‖v.snd‖ := by
  rcases v with ⟨b, u⟩
  rw [radialBundleMap_mk]
  dsimp only
  by_cases hu : u = 0
  · simp [hu]
  · have hΦu : Φ b u ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    rw [norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hΦu)]

/-- Radial rescaling of `(Φ b).symm` is a left inverse to radial rescaling of `Φ b` (and by
symmetry a right inverse as well). -/
@[simp]
theorem radialBundleMap_symm_radialBundleMap (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) (radialBundleMap F₁ F₂ Φ v) = v := by
  rcases v with ⟨b, u⟩
  by_cases hu : u = 0
  · simp [hu]
  · have hu_norm : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hΦu_norm : ‖Φ b u‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff _ (Φ b).injective).2 hu)
    have hcoeff :
        (‖u‖ / ‖(‖u‖ / ‖Φ b u‖) • u‖) * (‖u‖ / ‖Φ b u‖) = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp [hu_norm, hΦu_norm]
    have hnorm : ‖(‖u‖ / ‖Φ b u‖) • Φ b u‖ = ‖u‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hΦu_norm]
    simp only [radialBundleMap_mk]
    congr 1
    rw [hnorm, map_smul, ContinuousLinearEquiv.symm_apply_apply, smul_smul]
    simp [hcoeff]

end Algebraic

section TotalSpace

section Continuity

variable {B : Type*} [TopologicalSpace B]
  (F₁ F₂ : Type*) [TopologicalSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type*} {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

omit [TopologicalSpace F₁] in
/-- Operator-norm bound on the unit sphere at a base point `b₀` in the trivialization `e₂`:
there exists `C ≥ 0` such that `‖(Φ b₀).symm (e₂.symmL ℝ b₀ y)‖ < C * ‖e₂.symmL ℝ b₀ y‖` for
all `y ∈ sphere (0 : F₂) 1`. -/
private lemma exists_sphere_radial_ratio_lt (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    {b₀ : B} (hb₀ : b₀ ∈ (trivializationAt F₂ E₂ b₀).baseSet) :
    let e₂ := trivializationAt F₂ E₂ b₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ sphere (0 : F₂) 1,
      ‖(Φ b₀).symm (e₂.symmL ℝ b₀ y)‖ < C * ‖e₂.symmL ℝ b₀ y‖ := by
  let e₂ := trivializationAt F₂ E₂ b₀
  refine ⟨‖(Φ b₀).symm.toContinuousLinearMap‖ + 1, by positivity, fun y hy ↦ ?_⟩
  have hpos : 0 < ‖e₂.symmL ℝ b₀ y‖ := by
    refine norm_pos_iff.2 fun h0 ↦ ?_
    have hy0 : y = 0 := by
      rw [← e₂.continuousLinearMapAt_symmL (R := ℝ) hb₀ y, h0, map_zero]
    rw [mem_sphere_zero_iff_norm, hy0, norm_zero] at hy
    exact zero_ne_one hy
  exact ((Φ b₀).symm.toContinuousLinearMap.le_opNorm (e₂.symmL ℝ b₀ y)).trans_lt
    (mul_lt_mul_of_pos_right (lt_add_one _) hpos)

omit [TopologicalSpace F₁] [VectorBundle ℝ F₂ E₂] in
/-- Rescaling an arbitrary vector `u : E₁ b` to the unit sphere in `F₂` turns a unit-sphere
bound in `e₂` into the uniform ratio bound `‖u‖ / ‖Φ b u‖ ≤ C`. -/
private lemma radial_ratio_le_of_sphere_lt (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    {b : B} {e₂ : Trivialization F₂ (π F₂ E₂)} [e₂.IsLinear ℝ] (hb : b ∈ e₂.baseSet)
    {C : ℝ} (hC : 0 ≤ C)
    (hsphere : ∀ y ∈ sphere (0 : F₂) 1,
      ‖(Φ b).symm (e₂.symmL ℝ b y)‖ < C * ‖e₂.symmL ℝ b y‖)
    (u : E₁ b) : ‖u‖ / ‖Φ b u‖ ≤ C := by
  by_cases hu : u = 0
  · simp [hu, hC]
  · set w : E₂ b := Φ b u
    have hw : w ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    set z : F₂ := e₂.continuousLinearMapAt ℝ b w
    have hzw : e₂.symmL ℝ b z = w := e₂.symmL_continuousLinearMapAt hb w
    have hz : z ≠ 0 := fun hz0 ↦ hw (by rw [← hzw, hz0, map_zero])
    have hy : ‖z‖⁻¹ • z ∈ sphere (0 : F₂) 1 := by
      simp [norm_smul, norm_ne_zero_iff.2 hz]
    have hlt := hsphere (‖z‖⁻¹ • z) hy
    have hpos_z : 0 < ‖z‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hz)
    have hΦw : (Φ b).symm w = u := (Φ b).symm_apply_apply u
    rw [map_smul, hzw, map_smul, hΦw, norm_smul, norm_smul,
      Real.norm_of_nonneg hpos_z.le, mul_left_comm C] at hlt
    exact (div_le_iff₀ (norm_pos_iff.2 hw)).2 ((mul_lt_mul_iff_right₀ hpos_z).1 hlt).le

omit [TopologicalSpace F₁] in
/-- Near any base point `b₀`, the radial distortion `‖u‖ / ‖Φ b u‖` is uniformly bounded on fibres
over a neighbourhood of `b₀`. -/
private lemma exists_nhds_radial_ratio_le [FiniteDimensional ℝ F₂] (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (b₀ : B) :
    ∃ U ∈ 𝓝 b₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : B), b ∈ U → ∀ u : E₁ b, ‖u‖ / ‖Φ b u‖ ≤ C := by
  let e₂ := trivializationAt F₂ E₂ b₀
  have hb₀ : b₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ b₀
  -- Stage 1: obtain a strict bound `C` on the unit sphere over `b₀` from the operator norm.
  obtain ⟨C, hC₀, hC⟩ := exists_sphere_radial_ratio_lt F₂ Φ hb₀
  -- Stage 2: propagate the strict inequality from `{b₀} × S(F₂)` to a neighbourhood of `b₀`
  -- using compactness of the unit sphere and the generalized tube lemma.
  let g : e₂.baseSet × sphere (0 : F₂) 1 → TotalSpace F₂ E₂ :=
    fun q ↦ TotalSpace.mk' F₂ q.1.val (e₂.symmL ℝ q.1.val q.2.val)
  have hg : Continuous g :=
    (e₂.continuousOn_symm.comp_continuous
      ((continuous_subtypeVal.comp continuous_fst).prodMk
        (continuous_subtypeVal.comp continuous_snd))
      fun q ↦ ⟨q.1.property, mem_univ _⟩).congr fun q ↦ by simp [g]
  let φ₁ : e₂.baseSet × sphere (0 : F₂) 1 → ℝ := fun q ↦ ‖(Φ q.1.val).symm (g q).snd‖
  let φ₂ : e₂.baseSet × sphere (0 : F₂) 1 → ℝ := fun q ↦ ‖(g q).snd‖
  have hφ₁ : Continuous φ₁ := hnorm₁.comp (hΦ_symm.comp hg)
  have hφ₂ : Continuous φ₂ := hnorm₂.comp hg
  have : CompactSpace (sphere (0 : F₂) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  have hKC : ({⟨b₀, hb₀⟩} ×ˢ (univ : Set (sphere (0 : F₂) 1))) ⊆ {q | φ₁ q < C * φ₂ q} := by
    rintro ⟨b, y⟩ ⟨hb', -⟩
    obtain rfl : b = ⟨b₀, hb₀⟩ := mem_singleton_iff.1 hb'
    exact hC y.val y.property
  obtain ⟨V, W, hVo, -, hb₀V, hKW, hVW⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ
    (isOpen_lt hφ₁ (continuous_const.mul hφ₂)) hKC
  -- Stage 3: rescale arbitrary vectors in fibres over `V` to the unit sphere.
  refine ⟨Subtype.val '' V, (e₂.open_baseSet.isOpenMap_subtypeVal V hVo).mem_nhds
    ⟨⟨b₀, hb₀⟩, hb₀V (mem_singleton _), rfl⟩, C, hC₀, ?_⟩
  rintro _ ⟨⟨b, hb⟩, hbV, rfl⟩ u
  exact radial_ratio_le_of_sphere_lt F₂ Φ hb hC₀
    (fun y hy ↦ hVW (mk_mem_prod hbV (hKW (mem_univ (⟨y, hy⟩ : sphere (0 : F₂) 1))))) u

/-- **Continuity of radial bundle rescaling.** Rescaling a continuous bundle isomorphism
`Φ : E₁ ≃ E₂` fibrewise by `‖v‖ / ‖Φ v‖` is continuous whenever both bundles have continuous fibre
norms and `F₂` is finite-dimensional. -/
theorem continuous_radialBundleMap [FiberBundle F₁ E₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    Continuous (radialBundleMap F₁ F₂ Φ) := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
  obtain ⟨U, hU, C, -, hbound⟩ :=
    exists_nhds_radial_ratio_le F₁ F₂ Φ hnorm₁ hnorm₂ hΦ_symm v₀.proj
  obtain ⟨V, hVU, hVo, hb₀V⟩ := mem_nhds_iff.1 hU
  let W : Set (TotalSpace F₁ E₁) := π F₁ E₁ ⁻¹' V
  have hWo : IsOpen W := hVo.preimage (FiberBundle.continuous_proj F₁ E₁)
  have hsub : Continuous (W.domRestrict (radialBundleMap F₁ F₂ Φ)) := by
    refine Continuous.smul_totalSpace_of_norm_le (C := C)
      (φ := fun v : W ↦ TotalSpace.mk' F₂ v.val.proj (Φ v.val.proj v.val.snd))
      (c := fun v : W ↦ ‖v.val.snd‖ / ‖Φ v.val.proj v.val.snd‖) (hΦ.comp continuous_subtypeVal)
      (fun v ↦ ?_) (fun v hv ↦ ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hbound v.val.proj (hVU v.property) v.val.snd
    · exact (hnorm₁.comp continuous_subtypeVal).continuousAt.div
        (hnorm₂.comp (hΦ.comp continuous_subtypeVal)).continuousAt (norm_ne_zero_iff.2 hv)
  exact (continuousOn_iff_continuous_domRestrict.2 hsub).continuousAt (hWo.mem_nhds hb₀V)

end Continuity

variable {B : Type*} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type*} {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- **Metric-change radial bundle homeomorphism.** Given two finite-rank real vector bundles `E₁`
and `E₂` over `B` with continuous fibre norms and a continuous bundle isomorphism `Φ : E₁ ≃ E₂`,
radial rescaling `v ↦ (‖v‖ / ‖Φ v‖) • Φ v` is a homeomorphism `TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂`
covering the identity of `B` and preserving norms on every fibre. -/
def radialBundleHomeomorph [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun := radialBundleMap F₁ F₂ Φ
  invFun := radialBundleMap F₂ F₁ fun b ↦ (Φ b).symm
  left_inv := radialBundleMap_symm_radialBundleMap F₁ F₂ Φ
  right_inv := radialBundleMap_symm_radialBundleMap F₂ F₁ fun b ↦ (Φ b).symm
  continuous_toFun := continuous_radialBundleMap F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm
  continuous_invFun :=
    continuous_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁ hΦ_symm hΦ

@[simp]
theorem radialBundleHomeomorph_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (v : TotalSpace F₁ E₁) :
    radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v = radialBundleMap F₁ F₂ Φ v :=
  (rfl)

@[simp]
theorem radialBundleHomeomorph_symm_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (w : TotalSpace F₂ E₂) :
    (radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w :=
  (rfl)

end TotalSpace

end RadialMetricChange

end TauCeti
