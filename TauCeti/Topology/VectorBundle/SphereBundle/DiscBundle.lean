/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Topology.VectorBundle.OrthonormalTrivialization
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Topology.VectorBundle.Smul

/-!
# Local triviality, properness, and radial metric-change homeomorphisms of disc bundles

For a real vector bundle `E → B` with normed fibres, `TauCeti.discBundle F E` and
`TauCeti.sphereBundle F E` are the unit disc and unit sphere subsets of `TotalSpace F E` (defined in
`TauCeti.Topology.VectorBundle.SphereBundle.Basic`). This file develops local triviality,
properness, and radial metric-change homeomorphisms for disc and sphere bundles:

* `Bundle.Trivialization.discBundle`: restriction of a norm-preserving local trivialization of `E`
  to a local trivialization of `discBundleProj F E` with fibre `closedBall (0 : F) 1`;
* `TauCeti.exists_trivialization_discBundleProj` and `TauCeti.isProperMap_discBundleProj`: for a
  finite-rank continuous Riemannian vector bundle, `discBundleProj F E` is locally trivial with
  compact fibre `closedBall (0 : F) 1` and hence proper;
* `TauCeti.radialBundleHomeomorph`, `TauCeti.discBundleRadialHomeomorph`, and
  `TauCeti.sphereBundleRadialHomeomorph`: radial rescaling `v ↦ (‖v‖₁ / ‖Φ v‖₂) • Φ v` turns any
  continuous bundle isomorphism `Φ : E₁ ≃ E₂` between real vector bundles with continuous fibre
  norms into a fibrewise norm-preserving homeomorphism carrying `S(E₁)` onto `S(E₂)` (in arbitrary
  rank) and, when `F₁` and `F₂` are finite-dimensional, of total spaces carrying `D(E₁)` onto
  `D(E₂)`, showing in particular that the homeomorphism type of `(D(E), S(E))` over `B` is
  independent of the choice of continuous fibre metric.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2 (Euclidean metrics on vector bundles), §12, and §18 (unit
  sphere and unit disc bundles).
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (radial rescaling and metric independence of
  disc and sphere bundles).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 3.
-/

public section

noncomputable section

open Bundle Filter Metric Set Topology

universe w

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

open Classical in
/-- Restrict a fibrewise norm-preserving local trivialization `e` of `E` to a local trivialization
of `discBundleProj F E : D(E) → B` with model fibre `closedBall (0 : F) 1`. -/
def discBundle (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    Trivialization (closedBall (0 : F) 1) (discBundleProj F E) where
  toFun v := (discBundleProj F E v,
    if hb : v.val.proj ∈ e.baseSet then
      ⟨(e v.val).2,
        mem_closedBall_zero_iff.2
          ((he v.val.proj hb v.val.snd).trans_le (mem_discBundle.1 v.property))⟩
    else ⟨0, mem_closedBall_self zero_le_one⟩)
  invFun p :=
    if hb : p.1 ∈ e.baseSet then
      ⟨e.toOpenPartialHomeomorph.symm (p.1, p.2.val), by
        have hproj : (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)).proj = p.1 :=
          e.proj_symm_apply' hb
        have happ : e (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)) = (p.1, p.2.val) :=
          e.apply_symm_apply (e.mem_target.2 hb)
        have hiso := he _ (hproj.symm ▸ hb) (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)).snd
        rw [mem_discBundle, ← hiso, happ]
        exact mem_closedBall_zero_iff.1 p.2.property⟩
    else ⟨TotalSpace.mk' F p.1 0, by simp⟩
  source := discBundleProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' v hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, discBundleProj_apply, dite_eq_left hp.1]
    exact (e.proj_symm_apply' hp.1).symm ▸ hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by
      simpa only [mem_preimage, discBundleProj_apply] using hv
    apply Subtype.ext
    dsimp only
    rw [discBundleProj_apply, dite_eq_left hv', dite_eq_left hv']
    exact e.symm_apply_mk_proj (e.mem_source.2 hv')
  right_inv' p hp := by
    ext
    · dsimp only
      rw [discBundleProj_apply, dite_eq_left hp.1]
      exact e.proj_symm_apply' hp.1
    · dsimp only
      rw [dite_eq_left hp.1, dite_eq_left (by rw [e.proj_symm_apply' hp.1]; exact hp.1)]
      dsimp only
      rw [e.apply_symm_apply (e.mem_target.2 hp.1)]
  open_source := e.open_baseSet.preimage (discBundleProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine (discBundleProj F E).continuous.continuousOn.prodMk ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (continuous_snd.comp_continuousOn <|
      e.continuousOn.comp continuous_subtypeVal.continuousOn fun v hv ↦
        e.mem_source.2 (by simpa only [mem_preimage, discBundleProj_apply] using hv)).congr
      fun v hv ↦ ?_
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by
      simpa only [mem_preimage, discBundleProj_apply] using hv
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hv']
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).continuousOn
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mem_target.2 hp.1).congr fun p hp ↦ ?_
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hp.1]
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem discBundle_baseSet (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    (e.discBundle he).baseSet = e.baseSet :=
  (rfl)

open Classical in
@[simp]
theorem coe_discBundle_apply_snd (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)
    {v : TauCeti.discBundle F E} (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.discBundle he v).2 : F) = (e v.val).2 := by
  simp [discBundle, hv]

open Classical in
/-- Over its base set, the inverse chart of the disc bundle agrees with the inverse of `e`. -/
@[simp]
theorem coe_discBundle_symm_apply (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)
    {b : B} (hb : b ∈ e.baseSet) (w : closedBall (0 : F) 1) :
    ((e.discBundle he).toOpenPartialHomeomorph.symm (b, w) : TotalSpace F E) =
      e.toOpenPartialHomeomorph.symm (b, w.val) := by
  simp [discBundle, hb]

end Bundle.Trivialization

namespace TauCeti

section Proper

variable {B : Type w} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- Around every point of the base, `discBundleProj F E : D(E) → B` has a local trivialization with
model fibre `closedBall (0 : F) 1`. -/
theorem exists_trivialization_discBundleProj (b : B) :
    ∃ e : Trivialization (closedBall (0 : F) 1) (discBundleProj F E), b ∈ e.baseSet := by
  obtain ⟨e, _, hb, hiso⟩ :=
    OrthonormalBasis.exists_orthonormal_trivialization (E := E) (stdOrthonormalBasis ℝ F) b
  exact ⟨e.discBundle hiso, hb⟩

/-- **The unit disc bundle projection of a finite-rank continuous Riemannian bundle is proper.** -/
theorem isProperMap_discBundleProj : IsProperMap (discBundleProj F E) :=
  have : CompactSpace (closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  isProperMap_of_forall_exists_trivialization (exists_trivialization_discBundleProj F E)

end Proper

section RadialMetricChange

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
  rw [radialBundleMap_mk, radialBundleMap_mk]
  congr 1
  by_cases hu : u = 0
  · simp [hu]
  · have hΦu : Φ b u ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    rw [map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_smul, norm_smul,
      Real.norm_of_nonneg (by positivity), smul_smul]
    have hcoeff :
        ‖u‖ / ‖Φ b u‖ * ‖Φ b u‖ / (‖u‖ / ‖Φ b u‖ * ‖u‖) * (‖u‖ / ‖Φ b u‖) = 1 := by
      field_simp
    rw [hcoeff, one_smul]

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
  have hφ₂_pos (y : sphere (0 : F₂) 1) : 0 < φ₂ (⟨b₀, hb₀⟩, y) := by
    refine norm_pos_iff.2 fun h0 ↦ ?_
    dsimp only [φ₂, g] at h0
    have hy : (y : F₂) = 0 := by
      rw [← e₂.continuousLinearMapAt_symmL (R := ℝ) hb₀ y.val, h0, map_zero]
    have hmem := y.property
    rw [mem_sphere_zero_iff_norm, hy, norm_zero] at hmem
    exact zero_ne_one hmem
  have : CompactSpace (sphere (0 : F₂) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  let K : Set (e₂.baseSet × sphere (0 : F₂) 1) := {⟨b₀, hb₀⟩} ×ˢ univ
  have hKc : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hφ₂_ne : ∀ q ∈ K, φ₂ q ≠ 0 := by
    rintro ⟨b, y⟩ ⟨hb', -⟩
    obtain rfl : b = ⟨b₀, hb₀⟩ := mem_singleton_iff.1 hb'
    exact (hφ₂_pos y).ne'
  obtain ⟨M, hM⟩ :=
    (hKc.image_of_continuousOn (hφ₁.continuousOn.div hφ₂.continuousOn hφ₂_ne)).bddAbove
  let C : ℝ := max M 0 + 1
  have hC₀ : 0 ≤ C := by positivity
  have hKC : K ⊆ {q | φ₁ q < C * φ₂ q} := by
    rintro ⟨b, y⟩ hq
    obtain rfl : b = ⟨b₀, hb₀⟩ := mem_singleton_iff.1 hq.1
    have hle : φ₁ (⟨b₀, hb₀⟩, y) / φ₂ (⟨b₀, hb₀⟩, y) ≤ M :=
      hM ⟨(⟨b₀, hb₀⟩, y), hq, rfl⟩
    exact (div_lt_iff₀ (hφ₂_pos y)).1 (hle.trans_lt ((le_max_left M 0).trans_lt (lt_add_one _)))
  obtain ⟨V, W, hVo, -, hb₀V, hKW, hVW⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ
    (isOpen_lt hφ₁ (continuous_const.mul hφ₂)) hKC
  refine ⟨Subtype.val '' V, (e₂.open_baseSet.isOpenMap_subtypeVal V hVo).mem_nhds
    ⟨⟨b₀, hb₀⟩, hb₀V (mem_singleton _), rfl⟩, C, hC₀, ?_⟩
  rintro _ ⟨⟨b, hb⟩, hbV, rfl⟩ u
  by_cases hu : u = 0
  · simp [hu, hC₀]
  · set w : E₂ b := Φ b u
    have hw : w ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    set z : F₂ := e₂.continuousLinearMapAt ℝ b w
    have hzw : e₂.symmL ℝ b z = w := e₂.symmL_continuousLinearMapAt hb w
    have hz : z ≠ 0 := fun hz0 ↦ hw (by rw [← hzw, hz0, map_zero])
    let y : sphere (0 : F₂) 1 := ⟨‖z‖⁻¹ • z, by simp [norm_smul, norm_ne_zero_iff.2 hz]⟩
    have hlt : φ₁ (⟨b, hb⟩, y) < C * φ₂ (⟨b, hb⟩, y) := hVW ⟨hbV, hKW (mem_univ y)⟩
    have hgy : (g (⟨b, hb⟩, y)).snd = ‖z‖⁻¹ • w := by simp [g, y, map_smul, hzw]
    have hΦw : (Φ b).symm w = u := (Φ b).symm_apply_apply u
    have hpos_z : 0 < ‖z‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hz)
    simp only [φ₁, φ₂, hgy, map_smul, hΦw, norm_smul, Real.norm_of_nonneg hpos_z.le] at hlt
    rw [mul_left_comm C] at hlt
    exact (div_le_iff₀ (norm_pos_iff.2 hw)).2 ((mul_lt_mul_iff_right₀ hpos_z).1 hlt).le

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

section Subbundles

variable {B : Type w} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type w} {E₂ : B → Type w}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- **Metric-change radial homeomorphism of unit disc bundles.** -/
def discBundleRadialHomeomorph [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    discBundle F₁ E₁ ≃ₜ discBundle F₂ E₂ :=
  (radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).subtype fun v ↦ by simp

@[simp]
theorem coe_discBundleRadialHomeomorph_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (v : discBundle F₁ E₁) :
    (discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.val :=
  (rfl)

@[simp]
theorem coe_discBundleRadialHomeomorph_symm_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (w : discBundle F₂ E₂) :
    ((discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w : TotalSpace F₁ E₁) =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val :=
  (rfl)

omit [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] in
private lemma continuous_radialBundleMap_sphere (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) :
    Continuous fun v : sphereBundle F₁ E₁ ↦ radialBundleMap F₁ F₂ Φ v.val := by
  have hΦ' : Continuous fun v : sphereBundle F₁ E₁ ↦
      TotalSpace.mk' F₂ v.val.proj (Φ v.val.proj v.val.snd) := hΦ.comp continuous_subtypeVal
  refine Continuous.smul_totalSpace ?_ hΦ'
  exact (hnorm₁.comp continuous_subtypeVal).div (hnorm₂.comp hΦ') fun v ↦
    norm_ne_zero_iff.2 <| (map_ne_zero_iff _ (Φ v.val.proj).injective).2 <|
      norm_ne_zero_iff.1 ((mem_sphereBundle.1 v.property).symm ▸ one_ne_zero)

-- Unlike `discBundleRadialHomeomorph`, vectors on `sphereBundle` stay away from the zero section,
-- so continuity holds without `FiniteDimensional` and does not factor via `radialBundleHomeomorph`.
/-- **Metric-change radial homeomorphism of unit sphere bundles.** Holds in arbitrary rank (no
`FiniteDimensional` hypothesis is needed since unit vectors stay away from the zero section). -/
def sphereBundleRadialHomeomorph (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd)) :
    sphereBundle F₁ E₁ ≃ₜ sphereBundle F₂ E₂ where
  toFun v := ⟨radialBundleMap F₁ F₂ Φ v.val,
    mem_sphereBundle.2 ((norm_radialBundleMap F₁ F₂ Φ v.val).trans (mem_sphereBundle.1 v.property))⟩
  invFun w := ⟨radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val,
    mem_sphereBundle.2 ((norm_radialBundleMap F₂ F₁ _ w.val).trans (mem_sphereBundle.1 w.property))⟩
  left_inv v := Subtype.ext (radialBundleMap_symm_radialBundleMap F₁ F₂ Φ v.val)
  right_inv w := Subtype.ext (radialBundleMap_symm_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val)
  continuous_toFun := (continuous_radialBundleMap_sphere F₁ F₂ Φ hnorm₁ hnorm₂ hΦ).subtype_mk _
  continuous_invFun :=
    (continuous_radialBundleMap_sphere F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁
      hΦ_symm).subtype_mk _

@[simp]
theorem coe_sphereBundleRadialHomeomorph_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (v : sphereBundle F₁ E₁) :
    (sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.val :=
  (rfl)

@[simp]
theorem coe_sphereBundleRadialHomeomorph_symm_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.snd‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.snd‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.snd))
    (w : sphereBundle F₂ E₂) :
    ((sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w : TotalSpace F₁ E₁) =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.val :=
  (rfl)

end Subbundles

end RadialMetricChange

end TauCeti
