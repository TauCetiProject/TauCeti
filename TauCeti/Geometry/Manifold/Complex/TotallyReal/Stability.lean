/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TotallyReal
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.LinearAlgebra.TotallyReal.Finrank

/-!
# Stability of totally real embeddings

Maximal total reality of the tangent images of a `C¹` map `ι : N → M` is stable under
perturbations of the almost complex structure that are small in the `C⁰` sense, uniformly on
compact subsets of `N`. A fortiori it is stable under `C¹`-small perturbations.

Tangent spaces at different points are compared in the canonical trivializations of the
tangent bundle. In such a trivialization both the tangent image `im dι_x` and the structure
`J(ι x)` are read as a frame `F →L[ℝ] E` and an endomorphism of `E`, and the linear stability
theorem of `TauCeti.Analysis.Normed.Module.TotallyReal` applies to the resulting pairs.

The perturbed endomorphisms need not square to minus the identity, and only the original field
must be continuous; perturbations are arbitrary operators close to it in a chart.

## Main declarations

* `TauCeti.isMaximalTotallyReal_inCoordinates_iff`: maximal total reality is unchanged by
  reading a frame and an endomorphism in vector bundle trivializations.
* `TauCeti.exists_pos_eventually_isMaximalTotallyReal_range_mfderiv`: the local chart form, one
  radius for all operators close to `J(ι x₀)` in the chart at `ι x₀`.
* `TauCeti.exists_pos_forall_isMaximalTotallyReal_of_isCompact`: the compact chart form, one
  radius for a finite chart cover of a compact subset.
* `TauCeti.eventually_forall_isMaximalTotallyReal_of_isCompact`: continuous families of fields
  over any parameter space.
* `TauCeti.ContMDiffAlmostComplexStructureFamily.eventually_isTotallyRealEmbedding`: a totally
  real embedding of a compact manifold stays totally real for nearby members of a family.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public noncomputable section

open Bundle Filter Function Module Set Topology
open ContinuousLinearMap (inCoordinates)
open scoped Manifold ContDiff

namespace TauCeti

section Coordinates

variable {B₁ B₂ F₁ F₂ : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B₁ → Type*} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [VectorBundle ℝ F₁ E₁]
  {E₂ : B₂ → Type*} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₂ E₂]

/-- Reading a frame `A` and an endomorphism `K` of its target fibre in trivializations whose base
sets contain the fibres does not change maximal total reality of the image. -/
theorem isMaximalTotallyReal_inCoordinates_iff {x₀ x : B₁} {y₀ y : B₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet)
    (A : E₁ x →L[ℝ] E₂ y) (K : E₂ y →L[ℝ] E₂ y) :
    IsMaximalTotallyReal (inCoordinates F₂ E₂ F₂ E₂ y₀ y y₀ y K).toLinearMap
        (LinearMap.range (inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y A).toLinearMap) ↔
      IsMaximalTotallyReal K.toLinearMap (LinearMap.range A.toLinearMap) := by
  set e := (trivializationAt F₂ E₂ y₀).continuousLinearEquivAt ℝ y hy
  set e' := (trivializationAt F₁ E₁ x₀).continuousLinearEquivAt ℝ x hx
  have hA : inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y A =
      (e : E₂ y →L[ℝ] F₂).comp (A.comp (e'.symm : F₁ →L[ℝ] E₁ x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hy
  have hK : inCoordinates F₂ E₂ F₂ E₂ y₀ y y₀ y K =
      (e : E₂ y →L[ℝ] F₂).comp (K.comp (e.symm : F₂ →L[ℝ] E₂ y)) :=
    ContinuousLinearMap.inCoordinates_eq hy hy
  have hr : LinearMap.range (inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y A).toLinearMap =
      (LinearMap.range A.toLinearMap).map e.toLinearEquiv.toLinearMap := by
    rw [hA, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp_of_range_eq_top]
    · rfl
    · exact LinearMap.range_eq_top.mpr e'.symm.surjective
  rw [hr]
  refine isMaximalTotallyReal_map_linearEquiv_iff e.toLinearEquiv ?_
  ext v
  rw [hK]
  simp

end Coordinates

section Tangent

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  {ι : N → M}

/-- The local chart form of stability. If `ι` is `C¹` at `x₀` with injective differential and
`im dι_{x₀}` is maximal totally real for an injective `J₀`, then near `x₀` every operator on
`T_{ι x}M` whose expression in the chart at `ι x₀` is within a fixed `ε` of `J₀` keeps
`im dι_x` maximal totally real. The operators need not square to minus the identity. -/
theorem exists_pos_eventually_isMaximalTotallyReal_range_mfderiv {x₀ : N}
    (hι : ContMDiffAt I' I 1 ι x₀) (hinj : Injective (mfderiv I' I ι x₀))
    {J₀ : TangentSpace I (ι x₀) →L[ℝ] TangentSpace I (ι x₀)} (hJ₀ : Injective J₀)
    (h : IsMaximalTotallyReal J₀.toLinearMap
      (LinearMap.range (mfderiv I' I ι x₀).toLinearMap)) :
    ∃ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ A : TangentSpace I (ι x) →L[ℝ] TangentSpace I (ι x),
      dist (inCoordinates E (TangentSpace I) E (TangentSpace I) (ι x₀) (ι x) (ι x₀) (ι x) A) J₀ <
          ε →
        IsMaximalTotallyReal A.toLinearMap (LinearMap.range (mfderiv I' I ι x).toLinearMap) := by
  let D : N → F →L[ℝ] E := inTangentCoordinates I' I id ι (mfderiv I' I ι) x₀
  have hD : ContinuousAt D x₀ := (hι.mfderiv_const (m := 0) (by simp)).continuousAt
  have hD₀ : D x₀ = mfderiv I' I ι x₀ :=
    Manifold.inTangentCoordinates_eq_self_of_eq id ι _ rfl rfl
  obtain ⟨ε, hε, hstab⟩ := exists_pos_isMaximalTotallyReal_range_of_isCompact
    (isCompact_singleton (X := (F →L[ℝ] E) × (E →L[ℝ] E)) (x := (mfderiv I' I ι x₀, J₀)))
    (by rintro _ rfl; exact hinj) (by rintro _ rfl; exact hJ₀.comp hinj)
    (by rintro _ rfl; exact h)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hD.eventually (Metric.ball_mem_nhds _ hε), chart_source_mem_nhds H' x₀,
    hι.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H (ι x₀))]
    with x hDx hx hy A hA
  rw [dist_eq_norm, hD₀] at hDx
  exact (isMaximalTotallyReal_inCoordinates_iff hx hy (mfderiv I' I ι x) A).1
    (hstab _ rfl (D x) _ hDx (by rwa [← dist_eq_norm]))

/-- Stability for continuous families of fields over an arbitrary parameter space `T`, uniformly
on a compact set `K`. The field `𝒥 t` is continuous in `(t, y)` as a section of the endomorphism
bundle near the points `(t₀, ι x)`, `x ∈ K`; no square identity is imposed. -/
theorem eventually_forall_isMaximalTotallyReal_of_isCompact {T : Type*} [TopologicalSpace T]
    {𝒥 : T → ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {t₀ : T} {K : Set N}
    (hK : IsCompact K)
    (h𝒥 : ∀ x ∈ K, ContinuousAt (fun q : T × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) q.2 (𝒥 q.1 q.2)) (t₀, ι x))
    (hι : ∀ x ∈ K, ContMDiffAt I' I 1 ι x) (hinj : ∀ x ∈ K, Injective (mfderiv I' I ι x))
    (hJ : ∀ x ∈ K, Injective (𝒥 t₀ (ι x)))
    (h : ∀ x ∈ K, IsMaximalTotallyReal (𝒥 t₀ (ι x)).toLinearMap
      (LinearMap.range (mfderiv I' I ι x).toLinearMap)) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, IsMaximalTotallyReal (𝒥 t (ι x)).toLinearMap
      (LinearMap.range (mfderiv I' I ι x).toLinearMap) := by
  refine hK.eventually_forall_of_forall_eventually fun x₀ hx₀ ↦ ?_
  obtain ⟨ε, hε, hloc⟩ := exists_pos_eventually_isMaximalTotallyReal_range_mfderiv
    (hι x₀ hx₀) (hinj x₀ hx₀) (hJ x₀ hx₀) (h x₀ hx₀)
  have hc := ((continuousAt_hom_bundle (RingHom.id ℝ) _).1 ((h𝒥 x₀ hx₀).comp
    (f := fun q : T × N ↦ (q.1, ι q.2))
    (continuousAt_fst.prodMk ((hι x₀ hx₀).continuousAt.comp (x := (t₀, x₀))
      continuousAt_snd)))).2
  filter_upwards [hc.eventually (Metric.ball_mem_nhds _ hε), continuousAt_snd.eventually hloc]
    with q hq hq'
  simp only [Function.comp_apply, Manifold.inCoordinates_tangentSpace_self] at hq
  exact hq' _ hq

/-- The compact chart form of stability. A compact set `K` on which `ι` is `C¹` with maximal
totally real tangent images for a continuous field `J₀` is covered by finitely many open sets
`U c`, `c ∈ s`, with one radius `ε` such that on `U c` every operator whose expression in the
chart at `ι c` is within `ε` of that of `J₀` keeps the tangent image maximal totally real. -/
theorem exists_pos_forall_isMaximalTotallyReal_of_isCompact
    {J₀ : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {K : Set N} (hK : IsCompact K)
    (hJ₀c : ∀ x ∈ K, ContinuousAt (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (J₀ y)) (ι x))
    (hι : ∀ x ∈ K, ContMDiffAt I' I 1 ι x) (hinj : ∀ x ∈ K, Injective (mfderiv I' I ι x))
    (hJ : ∀ x ∈ K, Injective (J₀ (ι x)))
    (h : ∀ x ∈ K, IsMaximalTotallyReal (J₀ (ι x)).toLinearMap
      (LinearMap.range (mfderiv I' I ι x).toLinearMap)) :
    ∃ s : Finset N, (↑s ⊆ K) ∧ ∃ U : N → Set N, (∀ c ∈ s, IsOpen (U c) ∧ c ∈ U c) ∧
      K ⊆ ⋃ c ∈ s, U c ∧ ∃ ε > 0, ∀ c ∈ s, ∀ x ∈ U c,
        ∀ A : TangentSpace I (ι x) →L[ℝ] TangentSpace I (ι x),
          dist (inCoordinates E (TangentSpace I) E (TangentSpace I) (ι c) (ι x) (ι c) (ι x) A)
              (inCoordinates E (TangentSpace I) E (TangentSpace I) (ι c) (ι x) (ι c) (ι x)
                (J₀ (ι x))) < ε →
            IsMaximalTotallyReal A.toLinearMap
              (LinearMap.range (mfderiv I' I ι x).toLinearMap) := by
  have hloc (c : N) (hc : c ∈ K) : ∃ δ > 0, ∀ᶠ x in 𝓝 c,
      ∀ A : TangentSpace I (ι x) →L[ℝ] TangentSpace I (ι x),
        dist (inCoordinates E (TangentSpace I) E (TangentSpace I) (ι c) (ι x) (ι c) (ι x) A)
            (inCoordinates E (TangentSpace I) E (TangentSpace I) (ι c) (ι x) (ι c) (ι x)
              (J₀ (ι x))) < δ →
          IsMaximalTotallyReal A.toLinearMap
            (LinearMap.range (mfderiv I' I ι x).toLinearMap) := by
    obtain ⟨ε, hε, hev⟩ := exists_pos_eventually_isMaximalTotallyReal_range_mfderiv
      (hι c hc) (hinj c hc) (hJ c hc) (h c hc)
    have hcont := ((continuousAt_hom_bundle (RingHom.id ℝ) _).1
      ((hJ₀c c hc).comp (x := c) (hι c hc).continuousAt)).2
    refine ⟨ε / 2, half_pos hε, ?_⟩
    filter_upwards [hev, hcont.eventually (Metric.ball_mem_nhds _ (half_pos hε))]
      with x hx hJx A hA
    simp only [Function.comp_apply, Manifold.inCoordinates_tangentSpace_self] at hJx
    exact hx A ((dist_triangle _ _ _).trans_lt (by linarith))
  choose! δ hδ hev using hloc
  have hU (c : N) (hc : c ∈ K) := eventually_nhds_iff.1 (hev c hc)
  choose! U hUsub hUo hcU using hU
  obtain ⟨s, hsK, hKs⟩ := hK.elim_nhds_subcover U fun c hc ↦ (hUo c hc).mem_nhds (hcU c hc)
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε > 0, ∀ c ∈ s, ε ≤ δ c := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨s.inf' hs δ, (Finset.lt_inf'_iff hs).2 fun c hc ↦ hδ c (hsK c hc),
        fun c hc ↦ Finset.inf'_le δ hc⟩
  exact ⟨s, hsK, U, fun c hc ↦ ⟨hUo c (hsK c hc), hcU c (hsK c hc)⟩, hKs, ε, hε,
    fun c hc x hx A hA ↦ hUsub c (hsK c hc) x hx A (hA.trans_le (hεδ c hc))⟩

end Tangent

namespace ContMDiffAlmostComplexStructureFamily

variable {E H M F H' N EP HP P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n : ℕ∞} {ι : N → M}

/-- In a jointly continuous family of almost complex structures, maximal total reality of the
tangent images of a half-dimensional `C¹` map along a compact set `K` persists for nearby
parameters. -/
theorem eventually_forall_isMaximalTotallyReal
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    {p₀ : P} {K : Set N} (hK : IsCompact K) (hι : ∀ x ∈ K, ContMDiffAt I' I 1 ι x)
    (hdim : 2 * finrank ℝ F = finrank ℝ E)
    (h : ∀ x ∈ K, IsMaximalTotallyReal ((J.freeze p₀).almostComplexStructureAt (ι x)).toLinearMap
      (LinearMap.range (mfderiv I' I ι x).toLinearMap)) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K,
      IsMaximalTotallyReal ((J.freeze p).almostComplexStructureAt (ι x)).toLinearMap
        (LinearMap.range (mfderiv I' I ι x).toLinearMap) := by
  simp only [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap] at h ⊢
  refine eventually_forall_isMaximalTotallyReal_of_isCompact
    (𝒥 := fun p ↦ (J.freeze p).toEndomorphism) hK (fun _ _ ↦ ?_) hι
    (fun x hx ↦ (h x hx).injective_of_two_mul_finrank_eq
      (fun a b hab ↦ Subtype.ext ((J.freeze p₀).injective (ι x) hab)) hdim)
    (fun x _ ↦ (J.freeze p₀).injective (ι x)) h
  simpa only [freeze_toEndomorphism_apply] using J.contMDiff.continuous.continuousAt

/-- For a compact source, a `C¹` half-dimensional map with maximal totally real tangent images
keeps this property for all members of a family near the original one. -/
theorem eventually_isMaximalTotallyRealMap [CompactSpace N]
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) {p₀ : P}
    (hι : ContMDiff I' I 1 ι) (hdim : 2 * finrank ℝ F = finrank ℝ E)
    (h : IsMaximalTotallyRealMap I' I (J.freeze p₀).almostComplexStructureAt ι) :
    ∀ᶠ p in 𝓝 p₀, IsMaximalTotallyRealMap I' I (J.freeze p).almostComplexStructureAt ι := by
  rw [isMaximalTotallyRealMap_iff] at h
  filter_upwards [J.eventually_forall_isMaximalTotallyReal isCompact_univ (fun x _ ↦ hι x) hdim
    fun x _ ↦ h x] with p hp
  exact (isMaximalTotallyRealMap_iff).2 fun x ↦ hp x (mem_univ x)

/-- A totally real embedding of a compact manifold for one member of a jointly continuous family
of almost complex structures is totally real for all nearby members. The embedding and dimension
conditions do not involve the structure. -/
theorem eventually_isTotallyRealEmbedding [CompactSpace N]
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) {p₀ : P} {m : ℕ∞ω} (hm : 1 ≤ m)
    (h : IsTotallyRealEmbedding I' I m (J.freeze p₀).almostComplexStructureAt ι) :
    ∀ᶠ p in 𝓝 p₀, IsTotallyRealEmbedding I' I m (J.freeze p).almostComplexStructureAt ι := by
  filter_upwards [J.eventually_isMaximalTotallyRealMap (h.isSmoothEmbedding.contMDiff.of_le hm)
    h.two_mul_finrank h.isMaximalTotallyRealMap] with p hp
  exact ⟨h.isSmoothEmbedding, h.two_mul_finrank, hp⟩

end ContMDiffAlmostComplexStructureFamily

section Checks

open Complex

/-- Check: the doubled frame of the real line in `ℂ` for multiplication by `I` is invertible, so
the real line is maximal totally real for it. -/
theorem isMaximalTotallyReal_lsmul_I_range_ofRealCLM :
    IsMaximalTotallyReal (ContinuousLinearMap.lsmul ℝ ℂ I : ℂ →L[ℝ] ℂ).toLinearMap
      (LinearMap.range ofRealCLM.toLinearMap) := by
  refine isMaximalTotallyReal_range_of_bijective_coprod ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
  · simp only [LinearMap.coprod_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ofRealCLM_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hab
    have hre := congrArg re hab
    have him := congrArg im hab
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, add_im, mul_im] at hre him
    exact Prod.ext (by linarith) (by linarith)
  · refine ⟨(z.re, z.im), ?_⟩
    simp only [LinearMap.coprod_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ofRealCLM_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [mul_comm]
    exact re_add_im z

/-- Check: operators near multiplication by `I` in the model chart of `ℂ` keep the real line
maximal totally real, by the local chart form applied to the inclusion `ℝ → ℂ`. -/
theorem exists_pos_isMaximalTotallyReal_range_ofRealCLM :
    ∃ ε > 0, ∀ A : ℂ →L[ℝ] ℂ, dist A (ContinuousLinearMap.lsmul ℝ ℂ I) < ε →
      IsMaximalTotallyReal A.toLinearMap (LinearMap.range ofRealCLM.toLinearMap) := by
  have hinj : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ofRealCLM 0) := by
    rw [ContinuousLinearMap.mfderiv_eq]
    exact ofReal_injective
  have hJ : Injective (ContinuousLinearMap.lsmul ℝ ℂ I : ℂ →L[ℝ] ℂ) :=
    smul_right_injective ℂ I_ne_zero
  obtain ⟨ε, hε, hev⟩ := exists_pos_eventually_isMaximalTotallyReal_range_mfderiv
    (ι := ofRealCLM) (x₀ := 0) ofRealCLM.contMDiff.contMDiffAt hinj hJ
    (by rw [ContinuousLinearMap.mfderiv_eq]; exact isMaximalTotallyReal_lsmul_I_range_ofRealCLM)
  refine ⟨ε, hε, fun A hA ↦ ?_⟩
  have h := hev.self_of_nhds A
  simp only [inCoordinates_tangent_bundle_core_model_space, ContinuousLinearMap.mfderiv_eq] at h
  exact h hA

/-- Check: the radius is finite. The identity operator does not keep the real line maximal
totally real, since the real line is its own image. -/
theorem not_isMaximalTotallyReal_id_range_ofRealCLM :
    ¬ IsMaximalTotallyReal (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
      (LinearMap.range ofRealCLM.toLinearMap) := by
  intro h
  have hb := h.disjoint
  rw [Submodule.map_id, disjoint_self] at hb
  have h1 : (1 : ℂ) ∈ LinearMap.range ofRealCLM.toLinearMap := ⟨1, by simp⟩
  rw [hb, Submodule.mem_bot] at h1
  exact one_ne_zero h1

end Checks

end TauCeti
