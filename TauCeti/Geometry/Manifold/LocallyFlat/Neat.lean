/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth

/-!
# Neat smooth embeddings of half-space charted spaces are locally flat

`TauCeti.IsLocallyFlat.of_isSmoothEmbedding` proves that a smooth embedding into a *boundaryless*
manifold is locally flat. This file treats *neat* embeddings between charted spaces modelled on
Euclidean half-spaces `𝓡∂ k` and `𝓡∂ m`, meeting the boundary of the ambient space exactly in their
own boundary: `f ⁻¹' ∂N = ∂M`. The maximal-atlas charts in the immersion's normal form supply the
smoothness needed here; global `IsManifold` instances are unnecessary. Such an embedding is locally
flat with tangential model the half-space `EuclideanHalfSpace k`. Ambient charts take values in
`EuclideanHalfSpace k × F`, with `F` the complement of the immersion, and carry the image of `f`
exactly onto `EuclideanHalfSpace k × {0}`.

A properly embedded slice disc `D² → D⁴` in manifolds with boundary is the motivating example.
At a boundary point the standard picture of a neat submanifold is
`(ℝᵏ⁻¹ × [0, ∞)) × {0} ⊆ (ℝᵏ⁻¹ × [0, ∞)) × ℝᵐ⁻ᵏ`.

The immersion normal form `Manifold.IsImmersionAtOfComplement` reads `f` in charts as
`u ↦ L (u, 0)` for a linear equivalence `L : E × F ≃L E'`. When the ambient model has boundary,
the ambient chart only covers a piece of the half-space `range (𝓡∂ m)`, so `L⁻¹` composed with it
is not an open map into `E × F`. What is needed is a linear equivalence `A : E' ≃L E × F` that
still reads `f` as `u ↦ (u, 0)` and carries the half-space `range (𝓡∂ m)` onto
`range (𝓡∂ k) × F`, at least near the point considered.
`TauCeti.exists_isSliceChart_of_isImmersionAtOfComplement_of_straightening` shows that such a
*straightening* `A` gives a slice chart. It works for arbitrary models with corners.

For the half-space models a straightening always exists at a point of a neat embedding.

* At an interior point the image point is interior too, by neatness, and `A = L⁻¹` works on a small
  open set where both half-space conditions hold strictly.
* At a boundary point, the boundary coordinate `ν u = (L (u, 0)) 0` of the ambient chart pulled back
  along the immersion is nonnegative near the point and vanishes at it. A linear functional with
  this property on a neighbourhood in the half-space is a nonnegative multiple `c • u 0` of the
  domain's boundary coordinate. Neatness at interior points forces `c > 0`. The shear
  `(u, w) ↦ (u + c⁻¹ (L (0, w)) 0 • e₀, w)` composed with `L⁻¹` then rescales the ambient boundary
  coordinate to the domain's one and is a straightening.

Both cases use that interior and boundary points can be detected in the charts of the immersion,
which only lie in the maximal atlas: this is
`TauCeti.ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff_of_mem_maximalAtlas`. The
multiple of the boundary coordinate is supplied by
`ContinuousLinearMap.exists_pos_eq_mul_apply_zero_of_eventually_nonneg`.

## Main results

* `TauCeti.exists_isSliceChart_of_isImmersionAtOfComplement_of_straightening`: a straightening of
  the ambient model gives a slice chart valued in `H × F`.
* `TauCeti.exists_isSliceChart_of_isImmersionAtOfComplement_of_preimage_boundary`: the slice chart
  of a neat embedding of half-space charted spaces at a point.
* `TauCeti.IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding_of_preimage_boundary` and
  `TauCeti.IsLocallyFlat.of_isSmoothEmbedding_of_preimage_boundary`: a neat `C^n` embedding of
  half-space charted spaces, `n ≠ 0`, is locally flat with tangential model the half-space.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, Section 4, for neat
  submanifolds of manifolds with boundary.
* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 1, for local flatness of embeddings of manifolds with boundary.
-/

public section

namespace TauCeti

open Filter Manifold Set Topology

open scoped ContDiff Manifold

section Straightening

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- The partial homeomorphism `G → H × F` of model spaces induced by a linear equivalence
`A : E' ≃L E × F` which, on the open set `O`, carries `range J` onto `range I × F`. -/
private noncomputable def straighteningChart (A : E' ≃L[𝕜] E × F) {O : Set E'} (hO : IsOpen O)
    (hA : ∀ v ∈ O, v ∈ range J ↔ (A v).1 ∈ range I) : OpenPartialHomeomorph G (H × F) where
  toFun g := (I.symm (A (J g)).1, (A (J g)).2)
  invFun z := J.symm (A.symm (I z.1, z.2))
  source := J ⁻¹' O
  target := {z | A.symm (I z.1, z.2) ∈ O}
  map_source' g hg := by
    have hI : (A (J g)).1 ∈ range I := (hA _ hg).1 (mem_range_self g)
    simpa [I.right_inv hI] using hg
  map_target' z hz := by
    have hJ : A.symm (I z.1, z.2) ∈ range J := (hA _ hz).2 (by simp)
    simpa [mem_preimage, J.right_inv hJ] using hz
  left_inv' g hg := by
    have hI : (A (J g)).1 ∈ range I := (hA _ hg).1 (mem_range_self g)
    simp [I.right_inv hI]
  right_inv' z hz := by
    have hJ : A.symm (I z.1, z.2) ∈ range J := (hA _ hz).2 (by simp)
    simp [J.right_inv hJ]
  open_source := hO.preimage J.continuous
  open_target := hO.preimage (by fun_prop)
  continuousOn_toFun := by
    exact ((I.continuous_symm.comp (continuous_fst.comp (A.continuous.comp J.continuous))).prodMk
      (continuous_snd.comp (A.continuous.comp J.continuous))).continuousOn
  continuousOn_invFun := (J.continuous_symm.comp (by fun_prop)).continuousOn

/-- **The slice chart of a straightened immersion.** Let `f` be a topological embedding and a
`C^n` immersion at `x` with complement `F`, written in charts as `u ↦ L (u, 0)`. Suppose that the
linear equivalence `A : E' ≃L E × F` reads `L (u, 0)` as `(u, 0)` and, on an open set `O` around the
chart image of `f x`, carries the range of the ambient model onto `range I × F`. Then around `f x`
there is an ambient chart valued in `H × F` carrying `Set.range f` exactly onto `H × {0}`.

This is the form of the slice-chart argument of
`TauCeti.exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement` that allows the ambient
manifold to have boundary or corners: the straightening replaces the boundarylessness of the
ambient model. -/
theorem exists_isSliceChart_of_isImmersionAtOfComplement_of_straightening (hf : IsEmbedding f)
    {x : M} (h : IsImmersionAtOfComplement F I J n f x) (A : E' ≃L[𝕜] E × F)
    (hAL : ∀ u : E, A (h.equiv (u, 0)) = (u, 0)) {O : Set E'} (hO : IsOpen O)
    (hxO : h.codChart.extend J (f x) ∈ O) (hA : ∀ v ∈ O, v ∈ range J ↔ (A v).1 ∈ range I) :
    ∃ Φ : OpenPartialHomeomorph N (H × F), f x ∈ Φ.source ∧
      IsSliceChart Φ (univ ×ˢ ({0} : Set F)) (range f) := by
  -- The ambient chart of the immersion, straightened into `H × F`.
  set Ψ : OpenPartialHomeomorph N (H × F) := h.codChart.trans (straighteningChart A hO hA)
  -- Both hold by unfolding `OpenPartialHomeomorph.trans` and `straighteningChart`.
  have hΨ_apply : ∀ p : N, Ψ p =
      (I.symm (A (h.codChart.extend J p)).1, (A (h.codChart.extend J p)).2) := fun _ => rfl
  have hΨ_source : ∀ p : N, p ∈ Ψ.source ↔
      p ∈ h.codChart.source ∧ h.codChart.extend J p ∈ O := fun _ => Iff.rfl
  -- In this chart the immersion normal form says that `f` is the standard inclusion.
  have key : ∀ y ∈ h.domChart.source, Ψ (f y) = (h.domChart y, 0) := by
    intro y hy
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hw
    rw [hΨ_apply, hw, hAL, OpenPartialHomeomorph.extend_coe, Function.comp_apply, I.left_inv]
  -- Restrict to the part of the domain chart that the straightened chart sees, and cut that part of
  -- the image out of `range f` by an open set, using that `f` is an embedding.
  set D : Set M := h.domChart.source ∩ f ⁻¹' Ψ.source
  have hD : IsOpen D := h.domChart.open_source.inter (Ψ.open_source.preimage hf.continuous)
  obtain ⟨W, hW, hWf⟩ := hf.isInducing.isOpen_iff.1 hD
  have hmemW : ∀ y : M, f y ∈ W ↔ y ∈ D := fun y => by rw [← hWf]; exact Iff.rfl
  set V : Set N := (Ψ.source ∩ Ψ ⁻¹' (h.domChart.target ×ˢ (univ : Set F))) ∩ W
  have hVopen : IsOpen V :=
    (Ψ.isOpen_inter_preimage (h.domChart.open_target.prod isOpen_univ)).inter hW
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hfx : f x ∈ Ψ.source := (hΨ_source _).2 ⟨h.mem_codChart_source, hxO⟩
  have hfxV : f x ∈ V := by
    refine ⟨⟨hfx, ?_⟩, (hmemW x).2 ⟨hx, hfx⟩⟩
    rw [mem_preimage, key x hx]
    exact ⟨h.domChart.map_source hx, mem_univ _⟩
  refine ⟨Ψ.restrOpen V hVopen, ⟨hfx, hfxV⟩, isSliceChart_iff.2 fun p hp => ?_⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hp
  simp only [OpenPartialHomeomorph.coe_restrOpen]
  constructor
  · -- A point of the image lying in `W` comes from `D`, hence lands on the slice.
    rintro ⟨y, rfl⟩
    rw [key y ((hmemW y).1 hp.2.2).1]
    exact ⟨mem_univ _, rfl⟩
  · -- Conversely a point of the slice lying over the domain chart's target is such an image.
    rintro ⟨-, hps⟩
    have hpt : (Ψ p).1 ∈ h.domChart.target := hp.2.1.2.1
    have hy : h.domChart.symm (Ψ p).1 ∈ h.domChart.source := h.domChart.map_target hpt
    obtain ⟨hpsrc, hpO⟩ := (hΨ_source p).1 hp.1
    have hvI : (A (h.codChart.extend J p)).1 ∈ range I := (hA _ hpO).1 (by
      rw [OpenPartialHomeomorph.extend_coe]
      exact mem_range_self _)
    have hAv : A (h.codChart.extend J p) = (I (Ψ p).1, 0) := by
      rw [hΨ_apply, I.right_inv hvI, ← (hps : (Ψ p).2 = 0), hΨ_apply]
    have hmem : I (Ψ p).1 ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target']
      exact mem_image_of_mem _ hpt
    have hfy : h.codChart.extend J (f (h.domChart.symm (Ψ p).1)) = h.codChart.extend J p := by
      have hw := h.writtenInCharts hmem
      simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm, I.left_inv] at hw
      apply A.injective
      rw [hw, hAL, hAv]
    refine ⟨_, (h.codChart.extend J).injOn ?_ ?_ hfy⟩
    · rw [h.codChart.extend_source]
      exact h.source_subset_preimage_source hy
    · rwa [h.codChart.extend_source]

end Straightening

section HalfSpace

/-- **The shear straightening the half-spaces.** If the linear equivalence
`L : ℝᵏ × F ≃L ℝᵐ` reads the boundary coordinate of `ℝᵐ` on `ℝᵏ × {0}` as a positive multiple
`c • u 0` of the boundary coordinate of `ℝᵏ`, then `L⁻¹` followed by the shear
`(u, w) ↦ (u + c⁻¹ (L (0, w)) 0 • e₀, w)` still reads `L (u, 0)` as `(u, 0)` and carries the
half-space `range (𝓡∂ m)` onto `range (𝓡∂ k) × F`. -/
private theorem exists_straightening_of_eq_mul_apply_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k m : ℕ} [NeZero k] [NeZero m]
    (L : (EuclideanSpace ℝ (Fin k) × F) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) {c : ℝ} (hc : 0 < c)
    (hL : ∀ u, L (u, 0) 0 = c * u 0) :
    ∃ A : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × F),
      (∀ u, A (L (u, 0)) = (u, 0)) ∧ ∀ v, (v ∈ range (𝓡∂ m) ↔ (A v).1 ∈ range (𝓡∂ k)) := by
  set g : F →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (c⁻¹ • (EuclideanSpace.proj (0 : Fin m)).comp
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ F))).smulRight
      (EuclideanSpace.single 0 1)
  have hg : ∀ w, g w 0 = c⁻¹ * L (0, w) 0 := fun w => by simp [g]
  -- The shear `(u, w) ↦ (u + g w, w)`, built from `ContinuousLinearEquiv.skewProd` by swapping.
  set S : (EuclideanSpace ℝ (Fin k) × F) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × F) :=
    ((ContinuousLinearEquiv.prodComm ℝ _ F).trans
      ((ContinuousLinearEquiv.refl ℝ F).skewProd (ContinuousLinearEquiv.refl ℝ _) g)).trans
      (ContinuousLinearEquiv.prodComm ℝ F _)
  have hS : ∀ z, S z = (z.1 + g z.2, z.2) := fun z => by
    simp [S, ContinuousLinearEquiv.skewProd_apply]
  refine ⟨L.symm.trans S, fun u => ?_, fun v => ?_⟩
  · rw [ContinuousLinearEquiv.trans_apply, L.symm_apply_apply, hS, map_zero, add_zero]
  -- The boundary coordinate of `v` is `c` times that of its straightened image.
  have hsplit : v 0 = c * (S (L.symm v)).1 0 := by
    -- Split `v` through `L` into its tangential and complementary parts.
    calc v 0 = (L ((L.symm v).1, 0) + L (0, (L.symm v).2)) 0 := by
          rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, L.apply_symm_apply]
      _ = c * (S (L.symm v)).1 0 := by
          simp only [hS, PiLp.add_apply, hL, hg]
          field_simp
  simp only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
    ContinuousLinearEquiv.trans_apply, hsplit]
  exact mul_nonneg_iff_of_pos_left hc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k m : ℕ} [NeZero k] [NeZero m]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace k) M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace m) N]
  {n : ℕ∞ω} {f : M → N}

/-- **The slice chart of a neat embedding.** Let `f` be a topological embedding between charted
spaces modelled on Euclidean half-spaces, which is a `C^n` immersion at `x`, `n ≠ 0`, with
complement `F` and meets the boundary of `N` exactly in the boundary of `M`. Then around `f x`
there is an ambient chart valued in `EuclideanHalfSpace k × F` carrying `Set.range f` exactly onto
`EuclideanHalfSpace k × {0}`. -/
theorem exists_isSliceChart_of_isImmersionAtOfComplement_of_preimage_boundary (hn : n ≠ 0)
    (hf : IsEmbedding f) (hb : f ⁻¹' (𝓡∂ m).boundary N = (𝓡∂ k).boundary M) {x : M}
    (h : IsImmersionAtOfComplement F (𝓡∂ k) (𝓡∂ m) n f x) :
    ∃ Φ : OpenPartialHomeomorph N (EuclideanHalfSpace k × F), f x ∈ Φ.source ∧
      IsSliceChart Φ (univ ×ˢ ({0} : Set F)) (range f) := by
  set T := (h.domChart.extend (𝓡∂ k)).target
  set L := h.equiv
  -- Neatness, read in the charts of the immersion: a point of the domain chart is interior exactly
  -- when its image is.
  have hint : ∀ y : M, ((𝓡∂ m).IsInteriorPoint (f y) ↔ (𝓡∂ k).IsInteriorPoint y) := by
    intro y
    have hy := congrArg (y ∈ ·) hb
    simp only [mem_preimage, eq_iff_iff] at hy
    rw [(𝓡∂ m).isInteriorPoint_iff_not_isBoundaryPoint,
      (𝓡∂ k).isInteriorPoint_iff_not_isBoundaryPoint]
    exact not_congr hy
  have hsymm : ∀ u ∈ T, (h.domChart.extend (𝓡∂ k)).symm u ∈ h.domChart.source := fun u hu => by
    rw [← h.domChart.extend_source (I := 𝓡∂ k)]
    exact (h.domChart.extend (𝓡∂ k)).map_target hu
  have hcoord : ∀ u ∈ T, h.codChart.extend (𝓡∂ m) (f ((h.domChart.extend (𝓡∂ k)).symm u)) =
      L (u, 0) := fun u hu => h.writtenInCharts hu
  have hiff : ∀ u ∈ T, (0 < u 0 ↔ 0 < L (u, 0) 0) := by
    intro u hu
    have hy := hsymm u hu
    have hu0 : h.domChart.extend (𝓡∂ k) ((h.domChart.extend (𝓡∂ k)).symm u) 0 = u 0 := by
      rw [(h.domChart.extend (𝓡∂ k)).right_inv hu]
    -- The chart extensions read the half-space boundary coordinate of the charts, definitionally.
    rw [← hcoord u hu, ← hu0]
    exact (ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff_of_mem_maximalAtlas hn
      h.domChart_mem_maximalAtlas hy).symm.trans <| (hint _).symm.trans <|
      ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff_of_mem_maximalAtlas hn
        h.codChart_mem_maximalAtlas (h.source_subset_preimage_source hy)
  have hnonneg : ∀ u ∈ T, 0 ≤ L (u, 0) 0 := by
    intro u hu
    have hmem : L (u, 0) ∈ range (𝓡∂ m) := by
      rw [← hcoord u hu, OpenPartialHomeomorph.extend_coe]
      exact mem_range_self _
    rwa [range_modelWithCornersEuclideanHalfSpace] at hmem
  set p := h.domChart.extend (𝓡∂ k) x
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hpT : p ∈ T := (h.domChart.extend (𝓡∂ k)).map_source (by rwa [h.domChart.extend_source])
  have hxp : (h.domChart.extend (𝓡∂ k)).symm p = x := (h.domChart.extend (𝓡∂ k)).left_inv
    (by rwa [h.domChart.extend_source])
  have hfx : h.codChart.extend (𝓡∂ m) (f x) = L (p, 0) := by rw [← hcoord p hpT, hxp]
  by_cases hp : 0 < p 0
  · -- At an interior point both half-space conditions hold strictly near the point, and `L⁻¹`
    -- straightens the ambient chart there.
    refine exists_isSliceChart_of_isImmersionAtOfComplement_of_straightening hf h L.symm
      (fun u => L.symm_apply_apply _) (O := {v | 0 < v 0} ∩ {v | 0 < (L.symm v).1 0}) ?_ ?_ ?_
    · exact (isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt continuous_const (by fun_prop))
    · rw [hfx]
      exact ⟨(hiff p hpT).1 hp, by simpa using hp⟩
    · rintro v ⟨hv, hv'⟩
      simp only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
      exact iff_of_true hv.le hv'.le
  · -- At a boundary point the ambient boundary coordinate pulls back to a positive multiple of the
    -- domain's, and a shear of `L⁻¹` straightens the ambient chart everywhere.
    have hp0 : p 0 = 0 := by
      have hpr : p ∈ range (𝓡∂ k) := h.domChart.extend_target_subset_range hpT
      rw [range_modelWithCornersEuclideanHalfSpace] at hpr
      exact le_antisymm (not_lt.1 hp) hpr
    set ν : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin m)).comp
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F))
    have hν : ∀ u, ν u = L (u, 0) 0 := fun _ => rfl
    have hνp : ν p = 0 := by
      rw [hν]
      exact le_antisymm (not_lt.1 fun h' => hp ((hiff p hpT).2 h')) (hnonneg p hpT)
    have hT : T ∈ 𝓝[{y | 0 ≤ y 0}] p := by
      rw [← range_modelWithCornersEuclideanHalfSpace]
      exact h.domChart.extend_target_mem_nhdsWithin hx
    obtain ⟨c, hc, hνc⟩ := ContinuousLinearMap.exists_pos_eq_mul_apply_zero_of_eventually_nonneg
      ν hp0 hνp (eventually_of_mem hT hnonneg) (eventually_of_mem hT fun u hu => (hiff u hu).1)
    replace hνc : ∀ u, L (u, 0) 0 = c * u 0 := fun u => (hν u).symm.trans (hνc u)
    obtain ⟨A, hAL, hA⟩ := exists_straightening_of_eq_mul_apply_zero L hc hνc
    exact exists_isSliceChart_of_isImmersionAtOfComplement_of_straightening hf h A hAL
      isOpen_univ (mem_univ _) fun v _ => hA v

/-- **A neat `C^n` immersion between half-space charted spaces is locally flat** if it is a
topological embedding and `n ≠ 0`. The tangential model is the half-space `EuclideanHalfSpace k`,
so that boundary points of `M` are flattened onto the boundary of the slice, and the
complementary model is the
complement `F` of the immersion. -/
theorem IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding_of_preimage_boundary (hn : n ≠ 0)
    (h : IsImmersionOfComplement F (𝓡∂ k) (𝓡∂ m) n f) (hf : IsEmbedding f)
    (hb : f ⁻¹' (𝓡∂ m).boundary N = (𝓡∂ k).boundary M) :
    IsLocallyFlat (EuclideanHalfSpace k) F f :=
  isLocallyFlat_iff_isSliceEmbedding.2 ⟨hf, fun x =>
    exists_isSliceChart_of_isImmersionAtOfComplement_of_preimage_boundary hn hf hb (h x)⟩

/-- **A neat `C^n` embedding between half-space charted spaces is locally flat**, `n ≠ 0`: if `f`
meets the boundary of `N` exactly in the boundary of `M`, it is locally flat with tangential model
the half-space `EuclideanHalfSpace k` and complementary model the complement chosen by the
immersion. -/
theorem IsLocallyFlat.of_isSmoothEmbedding_of_preimage_boundary (hn : n ≠ 0)
    (h : IsSmoothEmbedding (𝓡∂ k) (𝓡∂ m) n f)
    (hb : f ⁻¹' (𝓡∂ m).boundary N = (𝓡∂ k).boundary M) :
    IsLocallyFlat (EuclideanHalfSpace k) h.isImmersion.complement f :=
  .of_isImmersionOfComplement_of_isEmbedding_of_preimage_boundary hn
    h.isImmersion.isImmersionOfComplement_complement h.isEmbedding hb

end HalfSpace

end TauCeti
