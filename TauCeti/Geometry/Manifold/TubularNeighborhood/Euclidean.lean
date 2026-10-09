/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Basic

/-!
# Tubular neighbourhoods in a Euclidean space

Let `f : M → V` be a `C²` embedding of a compact boundaryless manifold into a finite-dimensional
real inner product space. Its normal space at `x` is the orthogonal complement of the range of the
differential of `f` at `x`, and its normal vectors of length less than `ε` form the set
`TauCeti.normalTube I f ε ⊆ M × V`. This file proves the tubular neighbourhood theorem in this
setting: for some `ε > 0` the map `(x, v) ↦ f x + v` is an open embedding of that normal tube into
`V`. Its image is therefore an open neighbourhood of `f '' M` which the normal tube identifies
with a neighbourhood of the zero section of the normal bundle. Packaged with the subspace
topology on the total space of the normal bundle, this is the data
`TauCeti.IsTubularNeighborhood` asks for. Only compact `M` is treated, with a constant radius;
for noncompact submanifolds the radius has to be a positive continuous function on `M`.

## Main definitions

* `TauCeti.normalSubspace I f x`: the orthogonal complement in `V` of the range of the
  differential of `f` at `x`.
* `TauCeti.normalTube I f ε`: the normal vectors of length less than `ε`, as a subset of `M × V`.
* `TauCeti.normalTubeOfRadius I f r`: the normal vectors shorter than a radius `r` depending on
  their base point.

## Main results

* `TauCeti.exists_isOpenEmbedding_normalTube`: the tubular neighbourhood theorem for a compact
  `C²` embedded submanifold of a Euclidean space.
* `TauCeti.exists_isTubularNeighborhood_normalBundle`: the same statement as
  `TauCeti.IsTubularNeighborhood` data on the total space of the normal bundle.

## References

The proof follows Lee's.

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 4, Theorem 6.3.
-/

public section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- With `W₀` the normal space of `g` at `u₀` and `Q u` the orthogonal projection onto the normal
space at `u`, the map `(u, w) ↦ g u + Q u w` on `E × W₀` is a local homeomorphism at `(u₀, 0)`. Its
derivative there is the isomorphism `(du, dw) ↦ Dg du + dw` from `E × W₀` to `V`. -/
private theorem exists_openPartialHomeomorph_normal {g : E → V} {u₀ : E}
    (hg : ContDiffAt ℝ 2 g u₀) (hinj : Injective (fderiv ℝ g u₀)) :
    ∃ h : OpenPartialHomeomorph (E × (fderiv ℝ g u₀).rangeᗮ) V, (u₀, 0) ∈ h.source ∧
      ∀ q, h q = g q.1 + (fderiv ℝ g q.1).rangeᗮ.starProjection q.2 := by
  let A : E → E →L[ℝ] V := fderiv ℝ g
  set W₀ := (A u₀).rangeᗮ
  let Q : E → V →L[ℝ] V := fun u => (A u).rangeᗮ.starProjection
  have hQ₀ : ContDiffAt ℝ 1 Q u₀ :=
    (hg.fderiv_right (m := 1) (by norm_num)).starProjection_orthogonal_range hinj
  have hQW : ∀ w : W₀, Q u₀ w = w := fun w => Submodule.starProjection_eq_self_iff.mpr w.2
  let Ψ : E × W₀ → V := fun q => g q.1 + Q q.1 q.2
  have hΨ : ContDiffAt ℝ 1 Ψ (u₀, 0) :=
    ((hg.of_le (by norm_num)).comp (u₀, (0 : W₀)) contDiffAt_fst).add
      ((hQ₀.comp (u₀, (0 : W₀)) contDiffAt_fst).clm_apply
        (W₀.subtypeL.contDiff.contDiffAt.comp _ contDiffAt_snd))
  let D : E × W₀ →L[ℝ] V :=
    (A u₀).comp (ContinuousLinearMap.fst ℝ E W₀) + W₀.subtypeL.comp (ContinuousLinearMap.snd ℝ E W₀)
  -- `D` is injective since the range of `A u₀` meets `W₀` only in zero, and bijective by counting
  -- dimensions.
  have hDinj : Injective D := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, w⟩ h
    simp only [D, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply] at h
    have hx : A u₀ x ∈ (A u₀).range ⊓ W₀ := by
      refine ⟨LinearMap.mem_range_self _ x, ?_⟩
      rw [eq_neg_of_add_eq_zero_left h]
      exact W₀.neg_mem w.2
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hx
    obtain rfl : x = 0 := hinj (by simpa [A] using hx)
    simp only [map_zero, zero_add, ZeroMemClass.coe_eq_zero] at h
    simp [h]
  have hDsurj : Surjective D := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hDinj
    rw [Module.finrank_prod, LinearMap.finrank_orthogonal_range_of_injective hinj]
    have := Submodule.finrank_le (A u₀).range
    rw [LinearMap.finrank_range_of_inj hinj] at this
    omega
  let Deq : (E × W₀) ≃L[ℝ] V :=
    (LinearEquiv.ofBijective (D : E × W₀ →ₗ[ℝ] V) ⟨hDinj, hDsurj⟩).toContinuousLinearEquiv
  have hΨD : HasFDerivAt Ψ (Deq : E × W₀ →L[ℝ] V) (u₀, 0) := by
    have h1 : HasFDerivAt (fun q : E × W₀ => g q.1)
        ((A u₀).comp (ContinuousLinearMap.fst ℝ E W₀)) (u₀, 0) :=
      (hg.differentiableAt (by norm_num)).hasFDerivAt.comp (u₀, (0 : W₀)) hasFDerivAt_fst
    have hc : HasFDerivAt (fun q : E × W₀ => Q q.1)
        ((fderiv ℝ Q u₀).comp (ContinuousLinearMap.fst ℝ E W₀)) (u₀, 0) :=
      HasFDerivAt.comp (g := Q) (f := Prod.fst) (u₀, (0 : W₀))
        (hQ₀.differentiableAt one_ne_zero).hasFDerivAt hasFDerivAt_fst
    have hu : HasFDerivAt (fun q : E × W₀ => (q.2 : V))
        (W₀.subtypeL.comp (ContinuousLinearMap.snd ℝ E W₀)) (u₀, 0) :=
      W₀.subtypeL.hasFDerivAt.comp (u₀, (0 : W₀)) hasFDerivAt_snd
    convert h1.add (hc.clm_apply hu) using 1
    ext p <;> simp [Deq, D, hQW]
  exact ⟨hΨ.toOpenPartialHomeomorph Ψ hΨD one_ne_zero,
    hΨ.mem_toOpenPartialHomeomorph_source hΨD one_ne_zero, fun _ => rfl⟩

/-- **Local tubular neighbourhood theorem.** For a map `g : E → V` which is `C²` at `u₀` with
injective derivative there, the normal map `(u, v) ↦ g u + v`, restricted to the normal vectors
of length less than `δ` at points of a neighbourhood `s` of `u₀`, is injective and sends relatively
open sets to open sets. -/
private theorem exists_injOn_isOpen_image_normal {g : E → V} {u₀ : E}
    (hg : ContDiffAt ℝ 2 g u₀) (hinj : Injective (fderiv ℝ g u₀)) :
    ∃ s ∈ 𝓝 u₀, ∃ δ > 0,
      InjOn (fun p : E × V => g p.1 + p.2)
        {p | p.1 ∈ s ∧ p.2 ∈ (fderiv ℝ g p.1).rangeᗮ ∧ ‖p.2‖ < δ} ∧
      ∀ O : Set (E × V), IsOpen O → IsOpen ((fun p : E × V => g p.1 + p.2) ''
        (O ∩ {p | p.1 ∈ s ∧ p.2 ∈ (fderiv ℝ g p.1).rangeᗮ ∧ ‖p.2‖ < δ})) := by
  let A : E → E →L[ℝ] V := fderiv ℝ g
  set W₀ := (A u₀).rangeᗮ
  -- `Q u` is the orthogonal projection onto the normal space at `u`, and `R u` its compression
  -- to the normal space `W₀` at `u₀`.
  let Q : E → V →L[ℝ] V := fun u => (A u).rangeᗮ.starProjection
  let R : E → W₀ →L[ℝ] W₀ := fun u => W₀.orthogonalProjectionOnto ∘L Q u ∘L W₀.subtypeL
  have hQW : ∀ w : W₀, Q u₀ w = w := fun w => Submodule.starProjection_eq_self_iff.mpr w.2
  have hR₀ : R u₀ = 1 := by
    ext w
    simp [R, hQW]
  have hQ₀ : ContDiffAt ℝ 1 Q u₀ :=
    (hg.fderiv_right (m := 1) (by norm_num)).starProjection_orthogonal_range hinj
  have hRc : ContinuousAt R u₀ :=
    continuousAt_const.clm_comp (hQ₀.continuousAt.clm_comp continuousAt_const)
  have hev : ∀ᶠ u in 𝓝 u₀, ContDiffAt ℝ 2 g u ∧ Injective (A u) ∧ IsUnit (R u) := by
    have h2 : ∀ᶠ u in 𝓝 u₀, Injective (A u) :=
      (hg.fderiv_right (m := 1) (by norm_num)).continuousAt.preimage_mem_nhds
        (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)
    have hRu₀ : IsUnit (R u₀) := hR₀ ▸ isUnit_one
    have h3 : ∀ᶠ u in 𝓝 u₀, IsUnit (R u) :=
      hRc.preimage_mem_nhds ((Units.isOpen (R := W₀ →L[ℝ] W₀)).mem_nhds hRu₀)
    exact (hg.eventually (by simp)).and (h2.and h3)
  -- The normal map, with fibres parametrized by `W₀`, is a local homeomorphism `h`.
  obtain ⟨h, hsrc, hΨh⟩ := exists_openPartialHomeomorph_normal hg hinj
  -- `ρ` inverts `(u, w) ↦ (u, Q u w)` on normal vectors, and is continuous at `(u₀, 0)`.
  let ρ : E × V → E × W₀ := fun p => (p.1, Ring.inverse (R p.1) (W₀.orthogonalProjectionOnto p.2))
  have hρc : ContinuousAt ρ (u₀, 0) := by
    refine continuousAt_fst.prodMk (ContinuousAt.clm_apply ?_
      (W₀.orthogonalProjectionOnto.continuous.comp continuous_snd).continuousAt)
    have hinvc : ContinuousAt Ring.inverse (R u₀) := by
      rw [hR₀]
      exact NormedRing.inverse_continuousAt (R := W₀ →L[ℝ] W₀) 1
    exact ContinuousAt.comp (x := ((u₀, 0) : E × V)) hinvc
      (ContinuousAt.comp (x := ((u₀, 0) : E × V)) hRc continuousAt_fst)
  have hρ₀ : ρ (u₀, 0) = (u₀, 0) := by simp [ρ]
  have hρΩ : ρ ⁻¹' h.source ∈ 𝓝 (u₀, (0 : V)) :=
    hρc.preimage_mem_nhds (by rw [hρ₀]; exact h.open_source.mem_nhds hsrc)
  obtain ⟨s₁, hs₁, t, ht, hst⟩ := mem_nhds_prod_iff.mp hρΩ
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
  set s := interior (s₁ ∩ {u | ContDiffAt ℝ 2 g u ∧ Injective (A u) ∧ IsUnit (R u)})
  have hs : s ∈ 𝓝 u₀ := interior_mem_nhds.mpr (inter_mem hs₁ hev)
  have hss : ∀ {u}, u ∈ s → u ∈ s₁ ∧ ContDiffAt ℝ 2 g u ∧ Injective (A u) ∧ IsUnit (R u) :=
    fun hu => interior_subset
      (s := s₁ ∩ {u | ContDiffAt ℝ 2 g u ∧ Injective (A u) ∧ IsUnit (R u)}) hu
  have hkey : ∀ p : E × V, p.1 ∈ s → p.2 ∈ (A p.1).rangeᗮ → ‖p.2‖ < δ →
      ρ p ∈ h.source ∧ Q p.1 (ρ p).2 = p.2 := by
    rintro ⟨u, v⟩ hu hv hvδ
    obtain ⟨hu₁, -, hAu, hRu⟩ := hss hu
    refine ⟨hst ⟨hu₁, hδt (mem_ball_zero_iff.mpr hvδ)⟩, ?_⟩
    refine Submodule.starProjection_inverse_apply ?_ hRu hv
    rw [LinearMap.finrank_orthogonal_range_of_injective hinj,
      LinearMap.finrank_orthogonal_range_of_injective hAu]
  have hΨρ : ∀ p : E × V, Q p.1 (ρ p).2 = p.2 → h (ρ p) = g p.1 + p.2 := by
    intro p hp
    rw [hΨh]
    exact congrArg (g p.1 + ·) hp
  refine ⟨s, hs, δ, hδ, ?_, ?_⟩
  · rintro p ⟨hu, hv, hvδ⟩ p' ⟨hu', hv', hvδ'⟩ heq
    obtain ⟨hρp, hQp⟩ := hkey p hu hv hvδ
    obtain ⟨hρp', hQp'⟩ := hkey p' hu' hv' hvδ'
    have hρ : ρ p = ρ p' := h.injOn hρp hρp' (by rw [hΨρ p hQp, hΨρ p' hQp']; exact heq)
    have h1 : p.1 = p'.1 := by simpa [ρ] using congrArg Prod.fst hρ
    refine Prod.ext h1 ?_
    rw [← hQp, ← hQp', h1, hρ]
  · intro O hO
    -- The image is the image under `h` of an open subset of its source.
    let θ : E × W₀ → E × V := fun q => (q.1, Q q.1 q.2)
    have hθc : ContinuousOn θ (h.source ∩ s ×ˢ univ) := by
      rintro ⟨u, w⟩ ⟨-, hu, -⟩
      obtain ⟨-, hgu, hAu, -⟩ := hss hu
      refine (continuousAt_fst.prodMk ?_).continuousWithinAt
      have hQu : ContDiffAt ℝ 1 Q u :=
        (hgu.fderiv_right (m := 1) (by norm_num)).starProjection_orthogonal_range hAu
      exact ContinuousAt.clm_apply (ContinuousAt.comp (g := Q) (f := Prod.fst) (x := (u, w))
        hQu.continuousAt continuousAt_fst)
        (W₀.subtypeL.continuous.comp continuous_snd).continuousAt
    have himage : (fun p : E × V => g p.1 + p.2) ''
        (O ∩ {p | p.1 ∈ s ∧ p.2 ∈ (fderiv ℝ g p.1).rangeᗮ ∧ ‖p.2‖ < δ}) =
        h '' ((h.source ∩ s ×ˢ univ) ∩ θ ⁻¹' (O ∩ univ ×ˢ Metric.ball 0 δ)) := by
      ext y
      constructor
      · rintro ⟨p, ⟨hpO, hu, hv, hvδ⟩, rfl⟩
        obtain ⟨hρp, hQp⟩ := hkey p hu hv hvδ
        refine ⟨ρ p, ⟨⟨hρp, hu, mem_univ _⟩, ?_⟩, hΨρ p hQp⟩
        have hθρ : θ (ρ p) = p := Prod.ext rfl hQp
        rw [mem_preimage, hθρ]
        exact ⟨hpO, mem_univ _, mem_ball_zero_iff.mpr hvδ⟩
      · rintro ⟨⟨u, w⟩, ⟨⟨-, hu, -⟩, hθO, -, hθδ⟩, rfl⟩
        refine ⟨θ (u, w), ⟨hθO, hu, Submodule.starProjection_apply_mem _ _,
          mem_ball_zero_iff.mp hθδ⟩, ?_⟩
        rw [hΨh]
    rw [himage]
    exact h.isOpen_image_of_subset_source
      (hθc.isOpen_inter_preimage (h.open_source.inter (isOpen_interior.prod isOpen_univ))
        (hO.inter (isOpen_univ.prod Metric.isOpen_ball))) fun q hq => hq.1.1

end Local

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- The normal space of a map `f : M → V` into a real inner product space at `x`: the orthogonal
complement in `V` of the range of the differential of `f` at `x`. It realizes the quotient normal
space `TauCeti.SmoothEmbedding.NormalSpace` as a subspace of `V`, using the inner product. -/
noncomputable def normalSubspace (f : M → V) (x : M) : Submodule ℝ V :=
  (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V).rangeᗮ

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- A normal space is complete when the ambient inner product space is complete. -/
instance instCompleteSpaceNormalSubspace [CompleteSpace V] (f : M → V) (x : M) :
    CompleteSpace (normalSubspace I f x) := by
  unfold normalSubspace
  exact (Submodule.isClosed_orthogonal (𝕜 := ℝ) (E := V)
    (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V).range).completeSpace_coe

omit [FiniteDimensional ℝ E] in
/-- At an immersion point, the dimension of the normal space is the codimension. -/
theorem finrank_normalSubspace {f : M → V} {x : M}
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) :
    Module.finrank ℝ (normalSubspace I f x) = Module.finrank ℝ V - Module.finrank ℝ E := by
  unfold normalSubspace
  exact LinearMap.finrank_orthogonal_range_of_injective (V := V)
    (A := (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V).toLinearMap) himm

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- A vector is normal to `f` at `x` exactly when it is orthogonal to every value of the
differential of `f` at `x`. -/
@[simp]
theorem mem_normalSubspace_iff {f : M → V} {x : M} {v : V} :
    v ∈ normalSubspace I f x ↔ ∀ u : E, ⟪v, (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V) u⟫_ℝ = 0 :=
  ⟨fun h u => Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ u) h,
    fun h _ ⟨u, hu⟩ => hu ▸ inner_eq_zero_symm.mp (h u)⟩

variable (I) in
/-- The normal vectors along `f : M → V` of length less than `ε`, as a subset of `M × V`. -/
def normalTube (f : M → V) (ε : ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ < ε}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
@[simp]
theorem mem_normalTube {f : M → V} {ε : ℝ} {p : M × V} :
    p ∈ normalTube I f ε ↔ p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ < ε :=
  Iff.rfl

variable (I) in
/-- The normal vectors along `f` shorter than a radius depending on their base point. -/
def normalTubeOfRadius (f : M → V) (r : M → ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ < r p.1}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
@[simp]
theorem mem_normalTubeOfRadius {f : M → V} {r : M → ℝ} {p : M × V} :
    p ∈ normalTubeOfRadius I f r ↔ p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ < r p.1 :=
  Iff.rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- A constant radius gives the usual normal tube. -/
@[simp]
theorem normalTubeOfRadius_const (f : M → V) (ε : ℝ) :
    normalTubeOfRadius I f (fun _ => ε) = normalTube I f ε := by
  ext p
  simp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- Shrinking a variable normal tube to a smaller continuous radius preserves the open
embedding of normal addition. No regularity of the original radius is needed. -/
theorem isOpenEmbedding_normalTubeOfRadius_of_le {f : M → V} {r R : M → ℝ}
    (hr : Continuous r) (hrR : ∀ x, r x ≤ R x)
    (h : IsOpenEmbedding ((normalTubeOfRadius I f R).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
      fun p : M × V => f p.1 + p.2) := by
  have hsub : normalTubeOfRadius I f r ⊆ normalTubeOfRadius I f R := fun p hp =>
    mem_normalTubeOfRadius.mpr ⟨(mem_normalTubeOfRadius.mp hp).1,
      (mem_normalTubeOfRadius.mp hp).2.trans_le (hrR p.1)⟩
  apply h.comp (IsOpenEmbedding.inclusion hsub ?_)
  convert isOpen_lt ((continuous_norm.comp continuous_snd).comp
    (continuous_subtype_val : Continuous
      (Subtype.val : normalTubeOfRadius I f R → M × V)))
    ((hr.comp continuous_fst).comp continuous_subtype_val) using 1
  ext p
  simp only [mem_preimage, mem_normalTubeOfRadius, mem_ofPred_eq, Function.comp_apply]
  exact and_iff_right (mem_normalTubeOfRadius.mp p.2).1

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- At a point `y` of the source of a chart, the normal space of `f` is the orthogonal complement
of the range of the derivative of the coordinate expression of `f`. -/
theorem normalSubspace_eq_of_mem_source [IsManifold I 1 M] {f : M → V} {x y : M}
    (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    normalSubspace I f y = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)).rangeᗮ := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [normalSubspace, mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL]
  congr 1
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr L.surjective)

/-- The local tubular neighbourhood theorem on `M`: around every point there is an open set `W`
and a radius `δ` such that the normal map is injective, and sends relatively open sets to open
sets, on the normal vectors of length less than `δ` at points of `W`. -/
theorem exists_injOn_isOpen_image_normalTube [I.Boundaryless] [IsManifold I 2 M]
    {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f) (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (x₀ : M) :
    ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧ ∃ δ > 0,
      InjOn (fun p : M × V => f p.1 + p.2) {p | p.1 ∈ W ∧ p ∈ normalTube I f δ} ∧
      ∀ O : Set (M × V), IsOpen O →
        IsOpen ((fun p : M × V => f p.1 + p.2) '' (O ∩ {p | p.1 ∈ W ∧ p ∈ normalTube I f δ})) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  set e := extChartAt I x₀
  set g : E → V := f ∘ e.symm
  have hgd : ContDiffOn ℝ 2 g e.target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))
  have hgat : ∀ u ∈ e.target, ContDiffAt ℝ 2 g u := fun u hu =>
    hgd.contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hu)
  have hdiff : ∀ y ∈ e.source, DifferentiableAt ℝ g (e y) := fun y hy =>
    (hgat _ (e.map_source hy)).differentiableAt (by norm_num)
  have hnormal : ∀ y ∈ e.source, normalSubspace I f y = (fderiv ℝ g (e y)).rangeᗮ :=
    fun y hy => normalSubspace_eq_of_mem_source hy (hdiff y hy)
  have hx₀ : x₀ ∈ e.source := mem_extChartAt_source x₀
  obtain ⟨s, hs, δ, hδ, hinjOn, hopen⟩ := exists_injOn_isOpen_image_normal
    (hgat _ (e.map_source hx₀))
    (fderiv_comp_extChartAt_symm_injective hx₀ (hdiff x₀ hx₀) (himm x₀))
  -- Transport the local statement along the chart `e × id`.
  set s' := interior s ∩ e.target
  have hs'o : IsOpen s' := isOpen_interior.inter (isOpen_extChartAt_target x₀)
  set W := e.source ∩ e ⁻¹' s'
  have hWo : IsOpen W :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) hs'o
  have hmem : ∀ p : M × V, p.1 ∈ W ∧ p ∈ normalTube I f δ →
      (e p.1, p.2) ∈ {q : E × V | q.1 ∈ s ∧ q.2 ∈ (fderiv ℝ g q.1).rangeᗮ ∧ ‖q.2‖ < δ} := by
    rintro ⟨y, v⟩ ⟨⟨hy, hys⟩, hv, hvδ⟩
    exact ⟨interior_subset hys.1, by rw [← hnormal y hy]; exact hv, hvδ⟩
  have hΦ : ∀ p : M × V, p.1 ∈ e.source → f p.1 + p.2 = g (e p.1) + p.2 := fun p hp => by
    simp [g, e.left_inv hp]
  refine ⟨W, hWo, ⟨hx₀, mem_interior_iff_mem_nhds.mpr hs, e.map_source hx₀⟩, δ, hδ, ?_, ?_⟩
  · rintro p hp p' hp' heq
    have h := hinjOn (hmem p hp) (hmem p' hp')
      (by simpa only [hΦ p hp.1.1, hΦ p' hp'.1.1] using heq)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (e.injOn hp.1.1 hp'.1.1 h.1) h.2
  · intro O hO
    set O' : Set (E × V) := s' ×ˢ univ ∩ (Prod.map e.symm id) ⁻¹' O
    have hO' : IsOpen O' :=
      (((continuousOn_extChartAt_symm x₀).mono inter_subset_right).prodMap
        continuousOn_id).isOpen_inter_preimage (hs'o.prod isOpen_univ) hO
    convert hopen O' hO' using 1
    ext z
    constructor
    · rintro ⟨p, ⟨hpO, hp⟩, rfl⟩
      refine ⟨(e p.1, p.2), ⟨⟨⟨hp.1.2, mem_univ _⟩, ?_⟩, hmem p hp⟩, (hΦ p hp.1.1).symm⟩
      simpa [e.left_inv hp.1.1] using hpO
    · rintro ⟨⟨u, v⟩, ⟨⟨⟨hu, -⟩, huO⟩, -, hv, hvδ⟩, rfl⟩
      have hut : u ∈ e.target := hu.2
      refine ⟨(e.symm u, v), ⟨huO, ⟨e.map_target hut, by
        rw [mem_preimage, e.right_inv hut]; exact hu⟩, ?_, hvδ⟩, ?_⟩
      · rw [hnormal _ (e.map_target hut), e.right_inv hut]
        exact hv
      · simp [g]

/-- **Tubular neighbourhood theorem** for a compact `C²` embedded submanifold of a Euclidean
space: for some `ε > 0`, the map `(x, v) ↦ f x + v` is an open embedding of the normal vectors of
length less than `ε` into `V`. -/
theorem exists_isOpenEmbedding_normalTube [I.Boundaryless] [IsManifold I 2 M] [CompactSpace M]
    {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f) :
    ∃ ε > 0, IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2) := by
  choose W hWo hxW δ hδ hinjOn hopen using exists_injOn_isOpen_image_normalTube hf himm
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  -- A radius below the finitely many local radii.
  obtain ⟨ε₁, hε₁, hε₁δ⟩ : ∃ ε₁ > 0, ∀ x ∈ t, ε₁ ≤ δ x := by
    rcases t.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨t.inf' hne δ, (Finset.lt_inf'_iff hne).mpr fun x _ => hδ x,
        fun x hx => Finset.inf'_le δ hx⟩
  -- Points whose images are close lie in a common chart neighbourhood.
  set O := ⋃ x ∈ t, W x ×ˢ W x
  have hOo : IsOpen O := isOpen_biUnion fun x _ => (hWo x).prod (hWo x)
  have hdiag : ∀ y, (y, y) ∈ O := fun y => by
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x, hx, hy, hy⟩
  obtain ⟨m, hm, hmO⟩ : ∃ m > 0, ∀ y z : M, ‖f y - f z‖ < m → (y, z) ∈ O := by
    rcases Oᶜ.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, fun y z _ => by
        simpa using (compl_empty_iff.mp hE).symm ▸ mem_univ (y, z)⟩
    · have hcont : Continuous fun q : M × M => ‖f q.1 - f q.2‖ := by
        have := hf.continuous
        fun_prop
      obtain ⟨q, hq, hmin⟩ := hOo.isClosed_compl.isCompact.exists_isMinOn hne hcont.continuousOn
      refine ⟨‖f q.1 - f q.2‖, ?_, fun y z hyz => ?_⟩
      · rw [gt_iff_lt, norm_pos_iff, sub_ne_zero]
        intro h
        apply hq
        rw [← Prod.mk.eta (p := q), hinj h]
        exact hdiag q.2
      · by_contra h
        exact (not_le.mpr hyz) (hmin h)
  refine ⟨min ε₁ (m / 2), lt_min hε₁ (half_pos hm), ?_⟩
  set ε := min ε₁ (m / 2)
  have hloc : ∀ p ∈ normalTube I f ε, ∀ x ∈ t, p.1 ∈ W x →
      p ∈ {q : M × V | q.1 ∈ W x ∧ q ∈ normalTube I f (δ x)} := fun p hp x hx hpW =>
    ⟨hpW, hp.1, hp.2.trans_le ((min_le_left _ _).trans (hε₁δ x hx))⟩
  have hinjT : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε) := by
    intro p hp p' hp' heq
    have hlt : ‖f p.1 - f p'.1‖ < m := by
      have hsub : f p.1 - f p'.1 = p'.2 - p.2 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm (p'.2)]
        exact heq
      rw [hsub]
      calc ‖p'.2 - p.2‖ ≤ ‖p'.2‖ + ‖p.2‖ := norm_sub_le _ _
        _ < m / 2 + m / 2 := add_lt_add (hp'.2.trans_le (min_le_right _ _))
            (hp.2.trans_le (min_le_right _ _))
        _ = m := add_halves m
    obtain ⟨x, hx, h1, h2⟩ := mem_iUnion₂.mp (hmO _ _ hlt)
    exact hinjOn x (hloc p hp x hx h1) (hloc p' hp' x hx h2) heq
  refine .of_continuous_injective_isOpenMap ?_ (fun p p' h => Subtype.ext (hinjT p.2 p'.2 h)) ?_
  · have hfc := hf.continuous
    have hΦ : Continuous fun p : M × V => f p.1 + p.2 := by fun_prop
    exact hΦ.comp continuous_subtype_val
  · intro U hU
    obtain ⟨O₁, hO₁, rfl⟩ := isOpen_induced_iff.mp hU
    have himage : (normalTube I f ε).domRestrict (fun p : M × V => f p.1 + p.2) ''
        (Subtype.val ⁻¹' O₁) = ⋃ x ∈ t, (fun p : M × V => f p.1 + p.2) ''
          ((O₁ ∩ univ ×ˢ Metric.ball 0 ε) ∩ {q | q.1 ∈ W x ∧ q ∈ normalTube I f (δ x)}) := by
      ext z
      constructor
      · rintro ⟨⟨p, hp⟩, hpO, rfl⟩
        obtain ⟨x, hx, hpW⟩ := mem_iUnion₂.mp (ht (mem_univ p.1))
        exact mem_iUnion₂.mpr ⟨x, hx, p, ⟨⟨hpO, mem_univ _, mem_ball_zero_iff.mpr hp.2⟩,
          hloc p hp x hx hpW⟩, rfl⟩
      · intro hz
        obtain ⟨x, -, q, ⟨⟨hqO, -, hqε⟩, -, hq, -⟩, rfl⟩ := mem_iUnion₂.mp hz
        exact ⟨⟨q, hq, mem_ball_zero_iff.mp hqε⟩, hqO, rfl⟩
    rw [himage]
    exact isOpen_biUnion fun x _ => hopen x _ (hO₁.inter (isOpen_univ.prod Metric.isOpen_ball))

/-- The total space of the normal bundle of `f` carries the topology of a subspace of `M × V`,
independently of its model-fibre parameter `F`. -/
instance instTopologicalSpaceTotalSpaceNormalSubspace {F : Type*} (f : M → V) :
    TopologicalSpace (TotalSpace F fun x : M => normalSubspace I f x) :=
  TopologicalSpace.induced (fun p => (p.proj, (p.2 : V))) inferInstance

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- The total space of the normal bundle of `f` is embedded in `M × V`. -/
theorem isEmbedding_totalSpace_normalSubspace {F : Type*} (f : M → V) :
    IsEmbedding fun p : TotalSpace F (fun x : M => normalSubspace I f x) =>
      (p.proj, (p.2 : V)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [Subtype.ext h]

/-- **Tubular neighbourhood theorem** for a compact `C²` embedded submanifold of a Euclidean
space, as `IsTubularNeighborhood` data: for some `ε > 0`, the normal vectors of length less than
`ε`, in the total space of the normal bundle, are mapped by `(x, v) ↦ f x + v` homeomorphically
onto an open subset of `V`. The model-fibre parameter of `Bundle.TotalSpace` is taken to be `V`,
which contains every fibre. -/
theorem exists_isTubularNeighborhood_normalBundle [I.Boundaryless] [IsManifold I 2 M]
    [CompactSpace M] {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f) :
    ∃ ε > 0, IsTubularNeighborhood f
      {p : TotalSpace V (fun x : M => normalSubspace I f x) | ‖(p.2 : V)‖ < ε}
      fun p => f p.1.proj + p.1.2 := by
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  let ι : TotalSpace V (fun x : M => normalSubspace I f x) → M × V := fun p => (p.proj, p.2)
  have hι : IsEmbedding ι := isEmbedding_totalSpace_normalSubspace f
  set U := {p : TotalSpace V (fun x : M => normalSubspace I f x) | ‖(p.2 : V)‖ < ε}
  -- The normal vectors of length less than `ε` in the total space and in `M × V`.
  let σ : U ≃ₜ normalTube I f ε :=
    { toFun := fun p => ⟨ι p.1, p.1.2.2, p.2⟩
      invFun := fun q => ⟨⟨q.1.1, ⟨q.1.2, q.2.1⟩⟩, q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (hι.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (hι.isInducing.continuous_iff.mpr continuous_subtype_val).subtype_mk _ }
  refine ⟨ε, hε, ?_⟩
  exact
    { isOpen := (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).preimage
        hι.continuous
      zero_mem := fun x => by simp [zeroSection, hε]
      fiberwise_starConvex := fun x => by
        convert (convex_ball (0 : normalSubspace I f x) ε).starConvex (Metric.mem_ball_self hε)
        ext v
        simp
      isOpenEmbedding := hemb.comp σ.isOpenEmbedding
      isEmbedding_f := (hf.continuous.isClosedEmbedding hinj).isEmbedding
      map_zeroSection := fun x => by simp [zeroSection]
      continuous_radial := by
        refine hι.isInducing.continuous_iff.mpr ?_
        have h1 : Continuous fun p : Icc (0 : ℝ) 1 × U => ι p.2.1 :=
          hι.continuous.comp (continuous_subtype_val.comp continuous_snd)
        have h2 : Continuous fun p : Icc (0 : ℝ) 1 × U => (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        exact h1.fst.prodMk (h2.smul h1.snd) }

end Manifold

end TauCeti
