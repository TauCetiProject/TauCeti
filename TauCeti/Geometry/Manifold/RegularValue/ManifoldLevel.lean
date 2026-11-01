/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Regular fibres of manifold-valued maps

A regular fibre of a smooth map between finite-dimensional boundaryless real manifolds is an
embedded submanifold of the expected dimension. The carrier is the actual subtype
`{x // f x = c}`, with its subspace topology; neither manifold needs to be Hausdorff, and the
fibre may be empty.

`TauCeti.regularFiberChartedSpace` constructs an atlas using the preferred extended target chart.
`TauCeti.isManifold_regularFiber`, `TauCeti.isSmoothEmbedding_coe_regularFiber`, and
`TauCeti.range_mfderiv_coe_regularFiber` give its manifold, embedding, and tangent-kernel
properties.
`TauCeti.exists_regularFiber_smoothEmbedding` packages these properties existentially.
The smooth universal property follows from Mathlib's `ContMDiff.iff_comp_isImmersion`
and continuity into a subtype. No global charted-space instance is installed on a fibre or on its
ambient manifold.

The construction uses one extended target chart at `c`. Its open preimage contains the entire
fibre, and the regular level of the coordinate map there is homeomorphic to the original fibre.
The atlas is transported from `TauCeti.regularLevelChartedSpace`; no gluing of local fibre
atlases is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent spaces).
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace RegularFiber

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {c : N}

/-- The open preimage of the source of a target coordinate chart. -/
private def domain (hf : ContMDiff I J ∞ f) (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) :
    TopologicalSpace.Opens M :=
  ⟨f ⁻¹' φ.source, φ.open_source.preimage hf.continuous⟩

private theorem coordinate_eq_iff (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source)
    (x : domain hf φ) : φ (f x) = φ c ↔ f x = c :=
  ⟨fun h ↦ φ.toPartialEquiv.injOn x.2 hc h, congrArg φ⟩

/-- The coordinate level in the open preimage is the original fibre, with the same topology. -/
private def levelHomeomorph (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source) :
    {x : M // f x = c} ≃ₜ {x : domain hf φ // φ (f x) = φ c} where
  toFun x := ⟨⟨x, by simpa only [domain, TopologicalSpace.Opens.mem_mk,
    mem_preimage, x.2] using hc⟩, congrArg φ x.2⟩
  invFun x := ⟨x.1, (coordinate_eq_iff hf φ hc x.1).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem coe_levelHomeomorph (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source)
    (x : {x : M // f x = c}) : (levelHomeomorph hf φ hc x).1.1 = x.1 :=
  (rfl)

private theorem contMDiff_coordinate (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun x : domain hf φ ↦ φ (f x)) :=
  φ.contMDiffOn.comp_contMDiff (hf.comp contMDiff_subtype_val) fun x ↦ x.2

/-- Target coordinates and the open inclusion both have invertible differential, so regularity
is unchanged by passing to the coordinate level. -/
private theorem regularValue_coordinate (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    IsRegularValue I 𝓘(ℝ, F) (fun x : domain hf φ ↦ φ (f x)) (φ c) := by
  rw [isRegularValue_iff]
  intro x hx
  have hfx := (hf x.1).mdifferentiableAt (by simp)
  have hi := isLocalDiffeomorph_subtype_val (I := I) (n := ∞) (U := domain hf φ) x
  have hφ := φ.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ x.2
  have hd := hi.mdifferentiableAt (by simp)
  exact IsRegularPoint.comp (isRegularPoint_iff.2 (hφ.isInvertible_mfderiv (by simp)).surjective)
    ((hreg.isRegularPoint ((coordinate_eq_iff hf φ hc x).1 hx)).comp
      (isRegularPoint_iff.2 (hi.isInvertible_mfderiv (by simp)).surjective) hfx hd)
    (hφ.mdifferentiableAt (by simp)) (hfx.comp x hd)

variable [I.Boundaryless] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Transport the coordinate-level atlas to the actual fibre. -/
@[instance_reducible]
private noncomputable def chartedSpace_of_chart (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c} :=
  let q : domain hf φ → F := fun x ↦ φ (f x)
  let hq : ContMDiff I 𝓘(ℝ, F) ∞ q := contMDiff_coordinate hf φ
  let hqr : IsRegularValue I 𝓘(ℝ, F) q (φ c) := regularValue_coordinate hf φ hc hreg
  letI := regularLevelChartedSpace (fun x _ ↦ (hq x).of_le (by simp)) hqr rfl
  (levelHomeomorph hf φ hc).pullbackChartedSpace

private theorem isManifold_and_isSmoothEmbedding_of_chart (hf : ContMDiff I J ∞ f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    letI := chartedSpace_of_chart hf φ hc hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) ∞ {x : M // f x = c} ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I ∞
      (Subtype.val : {x : M // f x = c} → M) := by
  -- Construct the regular level on the open preimage of the single target chart.
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
  let q : domain hf φ → F := fun x ↦ φ (f x)
  have hq : ContMDiff I 𝓘(ℝ, F) ∞ q := contMDiff_coordinate hf φ
  have hqr : IsRegularValue I 𝓘(ℝ, F) q (φ c) := regularValue_coordinate hf φ hc hreg
  let := regularLevelChartedSpace (fun x _ ↦ (hq x).of_le (by simp)) hqr rfl
  have := isManifold_regularLevel (by simp) (fun x _ ↦ hq x) hqr rfl
  -- Transfer its atlas, then compose its inclusion with the open inclusion into `M`.
  let e := levelHomeomorph hf φ hc
  let := e.pullbackChartedSpace (H := Fin (finrank ℝ E - finrank ℝ F) → ℝ)
  have := e.pullback_isManifold K ∞
  refine ⟨inferInstance, ?_⟩
  have hlev := isImmersionOfComplement_coe_regularLevel (by simp)
    (fun x _ ↦ hq x) hqr rfl
  have hpre := isImmersionOfComplement_comp_diffeomorph (e.pullbackDiffeomorph K ∞) hlev
  rw [Homeomorph.coe_pullbackDiffeomorph] at hpre
  have hpost := isImmersionOfComplement_isLocalDiffeomorphAt_comp
    (fun x ↦ isLocalDiffeomorph_subtype_val (I := I) (n := ∞)
      (U := domain hf φ) (e x).1) hpre
  have heq : (fun x : {x : M // f x = c} ↦ ((e x).1 : M)) = Subtype.val :=
    funext (coe_levelHomeomorph hf φ hc)
  simp only [comp_def] at hpost
  rw [heq] at hpost
  exact ⟨hpost.isImmersion, Topology.IsEmbedding.subtypeVal⟩

end RegularFiber

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N} {c : N}

/-- The smooth atlas on a regular fibre, transported from the regular level in the preferred
extended target chart at `c`. It uses the subspace topology and is not a global instance. -/
@[instance_reducible]
noncomputable def regularFiberChartedSpace (hf : ContMDiff I J ∞ f)
    (hreg : IsRegularValue I J f c) :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c} :=
  RegularFiber.chartedSpace_of_chart hf (extChartPartialDiffeomorph J ∞ c)
    ((mem_extChartPartialDiffeomorph_source J ∞ c).2 BoundarylessManifold.isInteriorPoint) hreg

/-- The regular fibre with its preferred atlas is a smooth manifold. -/
theorem isManifold_regularFiber (hf : ContMDiff I J ∞ f) (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hf hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) ∞ {x : M // f x = c} :=
  (RegularFiber.isManifold_and_isSmoothEmbedding_of_chart hf
    (extChartPartialDiffeomorph J ∞ c)
    ((mem_extChartPartialDiffeomorph_source J ∞ c).2 BoundarylessManifold.isInteriorPoint) hreg).1

/-- The inclusion of the regular fibre with its preferred atlas is a smooth embedding. -/
theorem isSmoothEmbedding_coe_regularFiber (hf : ContMDiff I J ∞ f)
    (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hf hreg
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I ∞
      (Subtype.val : {x : M // f x = c} → M) :=
  (RegularFiber.isManifold_and_isSmoothEmbedding_of_chart hf
    (extChartPartialDiffeomorph J ∞ c)
    ((mem_extChartPartialDiffeomorph_source J ∞ c).2 BoundarylessManifold.isInteriorPoint) hreg).2

/-- The tangent image of the regular-fibre inclusion is the kernel of the ambient differential. -/
theorem range_mfderiv_coe_regularFiber (hf : ContMDiff I J ∞ f)
    (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hf hreg
    ∀ z : {x : M // f x = c},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I Subtype.val z).range =
        (mfderiv I J f z.1).ker := by
  let := regularFiberChartedSpace hf hreg
  have := isManifold_regularFiber hf hreg
  intro z
  have hdim := (hreg.isRegularPoint z.2).finrank_ker_mfderiv_add_finrank
  refine (hreg.isRegularPoint z.2).range_mfderiv_eq_ker_mfderiv
    (.of_forall fun w : {x : M // f x = c} ↦ w.2)
    ((isSmoothEmbedding_coe_regularFiber hf hreg).isImmersion.mfderiv_injective (by simp) z) ?_
  rw [finrank_fin_fun]
  omega

/-- **The regular-fibre theorem.** A regular fibre of a smooth map between finite-dimensional
boundaryless real manifolds admits a smooth manifold structure of dimension `dim M - dim N`,
with its subspace topology, for which the inclusion is a smooth embedding and has tangent image
`ker df`. No separation or countability assumptions are needed, and an empty fibre is allowed. -/
theorem exists_regularFiber_smoothEmbedding (hf : ContMDiff I J ∞ f)
    (hreg : IsRegularValue I J f c) :
    ∃ a : ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c},
      letI := a
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) ∞ {x : M // f x = c} ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I ∞
        (Subtype.val : {x : M // f x = c} → M) ∧
      ∀ z : {x : M // f x = c},
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I Subtype.val z).range =
          (mfderiv I J f z.1).ker := by
  exact ⟨regularFiberChartedSpace hf hreg, isManifold_regularFiber hf hreg,
    isSmoothEmbedding_coe_regularFiber hf hreg, range_mfderiv_coe_regularFiber hf hreg⟩

end TauCeti
