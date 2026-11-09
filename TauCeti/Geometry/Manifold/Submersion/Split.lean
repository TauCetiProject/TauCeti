/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Split differentials and submersion normal forms

`TauCeti.IsDiffSubmersionAt` means that the manifold derivative has a continuous linear right
inverse. It is meaningful for arbitrary models with corners, without a smoothness hypothesis.
Over a complete scalar field, for a finite-dimensional target it is equivalent to surjectivity,
hence to being a regular point.

For maps between finite-dimensional real or complex manifolds with boundaryless source, a split
differential and smoothness on a neighbourhood give Mathlib's submersion normal form. The complement
can be chosen uniformly as `Fin (dim E - dim F) → 𝕜`, even when the source is empty. Consequently
a smooth map is a submersion exactly when its differentials split. No separation or countability
hypothesis on either manifold is needed. These comparisons allow constructions using submersion
charts to be applied to maps specified by their differentials.

The normal-form construction uses `ContinuousLinearMap.implicitCoordEquiv` to identify the source
model with the target model times the derivative kernel, then applies the manifold inverse function
theorem to the map consisting of the target coordinates and the kernel projection.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem for submersions).
-/

public section

open Function Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

section Differential

variable {𝕜 E F E' H G H' M N M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {K : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace M'] [ChartedSpace H' M'] {f g : M → N} {x : M}

/-- A map is a differential submersion at a point if its manifold derivative admits a continuous
linear right inverse. Unlike the chart normal form, this predicate does not require smoothness. -/
def IsDiffSubmersionAt (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
    (f : M → N) (x : M) : Prop :=
  (mfderiv I J f x).HasRightInverse

/-- The differential-submersion predicate is the continuous right-inverse condition. -/
theorem isDiffSubmersionAt_iff :
    IsDiffSubmersionAt I J f x ↔ (mfderiv I J f x).HasRightInverse := Iff.rfl

/-- Differential submersions depend only on the germ of the map. -/
theorem IsDiffSubmersionAt.congr_of_eventuallyEq (hf : IsDiffSubmersionAt I J f x)
    (hfg : f =ᶠ[𝓝 x] g) : IsDiffSubmersionAt I J g x := by
  rw [isDiffSubmersionAt_iff, hfg.symm.mfderiv_eq]
  -- The equal values at `x` identify the two target tangent spaces.
  exact (tangentSpaceCast J (f x) (g x)).hasRightInverse.comp hf

/-- Composites of differentiable maps with split-surjective differentials again have
split-surjective differentials. -/
theorem IsDiffSubmersionAt.comp {g : N → M'}
    (hg : IsDiffSubmersionAt J K g (f x)) (hf : IsDiffSubmersionAt I J f x)
    (hgd : MDifferentiableAt J K g (f x)) (hfd : MDifferentiableAt I J f x) :
    IsDiffSubmersionAt I K (g ∘ f) x := by
  rw [isDiffSubmersionAt_iff, mfderiv_comp x hgd hfd]
  exact ContinuousLinearMap.HasRightInverse.comp hg hf

/-- For finite-dimensional targets, splitting the derivative is equivalent to being a regular
point. No differentiability or finite-dimensionality of the source is needed. -/
theorem isDiffSubmersionAt_iff_isRegularPoint [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    IsDiffSubmersionAt I J f x ↔ IsRegularPoint I J f x := by
  rw [isDiffSubmersionAt_iff, isRegularPoint_iff]
  exact ⟨ContinuousLinearMap.HasRightInverse.surjective,
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional⟩

end Differential

section NormalForm

variable {𝕜 E F G H M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M}

/-- A map smooth on an open neighbourhood of a regular point has the submersion normal form,
with the standard vector space of dimension `dim E - dim F` as complement. The source model is
boundaryless; neither manifold needs to be Hausdorff or second-countable. -/
theorem _root_.ContMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv {U : Set M}
    (hfU : ContMDiffOn I J n f U) (hU : IsOpen U) (hxU : x ∈ U) (hn : 1 ≤ n)
    (hs : Surjective (mfderiv I J f x)) :
    IsSubmersionAtOfComplement (Fin (Module.finrank 𝕜 E - Module.finrank 𝕜 F) → 𝕜)
      I J n f x := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  have hf := hfU.contMDiffAt (hU.mem_nhds hxU)
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold I 1 M := .of_le hn
  have : IsManifold J 1 N := .of_le hn
  -- Split the derivative into target and kernel coordinates.
  let D : E →L[𝕜] F := mfderiv I J f x
  have hD : D.range = ⊤ := LinearMap.range_eq_top.2 hs
  have hker : D.ker.ClosedComplemented :=
    D.ker_closedComplemented_of_finiteDimensional_range
  let L := D.implicitCoordEquiv hD hker
  let P := Classical.choose hker
  let c := extChartAt J (f x)
  let e := extChartAt I x
  let g : M → E := fun y ↦ L.symm (c (f y), P (e y))
  have hc : ContMDiffAt J 𝓘(𝕜, F) n c (f x) := contMDiffAt_extChartAt
  have he : ContMDiffAt I 𝓘(𝕜, E) n e x := contMDiffAt_extChartAt
  let q : M → F × D.ker := fun y ↦ (c (f y), P (e y))
  have hq := (hc.comp x hf).prodMk_space (P.contMDiff.contMDiffAt.comp x he)
  -- The product self-model and the product of self-models give the same differential.
  -- `erw` identifies the chart-centre tangent spaces with their model spaces.
  have hpair : mfderiv I 𝓘(𝕜, F × D.ker) q x = D.prod P := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    dsimp only [q]
    erw [mfderiv_prodMk ((hc.comp x hf).mdifferentiableAt hn0)
      ((P.contMDiff.contMDiffAt.comp x he).mdifferentiableAt hn0),
      mfderiv_comp x (hc.mdifferentiableAt hn0) (hf.mdifferentiableAt hn0),
      mfderiv_comp x P.mdifferentiableAt (he.mdifferentiableAt hn0)]
    simp only [c, e, mfderiv_extChartAt_self, mfderiv_eq_fderiv, P.fderiv]
    rfl
  -- Undoing `L` makes the derivative the identity. The normed-space tangent identifications
  -- in `mfderiv_eq_fderiv` are identities on vectors, as used in the final extensionality step.
  have hderiv : mfderiv I 𝓘(𝕜, E) g x = ContinuousLinearMap.id 𝕜 E := by
    dsimp only [g]
    erw [mfderiv_comp x L.symm.mdifferentiableAt (hq.mdifferentiableAt hn0)]
    erw [hpair, mfderiv_eq_fderiv, L.symm.fderiv, ← D.coe_implicitCoordEquiv hD hker]
    ext v
    exact L.symm_apply_apply v
  let W := (U ∩ f ⁻¹' (chartAt G (f x)).source) ∩ (chartAt H x).source
  have hW : IsOpen W := (hfU.continuousOn.isOpen_inter_preimage hU
    (chartAt G (f x)).open_source).inter (chartAt H x).open_source
  have hxW : x ∈ W := ⟨⟨hxU, mem_chart_source _ _⟩, mem_chart_source _ _⟩
  have hgW : ContMDiffOn I 𝓘(𝕜, E) n g W :=
    L.symm.contDiff.contMDiff.comp_contMDiffOn <|
      ((contMDiffOn_extChartAt (I := J)).comp (hfU.mono (fun y (h : y ∈ W) ↦ h.1.1))
        (fun y (h : y ∈ W) ↦ h.1.2)).prodMk_space
      (P.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.mono (fun y (h : y ∈ W) ↦ h.2)))
  -- The inverse function theorem supplies a smooth chart for `g`.
  -- The identity linear equivalence acts between the model copies of the tangent spaces.
  have hlocal : IsLocalDiffeomorphAt I 𝓘(𝕜, E) n g x :=
    isLocalDiffeomorphAt_of_mfderiv_eq hgW hW hxW BoundarylessManifold.isInteriorPoint hn
      (e := ContinuousLinearEquiv.refl 𝕜 E) (by rw [hderiv]; rfl)
  let Φ := hlocal.localInverse.symm
  have hxΦ : x ∈ Φ.source := hlocal.localInverse_mem_target
  obtain ⟨V, hVc, hV, hxV⟩ := mem_nhds_iff.1 <|
    hf.continuousAt.preimage_mem_nhds (chart_source_mem_nhds G (f x))
  let φ₀ := Φ.toOpenPartialHomeomorph.restrOpen V hV
  let φ := φ₀.transHomeomorph I.toHomeomorph.symm
  have hIsymm : ContMDiff 𝓘(𝕜, E) I n I.symm := by
    rw [← contMDiffOn_univ, ← I.range_eq_univ]
    exact I.contMDiffOn_symm
  have hφ : φ ∈ IsManifold.maximalAtlas I n M := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact hIsymm.comp_contMDiffOn (Φ.contMDiffOn.mono inter_subset_left)
    · exact (Φ.symm.contMDiffOn.mono inter_subset_left).comp I.contMDiff.contMDiffOn
        (fun y hy ↦ hy)
  -- A fixed standard complement lets the pointwise constructions assemble globally.
  have hdim : Module.finrank 𝕜 D.ker = Module.finrank 𝕜 E - Module.finrank 𝕜 F := by
    have hd := D.toLinearMap.finrank_range_add_finrank_ker
    rw [hD, finrank_top] at hd
    omega
  let K : D.ker ≃L[𝕜] (Fin (Module.finrank 𝕜 E - Module.finrank 𝕜 F) → 𝕜) :=
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)).toContinuousLinearEquiv
  apply (IsSubmersionAtOfComplement.congr_F K).mp
  refine IsSubmersionAtOfComplement.mk_of_charts L φ (chartAt G (f x))
    ?_ (mem_chart_source _ _) hφ (IsManifold.chart_mem_maximalAtlas _) ?_ ?_
  · exact ⟨hxΦ, hxV⟩
  · intro y hy
    exact hVc hy.2
  · intro v hv
    have hIv : I (I.symm v) = v := I.right_inv (I.range_eq_univ.symm ▸ mem_univ v)
    have hv₀ : v ∈ φ₀.target := by simpa [φ, hIv, I.range_eq_univ] using hv
    have hgv : g (φ₀.symm v) = v := hlocal.localInverse_right_inv hv₀.1
    have hvL := congrArg (fun z ↦ (L z).1) hgv
    -- Extending `φ` cancels its final `I.symm`, recovering `φ₀`; the first coordinate of `L g`
    -- is exactly the target-chart expression for `f`.
    simpa [g, c, extChartAt, φ, hIv] using hvL

/-- The submersion normal form is equivalent to a split differential for a map smooth on a
neighbourhood of the point. Smoothness is only needed to construct the normal form. -/
theorem isSubmersionAt_iff_split_mfderiv {U : Set M} (hf : ContMDiffOn I J n f U)
    (hU : IsOpen U) (hxU : x ∈ U) (hn : 1 ≤ n) :
    IsSubmersionAt I J n f x ↔ IsDiffSubmersionAt I J f x := by
  refine ⟨fun h ↦ h.hasRightInverse_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)), fun h ↦ ?_⟩
  exact (hf.isSubmersionAtOfComplement_of_surjective_mfderiv hU hxU hn
    (isRegularPoint_iff.mp (isDiffSubmersionAt_iff_isRegularPoint.mp h))).isSubmersionAt

/-- A smooth map with surjective differentials is a submersion with one fixed standard
complement. This also holds for an empty source. -/
theorem _root_.ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv
    (hf : ContMDiff I J n f) (hn : 1 ≤ n) (hs : ∀ x, Surjective (mfderiv I J f x)) :
    IsSubmersionOfComplement (Fin (Module.finrank 𝕜 E - Module.finrank 𝕜 F) → 𝕜)
      I J n f := by
  rw [Manifold.isSubmersionOfComplement_iff]
  exact fun x ↦ hf.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    isOpen_univ (mem_univ x) hn (hs x)

/-- A smooth map between finite-dimensional real or complex manifolds with boundaryless source is a
submersion exactly when every differential has a continuous linear right inverse. -/
theorem submersion_iff_split_mfderiv (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    IsSubmersion I J n f ↔ ∀ x, IsDiffSubmersionAt I J f x := by
  refine ⟨fun h x ↦ h.hasRightInverse_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) x, fun h ↦ ?_⟩
  exact (hf.isSubmersionOfComplement_of_surjective_mfderiv hn
    (fun x ↦ (isRegularPoint_iff.mp (isDiffSubmersionAt_iff_isRegularPoint.mp (h x))))).isSubmersion

end NormalForm

end TauCeti
