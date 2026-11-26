/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Cobordism invariance of the mapping degree

Let `W` be an oriented manifold with boundary of dimension `n + 1`, and let `F : W → N` be a proper
smooth map to a connected oriented boundaryless manifold of dimension `n`. The restriction of `F`
to the boundary `∂W`, with its outward-first orientation, has degree zero
(`TauCeti.degree_boundaryOrientation_comp_subtypeVal_eq_zero`).

The proof is Stokes' theorem. For a top form `θ` on `N`, the pullback `F^*θ` is closed, since
pullback commutes with the exterior derivative and every `(n + 1)`-form on `N` vanishes. Hence
`∫_{∂W} F^*θ = ∫_W d(F^*θ) = 0` (`TauCeti.integralTopForm_mpullback_comp_subtypeVal_eq_zero`,
stated for every closed `C¹` form `θ` whose pullback has compact support). Choosing `θ` of
integral one, the degree formula `∫_{∂W} F^*θ = deg(F|∂W) ∫_N θ` gives `deg(F|∂W) = 0`.

When the boundary is split into an incoming part `M₀` and an outgoing part `M₁`, that is, when
`∂W` is the disjoint union of the images of injective local diffeomorphisms `j₀ : M₀ → ∂W` reversing
and `j₁ : M₁ → ∂W` preserving orientation, the signed count over `∂W` is the signed count over `M₁`
minus that over `M₀` (`TauCeti.degreeAtRegularValue_eq_add_of_isCompl_range`). So the two ends of
the cobordism have the same degree: `deg (F ∘ j₀) = deg (F ∘ j₁)`
(`TauCeti.degree_eq_of_cobordism`). The ends need not be compact, only the map `F` proper.

This is the invariance used for evaluation maps of moduli spaces: along a compact oriented
universal family whose boundary is the final minus the initial moduli space, the evaluation degree
is unchanged. The homotopy invariance `TauCeti.degree_eq_of_homotopy` is the special case of the
cylinder `M × [0, 1]`, proved there directly.

## Main results

* `TauCeti.integralTopForm_mpullback_comp_subtypeVal_eq_zero`: the integral over `∂W` of the
  restriction of `F^*θ` vanishes for a closed form `θ`.
* `TauCeti.degree_boundaryOrientation_comp_subtypeVal_eq_zero`,
  `TauCeti.degreeAtRegularValue_boundaryOrientation_comp_subtypeVal_eq_zero`: the restriction of a
  proper smooth map to the oriented boundary has degree zero, and signed count zero over every
  regular value.
* `TauCeti.degreeAtRegularValue_eq_add_of_isCompl_range`: over a finite fibre, the signed count is
  additive when the source is split into the images of two orientation-preserving injective local
  diffeomorphisms.
* `TauCeti.degree_eq_of_cobordism`: the two ends of an oriented cobordism over `N` have the same
  degree.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, Lemma 1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti

open Manifold.Orientation

section Additivity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E₀ H₀ M₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M₀]
  [ChartedSpace H₀ M₀] [IsManifold I₀ 1 M₀]
  {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁]
  [ChartedSpace H₁ M₁] [IsManifold I₁ 1 M₁]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {ι : Type*} [Fintype ι] {m : ℕ∞ω}

/-- **Additivity of the signed count.** Let `M` be the disjoint union of the images of injective
`C^m` local diffeomorphisms `j₀ : M₀ → M` and `j₁ : M₁ → M` (`m ≠ 0`) preserving the orientations.
Over a value `y` with finite fibre, the signed count of `g : M → N` is the sum of those of
`g ∘ j₀` and `g ∘ j₁`. -/
theorem degreeAtRegularValue_eq_add_of_isCompl_range (o : Manifold.Orientation I M ι)
    (o₀ : Manifold.Orientation I₀ M₀ ι) (o₁ : Manifold.Orientation I₁ M₁ ι)
    (oN : Manifold.Orientation J N ι) {j₀ : M₀ → M} {j₁ : M₁ → M}
    (hj₀ : IsLocalDiffeomorph I₀ I m j₀) (hj₁ : IsLocalDiffeomorph I₁ I m j₁) (hm : m ≠ 0)
    (hi₀ : Injective j₀) (hi₁ : Injective j₁) (hc : IsCompl (range j₀) (range j₁))
    (ho₀ : ∀ x, IsOrientationPreservingAt o₀ o j₀ x)
    (ho₁ : ∀ x, IsOrientationPreservingAt o₁ o j₁ x) {g : M → N} {y : N}
    (hfin : (g ⁻¹' {y}).Finite) :
    degreeAtRegularValue o oN g y =
      degreeAtRegularValue o₀ oN (g ∘ j₀) y + degreeAtRegularValue o₁ oN (g ∘ j₁) y := by
  -- The fibre of `g` is the disjoint union of the images of the fibres of `g ∘ j₀` and `g ∘ j₁`.
  have hsplit : g ⁻¹' {y} = j₀ '' ((g ∘ j₀) ⁻¹' {y}) ∪ j₁ '' ((g ∘ j₁) ⁻¹' {y}) := by
    rw [preimage_comp, preimage_comp, image_preimage_eq_inter_range,
      image_preimage_eq_inter_range, ← inter_union_distrib_left, hc.sup_eq_top, top_eq_univ,
      inter_univ]
  have hdisj : Disjoint (j₀ '' ((g ∘ j₀) ⁻¹' {y})) (j₁ '' ((g ∘ j₁) ⁻¹' {y})) :=
    hc.disjoint.mono (image_subset_range _ _) (image_subset_range _ _)
  rw [degreeAtRegularValue_def, hsplit,
    finsum_mem_union hdisj (hfin.subset (hsplit ▸ subset_union_left))
      (hfin.subset (hsplit ▸ subset_union_right)),
    finsum_mem_image hi₀.injOn, finsum_mem_image hi₁.injOn, degreeAtRegularValue_def,
    degreeAtRegularValue_def]
  -- Each local diffeomorphism contributes the sign `1`.
  congr 1
  · refine finsum_mem_congr rfl fun x _ ↦ ?_
    rw [(hj₀ x).orientationSign_comp hm o₀ o oN g,
      orientationSign_of_isOrientationPreservingAt (ho₀ x), mul_one]
  · refine finsum_mem_congr rfl fun x _ ↦ ?_
    rw [(hj₁ x).orientationSign_comp hm o₁ o oN g,
      orientationSign_of_isOrientationPreservingAt (ho₁ x), mul_one]

end Additivity

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ((𝓡∂ (n + 1)).boundary W) :=
  isManifold_boundary W

/-- **Stokes' theorem for a pulled-back closed form.** For a `C²` map `F : W → N` from an oriented
manifold with boundary and a closed `C¹` form `θ` on `N` whose pullback to `W` has compact support,
the integral of `θ` pulled back to the oriented boundary `∂W` vanishes: it is the integral over `W`
of `d(F^*θ) = F^*(dθ) = 0`. -/
theorem integralTopForm_mpullback_comp_subtypeVal_eq_zero [IsManifold J 2 N] [SigmaCompactSpace W]
    (o : Manifold.Orientation (𝓡∂ (n + 1)) W (Fin (n + 1))) {F : W → N}
    (hF : ContMDiff (𝓡∂ (n + 1)) J 2 F) {θ : RoughForm J N ℝ n} (hθ : IsSmoothForm J 1 θ)
    (hclosed : mextDeriv θ = 0)
    (hc : IsCompact (_root_.tsupport (α := EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ)
      (mpullback (𝓡∂ (n + 1)) J F θ))) :
    integralTopForm (boundaryOrientation o)
      (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J (F ∘ Subtype.val) θ) = 0 := by
  rw [mpullback_comp
      ((isImmersion_subtypeVal_boundary (k := 1) W).contMDiff.mdifferentiable one_ne_zero)
      (hF.mdifferentiable (by simp)), ← boundaryRestriction_eq_mpullback,
    ← integralTopForm_mextDeriv o (hθ.mpullback hF) hc, hθ.mextDeriv_mpullback_eq_zero hclosed hF,
    integralTopForm_zero]

variable [IsManifold J ∞ N] [FiniteDimensional ℝ E'] [BoundarylessManifold J N] [T2Space N]
  [SigmaCompactSpace N] [ConnectedSpace N]

/-- **The boundary of a manifold maps with degree zero.** The restriction of a proper smooth map
`F : W → N`, from an oriented manifold with boundary of dimension `n + 1` to a connected oriented
boundaryless manifold of dimension `n`, to the boundary `∂W` with its outward-first orientation
has degree zero. -/
theorem degree_boundaryOrientation_comp_subtypeVal_eq_zero
    (o : Manifold.Orientation (𝓡∂ (n + 1)) W (Fin (n + 1))) (o' : Manifold.Orientation J N (Fin n))
    {F : W → N} (hF : ContMDiff (𝓡∂ (n + 1)) J ∞ F) (hFp : IsProperMap F) :
    degree (boundaryOrientation o) o' (F ∘ Subtype.val) = 0 := by
  have := hFp.sigmaCompactSpace
  -- The boundary inclusion is smooth, and proper since the boundary is closed.
  have hg := hF.comp (isImmersion_subtypeVal_boundary (k := ∞) W).contMDiff
  have hgp := hFp.comp
    ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W).isClosedEmbedding_subtypeVal.isProperMap
  obtain ⟨y⟩ : Nonempty N := inferInstance
  -- Integrate a closed top form of integral one over `N`.
  obtain ⟨θ, -, hθ⟩ :=
    exists_compactlySupportedClosedForms_integralTopForm_eq_one o' y (U := univ) Filter.univ_mem
  have hθc : IsCompact (_root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) θ.val.val) :=
    (mem_compactlySupportedForms J).mp ((mem_compactlySupportedClosedForms J).mp θ.property).1
  have h := integralTopForm_mpullback_eq_degree_mul (boundaryOrientation o) o' hg hgp
    θ.val.isSmoothForm hθc
  rw [hθ, mul_one, integralTopForm_mpullback_comp_subtypeVal_eq_zero o (hF.of_le (by simp))
    (θ.val.isSmoothForm.of_le (by simp))
    (mextDeriv_eq_zero_of_finrank_le (by simp [← o'.card_eq]) _)
    (RoughForm.isCompact_tsupport_mpullback hFp hθc)] at h
  exact_mod_cast h.symm

/-- The restriction of a proper smooth map to the oriented boundary `∂W` has signed count zero
over every regular value. -/
theorem degreeAtRegularValue_boundaryOrientation_comp_subtypeVal_eq_zero
    (o : Manifold.Orientation (𝓡∂ (n + 1)) W (Fin (n + 1))) (o' : Manifold.Orientation J N (Fin n))
    {F : W → N} (hF : ContMDiff (𝓡∂ (n + 1)) J ∞ F) (hFp : IsProperMap F) {y : N}
    (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J
      (F ∘ (Subtype.val : (𝓡∂ (n + 1)).boundary W → W)) y) :
    degreeAtRegularValue (boundaryOrientation o) o' (F ∘ Subtype.val) y = 0 := by
  have hι := ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W).isClosedEmbedding_subtypeVal
  rw [← degree_eq_degreeAtRegularValue (boundaryOrientation o) o'
    (hF.comp (isImmersion_subtypeVal_boundary (k := ∞) W).contMDiff) (hFp.comp hι.isProperMap) hy,
    degree_boundaryOrientation_comp_subtypeVal_eq_zero o o' hF hFp]

/-- **Cobordism invariance of the degree.** Let `F : W → N` be a proper smooth map from an
oriented manifold with boundary of dimension `n + 1` to a connected oriented boundaryless manifold
of dimension `n`. Suppose the boundary `∂W` is the disjoint union of the images of injective
smooth local diffeomorphisms `j₀ : M₀ → ∂W`, reversing orientation, and `j₁ : M₁ → ∂W`, preserving
it, so that `∂W = M₁ - M₀` as oriented manifolds. Then the maps `f₀ = F ∘ j₀` and `f₁ = F ∘ j₁`
have the same degree. -/
theorem degree_eq_of_cobordism {E₀ H₀ M₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [FiniteDimensional ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [BoundarylessManifold I₀ M₀]
    {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [BoundarylessManifold I₁ M₁]
    (o : Manifold.Orientation (𝓡∂ (n + 1)) W (Fin (n + 1)))
    (o₀ : Manifold.Orientation I₀ M₀ (Fin n)) (o₁ : Manifold.Orientation I₁ M₁ (Fin n))
    (o' : Manifold.Orientation J N (Fin n))
    {F : W → N} (hF : ContMDiff (𝓡∂ (n + 1)) J ∞ F) (hFp : IsProperMap F)
    {j₀ : M₀ → (𝓡∂ (n + 1)).boundary W} {j₁ : M₁ → (𝓡∂ (n + 1)).boundary W}
    (hj₀ : IsLocalDiffeomorph I₀ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ j₀)
    (hj₁ : IsLocalDiffeomorph I₁ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ j₁)
    (hi₀ : Injective j₀) (hi₁ : Injective j₁) (hc : IsCompl (range j₀) (range j₁))
    (ho₀ : ∀ x, IsOrientationReversingAt o₀ (boundaryOrientation o) j₀ x)
    (ho₁ : ∀ x, IsOrientationPreservingAt o₁ (boundaryOrientation o) j₁ x)
    {f₀ : M₀ → N} {f₁ : M₁ → N} (h₀ : ∀ x, F (j₀ x) = f₀ x) (h₁ : ∀ x, F (j₁ x) = f₁ x) :
    degree o₀ o' f₀ = degree o₁ o' f₁ := by
  set g : (𝓡∂ (n + 1)).boundary W → N := F ∘ Subtype.val
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ g :=
    hF.comp (isImmersion_subtypeVal_boundary W).contMDiff
  have hgp : IsProperMap g := hFp.comp
    ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W).isClosedEmbedding_subtypeVal.isProperMap
  obtain rfl : f₀ = g ∘ j₀ := funext fun x ↦ (h₀ x).symm
  obtain rfl : f₁ = g ∘ j₁ := funext fun x ↦ (h₁ x).symm
  -- The ends are Hausdorff, and each is a closed piece of the boundary, so its map to `N` is
  -- proper.
  have : T2Space M₀ := .of_injective_continuous hi₀ hj₀.contMDiff.continuous
  have : T2Space M₁ := .of_injective_continuous hi₁ hj₁.contMDiff.continuous
  have hp₀ : IsProperMap (g ∘ j₀) := hgp.comp (Topology.IsClosedEmbedding.isProperMap
    ⟨(hj₀.isLocalHomeomorph.isOpenEmbedding_of_injective hi₀).isEmbedding,
      hc.eq_compl ▸ hj₁.isOpen_range.isClosed_compl⟩)
  have hp₁ : IsProperMap (g ∘ j₁) := hgp.comp (Topology.IsClosedEmbedding.isProperMap
    ⟨(hj₁.isLocalHomeomorph.isOpenEmbedding_of_injective hi₁).isEmbedding,
      hc.symm.eq_compl ▸ hj₀.isOpen_range.isClosed_compl⟩)
  -- Sard's theorem gives a regular value of `g`, which is regular for both ends.
  have := hgp.sigmaCompactSpace
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ E' := by
    simp [← o'.card_eq]
  obtain ⟨y, hy⟩ := (dense_isRegularValue hcard (hg.mdifferentiable (by simp))).nonempty
  have hy₀ : IsRegularValue I₀ J (g ∘ j₀) y := isRegularValue_iff.mpr fun x hx ↦
    ((hj₀ x).isRegularPoint_comp_iff (by simp)).mpr (hy.isRegularPoint hx)
  have hy₁ : IsRegularValue I₁ J (g ∘ j₁) y := isRegularValue_iff.mpr fun x hx ↦
    ((hj₁ x).isRegularPoint_comp_iff (by simp)).mpr (hy.isRegularPoint hx)
  have hadd := degreeAtRegularValue_eq_add_of_isCompl_range (boundaryOrientation o) (-o₀) o₁ o'
    hj₀ hj₁ (by simp) hi₀ hi₁ hc (fun x ↦ (isOrientationPreservingAt_neg_left _ _ _ _).mpr (ho₀ x))
    ho₁ (hy.finite_preimage_of_isProperMap hcard hgp)
  rw [degreeAtRegularValue_boundaryOrientation_comp_subtypeVal_eq_zero o o' hF hFp hy,
    degreeAtRegularValue_neg_left] at hadd
  rw [degree_eq_degreeAtRegularValue o₀ o' (hg.comp hj₀.contMDiff) hp₀ hy₀,
    degree_eq_degreeAtRegularValue o₁ o' (hg.comp hj₁.contMDiff) hp₁ hy₁]
  linarith

end TauCeti
