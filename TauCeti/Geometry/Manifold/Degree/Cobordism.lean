/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import TauCeti.Geometry.Manifold.Boundary.SmoothMap
import TauCeti.Topology.IsLocalHomeomorph.Basic

/-!
# Cobordism invariance of the mapping degree

Let `W` be an oriented manifold with boundary of dimension `n + 1`, and let `F : W → N` be a proper
smooth map to a connected oriented boundaryless manifold of dimension `n`. The restriction of `F`
to the boundary `∂W`, with its outward-first orientation, has degree zero
(`TauCeti.degree_boundaryOrientation_comp_subtypeVal_eq_zero`).

The proof is Stokes' theorem. For a top form `θ` on `N`, the pullback `F^*θ` is closed, since
pullback commutes with the exterior derivative and every `(n + 1)`-form on `N` vanishes. Hence
`∫_{∂W} F^*θ = ∫_W d(F^*θ) = 0` (`TauCeti.integralTopForm_mpullback_comp_subtypeVal_eq_zero`
in `TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes`). Choosing `θ` of
integral one, the degree formula `∫_{∂W} F^*θ = deg(F|∂W) ∫_N θ` gives `deg(F|∂W) = 0`.

When the boundary is split into an incoming part `M₀` and an outgoing part `M₁`, that is, when
`∂W` is the disjoint union of the images of injective local diffeomorphisms `j₀ : M₀ → ∂W` reversing
and `j₁ : M₁ → ∂W` preserving orientation, the signed count over `∂W` is the signed count over `M₁`
minus that over `M₀` (`TauCeti.degreeAtRegularValue_eq_add_of_isCompl_range` in
`TauCeti.Geometry.Manifold.Degree.Basic`). So the two ends of
the cobordism have the same degree: `deg (F ∘ j₀) = deg (F ∘ j₁)`
(`TauCeti.degree_eq_of_cobordism`). The ends need not be compact, only the map `F` proper.

This is the invariance used for evaluation maps of moduli spaces: along a compact oriented
universal family whose boundary is the final minus the initial moduli space, the evaluation degree
is unchanged. The homotopy invariance `TauCeti.degree_eq_of_homotopy` is the special case of the
cylinder `M × [0, 1]`, proved there directly.

## Main results

* `TauCeti.degree_boundaryOrientation_comp_subtypeVal_eq_zero`,
  `TauCeti.degreeAtRegularValue_boundaryOrientation_comp_subtypeVal_eq_zero`: the restriction of a
  proper smooth map to the oriented boundary has degree zero, and signed count zero over every
  regular value.
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

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E'] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ((𝓡∂ (n + 1)).boundary W) :=
  isManifold_boundary W

/-- **The boundary of a manifold maps with degree zero.** The restriction of a proper smooth map
`F : W → N`, from an oriented manifold with boundary of dimension `n + 1` to a connected oriented
boundaryless manifold of dimension `n`, to the boundary `∂W` with its outward-first orientation
has degree zero. -/
theorem degree_boundaryOrientation_comp_subtypeVal_eq_zero
    (o : Manifold.Orientation (𝓡∂ (n + 1)) W (Fin (n + 1))) (o' : Manifold.Orientation J N (Fin n))
    {F : W → N} (hF : ContMDiff (𝓡∂ (n + 1)) J ∞ F) (hFp : IsProperMap F) :
    degree (boundaryOrientation o) o' (F ∘ Subtype.val) = 0 := by
  have := hFp.sigmaCompactSpace
  -- The boundary is closed, so the restriction of `F` to it is proper.
  have hgp := hFp.restrict ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W)
  obtain ⟨y⟩ : Nonempty N := inferInstance
  -- Integrate a closed top form of integral one over `N`.
  obtain ⟨θ, -, hθ⟩ :=
    exists_compactlySupportedClosedForms_integralTopForm_eq_one o' y (U := univ) Filter.univ_mem
  have hθc : IsCompact (_root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) θ.val.val) :=
    (mem_compactlySupportedForms J).mp ((mem_compactlySupportedClosedForms J).mp θ.property).1
  have h := integralTopForm_mpullback_eq_degree_mul (boundaryOrientation o) o'
    hF.comp_subtypeVal_boundary hgp θ.val.isSmoothForm hθc
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
  rw [← degree_eq_degreeAtRegularValue (boundaryOrientation o) o' hF.comp_subtypeVal_boundary
    (hFp.restrict ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W)) hy,
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
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ g := hF.comp_subtypeVal_boundary
  have hgp : IsProperMap g := hFp.restrict ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional W)
  obtain rfl : f₀ = g ∘ j₀ := funext fun x ↦ (h₀ x).symm
  obtain rfl : f₁ = g ∘ j₁ := funext fun x ↦ (h₁ x).symm
  -- The ends are Hausdorff, and each is a closed piece of the boundary, so its map to `N` is
  -- proper.
  have : T2Space M₀ := .of_injective_continuous hi₀ hj₀.contMDiff.continuous
  have : T2Space M₁ := .of_injective_continuous hi₁ hj₁.contMDiff.continuous
  have hp₀ : IsProperMap (g ∘ j₀) := hgp.comp (hj₀.isLocalHomeomorph.isClosedEmbedding_of_injective
    hi₀ (hc.eq_compl ▸ hj₁.isOpen_range.isClosed_compl)).isProperMap
  have hp₁ : IsProperMap (g ∘ j₁) := hgp.comp (hj₁.isLocalHomeomorph.isClosedEmbedding_of_injective
    hi₁ (hc.symm.eq_compl ▸ hj₀.isOpen_range.isClosed_compl)).isProperMap
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
