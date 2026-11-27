/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Invariance of weak pseudoholomorphic maps under diffeomorphisms of the target

Let `X` be a Riemann surface and `g : M → N` a smooth diffeomorphism between manifolds modelled
on the same boundaryless model `I`. A map `g ∘ u : X → N` is weakly pseudoholomorphic for a
domain-dependent structure `J` on `N` and an inhomogeneous term `ν` exactly when `u : X → M` is
weakly pseudoholomorphic for the pulled-back structure `g^* J` and term `g^* ν`
(`TauCeti.isWeakPseudoholomorphicOn_diffeomorph_comp_iff` on a set,
`TauCeti.isWeakPseudoholomorphic_diffeomorph_comp_iff` on the whole surface). This is the
invariance of the weak equation under diffeomorphisms of the target, with `J` and `ν`
transported along. As a Check, `z ↦ 2 z` solves the equation on `ℂ` for the structure `i`, since
`i` pulls back to itself along `z ↦ 2 z` (`TauCeti.twoSMulDiffeomorph`,
`TauCeti.pullback_twoSMulDiffeomorph_ofComplexManifold`, and for domain-dependent structures
`const_ofComplexManifold_eq_pullback_twoSMulDiffeomorph` in the namespace
`TauCeti.ContMDiffAlmostComplexStructureFamily`, whose fully qualified name is longer than a line)
and the identity solves it (`TauCeti.isWeakPseudoholomorphic_two_mul`).

The predicate tests every chart `ψ` of the maximal atlas of `M` and every chart `χ` of that of
`N`, and `ψ ↦ g⁻¹ ≫ ψ`, `χ ↦ g ≫ χ` match these charts so that `ψ = χ ∘ g`. In matched
charts the two coordinate equations are the same: the coordinate expressions `ψ ∘ u ∘ φ⁻¹` and
`χ ∘ (g ∘ u) ∘ φ⁻¹` are equal, and `g^* J` and `g^* ν` read in `ψ` are `J` and `ν` read in `χ`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_pullback`,
`TauCeti.InhomogeneousTerm.chartTerm_pullback`). The Sobolev class follows from continuity and
the coordinate equations
(`TauCeti.isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn`), and composition
with the homeomorphism `g` preserves continuity, so `s` need not be open. No comparison of the
equation in two charts of the same manifold is needed.

## Implementation notes

Both manifolds carry the same model `I`, so that `g⁻¹ ≫ ψ` is a chart of `N` for every chart `ψ`
of `M`. The structures are pulled back along a smooth `g`, so `J` and `ν` keep their regularity
`ℓ`. The boundary condition of the equation is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I N 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- The coordinate equations of `g ∘ u` for `(J, ν)` in charts `φ` and `χ` and of `u` for
`(g^* J, g^* ν)` in charts `φ` and `ψ` agree when `ψ = χ ∘ g`. -/
private theorem isWeakCauchyRiemannOn_chart_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N)
    {ψ : OpenPartialHomeomorph M H} {χ : OpenPartialHomeomorph N H}
    (hsrc : ψ.source = g ⁻¹' χ.source) (hfun : ∀ x, ψ x = χ (g x))
    (hsymm : ∀ w, ψ.symm w = g.symm (χ.symm w)) (φ : OpenPartialHomeomorph X ℂ) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ (g ∘ u) ⁻¹' χ.source))
        (J.chartField φ (χ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (χ.extendTrans I (Homeomorph.refl E)))
        (χ.extendTrans I (Homeomorph.refl E) ∘ (g ∘ u) ∘ φ.symm) ↔
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        ((J.pullback g le_top).chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        ((ν.pullback g le_top).chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  have hfun' : ⇑(ψ.extendTrans I (Homeomorph.refl E)) = χ.extendTrans I (Homeomorph.refl E) ∘ g :=
    funext fun x ↦ by simp [OpenPartialHomeomorph.extendTrans_apply, hfun]
  have hsymm' : ⇑(ψ.extendTrans I (Homeomorph.refl E)).symm =
      g.symm ∘ (χ.extendTrans I (Homeomorph.refl E)).symm :=
    funext fun w ↦ by simp [OpenPartialHomeomorph.extendTrans_symm_apply, hsymm]
  rw [J.chartField_pullback g le_top φ hfun' hsymm', ν.chartTerm_pullback g le_top φ hfun' hsymm',
    hfun', hsrc, preimage_comp]
  rfl

/-- **Invariance under diffeomorphisms of the target.** For a diffeomorphism `g : M → N`, the
map `g ∘ u` is weakly pseudoholomorphic on `s` for `J` and `ν` exactly when `u` is weakly
pseudoholomorphic on `s` for the pulled-back structure `g^* J` and term `g^* ν`. -/
theorem isWeakPseudoholomorphicOn_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphicOn J ν p (g ∘ u) s ↔
      IsWeakPseudoholomorphicOn (J.pullback g le_top) (ν.pullback g le_top) p u s := by
  simp only [isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn]
  refine and_congr (g.toHomeomorph.comp_continuousOn_iff u s)
    ⟨fun h φ hφ ψ hψ ↦ ?_, fun h φ hφ χ hχ ↦ ?_⟩
  · -- Test `g ∘ u` in the chart `g⁻¹ ≫ ψ` of `N`.
    refine (isWeakCauchyRiemannOn_chart_diffeomorph_comp_iff g ?_ (fun x ↦ ?_) (fun w ↦ ?_)
      φ).1
      (h φ hφ _ (g.symm.toPartialDiffeomorph.trans_mem_maximalAtlas hψ))
    · ext x
      simp
    · simp
    · simp
  · -- Test `u` in the chart `g ≫ χ` of `M`.
    refine (isWeakCauchyRiemannOn_chart_diffeomorph_comp_iff g ?_ (fun x ↦ ?_) (fun w ↦ ?_)
      φ).2 (h φ hφ _ (g.toPartialDiffeomorph.trans_mem_maximalAtlas hχ))
    · ext x
      simp
    · simp
    · simp

/-- **Invariance under diffeomorphisms of the target.** For a diffeomorphism `g : M → N`, the
map `g ∘ u` is weakly pseudoholomorphic for `J` and `ν` exactly when `u` is weakly
pseudoholomorphic for the pulled-back structure `g^* J` and term `g^* ν`. -/
theorem isWeakPseudoholomorphic_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphic J ν p (g ∘ u) ↔
      IsWeakPseudoholomorphic (J.pullback g le_top) (ν.pullback g le_top) p u := by
  simp only [← isWeakPseudoholomorphicOn_univ,
    isWeakPseudoholomorphicOn_diffeomorph_comp_iff g]

/-! ### Checks -/

section Checks

/-- The map `z ↦ 2 z` of `ℂ`, as a diffeomorphism. -/
noncomputable def twoSMulDiffeomorph : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv.toDiffeomorph

/-- The diffeomorphism `twoSMulDiffeomorph` is `z ↦ 2 z`. -/
@[simp]
theorem twoSMulDiffeomorph_apply (z : ℂ) : twoSMulDiffeomorph z = 2 * z := by
  simp [twoSMulDiffeomorph, two_mul, two_smul]

/-- The structure `i` of `ℂ` pulls back to itself along `z ↦ 2 z`. -/
theorem pullback_twoSMulDiffeomorph_ofComplexManifold {ℓ : ℕ∞} :
    ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ).pullback
      twoSMulDiffeomorph le_top =
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ := by
  refine ((ContMDiffAlmostComplexStructure.eq_pullback_iff twoSMulDiffeomorph
    ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) le_top).2
      fun x v ↦ ?_).symm
  beta_reduce
  rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
    SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
    SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold,
    SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  have hD : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) twoSMulDiffeomorph x =
      ((2 : ℝ) • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) := by
    have hg : ⇑twoSMulDiffeomorph = ⇑((2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) := by
      funext z
      simp [twoSMulDiffeomorph]
    rw [hg, ContinuousLinearMap.mfderiv_eq]
  have key (D : ℂ →L[ℝ] ℂ) (hD : D = (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) (w : ℂ) :
      D ((Complex.I • ContinuousLinearMap.id ℝ ℂ) w) =
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) (D w) := by
    subst hD
    simp only [smul_apply, ContinuousLinearMap.id_apply]
    rw [smul_comm]
  exact key _ hD v

/-- A domain-dependent structure equal to the structure `i` of `ℂ` at every domain point is its own
pullback along `z ↦ 2 z`. -/
theorem ContMDiffAlmostComplexStructureFamily.const_ofComplexManifold_eq_pullback_twoSMulDiffeomorph
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] {ℓ : ℕ∞} :
    ContMDiffAlmostComplexStructureFamily.const (IP := IP) (P := P)
        ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) =
      (ContMDiffAlmostComplexStructureFamily.const
        ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)).pullback
        twoSMulDiffeomorph le_top := by
  rw [ContMDiffAlmostComplexStructureFamily.pullback_const,
    pullback_twoSMulDiffeomorph_ofComplexManifold]

/-- **Check.** On `X = M = N = ℂ` with the structure `i`, the map `z ↦ 2 z` is weakly
pseudoholomorphic: it is `g ∘ id` for the diffeomorphism `g = (2 ·)`, along which `i` pulls back
to itself, and the identity solves the equation. -/
theorem isWeakPseudoholomorphic_two_mul {ℓ : ℕ∞} {p : ENNReal} :
    IsWeakPseudoholomorphic (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
      (fun z : ℂ ↦ 2 * z) := by
  have hJ :=
    ContMDiffAlmostComplexStructureFamily.const_ofComplexManifold_eq_pullback_twoSMulDiffeomorph
      (IP := 𝓘(ℝ, ℂ)) (P := ℂ) (ℓ := ℓ)
  have hid := (isWeakPseudoholomorphic_ofEq (ν := 0) rfl hJ).2
    (isWeakPseudoholomorphic_id (X := ℂ) (ℓ := ℓ) (p := p))
  rw [InhomogeneousTerm.ofEq_zero, ← InhomogeneousTerm.pullback_zero twoSMulDiffeomorph le_top,
    ← isWeakPseudoholomorphic_diffeomorph_comp_iff] at hid
  convert hid using 1
  funext z
  simp

end Checks

end TauCeti
