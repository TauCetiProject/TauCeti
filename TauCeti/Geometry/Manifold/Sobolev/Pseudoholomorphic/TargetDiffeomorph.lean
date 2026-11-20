/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Invariance of the weak pseudoholomorphic equation under diffeomorphisms of the target

Let `X` be a Riemann surface and `Ψ : M → M'` a smooth diffeomorphism between manifolds on a
common boundaryless model `I`. A domain-dependent almost complex structure `J` on `M` and an
inhomogeneous term `ν` for it are carried by `Ψ` to `J'` and `ν'` on `M'` when the differential of
`Ψ` intertwines them:

`dΨ_y ∘ J(x, y) = J'(x, Ψ y) ∘ dΨ_y` and `dΨ_y (ν(x, y) w) = ν'(x, Ψ y) w`.

Then `Ψ ∘ u` is weakly pseudoholomorphic on `s` for `(J', ν')` exactly when `u` is weakly
pseudoholomorphic on `s` for `(J, ν)`
(`Diffeomorph.isWeakPseudoholomorphicOn_diffeomorph_comp_iff`).

## Main results

* `Diffeomorph.isWeakPseudoholomorphicOn_diffeomorph_comp_iff`,
  `Diffeomorph.isWeakPseudoholomorphic_diffeomorph_comp_iff`: **Invariance under diffeomorphisms of
  the target.**

## Implementation notes

The two sides are compared chart by chart. A chart `ψ'` of the maximal atlas of `M'`
precomposed with `Ψ` is a chart `ψ = ψ' ∘ Ψ` of the maximal atlas of `M`
(`Diffeomorph.transOpenPartialHomeomorph_mem_maximalAtlas`), and every chart `ψ` of `M` arises
in this way from `ψ' = ψ ∘ Ψ⁻¹`. For such a pair the coordinate expressions `ψ ∘ u ∘ φ⁻¹` and
`ψ' ∘ (Ψ ∘ u) ∘ φ⁻¹` are equal, on equal domains. The chain rule `dψ_y = dψ'_{Ψ y} ∘ dΨ_y`
then shows that `J` read in `ψ` is `J'` read in `ψ'`
(`TauCeti.ContMDiffAlmostComplexStructure.chartPushforward_eq_of_eventuallyEq_comp`), and likewise
for the inhomogeneous terms, so the two coordinate equations coincide.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1 and 3.1 and Appendix B.4.
-/

public section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

/-! ### Corresponding charts -/

section Charts

variable {Ψ : M ≃ₘ⟮I, I⟯ M'} {ψ : OpenPartialHomeomorph M H} {ψ' : OpenPartialHomeomorph M' H}

omit [IsManifold I ∞ M] [IsManifold I ∞ M'] in
/-- Near a point of the source of a chart `ψ = ψ' ∘ Ψ`, the chart `ψ` read in `E` is the chart `ψ'`
read in `E`, composed with `Ψ`. -/
private theorem extendTrans_eventuallyEq_comp (happly : ∀ y ∈ ψ.source, ψ y = ψ' (Ψ y)) {y : M}
    (hy : y ∈ ψ.source) :
    (ψ.extendTrans I (Homeomorph.refl E) : M → E) =ᶠ[𝓝 y]
      ψ'.extendTrans I (Homeomorph.refl E) ∘ Ψ :=
  eventually_of_mem (ψ.open_source.mem_nhds hy) fun w hw ↦ by simp [happly w hw]

end Charts

/-! ### Invariance of the weak equation -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {J' : ContMDiffAlmostComplexStructureFamily I M' 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {ν' : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J'}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- **The coordinate equations of `Ψ ∘ u` and of `u` agree in corresponding charts.** If the
differential of `Ψ` intertwines `(J, ν)` with `(J', ν')` and `ψ = ψ' ∘ Ψ` on the source of `ψ`,
the preimage of the source of `ψ'`, then `Ψ ∘ u` solves the coordinate equation in the charts `φ`
and `ψ'` exactly when `u` solves it in the charts `φ` and `ψ`. -/
private theorem isWeakCauchyRiemannOn_diffeomorph_comp_iff (Ψ : M ≃ₘ⟮I, I⟯ M')
    (hJ : ∀ (x : X) (y : M) (v : TangentSpace I y),
      mfderiv I I Ψ y (J.freeze x y v) = J'.freeze x (Ψ y) (mfderiv I I Ψ y v))
    (hν : ∀ (x : X) (y : M) (w : TangentSpace 𝓘(ℝ, ℂ) x),
      mfderiv I I Ψ y (ν.val.tangentHom (x, y) w) = ν'.val.tangentHom (x, Ψ y) w)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph M' H} (hψ' : ψ' ∈ IsManifold.maximalAtlas I ∞ M')
    (hsource : ψ.source = Ψ ⁻¹' ψ'.source) (happly : ∀ y ∈ ψ.source, ψ y = ψ' (Ψ y))
    (φ : OpenPartialHomeomorph X ℂ) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ (Ψ ∘ u) ⁻¹' ψ'.source))
        (J'.chartField φ (ψ'.extendTrans I (Homeomorph.refl E)))
        (ν'.chartTerm φ (ψ'.extendTrans I (Homeomorph.refl E)))
        (ψ'.extendTrans I (Homeomorph.refl E) ∘ (Ψ ∘ u) ∘ φ.symm) ↔
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  set χ := ψ.extendTrans I (Homeomorph.refl E)
  set χ' := ψ'.extendTrans I (Homeomorph.refl E)
  set D := φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  -- The two domains of the coordinate equations coincide.
  have hD : φ.target ∩ φ.symm ⁻¹' (s ∩ (Ψ ∘ u) ⁻¹' ψ'.source) = D := by
    simp only [D, hsource, preimage_comp]
  -- On the common domain, `χ' ∘ Ψ` is `χ`.
  have hval {y : M} (hy : y ∈ ψ.source) : χ' (Ψ y) = χ y := by simp [χ, χ', happly y hy]
  rw [hD, isWeakCauchyRiemannOn_congr (U := D) (u := χ' ∘ (Ψ ∘ u) ∘ φ.symm)
    (v := χ ∘ u ∘ φ.symm) fun z (hz : z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) ↦
      hval hz.2.2]
  -- The structures and the terms read in the two charts agree on the common domain.
  refine isWeakCauchyRiemannOn_congr_ae ?_ ?_ <;>
    filter_upwards [ae_restrict_mem measurableSet_interior] with z hz
  all_goals
    have hzD : z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := interior_subset hz
    have hy : u (φ.symm z) ∈ ψ.source := hzD.2.2
    have hΨy : Ψ (u (φ.symm z)) ∈ ψ'.source := hsource.subset hy
  · simp only [ContMDiffAlmostComplexStructureFamily.chartField_apply, Function.comp_apply]
    exact ((J.freeze (φ.symm z)).chartPushforward_eq_of_eventuallyEq_comp (J'.freeze (φ.symm z))
      (by simpa [χ] using hy) (by simpa [χ'] using hΨy) (extendTrans_eventuallyEq_comp happly hy)
      (Ψ.mdifferentiable (by simp) _)
      ((ψ'.contMDiffAt_extendTrans hψ' contDiff_id hΨy).mdifferentiableAt (by simp))
      ((ψ.contMDiffAt_extendTrans_symm hψ contDiff_id
        (χ.map_source (by simpa [χ] using hy))).mdifferentiableAt (by simp))
      ((ψ'.contMDiffAt_extendTrans_symm hψ' contDiff_id
        (χ'.map_source (by simpa [χ'] using hΨy))).mdifferentiableAt (by simp))
      (hJ (φ.symm z) _)).symm
  · set y := u (φ.symm z)
    have hχy : y ∈ χ.source := by simpa [χ] using hy
    have hχ'y : Ψ y ∈ χ'.source := by simpa [χ'] using hΨy
    have hs : χ.symm (χ y) = y := χ.left_inv hχy
    have hs' : χ'.symm (χ y) = Ψ y := by rw [← hval hy]; exact χ'.left_inv hχ'y
    simp only [InhomogeneousTerm.chartTerm_apply, Function.comp_apply]
    -- Generalize the two base points, so that the tangent spaces can be identified.
    have key : ∀ y₁ y₂, y₁ = Ψ y → y₂ = y →
        (2 : ℝ) • mvfderiv I χ' y₁
            (ν'.val.tangentHom (φ.symm z, y₁) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ))) =
          (2 : ℝ) • mvfderiv I χ y₂
            (ν.val.tangentHom (φ.symm z, y₂) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ))) := by
      rintro _ _ rfl rfl
      congr 1
      rw [← hν]
      exact mfderiv_apply_mfderiv_of_eventuallyEq_comp
        (extendTrans_eventuallyEq_comp happly hy).symm
        ((ψ'.contMDiffAt_extendTrans hψ' contDiff_id hΨy).mdifferentiableAt (by simp))
        (Ψ.mdifferentiable (by simp) y) _
    exact key _ _ hs' hs

/-- **Invariance under diffeomorphisms of the target.** Let `Ψ : M → M'` be a smooth
diffeomorphism whose differential intertwines the domain-dependent structures and inhomogeneous
terms, `dΨ_y ∘ J(x, y) = J'(x, Ψ y) ∘ dΨ_y` and `dΨ_y ∘ ν(x, y) = ν'(x, Ψ y)`. Then `Ψ ∘ u` is
weakly pseudoholomorphic on `s` for `(J', ν')` exactly when `u` is weakly pseudoholomorphic on `s`
for `(J, ν)`. -/
theorem _root_.Diffeomorph.isWeakPseudoholomorphicOn_diffeomorph_comp_iff (Ψ : M ≃ₘ⟮I, I⟯ M')
    (hJ : ∀ (x : X) (y : M) (v : TangentSpace I y),
      mfderiv I I Ψ y (J.freeze x y v) = J'.freeze x (Ψ y) (mfderiv I I Ψ y v))
    (hν : ∀ (x : X) (y : M) (w : TangentSpace 𝓘(ℝ, ℂ) x),
      mfderiv I I Ψ y (ν.val.tangentHom (x, y) w) = ν'.val.tangentHom (x, Ψ y) w) :
    IsWeakPseudoholomorphicOn J' ν' p (Ψ ∘ u) s ↔ IsWeakPseudoholomorphicOn J ν p u s := by
  simp only [isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn]
  refine and_congr ?_ ⟨fun h φ hφ ψ hψ ↦ ?_, fun h φ hφ ψ' hψ' ↦ ?_⟩
  · -- Continuity transfers along the homeomorphism `Ψ`.
    exact Ψ.toHomeomorph.comp_continuousOn_iff u s
  · -- Transport the chart `ψ` of `M` to the chart `ψ ∘ Ψ⁻¹` of `M'`.
    have hψ' := Ψ.symm.transOpenPartialHomeomorph_mem_maximalAtlas hψ
    refine (isWeakCauchyRiemannOn_diffeomorph_comp_iff Ψ hJ hν hψ hψ' ?_ (fun y _ ↦ ?_) φ).1
      (h φ hφ _ hψ')
    · ext y
      simp
    · simp
  · -- Transport the chart `ψ'` of `M'` to the chart `ψ' ∘ Ψ` of `M`.
    have hψ := Ψ.transOpenPartialHomeomorph_mem_maximalAtlas hψ'
    exact (isWeakCauchyRiemannOn_diffeomorph_comp_iff Ψ hJ hν hψ hψ' (by simp)
      (fun y _ ↦ by simp) φ).2 (h φ hφ _ hψ)

/-- **Invariance under diffeomorphisms of the target**, on the whole surface: if the differential
of the smooth diffeomorphism `Ψ : M → M'` intertwines `(J, ν)` with `(J', ν')`, then `Ψ ∘ u` is
weakly pseudoholomorphic for `(J', ν')` exactly when `u` is weakly pseudoholomorphic for
`(J, ν)`. -/
theorem _root_.Diffeomorph.isWeakPseudoholomorphic_diffeomorph_comp_iff (Ψ : M ≃ₘ⟮I, I⟯ M')
    (hJ : ∀ (x : X) (y : M) (v : TangentSpace I y),
      mfderiv I I Ψ y (J.freeze x y v) = J'.freeze x (Ψ y) (mfderiv I I Ψ y v))
    (hν : ∀ (x : X) (y : M) (w : TangentSpace 𝓘(ℝ, ℂ) x),
      mfderiv I I Ψ y (ν.val.tangentHom (x, y) w) = ν'.val.tangentHom (x, Ψ y) w) :
    IsWeakPseudoholomorphic J' ν' p (Ψ ∘ u) ↔ IsWeakPseudoholomorphic J ν p u := by
  rw [← isWeakPseudoholomorphicOn_univ, ← isWeakPseudoholomorphicOn_univ]
  exact Ψ.isWeakPseudoholomorphicOn_diffeomorph_comp_iff hJ hν

end TauCeti
