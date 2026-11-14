/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry

/-!
# The Sobolev space `H¹` under Riemannian isometries

A Riemannian isometry `Φ : M → N` between compact Riemannian manifolds preserves the Riemannian
volume and the pointwise inner product `⟪∇u, ∇v⟫` of gradients. Hence precomposition `u ↦ u ∘ Φ`
preserves the `H¹` inner product `∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV` of smooth functions, and it extends to
a linear isometric equivalence

`TauCeti.Manifold.SobolevH1.compRiemannianIsometry Φ : H¹(N) ≃ₗᵢ H¹(M)`.

It is compatible with the value maps into `L²`, where it is composition with the
measure-preserving map `Φ`, and it preserves the Dirichlet form `∫ ⟪∇u, ∇v⟫ dV`. It is
contravariantly functorial: the identity isometry acts trivially and `(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*`.
Hence, for a group acting on a closed Riemannian manifold by isometries, `q ↦ (q⁻¹)^*` acts on
`H¹` by linear isometries preserving the energy form, compatibly with the corresponding action on
`L²`.

## Main declarations

* `TauCeti.Manifold.SobolevH1.inner_ofSmooth_comp`: precomposition with a Riemannian isometry
  preserves the `H¹` inner product of smooth functions.
* `TauCeti.Manifold.SobolevH1.compRiemannianIsometry`: the induced linear isometric equivalence
  `H¹(N) ≃ₗᵢ H¹(M)`.
* `TauCeti.Manifold.SobolevH1.toLp_compRiemannianIsometry`: its value in `L²` is the composition
  of the value with `Φ`.
* `TauCeti.Manifold.SobolevH1.dirichletForm_compRiemannianIsometry`: it preserves the Dirichlet
  form.
* `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_refl`,
  `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_trans` and
  `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_symm`: functoriality.

## References

* P. Bérard, *Transplantation et isospectralité. I*, Math. Ann. 292 (1992), §II.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]

/-- Precomposition `u ↦ u ∘ Φ` with a Riemannian isometry, on smooth functions. -/
private def compSmooth (Φ : RiemannianIsometry I I' M N) :
    C^∞⟮I', N; ℝ⟯ ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun u := u.comp Φ.toDiffeomorph.toContMDiffMap
  invFun u := u.comp Φ.symm.toDiffeomorph.toContMDiffMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := ContMDiffMap.ext fun y ↦ congrArg u (Φ.apply_symm_apply y)
  right_inv u := ContMDiffMap.ext fun x ↦ congrArg u (Φ.symm_apply_apply x)

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M] [MeasurableSpace M]
  [BorelSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [CompactSpace N] [IsManifold I' 1 N] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- **Isometry invariance of the `H¹` inner product.** Precomposition with a Riemannian isometry
`Φ : M → N` preserves `∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV` for smooth functions `u`, `v` on `N`. -/
theorem inner_ofSmooth_comp (Φ : RiemannianIsometry I I' M N) (u v : C^∞⟮I', N; ℝ⟯) :
    ⟪ofSmooth (u.comp Φ.toDiffeomorph.toContMDiffMap),
        ofSmooth (v.comp Φ.toDiffeomorph.toContMDiffMap)⟫_ℝ =
      ⟪ofSmooth u, ofSmooth v⟫_ℝ := by
  have hΦ := Φ.measurePreserving_riemannianVolume
  have he : MeasurableEmbedding Φ := Φ.toDiffeomorph.toHomeomorph.measurableEmbedding
  have hu := u.contMDiff.mdifferentiable (by simp)
  have hv := v.contMDiff.mdifferentiable (by simp)
  have hgrad (x : M) :
      ⟪mgradient I (u.comp Φ.toDiffeomorph.toContMDiffMap) x,
          mgradient I (v.comp Φ.toDiffeomorph.toContMDiffMap) x⟫_ℝ =
        ⟪mgradient I' u (Φ x), mgradient I' v (Φ x)⟫_ℝ :=
    Φ.isLocalRiemannianIsometry.inner_mgradient_comp_comp (hu _) (hv _)
  rw [inner_ofSmooth, inner_ofSmooth]
  simp only [hgrad]
  congr 1
  · exact hΦ.integral_comp he fun y ↦ u y * v y
  · exact hΦ.integral_comp he fun y ↦ ⟪mgradient I' u y, mgradient I' v y⟫_ℝ

/-- Precomposition with a Riemannian isometry preserves the `H¹` norm of smooth functions. -/
private theorem norm_ofSmooth_compSmooth (Φ : RiemannianIsometry I I' M N)
    (u : C^∞⟮I', N; ℝ⟯) : ‖ofSmooth (compSmooth Φ u)‖ = ‖ofSmooth u‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (ofSmooth u)]
  exact congrArg Real.sqrt (inner_ofSmooth_comp Φ u u)

/-- **Pullback along a Riemannian isometry on `H¹`.** A Riemannian isometry `Φ : M → N` between
compact Riemannian manifolds induces the linear isometric equivalence `H¹(N) ≃ₗᵢ H¹(M)` which
sends the class of a smooth function `u` to the class of `u ∘ Φ`
(`TauCeti.Manifold.SobolevH1.compRiemannianIsometry_ofSmooth`). Its inverse is pullback along
`Φ.symm` (`TauCeti.Manifold.SobolevH1.compRiemannianIsometry_symm`). -/
def compRiemannianIsometry (Φ : RiemannianIsometry I I' M N) :
    SobolevH1 I' N ≃ₗᵢ[ℝ] SobolevH1 I M :=
  (compSmooth Φ).extendOfIsometry ofSmooth ofSmooth denseRange_ofSmooth denseRange_ofSmooth
    (norm_ofSmooth_compSmooth Φ)

/-- Pullback along a Riemannian isometry sends the class of a smooth function `u` to the class
of `u ∘ Φ`. -/
@[simp]
theorem compRiemannianIsometry_ofSmooth (Φ : RiemannianIsometry I I' M N)
    (u : C^∞⟮I', N; ℝ⟯) :
    compRiemannianIsometry Φ (ofSmooth u) =
      ofSmooth (u.comp Φ.toDiffeomorph.toContMDiffMap) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

/-- The inverse of pullback along `Φ` is pullback along `Φ.symm`. -/
@[simp]
theorem compRiemannianIsometry_symm (Φ : RiemannianIsometry I I' M N) :
    (compRiemannianIsometry Φ).symm = compRiemannianIsometry Φ.symm :=
  LinearIsometryEquiv.ext <| congrFun <| denseRange_ofSmooth.equalizer
    (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _) <| funext fun u ↦ by
      rw [Function.comp_apply, Function.comp_apply, compRiemannianIsometry_ofSmooth]
      exact LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ u

/-- Pullback along the identity isometry is the identity of `H¹(M)`. -/
@[simp]
theorem compRiemannianIsometry_refl :
    compRiemannianIsometry (RiemannianIsometry.refl I M) = LinearIsometryEquiv.refl ℝ _ :=
  LinearIsometryEquiv.ext <| congrFun <| denseRange_ofSmooth.equalizer
    (LinearIsometryEquiv.continuous _) continuous_id <| funext fun u ↦ by
      rw [Function.comp_apply, compRiemannianIsometry_ofSmooth]
      exact congrArg ofSmooth
        (ContMDiffMap.ext fun x ↦ congrArg u (RiemannianIsometry.refl_apply I M x))

/-- Pullback is contravariant: pulling back along `Ψ ∘ Φ` is pulling back along `Ψ` and then
along `Φ`. -/
theorem compRiemannianIsometry_trans
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [CompactSpace P] [IsManifold I'' 1 P]
    [MeasurableSpace P] [BorelSpace P] [RiemannianBundle (fun z : P ↦ TangentSpace I'' z)]
    [IsContinuousRiemannianBundle E (fun z : P ↦ TangentSpace I'' z)]
    (Φ : RiemannianIsometry I I' M N) (Ψ : RiemannianIsometry I' I'' N P) :
    compRiemannianIsometry (Φ.trans Ψ) =
      (compRiemannianIsometry Ψ).trans (compRiemannianIsometry Φ) :=
  LinearIsometryEquiv.ext <| congrFun <| denseRange_ofSmooth.equalizer
    (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _) <| funext fun u ↦ by
      rw [Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.trans_apply,
        compRiemannianIsometry_ofSmooth, compRiemannianIsometry_ofSmooth,
        compRiemannianIsometry_ofSmooth]
      exact congrArg ofSmooth (ContMDiffMap.ext fun x ↦ congrArg u (Φ.trans_apply Ψ x))

/-- **Compatibility with `L²`.** The value in `L²(M)` of the pullback of `w ∈ H¹(N)` along a
Riemannian isometry `Φ` is the composition of the value of `w` with the measure-preserving map
`Φ`. -/
theorem toLp_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N) (w : SobolevH1 I' N) :
    toLp (compRiemannianIsometry Φ w) =
      Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume (toLp w) := by
  have hΦ := Φ.measurePreserving_riemannianVolume
  refine congrFun (denseRange_ofSmooth.equalizer
    (g := fun w ↦ toLp (compRiemannianIsometry Φ w))
    (toLp.continuous.comp (LinearIsometryEquiv.continuous _))
    ((Lp.isometry_compMeasurePreserving hΦ).continuous.comp toLp.continuous)
    (funext fun u ↦ ?_)) w
  rw [Function.comp_apply, Function.comp_apply, compRiemannianIsometry_ofSmooth]
  refine Lp.ext ((toLp_ofSmooth_ae_eq _).trans ?_)
  refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving _ hΦ).symm)
  exact (hΦ.quasiMeasurePreserving.ae_eq_comp (toLp_ofSmooth_ae_eq u)).symm

/-- **Isometry invariance of the Dirichlet form.** Pullback along a Riemannian isometry
preserves the Dirichlet form, the extension of `∫ ⟪∇u, ∇v⟫ dV` to `H¹`. -/
@[simp]
theorem dirichletForm_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N)
    (w v : SobolevH1 I' N) :
    dirichletForm (compRiemannianIsometry Φ w) (compRiemannianIsometry Φ v) =
      dirichletForm w v := by
  rw [dirichletForm_apply, dirichletForm_apply, LinearIsometryEquiv.inner_map_map,
    toLp_compRiemannianIsometry, toLp_compRiemannianIsometry]
  congr 1
  exact LinearIsometry.inner_map_map (𝕜 := ℝ)
    (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ Φ Φ.measurePreserving_riemannianVolume) _ _

end TauCeti.Manifold.SobolevH1
