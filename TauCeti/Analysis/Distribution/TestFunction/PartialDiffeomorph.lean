/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Pushforward of test densities along partial diffeomorphisms

Let `Φ` be a smooth partial diffeomorphism of a finite-dimensional real normed space `E`, and let
`V`, `Ω` be open sets with `V` contained in the source of `Φ` and `Φ '' V ⊆ Ω`. A test function
`φ` on `V`, read as the density `φ dx`, pushes forward along `Φ` to the density

`(Φ_* φ) (y) = |det D(Φ⁻¹)(y)| φ (Φ⁻¹ y)`

on `Ω`, extended by zero off `Φ '' V`. By the change of variables formula,
`∫ (Φ_* φ) g = ∫ φ (g ∘ Φ)` for every locally integrable `g` on `Ω`, so the transpose of `Φ_*` is
the pullback of distributions along `Φ`, see `TauCeti.Analysis.Distribution.PartialDiffeomorph`.
The pushforward is a continuous linear map for the LF topologies
(`PartialDiffeomorph.pushforwardTestFunction`). It is the composite of three continuous linear
maps: composition with `Φ⁻¹`, which is the pullback `TestFunction.pullbackCLM` of test forms of
degree zero along `Φ⁻¹`, multiplication by the Jacobian `|det D(Φ⁻¹)|`, which is smooth on the
target of `Φ` only (`TestFunction.smulLeftCLMOfContDiffOn`, with
`PartialDiffeomorph.contDiffOn_abs_det_fderiv_symm`), and extension from `Ω ∩ target` to `Ω`.

## Main declarations

* `PartialDiffeomorph.pushforwardTestFunction`: the pushforward `φ ↦ |det D(Φ⁻¹)| (φ ∘ Φ⁻¹)` of
  test densities, as a continuous linear map `𝓓(V, G) →L[ℝ] 𝓓(Ω, G)`.
* `PartialDiffeomorph.pushforwardTestFunction_apply_of_mem_target`,
  `PartialDiffeomorph.pushforwardTestFunction_apply_of_notMem_target`: its values.
* `PartialDiffeomorph.pushforwardTestFunction_apply_apply`: `(Φ_* φ) (Φ x) = |det DΦ(x)|⁻¹ φ x`.
* `PartialDiffeomorph.tsupport_pushforwardTestFunction_subset`: `supp Φ_* φ ⊆ Φ '' supp φ`.
* `PartialDiffeomorph.pushforwardTestFunction_trans`: functoriality, `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`.
* `PartialDiffeomorph.pushforwardTestFunction_pushforwardTestFunction_symm`,
  `PartialDiffeomorph.pushforwardTestFunction_symm_pushforwardTestFunction`:
  `Φ_* ∘ (Φ⁻¹)_* = id` on test functions on a subset of the target, and `(Φ⁻¹)_* ∘ Φ_* = id`.
* `PartialDiffeomorph.pushforwardTestFunction_monoCLM`,
  `PartialDiffeomorph.monoCLM_pushforwardTestFunction`: compatibility with extending test
  functions to larger open sets.
* `PartialDiffeomorph.pushforwardTestFunction_smulLeftCLMOfContDiffOn`:
  `Φ_* ((g ∘ Φ) φ) = g Φ_* φ` for `g` smooth on `Ω`.
* `ContinuousLinearEquiv.pushforwardTestFunction_toPartialDiffeomorph`: for a linear automorphism
  `e`, `e_* φ = |det e|⁻¹ (φ ∘ e⁻¹)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (the pullback of
  distributions by a diffeomorphism, as the transpose of this pushforward of densities).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction ContinuousAlternatingMap
open scoped Distributions Manifold ContDiff

namespace PartialDiffeomorph

variable {E G G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
  {Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {V Ω : Opens E}

/-! ### Composition with the inverse -/

/-- The part `Ω ∩ target` of `Ω` on which the inverse of `Φ` is defined, as an open set. -/
private def targetOpens (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (Ω : Opens E) : Opens E :=
  Ω ⊓ ⟨Φ.target, Φ.open_target⟩

/-- Within `Ω ∩ target`, the preimage under `Φ⁻¹` of a subset `K` of `V` is `Φ '' K`. -/
private theorem targetOpens_inter_preimage_symm (hV : (V : Set E) ⊆ Φ.source)
    (hVΩ : MapsTo Φ V Ω) {K : Set E} (hKV : K ⊆ V) :
    (targetOpens Φ Ω : Set E) ∩ Φ.symm ⁻¹' K = Φ '' K := by
  have himage : Φ '' K = Φ.target ∩ Φ.symm ⁻¹' K :=
    Φ.toPartialEquiv.image_eq_target_inter_inv_preimage (hKV.trans hV)
  rw [himage, targetOpens, Opens.coe_inf, inter_assoc]
  exact inter_eq_self_of_subset_right (himage ▸ (hVΩ.mono_left hKV).image_subset)

/-- Composition `φ ↦ φ ∘ Φ⁻¹` of test functions on `V` with the inverse, as test functions on
`Ω ∩ target`. It is the pullback along `Φ⁻¹` of test forms of degree zero; since `Φ '' V ⊆ Ω`,
the inverse is proper from `Ω ∩ target` to `V`. -/
private def compSymmCLM (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hV : (V : Set E) ⊆ Φ.source) (hVΩ : MapsTo Φ V Ω) : 𝓓(V, G) →L[ℝ] 𝓓(targetOpens Φ Ω, G) :=
  postcompCLM ((constOfIsEmptyLIE ℝ E G (Fin 0)).symm.toContinuousLinearEquiv :
      (E [⋀^Fin 0]→L[ℝ] G) →L[ℝ] G) ∘L
    pullbackCLM (k := 0) Φ.symm
      (Φ.symm.contDiffOn.mono inter_subset_right)
      (fun K hK hKV ↦ by
        rw [targetOpens_inter_preimage_symm hV hVΩ hKV]
        exact hK.image_of_continuousOn (Φ.contMDiffOn.continuousOn.mono (hKV.trans hV))) ∘L
    postcompCLM ((constOfIsEmptyLIE ℝ E G (Fin 0)).toContinuousLinearEquiv :
      G →L[ℝ] (E [⋀^Fin 0]→L[ℝ] G))

/-- At a point of the target, composition with the inverse is evaluation at the inverse image. -/
private theorem compSymmCLM_apply_of_mem_target (hV : (V : Set E) ⊆ Φ.source)
    (hVΩ : MapsTo Φ V Ω) (φ : 𝓓(V, G)) {y : E} (hy : y ∈ Φ.target) :
    compSymmCLM Φ hV hVΩ φ y = φ (Φ.symm y) := by
  by_cases hyΩ : y ∈ (Ω : Set E)
  · simp [compSymmCLM, postcompCLM_apply,
      pullbackCLM_apply_of_mem (Ω := targetOpens Φ Ω) _ (⟨hyΩ, hy⟩ : y ∈ targetOpens Φ Ω)]
  · -- Off `Ω`, the inverse image lies outside `V`, where `φ` vanishes.
    have hyt : y ∉ targetOpens Φ Ω := fun h ↦ hyΩ h.1
    simp only [compSymmCLM, ContinuousLinearMap.comp_apply, postcompCLM_apply, Function.comp_apply,
      pullbackCLM_apply_of_notMem _ hyt, _root_.map_zero]
    refine (image_eq_zero_of_notMem_tsupport fun h ↦ hyΩ ?_).symm
    rw [← Φ.right_inv hy]
    exact hVΩ (φ.tsupport_subset h)

/-- Off the target, composition with the inverse vanishes. -/
private theorem compSymmCLM_apply_of_notMem_target (hV : (V : Set E) ⊆ Φ.source)
    (hVΩ : MapsTo Φ V Ω) (φ : 𝓓(V, G)) {y : E} (hy : y ∉ Φ.target) :
    compSymmCLM Φ hV hVΩ φ y = 0 := by
  simp [compSymmCLM, postcompCLM_apply,
    pullbackCLM_apply_of_notMem (Ω := targetOpens Φ Ω) _ (fun h ↦ hy h.2 : y ∉ targetOpens Φ Ω)]

/-! ### The pushforward of test densities -/

variable [FiniteDimensional ℝ E]

/-- The **pushforward of test densities along a partial diffeomorphism**: for `V` contained in
the source of `Φ` and `Φ '' V ⊆ Ω`, a test function `φ` on `V` gives the test function
`y ↦ |det D(Φ⁻¹)(y)| φ (Φ⁻¹ y)` on `Ω`, extended by zero off `Φ '' V`. It is the density
`φ dx` pushed forward along `Φ`, and its transpose is the pullback of distributions along `Φ`. -/
def pushforwardTestFunction (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hV : (V : Set E) ⊆ Φ.source) (hVΩ : MapsTo Φ V Ω) : 𝓓(V, G) →L[ℝ] 𝓓(Ω, G) :=
  monoCLM ℝ ∘L smulLeftCLMOfContDiffOn
    ((Φ.contDiffOn_abs_det_fderiv_symm (m := ⊤) (by simp)).mono inter_subset_right) ∘L
    compSymmCLM Φ hV hVΩ

variable {hV : (V : Set E) ⊆ Φ.source} {hVΩ : MapsTo Φ V Ω}

/-- The pushforward of `φ` is the Jacobian `|det D(Φ⁻¹)|` times `φ ∘ Φ⁻¹`, on `Ω ∩ target`. -/
private theorem pushforwardTestFunction_apply (φ : 𝓓(V, G)) (y : E) :
    Φ.pushforwardTestFunction hV hVΩ φ y =
      |(fderiv ℝ Φ.symm y).det| • compSymmCLM Φ hV hVΩ φ y := by
  rw [pushforwardTestFunction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    monoCLM_apply, ite_eq_left ⟨le_rfl, inf_le_left⟩, smulLeftCLMOfContDiffOn_apply]

/-- At a point `y` of the target, the pushforward of `φ` is `|det D(Φ⁻¹)(y)| φ (Φ⁻¹ y)`. -/
theorem pushforwardTestFunction_apply_of_mem_target (φ : 𝓓(V, G)) {y : E} (hy : y ∈ Φ.target) :
    Φ.pushforwardTestFunction hV hVΩ φ y = |(fderiv ℝ Φ.symm y).det| • φ (Φ.symm y) := by
  rw [pushforwardTestFunction_apply, compSymmCLM_apply_of_mem_target hV hVΩ φ hy]

/-- Off the target, the pushforward vanishes. -/
@[simp]
theorem pushforwardTestFunction_apply_of_notMem_target (φ : 𝓓(V, G)) {y : E}
    (hy : y ∉ Φ.target) : Φ.pushforwardTestFunction hV hVΩ φ y = 0 := by
  rw [pushforwardTestFunction_apply, compSymmCLM_apply_of_notMem_target hV hVΩ φ hy, smul_zero]

/-- At the image `Φ x` of a point of the source, the pushforward of `φ` is
`|det DΦ(x)|⁻¹ φ x`. -/
@[simp]
theorem pushforwardTestFunction_apply_apply (φ : 𝓓(V, G)) {x : E} (hx : x ∈ Φ.source) :
    Φ.pushforwardTestFunction hV hVΩ φ (Φ x) = |(fderiv ℝ Φ x).det|⁻¹ • φ x := by
  rw [pushforwardTestFunction_apply_of_mem_target φ (Φ.map_source hx), Φ.left_inv hx,
    Φ.det_fderiv_symm_apply (by simp) hx, abs_inv]

/-- **Support of a pushforward.** The pushforward of `φ` is supported in `Φ '' supp φ`. -/
theorem tsupport_pushforwardTestFunction_subset (φ : 𝓓(V, G)) :
    tsupport (Φ.pushforwardTestFunction hV hVΩ φ) ⊆ Φ '' tsupport φ := by
  have hc : IsCompact (Φ '' tsupport φ) := φ.hasCompactSupport.isCompact.image_of_continuousOn
    (Φ.contMDiffOn.continuousOn.mono (φ.tsupport_subset.trans hV))
  refine closure_minimal (fun y hy ↦ ?_) hc.isClosed
  by_cases hyt : y ∈ Φ.target
  · rw [Function.mem_support, pushforwardTestFunction_apply_of_mem_target φ hyt] at hy
    exact ⟨Φ.symm y, subset_tsupport _ (right_ne_zero_of_smul hy), Φ.right_inv hyt⟩
  · exact absurd (pushforwardTestFunction_apply_of_notMem_target φ hyt) hy

/-- The pushforward commutes with postcomposition by a continuous linear map. -/
theorem pushforwardTestFunction_postcompCLM (L : G →L[ℝ] G') (φ : 𝓓(V, G)) :
    Φ.pushforwardTestFunction hV hVΩ (postcompCLM L φ) =
      postcompCLM L (Φ.pushforwardTestFunction hV hVΩ φ) := by
  ext y
  by_cases hy : y ∈ Φ.target
  · simp [pushforwardTestFunction_apply_of_mem_target _ hy, postcompCLM_apply]
  · simp [pushforwardTestFunction_apply_of_notMem_target _ hy, postcompCLM_apply]

/-- **Functoriality.** Pushing forward along a composite `Ψ ∘ Φ` of partial diffeomorphisms is
pushing forward along `Φ` and then along `Ψ`. -/
theorem pushforwardTestFunction_trans {W : Opens E}
    {Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} (hΩ : (Ω : Set E) ⊆ Ψ.source)
    (hΩW : MapsTo Ψ Ω W) (hVt : (V : Set E) ⊆ (Φ.trans Ψ).source)
    (hVW : MapsTo (Φ.trans Ψ) V W) (φ : 𝓓(V, G)) :
    (Φ.trans Ψ).pushforwardTestFunction hVt hVW φ =
      Ψ.pushforwardTestFunction hΩ hΩW (Φ.pushforwardTestFunction hV hVΩ φ) := by
  ext y
  by_cases hyΨ : y ∈ Ψ.target
  · rw [Ψ.pushforwardTestFunction_apply_of_mem_target _ hyΨ]
    by_cases hyΦ : Ψ.symm y ∈ Φ.target
    · have hyt : y ∈ (Φ.trans Ψ).target := by rw [trans_target]; exact ⟨hyΨ, hyΦ⟩
      rw [pushforwardTestFunction_apply_of_mem_target _ hyt,
        Φ.pushforwardTestFunction_apply_of_mem_target _ hyΦ, coe_trans_symm, smul_smul]
      congr 1
      -- The chain rule `D(Φ⁻¹ ∘ Ψ⁻¹)(y) = D(Φ⁻¹)(Ψ⁻¹ y) ∘ D(Ψ⁻¹)(y)` and multiplicativity of
      -- the determinant.
      rw [Function.comp_def, fderiv_fun_comp y (Φ.symm.differentiableAt (by simp) hyΦ)
        (Ψ.symm.differentiableAt (by simp) hyΨ), ContinuousLinearMap.det,
        ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul, mul_comm]
    · have hyt : y ∉ (Φ.trans Ψ).target := by rw [trans_target]; exact fun h ↦ hyΦ h.2
      rw [pushforwardTestFunction_apply_of_notMem_target _ hyt,
        Φ.pushforwardTestFunction_apply_of_notMem_target _ hyΦ, smul_zero]
  · have hyt : y ∉ (Φ.trans Ψ).target := by rw [trans_target]; exact fun h ↦ hyΨ h.1
    rw [pushforwardTestFunction_apply_of_notMem_target _ hyt,
      Ψ.pushforwardTestFunction_apply_of_notMem_target _ hyΨ]

/-- Pushing forward along `Φ⁻¹` and then along `Φ` gives back a test function on a subset `Ω` of
the target that `Φ⁻¹` maps into `V`. -/
@[simp]
theorem pushforwardTestFunction_pushforwardTestFunction_symm (hΩ : (Ω : Set E) ⊆ Φ.symm.source)
    (hΩV : MapsTo Φ.symm Ω V) (φ : 𝓓(Ω, G)) :
    Φ.pushforwardTestFunction hV hVΩ (Φ.symm.pushforwardTestFunction hΩ hΩV φ) = φ := by
  ext y
  by_cases hy : y ∈ Φ.target
  · have hys : Φ.symm y ∈ Φ.symm.target := Φ.map_target hy
    rw [pushforwardTestFunction_apply_of_mem_target _ hy,
      Φ.symm.pushforwardTestFunction_apply_of_mem_target _ hys, smul_smul]
    -- The two Jacobians are reciprocal: `|det DΦ(Φ⁻¹ y)| |det D(Φ⁻¹)(y)| = 1`.
    -- `Φ.symm.symm` has the underlying partial equivalence of `Φ`, by `PartialEquiv.symm_symm`.
    have hΦ : ⇑Φ.symm.symm = ⇑Φ := rfl
    rw [hΦ, Φ.right_inv hy, ← abs_mul, mul_comm,
      Φ.det_fderiv_mul_det_fderiv_symm (by simp) hy, abs_one, one_smul]
  · rw [pushforwardTestFunction_apply_of_notMem_target _ hy, eq_comm]
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hy (hΩ (φ.tsupport_subset h))

/-- Pushing forward along `Φ` and then along `Φ⁻¹` gives back a test function on `V`, when `Φ`
maps `V` into a subset `Ω` of the target that `Φ⁻¹` maps back into `V`. -/
@[simp]
theorem pushforwardTestFunction_symm_pushforwardTestFunction (hΩ : (Ω : Set E) ⊆ Φ.symm.source)
    (hΩV : MapsTo Φ.symm Ω V) (φ : 𝓓(V, G)) :
    Φ.symm.pushforwardTestFunction hΩ hΩV (Φ.pushforwardTestFunction hV hVΩ φ) = φ :=
  Φ.symm.pushforwardTestFunction_pushforwardTestFunction_symm hV hVΩ φ

/-- Extending a test function from `V' ≤ V` to `V` and then pushing it forward is pushing it
forward from `V'`. -/
theorem pushforwardTestFunction_monoCLM {V' : Opens E} (hV'V : V' ≤ V) (φ : 𝓓(V', G)) :
    Φ.pushforwardTestFunction hV hVΩ (monoCLM ℝ φ) =
      Φ.pushforwardTestFunction ((show (V' : Set E) ⊆ V from hV'V).trans hV)
        (hVΩ.mono_left hV'V) φ := by
  ext y
  by_cases hy : y ∈ Φ.target
  · simp [pushforwardTestFunction_apply_of_mem_target _ hy, monoCLM_apply, hV'V]
  · simp [hy]

/-- Pushing a test function forward to `Ω` and extending it to `Ω' ≥ Ω` is pushing it forward to
`Ω'`. -/
theorem monoCLM_pushforwardTestFunction {Ω' : Opens E} (hΩΩ' : Ω ≤ Ω') (φ : 𝓓(V, G)) :
    (monoCLM ℝ (Φ.pushforwardTestFunction hV hVΩ φ) : 𝓓(Ω', G)) =
      Φ.pushforwardTestFunction hV (hVΩ.mono_right (show (Ω : Set E) ⊆ Ω' from hΩΩ')) φ := by
  ext y
  rw [monoCLM_apply, ite_eq_left ⟨le_rfl, hΩΩ'⟩]
  by_cases hy : y ∈ Φ.target
  · rw [pushforwardTestFunction_apply_of_mem_target _ hy,
      pushforwardTestFunction_apply_of_mem_target _ hy]
  · rw [pushforwardTestFunction_apply_of_notMem_target _ hy,
      pushforwardTestFunction_apply_of_notMem_target _ hy]

/-- The pushforward intertwines multiplication by `g ∘ Φ` with multiplication by `g`, for `g`
smooth on `Ω`: `Φ_* ((g ∘ Φ) φ) = g Φ_* φ`. -/
theorem pushforwardTestFunction_smulLeftCLMOfContDiffOn {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g Ω)
    (φ : 𝓓(V, G)) :
    Φ.pushforwardTestFunction hV hVΩ (smulLeftCLMOfContDiffOn
        (hg.comp (Φ.contDiffOn.mono hV) hVΩ) φ) =
      smulLeftCLMOfContDiffOn hg (Φ.pushforwardTestFunction hV hVΩ φ) := by
  ext y
  by_cases hy : y ∈ Φ.target
  · simp only [pushforwardTestFunction_apply_of_mem_target _ hy, smulLeftCLMOfContDiffOn_apply,
      Function.comp_apply, Φ.right_inv hy, smul_comm |(fderiv ℝ Φ.symm y).det| (g y)]
  · simp [hy]

/-- For a linear automorphism `e` of `E`, the pushforward of test densities is
`φ ↦ |det e|⁻¹ (φ ∘ e⁻¹)`. -/
theorem _root_.ContinuousLinearEquiv.pushforwardTestFunction_toPartialDiffeomorph
    (e : E ≃L[ℝ] E) (hVΩ : MapsTo e V Ω) (φ : 𝓓(V, G)) :
    (e.toPartialDiffeomorph (n := ∞)).pushforwardTestFunction (by simp) (by simpa using hVΩ) φ =
      |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • e.transportTestFunction hVΩ φ := by
  ext y
  have hsymm : ⇑(e.toPartialDiffeomorph (n := ∞)).symm = e.symm := by ext; simp
  rw [pushforwardTestFunction_apply_of_mem_target _ (by simp), hsymm, e.symm.fderiv,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearEquiv.transportTestFunction_apply]
  -- `ContinuousLinearMap.det` is the determinant of the underlying linear map.
  rw [e.det_coe_symm, abs_inv]
  rfl

end PartialDiffeomorph
