/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import TauCeti.Topology.VectorBundle.Subbundle
import TauCeti.LinearAlgebra.TotallyReal.Frame
import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# Projection onto a maximal totally real subbundle

For a family `L` of real subspaces of the fibres of a complex vector bundle `V` whose fibres are
maximal totally real, `V x = L x ⊕ i L x`, and the projection of `V x` onto `L x` along `i L x` is
a continuous real-linear endomorphism of the fibre (`TauCeti.totallyRealProjection`). A real
local frame of `L` is then a complex basis of each such fibre
(`TauCeti.IsSubbundleFrameOn.complexBasis`).

Read in a trivialization, a real local frame `X` of `L` becomes the complex-linear frame operator
`c ↦ ∑ i, c i • X i`, which is bijective exactly where the fibre of `L` is maximal totally real
(`TauCeti.IsSubbundleFrameOn.bijective_trivOperator`). Since invertibility is an open condition
and the frame operator of a continuous frame is continuous, maximal total reality is an open
condition along a continuous frame (`TauCeti.eventually_isMaximalTotallyReal`).

## Main declarations

* `TauCeti.totallyRealProjection`: the projection of a fibre onto a maximal totally real
  subspace `L x` along `i L x`.
* `TauCeti.IsSubbundleFrameOn.complexBasis`: a real local frame of a maximal totally real
  fibre, as a complex basis of the fibre.
* `TauCeti.IsSubbundleFrameOn.bijective_trivOperator`: a real frame of a maximal totally real
  fibre is a complex basis, so its frame operator is bijective.
* `TauCeti.eventually_isMaximalTotallyReal`: along a continuous frame, maximal total reality is an
  open condition.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3, for maximal totally real boundary
  conditions.
-/

public noncomputable section

open Bundle FiberBundle Function Set
open scoped Topology

namespace TauCeti

section ComplexBasis

variable {B F : Type*} [TopologicalSpace B] {V : B → Type*} [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] {ι : Type*} {L : ∀ x, Submodule ℝ (V x)}
  {σ : ι → Π x, V x} {U : Set B}

/-- At a point where `L` is maximal totally real, a real local frame of `L` is a complex basis
of the fibre of `V`. -/
def IsSubbundleFrameOn.complexBasis (hX : IsSubbundleFrameOn F L σ U) {x : B} (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    Module.Basis ι ℂ (V x) :=
  hL.complexBasis (hX.basis hx)

theorem IsSubbundleFrameOn.complexBasis_def (hX : IsSubbundleFrameOn F L σ U) {x : B}
    (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    hX.complexBasis hx hL = hL.complexBasis (hX.basis hx) :=
  (rfl)

@[simp]
theorem IsSubbundleFrameOn.coe_complexBasis (hX : IsSubbundleFrameOn F L σ U) {x : B}
    (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ⇑(hX.complexBasis hx hL) = (σ · x) := by
  ext i
  simp [complexBasis_def, hX.coe_basis hx]

/-- The complex coordinates of a vector of `L x` in `hX.complexBasis hx hL` are its real
coordinates in the frame basis `hX.basis hx`. -/
@[simp]
theorem IsSubbundleFrameOn.complexBasis_repr_coe (hX : IsSubbundleFrameOn F L σ U) {x : B}
    (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (v : L x) (i : ι) :
    (hX.complexBasis hx hL).repr v i = (hX.basis hx).repr v i := by
  rw [complexBasis_def, hL.complexBasis_repr_coe]

end ComplexBasis

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {ι : Type*} {L : ∀ x, Submodule ℝ (V x)}

local instance realFormProjectionTopVectorBundleReal : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (F) in
/-- The projection of a fibre onto a maximal totally real subspace along its `i`-image, as a
continuous real-linear map. It is continuous because the fibre is finite-dimensional. -/
def totallyRealProjection {x : B} {L : Submodule ℝ (V x)}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) L) :
    V x →L[ℝ] V x where
  toLinearMap := L.projection _ hL.isCompl
  cont := by
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
    let f : F →ₗ[ℝ] F := e.toLinearEquiv.toLinearMap ∘ₗ L.projection _ hL.isCompl ∘ₗ
      e.symm.toLinearEquiv.toLinearMap
    have hf : ⇑(L.projection _ hL.isCompl) = e.symm ∘ f ∘ e := by
      funext v
      simp [f]
    -- The `cont` field is stated for the bare `toFun` of the linear map; restate it for the
    -- function coercion so that `hf` can rewrite it.
    change Continuous ⇑(L.projection _ hL.isCompl)
    rw [hf]
    exact e.symm.continuous.comp (f.continuous_of_finiteDimensional.comp e.continuous)

/-- Evaluation of the fibrewise projection. -/
@[simp]
theorem totallyRealProjection_apply {x : B} {L : Submodule ℝ (V x)}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) L)
    (v : V x) : totallyRealProjection F hL v = L.projection _ hL.isCompl v :=
  (rfl)

section Frame

variable {U : Set B} {X : ι → Π x, V x}

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- Read in the trivialization at `x₀`, a real frame `X` of `L` on `U` is the complex-linear
operator `c ↦ ∑ i, c i • X i y`. At a point of `U` where `L` is maximal totally real, this
operator is bijective: the real frame of `L y` is a complex basis of `V y`. -/
theorem IsSubbundleFrameOn.bijective_trivOperator [Fintype ι] (hX : IsSubbundleFrameOn F L X U)
    {x₀ y : B} (hyU : y ∈ U) (hy : y ∈ (trivializationAt F V x₀).baseSet)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y)) :
    Function.Bijective (IsSubbundleFrameOn.trivOperator ℂ F X x₀ y) := by
  set e := trivializationAt F V x₀
  let b := hX.complexBasis hyU hL
  have h : ⇑(IsSubbundleFrameOn.trivOperator ℂ F X x₀ y) =
      e.continuousLinearEquivAt ℂ y hy ∘ b.equivFun.symm := by
    funext c
    rw [Function.comp_apply, IsSubbundleFrameOn.trivOperator_apply hy,
      Trivialization.continuousLinearEquivAt_apply, Module.Basis.equivFun_symm_apply]
    simp [b, e]
  rw [h]
  exact (ContinuousLinearEquiv.bijective _).comp b.equivFun.symm.bijective

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- Conversely, where the frame operator is bijective, `L` is maximal totally real. -/
private theorem isMaximalTotallyReal_of_bijective_trivOperator [Fintype ι]
    (hX : IsSubbundleFrameOn F L X U)
    {x₀ y : B} (hyU : y ∈ U) (hy : y ∈ (trivializationAt F V x₀).baseSet)
    (hA : Function.Bijective (IsSubbundleFrameOn.trivOperator ℂ F X x₀ y)) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) := by
  set e := trivializationAt F V x₀
  let T : (ι → ℝ) →ₗ[ℝ] V y := Fintype.linearCombination ℝ (X · y)
  have hT : LinearMap.range T = L y := by
    rw [Fintype.range_linearCombination, hX.span_eq hyU]
  -- The doubled frame `(a, b) ↦ ∑ a i • X i y + i ∑ b i • X i y` is the frame operator applied
  -- to `a + i b`.
  let φ : (ι → ℝ) × (ι → ℝ) ≃ (ι → ℂ) :=
    (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ ℝ) (fun _ ↦ ℝ)).symm.trans
      (Equiv.piCongrRight fun _ ↦ Complex.equivRealProd.symm)
  have hφ (p : (ι → ℝ) × (ι → ℝ)) (i : ι) : φ p i = p.1 i + p.2 i * Complex.I :=
    Complex.equivRealProd_symm_apply _
  have hcoprod : ⇑(T.coprod (((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ).comp T)) =
      (e.continuousLinearEquivAt ℂ y hy).symm ∘ IsSubbundleFrameOn.trivOperator ℂ F X x₀ y ∘ φ := by
    funext p
    have hsmul (a : ℝ) (v : V y) : (a : ℂ) • v = a • v := algebraMap_smul ℂ a v
    rw [Function.comp_apply, Function.comp_apply, IsSubbundleFrameOn.trivOperator_apply hy,
      Trivialization.continuousLinearEquivAt_symm_apply, e.symm_apply_apply_mk hy]
    simp only [LinearMap.coprod_apply, LinearMap.comp_apply, T, Fintype.linearCombination_apply,
      LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, hφ, Finset.smul_sum, add_smul,
      Finset.sum_add_distrib, hsmul, mul_comm _ Complex.I, mul_smul]
  rw [← hT]
  refine isMaximalTotallyReal_range_of_bijective_coprod ?_
  rw [hcoprod]
  exact (ContinuousLinearEquiv.bijective _).comp (hA.comp φ.bijective)

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- **Maximal total reality is an open condition along a frame.** If `L` has a continuous local
frame on an open set `U` and its fibre at `x₀ ∈ U` is maximal totally real, then so are its fibres
at all points near `x₀`. -/
theorem eventually_isMaximalTotallyReal [Finite ι] (hU : IsOpen U)
    (hX : IsSubbundleFrameOn F L X U) {x₀ : B} (hx₀ : x₀ ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀)) :
    ∀ᶠ y in 𝓝 x₀,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) := by
  let := Fintype.ofFinite ι
  set e := trivializationAt F V x₀
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
  let A : B → (ι → ℂ) →L[ℂ] F := IsSubbundleFrameOn.trivOperator ℂ F X x₀
  have hA : ContinuousAt A x₀ := IsSubbundleFrameOn.continuousAt_trivOperator fun i ↦
    (hX.continuousOn i).continuousAt (hU.mem_nhds hx₀)
  have hinv : (A x₀).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (A x₀ : (ι → ℂ) →ₗ[ℂ] F)
      (hX.bijective_trivOperator hx₀ he₀ hL)).toContinuousLinearEquiv, rfl⟩
  filter_upwards [hA.eventually_mem
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds (x := A x₀) hinv),
    hU.mem_nhds hx₀, e.open_baseSet.mem_nhds he₀] with y hAy hyU hye
  exact isMaximalTotallyReal_of_bijective_trivOperator hX hyU hye hAy.bijective

end Frame

end TauCeti
