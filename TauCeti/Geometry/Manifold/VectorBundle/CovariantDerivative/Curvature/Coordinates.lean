/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Frame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Curvature in a coordinate frame

The `l`-th coefficient of `R(∂ᵢ, ∂ⱼ)∂ₖ` is
`∂ᵢΓˡⱼₖ - ∂ⱼΓˡᵢₖ + ∑ₘ (Γᵐⱼₖ Γˡᵢₘ - Γᵐᵢₖ Γˡⱼₘ)`.
The first two arguments are the curvature directions, the third is the vector being
differentiated, and the last index is the output coefficient.

Both the vector-valued expansion and its scalar coefficients are provided. They use the
existing tangent trivialization and `TauCeti.Manifold.christoffelSymbol`, so an explicit
metric's Christoffel calculation can be substituted directly to compute its curvature.
Only `C¹` regularity of the connection on the chosen chart is required. The manifold is
`C³` over the real or complex numbers, and analytic over other complete normed fields,
as prescribed by `minSmoothness`. No metric or torsion hypothesis is needed. The formulas
hold on chart sources, including boundary points.

For a smooth connection on a smooth real vector bundle (and in particular on the tangent bundle),
the pointwise curvature tensor has the same expansion in terms of the model-space Christoffel map
`Γ` (`TauCeti.Manifold.bundleChristoffelMap` / `TauCeti.Manifold.christoffelMap`): on vectors with
coordinates `a`, `c` and `w`, the curvature `R(a, c)w` has coordinates

`dΓ(a)(w, c) - dΓ(c)(w, a) + Γ(Γ(w, c), a) - Γ(Γ(w, a), c)`,

where `Γ(v, u)` is the coordinate vector of `∇_u` applied to the section with constant coordinates
`v` (`CovariantDerivative.curvatureTensor_symm_trivializationAt_bundle` and
`CovariantDerivative.curvatureTensor_symm_trivializationAt`). Covariant derivatives along curves,
parametrized surfaces, and Frobenius total differential systems are computed with `Γ` as a bilinear
map rather than through its scalar symbols, so this is the form in which their commutators are
compared with the curvature.

The sign convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7, pp. 196–198:
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/

public section

noncomputable section

open Bundle FiberBundle Module Set TauCeti
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti.Manifold

section Frame

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (minSmoothness 𝕜 3) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E) (x₀ : M)

local notation "e" => trivializationAt E (TangentSpace I) x₀
variable [ContMDiffCovariantDerivativeOn E 1 cov.toFun
  (trivializationAt E (TangentSpace I) x₀).baseSet]

local notation "Γ" => christoffelSymbol I b e cov
local notation "X" => Bundle.Trivialization.localFrame (trivializationAt E (TangentSpace I) x₀) b

/-- The coordinate expansion of `R(∂ᵢ, ∂ⱼ)∂ₖ`. Its coefficients are the difference of
the directional derivatives of the Christoffel symbols plus their quadratic contraction.
This is valid for any `C¹` connection, without a metric or a torsion hypothesis. -/
theorem curvatureOperator_localFrame_eq_sum {x : M}
    (hx : x ∈ (extChartAt I x₀).source) (i j k : ι) :
    cov.curvatureOperator (X i) (X j) (X k) x =
      ∑ l, (mvfderiv I (Γ j k l) x (X i x) - mvfderiv I (Γ i k l) x (X j x) +
        ∑ m, (Γ j k m x * Γ i m l x - Γ i k m x * Γ j m l x)) • X l x := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : IsManifold I 3 M :=
    IsManifold.of_le (n := minSmoothness 𝕜 3) (le_minSmoothness (𝕜 := 𝕜))
  have : IsManifold I (2 + 1) M :=
    IsManifold.of_le (n := minSmoothness 𝕜 3)
      (le_trans (by norm_num) (le_minSmoothness (𝕜 := 𝕜)))
  have : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : x ∈ (e).baseSet := by simpa using hx
  let hs := (e).isLocalFrameOn_localFrame_baseSet I 2 b
  rw [hs.coeff_sum_eq (cov.curvatureOperator (X i) (X j) (X k)) hbase]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h := hs.coeff_curvatureOperator_frame (e).open_baseSet cov hbase i j k l
  have : IsManifold I (minSmoothness 𝕜 2) M :=
    IsManifold.of_le (n := minSmoothness 𝕜 3)
      (minSmoothness_monotone (𝕜 := 𝕜) (by norm_num))
  have hΓ (a c d : ι) (y : M) : hs.coeff d y (cov (X c) y (X a y)) = Γ a c d y := by
    rw [christoffelSymbol_apply]
    -- The coefficient functional is independent of the frame's regularity index.
    rfl
  rw [mlieBracket_localFrame_trivializationAt b x₀ hx i j] at h
  simp only [map_zero, zero_mul, Finset.sum_const_zero, sub_zero, hΓ] at h
  exact congrArg (fun c ↦ c • X l x) h

/-- The scalar coordinate formula for `R(∂ᵢ, ∂ⱼ)∂ₖ`, in the output component `l`.
The order of the indices agrees with `christoffelSymbol`: `Γ i k l` is the `l`-th
component of `∇_{∂ᵢ} ∂ₖ`. -/
theorem localFrameCoeff_curvatureOperator {x : M}
    (hx : x ∈ (extChartAt I x₀).source) (i j k l : ι) :
    (e).localFrameCoeff I b l x (cov.curvatureOperator (X i) (X j) (X k) x) =
      mvfderiv I (Γ j k l) x (X i x) - mvfderiv I (Γ i k l) x (X j x) +
        ∑ m, (Γ j k m x * Γ i m l x - Γ i k m x * Γ j m l x) := by
  classical
  have hbase : x ∈ (e).baseSet := by simpa using hx
  rw [curvatureOperator_localFrame_eq_sum cov b x₀ hx i j k]
  simp [localFrameCoeff_localFrame b hbase]

end Frame

section BundleTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) (x₀ : M)

/-- **The curvature tensor of a vector-bundle connection in preferred trivializations**, in terms
of `Γ = bundleChristoffelMap b (trivializationAt E (TangentSpace I) x₀) ∇`. On tangent vectors with
coordinates `a` and `c` and a fibre vector with coordinates `w`, the curvature `R(a, c)w` has
coordinates `dΓ(a)(w, c) - dΓ(c)(w, a) + Γ(Γ(w, c), a) - Γ(Γ(w, a), c)`. -/
theorem curvatureTensor_symm_trivializationAt_bundle {x : M}
    (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hx : x ∈ (extChartAt I x₀).source) (a c : E) (w : F) :
    letI eV := trivializationAt F V x₀
    letI eT := trivializationAt E (TangentSpace I) x₀
    letI Γ := bundleChristoffelMap b eT (cov.isCovariantDerivativeOn (s := eV.baseSet))
    cov.curvatureTensor x (eT.symm x a) (eT.symm x c) (eV.symm x w) =
      eV.symm x (mvfderiv I Γ x (eT.symm x a) w c - mvfderiv I Γ x (eT.symm x c) w a +
        Γ x (Γ x w c) a - Γ x (Γ x w a) c) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let O := eV.baseSet ∩ eT.baseSet
  have hxT : x ∈ eT.baseSet := by simpa [eT] using hx
  have hxO : x ∈ O := ⟨hxV, hxT⟩
  have hOopen : IsOpen O := eV.open_baseSet.inter eT.open_baseSet
  have hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set Γ := bundleChristoffelMap b eT hcov
  have hΓ : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ x :=
    ((contMDiffOn_bundleChristoffelMap (n := ∞) b eT hcov).contMDiffAt
      (hOopen.mem_nhds hxO)).mdifferentiableAt (by simp)
  have hX (u : E) : CMDiff[O] ∞ (T% (fun y ↦ eT.symm y u)) :=
    (contMDiffOn_symm_baseSet u).mono inter_subset_right
  have hσw : CMDiff[O] ∞ (T% (fun y ↦ eV.symm y w)) :=
    (contMDiffOn_symm_baseSet w).mono inter_subset_left
  -- Coordinate vector fields commute, so curvature reduces to a commutator of covariant
  -- derivatives.
  have h := cov.curvatureTensor_apply_of_contMDiffOn x hOopen hxO (hX a) (hX c) hσw
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  rw [h, curvatureOperator_apply, mlieBracket_symm_trivializationAt x₀ hx a c, map_zero, sub_zero]
  -- Compute each iterated derivative via `covariantDerivative_symm_comp_apply_symm_bundle`.
  have hinner (v v' : E) :
      cov (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v')) x (eT.symm x v) =
        eV.symm x (mvfderiv I Γ x (eT.symm x v) w v' + Γ x (Γ x w v') v) := by
    have hL_diff : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ Γ y w v') x :=
      (hΓ.clm_apply mdifferentiableAt_const).clm_apply mdifferentiableAt_const
    have hL_mv : mvfderiv I (fun y ↦ Γ y w v') x (eT.symm x v) =
        mvfderiv I Γ x (eT.symm x v) w v' :=
      mvfderiv_clm_apply_const_apply₂ hΓ w v' (eT.symm x v)
    have hsmooth : CMDiff[O] ∞
        (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) :=
      ContMDiffOn.clm_bundle_apply
        ((ContMDiffCovariantDerivativeOn.contMDiff
          (contMDiffOn_symm_baseSet (e := eV) (n := ∞ + 1) w)).mono inter_subset_left)
        (hX v')
    have heq : ∀ᶠ y in 𝓝 x, cov (fun z ↦ eV.symm z w) y (eT.symm y v') = eV.symm y (Γ y w v') :=
      Filter.eventually_of_mem (hOopen.mem_nhds hxO) fun y hy ↦
        covariantDerivative_symm_apply_symm_bundle b eT hcov hy.1 hy.2 w v'
    have hd₁ : MDiffAt (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) x :=
      (hsmooth.contMDiffAt (hOopen.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hd₂ : MDiffAt (T% (fun y ↦ eV.symm y (Γ y w v'))) x :=
      hd₁.congr_of_eventuallyEq (heq.mono fun y hy ↦ by simp only [hy])
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hd₁ hd₂ Filter.univ_mem heq,
      covariantDerivative_symm_comp_apply_symm_bundle b eT hcov hxV hxT hL_diff v, hL_mv]
  have hsub (A B : F) : eV.symm x A - eV.symm x B = eV.symm x (A - B) := by
    simp only [← eV.symmL_apply (R := ℝ) hxV, map_sub]
  rw [hinner a c, hinner c a, hsub]
  congr 1
  abel

end BundleTensor

section Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (x₀ : M)

local notation "e" => trivializationAt E (TangentSpace I) x₀

/-- **The curvature tensor in a chart**, in terms of the model-space Christoffel map
`Γ = christoffelMap b ∇` of the chart at `x₀`. On tangent vectors with coordinates `a`, `c` and
`w`, the curvature `R(a, c)w` has coordinates
`dΓ(a)(w, c) - dΓ(c)(w, a) + Γ(Γ(w, c), a) - Γ(Γ(w, a), c)`. -/
theorem curvatureTensor_symm_trivializationAt {x : M} (hx : x ∈ (extChartAt I x₀).source)
    (a c w : E) :
    letI Γ := christoffelMap b (cov.isCovariantDerivativeOn (s := (e).baseSet))
    cov.curvatureTensor x ((e).symm x a) ((e).symm x c) ((e).symm x w) =
      (e).symm x (mvfderiv I Γ x ((e).symm x a) w c - mvfderiv I Γ x ((e).symm x c) w a +
        Γ x (Γ x w c) a - Γ x (Γ x w a) c) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rw [christoffelMap_eq_bundleChristoffelMap]
  exact cov.curvatureTensor_symm_trivializationAt_bundle b x₀ (by simpa using hx) hx a c w

end Tensor

end CovariantDerivative
