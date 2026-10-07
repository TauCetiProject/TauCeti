/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of adapted pseudo-gradients

Every Morse function on a compact boundaryless manifold, modelled on a finite-dimensional real
normed space, has a pseudo-gradient field adapted to it
(`TauCeti.IsMorse.exists_isAdaptedPseudoGradient`).

The proof follows Audin and Damian. Near each critical point the field is the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` of a Morse chart, pulled back to the manifold (`TauCeti.MorseChart.field`). Near a
regular point it is a constant field in a chart, chosen in a direction in which `f` decreases
(`TauCeti.chartConstField`). These local fields are glued by Mathlib's
partition-of-unity theorem for sections with values in fibrewise convex sets,
`exists_contMDiffSection_forall_mem_convex_of_local`. The convex set at a point asks for
`df(X) < 0` if the point is regular, and for equality with the Morse field if the point lies in a
closed neighbourhood of a critical point. These neighbourhoods are chosen pairwise disjoint, which
is possible because a Morse function on a compact manifold has finitely many critical points
(`TauCeti.IsMorse.finite_setOf_mfderiv_eq_zero`).

## Main declarations

* `TauCeti.mfderiv_eq_fderiv_comp_of_eqOn`, `TauCeti.mvfderiv_mpullback_apply`,
  `TauCeti.contMDiffOn_mpullback`: calculus for a function and a vector field read in a chart of
  the maximal atlas.
* `TauCeti.MorseChart.field`: the linear field of a Morse chart, on the manifold, with
  `TauCeti.MorseChart.mvfderiv_field_apply_lt_zero` and `TauCeti.MorseChart.mfderiv_eq_zero_iff`.
* `TauCeti.chartConstField`: a constant field in a chart, with
  `TauCeti.exists_mem_nhds_mvfderiv_chartConstField_lt_zero`.
* `TauCeti.IsMorse.finite_setOf_mfderiv_eq_zero`: finiteness of the critical set.
* `TauCeti.IsMorse.exists_isAdaptedPseudoGradient`: existence of adapted pseudo-gradients.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.2.3 and its proof.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

section ChartCalculus

variable {e : OpenPartialHomeomorph M E} {h : E → ℝ}

/-- If `f = h ∘ e` on the source of a chart `e` of the maximal atlas, with `h` differentiable,
then `df_y = dh_{e y} ∘ de_y`. -/
theorem mfderiv_eq_fderiv_comp_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y =
      (fderiv ℝ h (e y) : E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y) := by
  have hev : f =ᶠ[𝓝 y] h ∘ e := Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hfh
  rw [hev.mfderiv_eq]
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  rw [mfderiv_comp y (hh.mdifferentiableAt) (mdifferentiableAt_of_mem_maximalAtlas he1 hy),
    mfderiv_eq_fderiv]
  rfl

/-- `isInvertible_mfderiv_extend` for a chart of the maximal atlas of a manifold modelled on its
own model space, where the extended chart is the chart itself. -/
private theorem isInvertible_mfderiv_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : M} (hy : y ∈ e.source) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).IsInvertible := by
  have := isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy
  have hext : (e.extend 𝓘(ℝ, E) : M → E) = e := by ext z; simp
  rwa [hext] at this

/-- Where `f = h ∘ e` on the source of a chart `e`, the critical points of `f` in the source are the
preimages of the critical points of `h`. -/
theorem mfderiv_eq_zero_iff_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ fderiv ℝ h (e y) = 0 := by
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy hh]
  have hinv := isInvertible_mfderiv_chart he hy
  constructor
  · intro h0
    ext v
    have hw := DFunLike.congr_fun h0 ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse v)
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse v) = v :=
      hinv.self_apply_inverse v
    exact (congrArg (fderiv ℝ h (e y)) hv).symm.trans hw
  · intro h0
    rw [h0]
    rfl

/-- The pullback `de_y⁻¹ (V (e y))` of a vector field `V` on the model space by a chart `e`. -/
theorem mfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M} (hy : y ∈ e.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = V (e y) := by
  rw [VectorField.mpullback_apply]
  exact (isInvertible_mfderiv_chart he hy).self_apply_inverse _

/-- The derivative of `f` along the pullback of a vector field `V` by a chart `e`, where
`f = h ∘ e` on the source of `e`. -/
theorem mvfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M}
    (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mvfderiv 𝓘(ℝ, E) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) =
      fderiv ℝ h (e y) (V (e y)) := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = _
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy hh]
  exact congrArg (fderiv ℝ h (e y)) (mfderiv_mpullback_apply he V hy)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The pullback of a smooth vector field on the model space by a chart of the maximal atlas is
smooth on the source of the chart. -/
theorem contMDiffOn_mpullback (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {V : (z : E) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContDiffOn ℝ ∞ V e.target) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y⟩ : TangentBundle 𝓘(ℝ, E) M))
      e.source := by
  intro y hy
  have hVy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun z ↦ (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) E)) (e y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.2
      ((hV (e y) (e.map_source hy)).contDiffAt (e.open_target.mem_nhds (e.map_source hy)))
  exact (ContMDiffAt.mpullback_vectorField_preimage hVy (contMDiffAt_of_mem_maximalAtlas he hy)
    (isInvertible_mfderiv_chart he hy) (by simp)).contMDiffWithinAt

end ChartCalculus

section MorseChartField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] {x : M}

/-- The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` has derivative `v ↦ Σᵢ wᵢ uᵢ vᵢ`. -/
theorem hasFDerivAt_diagonalQuadratic {n : ℕ} (c : ℝ) (w u : Fin n → ℝ) :
    HasFDerivAt (fun u : Fin n → ℝ ↦ c + (2 : ℝ)⁻¹ * ∑ i, w i * (u i * u i))
      (∑ i, (w i * u i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u := by
  have hp : ∀ i, HasFDerivAt (fun u : Fin n → ℝ ↦ u i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u :=
    fun i ↦ hasFDerivAt_apply i u
  have hs : HasFDerivAt (fun v : Fin n → ℝ ↦ ∑ i, w i * (v i * v i))
      (∑ i ∈ Finset.univ, w i • (u i • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n ↦ ℝ) i + u i • ContinuousLinearMap.proj i)) u :=
    HasFDerivAt.fun_sum fun i _ ↦ ((hp i).mul (hp i)).const_mul (w i)
  have h := (hs.const_mul (2 : ℝ)⁻¹).const_add c
  convert h using 1
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, add_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The quadratic normal form of a Morse chart, as a function on the model space. -/
noncomputable def quadratic (z : E) : ℝ :=
  f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * (φ.coord z i) ^ 2

/-- The negative gradient `z ↦ L⁻¹ (-(wᵢ (L z)ᵢ)ᵢ)` of the quadratic normal form, read in the
coordinates of the Morse chart. -/
noncomputable def linearField (z : E) : E :=
  φ.coord.symm fun i ↦ -(φ.weight i * φ.coord z i)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- On the source of a Morse chart, `f` is the quadratic normal form read in the chart. -/
theorem eqOn_quadratic : EqOn f (φ.quadratic ∘ φ.toChart) φ.toChart.source := fun y hy ↦ by
  simp only [comp_apply, quadratic]
  exact φ.eq_quadratic y hy

/-- The coordinate change of a Morse chart, as a continuous linear equivalence. -/
noncomputable def coordL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  φ.coord.toContinuousLinearEquiv

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `coordL` is `coord`. -/
@[simp]
theorem coordL_apply (z : E) : φ.coordL z = φ.coord z := by
  simp [coordL]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form. -/
theorem hasFDerivAt_quadratic (z : E) :
    HasFDerivAt φ.quadratic
      ((∑ i, (φ.weight i * φ.coord z i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
          (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))) z := by
  have h := (hasFDerivAt_diagonalQuadratic (f x) φ.weight (φ.coordL z)).comp z
    φ.coordL.hasFDerivAt
  convert h using 1
  · ext v
    simp [quadratic, sq]
  · simp

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form is `v ↦ Σᵢ wᵢ (L z)ᵢ (L v)ᵢ`. -/
theorem fderiv_quadratic_apply (z v : E) :
    fderiv ℝ φ.quadratic z v = ∑ i, φ.weight i * φ.coord z i * φ.coord v i := by
  rw [(φ.hasFDerivAt_quadratic z).fderiv]
  simp

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The quadratic normal form is differentiable. -/
theorem differentiableAt_quadratic (z : E) : DifferentiableAt ℝ φ.quadratic z :=
  (φ.hasFDerivAt_quadratic z).differentiableAt

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The quadratic normal form has a single critical point, the origin. -/
theorem fderiv_quadratic_eq_zero_iff {z : E} : fderiv ℝ φ.quadratic z = 0 ↔ z = 0 := by
  constructor
  · intro h0
    have hz : φ.coord z = 0 := by
      ext i
      have := congrArg (fun T : E →L[ℝ] ℝ ↦ T (φ.coord.symm (Pi.single i (φ.weight i))))
        h0
      simp only [fderiv_quadratic_apply, LinearEquiv.apply_symm_apply,
        zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
      simp only [Pi.single_eq_same] at this
      rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] at this <;> simpa using this
    simpa using congrArg φ.coord.symm hz
  · rintro rfl
    ext v
    simp [fderiv_quadratic_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form along the linear field is `-‖L z‖²`. -/
theorem fderiv_quadratic_linearField (z : E) :
    fderiv ℝ φ.quadratic z (φ.linearField z) = -∑ i, (φ.coord z i) ^ 2 := by
  rw [fderiv_quadratic_apply]
  simp only [linearField, LinearEquiv.apply_symm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] <;> ring

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The linear field of a Morse chart is smooth. -/
theorem contDiff_linearField : ContDiff ℝ ∞ φ.linearField := by
  have h1 : ContDiff ℝ ∞ (fun z : E ↦ fun i ↦ -(φ.weight i * φ.coordL z i)) :=
    contDiff_pi.2 fun i ↦
      (contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp φ.coordL.contDiff)).neg
  have : φ.linearField = φ.coordL.symm ∘ fun z i ↦ -(φ.weight i * φ.coordL z i) := by
    ext z
    simp [linearField, coordL]
  rw [this]
  exact φ.coordL.symm.contDiff.comp h1

/-- The linear field of a Morse chart, as a vector field on the model space. -/
noncomputable def linearVectorField : (z : E) → TangentSpace 𝓘(ℝ, E) z := φ.linearField

/-- The pullback to the manifold of the linear field of a Morse chart. -/
noncomputable def field : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart φ.linearVectorField

/-- The field of a Morse chart is smooth on the source of the chart. -/
theorem contMDiffOn_field :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, φ.field y⟩ : TangentBundle 𝓘(ℝ, E) M)) φ.toChart.source :=
  contMDiffOn_mpullback φ.mem_maximalAtlas φ.contDiff_linearField.contDiffOn

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- In the coordinates of the Morse chart, the field is `z ↦ (-wᵢ zᵢ)ᵢ`. -/
theorem coord_mfderiv_field {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (φ.field y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [field, mfderiv_mpullback_apply φ.mem_maximalAtlas _ hy]
  simp [linearVectorField, linearField]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of `f` along the field of a Morse chart is `-‖L (ψ y)‖²`. -/
theorem mvfderiv_field_apply {y : M} (hy : y ∈ φ.toChart.source) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) = -∑ i, (φ.coord (φ.toChart y) i) ^ 2 := by
  rw [field, mvfderiv_mpullback_apply φ.mem_maximalAtlas φ.eqOn_quadratic _ hy
    (φ.differentiableAt_quadratic _)]
  exact φ.fderiv_quadratic_linearField _

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The centre is the only point of the source sent to `0`. -/
theorem toChart_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) : φ.toChart y = 0 ↔ y = x := by
  refine ⟨fun h ↦ φ.toChart.injOn hy φ.mem_source ?_, fun h ↦ h ▸ φ.apply_self⟩
  rw [h, φ.apply_self]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `f` strictly decreases along the field away from the centre of the chart. -/
theorem mvfderiv_field_apply_lt_zero {y : M} (hy : y ∈ φ.toChart.source) (hyx : y ≠ x) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) < 0 := by
  rw [φ.mvfderiv_field_apply hy, neg_lt_zero]
  have hne : φ.coord (φ.toChart y) ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff, φ.toChart_eq_zero_iff hy]
    exact hyx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
    ⟨i, Finset.mem_univ _, by simpa using (sq_pos_of_ne_zero hi : (0 : ℝ) < _)⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The centre is the only critical point of `f` in the source of a Morse chart. -/
theorem mfderiv_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ y = x := by
  rw [mfderiv_eq_zero_iff_of_eqOn φ.mem_maximalAtlas φ.eqOn_quadratic hy
    (φ.differentiableAt_quadratic _), φ.fderiv_quadratic_eq_zero_iff, φ.toChart_eq_zero_iff hy]

end MorseChart

end MorseChartField

section RegularField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The coordinate expression of `f` in the preferred chart at `p`. -/
theorem eqOn_comp_chartAt_symm (p : M) :
    EqOn f ((f ∘ (chartAt E p).symm) ∘ chartAt E p) (chartAt E p).source := fun y hy ↦ by
  simp [(chartAt E p).left_inv hy]

omit [FiniteDimensional ℝ E] in
/-- The coordinate expression of a smooth function is smooth on the chart target. -/
theorem contDiffOn_comp_chartAt_symm (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) (chartAt E p).target :=
  (hf.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn

/-- The constant vector field with value `v` on the model space. -/
noncomputable def constVectorField (v : E) : (z : E) → TangentSpace 𝓘(ℝ, E) z := fun _ ↦ v

variable (E) in
/-- The constant vector field with value `v` in the preferred chart at `p`, pulled back to the
manifold. -/
noncomputable def chartConstField (p : M) (v : E) : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) (constVectorField v)

omit [FiniteDimensional ℝ E] in
/-- A constant field in a chart is smooth on the source of the chart. -/
theorem contMDiffOn_chartConstField [FiniteDimensional ℝ E] (p : M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, chartConstField E p v y⟩ : TangentBundle 𝓘(ℝ, E) M)) (chartAt E p).source :=
  contMDiffOn_mpullback (IsManifold.chart_mem_maximalAtlas p) contDiffOn_const

omit [FiniteDimensional ℝ E] in
/-- Near a regular point of `f`, some constant field in the preferred chart is a direction of
strict decrease of `f`. -/
theorem exists_mem_nhds_mvfderiv_chartConstField_lt_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {y₀ : M} (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0) :
    ∃ v : E, ∃ U ∈ 𝓝 y₀, U ⊆ (chartAt E y₀).source ∧
      ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (chartConstField E y₀ v y) < 0 := by
  set c := chartAt E y₀
  set h := f ∘ c.symm
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hdiff : ∀ y ∈ c.source, DifferentiableAt ℝ h (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt (by simp)
  have hL : fderiv ℝ h (c y₀) ≠ 0 := fun h0 ↦ hcrit
    ((mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hmem (hdiff y₀ hmem)).2 h0)
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ h (c y₀) w ≠ 0 := by
    by_contra hno
    simp only [ne_eq, not_exists, not_not] at hno
    exact hL (ContinuousLinearMap.ext hno)
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℝ h (c y₀) v < 0 := by
    rcases hw.lt_or_gt with hlt | hgt
    · exact ⟨w, hlt⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  have hcont : ContinuousAt (fun z ↦ fderiv ℝ h z v) (c y₀) :=
    (((contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target
      (by simp)).continuousAt (c.open_target.mem_nhds (c.map_source hmem))).clm_apply
      continuousAt_const
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ h (c y) v < 0 :=
    (hcont.comp (c.continuousAt hmem)).eventually (gt_mem_nhds hv)
  refine ⟨v, {y | y ∈ c.source ∧ fderiv ℝ h (c y) v < 0},
    Filter.inter_mem (c.open_source.mem_nhds hmem) hev, fun y hy ↦ hy.1, fun y hy ↦ ?_⟩
  rw [chartConstField, mvfderiv_mpullback_apply (IsManifold.chart_mem_maximalAtlas y₀)
    (eqOn_comp_chartAt_symm y₀) _ hy.1 (hdiff y hy.1)]
  exact hy.2

end RegularField

section Existence

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The restriction of a Morse chart to an open neighbourhood of its centre. -/
noncomputable def MorseChart.restr {x : M} (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s)
    (hx : x ∈ s) : MorseChart E f x where
  toChart := φ.toChart.restr s
  mem_maximalAtlas := restr_mem_maximalAtlas _ φ.mem_maximalAtlas hs
  mem_source := by rw [φ.toChart.restr_source' s hs]; exact ⟨φ.mem_source, hx⟩
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_one := φ.weight_eq_neg_one_or_eq_one
  ncard_weight_neg := φ.ncard_weight_neg
  eq_quadratic y hy := φ.eq_quadratic y (by rw [φ.toChart.restr_source' s hs] at hy; exact hy.1)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The source of a restricted Morse chart. -/
theorem MorseChart.restr_source {x : M} (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s)
    (hx : x ∈ s) : (φ.restr hs hx).toChart.source = φ.toChart.source ∩ s :=
  φ.toChart.restr_source' s hs

omit [FiniteDimensional ℝ E] in
/-- A point is critical for a smooth `f` exactly when it is critical for the coordinate expression
of `f` in the preferred extended chart at that point. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (x : M) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ↔
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) (extChartAt 𝓘(ℝ, E) x x) = 0 := by
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp
  rw [hext, hext']
  exact mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas x)
    (eqOn_comp_chartAt_symm x) (mem_chart_source E x)
    (((contDiffOn_comp_chartAt_symm hf x).contDiffAt ((chartAt E x).open_target.mem_nhds
      (mem_chart_target E x))).differentiableAt (by simp))

/-- Every critical point of a Morse function has a Morse chart. -/
theorem IsMorse.nonempty_morseChart (hf : IsMorse 𝓘(ℝ, E) f) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : Nonempty (MorseChart E f x) :=
  ((isMorse_iff.1 hf).2 x ((mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm hf.contMDiff x).1
    hx)).nonempty_morseChart (Filter.Eventually.of_forall fun _ ↦ hf.contMDiff.contMDiffAt)

omit [FiniteDimensional ℝ E] in
/-- The regular points of a smooth function form an open set. -/
theorem isOpen_setOf_mfderiv_ne_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    IsOpen {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ ↦ ?_
  set c := chartAt E y₀
  have hcont : ContinuousOn (fderiv ℝ (f ∘ c.symm)) c.target :=
    (contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target (by simp)
  have hdiff : ∀ y ∈ c.source, DifferentiableAt ℝ (f ∘ c.symm) (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt (by simp)
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hiff : ∀ y ∈ c.source, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ fderiv ℝ (f ∘ c.symm) (c y) = 0 :=
    fun y hy ↦ mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hy (hdiff y hy)
  have h0 : fderiv ℝ (f ∘ c.symm) (c y₀) ≠ 0 := fun h ↦ hy₀ ((hiff y₀ hmem).2 h)
  have hca : ContinuousAt (fderiv ℝ (f ∘ c.symm)) (c y₀) :=
    hcont.continuousAt (c.open_target.mem_nhds (c.map_source hmem))
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ (f ∘ c.symm) (c y) ≠ 0 :=
    (hca.comp (c.continuousAt hmem)).eventually_ne h0
  filter_upwards [hev, c.open_source.mem_nhds hmem] with y hy hys
  exact fun h ↦ hy ((hiff y hys).1 h)

/-- **A Morse function on a compact manifold has finitely many critical points.** They form a
closed set, each of them is isolated by its Morse chart, and a closed discrete subset of a compact
space is finite. -/
theorem IsMorse.finite_setOf_mfderiv_eq_zero [CompactSpace M] (hf : IsMorse 𝓘(ℝ, E) f) :
    {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0}.Finite := by
  have hclosed : IsClosed {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0} := by
    have := (isOpen_setOf_mfderiv_ne_zero hf.contMDiff).isClosed_compl
    simpa only [compl_ofPred, ne_eq, not_not] using this
  refine hclosed.isCompact.finite (isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx ↦ ?_)
  obtain ⟨φ⟩ := hf.nonempty_morseChart hx
  refine ⟨φ.toChart.source, φ.toChart.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    exact (φ.mfderiv_eq_zero_iff hy).1 hyc
  · rintro rfl
    exact ⟨φ.mem_source, hx⟩

/-- **Existence of adapted pseudo-gradients** (Audin--Damian, Proposition 2.2.3). Every Morse
function on a compact manifold has a pseudo-gradient field adapted to it. -/
theorem IsMorse.exists_isAdaptedPseudoGradient [CompactSpace M] [T2Space M]
    (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x, IsAdaptedPseudoGradient f X := by
  classical
  set C := {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0} with hCdef
  have hC : C.Finite := hf.finite_setOf_mfderiv_eq_zero
  let φ : ∀ x ∈ C, MorseChart E f x := fun x hx ↦ (hf.nonempty_morseChart hx).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  have hK : ∀ x (hx : x ∈ C), ∃ K, K ∈ 𝓝 x ∧ IsClosed K ∧ K ⊆ (φ x hx).toChart.source ∩ W x :=
    fun x hx ↦ exists_mem_nhds_isClosed_subset
      (Filter.inter_mem ((φ x hx).toChart.open_source.mem_nhds (φ x hx).mem_source)
        ((hW x).2.mem_nhds (hW x).1))
  choose K hKn hKc hKsub using hK
  let K' : M → Set M := fun x ↦ if hx : x ∈ C then K x hx else ∅
  have hK' : ∀ x (hx : x ∈ C), K' x = K x hx := fun x hx ↦ by simp [K', hx]
  let ℓ : (y : M) → (TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) := fun y ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y
  let t : (y : M) → Set (TangentSpace 𝓘(ℝ, E) y) := fun y ↦
    {v | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} ∩
      ⋂ x, ⋂ (hx : x ∈ C), ⋂ (_ : y ∈ K x hx), {(φ x hx).field y}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine Convex.inter ?_ (convex_iInter fun x ↦ convex_iInter fun hx ↦
      convex_iInter fun _ ↦ convex_singleton _)
    by_cases hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0
    · have : {v : TangentSpace 𝓘(ℝ, E) y | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} = univ := by
        ext v
        simp [hy]
      rw [this]
      exact convex_univ
    · have : {v : TangentSpace 𝓘(ℝ, E) y | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} =
          {v | ℓ y v < 0} := by
        ext v
        simp [hy]
      rw [this]
      exact convex_halfSpace_lt (ℓ y).isLinear (0 : ℝ)
  have hloc : ∀ y₀ : M, ∃ U ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧ ∀ y ∈ U, s y ∈ t y := by
    intro y₀
    by_cases h : ∃ x, ∃ hx : x ∈ C, y₀ ∈ K x hx
    · obtain ⟨x, hx, hy₀⟩ := h
      have hUo : IsOpen ((φ x hx).toChart.source ∩ W x) :=
        (φ x hx).toChart.open_source.inter (hW x).2
      refine ⟨_, hUo.mem_nhds (hKsub x hx hy₀), (φ x hx).field,
        (φ x hx).contMDiffOn_field.mono inter_subset_left, fun y hy ↦ ⟨fun hcrit ↦ ?_, ?_⟩⟩
      · have hyx : y ≠ x := by
          rintro rfl
          exact hcrit hx
        exact (φ x hx).mvfderiv_field_apply_lt_zero hy.1 hyx
      · simp only [mem_iInter, mem_singleton_iff]
        intro x' hx' hy'
        have hxx' : x = x' := by
          by_contra hne
          exact Set.disjoint_left.1 (hWdisj hx hx' hne) hy.2 ((hKsub x' hx' hy').2)
        subst hxx'
        rfl
    · simp only [not_exists] at h
      have hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0 := fun h0 ↦
        h y₀ h0 (mem_of_mem_nhds (hKn y₀ h0))
      obtain ⟨v, U, hU, hUc, hUneg⟩ :=
        exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf.contMDiff hcrit
      have hclosed : IsClosed (⋃ x ∈ C, K' x) :=
        hC.isClosed_biUnion fun x hx ↦ by rw [hK' x hx]; exact hKc x hx
      have hy₀K : y₀ ∈ (⋃ x ∈ C, K' x)ᶜ := by
        simp only [mem_compl_iff, mem_iUnion, not_exists]
        intro x hx hmem
        rw [hK' x hx] at hmem
        exact h x hx hmem
      refine ⟨_, Filter.inter_mem (hclosed.isOpen_compl.mem_nhds hy₀K) hU,
        chartConstField E y₀ v,
        (contMDiffOn_chartConstField y₀ v).mono fun y hy ↦ hUc hy.2,
        fun y hy ↦ ⟨fun _ ↦ ?_, ?_⟩⟩
      · exact hUneg y hy.2
      · simp only [mem_iInter, mem_singleton_iff]
        intro x hx hyK
        exfalso
        refine hy.1 (mem_iUnion₂.2 ⟨x, hx, ?_⟩)
        rw [hK' x hx]
        exact hyK
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (TangentSpace 𝓘(ℝ, E)) t ht hloc
  refine ⟨fun y ↦ s y, s.contMDiff, fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · exact (hs y).1 hy
  have hxC : x ∈ C := hx
  refine ⟨(φ x hxC).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hKn x hxC)),
    fun y hy ↦ ?_⟩
  rw [MorseChart.restr_source] at hy
  have hyK : y ∈ K x hxC := interior_subset hy.2
  have hsy : s y = (φ x hxC).field y := by
    have := (hs y).2
    simp only [mem_iInter, mem_singleton_iff] at this
    exact this x hxC hyK
  rw [hsy]
  exact (φ x hxC).coord_mfderiv_field hy.1

end Existence

end TauCeti
