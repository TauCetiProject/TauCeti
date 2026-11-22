/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic

/-!
# Morse–Bott charts

Near a point `x` of a Morse–Bott critical submanifold of a function `f`, there is a chart of the
maximal atlas, centred at `x`, in which `f` is its critical value plus a diagonal quadratic form
that ignores the directions along the submanifold: after a linear change of coordinates
`L : E ≃ (Fin n → ℝ)`,

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`, with every `wᵢ ∈ {-1, 0, 1}`.

Such a chart is recorded as a `TauCeti.MorseBottChart`. The coordinates of weight `0` are the
coordinates along the critical submanifold and those of weight `±1` its negative and positive
normal coordinates. The Morse charts `TauCeti.MorseChart`, in which every weight is `±1`, extend
this structure, so the chart calculus of this file applies to them as well.

In a Morse–Bott chart the critical points of `f` are exactly the points whose coordinates of
nonzero weight vanish (`TauCeti.MorseBottChart.mfderiv_eq_zero_iff`): the chart straightens the
critical set into the coordinate plane of the weight-zero coordinates, on which `f` is constant
(`TauCeti.MorseBottChart.apply_eq_of_mfderiv_eq_zero`). The existence of Morse–Bott charts at the
points of a Morse–Bott critical submanifold is in
`TauCeti.Geometry.Manifold.Morse.Bott.Chart.Existence`.

Morse–Bott charts are the local models in which the negative gradient flow of a Morse–Bott
function is normalized: the linear field `z ↦ (-wᵢ zᵢ)ᵢ` is the negative gradient of the normal
form for the Euclidean metric of the coordinates, and its flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` fixes the
coordinates along the critical submanifold and is linear in the normal ones. The pseudo-gradients
that are linear in such charts are in `TauCeti.Geometry.Manifold.Morse.Bott.PseudoGradient`.

## Main declarations

* `TauCeti.MorseBottChart`: a chart centred at a critical point in which the function is a
  diagonal quadratic form with weights in `{-1, 0, 1}`.
* `TauCeti.MorseBottChart.restr`, `TauCeti.MorseBottChart.neg`: restriction to an open
  neighbourhood of the centre, and the chart of `-f` with the opposite weights.
* `TauCeti.MorseBottChart.quadratic`: the quadratic normal form, with
  `TauCeti.MorseBottChart.eqOn_quadratic` and `TauCeti.MorseBottChart.contDiff_quadratic`.
* `TauCeti.MorseBottChart.contMDiffOn` and `TauCeti.MorseBottChart.contMDiffAt`: a function is
  smooth on the source of a Morse–Bott chart.
* `TauCeti.MorseBottChart.mvfderiv_apply`: the differential of `f` in a Morse–Bott chart.
* `TauCeti.MorseBottChart.mfderiv_eq_zero_iff`: the critical points in a Morse–Bott chart are the
  points whose coordinates of nonzero weight vanish.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and their gradient flows).
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

variable (E) in
/-- A **Morse–Bott chart** for `f` at `x`: a chart of the maximal atlas, centred at `x`, together
with a linear change of coordinates `L : E ≃ (Fin n → ℝ)` and weights `wᵢ ∈ {-1, 0, 1}`, such that
on the source of the chart `f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`. The coordinates of weight `0`
run along the critical set and those of weight `±1` across it. -/
structure MorseBottChart (f : M → ℝ) (x : M) where
  /-- The chart. -/
  toChart : OpenPartialHomeomorph M E
  mem_maximalAtlas : toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  mem_source : x ∈ toChart.source
  apply_self : toChart x = 0
  /-- The linear change of coordinates that diagonalizes the normal form. -/
  coord : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)
  /-- The diagonal weights of the normal form: `0` along the critical set, `±1` across it. -/
  weight : Fin (Module.finrank ℝ E) → ℝ
  weight_eq_neg_one_or_eq_zero_or_eq_one : ∀ i, weight i = -1 ∨ weight i = 0 ∨ weight i = 1
  eq_quadratic : ∀ y ∈ toChart.source,
    f y = f x + (2 : ℝ)⁻¹ * ∑ i, weight i * (coord (toChart y) i) ^ 2

attribute [simp] MorseBottChart.mem_source MorseBottChart.apply_self

namespace MorseBottChart

/-- The restriction of a Morse–Bott chart to an open neighbourhood `s` of its centre: the chart is
restricted to `s`, and the coordinates and weights are unchanged. -/
noncomputable def restr (φ : MorseBottChart E f x) {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    MorseBottChart E f x where
  toChart := φ.toChart.restr s
  mem_maximalAtlas := restr_mem_maximalAtlas _ φ.mem_maximalAtlas hs
  mem_source := by rw [φ.toChart.restr_source' s hs]; exact ⟨φ.mem_source, hx⟩
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_zero_or_eq_one := φ.weight_eq_neg_one_or_eq_zero_or_eq_one
  eq_quadratic y hy := φ.eq_quadratic y (by rw [φ.toChart.restr_source' s hs] at hy; exact hy.1)

variable (φ : MorseBottChart E f x)

section Restr

variable {s : Set M} (hs : IsOpen s) (hx : x ∈ s)

/-- The chart of a restricted Morse–Bott chart is the restricted chart. -/
@[simp]
theorem restr_toChart : (φ.restr hs hx).toChart = φ.toChart.restr s := by
  rw [restr]

/-- Restricting a Morse–Bott chart does not change its coordinates. -/
@[simp]
theorem restr_coord : (φ.restr hs hx).coord = φ.coord := by
  rw [restr]

/-- Restricting a Morse–Bott chart does not change its weights. -/
@[simp]
theorem restr_weight : (φ.restr hs hx).weight = φ.weight := by
  rw [restr]

/-- The source of a restricted Morse–Bott chart is the intersection of the source with `s`. -/
theorem restr_source : (φ.restr hs hx).toChart.source = φ.toChart.source ∩ s := by
  rw [restr_toChart, φ.toChart.restr_source' s hs]

end Restr

/-- A Morse–Bott chart for `f` is a Morse–Bott chart for `-f`, with the opposite weights. -/
def neg : MorseBottChart E (-f) x where
  toChart := φ.toChart
  mem_maximalAtlas := φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := -φ.weight
  weight_eq_neg_one_or_eq_zero_or_eq_one i := by
    rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one i with h | h | h <;> simp [h]
  eq_quadratic y hy := by
    simp only [Pi.neg_apply, φ.eq_quadratic y hy, neg_mul, Finset.sum_neg_distrib, mul_neg,
      neg_add_rev]
    ring

/-- The negated Morse–Bott chart has the same chart. -/
@[simp]
theorem neg_toChart : φ.neg.toChart = φ.toChart := by
  rw [neg]

/-- The negated Morse–Bott chart has the same coordinates. -/
@[simp]
theorem neg_coord : φ.neg.coord = φ.coord := by
  rw [neg]

/-- The negated Morse–Bott chart has the opposite weights. -/
@[simp]
theorem neg_weight : φ.neg.weight = -φ.weight := by
  rw [neg]

/-- The inverse of the chart of a Morse–Bott chart sends `0` to the centre. -/
@[simp]
theorem toChart_symm_zero : φ.toChart.symm 0 = x := by
  rw [← φ.apply_self, φ.toChart.left_inv φ.mem_source]

/-- A Morse–Bott chart belongs to the `C¹` maximal atlas. -/
theorem mem_maximalAtlas_one : φ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
  IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas

/-- A point of the chart is the point with its own coordinates. -/
theorem toChart_symm_coord_symm_coord {y : M} (hy : y ∈ φ.toChart.source) :
    φ.toChart.symm (φ.coord.symm (φ.coord (φ.toChart y))) = y := by
  rw [LinearEquiv.symm_apply_apply, φ.toChart.left_inv hy]

/-- The centre is the only point of the source sent to `0`. -/
theorem toChart_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) : φ.toChart y = 0 ↔ y = x := by
  refine ⟨fun h ↦ φ.toChart.injOn hy φ.mem_source ?_, fun h ↦ h ▸ φ.apply_self⟩
  rw [h, φ.apply_self]

/-- The centre is the point with coordinates `0`. -/
theorem toChart_symm_coord_symm_zero : φ.toChart.symm (φ.coord.symm 0) = x := by
  rw [map_zero, φ.toChart_symm_zero]

/-- The chart of a Morse–Bott chart is differentiable on its source. -/
theorem mdifferentiableAt_toChart {y : M} (hy : y ∈ φ.toChart.source) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y :=
  mdifferentiableAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one hy

include φ in
/-- A space with a Morse–Bott chart is finite-dimensional. -/
theorem finiteDimensional : FiniteDimensional ℝ E :=
  Module.Finite.equiv φ.coord.symm

/-- A weight of a Morse–Bott chart is nonzero exactly when its square is `1`. -/
theorem weight_ne_zero_iff (i : Fin (Module.finrank ℝ E)) :
    φ.weight i ≠ 0 ↔ φ.weight i ^ 2 = 1 := by
  rcases φ.weight_eq_neg_one_or_eq_zero_or_eq_one i with h | h | h <;> simp [h]

/-- The coordinate change of a Morse–Bott chart, as a continuous linear equivalence. -/
noncomputable def coordL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  have := φ.finiteDimensional
  φ.coord.toContinuousLinearEquiv

/-- `coordL` is `coord`. -/
@[simp]
theorem coordL_apply (z : E) : φ.coordL z = φ.coord z := by
  simp [coordL]

/-- The inverse of `coordL` is the inverse of `coord`. -/
@[simp]
theorem coordL_symm_apply (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.coordL.symm z = φ.coord.symm z := by
  simp [coordL]

/-- Coordinates of small sup norm are coordinates of points of the chart. -/
theorem exists_pos_forall_norm_lt_mem_target :
    ∃ r > 0, ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target := by
  have := φ.finiteDimensional
  have h0 : (0 : Fin (Module.finrank ℝ E) → ℝ) ∈ φ.coordL.symm ⁻¹' φ.toChart.target := by
    rw [mem_preimage, map_zero, ← φ.apply_self]
    exact φ.toChart.map_source φ.mem_source
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (φ.toChart.open_target.preimage φ.coordL.symm.continuous) 0 h0
  exact ⟨r, hr, fun z hz ↦ by simpa using hball (mem_ball_zero_iff.2 hz)⟩

/-- The coordinate change of a Morse–Bott chart is continuous. -/
theorem continuous_coord : Continuous φ.coord := by
  have := φ.finiteDimensional
  exact φ.coordL.continuous.congr φ.coordL_apply

open Filter in
/-- The point with coordinates `w` tends to the centre as `w` tends to `0`. -/
theorem tendsto_toChart_symm_coord_symm_nhds_zero :
    Tendsto (fun w ↦ φ.toChart.symm (φ.coord.symm w)) (𝓝 0) (𝓝 x) := by
  have := φ.finiteDimensional
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have h := (φ.toChart.continuousAt_symm (hrT 0 (by simpa using hr))).comp
    (φ.coordL.symm.continuous.continuousAt.congr (.of_forall φ.coordL_symm_apply))
  rwa [ContinuousAt, comp_apply, φ.toChart_symm_coord_symm_zero] at h

/-- The quadratic normal form of a Morse–Bott chart, as a function on the model space. -/
noncomputable def quadratic (z : E) : ℝ :=
  f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * (φ.coord z i) ^ 2

/-- The value of the quadratic normal form of a Morse–Bott chart. -/
theorem quadratic_apply (z : E) :
    φ.quadratic z = f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * (φ.coord z i) ^ 2 :=
  (rfl)

/-- On the source of a Morse–Bott chart, `f` is the quadratic normal form read in the chart. -/
theorem eqOn_quadratic : EqOn f (φ.quadratic ∘ φ.toChart) φ.toChart.source := fun y hy ↦ by
  simp only [comp_apply, quadratic_apply]
  exact φ.eq_quadratic y hy

/-- The quadratic normal form is smooth. -/
theorem contDiff_quadratic : ContDiff ℝ ∞ φ.quadratic := by
  have hi (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ fun z ↦ φ.coordL z i :=
    contDiff_pi.1 φ.coordL.contDiff i
  simp only [coordL_apply] at hi
  exact contDiff_const.add (contDiff_const.mul (ContDiff.sum fun i _ ↦
    contDiff_const.mul ((hi i).pow 2)))

/-- A function is smooth on the source of a Morse–Bott chart: there, it is a quadratic polynomial
in the coordinates of a chart of the maximal atlas. -/
theorem contMDiffOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f φ.toChart.source :=
  (φ.contDiff_quadratic.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas φ.mem_maximalAtlas)).congr φ.eqOn_quadratic

/-- A function is smooth at every point of the source of a Morse–Bott chart, in particular at its
centre. -/
theorem contMDiffAt {y : M} (hy : y ∈ φ.toChart.source) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y :=
  φ.contMDiffOn.contMDiffAt (φ.toChart.open_source.mem_nhds hy)

/-- The derivative of the quadratic normal form. -/
theorem hasFDerivAt_quadratic (z : E) :
    HasFDerivAt φ.quadratic
      ((∑ i, (φ.weight i * φ.coord z i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
          (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))) z := by
  have h := ((hasFDerivAt_diagonalQuadratic φ.weight (φ.coordL z)).const_add (f x)).comp z
    φ.coordL.hasFDerivAt
  convert h using 1
  · ext v
    simp [quadratic_apply, diagonalQuadratic_apply, Finset.mul_sum, div_eq_inv_mul]
  · simp

/-- The quadratic normal form is differentiable. -/
theorem differentiableAt_quadratic (z : E) : DifferentiableAt ℝ φ.quadratic z := by
  have := φ.finiteDimensional
  exact (φ.hasFDerivAt_quadratic z).differentiableAt

/-- The derivative of the quadratic normal form is `v ↦ Σᵢ wᵢ (L z)ᵢ (L v)ᵢ`. -/
theorem fderiv_quadratic_apply (z v : E) :
    fderiv ℝ φ.quadratic z v = ∑ i, φ.weight i * φ.coord z i * φ.coord v i := by
  rw [(φ.hasFDerivAt_quadratic z).fderiv]
  simp

/-- The critical points of the quadratic normal form are the points whose coordinates of nonzero
weight vanish. -/
theorem fderiv_quadratic_eq_zero_iff {z : E} :
    fderiv ℝ φ.quadratic z = 0 ↔ ∀ i, φ.weight i ≠ 0 → φ.coord z i = 0 := by
  constructor
  · intro h0 i hi
    have := congrArg (fun T : E →L[ℝ] ℝ ↦ T (φ.coord.symm (Pi.single i (φ.weight i)))) h0
    simp only [fderiv_quadratic_apply, LinearEquiv.apply_symm_apply,
      zero_apply] at this
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
    simp only [Pi.single_eq_same] at this
    have h2 := (φ.weight_ne_zero_iff i).1 hi
    calc φ.coord z i = φ.weight i ^ 2 * φ.coord z i := by rw [h2, one_mul]
      _ = 0 := by rw [← this]; ring
  · intro h
    ext v
    simp only [fderiv_quadratic_apply, zero_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    by_cases hi : φ.weight i = 0
    · simp [hi]
    · simp [h i hi]

/-- **The differential of `f` in a Morse–Bott chart** is `v ↦ Σᵢ wᵢ (L (ψ y))ᵢ (L (dψ v))ᵢ`. -/
theorem mvfderiv_apply {y : M} (hy : y ∈ φ.toChart.source) (v : TangentSpace 𝓘(ℝ, E) y) :
    mvfderiv 𝓘(ℝ, E) f y v = ∑ i, φ.weight i * φ.coord (φ.toChart y) i *
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v) i := by
  -- `mvfderiv` composes `mfderiv` with `NormedSpace.fromTangentSpace`, which is the identity
  -- on the underlying type `ℝ` of `TangentSpace 𝓘(ℝ) (f y)` and has no Mathlib `simp` lemma.
  rw [mvfderiv, ContinuousLinearMap.comp_apply,
    mfderiv_eq_fderiv_comp_of_eqOn φ.mem_maximalAtlas_one φ.eqOn_quadratic hy]
  exact φ.fderiv_quadratic_apply _ _

/-- **The critical points in a Morse–Bott chart** are the points of its source whose coordinates
of nonzero weight vanish: the chart straightens the critical set into the coordinate plane of the
weight-zero coordinates. -/
theorem mfderiv_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ ∀ i, φ.weight i ≠ 0 → φ.coord (φ.toChart y) i = 0 := by
  rw [mfderiv_eq_zero_iff_of_eqOn φ.mem_maximalAtlas_one φ.eqOn_quadratic hy,
    φ.fderiv_quadratic_eq_zero_iff]

include φ in
/-- The centre of a Morse–Bott chart is a critical point. -/
theorem mfderiv_self : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 :=
  (φ.mfderiv_eq_zero_iff φ.mem_source).2 fun i _ ↦ by simp

/-- `f` takes the critical value `f x` at every critical point in the source of a Morse–Bott
chart. -/
theorem apply_eq_of_mfderiv_eq_zero {y : M} (hy : y ∈ φ.toChart.source)
    (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0) : f y = f x := by
  rw [φ.eq_quadratic y hy, add_eq_left]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
  by_cases hi : φ.weight i = 0
  · simp [hi]
  · simp [(φ.mfderiv_eq_zero_iff hy).1 hcrit i hi]

end MorseBottChart

end TauCeti
