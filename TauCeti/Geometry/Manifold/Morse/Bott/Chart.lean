/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Lemma
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Morse–Bott charts

Near a point `x` of a Morse–Bott critical submanifold of a function `f`, there is a chart of the
maximal atlas, centred at `x`, in which `f` is its critical value plus a diagonal quadratic form
that ignores the directions along the submanifold: after a linear change of coordinates
`L : E ≃ (Fin n → ℝ)`,

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`, with every `wᵢ ∈ {-1, 0, 1}`.

Such a chart is recorded as a `TauCeti.MorseBottChart`. The coordinates of weight `0` are the
coordinates along the critical submanifold and those of weight `±1` its negative and positive
normal coordinates. This extends the Morse charts `TauCeti.MorseChart`, in which every weight is
`±1` (`TauCeti.MorseChart.toMorseBottChart`), to critical points lying on critical submanifolds of
positive dimension.

In a Morse–Bott chart the critical points of `f` are exactly the points whose coordinates of
nonzero weight vanish (`TauCeti.MorseBottChart.mfderiv_eq_zero_iff`): the chart straightens the
critical set into the coordinate plane of the weight-zero coordinates, on which `f` is constant
(`TauCeti.MorseBottChart.apply_eq_of_mfderiv_eq_zero`). Conversely, every point of a
Morse–Bott critical submanifold of a smooth function has a Morse–Bott chart
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.nonempty_morseBottChart`): it is the
normalized Morse–Bott lemma
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_normalized_morseBott_chart`,
read as a single chart of the maximal atlas of `M`, with its normal coordinates rescaled by `√2`.
So every critical point of a Morse–Bott function has one
(`TauCeti.IsMorseBottFamily.nonempty_morseBottChart`).

Morse–Bott charts are the local models in which the negative gradient flow of a Morse–Bott
function is normalized: the linear field `z ↦ (-wᵢ zᵢ)ᵢ` is the negative gradient of the normal
form for the Euclidean metric of the coordinates, and its flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` fixes the
coordinates along the critical submanifold and is linear in the normal ones. The pseudo-gradients
that are linear in such charts are in `TauCeti.Geometry.Manifold.Morse.Bott.PseudoGradient`.

## Main declarations

* `TauCeti.MorseBottChart`: a chart centred at a critical point in which the function is a
  diagonal quadratic form with weights in `{-1, 0, 1}`.
* `TauCeti.MorseChart.toMorseBottChart`: a Morse chart is a Morse–Bott chart.
* `TauCeti.MorseBottChart.restr`, `TauCeti.MorseBottChart.neg`: restriction to an open
  neighbourhood of the centre, and the chart of `-f` with the opposite weights.
* `TauCeti.MorseBottChart.mvfderiv_apply`: the differential of `f` in a Morse–Bott chart.
* `TauCeti.MorseBottChart.mfderiv_eq_zero_iff`: the critical points in a Morse–Bott chart are the
  points whose coordinates of nonzero weight vanish.
* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.nonempty_morseBottChart`: every point
  of a Morse–Bott critical submanifold of a smooth function has a Morse–Bott chart.
* `TauCeti.IsMorseBottFamily.nonempty_morseBottChart`: every critical point of a Morse–Bott
  function has a Morse–Bott chart.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
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

/-- A Morse chart is a Morse–Bott chart, all of whose weights are nonzero. -/
def MorseChart.toMorseBottChart (φ : MorseChart E f x) : MorseBottChart E f x where
  toChart := φ.toChart
  mem_maximalAtlas := φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_zero_or_eq_one i := (φ.weight_eq_neg_one_or_eq_one i).imp_right .inr
  eq_quadratic := φ.eq_quadratic

namespace MorseChart

variable (φ : MorseChart E f x)

@[simp]
theorem toMorseBottChart_toChart : φ.toMorseBottChart.toChart = φ.toChart := by
  rw [toMorseBottChart]

@[simp]
theorem toMorseBottChart_coord : φ.toMorseBottChart.coord = φ.coord := by
  rw [toMorseBottChart]

@[simp]
theorem toMorseBottChart_weight : φ.toMorseBottChart.weight = φ.weight := by
  rw [toMorseBottChart]

end MorseChart

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

@[simp]
theorem neg_toChart : φ.neg.toChart = φ.toChart := by
  rw [neg]

@[simp]
theorem neg_coord : φ.neg.coord = φ.coord := by
  rw [neg]

@[simp]
theorem neg_weight : φ.neg.weight = -φ.weight := by
  rw [neg]

/-- The inverse of the chart of a Morse–Bott chart sends `0` to the centre. -/
theorem toChart_symm_zero : φ.toChart.symm 0 = x := by
  rw [← φ.apply_self, φ.toChart.left_inv φ.mem_source]

/-- A Morse–Bott chart belongs to the `C¹` maximal atlas. -/
theorem mem_maximalAtlas_one : φ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
  IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas

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

/-! ### Existence on Morse–Bott critical submanifolds -/

section Existence

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {i : SmoothEmbedding J 𝓘(ℝ, E) ∞ S M}

/-- Coordinates `(b, y)` on `E' × ℝᵐ` in which `Σⱼ ±yⱼ²` is a diagonal quadratic form with
weights `0` on the base and `±1` on the fibre: a basis of `E'` on the base and `√2 y` on the fibre,
indexed by `Fin N` for any `N = dim E' + m`. -/
private theorem exists_linearEquiv_weight [FiniteDimensional ℝ E'] {m N : ℕ}
    (hN : N = Module.finrank ℝ E' + m) (ind : ℕ) :
    ∃ (T : (E' × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (Fin N → ℝ)) (w : Fin N → ℝ),
      (∀ j, w j = -1 ∨ w j = 0 ∨ w j = 1) ∧ ∀ v, (2 : ℝ)⁻¹ * ∑ j, w j * T v j ^ 2 =
        ∑ k, (if k.val < ind then -1 else 1) * v.2 k ^ 2 := by
  set d := Module.finrank ℝ E'
  let eN : Fin N ≃ Fin d ⊕ Fin m := (finCongr hN).trans finSumFinEquiv.symm
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  let T : (E' × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (Fin N → ℝ) :=
    (((Module.finBasis ℝ E').equivFun.prodCongr ((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).trans
      (LinearEquiv.smulOfNeZero ℝ _ _ hsqrt))).trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin m) ℝ ℝ).symm).trans
      (LinearEquiv.funCongrLeft ℝ ℝ eN)
  have hT (v : E' × EuclideanSpace ℝ (Fin m)) (j : Fin N) :
      T v j = Sum.elim ((Module.finBasis ℝ E').equivFun v.1)
        (fun k ↦ Real.sqrt 2 * v.2 k) (eN j) := by
    rcases hj : eN j with k | k <;>
      simp [T, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, hj]
  let sg : Fin m → ℝ := fun k ↦ if k.val < ind then -1 else 1
  let w : Fin N → ℝ := fun j ↦ Sum.elim (fun _ ↦ 0) sg (eN j)
  have hsum (u : Fin d → ℝ) (v : Fin m → ℝ) :
      ∑ j, w j * Sum.elim u v (eN j) ^ 2 = ∑ k, sg k * v k ^ 2 := by
    rw [eN.sum_comp (fun k ↦ Sum.elim (fun _ ↦ (0 : ℝ)) sg k * Sum.elim u v k ^ 2),
      Fintype.sum_sum_type]
    simp
  refine ⟨T, w, fun j ↦ ?_, fun v ↦ ?_⟩
  · simp only [w, sg]
    rcases eN j with k | k
    · simp
    · simp only [Sum.elim_inr]
      split_ifs <;> simp
  · simp only [hT, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    ring

omit [FiniteDimensional ℝ E] [J.Boundaryless] in
/-- A chart `c` of the maximal atlas, followed by the inverse of a linear isomorphism `L`, a
smooth partial diffeomorphism `ψ`, the translation by `-b` and a linear isomorphism `K` back to
the model, is again a chart of the maximal atlas. -/
private theorem exists_trans_mem_maximalAtlas {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {c : OpenPartialHomeomorph M E}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (L : E₁ ≃L[ℝ] E)
    (ψ : OpenPartialHomeomorph E₁ E₂) (hψ : ContDiffOn ℝ ∞ ψ ψ.source)
    (hψinv : ContDiffOn ℝ ∞ ψ.symm ψ.target) (K : E₂ ≃L[ℝ] E) (b : E₂) :
    ∃ Φ : OpenPartialHomeomorph E E, (∀ w, Φ w = K (ψ (L.symm w) - b)) ∧
      Φ.source = L.symm ⁻¹' ψ.source ∧ c.trans Φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
  let Φ : OpenPartialHomeomorph E E :=
    (L.symm.toHomeomorph.toOpenPartialHomeomorph.trans ψ).trans
      ((Homeomorph.subRight b).trans K.toHomeomorph).toOpenPartialHomeomorph
  have hΦsrc : Φ.source = L.symm ⁻¹' ψ.source := by simp [Φ]
  have hΦtgt : Φ.target = (fun w ↦ K.symm w + b) ⁻¹' ψ.target := by
    ext w
    simp [Φ]
  refine ⟨Φ, fun _ ↦ rfl, hΦsrc, trans_mem_maximalAtlas_of_contDiffAt hc (fun z hz ↦ ?_)
    (fun z hz ↦ ?_)⟩
  · rw [hΦsrc] at hz
    have hψz : ContDiffAt ℝ ∞ ψ (L.symm z) := (hψ _ hz).contDiffAt (ψ.open_source.mem_nhds hz)
    exact K.contDiff.contDiffAt.comp z ((hψz.comp z L.symm.contDiff.contDiffAt).sub
      contDiffAt_const)
  · rw [hΦtgt] at hz
    have hψz : ContDiffAt ℝ ∞ ψ.symm (K.symm z + b) :=
      (hψinv _ hz).contDiffAt (ψ.open_target.mem_nhds hz)
    exact L.contDiff.contDiffAt.comp z
      (hψz.comp z (K.symm.contDiff.contDiffAt.add contDiffAt_const))

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-- **The Morse–Bott lemma as a chart of the maximal atlas.** Every point `i s` of a Morse–Bott
critical submanifold of a function `f`, smooth near `i s`, has a Morse–Bott chart: a chart of the
maximal atlas of `M`, centred at `i s`, in which `f y = f (i s) + (1/2) Σⱼ wⱼ (L (ψ y))ⱼ²` with
weights `wⱼ ∈ {-1, 0, 1}`.

The chart is the normalized Morse–Bott lemma
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_normalized_morseBott_chart`,
in which `f` reads `f (i s) + Σⱼ ±yⱼ²` in slice coordinates `(b, y)`, translated to centre `i s`
and with the normal coordinates `y` rescaled by `√2`. -/
theorem nonempty_morseBottChart (hi : i.IsNondegenerateCriticalSubmanifold f) (s : S)
    (hf : ∀ᶠ y in 𝓝 (i s), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y) :
    Nonempty (MorseBottChart E f (i s)) := by
  -- Slice charts of `i` at `s`, with complement `F`.
  let F := i.isImmersion.complement
  have h : Manifold.IsImmersionAtOfComplement F J 𝓘(ℝ, E) ∞ i s :=
    i.isImmersion.isImmersionOfComplement_complement s
  set φ := h.domChart.extend J with hφ
  set c := h.codChart with hc
  set L := h.equiv with hL
  set a := φ s with ha
  obtain ⟨ψ, U, V, -, -, haU, h0V, hsource, -, hUVξ, hsec, -, hψ0, -, hψ, hψinv, hψg⟩ :=
    hi.exists_normalized_morseBott_chart h (k := ⊤) (by simp) (by simp)
      (hf.mono fun y hy ↦ hy.of_le (by simp))
  have : FiniteDimensional ℝ (E' × F) := L.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_surjective (LinearMap.fst ℝ E' F) LinearMap.fst_surjective
  have : FiniteDimensional ℝ F :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' F) LinearMap.snd_surjective
  -- The extended chart of the model `𝓘(ℝ, E)` is the chart itself.
  have hξs : ∀ w, (c.extend 𝓘(ℝ, E)).symm w = c.symm w := fun w ↦ by simp
  have hξt : (c.extend 𝓘(ℝ, E)).target = c.target := by simp
  -- The centre `i s` has slice coordinates `(a, 0)`.
  have hsa : c.symm (L (a, 0)) = i s := by
    rw [← hξs, hsec a haU, ha, hφ, (h.domChart.extend J).left_inv
      (by simpa using h.mem_domChart_source)]
  have hUVc : U ×ˢ V ⊆ L ⁻¹' c.target := hξt ▸ hUVξ
  have hca : c (i s) = L (a, 0) := by
    rw [← hsa, c.right_inv (hUVc (mk_mem_prod haU h0V))]
  -- The final linear coordinates `T`, with their weights `w`.
  have hN : Module.finrank ℝ E = Module.finrank ℝ E' + Module.finrank ℝ F := by
    rw [← L.toLinearEquiv.finrank_eq, Module.finrank_prod]
  obtain ⟨T, w, hw, hTw⟩ := exists_linearEquiv_weight hN (manifoldMorseIndex 𝓘(ℝ, E) f (i s))
  -- The chart: slice coordinates, then `ψ`, then the translation of `(a, 0)` to `0` and the
  -- coordinates `T`, read back in `E` through a basis of `E`.
  let B := (Module.finBasis ℝ E).equivFun
  let K : (E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) ≃L[ℝ] E :=
    (T.trans B.symm).toContinuousLinearEquiv
  have hBK (v : E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) : B (K v) = T v := by simp [K]
  obtain ⟨Φ, hΦ, hΦsrc, hΦmem⟩ := exists_trans_mem_maximalAtlas h.codChart_mem_maximalAtlas L ψ hψ
    hψinv K ((a, 0) : E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))
  refine ⟨⟨c.trans Φ, hΦmem, ?_, ?_, B, w, hw, fun y hy ↦ ?_⟩⟩
  · -- The chart is defined at `i s`.
    refine ⟨h.mem_codChart_source, ?_⟩
    rw [mem_preimage, hΦsrc, mem_preimage, OpenPartialHomeomorph.symm_symm, hca,
      L.symm_apply_apply, hsource]
    exact mk_mem_prod haU h0V
  · -- It sends `i s` to `0`.
    rw [OpenPartialHomeomorph.coe_trans, comp_apply, hca, hΦ, L.symm_apply_apply, hψ0, sub_self,
      map_zero]
  · -- The normal form.
    rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage, hΦsrc,
      mem_preimage] at hy
    have hfy := hψg _ hy.2
    rw [comp_apply, comp_apply, ← hL, ← hc, hξs, L.apply_symm_apply, c.left_inv hy.1] at hfy
    rw [hfy, OpenPartialHomeomorph.coe_trans, comp_apply, hΦ, hBK, hTw, Prod.snd_sub,
      sub_zero]

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end Existence

section Family

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, (J a).Boundaryless] {S : ι → Type*} [∀ a, TopologicalSpace (S a)]
  [∀ a, ChartedSpace (H' a) (S a)] {i : ∀ a, SmoothEmbedding (J a) 𝓘(ℝ, E) ∞ (S a) M}

/-- **Every critical point of a Morse–Bott function has a Morse–Bott chart.** -/
theorem IsMorseBottFamily.nonempty_morseBottChart (h : IsMorseBottFamily i f)
    (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) : Nonempty (MorseBottChart E f x) := by
  obtain ⟨a, s, rfl⟩ := mem_iUnion.1 (h.criticalPoints_subset_iUnion_range hx)
  exact (h.isNondegenerateCriticalSubmanifold a).nonempty_morseBottChart s
    (.of_forall fun _ ↦ h.contMDiff.contMDiffAt)

end Family

end TauCeti
