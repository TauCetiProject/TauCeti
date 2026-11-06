/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Scalar coordinates of a finite-dimensional weak-derivative graph

The native weak-derivative graph over the identity of `Lp F` is continuously linearly equivalent
to a finite tuple of scalar `W1p` spaces, for any finite basis of a finite-dimensional real normed
space `F`. The value and derivative of the inverse are reconstructed in that basis. This permits
scalar Sobolev estimates to be applied to vector-valued fields without a new Sobolev carrier.

## Main declarations

* `coordinatesL`: the native scalar projections, bundled into one continuous linear map.
* `coordinatesEquiv`: their continuous linear equivalence with scalar `W1p` tuples.
* `ofCoordinates`: explicit reconstruction of the vector field and its weak derivative.
* `prev_coordinatesEquiv_symm_ae`, `weakFDeriv_coordinatesEquiv_symm_ae`: reconstruction
  formulas for values and derivatives in every direction on one almost-everywhere set.
* `coordinateValue_change_basis`, `coordinateDerivative_change_basis`: basis independence
  of the reconstructed fields.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar coordinate map on an existing vector-valued weak-derivative graph. -/
def coordinatesL (b : Module.Basis ι ℝ F) :
    WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) →L[ℝ]
      (ι → W1p μ Ω p) :=
  ContinuousLinearMap.pi fun i ↦
    toW1pL (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
      (b.coord i).toContinuousLinearMap

omit [Fintype ι] in
/-- A coordinate value is the corresponding scalar projection of the original field. -/
@[simp]
theorem value_coordinatesL (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    W1p.value (coordinatesL b u i) =
      (b.coord i).toContinuousLinearMap.compLpL p (μ.restrict Ω)
        (prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u) := by
  simp [coordinatesL]

omit [Fintype ι] in
/-- The coordinate tuple has the expected scalar values almost everywhere. -/
theorem coordinatesL_value_ae (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    W1p.value (coordinatesL b u i) =ᵐ[μ.restrict Ω]
      fun x ↦ b.coord i (prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u x) := by
  rw [value_coordinatesL]
  exact (b.coord i).toContinuousLinearMap.coeFn_compLpL _

omit [Fintype ι] in
/-- The coordinate weak gradients encode every direction of the original weak derivative. -/
theorem coordinatesL_gradient_ae (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    ∀ᵐ x ∂μ.restrict Ω, ∀ v, ⟪W1p.gradient (coordinatesL b u i) x, v⟫_ℝ =
      b.coord i (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u x v) :=
  inner_gradient_toW1pL_ae _ (b.coord i).toContinuousLinearMap u

/-- Reconstruct the value field from scalar Sobolev functions in a finite basis. -/
def coordinateValue (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) : Lp F p (μ.restrict Ω) :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (μ.restrict Ω)
    (W1p.value (u i))

/-- Reconstruct the derivative from the scalar weak gradients. -/
def coordinateDerivative (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    Lp (E →L[ℝ] F) p (μ.restrict Ω) :=
  ∑ i, (((ContinuousLinearMap.compL ℝ E ℝ F
    (ContinuousLinearMap.toSpanSingleton ℝ (b i))).comp (innerSL ℝ)).compLpL p
      (μ.restrict Ω)) (W1p.gradient (u i))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The reconstructed value is the pointwise basis expansion almost everywhere. -/
theorem coordinateValue_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    coordinateValue b u =ᵐ[μ.restrict Ω] fun x ↦ ∑ i, W1p.value (u i) x • b i := by
  classical
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (μ.restrict Ω)
      (W1p.value (u i))), ae_all_iff.mpr (fun i ↦
        (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL (W1p.value (u i)))]
    with x hs hc
  simp only [coordinateValue, hs, hc, ContinuousLinearMap.toSpanSingleton_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The reconstructed derivative sends a direction to the basis expansion of the scalar
weak gradients paired with that direction. -/
theorem coordinateDerivative_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    ∀ᵐ x ∂μ.restrict Ω, ∀ v,
      coordinateDerivative b u x v = ∑ i, ⟪W1p.gradient (u i) x, v⟫_ℝ • b i := by
  classical
  let A (i : ι) : E →L[ℝ] E →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ E ℝ F (ContinuousLinearMap.toSpanSingleton ℝ (b i))).comp
      (innerSL ℝ)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ (A i).compLpL p (μ.restrict Ω) (W1p.gradient (u i))),
    ae_all_iff.mpr (fun i ↦ (A i).coeFn_compLpL (W1p.gradient (u i)))] with x hs hc
  intro v
  simp only [coordinateDerivative, hs, hc, A, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, sum_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]

/-- The reconstructed fields satisfy the native weak Fréchet derivative relation. -/
theorem hasWeakFDerivOn_coordinateValue (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    HasWeakFDerivOn μ Ω (coordinateValue b u) (coordinateDerivative b u) := by
  classical
  have hs := HasWeakFDerivOn.sum Finset.univ (fun i _ ↦
    (W1p.hasWeakFDerivOn (u i)).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)))
  apply (hs.congr_ae (coordinateValue_ae b u).symm).congr_ae_deriv
  filter_upwards [coordinateDerivative_ae b u] with x hx
  ext v
  simpa only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply] using (hx v).symm

/-- Reconstruct a native vector-valued weak-derivative graph from scalar Sobolev coordinates. -/
def ofCoordinates (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) :=
  mk _ (coordinateValue b u) (coordinateDerivative b u) (hasWeakFDerivOn_coordinateValue b u)

/-- Reconstruction preserves the prescribed value field. -/
@[simp]
theorem prev_ofCoordinates (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) (ofCoordinates b u) =
      coordinateValue b u := by
  rw [ofCoordinates]
  exact prev_mk _ _ _ _

/-- Reconstruction preserves the prescribed derivative field. -/
@[simp]
theorem weakFDeriv_ofCoordinates (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) (ofCoordinates b u) =
      coordinateDerivative b u := by
  rw [ofCoordinates]
  exact weakFDeriv_mk _ _ _ _

omit [Fintype ι] in
/-- Scalar coordinate functions recover the original graph element. -/
theorem coordinatesL_injective [Finite ι] (b : Module.Basis ι ℝ F) :
    Function.Injective (coordinatesL (μ := μ) (Ω := Ω) (p := p) b) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro u v huv
  apply WeakDerivStep.ext
  rw [eq_sum_basis_compLpL b (prev _ u), eq_sum_basis_compLpL b (prev _ v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← value_coordinatesL b u i, ← value_coordinatesL b v i, huv]

/-- Taking coordinates of the reconstructed graph returns the original scalar Sobolev tuple. -/
@[simp]
theorem coordinatesL_ofCoordinates (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    coordinatesL b (ofCoordinates b u) = u := by
  classical
  funext i
  apply W1p.ext_value
  rw [value_coordinatesL, prev_ofCoordinates]
  apply Lp.ext
  filter_upwards [(b.coord i).toContinuousLinearMap.coeFn_compLpL (coordinateValue b u),
    coordinateValue_ae b u] with x hc hv
  rw [hc, hv]
  simp [Module.Basis.coord_apply, map_sum, Finsupp.single_apply]

/-- Reconstructing the coordinates of a graph returns that graph, including its weak derivative. -/
@[simp]
theorem ofCoordinates_coordinatesL (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) :
    ofCoordinates b (coordinatesL b u) = u :=
  (coordinatesL_injective b) (coordinatesL_ofCoordinates b (coordinatesL b u))

omit [Fintype ι] in
/-- Every scalar Sobolev tuple is the coordinate tuple of a vector-valued graph. -/
theorem coordinatesL_surjective [Finite ι] (b : Module.Basis ι ℝ F) :
    Function.Surjective (coordinatesL (μ := μ) (Ω := Ω) (p := p) b) :=
  by
    let : Fintype ι := Fintype.ofFinite ι
    exact fun u ↦ ⟨ofCoordinates b u, coordinatesL_ofCoordinates b u⟩

/-- A finite basis identifies the native vector-valued first-order weak-derivative graph with
a finite tuple of scalar Sobolev spaces by a continuous linear equivalence. -/
def coordinatesEquiv (b : Module.Basis ι ℝ F) :
    WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) ≃L[ℝ]
      (ι → W1p μ Ω p) :=
  ContinuousLinearEquiv.ofBijective (coordinatesL b)
    (LinearMap.ker_eq_bot.2 (coordinatesL_injective b))
    (LinearMap.range_eq_top.2 (coordinatesL_surjective b))

/-- The coordinate equivalence applies the native scalar projections. -/
@[simp]
theorem coordinatesEquiv_apply (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) :
    coordinatesEquiv b u = coordinatesL b u :=
  (rfl)

/-- The inverse of the coordinate equivalence reconstructs the value and its weak derivative. -/
@[simp]
theorem coordinatesEquiv_symm_apply (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    (coordinatesEquiv b).symm u = ofCoordinates b u := by
  apply (coordinatesEquiv b).injective
  simp

/-- The inverse coordinate equivalence has the expected almost-everywhere value formula. -/
theorem prev_coordinatesEquiv_symm_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) ((coordinatesEquiv b).symm u)
      =ᵐ[μ.restrict Ω] fun x ↦ ∑ i, W1p.value (u i) x • b i := by
  rw [coordinatesEquiv_symm_apply, prev_ofCoordinates]
  exact coordinateValue_ae b u

/-- The inverse coordinate equivalence reconstructs the derivative in every direction on a
single almost-everywhere set. -/
theorem weakFDeriv_coordinatesEquiv_symm_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    ∀ᵐ x ∂μ.restrict Ω, ∀ v,
      weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
        ((coordinatesEquiv b).symm u) x v = ∑ i, ⟪W1p.gradient (u i) x, v⟫_ℝ • b i := by
  rw [coordinatesEquiv_symm_apply, weakFDeriv_ofCoordinates]
  exact coordinateDerivative_ae b u

/-- Changing the coefficient basis reconstructs the same vector-valued value field. -/
theorem coordinateValue_change_basis {κ : Type*} [Fintype κ] (b : Module.Basis ι ℝ F)
    (c : Module.Basis κ ℝ F) (u : ι → W1p μ Ω p) :
    coordinateValue c (coordinatesEquiv c ((coordinatesEquiv b).symm u)) =
      coordinateValue b u := by
  have he := prev_ofCoordinates c (coordinatesEquiv c ((coordinatesEquiv b).symm u))
  rw [← coordinatesEquiv_symm_apply,
    (coordinatesEquiv c).symm_apply_apply, coordinatesEquiv_symm_apply,
    prev_ofCoordinates] at he
  simpa only [coordinatesEquiv_symm_apply] using he.symm

/-- Changing the coefficient basis also reconstructs the same weak derivative. -/
theorem coordinateDerivative_change_basis {κ : Type*} [Fintype κ] (b : Module.Basis ι ℝ F)
    (c : Module.Basis κ ℝ F) (u : ι → W1p μ Ω p) :
    coordinateDerivative c (coordinatesEquiv c ((coordinatesEquiv b).symm u)) =
      coordinateDerivative b u := by
  have he := weakFDeriv_ofCoordinates c (coordinatesEquiv c ((coordinatesEquiv b).symm u))
  rw [← coordinatesEquiv_symm_apply,
    (coordinatesEquiv c).symm_apply_apply, coordinatesEquiv_symm_apply,
    weakFDeriv_ofCoordinates] at he
  simpa only [coordinatesEquiv_symm_apply] using he.symm

end TauCeti.WeakDerivStep
