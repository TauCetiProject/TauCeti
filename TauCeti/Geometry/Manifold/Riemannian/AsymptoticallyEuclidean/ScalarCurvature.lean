/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Infinity
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Divergence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet
import Mathlib.MeasureTheory.Integral.Asymptotics
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Topology.Instances.Matrix

/-!
# The scalar curvature of asymptotically Euclidean coefficients and existence of the mass

Let `g : ℝⁿ → (Fin n → Fin n → ℝ)` be metric coefficients in a coordinate system on the exterior of
a ball. Their **coordinate scalar curvature** `TauCeti.coordinateScalarCurvature g` is the scalar
curvature of their coordinate jet, `TauCeti.Manifold.scalarCurvatureOfJet` of the coefficients and
their first and second partial derivatives. For a smooth Riemannian metric read in a chart, this is
its scalar curvature at the corresponding point
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvatureOfJet`, for the standard basis
of `ℝⁿ`).

If `g_ij - δ_ij` is `O₂(|x|^(-t))` for some `t > 0`, that is a symbol of order `-t` and regularity
`2` at infinity in the sense of `TauCeti.IsSymbolAtInfinity`, then the coordinate scalar curvature
differs from the linearized scalar curvature `TauCeti.linearizedScalarCurvature g` by terms
quadratic in `g - δ` and its derivatives, which are `O(|x|^(-2t-2))`
(`TauCeti.isBigO_coordinateScalarCurvature_sub_linearizedScalarCurvature`). When `2t + 2 > n`, that
is `t > (n - 2) / 2`, these terms are integrable at infinity
(`TauCeti.integrableAtFilter_coordinateScalarCurvature_sub_linearizedScalarCurvature`). Hence if
the coordinate scalar curvature is integrable at infinity, so is the linearized scalar curvature,
and the divergence identity of `TauCeti.tendsto_normalizedCoordinateFlux_of_integrableOn` shows
that the normalized ADM flux converges as the radius tends to infinity: **the ADM mass exists**
(`TauCeti.exists_tendsto_normalizedCoordinateFlux_of_integrableAtFilter`).

## Main declarations

* `TauCeti.coordinateScalarCurvature`: the scalar curvature of metric coefficients on `ℝⁿ`.
* `TauCeti.continuousAt_coordinateScalarCurvature`: it is continuous at points where the
  coefficients are `C²` and the Gram matrix is invertible.
* `TauCeti.isBigO_coordinateScalarCurvature_sub_linearizedScalarCurvature`: the quadratic remainder
  is `O(|x|^(-2t-2))`.
* `TauCeti.integrableAtFilter_coordinateScalarCurvature_sub_linearizedScalarCurvature`: it is
  integrable at infinity when `2t + 2 > n`.
* `TauCeti.exists_tendsto_normalizedCoordinateFlux_of_integrableAtFilter`: existence of the mass.

## References

* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Definition 8.2,
  Lemma 9.4 and Theorem 9.6 (existence of the mass).
* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  §4.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Asymptotics Bornology Module
open scoped Topology

namespace TauCeti

variable {n : ℕ}

/-- The **coordinate scalar curvature** of metric coefficients `g i j` on `ℝⁿ`: the scalar
curvature `TauCeti.Manifold.scalarCurvatureOfJet` of their coordinate jet at `x`, made of the Gram
matrix `g_ij(x)`, the first partial derivatives `∂ₖ g_ij(x)` and the second partial derivatives
`∂ₘ ∂ₖ g_ij(x)`. For a smooth Riemannian metric whose chart metric has the coefficients `g` in the
standard basis, this is its scalar curvature
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvatureOfJet`). -/
def coordinateScalarCurvature (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Manifold.scalarCurvatureOfJet (Matrix.of fun i j ↦ g x i j)
    (fun k i j ↦ fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single k 1))
    (fun m k i j ↦ fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x
      (EuclideanSpace.single m 1))

/-- Unfolding lemma for `TauCeti.coordinateScalarCurvature`. -/
theorem coordinateScalarCurvature_def (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateScalarCurvature g x =
      Manifold.scalarCurvatureOfJet (Matrix.of fun i j ↦ g x i j)
        (fun k i j ↦ fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single k 1))
        (fun m k i j ↦ fderiv ℝ
          (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x
          (EuclideanSpace.single m 1)) :=
  (rfl)

/-- Constant coefficients, such as those of the Euclidean metric `δ_ij`, have vanishing coordinate
scalar curvature. -/
@[simp]
theorem coordinateScalarCurvature_const (a : Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateScalarCurvature (fun _ ↦ a) x = 0 := by
  simp [coordinateScalarCurvature_def, Manifold.scalarCurvatureOfJet_def,
    Manifold.riemannOfJet_def, Manifold.christoffelDerivOfJet_def,
    Manifold.christoffelOfJet_def]

/-- The coordinate scalar curvature at `x` only depends on the coefficients near `x`. -/
theorem coordinateScalarCurvature_congr_of_eventuallyEq
    {g g' : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : g =ᶠ[𝓝 x] g') :
    coordinateScalarCurvature g x = coordinateScalarCurvature g' x := by
  -- The coefficients and their first partial derivatives agree near `x`.
  have hd (i j : Fin n) : (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ (fun z ↦ g' z i j) y :=
    h.eventuallyEq_nhds.mono fun y hy ↦ (hy.fun_comp fun a ↦ a i j).fderiv_eq
  have hdd (i j k : Fin n) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g' z i j) y (EuclideanSpace.single k 1)) x :=
    ((hd i j).fun_comp fun L ↦ L (EuclideanSpace.single k 1)).fderiv_eq
  simp only [coordinateScalarCurvature_def, h.eq_of_nhds, (hd _ _).eq_of_nhds, hdd]

/-- The coordinate scalar curvature is continuous at every point where the coefficients are `C²`
and their Gram matrix is invertible. -/
theorem continuousAt_coordinateScalarCurvature
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x)
    (hdet : (Matrix.of fun i j ↦ g x i j).det ≠ 0) :
    ContinuousAt (coordinateScalarCurvature g) x := by
  have hD (i j k : Fin n) :
      ContDiffAt ℝ 1 (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x :=
    ((hg i j).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have h₀ : ContinuousAt (fun y ↦ Matrix.of fun i j ↦ g y i j) x :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ (hg i j).continuousAt
  have h₁ : ContinuousAt (fun y k i j ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1))
      x :=
    continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦
      (hD i j k).continuousAt
  have h₂ : ContinuousAt (fun y m k i j ↦ fderiv ℝ
      (fun y' ↦ fderiv ℝ (fun z ↦ g z i j) y' (EuclideanSpace.single k 1)) y
      (EuclideanSpace.single m 1)) x :=
    continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
      continuousAt_pi.2 fun j ↦ (((hD i j k).fderiv_right (m := 0) (by norm_num)).continuousAt
        ).clm_apply continuousAt_const
  simpa only [← coordinateScalarCurvature_def] using h₀.scalarCurvatureOfJet hdet h₁ h₂

section Decay

variable {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {t : ℝ}

/-- Coefficients whose difference from `δ_ij` is a symbol of regularity `2` at infinity are `C²`
near infinity. -/
private lemma eventually_contDiffAt_of_isSymbolAtInfinity {ℓ : ℝ}
    (hg : ∀ i j, IsSymbolAtInfinity 2 ℓ fun x ↦ g x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    ∀ᶠ x in cobounded _, ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x := by
  refine eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ ?_
  filter_upwards [(hg i j).eventually_contDiffAt] with x hx
  simpa using hx.add (contDiffAt_const (c := (1 : Matrix (Fin n) (Fin n) ℝ) i j))

/-- Coefficients decaying to `δ_ij` have Gram matrices tending to the identity. -/
private lemma tendsto_matrix_of_of_isSymbolAtInfinity (ht : 0 < t)
    (hg : ∀ i j, IsSymbolAtInfinity 2 (-t) fun x ↦ g x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    Tendsto (fun x ↦ Matrix.of fun i j ↦ g x i j) (cobounded _) (𝓝 1) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ by
    simpa using (hg i j).tendsto_of_sub (neg_lt_zero.2 ht)

/-- **The scalar curvature is linear up to quadratic terms.** If the metric coefficients satisfy
`g_ij - δ_ij = O₂(|x|^(-t))` for some `t > 0`, then their coordinate scalar curvature differs from
their linearized scalar curvature by `O(|x|^(-2t-2))` at infinity. -/
theorem isBigO_coordinateScalarCurvature_sub_linearizedScalarCurvature (ht : 0 < t)
    (hg : ∀ i j, IsSymbolAtInfinity 2 (-t) fun x ↦ g x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    (fun x ↦ coordinateScalarCurvature g x - linearizedScalarCurvature g x) =O[cobounded _]
      fun x ↦ ‖x‖ ^ (-2 * t - 2) := by
  -- The first partial derivatives are symbols of order `-t - 1`, so the second ones are
  -- `O(|x|^(-t-2))`.
  have hD (i j k : Fin n) : IsSymbolAtInfinity 1 (-t - 1)
      fun x ↦ fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single k 1) := by
    have := (hg i j).fderiv.continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1))
    simp only [fderiv_sub_const, ContinuousLinearMap.apply_apply] at this
    exact_mod_cast this
  have hDD (m k i j : Fin n) : (fun x ↦ fderiv ℝ
      (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x
      (EuclideanSpace.single m 1)) =O[cobounded _] fun x ↦ ‖x‖ ^ (-t - 1 - 1) :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single m 1)).isBigO_comp _ _).trans
      (hD i j k).fderiv.isBigO
  have hsymm : ∀ᶠ x in cobounded _, ∀ m k i j : Fin n,
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x
          (EuclideanSpace.single m 1) =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single m 1)) x
          (EuclideanSpace.single k 1) := by
    filter_upwards [eventually_contDiffAt_of_isSymbolAtInfinity hg] with x hx m k i j
    exact fderiv_fderiv_apply_comm (hx i j) (by simp) _ _
  have key := Manifold.isBigO_scalarCurvatureOfJet_sub
    (tendsto_matrix_of_of_isSymbolAtInfinity ht hg)
    (fun i j ↦ by simpa using (hg i j).isBigO) (fun k i j ↦ (hD i j k).isBigO) hDD hsymm
  refine (key.trans ?_).congr_left fun x ↦ by
    rw [coordinateScalarCurvature_def, linearizedScalarCurvature_def]
  -- Both quadratic terms are `|x|^(-2t-2)`.
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ne_cobounded 0] with x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h : ‖‖x‖ ^ (-t)‖ * ‖‖x‖ ^ (-t - 1 - 1)‖ + ‖‖x‖ ^ (-t - 1)‖ ^ 2 =
      2 * ‖‖x‖ ^ (-2 * t - 2)‖ := by
    have h₁ : ‖x‖ ^ (-t) * ‖x‖ ^ (-t - 1 - 1) = ‖x‖ ^ (-2 * t - 2) := by
      rw [← Real.rpow_add hx']
      congr 1
      ring
    have h₂ : (‖x‖ ^ (-t - 1)) ^ 2 = ‖x‖ ^ (-2 * t - 2) := by
      rw [← Real.rpow_mul_natCast hx'.le]
      congr 1
      push_cast
      ring
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg hx'.le _), h₁, h₂]
    ring
  rw [h, norm_mul, Real.norm_two, norm_norm]

/-- **The quadratic remainder is integrable at infinity.** If `g_ij - δ_ij = O₂(|x|^(-t))` with
`t > 0` and `2t + 2 > n`, then the coordinate scalar curvature minus the linearized scalar
curvature is integrable on the complement of a large ball. -/
theorem integrableAtFilter_coordinateScalarCurvature_sub_linearizedScalarCurvature (ht : 0 < t)
    (htn : (n : ℝ) < 2 * t + 2)
    (hg : ∀ i j, IsSymbolAtInfinity 2 (-t) fun x ↦ g x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    IntegrableAtFilter (fun x ↦ coordinateScalarCurvature g x - linearizedScalarCurvature g x)
      (cobounded _) := by
  -- Near infinity the coefficients are `C²` with invertible Gram matrix, so the coordinate scalar
  -- curvature is continuous there.
  have hdet : ∀ᶠ x in cobounded _, (Matrix.of fun i j ↦ g x i j).det ≠ 0 :=
    Matrix.eventually_det_ne_zero_of_tendsto_one (tendsto_matrix_of_of_isSymbolAtInfinity ht hg)
  obtain ⟨R, -, hR⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).mem_iff.1
      ((eventually_contDiffAt_of_isSymbolAtInfinity hg).and hdet)
  have hm : StronglyMeasurableAtFilter
      (fun x ↦ coordinateScalarCurvature g x - linearizedScalarCurvature g x) (cobounded _) :=
    ⟨(closedBall 0 R)ᶜ, (hasBasis_cobounded_compl_closedBall 0).mem_of_mem trivial,
      (ContinuousOn.aestronglyMeasurable (fun x hx ↦ (continuousAt_coordinateScalarCurvature
        (hR hx).1 (hR hx).2).continuousWithinAt) measurableSet_closedBall.compl).sub
        (measurable_linearizedScalarCurvature g).aestronglyMeasurable⟩
  have hO := isBigO_coordinateScalarCurvature_sub_linearizedScalarCurvature ht hg
  have hint := integrableAtFilter_norm_rpow_cobounded (E := EuclideanSpace ℝ (Fin n))
    (mu := volume) (s := -2 * t - 2) (by rw [finrank_euclideanSpace_fin]; linarith)
  rw [cobounded_eq_cocompact] at hO hm hint ⊢
  exact hO.integrableAtFilter hm hint

/-- **Existence of the mass.** If the metric coefficients satisfy `g_ij - δ_ij = O₂(|x|^(-t))`
with `t > 0` and `2t + 2 > n`, and their coordinate scalar curvature is integrable at infinity,
then the normalized ADM flux converges as the radius tends to infinity. -/
theorem exists_tendsto_normalizedCoordinateFlux_of_integrableAtFilter (ht : 0 < t)
    (htn : (n : ℝ) < 2 * t + 2)
    (hg : ∀ i j, IsSymbolAtInfinity 2 (-t) fun x ↦ g x i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hS : IntegrableAtFilter (coordinateScalarCurvature g) (cobounded _)) :
    ∃ m, Tendsto (normalizedCoordinateFlux g) atTop (𝓝 m) := by
  -- The linearized scalar curvature is the coordinate scalar curvature minus the remainder.
  obtain ⟨s, hs, hL⟩ : IntegrableAtFilter (linearizedScalarCurvature g) (cobounded _) := by
    have h := hS.sub
      (integrableAtFilter_coordinateScalarCurvature_sub_linearizedScalarCurvature ht htn hg)
    rwa [show coordinateScalarCurvature g - _ = linearizedScalarCurvature g from
      funext fun x ↦ sub_sub_cancel _ _] at h
  obtain ⟨R, -, hR⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).mem_iff.1
      (inter_mem hs (eventually_contDiffAt_of_isSymbolAtInfinity hg))
  exact exists_tendsto_normalizedCoordinateFlux_of_integrableOn
    (fun i j x hx ↦ ((hR hx).2 i j).contDiffWithinAt) (hL.mono_set fun x hx ↦ (hR hx).1)

end Decay

end TauCeti
