/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
public import TauCeti.Analysis.SpecialFunctions.CantorFunction
public import Mathlib.Analysis.Calculus.Deriv.Abs

import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Checks for `ACL` and `ACL^p` maps

Checks for the formal derivative `TauCeti.formalDeriv`, the line
function `TauCeti.lineFunction` and the class `TauCeti.IsACLOn`, on `ℝ² = EuclideanSpace ℝ (Fin 2)`
with coordinates `x₁ = x 0` and `x₂ = x 1`.

* `|x₁|` is `ACL^∞` (`TauCeti.ACLChecks.isACLpOn_absFst`). Off the line `x₁ = 0` its formal
  derivative is `e₁ ↦ sign x₁`, `e₂ ↦ 0`; on that line the first partial derivative does not
  exist and the formal derivative sends `e₁` to `0`; the line is a null set
  (`TauCeti.ACLChecks.volume_setOf_fst_eq_zero`).
* `c(x₁)`, for the Cantor function `c`, has both partial derivatives `0` almost everywhere
  (`TauCeti.ACLChecks.ae_hasLineDerivAt_cantorFst`), so its formal derivative vanishes almost
  everywhere (`TauCeti.ACLChecks.ae_formalDeriv_cantorFst_eq_zero`), but it is not `ACL`
  (`TauCeti.ACLChecks.not_isACLOn_cantorFst`): every line function in the first direction on the
  box `[0, 1]²` is `c` on `[0, 1]`.
* The indicator of `{0}` is absolutely continuous on every segment of a coordinate line missing `0`
  (`TauCeti.ACLChecks.absolutelyContinuousOnInterval_lineFunction_indicatorZero`) but is not
  `ACL`, since it is not continuous (`TauCeti.ACLChecks.not_isACLOn_indicatorZero`).
* The formal derivative takes partial derivatives as columns: for `u(x₁, x₂) = (x₂, 0)` it is
  `e₁ ↦ 0`, `e₂ ↦ e₁`, which is `fderiv ℝ u x`
  (`TauCeti.ACLChecks.formalDeriv_sndSmulSingleZero`).
* The segment of the line function is the one of the box: through `(1/2, 1/2)` in the second
  direction, the line function is `t ↦ u(1/2, t)` (`TauCeti.ACLChecks.lineFunction_halfHalf`),
  and on `[0, 1]` it stays in `[0, 1]²` (`TauCeti.ACLChecks.equiv_symm_half_mem_coordinateBox`),
  while the unshifted `t ↦ u(x + t e₂)` leaves the box at `t = 1`
  (`TauCeti.ACLChecks.halfHalf_add_one_smul_single_notMem_coordinateBox`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace TauCeti.ACLChecks

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "e" => EuclideanSpace.single

/-! ### `|x₁|` -/

/-- The map `x ↦ |x₁|` on `ℝ²`. -/
def absFst (x : ℝ²) : ℝ := |x 0|

/-- The value of `|x₁|` at `x`. -/
theorem absFst_apply (x : ℝ²) : absFst x = |x 0| := (rfl)

/-- `|x₁|` is `1`-Lipschitz. -/
theorem lipschitzWith_absFst : LipschitzWith 1 absFst := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [NNReal.coe_one, one_mul, absFst_apply, absFst_apply, Real.dist_eq]
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  simpa [Real.norm_eq_abs, dist_eq_norm] using PiLp.norm_apply_le (x - y) 0

/-- `|x₁|` is `ACL^∞` on `ℝ²`. -/
theorem isACLpOn_absFst : IsACLpOn absFst ∞ univ :=
  lipschitzWith_absFst.locallyLipschitz.isACLpOn univ ∞

/-- Off the line `x₁ = 0`, the formal derivative of `|x₁|` sends `e₁` to `sign x₁`. -/
theorem formalDeriv_absFst_single_zero {x : ℝ²} (hx : x 0 ≠ 0) :
    formalDeriv absFst x (e 0 1) = SignType.sign (x 0) := by
  rw [formalDeriv_apply_single]
  exact ((hasDerivAt_abs hx).hasLineDerivAt_of_add_smul <| .of_forall fun t ↦ by
    simp [absFst_apply]).lineDeriv

/-- The formal derivative of `|x₁|` sends `e₂` to `0`. -/
theorem formalDeriv_absFst_single_one (x : ℝ²) : formalDeriv absFst x (e 1 1) = 0 := by
  rw [formalDeriv_apply_single]
  exact ((hasDerivAt_const (x 1) |x 0|).hasLineDerivAt_of_add_smul <| .of_forall fun t ↦ by
    simp [absFst_apply]).lineDeriv

/-- On the line `x₁ = 0`, the first partial derivative of `|x₁|` does not exist. -/
theorem not_lineDifferentiableAt_absFst {x : ℝ²} (hx : x 0 = 0) :
    ¬ LineDifferentiableAt ℝ absFst x (e 0 1) := by
  intro h
  unfold LineDifferentiableAt at h
  refine not_differentiableAt_abs_zero ?_
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  simp [absFst_apply, hx]

/-- On the line `x₁ = 0`, the formal derivative of `|x₁|` sends `e₁` to `0`. -/
theorem formalDeriv_absFst_single_zero_of_eq_zero {x : ℝ²} (hx : x 0 = 0) :
    formalDeriv absFst x (e 0 1) = 0 := by
  rw [formalDeriv_apply_single]
  exact lineDeriv_zero_of_not_lineDifferentiableAt (not_lineDifferentiableAt_absFst hx)

/-- The line `x₁ = 0` is a null set in `ℝ²`. -/
theorem volume_setOf_fst_eq_zero : volume {x : ℝ² | x 0 = 0} = 0 := by
  simpa using volume_setOf_apply_mem_eq_zero (Real.volume_singleton (a := 0)) 0

/-! ### The Cantor function of `x₁` -/

/-- The map `x ↦ c(x₁)` on `ℝ²`, for the Cantor function `c`. -/
def cantorFst (x : ℝ²) : ℝ := cantorFunction (x 0)

/-- The value of `c(x₁)` at `x`. -/
theorem cantorFst_apply (x : ℝ²) : cantorFst x = cantorFunction (x 0) := (rfl)

/-- Every line function of `c(x₁)` in the first direction is the Cantor function. -/
theorem lineFunction_cantorFst (x : ℝ²) : lineFunction cantorFst x 0 = cantorFunction := by
  funext t
  simp [lineFunction_apply, cantorFst_apply]

/-- The closed box `[0, 1]²` has measure `1`. -/
theorem volume_coordinateBox_zero_one :
    volume (coordinateBox (fun _ : Fin 2 ↦ (0 : ℝ)) fun _ ↦ 1) = 1 := by
  simp [volume_coordinateBox]

/-- `c(x₁)` is not `ACL` on `ℝ²`: on the box `[0, 1]²`, every line function in the first direction
is the Cantor function on `[0, 1]`, which is not absolutely continuous. -/
theorem not_isACLOn_cantorFst : ¬ IsACLOn cantorFst univ := by
  intro h
  have hae := h.ae_absolutelyContinuousOnInterval (fun _ ↦ 0) (fun _ ↦ 1)
    (fun _ ↦ zero_lt_one) (subset_univ _) 0
  simp only [lineFunction_cantorFst] at hae
  have hfalse : ∀ᵐ _ ∂volume.restrict (coordinateBox (fun _ : Fin 2 ↦ (0 : ℝ)) fun _ ↦ 1),
      False := hae.mono fun _ hx ↦ not_absolutelyContinuousOnInterval_cantorFunction hx
  have h0 : volume.restrict (coordinateBox (fun _ : Fin 2 ↦ (0 : ℝ)) fun _ ↦ 1) univ = 0 := by
    simpa [ae_iff] using hfalse
  rw [Measure.restrict_apply_univ, volume_coordinateBox_zero_one] at h0
  exact one_ne_zero h0

/-- Almost everywhere, both partial derivatives of `c(x₁)` exist and are `0`: a definition of
`ACL` asking only for partial derivatives almost everywhere would accept `c(x₁)`. -/
theorem ae_hasLineDerivAt_cantorFst :
    ∀ᵐ x : ℝ², ∀ i, HasLineDerivAt ℝ cantorFst 0 x (e i 1) := by
  refine ae_iff.2 (measure_mono_null (fun x hx ↦ ?_)
    (volume_setOf_apply_mem_eq_zero (ae_iff.1 ae_hasDerivAt_cantorFunction) 0))
  simp only [mem_ofPred_eq] at hx ⊢
  intro h
  apply hx
  intro i
  fin_cases i
  · exact h.hasLineDerivAt_of_add_smul <| .of_forall fun t ↦ by simp [cantorFst_apply]
  · exact (hasDerivAt_const (x 1) (cantorFunction (x 0))).hasLineDerivAt_of_add_smul
      (.of_forall fun t ↦ by simp [cantorFst_apply])

/-- The formal derivative of `c(x₁)` vanishes almost everywhere. -/
theorem ae_formalDeriv_cantorFst_eq_zero : ∀ᵐ x : ℝ², formalDeriv cantorFst x = 0 :=
  ae_hasLineDerivAt_cantorFst.mono fun _ hx ↦ EuclideanSpace.ext_continuousLinearMap_single
    fun i ↦ by rw [formalDeriv_apply_single, zero_apply, (hx i).lineDeriv]

/-! ### The indicator of the origin -/

/-- The indicator of `{0}` in `ℝ²`. -/
def indicatorZero : ℝ² → ℝ := ({0} : Set ℝ²).indicator 1

/-- The indicator of `{0}` is not continuous at `0`, so it is not `ACL` on `ℝ²`. -/
theorem not_isACLOn_indicatorZero : ¬ IsACLOn indicatorZero univ := by
  intro h
  have hc : ContinuousAt indicatorZero 0 := h.continuousOn.continuousAt univ_mem
  have ht : Tendsto (fun r : ℝ ↦ (r • e 0 1 : ℝ²)) (𝓝[≠] 0) (𝓝 0) := by
    have hc' : Continuous fun r : ℝ ↦ (r • e 0 1 : ℝ²) := continuous_id.smul continuous_const
    have h1 := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using h1
  have hlim : Tendsto (fun r : ℝ ↦ indicatorZero (r • e 0 1)) (𝓝[≠] 0) (𝓝 1) := by
    have h1 := hc.tendsto.comp ht
    rwa [show indicatorZero 0 = 1 by simp [indicatorZero]] at h1
  have hzero : (fun r : ℝ ↦ indicatorZero (r • e 0 1)) =ᶠ[𝓝[≠] 0] fun _ ↦ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : r ≠ 0 := hr
    simp [indicatorZero, hr']
  have := tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds
  norm_num at this

/-- On a coordinate line missing `0`, the indicator of `{0}` is `0`, hence absolutely continuous on
every segment. -/
theorem absolutelyContinuousOnInterval_lineFunction_indicatorZero {x : ℝ²} {i : Fin 2}
    (hx : ∃ j ≠ i, x j ≠ 0) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (lineFunction indicatorZero x i) a b := by
  have h0 : lineFunction indicatorZero x i = fun _ ↦ 0 := by
    funext t
    obtain ⟨j, hji, hxj⟩ := hx
    rw [lineFunction_apply, indicatorZero, indicator_of_notMem]
    intro h
    have := congrArg (fun y : ℝ² ↦ y j) (mem_singleton_iff.1 h)
    exact hxj (by simpa [hji] using this)
  rw [h0]
  exact (LipschitzWith.const' (0 : ℝ) (K := 0)).lipschitzOnWith.absolutelyContinuousOnInterval

/-! ### Columns -/

/-- The linear map `(x₁, x₂) ↦ (x₂, 0)` on `ℝ²`. -/
def sndSmulSingleZero : ℝ² →L[ℝ] ℝ² := (EuclideanSpace.proj (1 : Fin 2)).smulRight (e 0 (1 : ℝ))

/-- The value of `(x₁, x₂) ↦ (x₂, 0)` at `x`. -/
theorem sndSmulSingleZero_apply (x : ℝ²) : sndSmulSingleZero x = x 1 • e 0 1 := (rfl)

/-- The formal derivative takes partial derivatives as columns: for `u(x₁, x₂) = (x₂, 0)`, it sends
`e₁ ↦ 0` and `e₂ ↦ e₁`, the matrix `[[0, 1], [0, 0]]`, and it is the Fréchet derivative. The rows
would give `e₁ ↦ e₂`, which is not the derivative. -/
theorem formalDeriv_sndSmulSingleZero (x : ℝ²) :
    formalDeriv sndSmulSingleZero x (e 0 1) = 0 ∧
      formalDeriv sndSmulSingleZero x (e 1 1) = e 0 1 ∧
      formalDeriv sndSmulSingleZero x = fderiv ℝ sndSmulSingleZero x ∧
      formalDeriv sndSmulSingleZero x (e 0 1) ≠ e 1 1 := by
  have hd : formalDeriv sndSmulSingleZero x = sndSmulSingleZero :=
    (formalDeriv_eq_fderiv sndSmulSingleZero.differentiableAt).trans sndSmulSingleZero.fderiv
  refine ⟨?_, ?_, formalDeriv_eq_fderiv sndSmulSingleZero.differentiableAt, ?_⟩
  · simp [hd, sndSmulSingleZero_apply]
  · simp [hd, sndSmulSingleZero_apply]
  · rw [hd, sndSmulSingleZero_apply]
    intro h
    have := congrArg (fun y : ℝ² ↦ y 1) h
    simp at this

/-! ### The segment of a line function -/

/-- The point `(1/2, 1/2)` of `ℝ²`. -/
def halfHalf : ℝ² := (EuclideanSpace.equiv (Fin 2) ℝ).symm fun _ ↦ 1 / 2

/-- Through `(1/2, 1/2)` in the second direction, the line function of any `u` is
`t ↦ u(1/2, t)`. -/
theorem lineFunction_halfHalf {F : Type*} (u : ℝ² → F) (t : ℝ) :
    lineFunction u halfHalf 1 t = u ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![1 / 2, t]) := by
  rw [lineFunction_apply]
  congr 1
  ext j
  fin_cases j <;> simp [halfHalf]

/-- For `t ∈ [0, 1]`, the point `(1/2, t)` lies in the box `[0, 1]²`, so the line function through
`(1/2, 1/2)` in the second direction reads `u` on the segment of the box. -/
theorem equiv_symm_half_mem_coordinateBox {t : ℝ} (ht : t ∈ Icc 0 1) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1 / 2, t] ∈ coordinateBox (fun _ ↦ 0) fun _ ↦ 1 :=
  mem_coordinateBox.2 fun j ↦ by fin_cases j <;> norm_num [ht.1, ht.2]

/-- The unshifted `t ↦ u(x + t e₂)` through `x = (1/2, 1/2)` reads `u` at `(1/2, 3/2)` at `t = 1`,
outside the box `[0, 1]²`. -/
theorem halfHalf_add_one_smul_single_notMem_coordinateBox :
    halfHalf + (1 : ℝ) • e 1 1 ∉ coordinateBox (fun _ ↦ 0) fun _ ↦ 1 := by
  intro h
  have := (mem_coordinateBox.1 h 1).2
  simp [halfHalf] at this
  norm_num at this

end TauCeti.ACLChecks
