/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
public import TauCeti.Analysis.SpecialFunctions.CantorFunction
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Shift

import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Checks for `ACL` and `ACL^p` maps

Checks of QuasiregularMaps §5.1 for the formal derivative `TauCeti.formalDeriv`, the line
function `TauCeti.lineFunction` and the class `TauCeti.IsACLOn`, on `ℝ² = EuclideanSpace ℝ (Fin 2)`
with coordinates `x₁ = x 0` and `x₂ = x 1`.

* `|x₁|` is `ACL^∞` (`TauCeti.ACLChecks.isACLpOn_absFst`). Off the line `x₁ = 0` its formal
  derivative is `e₁ ↦ sign x₁`, `e₂ ↦ 0`; on that line the first partial derivative does not
  exist and the formal derivative sends `e₁` to `0`; the line is a null set
  (`TauCeti.ACLChecks.volume_setOf_fst_eq_zero`).
* `c(x₁)`, for the Cantor function `c`, has formal derivative `0` almost everywhere
  (`TauCeti.ACLChecks.ae_formalDeriv_cantorFst_eq_zero`) but is not `ACL`
  (`TauCeti.ACLChecks.not_isACLOn_cantorFst`): every line function in the first direction on the
  box `[0, 1]²` is `c` on `[0, 1]`.
* The indicator of `{0}` is absolutely continuous on every coordinate segment missing `0`
  (`TauCeti.ACLChecks.absolutelyContinuousOnInterval_lineFunction_indicatorZero`) but is not
  `ACL`, since it is not continuous (`TauCeti.ACLChecks.not_isACLOn_indicatorZero`).
* The formal derivative takes partial derivatives as columns: for `u(x₁, x₂) = (x₂, 0)` it is
  `e₁ ↦ 0`, `e₂ ↦ e₁`, which is `fderiv ℝ u x` (`TauCeti.ACLChecks.formalDeriv_swapFst`).
* The segment of the line function is the one of the box: through `(1/2, 1/2)` in the second
  direction, the line function is `t ↦ u(1/2, t)`, and on `[0, 1]` it stays in `[0, 1]²`, while
  the unshifted `t ↦ u(x + t e₂)` leaves the box at `t = 1`
  (`TauCeti.ACLChecks.lineFunction_half_half`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace TauCeti.ACLChecks

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "e" => EuclideanSpace.single

/-- If `f` has derivative `f'` at `a`, then `t ↦ f(a + t)` has derivative `f'` at `0`. -/
theorem hasDerivAt_comp_const_add_zero {f : ℝ → ℝ} {f' a : ℝ} (h : HasDerivAt f f' a) :
    HasDerivAt (fun t ↦ f (a + t)) f' 0 := by
  have h' : HasDerivAt f f' (a + 0) := by rwa [add_zero]
  exact HasDerivAt.comp_const_add a 0 h'

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
  refine HasLineDerivAt.lineDeriv ?_
  refine (hasDerivAt_comp_const_add_zero (hasDerivAt_abs hx)).congr_of_eventuallyEq
    (Eventually.of_forall fun t ↦ ?_)
  simp [absFst_apply]

/-- The formal derivative of `|x₁|` sends `e₂` to `0`. -/
theorem formalDeriv_absFst_single_one (x : ℝ²) : formalDeriv absFst x (e 1 1) = 0 := by
  rw [formalDeriv_apply_single]
  refine HasLineDerivAt.lineDeriv ?_
  refine (hasDerivAt_const (0 : ℝ) |x 0|).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  simp [absFst_apply]

/-- On the line `x₁ = 0`, the first partial derivative of `|x₁|` does not exist. -/
theorem not_lineDifferentiableAt_absFst {x : ℝ²} (hx : x 0 = 0) :
    ¬ LineDifferentiableAt ℝ absFst x (e 0 1) := by
  intro h
  refine not_differentiableAt_abs_zero ?_
  have h' : DifferentiableAt ℝ (fun t : ℝ ↦ absFst (x + t • e 0 1)) 0 := h
  refine h'.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  simp [absFst_apply, hx]

/-- On the line `x₁ = 0`, the formal derivative of `|x₁|` sends `e₁` to `0`. -/
theorem formalDeriv_absFst_single_zero_of_eq_zero {x : ℝ²} (hx : x 0 = 0) :
    formalDeriv absFst x (e 0 1) = 0 := by
  rw [formalDeriv_apply_single]
  exact lineDeriv_zero_of_not_lineDifferentiableAt (not_lineDifferentiableAt_absFst hx)

/-- The line `x₁ = 0` is a null set in `ℝ²`. -/
theorem volume_setOf_fst_eq_zero : volume {x : ℝ² | x 0 = 0} = 0 := by
  have h : {x : ℝ² | x 0 = 0} =
      ((LinearMap.ker (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap :
        Submodule ℝ ℝ²) : Set ℝ²) := by
    ext x
    simp
  rw [h]
  refine Measure.addHaar_submodule _ _ fun htop ↦ ?_
  have : e 0 (1 : ℝ) ∈ LinearMap.ker (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap :=
    htop ▸ Submodule.mem_top
  simp at this

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
  rw [coordinateBox_eq_preimage_Icc]
  rw [show ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc (fun _ ↦ (0 : ℝ)) fun _ ↦ 1) =
    WithLp.ofLp ⁻¹' Icc (fun _ ↦ (0 : ℝ)) fun _ ↦ 1 from rfl,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp

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

/-- The formal derivative of `c(x₁)` vanishes almost everywhere: a definition of `ACL` asking only
for partial derivatives almost everywhere would accept `c(x₁)`. -/
theorem ae_formalDeriv_cantorFst_eq_zero : ∀ᵐ x : ℝ², formalDeriv cantorFst x = 0 := by
  have hnull : volume {x : ℝ² | ¬ HasDerivAt cantorFunction 0 (x 0)} = 0 := by
    have hpi := Measure.pi_eval_preimage_null (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
      (i := 0) (ae_iff.1 ae_hasDerivAt_cantorFunction)
    rw [← volume_pi] at hpi
    exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.preimage_null hpi
  refine ae_iff.2 (measure_mono_null (fun x hx ↦ ?_) hnull)
  simp only [mem_ofPred_eq] at hx ⊢
  intro h
  apply hx
  refine EuclideanSpace.ext_continuousLinearMap_single fun i ↦ ?_
  rw [formalDeriv_apply_single, zero_apply]
  refine HasLineDerivAt.lineDeriv ?_
  fin_cases i
  · refine (hasDerivAt_comp_const_add_zero h).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ ?_)
    simp [cantorFst_apply]
  · refine (hasDerivAt_const (0 : ℝ) (cantorFunction (x 0))).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ ?_)
    simp [cantorFst_apply]

/-! ### The indicator of the origin -/

/-- The indicator of `{0}` in `ℝ²`. -/
def indicatorZero : ℝ² → ℝ := ({0} : Set ℝ²).indicator 1

/-- The indicator of `{0}` is not continuous at `0`, so it is not `ACL` on any set containing a
neighbourhood of `0`. -/
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
def swapFst : ℝ² →L[ℝ] ℝ² := (EuclideanSpace.proj (1 : Fin 2)).smulRight (e 0 (1 : ℝ))

/-- The value of `(x₁, x₂) ↦ (x₂, 0)` at `x`. -/
theorem swapFst_apply (x : ℝ²) : swapFst x = x 1 • e 0 1 := (rfl)

/-- The formal derivative takes partial derivatives as columns: for `u(x₁, x₂) = (x₂, 0)`, it sends
`e₁ ↦ 0` and `e₂ ↦ e₁`, the matrix `[[0, 1], [0, 0]]`, and it is the Fréchet derivative. The rows
would give `e₁ ↦ e₂`, which is not the derivative. -/
theorem formalDeriv_swapFst (x : ℝ²) :
    formalDeriv swapFst x (e 0 1) = 0 ∧ formalDeriv swapFst x (e 1 1) = e 0 1 ∧
      formalDeriv swapFst x = fderiv ℝ swapFst x ∧ formalDeriv swapFst x (e 0 1) ≠ e 1 1 := by
  have hd : formalDeriv swapFst x = swapFst :=
    (formalDeriv_eq_fderiv swapFst.differentiableAt).trans swapFst.fderiv
  refine ⟨?_, ?_, formalDeriv_eq_fderiv swapFst.differentiableAt, ?_⟩
  · simp [hd, swapFst_apply]
  · simp [hd, swapFst_apply]
  · rw [hd, swapFst_apply]
    intro h
    have := congrArg (fun y : ℝ² ↦ y 1) h
    simp at this

/-! ### The segment of a line function -/

/-- The point `(1/2, 1/2)` of `ℝ²`. -/
def halfHalf : ℝ² := (EuclideanSpace.equiv (Fin 2) ℝ).symm fun _ ↦ 1 / 2

/-- Through `x = (1/2, 1/2)` in the second direction, the line function of any `u` is
`t ↦ u(1/2, t)`, reading `u` on the segment of the box `[0, 1]²` for `t ∈ [0, 1]`; the unshifted
`t ↦ u(x + t e₂)` reads `u` at `(1/2, 3/2)` at `t = 1`, outside the box. -/
theorem lineFunction_half_half {F : Type*} (u : ℝ² → F) (t : ℝ) :
    lineFunction u halfHalf 1 t = u ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![1 / 2, t]) ∧
      (t ∈ Icc 0 1 → (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1 / 2, t] ∈
        coordinateBox (fun _ ↦ 0) fun _ ↦ 1) ∧
      halfHalf + (1 : ℝ) • e 1 1 ∉ coordinateBox (fun _ ↦ 0) fun _ ↦ 1 := by
  refine ⟨?_, fun ht ↦ mem_coordinateBox.2 fun j ↦ ?_, fun h ↦ ?_⟩
  · rw [lineFunction_apply]
    congr 1
    ext j
    fin_cases j <;> simp [halfHalf]
  · fin_cases j <;> norm_num [ht.1, ht.2]
  · have := (mem_coordinateBox.1 h 1).2
    simp [halfHalf] at this
    norm_num at this

end TauCeti.ACLChecks
