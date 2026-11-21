/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
public import TauCeti.Analysis.Sobolev.BesselPotential.Exp
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.PDE.Vortex.Reduced.Sobolev
import TauCeti.Analysis.Polynomial.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian

/-!
# The reduced vortex equation as a smooth map between Sobolev spaces

Let `P` be a complex polynomial of degree `m ≥ 1`, and put

`h = ‖P‖² / (1 + ‖P‖²)`,    `g = 2 ‖P'‖² / (1 + ‖P‖²)²`,    `k = (h - 1) / 8 + g`.

Taubes's plane vortex with zero divisor `P` is reconstructed from the solution `w` of the reduced
equation

`Δw = (h exp (2w) - 1) / 8 + g = h (exp (2w) - 1) / 8 + k`

(`TauCeti.Vortex.reducedSource`). This file sets the equation on the Bessel-potential scale: for
`s > 1`, so that `H^s(ℂ)` is an algebra, the map

`N(w) = -Δw + h (exp (2w) - 1) / 8 + k`,    `N : H^(s+2)(ℂ) → H^s(ℂ)`

(`TauCeti.Vortex.reducedEquationMap`) is well defined and smooth. The coefficient `h` does not
decay at infinity, but `1 - h = (1 + ‖P‖²)⁻¹` and `k` lie in every `H^s(ℂ)`
(`Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions`,
`TauCeti.Vortex.backgroundSource_mem_realSobolevFunctions`), and
`h (exp (2w) - 1) = (exp (2w) - 1) - (1 - h)(exp (2w) - 1)` is built from the smooth exponential
`BesselPotentialSpace.expSubOne` and the product `BesselPotentialSpace.mulCLM` of `H^s(ℂ)`.

The map is `C^∞`, indeed `C^∞` over `ℂ` (`TauCeti.Vortex.contDiff_reducedEquationMap`), and its
derivative at `w` is the Schrödinger operator

`DN(w) v = -Δv + h exp (2w) v / 4`

(`TauCeti.Vortex.hasFDerivAt_reducedEquationMap`, `TauCeti.Vortex.fderiv_reducedEquationMap`,
`TauCeti.Vortex.reducedEquationDeriv`,
`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationDeriv`). The `L²` function of `N(w)` is
`-Δw + h (exp (2w) - 1) / 8 + k` (`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationMap`), the
residual of the reduced equation, so a zero of `N` is an almost-everywhere, possibly
complex-valued, solution. Conversely, the element of `H^(s+2)(ℂ)` of a classical real
square-integrable solution is a zero of `N`
(`TauCeti.Vortex.reducedEquationMap_eq_zero_of_laplacian_eq`), and Taubes's solution gives one
(`TauCeti.Vortex.exists_reducedEquationMap_eq_zero`).

This is the nonlinear operator for an implicit-function-theorem argument making the solution of
the reduced equation depend smoothly on the divisor; that argument still needs the invertibility
of the derivative `DN(w)`, which this file does not prove.

## Main definitions

* `TauCeti.Vortex.sobolevBackgroundDefect`: the coefficient `1 - h = (1 + ‖P‖²)⁻¹` in `H^s(ℂ)`.
* `TauCeti.Vortex.sobolevBackgroundSource`: the source `k` in `H^s(ℂ)`.
* `TauCeti.Vortex.reducedEquationMap`: the map `N : H^(s+2)(ℂ) → H^s(ℂ)`.
* `TauCeti.Vortex.reducedEquationDeriv`: its derivative `-Δ + h exp (2w) / 4` at `w`.

## Main results

* `TauCeti.Vortex.hasFDerivAt_reducedEquationMap`, `TauCeti.Vortex.fderiv_reducedEquationMap`:
  the derivative of `N`.
* `TauCeti.Vortex.contDiff_reducedEquationMap`: `N` is `C^∞`.
* `TauCeti.Vortex.coeFn_inclusionLp_reducedEquationMap`: the `L²` function of `N(w)`.
* `TauCeti.Vortex.reducedEquationMap_eq_zero_of_laplacian_eq`,
  `TauCeti.Vortex.exists_reducedEquationMap_eq_zero`: solutions of the reduced equation are zeros
  of `N`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open BesselPotentialSpace TemperedDistribution MeasureTheory Filter
open scoped BesselPotentialSpace Laplacian ContDiff

namespace TauCeti.Vortex

variable {P : Polynomial ℂ} {s : ℝ}

/-- The coefficient `1 - h = (1 + ‖P‖²)⁻¹` of the reduced vortex equation, with
`h = TauCeti.Vortex.backgroundWeight (P.eval ·)`, as an element of `H^s(ℂ)`. -/
def sobolevBackgroundDefect (hm : 0 < P.natDegree) (hs : 0 ≤ s) : H^{s}(ℂ) :=
  ofRealSobolevFunction hs (Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions hm s)

/-- The `L²` function of `sobolevBackgroundDefect hm hs` is `(1 + ‖P‖²)⁻¹`. -/
theorem coeFn_inclusionLp_sobolevBackgroundDefect (hm : 0 < P.natDegree) (hs : 0 ≤ s) :
    ⇑(inclusionLp hs (sobolevBackgroundDefect hm hs)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ (((1 + ‖P.eval z‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
  coeFn_inclusionLp_ofRealSobolevFunction hs _

/-- The source `k = (h - 1) / 8 + g` of the reduced vortex equation,
`TauCeti.Vortex.backgroundSource (P.eval ·)`, as an element of `H^s(ℂ)`. -/
def sobolevBackgroundSource (hm : 0 < P.natDegree) (hs : 0 ≤ s) : H^{s}(ℂ) :=
  ofRealSobolevFunction hs (backgroundSource_mem_realSobolevFunctions hm s)

/-- The `L²` function of `sobolevBackgroundSource hm hs` is
`TauCeti.Vortex.backgroundSource (P.eval ·)`. -/
theorem coeFn_inclusionLp_sobolevBackgroundSource (hm : 0 < P.natDegree) (hs : 0 ≤ s) :
    ⇑(inclusionLp hs (sobolevBackgroundSource hm hs)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ (backgroundSource (P.eval ·) z : ℂ) :=
  coeFn_inclusionLp_ofRealSobolevFunction hs _

/-- Multiplication by `h = 1 - (1 + ‖P‖²)⁻¹` on `H^s(ℂ)`: the `L²` function of
`x - (1 + ‖P‖²)⁻¹ x` is `h x`. -/
private theorem coeFn_inclusionLp_sub_mulCLM_sobolevBackgroundDefect (hm : 0 < P.natDegree)
    (hs : 1 < s) (x : H^{s}(ℂ)) :
    ⇑(inclusionLp (by linarith)
        (x - mulCLM (finrank_real_complex_lt_two_mul hs)
          (sobolevBackgroundDefect hm (by linarith)) x))
      =ᵐ[(volume : Measure ℂ)]
      fun z ↦ (backgroundWeight (P.eval ·) z : ℂ) * inclusionLp (by linarith) x z := by
  have h0 : (0 : ℝ) ≤ s := by linarith
  have hφx := coeFn_toLp_inclusion_mulCLM (finrank_real_complex_lt_two_mul hs) h0
    (sobolevBackgroundDefect hm h0) x
  simp only [toLp_inclusion] at hφx
  filter_upwards [coeFn_inclusionLp_sub_ae_eq h0 EventuallyEq.rfl hφx,
    coeFn_inclusionLp_sobolevBackgroundDefect hm h0] with z h₁ h₂
  rw [h₁, h₂]
  have hN : (1 + (‖P.eval z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity :
      (1 + ‖P.eval z‖ ^ 2 : ℝ) ≠ 0)
  simp only [backgroundWeight_def]
  push_cast
  field_simp
  ring

/-- **The reduced vortex equation on the Sobolev scale.** For a polynomial `P` of positive degree
and `s > 1`, the map `N : H^(s+2)(ℂ) → H^s(ℂ)`,

`N(w) = -Δw + h (exp (2w) - 1) / 8 + k`,

with `h = ‖P‖² / (1 + ‖P‖²)` and `k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`. The `L²` function
of `N(w)` is the residual of the reduced equation
`Δw = (h exp (2w) - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`
(`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationMap`), so a zero of `N` is an
almost-everywhere, possibly complex-valued, solution, and the element of `H^(s+2)(ℂ)` of a
classical real square-integrable solution is a zero
(`TauCeti.Vortex.reducedEquationMap_eq_zero_of_laplacian_eq`). Here `h (exp (2w) - 1)` is
computed as `(1 - (1 - h)) (exp (2w) - 1)`, since `1 - h`, unlike `h`, lies in `H^s(ℂ)`. -/
def reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) : H^{s}(ℂ) :=
  -laplacianCLM s w + (8⁻¹ : ℂ) • (ContinuousLinearMap.id ℂ H^{s}(ℂ) -
      mulCLM (finrank_real_complex_lt_two_mul hs) (sobolevBackgroundDefect hm (by linarith)))
    (expSubOne (finrank_real_complex_lt_two_mul hs) ((2 : ℂ) • inclusion (by linarith) w)) +
    sobolevBackgroundSource hm (by linarith)

/-- **The linearized reduced vortex equation.** The derivative of
`TauCeti.Vortex.reducedEquationMap` at `w`, the operator `v ↦ -Δv + h exp (2w) v / 4`
(`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationDeriv`), computed as
`-Δv + (1 - (1 - h)) (1 + (exp (2w) - 1)) v / 4`. -/
def reducedEquationDeriv (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) :=
  -laplacianCLM s + (4⁻¹ : ℂ) • ((ContinuousLinearMap.id ℂ H^{s}(ℂ) -
      mulCLM (finrank_real_complex_lt_two_mul hs) (sobolevBackgroundDefect hm (by linarith))) ∘L
    (ContinuousLinearMap.id ℂ H^{s}(ℂ) + mulCLM (finrank_real_complex_lt_two_mul hs)
      (expSubOne (finrank_real_complex_lt_two_mul hs) ((2 : ℂ) • inclusion (by linarith) w))) ∘L
    inclusion (by linarith))

/-- **The derivative of the reduced vortex equation**: at `w`, the derivative of
`TauCeti.Vortex.reducedEquationMap` is `TauCeti.Vortex.reducedEquationDeriv`,
`v ↦ -Δv + h exp (2w) v / 4`. -/
theorem hasFDerivAt_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    HasFDerivAt (reducedEquationMap hm hs) (reducedEquationDeriv hm hs w) w := by
  have hs' := finrank_real_complex_lt_two_mul hs
  set ι : H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) := inclusion (by linarith)
  set A : H^{s}(ℂ) →L[ℂ] H^{s}(ℂ) := ContinuousLinearMap.id ℂ H^{s}(ℂ) -
    mulCLM hs' (sobolevBackgroundDefect hm (by linarith))
  have h₁ : HasFDerivAt ((2 : ℂ) • ⇑ι) ((2 : ℂ) • ι) w := ι.hasFDerivAt.const_smul _
  have h₂ := (A.hasFDerivAt.comp w ((hasFDerivAt_expSubOne hs' _).comp w h₁)).const_smul (8⁻¹ : ℂ)
  have h₃ := ((laplacianCLM s).hasFDerivAt.neg.add h₂).add_const
    (sobolevBackgroundSource hm (by linarith : (0 : ℝ) ≤ s))
  refine h₃.congr_fderiv ?_
  ext v
  simp only [reducedEquationDeriv, _root_.add_apply, _root_.neg_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul, A, ι]
  norm_num

/-- The derivative of `TauCeti.Vortex.reducedEquationMap` at `w` is
`TauCeti.Vortex.reducedEquationDeriv`. -/
theorem fderiv_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    fderiv ℂ (reducedEquationMap hm hs) w = reducedEquationDeriv hm hs w :=
  (hasFDerivAt_reducedEquationMap hm hs w).fderiv

/-- **The reduced vortex equation is a smooth map** `H^(s+2)(ℂ) → H^s(ℂ)`, `s > 1`: it is `C^∞`
over `ℂ`. -/
theorem contDiff_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) :
    ContDiff ℂ ∞ (reducedEquationMap hm hs) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  exact ((laplacianCLM s).contDiff.neg.add
    (((ContinuousLinearMap.id ℂ H^{s}(ℂ) - mulCLM hs' (sobolevBackgroundDefect hm
      (by linarith))).contDiff.comp ((contDiff_expSubOne hs').comp
        ((inclusion (by linarith)).contDiff.const_smul (2 : ℂ)))).const_smul _)).add
    contDiff_const

/-- The `L²` function of `exp (2w) - 1` in `H^s(ℂ)`, for `w ∈ H^(s+2)(ℂ)`. -/
private theorem coeFn_inclusionLp_expSubOne_two_smul (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    ⇑(inclusionLp (by linarith)
        (expSubOne (finrank_real_complex_lt_two_mul hs) ((2 : ℂ) • inclusion (by linarith) w)))
      =ᵐ[(volume : Measure ℂ)] fun z ↦ Complex.exp (2 * inclusionLp (by linarith) w z) - 1 := by
  have h0 : (0 : ℝ) ≤ s := by linarith
  have hι : s ≤ s + 2 := by linarith
  have he := coeFn_toLp_inclusion_expSubOne (finrank_real_complex_lt_two_mul hs) h0
    ((2 : ℂ) • inclusion hι w)
  simp only [toLp_inclusion] at he
  filter_upwards [he, coeFn_inclusionLp_smul_ae_eq h0 (2 : ℂ) (u := inclusion hι w)
    EventuallyEq.rfl] with z h₁ h₂
  rw [h₁, h₂, smul_eq_mul, inclusionLp_inclusion]

/-- The `L²` function of `TauCeti.Vortex.reducedEquationMap`: for `w ∈ H^(s+2)(ℂ)`, with `L²`
function `w(z)`, the `L²` function of `N(w)` is `-Δw + h (exp (2w) - 1) / 8 + k`, where
`h = TauCeti.Vortex.backgroundWeight (P.eval ·)` and
`k = TauCeti.Vortex.backgroundSource (P.eval ·)`. For a real `w` this is
`-Δw + TauCeti.Vortex.reducedSource P w`. -/
theorem coeFn_inclusionLp_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s)
    (w : H^{s + 2}(ℂ)) :
    ⇑(inclusionLp (by linarith) (reducedEquationMap hm hs w)) =ᵐ[(volume : Measure ℂ)] fun z ↦
      -inclusionLp (by linarith) (laplacianCLM s w) z +
        (backgroundWeight (P.eval ·) z : ℂ) *
          (Complex.exp (2 * inclusionLp (by linarith) w z) - 1) / 8 +
        (backgroundSource (P.eval ·) z : ℂ) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have h0 : (0 : ℝ) ≤ s := by linarith
  have he := coeFn_inclusionLp_expSubOne_two_smul hs w
  set e := expSubOne hs' ((2 : ℂ) • inclusion (by linarith) w)
  have hneg : ⇑(inclusionLp h0 (-laplacianCLM s w)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ -inclusionLp h0 (laplacianCLM s w) z := by
    rw [map_neg]
    exact Lp.coeFn_neg _
  have hN := coeFn_inclusionLp_add_ae_eq h0 (coeFn_inclusionLp_add_ae_eq h0 hneg
    (coeFn_inclusionLp_smul_ae_eq h0 8⁻¹
      (coeFn_inclusionLp_sub_mulCLM_sobolevBackgroundDefect hm hs e)))
    (coeFn_inclusionLp_sobolevBackgroundSource hm h0)
  filter_upwards [hN, he] with z h₁ h₂
  rw [reducedEquationMap]
  simp only [_root_.sub_apply, ContinuousLinearMap.id_apply]
  rw [h₁, h₂, smul_eq_mul]
  ring

/-- The `L²` function of `TauCeti.Vortex.reducedEquationDeriv`: for `w, v ∈ H^(s+2)(ℂ)`, with `L²`
functions `w(z)` and `v(z)`, the derivative `DN(w) v` has `L²` function `-Δv + h exp (2w) v / 4`,
where `h = TauCeti.Vortex.backgroundWeight (P.eval ·)`. -/
theorem coeFn_inclusionLp_reducedEquationDeriv (hm : 0 < P.natDegree) (hs : 1 < s)
    (w v : H^{s + 2}(ℂ)) :
    ⇑(inclusionLp (by linarith) (reducedEquationDeriv hm hs w v)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ -inclusionLp (by linarith) (laplacianCLM s v) z +
        (backgroundWeight (P.eval ·) z : ℂ) * Complex.exp (2 * inclusionLp (by linarith) w z) *
          inclusionLp (by linarith) v z / 4 := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have h0 : (0 : ℝ) ≤ s := by linarith
  have he := coeFn_inclusionLp_expSubOne_two_smul hs w
  set ι : H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) := inclusion (by linarith)
  set e := expSubOne hs' ((2 : ℂ) • ι w)
  set X := ι v + mulCLM hs' e (ι v)
  -- The `L²` function of `X = (1 + (exp (2w) - 1)) v` is `exp (2w) v`.
  have hX : ⇑(inclusionLp h0 X) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ Complex.exp (2 * inclusionLp (by linarith) w z) * inclusionLp (by linarith) v z := by
    have heι := coeFn_toLp_inclusion_mulCLM hs' h0 e (ι v)
    simp only [toLp_inclusion] at heι
    filter_upwards [coeFn_inclusionLp_add_ae_eq h0 EventuallyEq.rfl heι, he] with z h₁ h₂
    rw [h₁, h₂, inclusionLp_inclusion]
    ring
  have hD : reducedEquationDeriv hm hs w v =
      -laplacianCLM s v + (4⁻¹ : ℂ) • (X - mulCLM hs' (sobolevBackgroundDefect hm h0) X) := by
    simp only [reducedEquationDeriv, _root_.add_apply, _root_.neg_apply, _root_.smul_apply,
      _root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, X, e, ι]
  have hneg : ⇑(inclusionLp h0 (-laplacianCLM s v)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ -inclusionLp h0 (laplacianCLM s v) z := by
    rw [map_neg]
    exact Lp.coeFn_neg _
  rw [hD]
  filter_upwards [coeFn_inclusionLp_add_ae_eq h0 hneg (coeFn_inclusionLp_smul_ae_eq h0 4⁻¹
    (coeFn_inclusionLp_sub_mulCLM_sobolevBackgroundDefect hm hs X)), hX] with z h₁ h₂
  rw [h₁, h₂, smul_eq_mul]
  ring

/-- **Solutions of the reduced equation are zeros of `TauCeti.Vortex.reducedEquationMap`.** Let
`w` be a real `C²` solution of the reduced equation `Δw = TauCeti.Vortex.reducedSource P w`
whose class `W` lies in `H^(s+2)(ℂ)`. Then `N(W) = 0`. -/
theorem reducedEquationMap_eq_zero_of_laplacian_eq (hm : 0 < P.natDegree) (hs : 1 < s)
    {w : ℂ → ℝ} (hw : ContDiff ℝ 2 w) (hΔ : ∀ z, Δ w z = reducedSource P w z)
    {W : H^{s + 2}(ℂ)}
    (hW : ⇑(inclusionLp (by linarith) W) =ᵐ[(volume : Measure ℂ)] fun z ↦ (w z : ℂ)) :
    reducedEquationMap hm hs W = 0 := by
  have h0 : (0 : ℝ) ≤ s := by linarith
  have hN := coeFn_inclusionLp_reducedEquationMap hm hs W
  -- The source is square integrable, as the `L²` function of `N(W) + ΔW`.
  have hsrc : MemLp (fun z ↦ (reducedSource P w z : ℂ)) 2 volume := by
    refine (Lp.memLp (inclusionLp h0 (reducedEquationMap hm hs W + laplacianCLM s W))).ae_eq ?_
    filter_upwards [coeFn_inclusionLp_add_ae_eq h0 hN EventuallyEq.rfl, hW] with z h₁ h₂
    rw [h₁, h₂, reducedSource_def]
    push_cast
    ring
  have hΔ2 : MemLp (Δ w) 2 volume := by
    have h := hsrc.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at h
    exact h.ae_eq (Eventually.of_forall fun z ↦ (hΔ z).symm)
  have hL := coeFn_inclusionLp_laplacianCLM_ae_eq h0 hw hΔ2 hW
  refine inclusionLp_injective h0 (Lp.ext ?_)
  rw [map_zero]
  filter_upwards [hN, hL, hW, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, Pi.zero_apply, hΔ z, reducedSource_def]
  push_cast
  ring

/-- **The reduced vortex equation has a zero in every `H^(s+2)(ℂ)`.** Taubes's smooth solution
`w` of the reduced equation (`TauCeti.Vortex.exists_contDiff_memLp_laplacian_eq_reduced`) has its
class `W` in `H^(s+2)(ℂ)`, and `N(W) = 0`. -/
theorem exists_reducedEquationMap_eq_zero (hm : 0 < P.natDegree) (hs : 1 < s) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ (∀ z, Δ w z = reducedSource P w z) ∧ ∃ W : H^{s + 2}(ℂ),
      ⇑(inclusionLp (by linarith) W) =ᵐ[(volume : Measure ℂ)] (fun z ↦ (w z : ℂ)) ∧
        reducedEquationMap hm hs W = 0 := by
  obtain ⟨w, hw, hw2, -, heq⟩ := exists_contDiff_memLp_laplacian_eq_reduced hm
  have hΔ (z : ℂ) : Δ w z = reducedSource P w z := by
    rw [heq z, reducedSource_def, backgroundSource_def]
    ring
  have hmem := mem_realSobolevFunctions_of_laplacian_eq_reduced hm (hw.of_le (by simp)) hw2 heq
    (s + 2)
  have hW := coeFn_inclusionLp_ofRealSobolevFunction (by linarith) hmem
  exact ⟨w, hw, hΔ, _, hW,
    reducedEquationMap_eq_zero_of_laplacian_eq hm hs (hw.of_le (by simp)) hΔ hW⟩

end TauCeti.Vortex
