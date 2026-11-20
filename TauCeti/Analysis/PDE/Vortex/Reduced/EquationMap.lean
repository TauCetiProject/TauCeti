/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
public import TauCeti.Analysis.Sobolev.BesselPotential.Exp
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
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
(`Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions`), and
`h (exp (2w) - 1) = (exp (2w) - 1) - (1 - h)(exp (2w) - 1)` is built from the smooth exponential
`BesselPotentialSpace.expSubOne` and the product `BesselPotentialSpace.mulCLM` of `H^s(ℂ)`.

The map is `C^∞`, indeed `C^∞` over `ℂ` (`TauCeti.Vortex.contDiff_reducedEquationMap`), and its
derivative at `w` is the Schrödinger operator

`DN(w) v = -Δv + h exp (2w) v / 4`

(`TauCeti.Vortex.hasFDerivAt_reducedEquationMap`, `TauCeti.Vortex.reducedEquationDeriv`,
`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationDeriv`). The `L²` function of `N(w)` is
`-Δw + h (exp (2w) - 1) / 8 + k` (`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationMap`), so the
zeros of `N` are the solutions of the reduced equation: the element of `H^(s+2)(ℂ)` of a classical
square-integrable solution is a zero of `N`
(`TauCeti.Vortex.reducedEquationMap_eq_zero_of_laplacian_eq`), and Taubes's solution gives one
(`TauCeti.Vortex.exists_reducedEquationMap_eq_zero`).

This is the nonlinear operator to which the implicit function theorem applies, to make the
solution of the reduced equation depend smoothly on the divisor.

## Main definitions

* `TauCeti.Vortex.sobolevBackgroundDefect`: the coefficient `1 - h = (1 + ‖P‖²)⁻¹` in `H^s(ℂ)`.
* `TauCeti.Vortex.reducedEquationMap`: the map `N : H^(s+2)(ℂ) → H^s(ℂ)`.
* `TauCeti.Vortex.reducedEquationDeriv`: its derivative `-Δ + h exp (2w) / 4` at `w`.

## Main results

* `TauCeti.Vortex.hasFDerivAt_reducedEquationMap`: the derivative of `N`.
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

open BesselPotentialSpace TemperedDistribution MeasureTheory Module Filter
open scoped BesselPotentialSpace Laplacian ContDiff

namespace TauCeti.Vortex

variable {P : Polynomial ℂ} {s : ℝ}

/-- `H^s(ℂ)` is an algebra for `s > 1`. -/
private theorem finrank_lt_two_mul (hs : 1 < s) : (finrank ℝ ℂ : ℝ) < 2 * s := by
  rw [Complex.finrank_real_complex]
  push_cast
  linarith

/-- The coefficient `1 - h = (1 + ‖P‖²)⁻¹` lies in every real Bessel-potential space. -/
private theorem inv_one_add_norm_eval_sq_mem (hm : 0 < P.natDegree) (s : ℝ) :
    (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) ∈ realSobolevFunctions ℂ s 2 :=
  realSobolevFunctions_mono (by norm_num) ENNReal.ofNat_ne_top (Nat.le_ceil s)
    (Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions hm ⌈s⌉₊)

/-- The source `k = (h - 1) / 8 + g` lies in every real Bessel-potential space. -/
private theorem backgroundSource_mem (hm : 0 < P.natDegree) (s : ℝ) :
    backgroundSource (P.eval ·) ∈ realSobolevFunctions ℂ s 2 := by
  have hk : backgroundSource (P.eval ·) = (-(8 : ℝ)⁻¹) • (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) +
      (2 : ℝ) • fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
    ext z
    have hN : (1 + ‖P.eval z‖ ^ 2) ≠ 0 := by positivity
    simp only [backgroundSource_def, backgroundWeight_def, Polynomial.deriv, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hk]
  exact add_mem (Submodule.smul_mem _ _ (inv_one_add_norm_eval_sq_mem hm s))
    (Submodule.smul_mem _ _ (realSobolevFunctions_mono (by norm_num) ENNReal.ofNat_ne_top
      (Nat.le_ceil s)
      (Polynomial.norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions
        P ⌈s⌉₊)))

/-- The coefficient `1 - h = (1 + ‖P‖²)⁻¹` of the reduced vortex equation, with
`h = TauCeti.Vortex.backgroundWeight (P.eval ·)`, as an element of `H^s(ℂ)`. -/
def sobolevBackgroundDefect (hm : 0 < P.natDegree) (hs : 0 ≤ s) : H^{s}(ℂ) :=
  ofRealSobolevFunction hs (inv_one_add_norm_eval_sq_mem hm s)

/-- The `L²` function of `sobolevBackgroundDefect hm hs` is `(1 + ‖P‖²)⁻¹`. -/
theorem coeFn_inclusionLp_sobolevBackgroundDefect (hm : 0 < P.natDegree) (hs : 0 ≤ s) :
    ⇑(inclusionLp hs (sobolevBackgroundDefect hm hs)) =ᵐ[(volume : Measure ℂ)]
      fun z ↦ (((1 + ‖P.eval z‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
  coeFn_inclusionLp_ofRealSobolevFunction hs _

/-- The source `k = (h - 1) / 8 + g` of the reduced vortex equation as an element of `H^s(ℂ)`. -/
private def sobolevBackgroundSource (hm : 0 < P.natDegree) (hs : 0 ≤ s) : H^{s}(ℂ) :=
  ofRealSobolevFunction hs (backgroundSource_mem hm s)

/-- **The reduced vortex equation on the Sobolev scale.** For a polynomial `P` of positive degree
and `s > 1`, the map `N : H^(s+2)(ℂ) → H^s(ℂ)`,

`N(w) = -Δw + h (exp (2w) - 1) / 8 + k`,

with `h = ‖P‖² / (1 + ‖P‖²)` and `k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`. Its zeros are the
solutions of the reduced equation `Δw = (h exp (2w) - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`
(`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationMap`). Here `h (exp (2w) - 1)` is computed as
`(1 - (1 - h)) (exp (2w) - 1)`, since `1 - h`, unlike `h`, lies in `H^s(ℂ)`. -/
def reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) : H^{s}(ℂ) :=
  -laplacianCLM s w + (8⁻¹ : ℂ) • (ContinuousLinearMap.id ℂ H^{s}(ℂ) -
      mulCLM (finrank_lt_two_mul hs) (sobolevBackgroundDefect hm (by linarith)))
    (expSubOne (finrank_lt_two_mul hs) ((2 : ℂ) • inclusion (by linarith) w)) +
    sobolevBackgroundSource hm (by linarith)

/-- **The linearized reduced vortex equation.** The derivative of
`TauCeti.Vortex.reducedEquationMap` at `w`, the operator `v ↦ -Δv + h exp (2w) v / 4`
(`TauCeti.Vortex.coeFn_inclusionLp_reducedEquationDeriv`), computed as
`-Δv + (1 - (1 - h)) (1 + (exp (2w) - 1)) v / 4`. -/
def reducedEquationDeriv (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) :=
  -laplacianCLM s + (4⁻¹ : ℂ) • ((ContinuousLinearMap.id ℂ H^{s}(ℂ) -
      mulCLM (finrank_lt_two_mul hs) (sobolevBackgroundDefect hm (by linarith))) ∘L
    (ContinuousLinearMap.id ℂ H^{s}(ℂ) + mulCLM (finrank_lt_two_mul hs)
      (expSubOne (finrank_lt_two_mul hs) ((2 : ℂ) • inclusion (by linarith) w))) ∘L
    inclusion (by linarith))

/-- **The derivative of the reduced vortex equation**: at `w`, the derivative of
`TauCeti.Vortex.reducedEquationMap` is `TauCeti.Vortex.reducedEquationDeriv`,
`v ↦ -Δv + h exp (2w) v / 4`. -/
theorem hasFDerivAt_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) (w : H^{s + 2}(ℂ)) :
    HasFDerivAt (reducedEquationMap hm hs) (reducedEquationDeriv hm hs w) w := by
  have hs' := finrank_lt_two_mul hs
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

/-- **The reduced vortex equation is a smooth map** `H^(s+2)(ℂ) → H^s(ℂ)`, `s > 1`: it is `C^∞`
over `ℂ`. -/
theorem contDiff_reducedEquationMap (hm : 0 < P.natDegree) (hs : 1 < s) :
    ContDiff ℂ ∞ (reducedEquationMap hm hs) := by
  have hs' := finrank_lt_two_mul hs
  exact ((laplacianCLM s).contDiff.neg.add
    (((ContinuousLinearMap.id ℂ H^{s}(ℂ) - mulCLM hs' (sobolevBackgroundDefect hm
      (by linarith))).contDiff.comp ((contDiff_expSubOne hs').comp
        ((inclusion (by linarith)).contDiff.const_smul (2 : ℂ)))).const_smul _)).add
    contDiff_const

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
  have hs' := finrank_lt_two_mul hs
  have h0 : (0 : ℝ) ≤ s := by linarith
  set ι : H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) := inclusion (by linarith)
  set φ := sobolevBackgroundDefect hm h0
  set e := expSubOne hs' ((2 : ℂ) • ι w)
  have hι : inclusionLp h0 (ι w) = inclusionLp (by linarith) w := inclusionLp_inclusion _ h0 w
  have he := coeFn_toLp_inclusion_expSubOne hs' h0 ((2 : ℂ) • ι w)
  have hφe := coeFn_toLp_inclusion_mulCLM hs' h0 φ e
  simp only [toLp_inclusion] at he hφe
  rw [reducedEquationMap]
  simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, map_add, map_neg,
    map_smul, map_sub]
  filter_upwards [Lp.coeFn_add (-inclusionLp h0 (laplacianCLM s w) + (8⁻¹ : ℂ) •
      (inclusionLp h0 e - inclusionLp h0 (mulCLM hs' φ e)))
      (inclusionLp h0 (sobolevBackgroundSource hm h0)),
    Lp.coeFn_add (-inclusionLp h0 (laplacianCLM s w))
      ((8⁻¹ : ℂ) • (inclusionLp h0 e - inclusionLp h0 (mulCLM hs' φ e))),
    Lp.coeFn_neg (inclusionLp h0 (laplacianCLM s w)),
    Lp.coeFn_smul (8⁻¹ : ℂ) (inclusionLp h0 e - inclusionLp h0 (mulCLM hs' φ e)),
    Lp.coeFn_sub (inclusionLp h0 e) (inclusionLp h0 (mulCLM hs' φ e)), he, hφe,
    Lp.coeFn_smul (2 : ℂ) (inclusionLp h0 (ι w)), coeFn_inclusionLp_sobolevBackgroundDefect hm h0,
    coeFn_inclusionLp_ofRealSobolevFunction h0 (backgroundSource_mem hm s)]
    with z h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  simp only [map_smul] at h₆ h₈
  rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, Pi.neg_apply, h₄, Pi.smul_apply, h₅,
    Pi.sub_apply, h₇, h₆, h₈, Pi.smul_apply, hι, h₉]
  rw [show sobolevBackgroundSource hm h0 = ofRealSobolevFunction h0 (backgroundSource_mem hm s)
    from rfl, h₁₀]
  have hN : (1 + (‖P.eval z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity :
      (1 + ‖P.eval z‖ ^ 2 : ℝ) ≠ 0)
  simp only [backgroundWeight_def, smul_eq_mul]
  push_cast
  field_simp
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
  have hs' := finrank_lt_two_mul hs
  have h0 : (0 : ℝ) ≤ s := by linarith
  set ι : H^{s + 2}(ℂ) →L[ℂ] H^{s}(ℂ) := inclusion (by linarith)
  set φ := sobolevBackgroundDefect hm h0
  set e := expSubOne hs' ((2 : ℂ) • ι w)
  set X := ι v + mulCLM hs' e (ι v)
  have hι (u : H^{s + 2}(ℂ)) : inclusionLp h0 (ι u) = inclusionLp (by linarith) u :=
    inclusionLp_inclusion _ h0 u
  have hX : inclusionLp h0 X = inclusionLp h0 (ι v) + inclusionLp h0 (mulCLM hs' e (ι v)) :=
    map_add _ _ _
  have he := coeFn_toLp_inclusion_expSubOne hs' h0 ((2 : ℂ) • ι w)
  have hφX := coeFn_toLp_inclusion_mulCLM hs' h0 φ X
  have heι := coeFn_toLp_inclusion_mulCLM hs' h0 e (ι v)
  simp only [toLp_inclusion] at he hφX heι
  have hD : reducedEquationDeriv hm hs w v =
      -laplacianCLM s v + (4⁻¹ : ℂ) • (X - mulCLM hs' φ X) := rfl
  rw [hD]
  simp only [map_add, map_neg, map_smul, map_sub]
  filter_upwards [Lp.coeFn_add (-inclusionLp h0 (laplacianCLM s v))
      ((4⁻¹ : ℂ) • (inclusionLp h0 X - inclusionLp h0 (mulCLM hs' φ X))),
    Lp.coeFn_neg (inclusionLp h0 (laplacianCLM s v)),
    Lp.coeFn_smul (4⁻¹ : ℂ) (inclusionLp h0 X - inclusionLp h0 (mulCLM hs' φ X)),
    Lp.coeFn_sub (inclusionLp h0 X) (inclusionLp h0 (mulCLM hs' φ X)), hφX,
    Lp.coeFn_add (inclusionLp h0 (ι v)) (inclusionLp h0 (mulCLM hs' e (ι v))), heι, he,
    Lp.coeFn_smul (2 : ℂ) (inclusionLp h0 (ι w)), coeFn_inclusionLp_sobolevBackgroundDefect hm h0]
    with z h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  simp only [map_smul] at h₈ h₉
  rw [h₁, Pi.add_apply, h₂, Pi.neg_apply, h₃, Pi.smul_apply, h₄, Pi.sub_apply, h₅, h₁₀, hX, h₆,
    Pi.add_apply, h₇, h₈, h₉, Pi.smul_apply, hι, hι]
  have hN : (1 + (‖P.eval z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity :
      (1 + ‖P.eval z‖ ^ 2 : ℝ) ≠ 0)
  simp only [backgroundWeight_def, smul_eq_mul]
  push_cast
  field_simp
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
    refine (Lp.memLp (inclusionLp h0 (reducedEquationMap hm hs W) +
      inclusionLp h0 (laplacianCLM s W))).ae_eq ?_
    filter_upwards [Lp.coeFn_add (inclusionLp h0 (reducedEquationMap hm hs W))
      (inclusionLp h0 (laplacianCLM s W)), hN, hW] with z h₁ h₂ h₃
    rw [h₁, Pi.add_apply, h₂, h₃, reducedSource_def]
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
