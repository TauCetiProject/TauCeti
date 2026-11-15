/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Generating functions of area-preserving maps of the strip

Let `F = (X, Y)` be a map of the plane `ℝ × ℝ`, with coordinates `(x, y)`, which is `C²` near
the region of interest, for instance a lift of an area-preserving diffeomorphism of the annulus
`(ℝ / ℤ) × [0, 1]` to a neighbourhood of the strip `ℝ × [0, 1]`. This file constructs its
generating function in the mixed coordinates `(x, y)`,

`S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt`

(`TauCeti.stripGeneratingFunction`), with the convention `y = -∂₁ S`, `Y = ∂₂ S` in the
coordinates `(x, X)`.

* `S` vanishes on the lower boundary line `y = 0`
  (`TauCeti.stripGeneratingFunction_mk_zero`). It is invariant under a translation
  `(x, y) ↦ (x + a, y)`, such as the deck translation `a = 1`, when `F` commutes with it
  (`TauCeti.stripGeneratingFunction_add_fst`); it suffices that `F` commutes with the translation
  near every interior point of the segment from `(x, 0)` to `(x, y)`
  (`TauCeti.stripGeneratingFunction_add_fst_of_eventuallyEq`).
* `S` is `C^n` at `(x, y)` when `F` is `C^(n + 1)` at every point of the segment from `(x, 0)` to
  `(x, y)` (`TauCeti.contDiffAt_stripGeneratingFunction`), so `S` is `C^n` when `F` is `C^(n + 1)`
  (`TauCeti.contDiff_stripGeneratingFunction`).
* If `F` is `C²` at every point of that segment, maps `(x, 0)` into the lower boundary line,
  `Y(x, 0) = 0`, and preserves the area form `dx ∧ dy` at the interior points of the segment, then
  `dS = Y dX - y dx` at `(x, y)`, that is `∂ₓ S = Y ∂ₓ X - y` and `∂_y S = Y ∂_y X`
  (`TauCeti.hasFDerivAt_stripGeneratingFunction`). The proof differentiates under the integral:
  the `x`-derivative of the integrand differs from the `t`-derivative of `Y ∂ₓ X` by minus the
  Jacobian determinant, which is `1`.
* Consequently, near a point where the twist `∂_y X` does not vanish, the map
  `(x, y) ↦ (x, X(x, y))` is locally invertible, and any function `S'` of `(x, X)` which
  agrees with `S` through it satisfies the generating equations
  `∂₁ S'(x, X) = -y`, `∂₂ S'(x, X) = Y(x, y)` at `X = X(x, y)`
  (`TauCeti.hasFDerivAt_of_eventuallyEq_stripGeneratingFunction`).

The normalization `S = 0` on the lower boundary fixes the additive constant of the generating
function. For the affine shear `(x, y) ↦ (x + a + c y, y)` the generating function is `c y² / 2`
(`TauCeti.stripGeneratingFunction_affineShear`). When the twist `c` is nonzero, this is
`(X - x - a)² / (2c)` in the coordinates `(x, X)`, and its generating equations read
`-∂₁ S' = y = ∂₂ S'` (`TauCeti.hasFDerivAt_affineShear_generatingFunction`).

These are the generating functions of the area-preserving twist factors in the
generating-function proof of the Poincaré–Birkhoff theorem.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 4 (generating functions).
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology Interval

namespace TauCeti

/-- The **generating function** of a map `F = (X, Y)` of the plane, in the mixed coordinates
`(x, y)`: `S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt`. When `F` is `C²`, preserves area and maps the
line `y = 0` into itself, `dS = Y dX - y dx` (`TauCeti.hasFDerivAt_stripGeneratingFunction`). -/
def stripGeneratingFunction (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..p.2, (F (p.1, t)).2 * (fderiv ℝ F (p.1, t) (0, 1)).1

variable {F : ℝ × ℝ → ℝ × ℝ}

theorem stripGeneratingFunction_def (p : ℝ × ℝ) :
    stripGeneratingFunction F p =
      ∫ t in (0 : ℝ)..p.2, (F (p.1, t)).2 * (fderiv ℝ F (p.1, t) (0, 1)).1 :=
  (rfl)

/-- The generating function vanishes on the lower boundary line `y = 0`. -/
@[simp]
theorem stripGeneratingFunction_mk_zero (x : ℝ) : stripGeneratingFunction F (x, 0) = 0 := by
  simp [stripGeneratingFunction_def]

/-- If `F` commutes with the translation `(x, y) ↦ (x + a, y)` near every interior point of the
segment from `(p.1, 0)` to `p`, its generating function takes the same value at `p` and at
`p + (a, 0)`. -/
theorem stripGeneratingFunction_add_fst_of_eventuallyEq {a : ℝ} {p : ℝ × ℝ}
    (hF : ∀ t ∈ uIoo 0 p.2, (fun q ↦ F (q + (a, 0))) =ᶠ[𝓝 (p.1, t)] fun q ↦ F q + (a, 0)) :
    stripGeneratingFunction F (p + (a, 0)) = stripGeneratingFunction F p := by
  simp only [stripGeneratingFunction_def, Prod.fst_add, Prod.snd_add, add_zero]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hq : ((p.1 + a, t) : ℝ × ℝ) = (p.1, t) + (a, 0) := by simp
  -- Commuting with the translation near `(p.1, t)` makes the derivative of `F` invariant under it.
  have hD : fderiv ℝ F ((p.1, t) + (a, 0)) = fderiv ℝ F (p.1, t) := by
    simpa only [fderiv_comp_add_right, fderiv_add_const] using (hF t ht).fderiv_eq (𝕜 := ℝ)
  have hv : F ((p.1, t) + (a, 0)) = F (p.1, t) + (a, 0) := (hF t ht).self_of_nhds
  simp only [hq, hv, hD, Prod.snd_add, add_zero]

/-- If `F` commutes with the translation `(x, y) ↦ (x + a, y)`, its generating function is
invariant under that translation. -/
theorem stripGeneratingFunction_add_fst {a : ℝ} (hF : ∀ q, F (q + (a, 0)) = F q + (a, 0))
    (p : ℝ × ℝ) : stripGeneratingFunction F (p + (a, 0)) = stripGeneratingFunction F p :=
  stripGeneratingFunction_add_fst_of_eventuallyEq fun _ _ ↦ .of_forall hF

/-! ### Regularity -/

variable {U : Set (ℝ × ℝ)}

/-- If `F` is `C^k`, for `k ≠ ∞`, at every point of the segment from `(x, 0)` to `(x, y)`,
then it is `C^k` on an open set containing that segment. -/
private theorem exists_isOpen_contDiffOn_segment {k : WithTop ℕ∞} (hk : k ≠ ∞) {x y : ℝ}
    (hF : ∀ t ∈ [[0, y]], ContDiffAt ℝ k F (x, t)) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ContDiffOn ℝ k F U ∧ {x} ×ˢ [[0, y]] ⊆ U := by
  obtain ⟨U, hU, hsU, hFU⟩ := exists_isOpen_superset_contDiffOn hk
    (s := {x} ×ˢ [[0, y]]) fun q ⟨hx, ht⟩ ↦ (mem_singleton_iff.1 hx) ▸ hF q.2 ht
  exact ⟨U, hU, hFU, hsU⟩

/-- The integrand `Y ∂_u X` along a direction `u` of a map which is `C^(n + 1)` on an open set
is `C^n` there. -/
private theorem contDiffOn_snd_mul_fst_fderiv {n : ℕ∞} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (n + 1) F U) (u : ℝ × ℝ) :
    ContDiffOn ℝ n (fun q ↦ (F q).2 * (fderiv ℝ F q u).1) U :=
  (contDiff_snd.comp_contDiffOn (hF.of_le le_self_add)).mul
    (contDiff_fst.comp_contDiffOn ((hF.fderiv_of_isOpen hU le_rfl).clm_apply contDiffOn_const))

/-- The generating function is `C^n` at `p` when `F` is `C^(n + 1)` at every point of the
segment from `(p.1, 0)` to `p`. -/
theorem contDiffAt_stripGeneratingFunction {n : ℕ∞} {p : ℝ × ℝ}
    (hF : ∀ t ∈ [[0, p.2]], ContDiffAt ℝ (n + 1) F (p.1, t)) :
    ContDiffAt ℝ n (stripGeneratingFunction F) p := by
  -- `C^∞` is `C^m` for every finite `m`, so it suffices to treat finite `n`.
  suffices H : ∀ m : ℕ∞, m ≠ ⊤ → (∀ t ∈ [[0, p.2]], ContDiffAt ℝ (m + 1) F (p.1, t)) →
      ContDiffAt ℝ m (stripGeneratingFunction F) p by
    rcases eq_or_ne n ⊤ with rfl | hn
    · exact contDiffAt_infty.2 fun m ↦
        H m (ENat.natCast_ne_top m) fun t ht ↦ (hF t ht).of_le (by simp)
    · exact H n hn hF
  intro n hn hF
  -- For finite `n`, `F` is `C^(n + 1)` on an open set `U` containing the segment.
  obtain ⟨U, hU, hFU, hp⟩ := exists_isOpen_contDiffOn_segment (by simpa using hn) hF
  set g : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1
  -- Rescale the variable interval `[0, y]` to `[0, 1]`.
  have h : stripGeneratingFunction F = fun p ↦ p.2 * ∫ s in (0 : ℝ)..1, g (p.1, p.2 * s) := by
    funext p
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t ↦ g (p.1, t)) p.2
    simpa [stripGeneratingFunction_def, g] using this.symm
  rw [h]
  -- The rescaled integrand is `C^n` on the open set `W`, which contains `{p} × [0, 1]`, hence on
  -- a product `u × [0, 1]` with `u` an open neighbourhood of `p`.
  set W : Set ((ℝ × ℝ) × ℝ) := (fun z ↦ (z.1.1, z.1.2 * z.2)) ⁻¹' U
  have hg : ContDiffOn ℝ n (fun z : (ℝ × ℝ) × ℝ ↦ g (z.1.1, z.1.2 * z.2)) W :=
    (contDiffOn_snd_mul_fst_fderiv hU hFU (0, 1)).comp (by fun_prop) fun _ hz ↦ hz
  have hpW : {p} ×ˢ [[(0 : ℝ), 1]] ⊆ W := by
    rintro ⟨q, s⟩ ⟨rfl, hs⟩
    exact hp ⟨rfl, by
      simpa only [image_const_mul_uIcc, mul_zero, mul_one] using mem_image_of_mem (q.2 * ·) hs⟩
  obtain ⟨u, v, hu, -, hpu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc (hU.preimage (by fun_prop)) hpW
  have hint := ContDiffOn.parametric_intervalIntegral (μ := MeasureTheory.volume)
    (f := fun q s ↦ g (q.1, q.2 * s)) hu (hg.mono ((prod_mono le_rfl hv).trans huv))
  exact contDiffAt_snd.mul (hint.contDiffAt (hu.mem_nhds (hpu rfl)))

/-- The generating function of a `C^(n + 1)` map is `C^n`. -/
theorem contDiff_stripGeneratingFunction {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (stripGeneratingFunction F) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_stripGeneratingFunction fun _ _ ↦ hF.contDiffAt

/-! ### The derivative of the generating function -/

/-- The derivative of `q ↦ Y(q) ∂_u X(q)` at `q` in the direction `v` is
`∂_v Y ∂_u X + Y ∂_v ∂_u X`. -/
private theorem hasFDerivAt_snd_mul_fst_fderiv {q : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F q)
    (u : ℝ × ℝ) :
    HasFDerivAt (fun q ↦ (F q).2 * (fderiv ℝ F q u).1)
      ((F q).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((fderiv ℝ (fderiv ℝ F) q).flip u) +
        (fderiv ℝ F q u).1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ F q)) q := by
  have hF1 : HasFDerivAt F (fderiv ℝ F q) q := (hF.differentiableAt two_ne_zero).hasFDerivAt
  exact (hasFDerivAt_snd.comp q hF1).mul
    (hasFDerivAt_fst.comp q (hF.hasFDerivAt_fderiv_apply le_rfl u))

/-- The `x`-derivative of the integrand `Y ∂_y X` of the generating function is the `y`-derivative
of `Y ∂ₓ X` minus the Jacobian determinant of `F`. -/
private theorem fderiv_snd_mul_fst_fderiv_eq {q : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F q) :
    fderiv ℝ (fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1) q (1, 0) =
      fderiv ℝ (fun q ↦ (F q).2 * (fderiv ℝ F q (1, 0)).1) q (0, 1) -
        (fderiv ℝ F q).det := by
  have hsymm : fderiv ℝ (fderiv ℝ F) q (1, 0) (0, 1) = fderiv ℝ (fderiv ℝ F) q (0, 1) (1, 0) :=
    hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) _ _
  rw [(hasFDerivAt_snd_mul_fst_fderiv hF (0, 1)).fderiv,
    (hasFDerivAt_snd_mul_fst_fderiv hF (1, 0)).fderiv, ContinuousLinearMap.det,
    LinearMap.det_finTwoProd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_coe, smul_eq_mul, hsymm]
  ring

/-- The partial derivative of the generating function in `x`: if `F` is `C²` on an open set
containing the segment from `(x, 0)` to `(x, y)`, maps `(x, 0)` to the line `y = 0` and preserves
area at the interior points of the segment, then `∂ₓ S(x, y) = Y(x, y) ∂ₓ X(x, y) - y`. -/
private theorem hasDerivAt_stripGeneratingFunction_fst (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    {x y : ℝ} (hp : {x} ×ˢ [[0, y]] ⊆ U) (hY : (F (x, 0)).2 = 0)
    (hdet : ∀ t ∈ uIoo 0 y, (fderiv ℝ F (x, t)).det = 1) :
    HasDerivAt (fun s ↦ stripGeneratingFunction F (s, y))
      ((F (x, y)).2 * (fderiv ℝ F (x, y) (1, 0)).1 - y) x := by
  set g : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1
  set h : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (1, 0)).1
  have hg : ContDiffOn ℝ 1 g U :=
    contDiffOn_snd_mul_fst_fderiv (n := 1) hU (hF.of_le (by norm_num)) (0, 1)
  have hh : ContDiffOn ℝ 1 h U :=
    contDiffOn_snd_mul_fst_fderiv (n := 1) hU (hF.of_le (by norm_num)) (1, 0)
  have hseg (t : ℝ) (ht : t ∈ [[0, y]]) : (x, t) ∈ U := hp ⟨rfl, ht⟩
  -- Differentiate under the integral sign.
  obtain ⟨-, hd⟩ := hasDerivAt_intervalIntegral_of_contDiffOn hU hg hp
  -- The `y`-derivatives of `h` along the segment, and their integral.
  have hcont : ContinuousOn (fun t ↦ fderiv ℝ h (x, t) (0, 1)) [[0, y]] :=
    ((hh.continuousOn_fderiv_of_isOpen hU le_rfl).comp (by fun_prop) hseg).clm_apply
      continuousOn_const
  have hderiv (t : ℝ) (ht : t ∈ [[0, y]]) :
      HasDerivAt (fun t ↦ h (x, t)) (fderiv ℝ h (x, t) (0, 1)) t :=
    hasDerivAt_slice_right ((hh.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt one_ne_zero)
  have hFTC : ∫ t in (0 : ℝ)..y, fderiv ℝ h (x, t) (0, 1) = h (x, y) - h (x, 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hdetint : ∫ t in (0 : ℝ)..y, (fderiv ℝ F (x, t)).det = y := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (1 : ℝ)) fun t ht ↦ hdet t ht]
    simp
  have hdetcont : ContinuousOn (fun t ↦ (fderiv ℝ F (x, t)).det) [[0, y]] :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      ((hF.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp (by fun_prop) hseg)
  have hval : ∫ t in (0 : ℝ)..y, fderiv ℝ g (x, t) (1, 0) =
      (F (x, y)).2 * (fderiv ℝ F (x, y) (1, 0)).1 - y := by
    have hcongr : EqOn (fun t ↦ fderiv ℝ g (x, t) (1, 0))
        (fun t ↦ fderiv ℝ h (x, t) (0, 1) - (fderiv ℝ F (x, t)).det) [[0, y]] :=
      fun t ht ↦ fderiv_snd_mul_fst_fderiv_eq (hF.contDiffAt (hU.mem_nhds (hseg t ht)))
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub
      hcont.intervalIntegrable hdetcont.intervalIntegrable, hFTC, hdetint]
    simp [h, hY]
  rw [← hval]
  exact hd

/-- **The generating function of an area-preserving map.** If `F = (X, Y)` is `C²` at every point
of the segment from `(x, 0)` to `p = (x, y)`, maps `(x, 0)` to the line `y = 0` and preserves the
area form `dx ∧ dy` at the interior points of that segment, then its generating function `S`
satisfies `dS = Y dX - y dx` at `p`: `∂ₓ S = Y ∂ₓ X - y` and `∂_y S = Y ∂_y X`. -/
theorem hasFDerivAt_stripGeneratingFunction {p : ℝ × ℝ}
    (hF : ∀ t ∈ [[0, p.2]], ContDiffAt ℝ 2 F (p.1, t)) (hY : (F (p.1, 0)).2 = 0)
    (hdet : ∀ t ∈ uIoo 0 p.2, (fderiv ℝ F (p.1, t)).det = 1) :
    HasFDerivAt (stripGeneratingFunction F)
      ((F p).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) -
        p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨x, y⟩ := p
  have hS : DifferentiableAt ℝ (stripGeneratingFunction F) (x, y) :=
    (contDiffAt_stripGeneratingFunction (n := 1) fun t ht ↦
      (hF t ht).of_le (by norm_num)).differentiableAt one_ne_zero
  -- `F` is `C²` on an open set `U` containing the segment.
  obtain ⟨U, hU, hFU, hp⟩ := exists_isOpen_contDiffOn_segment (by simp) hF
  convert hS.hasFDerivAt using 1
  -- Compare the two partial derivatives.
  have hfst : HasDerivAt (fun s ↦ stripGeneratingFunction F (s, y))
      (fderiv ℝ (stripGeneratingFunction F) (x, y) (1, 0)) x :=
    hasDerivAt_slice_left hS
  have hsnd : HasDerivAt (fun t ↦ stripGeneratingFunction F (x, t))
      (fderiv ℝ (stripGeneratingFunction F) (x, y) (0, 1)) y :=
    hasDerivAt_slice_right hS
  -- The `y`-derivative is the fundamental theorem of calculus, on the open set `V` of heights `t`
  -- with `(x, t) ∈ U`.
  have hV : IsOpen ((fun t : ℝ ↦ (x, t)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hsegV : [[0, y]] ⊆ (fun t : ℝ ↦ (x, t)) ⁻¹' U := fun t ht ↦ hp ⟨rfl, ht⟩
  have hyV : y ∈ (fun t : ℝ ↦ (x, t)) ⁻¹' U := hsegV right_mem_uIcc
  have hc : ContinuousOn (fun t ↦ (F (x, t)).2 * (fderiv ℝ F (x, t) (0, 1)).1)
      ((fun t : ℝ ↦ (x, t)) ⁻¹' U) :=
    (contDiffOn_snd_mul_fst_fderiv (n := 0) hU (hFU.of_le (by norm_num)) (0, 1)).continuousOn.comp
      (by fun_prop) fun _ ht ↦ ht
  have hsnd' : HasDerivAt (fun t ↦ stripGeneratingFunction F (x, t))
      ((F (x, y)).2 * (fderiv ℝ F (x, y) (0, 1)).1) y :=
    intervalIntegral.integral_hasDerivAt_right (hc.mono hsegV).intervalIntegrable
      (hc.stronglyMeasurableAtFilter hV y hyV) (hc.continuousAt (hV.mem_nhds hyV))
  refine ContinuousLinearMap.prod_ext (ContinuousLinearMap.ext_ring ?_)
    (ContinuousLinearMap.ext_ring ?_)
  · simpa using (hfst.unique (hasDerivAt_stripGeneratingFunction_fst hU hFU hp hY hdet)).symm
  · simpa using (hsnd.unique hsnd').symm

/-- **The generating equations.** Let `F = (X, Y)` be `C²` at every point of the segment from
`(x, 0)` to `p = (x, y)`, map `(x, 0)` to the line `y = 0`, preserve area at the interior points of
that segment, and twist at `p`: `∂_y X(p) ≠ 0`. If a function `S'` of `(x, X)` agrees near `p`
with the generating function of `F` through `(x, y) ↦ (x, X(x, y))`, then at `(x, X(p))` it has
derivative `Y(p) dX - y dx`. That is, `∂₁ S'(x, X) = -y` and `∂₂ S'(x, X) = Y`. -/
theorem hasFDerivAt_of_eventuallyEq_stripGeneratingFunction {p : ℝ × ℝ}
    (hF : ∀ t ∈ [[0, p.2]], ContDiffAt ℝ 2 F (p.1, t))
    (hY : (F (p.1, 0)).2 = 0) (hdet : ∀ t ∈ uIoo 0 p.2, (fderiv ℝ F (p.1, t)).det = 1)
    (htwist : (fderiv ℝ F p (0, 1)).1 ≠ 0) {S' : ℝ × ℝ → ℝ}
    (hS' : (fun q ↦ S' (q.1, (F q).1)) =ᶠ[𝓝 p] stripGeneratingFunction F) :
    HasFDerivAt S' ((F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ -
      p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) (p.1, (F p).1) := by
  have hFp : ContDiffAt ℝ 2 F p := hF p.2 right_mem_uIcc
  set G : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1, (F q).1)
  set G' : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p))
  set Λ : (ℝ × ℝ) →L[ℝ] ℝ :=
    (F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  -- The coordinate change `G` has invertible derivative, since its determinant is the twist.
  have hdetG : G'.det ≠ 0 := by
    simpa [G', ContinuousLinearMap.det, LinearMap.det_finTwoProd] using htwist
  set e : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ := G'.toContinuousLinearEquivOfDetNeZero hdetG
  have he : (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) = G' := G'.coe_toContinuousLinearEquivOfDetNeZero hdetG
  have hG : HasStrictFDerivAt G (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p := by
    rw [he]
    exact hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_fst.comp p
      (hFp.hasStrictFDerivAt (hFp.differentiableAt two_ne_zero).hasFDerivAt two_ne_zero))
  -- Through the local inverse of `G`, `S'` is the generating function.
  set k := hG.localInverse G e p
  have heq : S' =ᶠ[𝓝 (G p)] stripGeneratingFunction F ∘ k := by
    filter_upwards [hG.eventually_right_inverse, hG.localInverse_tendsto.eventually hS']
      with z hz hz'
    calc S' z = S' (G (k z)) := by rw [hz]
      _ = (stripGeneratingFunction F ∘ k) z := hz'
  -- The derivative of `S'` is `Λ`, since `Λ ∘ dG = dS`.
  have hΛ : (F p).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) -
      p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ = Λ.comp (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) := by
    rw [he]
    ext <;> simp [G', Λ]
  have hS : HasFDerivAt (stripGeneratingFunction F)
      ((F p).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) -
        p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) (k (G p)) := by
    have hkp : k (G p) = p := hG.localInverse_apply_image
    rw [hkp]
    exact hasFDerivAt_stripGeneratingFunction hF hY hdet
  have hSk := hS.comp (G p) hG.to_localInverse.hasFDerivAt
  rw [hΛ, ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_comp_coe_symm,
    ContinuousLinearMap.comp_id] at hSk
  exact hSk.congr_of_eventuallyEq heq

/-! ### Affine shears -/

/-- The affine shear `(x, y) ↦ (x + a + c y, y)` has derivative `(u, v) ↦ (u + c v, v)`. -/
private theorem hasFDerivAt_affineShear (a c : ℝ) (q : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ + c • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
  ((hasFDerivAt_fst.add_const a).add (hasFDerivAt_snd.const_mul c)).prodMk hasFDerivAt_snd

/-- The generating function of the affine shear `(x, y) ↦ (x + a + c y, y)` is `c y² / 2`. -/
theorem stripGeneratingFunction_affineShear (a c : ℝ) (p : ℝ × ℝ) :
    stripGeneratingFunction (fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2)) p = c * p.2 ^ 2 / 2 := by
  simp only [stripGeneratingFunction_def, (hasFDerivAt_affineShear a c _).fderiv]
  simp only [ContinuousLinearMap.prod_apply, add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, zero_add,
    intervalIntegral.integral_mul_const, integral_id]
  ring

/-- **The generating equations of an affine shear.** For `c ≠ 0`, the function
`S'(x, X) = (X - x - a)² / (2c)` generates the affine shear `(x, y) ↦ (x + a + c y, y)`: at the
point `(x, X) = (x, x + a + c y)` its partial derivatives are `∂₁ S' = -y` and `∂₂ S' = y`, the
second coordinate of the image. -/
theorem hasFDerivAt_affineShear_generatingFunction {a c : ℝ} (hc : c ≠ 0) (x y : ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ ↦ (z.2 - z.1 - a) ^ 2 / (2 * c))
      (y • ContinuousLinearMap.snd ℝ ℝ ℝ - y • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (x, x + a + c * y) := by
  have hF : ContDiff ℝ 2 fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2) := by fun_prop
  have hdet (q : ℝ × ℝ) : (fderiv ℝ (fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2)) q).det = 1 := by
    rw [(hasFDerivAt_affineShear a c q).fderiv, ContinuousLinearMap.det,
      LinearMap.det_finTwoProd]
    simp
  have htwist : (fderiv ℝ (fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2)) (x, y) (0, 1)).1 ≠ 0 := by
    simpa [(hasFDerivAt_affineShear a c _).fderiv] using hc
  refine hasFDerivAt_of_eventuallyEq_stripGeneratingFunction (fun _ _ ↦ hF.contDiffAt) rfl
    (fun t _ ↦ hdet _) htwist
    (Eventually.of_forall fun q ↦ ?_)
  rw [stripGeneratingFunction_affineShear]
  field_simp
  ring

end TauCeti
