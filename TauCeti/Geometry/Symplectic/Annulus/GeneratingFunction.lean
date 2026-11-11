/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Generating functions of area-preserving maps of the strip

Let `F = (X, Y)` be a `C²` map of the plane `ℝ × ℝ`, with coordinates `(x, y)`, for instance a lift
of an area-preserving diffeomorphism of the annulus `(ℝ / ℤ) × [0, 1]` to the strip
`ℝ × [0, 1]`. This file constructs its generating function in the mixed coordinates `(x, y)`,

`S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt`

(`TauCeti.stripGeneratingFunction`), with the convention `y = -∂₁ S`, `Y = ∂₂ S` in the
coordinates `(x, X)`.

* `S` vanishes on the lower boundary line `y = 0`
  (`TauCeti.stripGeneratingFunction_mk_zero`), and it is invariant under the translation
  `(x, y) ↦ (x + 1, y)` when `F` commutes with it
  (`TauCeti.stripGeneratingFunction_add_one_fst`).
* `S` is `C^n` when `F` is `C^(n + 1)` (`TauCeti.contDiff_stripGeneratingFunction`).
* If `F` maps the lower boundary line into itself, `Y(x, 0) = 0`, and preserves the area form
  `dx ∧ dy` along the segment from `(x, 0)` to `(x, y)`, then
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
(`TauCeti.stripGeneratingFunction_affineShear`), which in the coordinates `(x, X)` is
`(X - x - a)² / (2c)`; its generating equations read `-∂₁ S' = y = ∂₂ S'`
(`TauCeti.hasFDerivAt_affineShear_generatingFunction`).

These are the generating functions of the area-preserving twist factors in the
generating-function proof of the Poincaré–Birkhoff theorem.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapter 5 (generating functions).
-/

public section

noncomputable section

open Filter Set
open scoped Topology Interval

namespace TauCeti

/-- The **generating function** of a map `F = (X, Y)` of the plane, in the mixed coordinates
`(x, y)`: `S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt`. When `F` preserves area and maps the line
`y = 0` into itself, `dS = Y dX - y dx` (`TauCeti.hasFDerivAt_stripGeneratingFunction`). -/
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

/-- If `F` commutes with the translation `(x, y) ↦ (x + 1, y)`, its generating function is
invariant under that translation. -/
theorem stripGeneratingFunction_add_one_fst (hF : ∀ p, F (p + (1, 0)) = F p + (1, 0))
    (p : ℝ × ℝ) : stripGeneratingFunction F (p + (1, 0)) = stripGeneratingFunction F p := by
  -- Commuting with the translation makes the derivative of `F` invariant under it.
  have hD (q : ℝ × ℝ) : fderiv ℝ F (q + (1, 0)) = fderiv ℝ F q := by
    have h := congrArg (fun G : ℝ × ℝ → ℝ × ℝ ↦ fderiv ℝ G q) (funext hF)
    simpa only [fderiv_comp_add_right, fderiv_add_const] using h
  simp only [stripGeneratingFunction_def, Prod.fst_add, Prod.snd_add, add_zero]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hq : ((p.1 + 1, t) : ℝ × ℝ) = (p.1, t) + (1, 0) := by simp
  simp only [hq, hF, hD, Prod.snd_add, add_zero]

/-! ### Regularity -/

/-- The integrand `Y ∂_u X` along a direction `u` of a `C^(n + 1)` map is `C^n`. -/
private theorem contDiff_snd_mul_fst_fderiv {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) (u : ℝ × ℝ) :
    ContDiff ℝ n fun q ↦ (F q).2 * (fderiv ℝ F q u).1 :=
  (contDiff_snd.comp (hF.of_le le_self_add)).mul
    (contDiff_fst.comp ((hF.fderiv_right le_rfl).clm_apply contDiff_const))

/-- The generating function of a `C^(n + 1)` map is `C^n`. -/
theorem contDiff_stripGeneratingFunction {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (stripGeneratingFunction F) := by
  set g : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1
  -- Rescale the variable interval `[0, y]` to `[0, 1]`.
  have h : stripGeneratingFunction F = fun p ↦ p.2 * ∫ s in (0 : ℝ)..1, g (p.1, p.2 * s) := by
    funext p
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t ↦ g (p.1, t)) p.2
    simpa [stripGeneratingFunction_def, g] using this.symm
  rw [h]
  have hg : ContDiff ℝ n fun z : (ℝ × ℝ) × ℝ ↦ g (z.1.1, z.1.2 * z.2) :=
    (contDiff_snd_mul_fst_fderiv hF (0, 1)).comp (by fun_prop)
  exact contDiff_snd.mul (ContDiff.parametric_intervalIntegral hg)

/-! ### The derivative of the generating function -/

/-- The derivative of `q ↦ Y(q) ∂_u X(q)` at `q` in the direction `v` is
`∂_v Y ∂_u X + Y ∂_v ∂_u X`. -/
private theorem hasFDerivAt_snd_mul_fst_fderiv (hF : ContDiff ℝ 2 F) (u q : ℝ × ℝ) :
    HasFDerivAt (fun q ↦ (F q).2 * (fderiv ℝ F q u).1)
      ((F q).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((fderiv ℝ (fderiv ℝ F) q).flip u) +
        (fderiv ℝ F q u).1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ F q)) q := by
  have hF1 : HasFDerivAt F (fderiv ℝ F q) q :=
    (hF.differentiable (by norm_num) q).hasFDerivAt
  have hF2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) q) q :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero q).hasFDerivAt
  have hu := hF2.clm_apply (hasFDerivAt_const u q)
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hu
  exact (hasFDerivAt_snd.comp q hF1).mul (hasFDerivAt_fst.comp q hu)

/-- The `x`-derivative of the integrand `Y ∂_y X` of the generating function is the `y`-derivative
of `Y ∂ₓ X` minus the Jacobian determinant of `F`. -/
private theorem fderiv_snd_mul_fst_fderiv_eq (hF : ContDiff ℝ 2 F) (q : ℝ × ℝ) :
    fderiv ℝ (fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1) q (1, 0) =
      fderiv ℝ (fun q ↦ (F q).2 * (fderiv ℝ F q (1, 0)).1) q (0, 1) -
        (fderiv ℝ F q).det := by
  have hsymm : fderiv ℝ (fderiv ℝ F) q (1, 0) (0, 1) = fderiv ℝ (fderiv ℝ F) q (0, 1) (1, 0) :=
    hF.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) _ _
  rw [(hasFDerivAt_snd_mul_fst_fderiv hF (0, 1) q).fderiv,
    (hasFDerivAt_snd_mul_fst_fderiv hF (1, 0) q).fderiv, ContinuousLinearMap.det,
    LinearMap.det_finTwoProd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_coe, smul_eq_mul, hsymm]
  ring

/-- The partial derivative of the generating function in `x`: if `F` maps `(x, 0)` to the line
`y = 0` and preserves area along the segment from `(x, 0)` to `(x, y)`, then
`∂ₓ S(x, y) = Y(x, y) ∂ₓ X(x, y) - y`. -/
private theorem hasDerivAt_stripGeneratingFunction_fst (hF : ContDiff ℝ 2 F) {x y : ℝ}
    (hY : (F (x, 0)).2 = 0) (hdet : ∀ t ∈ [[0, y]], (fderiv ℝ F (x, t)).det = 1) :
    HasDerivAt (fun s ↦ stripGeneratingFunction F (s, y))
      ((F (x, y)).2 * (fderiv ℝ F (x, y) (1, 0)).1 - y) x := by
  set g : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (0, 1)).1
  set h : ℝ × ℝ → ℝ := fun q ↦ (F q).2 * (fderiv ℝ F q (1, 0)).1
  have hg : ContDiff ℝ 1 g := contDiff_snd_mul_fst_fderiv (n := 1) (hF.of_le (by norm_num)) (0, 1)
  have hh : ContDiff ℝ 1 h := contDiff_snd_mul_fst_fderiv (n := 1) (hF.of_le (by norm_num)) (1, 0)
  -- Differentiate under the integral sign.
  obtain ⟨-, hd⟩ := hasDerivAt_intervalIntegral_of_contDiffOn (G := g) isOpen_univ
    hg.contDiffOn (subset_univ ({x} ×ˢ [[0, y]])) (x₀ := x) (a := 0) (b := y)
  -- The `y`-derivatives of `h` along the segment, and their integral.
  have hcont : Continuous fun t ↦ fderiv ℝ h (x, t) (0, 1) :=
    ((hh.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const
  have hderiv (t : ℝ) : HasDerivAt (fun t ↦ h (x, t)) (fderiv ℝ h (x, t) (0, 1)) t :=
    ((hh.differentiable one_ne_zero (x, t)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hFTC : ∫ t in (0 : ℝ)..y, fderiv ℝ h (x, t) (0, 1) = h (x, y) - h (x, 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      (hcont.intervalIntegrable _ _)
  have hdetint : ∫ t in (0 : ℝ)..y, (fderiv ℝ F (x, t)).det = y := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)) fun t ht ↦ hdet t ht]
    simp
  have hdetcont : Continuous fun t ↦ (fderiv ℝ F (x, t)).det :=
    ContinuousLinearMap.continuous_det.comp ((hF.continuous_fderiv (by norm_num)).comp
      (by fun_prop))
  have hval : ∫ t in (0 : ℝ)..y, fderiv ℝ g (x, t) (1, 0) =
      (F (x, y)).2 * (fderiv ℝ F (x, y) (1, 0)).1 - y := by
    simp only [g, fderiv_snd_mul_fst_fderiv_eq hF]
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (hdetcont.intervalIntegrable _ _), hFTC, hdetint]
    simp [h, hY]
  rw [← hval]
  exact hd

/-- **The generating function of an area-preserving map.** If `F = (X, Y)` is `C²`, maps `(x, 0)`
to the line `y = 0` and preserves the area form `dx ∧ dy` along the segment from `(x, 0)` to
`p = (x, y)`, then its generating function `S` satisfies `dS = Y dX - y dx` at `p`:
`∂ₓ S = Y ∂ₓ X - y` and `∂_y S = Y ∂_y X`. -/
theorem hasFDerivAt_stripGeneratingFunction (hF : ContDiff ℝ 2 F) {p : ℝ × ℝ}
    (hY : (F (p.1, 0)).2 = 0) (hdet : ∀ t ∈ [[0, p.2]], (fderiv ℝ F (p.1, t)).det = 1) :
    HasFDerivAt (stripGeneratingFunction F)
      ((F p).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p) -
        p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨x, y⟩ := p
  have hS : DifferentiableAt ℝ (stripGeneratingFunction F) (x, y) :=
    (contDiff_stripGeneratingFunction (n := 1) (hF.of_le (by norm_num))).differentiable
      one_ne_zero _
  convert hS.hasFDerivAt using 1
  -- Compare the two partial derivatives.
  have hfst : HasDerivAt (fun s ↦ stripGeneratingFunction F (s, y))
      (fderiv ℝ (stripGeneratingFunction F) (x, y) (1, 0)) x := by
    -- Elaborate the composition first; its function `S ∘ (·, y)` is then unfolded by `exact`.
    have h := hS.hasFDerivAt.comp_hasDerivAt x
      (HasDerivAt.prodMk (hasDerivAt_id' x) (hasDerivAt_const x y))
    exact h
  have hsnd : HasDerivAt (fun t ↦ stripGeneratingFunction F (x, t))
      (fderiv ℝ (stripGeneratingFunction F) (x, y) (0, 1)) y :=
    hS.hasFDerivAt.comp_hasDerivAt y (HasDerivAt.prodMk (hasDerivAt_const y x) (hasDerivAt_id' y))
  have hsnd' : HasDerivAt (fun t ↦ stripGeneratingFunction F (x, t))
      ((F (x, y)).2 * (fderiv ℝ F (x, y) (0, 1)).1) y :=
    ((contDiff_snd_mul_fst_fderiv (n := 0) (hF.of_le (by norm_num)) (0, 1)).continuous.comp
      (by fun_prop : Continuous fun t : ℝ ↦ (x, t)) |>.integral_hasStrictDerivAt 0 y).hasDerivAt
  refine ContinuousLinearMap.prod_ext (ContinuousLinearMap.ext_ring ?_)
    (ContinuousLinearMap.ext_ring ?_)
  · simpa using (hfst.unique (hasDerivAt_stripGeneratingFunction_fst hF hY hdet)).symm
  · simpa using (hsnd.unique hsnd').symm

/-- **The generating equations.** Let `F = (X, Y)` be a `C²` map which maps `(x, 0)` to the line
`y = 0`, preserves area along the segment from `(x, 0)` to `p = (x, y)`, and twists at `p`:
`∂_y X(p) ≠ 0`. If a function `S'` of `(x, X)` agrees near `p` with the generating function of `F`
through `(x, y) ↦ (x, X(x, y))`, then at `(x, X(p))` it has derivative `Y(p) dX - y dx`. That is,
`∂₁ S'(x, X) = -y` and `∂₂ S'(x, X) = Y`. -/
theorem hasFDerivAt_of_eventuallyEq_stripGeneratingFunction (hF : ContDiff ℝ 2 F) {p : ℝ × ℝ}
    (hY : (F (p.1, 0)).2 = 0) (hdet : ∀ t ∈ [[0, p.2]], (fderiv ℝ F (p.1, t)).det = 1)
    (htwist : (fderiv ℝ F p (0, 1)).1 ≠ 0) {S' : ℝ × ℝ → ℝ}
    (hS' : (fun q ↦ S' (q.1, (F q).1)) =ᶠ[𝓝 p] stripGeneratingFunction F) :
    HasFDerivAt S' ((F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ -
      p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) (p.1, (F p).1) := by
  set G : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1, (F q).1)
  set G' : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F p))
  set Λ : (ℝ × ℝ) →L[ℝ] ℝ :=
    (F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  -- The coordinate change `G` has invertible derivative, since its determinant is the twist.
  have hdetG : LinearMap.det (G' : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) ≠ 0 := by
    simpa [G', LinearMap.det_finTwoProd] using htwist
  set e : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
    (LinearMap.equivOfDetNeZero (G' : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) hdetG).toContinuousLinearEquiv
  have he : (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) = G' := by
    ext <;> rfl
  have hG : HasStrictFDerivAt G (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p := by
    rw [he]
    exact hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_fst.comp p
      (hF.hasStrictFDerivAt two_ne_zero))
  -- Through the local inverse of `G`, `S'` is the generating function.
  set k := hG.localInverse G e p
  have hk : Tendsto k (𝓝 (G p)) (𝓝 p) := by
    have := hG.localInverse_continuousAt.tendsto
    rwa [hG.eventually_left_inverse.self_of_nhds] at this
  have heq : S' =ᶠ[𝓝 (G p)] stripGeneratingFunction F ∘ k := by
    filter_upwards [hG.eventually_right_inverse, hk.eventually hS'] with z hz hz'
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
    have hkp : k (G p) = p := hG.eventually_left_inverse.self_of_nhds
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
  refine hasFDerivAt_of_eventuallyEq_stripGeneratingFunction hF rfl (fun t _ ↦ hdet _) htwist
    (Eventually.of_forall fun q ↦ ?_)
  rw [stripGeneratingFunction_affineShear]
  field_simp
  ring

end TauCeti
