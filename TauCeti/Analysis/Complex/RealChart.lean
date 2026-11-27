/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# Maps of the complex plane in real coordinates

A map `f : ℂ → ℂ` of the plane, read in the real coordinates `ℝ × ℝ ≃ ℂ` given by
`Complex.equivRealProdCLM`, is `TauCeti.Complex.realChart f`, which sends `(s, t)` to the real
coordinates of `f (s + i t)` (`TauCeti.Complex.realChart_mk`). When `f` has complex derivative
`f'`, the real derivative of its real chart is multiplication by `f'`
(`TauCeti.Complex.hasFDerivAt_realChart`, `TauCeti.Complex.fderiv_realChart_apply`), whose real
determinant is `|f'|²`, so the Jacobian determinant of the real chart is nonnegative
(`TauCeti.Complex.det_fderiv_realChart`, `TauCeti.Complex.det_fderiv_realChart_nonneg`), and the
real derivative is nonzero when `f'` is (`TauCeti.Complex.fderiv_realChart_ne_zero`). By the
chain rule, the partial derivatives of `ξ ∘ realChart f` are those of `ξ` composed with the
conformal matrix of `f'` (`TauCeti.Complex.fderiv_comp_realChart_apply_one_zero`,
`TauCeti.Complex.fderiv_comp_realChart_apply_zero_one`), so the Jacobian times a weighted density
`r ‖ξ‖² + ‖∂₁ξ‖² + ‖∂₂ξ‖²` at the image point is controlled by the `W^{1,2}` density of
`ξ ∘ realChart f` (`TauCeti.Complex.det_fderiv_realChart_mul_le`). A map that is `C^n` over `ℂ`
is `C^n` over `ℝ` in real coordinates (`TauCeti.Complex.contDiff_realChart`), and likewise at a
point (`TauCeti.Complex.contDiffAt_realChart`). The inversion `w ↦ w⁻¹` in real coordinates is an
involution (`TauCeti.Complex.realChart_inv_involutive`) that inverts the Euclidean norm
(`TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv`); away from `0` it is smooth
(`TauCeti.Complex.contDiffAt_realChart_inv`) with Jacobian determinant `|w⁻¹|⁴`
(`TauCeti.Complex.det_fderiv_realChart_inv`). Read through the inversion, a function vanishing on
the disc `|w| < r` vanishes on `|ζ| > r⁻¹` (`TauCeti.Complex.apply_realChart_inv_eq_zero`), and
also near `ζ = 0` when it has compact support
(`TauCeti.Complex.exists_pos_forall_apply_realChart_inv_eq_zero`).
The real chart of an injective map is injective (`TauCeti.Complex.realChart_injective`), and so is
the real chart of a map injective on a set, on the corresponding set
(`TauCeti.Complex.injOn_realChart`). The real chart maps the real coordinates of a set onto those
of its image (`TauCeti.Complex.image_realChart_preimage`).
Adding or subtracting a real number `c` is adding or subtracting `(c, 0)` in real coordinates
(`TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero`,
`TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero`). In real coordinates, every part
`‖w‖ > r` of the plane contains a part `‖w‖ > exp (2πa)` with `a` as large as desired
(`TauCeti.exists_le_exp_lt_norm_subset`).
-/

public section

namespace TauCeti.Complex

/-- A map `f : ℂ → ℂ` of the plane, written in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def realChart (f : ℂ → ℂ) : ℝ × ℝ → ℝ × ℝ :=
  Complex.equivRealProdCLM ∘ f ∘ Complex.equivRealProdCLM.symm

theorem realChart_apply (f : ℂ → ℂ) (z : ℝ × ℝ) :
    realChart f z = Complex.equivRealProdCLM (f (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- In real coordinates, `f` sends `(s, t)` to the real coordinates of `f (s + i t)`. -/
theorem realChart_mk (f : ℂ → ℂ) (s t : ℝ) :
    realChart f (s, t) = Complex.equivRealProdCLM (f (s + t * Complex.I)) := by
  rw [realChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- In complex coordinates, the real chart of `f` is `f`. -/
@[simp]
theorem equivRealProdCLM_symm_realChart (f : ℂ → ℂ) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (realChart f z) = f (Complex.equivRealProdCLM.symm z) :=
  Complex.equivRealProdCLM.symm_apply_apply _

/-- The real chart of `f` at the real coordinates of `w` is the real coordinates of `f w`. -/
theorem realChart_equivRealProdCLM (f : ℂ → ℂ) (w : ℂ) :
    realChart f (Complex.equivRealProdCLM w) = Complex.equivRealProdCLM (f w) := by
  rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- In real coordinates, the derivative of a map with complex derivative `f'` is multiplication
by `f'`. -/
theorem hasFDerivAt_realChart {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    HasFDerivAt (realChart f)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ).comp
          (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) w :=
  Complex.equivRealProdCLM.hasFDerivAt.comp w
    ((hf.hasFDerivAt.restrictScalars ℝ).comp w Complex.equivRealProdCLM.symm.hasFDerivAt)

theorem fderiv_realChart_apply {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) (v : ℝ × ℝ) :
    fderiv ℝ (realChart f) w v =
      Complex.equivRealProdCLM (f' * Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_realChart hf).fderiv]
  simp [mul_comm]

/-- In real coordinates, the Jacobian determinant of a map with complex derivative `f'` is
`|f'|²`. -/
theorem det_fderiv_realChart {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    (fderiv ℝ (realChart f) w).det = Complex.normSq f' := by
  rw [(hasFDerivAt_realChart hf).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- In real coordinates, the Jacobian determinant of a map with a complex derivative is
nonnegative. -/
theorem det_fderiv_realChart_nonneg {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    0 ≤ (fderiv ℝ (realChart f) w).det := by
  rw [det_fderiv_realChart hf]
  exact Complex.normSq_nonneg f'

/-- In real coordinates, a map with nonzero complex derivative has nonzero derivative. -/
theorem fderiv_realChart_ne_zero {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) (hf' : f' ≠ 0) :
    fderiv ℝ (realChart f) w ≠ 0 := by
  intro h
  have h₁ := congrArg (fun L ↦ L (Complex.equivRealProdCLM 1)) h
  simp only [fderiv_realChart_apply hf, ContinuousLinearEquiv.symm_apply_apply, mul_one,
    zero_apply, map_eq_zero_iff _ Complex.equivRealProdCLM.injective] at h₁
  exact hf' h₁

/-- **The chain rule along a real chart, along `(1, 0)`.** If `f` has complex derivative
`f' = a + i b`, the derivative of `ξ ∘ realChart f` along `(1, 0)` is `a ∂₁ξ + b ∂₂ξ`, the partial
derivatives of `ξ` taken at the image point. -/
theorem fderiv_comp_realChart_apply_one_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ} {ξ : ℝ × ℝ → V}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w))
    (hξ : DifferentiableAt ℝ ξ (realChart f w)) :
    fderiv ℝ (ξ ∘ realChart f) w (1, 0) =
      f'.re • fderiv ℝ ξ (realChart f w) (1, 0) + f'.im • fderiv ℝ ξ (realChart f w) (0, 1) := by
  rw [fderiv_comp w hξ (hasFDerivAt_realChart hf).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_realChart_apply hf,
    ← ContinuousLinearMap.apply_mk_eq_smul_add_smul]
  congr 1
  simp [Complex.equivRealProdCLM_symm_apply]

/-- **The chain rule along a real chart, along `(0, 1)`.** If `f` has complex derivative
`f' = a + i b`, the derivative of `ξ ∘ realChart f` along `(0, 1)` is `-b ∂₁ξ + a ∂₂ξ`, the partial
derivatives of `ξ` taken at the image point. -/
theorem fderiv_comp_realChart_apply_zero_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ} {ξ : ℝ × ℝ → V}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w))
    (hξ : DifferentiableAt ℝ ξ (realChart f w)) :
    fderiv ℝ (ξ ∘ realChart f) w (0, 1) =
      (-f'.im) • fderiv ℝ ξ (realChart f w) (1, 0) + f'.re • fderiv ℝ ξ (realChart f w) (0, 1) := by
  rw [fderiv_comp w hξ (hasFDerivAt_realChart hf).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_realChart_apply hf,
    ← ContinuousLinearMap.apply_mk_eq_smul_add_smul]
  congr 1
  simp [Complex.equivRealProdCLM_symm_apply]

/-- **The weighted density along a real chart.** Let `f` have a complex derivative at `w`, and
let the weight `r` times the Jacobian of `realChart f` at `w` be at most `M`, with `2 ≤ M`. Then
the Jacobian times the weighted density `r ‖ξ‖² + ‖∂₁ξ‖² + ‖∂₂ξ‖²` at `realChart f w` is at most
`M` times the `W^{1,2}` density of `ξ ∘ realChart f` at `w`. -/
theorem det_fderiv_realChart_mul_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ} {ξ : ℝ × ℝ → V} {r M : ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w))
    (hξ : DifferentiableAt ℝ ξ (realChart f w)) (hr : r * (fderiv ℝ (realChart f) w).det ≤ M)
    (hM : 2 ≤ M) :
    (fderiv ℝ (realChart f) w).det *
        (r * ‖ξ (realChart f w)‖ ^ 2 + ‖fderiv ℝ ξ (realChart f w) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ (realChart f w) (0, 1)‖ ^ 2) ≤
      M * (‖fderiv ℝ (ξ ∘ realChart f) w (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ realChart f) w (0, 1)‖ ^ 2 + ‖ξ (realChart f w)‖ ^ 2) := by
  set X := fderiv ℝ ξ (realChart f w) (1, 0)
  set Y := fderiv ℝ ξ (realChart f w) (0, 1)
  -- The conformal matrix of `f'` scales the squared partial derivatives by at most twice `|f'|²`.
  have hconf := le_two_mul_norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq f'.re f'.im X Y
  rw [fderiv_comp_realChart_apply_one_zero hf hξ, fderiv_comp_realChart_apply_zero_one hf hξ]
  rw [det_fderiv_realChart hf, Complex.normSq_apply] at hr ⊢
  nlinarith [sq_nonneg ‖ξ (realChart f w)‖, sq_nonneg ‖f'.re • X + f'.im • Y‖,
    sq_nonneg ‖(-f'.im) • X + f'.re • Y‖]

/-- A map that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates. -/
theorem contDiff_realChart {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℂ n f) :
    ContDiff ℝ n (realChart f) :=
  Complex.equivRealProdCLM.contDiff.comp
    ((hf.restrict_scalars ℝ).comp Complex.equivRealProdCLM.symm.contDiff)

/-- A map that is `C^n` over `ℂ` at a point is `C^n` over `ℝ` in real coordinates there. -/
theorem contDiffAt_realChart {f : ℂ → ℂ} {n : WithTop ℕ∞} {w : ℝ × ℝ}
    (hf : ContDiffAt ℂ n f (Complex.equivRealProdCLM.symm w)) :
    ContDiffAt ℝ n (realChart f) w :=
  Complex.equivRealProdCLM.contDiff.contDiffAt.comp w
    ((hf.restrict_scalars ℝ).comp w Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

/-- The inversion `w ↦ w⁻¹`, read in real coordinates, is an involution. -/
theorem realChart_inv_involutive : Function.Involutive (realChart (·⁻¹)) := fun w ↦ by
  rw [realChart_apply, equivRealProdCLM_symm_realChart, inv_inv,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The inversion inverts the Euclidean norm. -/
theorem norm_equivRealProdCLM_symm_realChart_inv (w : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (realChart (·⁻¹) w)‖ = ‖Complex.equivRealProdCLM.symm w‖⁻¹ := by
  rw [equivRealProdCLM_symm_realChart, norm_inv]

/-- Away from `0`, the Jacobian determinant of the inversion at `w` is `|w|⁻⁴ = |w⁻¹|⁴`. -/
theorem det_fderiv_realChart_inv {w : ℝ × ℝ} (hw : Complex.equivRealProdCLM.symm w ≠ 0) :
    (fderiv ℝ (realChart (·⁻¹)) w).det =
      ‖Complex.equivRealProdCLM.symm (realChart (·⁻¹) w)‖ ^ 4 := by
  rw [det_fderiv_realChart (hasDerivAt_inv hw), norm_equivRealProdCLM_symm_realChart_inv,
    Complex.normSq_eq_norm_sq, norm_neg, norm_inv, norm_pow]
  ring

/-- Away from `0`, the inversion is smooth in real coordinates. -/
theorem contDiffAt_realChart_inv {w : ℝ × ℝ} (hw : Complex.equivRealProdCLM.symm w ≠ 0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (realChart (·⁻¹)) w :=
  contDiffAt_realChart (contDiffAt_inv ℂ hw)

/-- A function vanishing on the disc `|w| < r` vanishes, read through the inversion, on
`|ζ| > r⁻¹`. -/
theorem apply_realChart_inv_eq_zero {E : Type*} [Zero E] {f : ℝ × ℝ → E} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → f z = 0) {ζ : ℝ × ℝ}
    (hζ : r⁻¹ < ‖Complex.equivRealProdCLM.symm ζ‖) : f (realChart (·⁻¹) ζ) = 0 :=
  hf _ (by
    rw [norm_equivRealProdCLM_symm_realChart_inv]
    exact inv_lt_of_inv_lt₀ hr hζ)

/-- A compactly supported function vanishing on the disc `|w| < r` vanishes, read through the
inversion, on a neighbourhood `|ζ| < δ` of `ζ = 0`. -/
theorem exists_pos_forall_apply_realChart_inv_eq_zero {E : Type*} [Zero E] {f : ℝ × ℝ → E}
    (hc : HasCompactSupport f) {r : ℝ} (hr : 0 < r)
    (hf : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → f z = 0) :
    ∃ δ > 0, ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < δ → f (realChart (·⁻¹) ζ) = 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn
    Complex.equivRealProdCLM.symm.continuous.continuousOn
  refine ⟨(max M 1)⁻¹, by positivity, fun ζ hζ ↦ ?_⟩
  by_cases hx : Complex.equivRealProdCLM.symm ζ = 0
  · have h0 : realChart (·⁻¹) ζ = 0 := by simp [realChart_apply, hx]
    exact h0 ▸ hf 0 (by simpa using hr)
  · refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
    have h1 := hM _ hmem
    rw [norm_equivRealProdCLM_symm_realChart_inv] at h1
    have h2 : max M 1 < ‖Complex.equivRealProdCLM.symm ζ‖⁻¹ :=
      lt_inv_of_lt_inv₀ (norm_pos_iff.2 hx) hζ
    linarith [le_max_left M 1]

/-- The real chart of an injective map is injective. -/
theorem realChart_injective {f : ℂ → ℂ} (hf : Function.Injective f) :
    Function.Injective (realChart f) :=
  Complex.equivRealProdCLM.injective.comp (hf.comp Complex.equivRealProdCLM.symm.injective)

/-- In real coordinates, subtracting `(c, 0)` is subtracting the real number `c`. -/
theorem equivRealProdCLM_symm_sub_prodMk_zero (z : ℝ × ℝ) (c : ℝ) :
    Complex.equivRealProdCLM.symm (z - (c, 0)) = Complex.equivRealProdCLM.symm z - c := by
  apply Complex.ext <;> simp

/-- In real coordinates, adding `(c, 0)` is adding the real number `c`. -/
theorem equivRealProdCLM_symm_add_prodMk_zero (z : ℝ × ℝ) (c : ℝ) :
    Complex.equivRealProdCLM.symm (z + (c, 0)) = Complex.equivRealProdCLM.symm z + c := by
  apply Complex.ext <;> simp

/-- The real chart of a map injective on the image of `s` in `ℂ` is injective on `s`. -/
theorem injOn_realChart {f : ℂ → ℂ} {s : Set (ℝ × ℝ)}
    (hf : Set.InjOn f (Complex.equivRealProdCLM.symm '' s)) : Set.InjOn (realChart f) s :=
  fun _ hp _ hq h ↦ Complex.equivRealProdCLM.symm.injective <|
    hf (Set.mem_image_of_mem _ hp) (Set.mem_image_of_mem _ hq)
      (by simpa using congrArg Complex.equivRealProdCLM.symm h)

/-- The real chart of `f` maps the real coordinates of a set `s` onto the real coordinates of
`f '' s`. -/
theorem image_realChart_preimage (f : ℂ → ℂ) (s : Set ℂ) :
    realChart f '' (Complex.equivRealProdCLM.symm ⁻¹' s) =
      Complex.equivRealProdCLM.symm ⁻¹' (f '' s) := by
  rw [realChart, Set.image_comp, Set.image_comp,
    Set.image_preimage_eq _ Complex.equivRealProdCLM.symm.surjective,
    Complex.equivRealProdCLM.image_eq_preimage_symm]

end TauCeti.Complex

namespace TauCeti

/-- In the real coordinates of `ℂ`, every part `‖w‖ > r` of the plane contains a part
`‖w‖ > exp (2πa)` with `a ≥ T₀`. -/
theorem exists_le_exp_lt_norm_subset (T₀ r : ℝ) :
    ∃ a : ℝ, T₀ ≤ a ∧
      {z : ℝ × ℝ | Real.exp (2 * Real.pi * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
        {z | r < ‖Complex.equivRealProdCLM.symm z‖} := by
  have h := Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop Real.two_pi_pos)
  obtain ⟨a, ha, hr⟩ := ((Filter.eventually_ge_atTop T₀).and (h.eventually_ge_atTop r)).exists
  exact ⟨a, ha, fun _ hz ↦ hr.trans_lt hz⟩

end TauCeti
