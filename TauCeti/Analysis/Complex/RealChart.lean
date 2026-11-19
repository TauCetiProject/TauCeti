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
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.DiscreteSubset
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Maps of the complex plane in real coordinates

A map `f : ℂ → ℂ` of the plane, read in the real coordinates `ℝ × ℝ ≃ ℂ` given by
`Complex.equivRealProdCLM`, is `TauCeti.Complex.realChart f`. When `f` has complex derivative
`f'`, the real derivative of its real chart is multiplication by `f'`
(`TauCeti.Complex.hasFDerivAt_realChart`, `TauCeti.Complex.fderiv_realChart_apply`), whose real
determinant is `|f'|²`, so the Jacobian determinant of the real chart is nonnegative
(`TauCeti.Complex.det_fderiv_realChart`, `TauCeti.Complex.det_fderiv_realChart_nonneg`), and a map
that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates (`TauCeti.Complex.contDiff_realChart`).
The real chart of an injective map is injective (`TauCeti.Complex.realChart_injective`), and so is
the real chart of a map injective on a set, on the corresponding set
(`TauCeti.Complex.injOn_realChart`). The real chart maps the real coordinates of a set onto those
of its image (`TauCeti.Complex.image_realChart_preimage`).

Conversely, a map `f : ℝ × ℝ → E` can be read in the complex coordinate
`Complex.equivRealProdCLM`. Vanishing on a set, vanishing to finite order at a point and
codiscreteness of the nonzero set pass from the complex coordinate back to `ℝ × ℝ`
(`TauCeti.eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM`,
`TauCeti.isBigO_comp_equivRealProdCLM_pow`,
`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM`).
-/

public section

namespace TauCeti.Complex

/-- A map `f : ℂ → ℂ` of the plane, written in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def realChart (f : ℂ → ℂ) : ℝ × ℝ → ℝ × ℝ :=
  Complex.equivRealProdCLM ∘ f ∘ Complex.equivRealProdCLM.symm

theorem realChart_apply (f : ℂ → ℂ) (z : ℝ × ℝ) :
    realChart f z = Complex.equivRealProdCLM (f (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

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

/-- A map that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates. -/
theorem contDiff_realChart {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℂ n f) :
    ContDiff ℝ n (realChart f) :=
  Complex.equivRealProdCLM.contDiff.comp
    ((hf.restrict_scalars ℝ).comp Complex.equivRealProdCLM.symm.contDiff)

/-- The real chart of an injective map is injective. -/
theorem realChart_injective {f : ℂ → ℂ} (hf : Function.Injective f) :
    Function.Injective (realChart f) :=
  Complex.equivRealProdCLM.injective.comp (hf.comp Complex.equivRealProdCLM.symm.injective)

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

/-! ### Transport from real coordinates -/

section RealCoordinates

open Asymptotics Filter Function Set Topology

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E} {Ω : Set (ℝ × ℝ)}

/-- A map vanishing on `Ω` in the complex coordinate `Complex.equivRealProdCLM` vanishes on `Ω`. -/
theorem eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM
    (h : EqOn (f ∘ Complex.equivRealProdCLM) 0 (Complex.equivRealProdCLM ⁻¹' Ω)) :
    EqOn f 0 Ω := fun z hz ↦ by
  simpa using h (show Complex.equivRealProdCLM.symm z ∈ _ by simpa using hz)

/-- A map vanishing to order `n` at `z₀` vanishes to order `n` at the corresponding point in the
complex coordinate `Complex.equivRealProdCLM`: there the vanishing order is measured by
`‖e w - e w₀‖ ≤ ‖e‖ ‖w - w₀‖`. -/
theorem isBigO_comp_equivRealProdCLM_pow {z₀ : ℝ × ℝ} {n : ℕ}
    (h : f =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) :
    (f ∘ Complex.equivRealProdCLM) =O[𝓝 (Complex.equivRealProdCLM.symm z₀)]
      fun w ↦ (w - Complex.equivRealProdCLM.symm z₀) ^ n := by
  set e := Complex.equivRealProdCLM
  have h := h.comp_tendsto
    ((e.continuous.tendsto (e.symm z₀)).trans_eq (by rw [e.apply_symm_apply]))
  refine h.trans (IsBigO.of_bound (‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ^ n) (Eventually.of_forall fun w ↦ ?_))
  have hw : e w - z₀ = e (w - e.symm z₀) := by simp
  simp only [comp_apply, hw, norm_pow, norm_norm, ← mul_pow]
  gcongr
  exact (e : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _

/-- A map whose nonzero set is codiscrete in `e ⁻¹' Ω` in the complex coordinate
`e = Complex.equivRealProdCLM` has nonzero set codiscrete in `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM
    (h : {w | (f ∘ Complex.equivRealProdCLM) w ≠ 0} ∈
      codiscreteWithin (Complex.equivRealProdCLM ⁻¹' Ω)) :
    {z | f z ≠ 0} ∈ codiscreteWithin Ω := by
  set e := Complex.equivRealProdCLM
  -- Transport the codiscrete set back along the homeomorphism `e`.
  have := (e.toHomeomorph.isEmbedding.image_mem_codiscreteWithin
    (s := e ⁻¹' {z | f z ≠ 0}) (t := e ⁻¹' Ω)).2 h
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
    image_preimage_eq _ e.surjective] using this

end RealCoordinates

end TauCeti
