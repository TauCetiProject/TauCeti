/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The canonical Morse–Palais operator

Palais's proof of the Morse lemma writes a function with a critical point at `0` as
`f v = f 0 + ½ A(v)(v, v)`, where `A(v) = hessianAverage f 0 v` is the averaged Hessian along the
segment from `0` to `v`, and then takes the square root `R(v)` near the identity of the operator
`H⁻¹ ∘ A(v)`, where `H = D²f(0)` is the Hessian. Then `R(v)` is self-adjoint for `H` and
`H (R(v) v) (R(v) v) = A(v)(v, v)`, so `v ↦ R(v) v` puts `f` in its Hessian normal form.

This file names that operator, `TauCeti.morsePalaisOperator f v`. Unlike the existential normal
forms of `TauCeti.Analysis.Calculus.Morse.NormalForm` and
`TauCeti.Analysis.Calculus.Morse.Parametric`, it is determined by `f` alone, with no choices, so
normal forms built from it in different coordinates or near different points can be compared
and glued.

For a family `F (b, v)` of functions with critical zero section, the operator is taken fibrewise,
`R (b, v) = morsePalaisOperator (fun v ↦ F (b, v)) v`, with reference form the vertical Hessian
`H_b` at `(b, 0)`, and not a Hessian at a fixed basepoint. Near every point `(b₀, 0)` at which
`H_{b₀}` is invertible, it is `C^n` when `F` is `C^{n+2}`, it is the identity on the zero
section, and it satisfies the congruence `H_b (R w) (R w') = A (b, v) w w'` and hence the normal
form `F (b, v) = F (b, 0) + ½ H_b (R v) (R v)`.

It is natural under fibrewise linear changes of coordinates `v = L_b v'` depending continuously
on the base (`TauCeti.eventually_morsePalaisOperator_comp`): the operator of
`(b, v') ↦ F (b, L_b v')` is `L_b⁻¹ ∘ R (b, L_b v') ∘ L_b`. These are the transition maps
between local trivializations of a vector bundle. It also depends only on the function along the
segment from `0` to `v` (`TauCeti.morsePalaisOperator_congr_of_eqOn`). The naturality comes
from the uniqueness of square roots near the identity (`TauCeti.eventually_map_sqrtNearOne`).

Because the operator is canonical, the local normal forms near the points of the zero section
glue: over an open set `U` of the base on which the zero section is critical and
nondegenerate, `(b, v) ↦ (b, R (b, v) v)` is a single `C^n` chart on a neighbourhood of the whole
zero section over `U`, in which `F` is its vertical Hessian quadratic form
(`TauCeti.exists_morsePalaisOperator_chart`). Its fibres are unions of balls about `0`, which
are nested, so the chart is injective.

## Main declarations

* `TauCeti.morsePalaisOperator`: the square root near the identity of `H⁻¹ ∘ A(v)`.
* `TauCeti.morsePalaisOperator_zero`: it is the identity at `v = 0`.
* `TauCeti.morsePalaisOperator_congr_of_eqOn`: it only depends on the function near the segment.
* `TauCeti.eventually_contDiffAt_morsePalaisOperator`: the fibrewise operator of a `C^{n+2}`
  family is `C^n` near each point of the zero section with invertible vertical Hessian.
* `TauCeti.eventually_morsePalaisOperator_congruence`: it is a congruence from the vertical
  Hessian to the averaged Hessian.
* `TauCeti.eventually_eq_add_morsePalaisOperator`: the parametric Morse normal form.
* `TauCeti.eventually_morsePalaisOperator_comp`: naturality under fibrewise linear changes of
  coordinates.
* `TauCeti.exists_morsePalaisOperator_chart`: the parametric Morse lemma along the whole zero
  section over an open set of the base, in a single chart given by the operator.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the operator square root.
* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The **Morse–Palais operator** of `f : E → ℝ` at the displacement `v`: the square root near
the identity (`TauCeti.sqrtNearOne`) of the operator `H⁻¹ ∘ hessianAverage f 0 v`, where
`H = D²f(0)` is the Hessian at `0`. When `0` is a nondegenerate critical point it is the identity
at `v = 0` (`TauCeti.morsePalaisOperator_zero`), and `v ↦ morsePalaisOperator f v v` carries `f`
to its Hessian normal form near `0`. -/
def morsePalaisOperator (f : E → ℝ) (v : E) : E →L[ℝ] E :=
  sqrtNearOne (E →L[ℝ] E) ((fderiv ℝ (fderiv ℝ f) 0).inverse.comp (hessianAverage f 0 v))

theorem morsePalaisOperator_def (f : E → ℝ) (v : E) :
    morsePalaisOperator f v =
      sqrtNearOne (E →L[ℝ] E) ((fderiv ℝ (fderiv ℝ f) 0).inverse.comp (hessianAverage f 0 v)) :=
  (rfl)

/-- The operator `H⁻¹ ∘ hessianAverage f 0 v` whose square root is the Morse–Palais operator. -/
private def comparison (f : E → ℝ) (v : E) : E →L[ℝ] E :=
  (fderiv ℝ (fderiv ℝ f) 0).inverse.comp (hessianAverage f 0 v)

private theorem morsePalaisOperator_eq_comparison (f : E → ℝ) (v : E) :
    morsePalaisOperator f v = sqrtNearOne (E →L[ℝ] E) (comparison f v) :=
  (rfl)

omit [CompleteSpace E] in
private theorem comparison_zero {f : E → ℝ} (h : (fderiv ℝ (fderiv ℝ f) 0).IsInvertible) :
    comparison f 0 = 1 := by
  rw [comparison, hessianAverage_zero, h.inverse_comp_self, ContinuousLinearMap.one_def]

/-- At a nondegenerate critical point the Morse–Palais operator is the identity at `v = 0`. -/
theorem morsePalaisOperator_zero {f : E → ℝ} (h : (fderiv ℝ (fderiv ℝ f) 0).IsInvertible) :
    morsePalaisOperator f 0 = 1 := by
  rw [morsePalaisOperator_eq_comparison, comparison_zero h, sqrtNearOne_one]

omit [CompleteSpace E] in
private theorem fderiv_fderiv_apply_comparison {f : E → ℝ}
    (h : (fderiv ℝ (fderiv ℝ f) 0).IsInvertible) (v w : E) :
    fderiv ℝ (fderiv ℝ f) 0 (comparison f v w) = hessianAverage f 0 v w := by
  rw [comparison, ContinuousLinearMap.comp_apply, h.self_apply_inverse]

/-- The **Morse–Palais operator only depends on `f` near the segment** from `0` to `v`: functions
agreeing on an open set star-convex about `0` and containing `v` have the same operator at
`v`. -/
theorem morsePalaisOperator_congr_of_eqOn {f g : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hU₀ : StarConvex ℝ 0 U) (hfg : EqOn f g U) {v : E} (hv : v ∈ U) :
    morsePalaisOperator f v = morsePalaisOperator g v := by
  have hD : ∀ y ∈ U, fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := fun y hy ↦
    (hfg.eventuallyEq_of_mem (hU.mem_nhds hy)).fderiv.fderiv_eq
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1, (0 : E) + t • v ∈ U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simpa using hU₀.smul_mem hv ht.1 ht.2
  have hA : hessianAverage f 0 v = hessianAverage g 0 v := by
    rw [hessianAverage_eq_integral_Icc, hessianAverage_eq_integral_Icc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hD _ (hseg t (by rwa [uIcc_of_le zero_le_one]))]
  rw [morsePalaisOperator_def, morsePalaisOperator_def, hA,
    hD 0 (by simpa using hseg 0 (by simp))]

section Adjoint

omit [CompleteSpace E]

/-- The adjoint of an operator `T` for the pairing given by a bilinear form `B`, when `B` is
invertible: `B (bilinAdjoint B T w) w' = B w (T w')`. -/
private def bilinAdjoint (B : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) : E →L[ℝ] E :=
  B.inverse.comp (((ContinuousLinearMap.compL ℝ E E ℝ).flip T).comp B)

private theorem bilinAdjoint_apply {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible)
    (T : E →L[ℝ] E) (w w' : E) : B (bilinAdjoint B T w) w' = B w (T w') := by
  simp [bilinAdjoint, hB.self_apply_inverse]

private theorem eq_of_forall_bilin_apply {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible)
    {T₁ T₂ : E →L[ℝ] E} (h : ∀ w w', B (T₁ w) w' = B (T₂ w) w') : T₁ = T₂ :=
  ContinuousLinearMap.ext fun w ↦ hB.injective (ContinuousLinearMap.ext (h w))

private theorem bilinAdjoint_mul_self {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible)
    (T : E →L[ℝ] E) : bilinAdjoint B (T * T) = bilinAdjoint B T * bilinAdjoint B T :=
  eq_of_forall_bilin_apply hB fun w w' ↦ by simp only [mul_apply_eq_comp, bilinAdjoint_apply hB]

private theorem bilinAdjoint_one {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible) :
    bilinAdjoint B 1 = 1 :=
  eq_of_forall_bilin_apply hB fun w w' ↦ by simp [bilinAdjoint_apply hB]

/-- The adjoint depends continuously on the form, at an invertible form, and on the operator. -/
private theorem ContinuousAt.bilinAdjoint [CompleteSpace E] {X : Type*} [TopologicalSpace X]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {T : X → E →L[ℝ] E} {x : X} (hBx : (B x).IsInvertible)
    (hB : ContinuousAt B x) (hT : ContinuousAt T x) :
    ContinuousAt (fun x ↦ bilinAdjoint (B x) (T x)) x :=
  (ContinuousAt.comp (g := ContinuousLinearMap.inverse) (f := B)
    (hBx.contDiffAt_map_inverse (n := 0)).continuousAt hB).clm_comp
    ((((ContinuousLinearMap.compL ℝ E E ℝ).flip).continuous.continuousAt.comp hT).clm_comp hB)

end Adjoint

section Comp

omit [CompleteSpace E] [CompleteSpace E'] in
/-- The second derivative of `f ∘ L` for a linear equivalence `L`. -/
private theorem fderiv_fderiv_comp_equiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (L : E' ≃L[ℝ] E) (y w w' : E') :
    fderiv ℝ (fderiv ℝ (f ∘ L)) y w w' = fderiv ℝ (fderiv ℝ f) (L y) (L w) (L w') := by
  have hL : fderiv ℝ L = fun _ ↦ (L : E' →L[ℝ] E) := funext fun _ ↦ L.fderiv
  simp [fderiv_fderiv_comp_apply hf.contDiffAt L.contDiff.contDiffAt, hL]

omit [CompleteSpace E] [CompleteSpace E'] in
/-- The comparison operator is natural under linear changes of coordinates. -/
private theorem comparison_comp {f : E → ℝ} (hf : ContDiff ℝ 2 f) (L : E' ≃L[ℝ] E) (v : E') :
    comparison (f ∘ L) v = ((L.symm : E →L[ℝ] E').comp (comparison f (L v))).comp
      (L : E' →L[ℝ] E) := by
  -- Precomposition with `L` identifies the dual spaces.
  let L' : (E →L[ℝ] ℝ) ≃L[ℝ] (E' →L[ℝ] ℝ) := L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hL' (φ : E →L[ℝ] ℝ) (w : E') : L' φ w = φ (L w) := rfl
  have hH : fderiv ℝ (fderiv ℝ (f ∘ L)) 0 =
      (L' : (E →L[ℝ] ℝ) →L[ℝ] (E' →L[ℝ] ℝ)).comp
        ((fderiv ℝ (fderiv ℝ f) 0).comp (L : E' →L[ℝ] E)) := by
    ext w w'
    simp [fderiv_fderiv_comp_equiv_apply hf, hL']
  have hA : hessianAverage (f ∘ L) 0 v =
      (L' : (E →L[ℝ] ℝ) →L[ℝ] (E' →L[ℝ] ℝ)).comp
        ((hessianAverage f 0 (L v)).comp (L : E' →L[ℝ] E)) := by
    ext w w'
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hL',
      hessianAverage_apply (hf.comp L.contDiff), hessianAverage_apply hf]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp [fderiv_fderiv_comp_equiv_apply hf]
  rw [comparison, comparison, hH, hA, ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv]
  ext w
  simp

end Comp

section Parametric

variable {F : P × E → ℝ} {b₀ : P} {n : ℕ∞}

omit [CompleteSpace E] in
/-- The vertical Hessian of a jointly `C^{n+2}` family along its zero section is `C^n` in the
base. -/
private theorem contDiff_fderiv_fderiv_slice (hF : ContDiff ℝ (n + 2) F) :
    ContDiff ℝ n (fun b : P ↦ fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0) := by
  have h := (contDiff_hessianAverage_param hF 0).comp
    (contDiff_id.prodMk contDiff_const : ContDiff ℝ n fun b : P ↦ (b, (0 : E)))
  simpa [Function.comp_def] using h

private theorem contDiffAt_comparison (hF : ContDiff ℝ (n + 2) F) {z : P × E}
    (hz : (fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0).IsInvertible) :
    ContDiffAt ℝ n (fun z : P × E ↦ comparison (fun v ↦ F (z.1, v)) z.2) z := by
  have hH := (contDiff_fderiv_fderiv_slice hF).comp (contDiff_fst (E := P) (F := E))
  exact (hz.contDiffAt_map_inverse.comp z hH.contDiffAt).clm_comp
    (contDiff_hessianAverage_param hF 0).contDiffAt

private theorem continuousAt_comparison (hF : ContDiff ℝ 2 F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    ContinuousAt (fun z : P × E ↦ comparison (fun v ↦ F (z.1, v)) z.2) (b₀, 0) :=
  (contDiffAt_comparison (F := F) (n := 0) (by simpa using hF) hH).continuousAt

private theorem tendsto_comparison (hF : ContDiff ℝ 2 F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    Tendsto (fun z : P × E ↦ comparison (fun v ↦ F (z.1, v)) z.2) (𝓝 (b₀, 0)) (𝓝 1) := by
  simpa [comparison_zero hH] using (continuousAt_comparison hF hH).tendsto

private theorem eventually_isInvertible_fderiv_fderiv_slice (hF : ContDiff ℝ 2 F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    ∀ᶠ b in 𝓝 b₀, (fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0).IsInvertible :=
  ((contDiff_fderiv_fderiv_slice (n := 0) (by simpa using hF)).continuous.tendsto b₀).eventually
    hH.eventually_nhds

/-- **Regularity of the Morse–Palais operator.** For a jointly `C^{n+2}` family `F (b, v)` whose
vertical Hessian at `(b₀, 0)` is invertible, the fibrewise Morse–Palais operator is `C^n` at every
point near `(b₀, 0)`. -/
theorem eventually_contDiffAt_morsePalaisOperator (hF : ContDiff ℝ (n + 2) F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (b₀, (0 : E)),
      ContDiffAt ℝ n (fun z : P × E ↦ morsePalaisOperator (fun v ↦ F (z.1, v)) z.2) z := by
  have hF₂ : ContDiff ℝ 2 F := hF.of_le (by simp)
  have han : ∀ᶠ z in 𝓝 (b₀, (0 : E)),
      AnalyticAt ℝ (sqrtNearOne (E →L[ℝ] E)) (comparison (fun v ↦ F (z.1, v)) z.2) :=
    (tendsto_comparison hF₂ hH).eventually
      ((isOpen_analyticAt ℝ _).mem_nhds analyticAt_sqrtNearOne)
  filter_upwards [han, continuousAt_fst.eventually
    (eventually_isInvertible_fderiv_fderiv_slice hF₂ hH)] with z hz hzH
  simp only [morsePalaisOperator_eq_comparison]
  exact hz.contDiffAt.comp z (contDiffAt_comparison hF hzH)

/-- **The Morse–Palais congruence.** For a jointly `C²` family `F (b, v)` whose vertical Hessian
at `(b₀, 0)` is invertible, near `(b₀, 0)` the fibrewise Morse–Palais operator `R` is a
congruence from the vertical Hessian `H_b` at `(b, 0)` to the averaged Hessian:
`H_b (R w) (R w') = hessianAverage (F (b, ·)) 0 v w w'`. -/
theorem eventually_morsePalaisOperator_congruence (hF : ContDiff ℝ 2 F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (b₀, (0 : E)), ∀ w w',
      fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
          (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 w)
          (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 w') =
        hessianAverage (fun v ↦ F (z.1, v)) 0 z.2 w w' := by
  set H : P → E →L[ℝ] E →L[ℝ] ℝ := fun b ↦ fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0 with hHdef
  set C : P × E → E →L[ℝ] E := fun z ↦ comparison (fun v ↦ F (z.1, v)) z.2 with hCdef
  have hslice (b : P) : ContDiff ℝ 2 (fun v ↦ F (b, v)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hHsymm (b : P) (w w' : E) : H b w w' = H b w' w := by
    simpa using hessianAverage_symm (hslice b) 0 0 w w'
  have hCapply {z : P × E} (hz : (H z.1).IsInvertible) (w w' : E) :
      H z.1 (C z w) w' = hessianAverage (fun v ↦ F (z.1, v)) 0 z.2 w w' := by
    rw [fderiv_fderiv_apply_comparison hz]
  have hHev : ∀ᶠ z in 𝓝 (b₀, (0 : E)), (H z.1).IsInvertible :=
    continuousAt_fst.eventually (eventually_isInvertible_fderiv_fderiv_slice hF hH)
  -- The comparison operator is self-adjoint for `H b`, and the adjoint of its square root tends
  -- to the identity, so by uniqueness that square root is self-adjoint too.
  have hCadj : ∀ᶠ z in 𝓝 (b₀, (0 : E)), bilinAdjoint (H z.1) (C z) = C z := by
    filter_upwards [hHev] with z hz
    refine eq_of_forall_bilin_apply hz fun w w' ↦ ?_
    rw [bilinAdjoint_apply hz, hCapply hz, hHsymm, hCapply hz, hessianAverage_symm (hslice z.1)]
  have hroot : ContinuousAt (fun z ↦ sqrtNearOne (E →L[ℝ] E) (C z)) (b₀, 0) :=
    ContinuousAt.comp (by simpa [hCdef, comparison_zero hH] using continuousAt_sqrtNearOne)
      (continuousAt_comparison hF hH)
  have hadj : Tendsto (fun z : P × E ↦ bilinAdjoint (H z.1) (sqrtNearOne (E →L[ℝ] E) (C z)))
      (𝓝 (b₀, 0)) (𝓝 1) := by
    have hHcont : ContinuousAt (fun z : P × E ↦ H z.1) (b₀, 0) :=
      ((contDiff_fderiv_fderiv_slice (n := 0) (by simpa using hF)).continuous.comp
        continuous_fst).continuousAt
    have h1 : bilinAdjoint (H b₀) 1 = 1 := bilinAdjoint_one hH
    simpa [hCdef, comparison_zero hH, h1] using
      (ContinuousAt.bilinAdjoint (B := fun z : P × E ↦ H z.1) hH hHcont hroot).tendsto
  filter_upwards [hHev, hCadj, eventually_map_sqrtNearOne
    (hHev.mono fun z hz ↦ bilinAdjoint_mul_self hz) (tendsto_comparison hF hH) hadj,
    (tendsto_comparison hF hH).eventually eventually_mul_self_sqrtNearOne] with z hz hzC hroot hmul
    w w'
  rw [hzC] at hroot
  -- `R * R = C z` and `H (C z ·) = A`.
  simp only [morsePalaisOperator_eq_comparison]
  set R := sqrtNearOne (E →L[ℝ] E) (C z)
  calc H z.1 (R w) (R w') = H z.1 (bilinAdjoint (H z.1) R w) (R w') := by rw [hroot]
    _ = H z.1 w ((R * R) w') := by rw [bilinAdjoint_apply hz, mul_apply_eq_comp]
    _ = hessianAverage (fun v ↦ F (z.1, v)) 0 z.2 w w' := by
      rw [hmul, hHsymm, hCapply hz, hessianAverage_symm (hslice z.1)]

/-- **The parametric Morse normal form, with the canonical operator.** Let `F (b, v)` be a jointly
`C²` family whose zero section is critical in the fibre direction near `b₀` and whose vertical
Hessian at `(b₀, 0)` is invertible. Then near `(b₀, 0)`,
`F (b, v) = F (b, 0) + ½ H_b (R v) (R v)`, where `R` is the fibrewise Morse–Palais operator and
`H_b` is the vertical Hessian at `(b, 0)`. -/
theorem eventually_eq_add_morsePalaisOperator (hF : ContDiff ℝ 2 F)
    (hcrit : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (b₀, (0 : E)), F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
        (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2)
        (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2) := by
  filter_upwards [eventually_morsePalaisOperator_congruence hF hH,
    continuousAt_fst.eventually hcrit] with z hz hzcrit
  have ht := map_add_eq_add_hessianAverage (f := fun v ↦ F (z.1, v))
    (hF.comp (contDiff_const.prodMk contDiff_id)) 0 z.2
  rw [hz]
  simpa only [zero_add, hzcrit, zero_apply, add_zero, smul_eq_mul,
    Prod.mk.eta] using ht

/-- **Naturality of the Morse–Palais operator.** Let `F (b, v)` be a jointly `C²` family whose
vertical Hessian at `(b₀, 0)` is invertible, and let `L b : E' ≃L[ℝ] E` be linear changes of
fibre coordinates, continuous at `b₀`. Near `(b₀, 0)`, the
Morse–Palais operator of the family `(b, v') ↦ F (b, L b v')` is the conjugate
`(L b)⁻¹ ∘ R (b, L b v') ∘ L b` of the operator `R` of `F`. -/
theorem eventually_morsePalaisOperator_comp (hF : ContDiff ℝ 2 F)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) {L : P → E' ≃L[ℝ] E}
    (hL : ContinuousAt (fun b ↦ (L b : E' →L[ℝ] E)) b₀) :
    ∀ᶠ z in 𝓝 (b₀, (0 : E')),
      morsePalaisOperator (fun v ↦ F (z.1, L z.1 v)) z.2 =
        (((L z.1).symm : E →L[ℝ] E').comp
          (morsePalaisOperator (fun v ↦ F (z.1, v)) (L z.1 z.2))).comp (L z.1 : E' →L[ℝ] E) := by
  have hslice (b : P) : ContDiff ℝ 2 (fun v ↦ F (b, v)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  -- conjugation by `L b`
  let φ : P × E' → (E →L[ℝ] E) → (E' →L[ℝ] E') := fun z T ↦
    (((L z.1).symm : E →L[ℝ] E').comp T).comp (L z.1 : E' →L[ℝ] E)
  let x : P × E' → E →L[ℝ] E := fun z ↦ comparison (fun v ↦ F (z.1, v)) (L z.1 z.2)
  have hLc : ContinuousAt (fun z : P × E' ↦ (L z.1 : E' →L[ℝ] E)) (b₀, 0) :=
    ContinuousAt.comp (g := fun b ↦ (L b : E' →L[ℝ] E)) hL continuousAt_fst
  -- the inverses are continuous, since inversion is continuous at invertible maps
  have hL' : ContinuousAt (fun b ↦ ((L b).symm : E →L[ℝ] E')) b₀ := by
    simpa [Function.comp_def, ContinuousLinearMap.inverse_equiv] using
      ContinuousAt.comp (g := ContinuousLinearMap.inverse)
        (f := fun b ↦ (L b : E' →L[ℝ] E)) (contDiffAt_map_inverse (n := 0) (L b₀)).continuousAt hL
  have hL'c : ContinuousAt (fun z : P × E' ↦ ((L z.1).symm : E →L[ℝ] E')) (b₀, 0) :=
    ContinuousAt.comp (g := fun b ↦ ((L b).symm : E →L[ℝ] E')) hL' continuousAt_fst
  have hg : ContinuousAt (fun z : P × E' ↦ (z.1, L z.1 z.2)) (b₀, 0) :=
    continuousAt_fst.prodMk (hLc.clm_apply continuousAt_snd)
  have hx : ContinuousAt x (b₀, 0) := by
    refine ContinuousAt.comp (g := fun z : P × E ↦ comparison (fun v ↦ F (z.1, v)) z.2)
      (f := fun z : P × E' ↦ (z.1, L z.1 z.2)) ?_ hg
    simpa using continuousAt_comparison hF hH
  have hx₀ : x (b₀, 0) = 1 := by simpa [x] using comparison_zero hH
  have hxt : Tendsto x (𝓝 (b₀, 0)) (𝓝 1) := hx₀ ▸ hx.tendsto
  have hsq : ∀ᶠ z in 𝓝 (b₀, (0 : E')), ∀ T, φ z (T * T) = φ z T * φ z T :=
    Eventually.of_forall fun z T ↦ by ext w; simp [φ]
  have hφ : Tendsto (fun z ↦ φ z (sqrtNearOne (E →L[ℝ] E) (x z))) (𝓝 (b₀, 0)) (𝓝 1) := by
    have hroot : ContinuousAt (fun z ↦ sqrtNearOne (E →L[ℝ] E) (x z)) (b₀, 0) :=
      ContinuousAt.comp (g := sqrtNearOne (E →L[ℝ] E)) (by rw [hx₀]; exact continuousAt_sqrtNearOne)
        hx
    have hc : ContinuousAt (fun z ↦ φ z (sqrtNearOne (E →L[ℝ] E) (x z))) (b₀, 0) :=
      (hL'c.clm_comp hroot).clm_comp hLc
    have h1 : φ (b₀, 0) (sqrtNearOne (E →L[ℝ] E) (x (b₀, 0))) = 1 := by
      ext w
      simp [φ, hx₀]
    simpa [h1] using hc.tendsto
  filter_upwards [eventually_map_sqrtNearOne hsq hxt hφ] with z hz
  have hfun : (fun v ↦ F (z.1, L z.1 v)) = (fun v ↦ F (z.1, v)) ∘ L z.1 := rfl
  rw [morsePalaisOperator_eq_comparison, morsePalaisOperator_eq_comparison, hfun,
    comparison_comp (hslice z.1)]
  exact hz.symm

end Parametric

section Chart

/-- For a jointly `C^{n+2}` family, with `1 ≤ n ≤ ∞`, the map `z ↦ (z.1, R z z.2)` given by the
fibrewise Morse–Palais operator is a `C^n` local diffeomorphism at each point `(b₀, 0)` of the zero
section with invertible vertical Hessian. -/
private theorem exists_partialDiffeomorph_morsePalaisOperator [CompleteSpace P] {G : P × E → ℝ}
    {b₀ : P} {n : ℕ∞} (hG : ContDiff ℝ (n + 2) G)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ G (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ Θ : PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n,
      (b₀, (0 : E)) ∈ Θ.source ∧
      ∀ z ∈ Θ.source, Θ z = (z.1, morsePalaisOperator (fun v ↦ G (z.1, v)) z.2 z.2) := by
  set R : P × E → E →L[ℝ] E := fun z ↦ morsePalaisOperator (fun v ↦ G (z.1, v)) z.2 with hRdef
  set Φ : P × E → P × E := fun z ↦ (z.1, R z z.2) with hΦdef
  obtain ⟨s, hsR, hs, hb₀s⟩ := mem_nhds_iff.mp (eventually_contDiffAt_morsePalaisOperator hG hH)
  have hΦs : ContDiffOn ℝ n Φ s := fun z hz ↦
    (contDiffAt_fst.prodMk ((hsR hz).clm_apply contDiffAt_snd)).contDiffWithinAt
  -- `Φ` has derivative the identity at `(b₀, 0)`, since `R (b₀, 0) = 1`.
  have hR₀ : R (b₀, 0) = 1 := morsePalaisOperator_zero hH
  have hd : HasFDerivAt (fun z : P × E ↦ R z z.2)
      ((R (b₀, 0)).comp (ContinuousLinearMap.snd ℝ P E) + (fderiv ℝ R (b₀, 0)).flip 0)
      (b₀, 0) :=
    ((hsR hb₀s).differentiableAt (by simpa using hn : ((n : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt.clm_apply
      hasFDerivAt_snd
  have hΦd : HasFDerivAt Φ (ContinuousLinearMap.id ℝ (P × E)) (b₀, 0) := by
    convert hasFDerivAt_fst.prodMk hd using 1
    ext z <;> simp [hR₀]
  obtain ⟨Θ, hΘ, hb₀Θ, hΘs, hΘsymm⟩ := ContDiffOn.exists_openPartialHomeomorph hΦs hs hb₀s
    (ENat.one_le_iff_ne_zero_withTop.2 (by simpa using hn))
    (e := ContinuousLinearEquiv.refl ℝ (P × E)) hΦd.fderiv.symm
  refine ⟨{ toPartialEquiv := Θ.toPartialEquiv
            open_source := Θ.open_source
            open_target := Θ.open_target
            contMDiffOn_toFun := (hΘ ▸ hΦs.mono hΘs).contMDiffOn
            contMDiffOn_invFun := hΘsymm.contMDiffOn }, hb₀Θ, fun z _ ↦ ?_⟩
  -- the partial diffeomorphism just built has the forward map of `Θ`
  exact (by rw [hΘ] : Θ z = Φ z)

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] {F : P × E → ℝ} {W : Set (P × E)}
  {U : Set P} {n : ℕ∞}

/-- The local step of `TauCeti.exists_morsePalaisOperator_chart`: near a point `(b₀, 0)` of the
zero section, on a product of an open set `U₀ ∋ b₀` with a ball, the map
`z ↦ (z.1, R z z.2)` is a `C^n` partial diffeomorphism and `F` is in normal form. -/
private theorem exists_morsePalaisOperator_local (hW : IsOpen W) (hF : ContDiffOn ℝ (n + 2) F W)
    (hU : IsOpen U) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    {b₀ : P} (hb₀ : b₀ ∈ U) (hb₀W : (b₀, (0 : E)) ∈ W)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (U₀ : Set P) (r : ℝ) (Θ : PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n),
      IsOpen U₀ ∧ b₀ ∈ U₀ ∧ 0 < r ∧ Θ.source = U₀ ×ˢ Metric.ball 0 r ∧
      U₀ ×ˢ Metric.ball 0 r ⊆ W ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r,
        Θ z = (z.1, morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2)) ∧
      ∀ z ∈ U₀ ×ˢ Metric.ball 0 r, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
          (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2)
          (morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2) := by
  -- Replace `F` by a globally `C^{n+2}` function `G` agreeing with it near `(b₀, 0)`.
  obtain ⟨G, hG, -, hGF⟩ := hF.exists_contDiff_eventuallyEq_of_finiteDimensional
    (hW.mem_nhds hb₀W)
  obtain ⟨U₁, V₁, hU₁, hb₀U₁, hV₁, h0V₁, hUV₁⟩ := mem_nhds_prod_iff'.mp hGF
  have hslice {b : P} (hb : b ∈ U₁) : (fun v ↦ G (b, v)) =ᶠ[𝓝 0] fun v ↦ F (b, v) :=
    Filter.mem_of_superset (hV₁.mem_nhds h0V₁) fun v hv ↦ hUV₁ (mk_mem_prod hb hv)
  have hHG {b : P} (hb : b ∈ U₁) : fderiv ℝ (fderiv ℝ (fun v ↦ G (b, v))) 0 =
      fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0 :=
    (hslice hb).fderiv.fderiv_eq
  have hHG₀ : (fderiv ℝ (fderiv ℝ (fun v ↦ G (b₀, v))) 0).IsInvertible := by
    rwa [hHG hb₀U₁]
  have hcritG : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ G (b, v)) 0 = 0 := by
    filter_upwards [hU₁.mem_nhds hb₀U₁, hU.mem_nhds hb₀] with b hb hbU
    rw [(hslice hb).fderiv_eq, hcrit b hbU]
  obtain ⟨Θ, hb₀Θ, hΘ⟩ := exists_partialDiffeomorph_morsePalaisOperator hG hHG₀ hn
  -- Shrink to a product of an open set with a ball on which `G = F` and the normal form holds.
  have hmem : (Θ.source ∩ W) ∩ (U₁ ×ˢ V₁ ∩ {z | G z = G (z.1, 0) + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ (fun v ↦ G (z.1, v))) 0
        (morsePalaisOperator (fun v ↦ G (z.1, v)) z.2 z.2)
        (morsePalaisOperator (fun v ↦ G (z.1, v)) z.2 z.2)}) ∈ 𝓝 (b₀, (0 : E)) :=
    Filter.inter_mem (Filter.inter_mem (Θ.open_source.mem_nhds hb₀Θ) (hW.mem_nhds hb₀W))
      (Filter.inter_mem ((hU₁.prod hV₁).mem_nhds ⟨hb₀U₁, h0V₁⟩)
        (eventually_eq_add_morsePalaisOperator (hG.of_le (by simp)) hcritG hHG₀))
  obtain ⟨U₀, V₀, hU₀, hb₀U₀, hV₀, h0V₀, hUV₀⟩ := mem_nhds_prod_iff'.mp hmem
  obtain ⟨r, hr, hrV₀⟩ := Metric.isOpen_iff.mp hV₀ 0 h0V₀
  have hsub : U₀ ×ˢ Metric.ball 0 r ⊆ U₀ ×ˢ V₀ := prod_mono le_rfl hrV₀
  -- On this product the operators of `F` and `G` agree, and so do their vertical Hessians.
  have hRF {z : P × E} (hz : z ∈ U₀ ×ˢ Metric.ball 0 r) :
      morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 =
        morsePalaisOperator (fun v ↦ G (z.1, v)) z.2 := by
    refine morsePalaisOperator_congr_of_eqOn Metric.isOpen_ball
      ((convex_ball 0 r).starConvex (Metric.mem_ball_self hr)) (fun v hv ↦ ?_) hz.2
    exact (hUV₁ (hUV₀ (hsub (mk_mem_prod hz.1 hv))).2.1).symm
  have hzero {b : P} (hb : b ∈ U₀) : (b, (0 : E)) ∈ U₀ ×ˢ Metric.ball 0 r :=
    mk_mem_prod hb (Metric.mem_ball_self hr)
  have hprod : IsOpen (U₀ ×ˢ Metric.ball (0 : E) r) := hU₀.prod Metric.isOpen_ball
  refine ⟨U₀, r, Θ.restrOpen _ hprod, hU₀, hb₀U₀, hr, ?_, fun z hz ↦ (hUV₀ (hsub hz)).1.2,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact inter_eq_right.mpr fun z hz ↦ (hUV₀ (hsub hz)).1.1
  · rw [PartialDiffeomorph.coe_restrOpen, hΘ z (hUV₀ (hsub hz)).1.1, hRF hz]
  · have hz' := hUV₀ (hsub hz)
    have hz₀ := hUV₀ (hsub (hzero hz.1))
    rw [hRF hz, ← hUV₁ hz'.2.1, ← hUV₁ hz₀.2.1, ← hHG hz₀.2.1.1]
    exact hz'.2.2

/-- **The parametric Morse lemma along the whole zero section.** Let `F (b, v)` be `C^{n+2}`, with
`1 ≤ n ≤ ∞`, on an open set `W` containing the zero section over an open set `U` of the base,
with critical zero section and invertible vertical Hessian `H_b` at every `(b, 0)`, `b ∈ U`.
Then there is a single chart `ψ`, `C^n` in both directions and with source in `W` containing the
whole zero section over `U`, which is given on its source by the canonical Morse–Palais operator,
`ψ (b, v) = (b, R (b, v) v)`, preserves the base in both directions, and puts `F` in normal form:
`F (b, v) = F (b, 0) + ½ H_b (ψ (b, v)).2 (ψ (b, v)).2`. -/
theorem exists_morsePalaisOperator_chart (hW : IsOpen W) (hF : ContDiffOn ℝ (n + 2) F W)
    (hU : IsOpen U) (hUW : ∀ b ∈ U, (b, (0 : E)) ∈ W)
    (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : ∀ b ∈ U, (fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph (P × E) (P × E),
      ψ.source ⊆ W ∧ (∀ b ∈ U, (b, (0 : E)) ∈ ψ.source) ∧
      (∀ z ∈ ψ.source, ψ z = (z.1, morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  have : Nonempty (PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n) :=
    ⟨(Diffeomorph.refl 𝓘(ℝ, P × E) (P × E) n).toPartialDiffeomorph⟩
  choose! U₀ r Θ hU₀ hbU₀ hr hΘsource hsubW hΘeq hnf using fun b (hb : b ∈ U) ↦
    exists_morsePalaisOperator_local hW hF hU hcrit hb (hUW b hb) (hH b hb) hn
  set Φ : P × E → P × E := fun z ↦ (z.1, morsePalaisOperator (fun v ↦ F (z.1, v)) z.2 z.2)
    with hΦdef
  set S : Set (P × E) := ⋃ b ∈ U, U₀ b ×ˢ Metric.ball 0 (r b) with hSdef
  have hS : IsOpen S :=
    isOpen_biUnion fun b hb ↦ (hU₀ b hb).prod Metric.isOpen_ball
  have hmemS {z : P × E} : z ∈ S ↔ ∃ b ∈ U, z ∈ U₀ b ×ˢ Metric.ball 0 (r b) := by
    simp only [hSdef, mem_iUnion, exists_prop]
  -- On each product piece, `Φ` is the partial diffeomorphism `Θ b`.
  have hΦΘ {b : P} (hb : b ∈ U) {z : P × E} (hz : z ∈ U₀ b ×ˢ Metric.ball 0 (r b)) :
      Φ z = Θ b z := (hΘeq b hb z hz).symm
  -- The fibres of the pieces are nested balls about `0`, so `Φ` is injective on their union.
  have hinj : InjOn Φ S := by
    intro z hz z' hz' h
    obtain ⟨b, hb, hzb⟩ := hmemS.mp hz
    obtain ⟨b', hb', hzb'⟩ := hmemS.mp hz'
    have h1 : z.1 = z'.1 := by simpa [hΦdef] using congrArg Prod.fst h
    wlog hle : r b ≤ r b' generalizing z z' b b'
    · exact (this hz' hz h.symm b' hb' hzb' b hb hzb h1.symm (le_of_not_ge hle)).symm
    have hzb'' : z ∈ U₀ b' ×ˢ Metric.ball 0 (r b') :=
      ⟨h1 ▸ hzb'.1, Metric.ball_subset_ball hle hzb.2⟩
    refine (Θ b').toPartialEquiv.injOn (hΘsource b' hb' ▸ hzb'') (hΘsource b' hb' ▸ hzb') ?_
    rw [← hΦΘ hb' hzb'', ← hΦΘ hb' hzb', h]
  have hld : IsLocalDiffeomorphOn 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) n Φ S := fun ⟨z, hz⟩ ↦ by
    obtain ⟨b, hb, hzb⟩ := hmemS.mp hz
    exact isLocalDiffeomorphAt_of_eqOn (hΘsource b hb ▸ hzb) fun z' hz' ↦
      hΦΘ hb (hΘsource b hb ▸ hz')
  have : Nonempty (P × E) := ⟨0⟩
  let ψ := (hld.partialDiffeomorphOfInjOn hS hinj).toOpenPartialHomeomorph
  have hψ : (ψ : P × E → P × E) = Φ := by
    simp only [ψ, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn]
  have hψsource : ψ.source = S := by
    simp only [ψ, PartialDiffeomorph.toOpenPartialHomeomorph_source,
      IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]
  refine ⟨ψ, fun z hz ↦ ?_, fun b hb ↦ ?_, fun z _ ↦ by rw [hψ], fun z hz ↦ ?_,
    (hld.partialDiffeomorphOfInjOn hS hinj).contMDiffOn_toFun.contDiffOn,
    (hld.partialDiffeomorphOfInjOn hS hinj).contMDiffOn_invFun.contDiffOn, fun z hz ↦ ?_⟩
  · obtain ⟨b, hb, hzb⟩ := hmemS.mp (hψsource ▸ hz)
    exact hsubW b hb hzb
  · rw [hψsource]
    exact hmemS.mpr ⟨b, hb, hbU₀ b hb, Metric.mem_ball_self (hr b hb)⟩
  · -- the first coordinate of `ψ (ψ.symm z) = z` is that of `ψ.symm z`
    have h := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ] at h
  · obtain ⟨b, hb, hzb⟩ := hmemS.mp (hψsource ▸ hz)
    rw [hψ]
    exact hnf b hb z hzb

end Chart

end TauCeti
