/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Model

/-!
# Changes of chart of the normal model

Let `C` be an embedded pseudoholomorphic curve in an almost complex four-manifold with complex
normal line `N_C`. Over a holomorphic chart `z` of `C` and in a frame of `N_C` with fibre
coordinate `w`, the real normal Cauchy–Riemann operator reads `D s = ∂bar s + ν s + μ conj s`, and
the normal model `J_N` on `ℂ × ℂ` is `TauCeti.normalModelStructure ν μ`. A second chart `z'` and
frame `w'` of `N_C` are related to the first by

`T(z', w') = (φ z', g z' * w')`,

with `φ` a holomorphic change of base coordinate and `g` a nowhere-vanishing change of frame. This
file computes how `J_N` transforms under `T`: the local structures `J_N` of two charts of `N_C`
agree on their overlap exactly when `T` is holomorphic between them, and this is the transformation
law of the coefficients of `D`. With `φ'` the complex derivative of `φ` and
`∂bar g = TauCeti.conjWirtingerDeriv g z' 1`, the map `T` is holomorphic from `J_N(ν', μ')` to
`J_N(ν, μ)` at `(z', w')` exactly when

`g (ν' w' + μ' conj w') - ∂bar g w' = conj φ' (ν(φ z') g w' + μ(φ z') conj (g w'))`

(`TauCeti.isJHolomorphicAt_prodMk_mul_normalModelStructure_iff`), and it is holomorphic
everywhere exactly when

`g ν' - ∂bar g = conj φ' (ν ∘ φ) g`  and  `g μ' = conj φ' (μ ∘ φ) conj g`

at every point (`TauCeti.isJHolomorphic_prodMk_mul_normalModelStructure_iff`). These are the
laws by which the coefficients of `D` change when a section `s` of the first chart is written as
`s ∘ φ = g s'` in the second. Two special cases:

* a **change of normal frame** `w ↦ g(z) w` carries `J_N(ν, μ)` to `J_N(ν', μ')` with
  `ν' = ν - g⁻¹ ∂bar g` and `μ' = (g / conj g) μ`
  (`TauCeti.isJHolomorphic_prodMk_fst_mul_normalModelStructure`);
* a **holomorphic change of base coordinate** `z = φ(z')` carries `J_N(ν', μ')` to `J_N(ν, μ)`
  with `ν' = conj φ' (ν ∘ φ)` and `μ' = conj φ' (μ ∘ φ)`, the law of the `(0,1)`-form
  coefficients of `D` (`TauCeti.isJHolomorphic_prodMap_normalModelStructure`).

The primitive `λ_A(z, w)(ξ, η) = (ω(w, η) + |w|² A(z) ξ) / 2` of the taming form of the normal
model (`TauCeti.normalModelPrimitive`) transforms as a connection form. If `g` has unit modulus at
`z'`, the pullback of `λ_A` by `T` at `(z', w')` is `λ_{A'}` with
`A'(z') ξ = A(φ z')(φ' ξ) + Im (conj (g z') dg(ξ))`
(`TauCeti.normalModelPrimitive_compContinuousLinearMap_fderiv_prodMk_mul`). For `g = e^{iθ}` the
last term is `dθ`: the connection forms of a unitary connection in two unitary frames are related
in exactly this way, so the primitives `(ρ² / 2) (dθ + A)` written in the two charts agree.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (the linearized operator in local coordinates and frames).
-/

public section

namespace TauCeti

open Complex ComplexConjugate

variable {ν μ ν' μ' φ g : ℂ → ℂ} {φ' z : ℂ}

/-- The chart change `(z, w) ↦ (φ z, g z * w)` has the real derivative
`(ξ, η) ↦ (φ' ξ, dg(ξ) w + g z η)` at `(z, w)`. -/
private theorem exists_hasFDerivAt_chartChange (hφ : HasDerivAt φ φ' z)
    (hg : DifferentiableAt ℝ g z) (w : ℂ) :
    ∃ L : ℂ × ℂ →L[ℝ] ℂ × ℂ, HasFDerivAt (fun p : ℂ × ℂ ↦ (φ p.1, g p.1 * p.2)) L (z, w) ∧
      ∀ ξ : ℂ × ℂ, L ξ = (φ' * ξ.1, fderiv ℝ g z ξ.1 * w + g z * ξ.2) := by
  have h₁ : HasFDerivAt (fun p : ℂ × ℂ ↦ φ p.1) _ (z, w) :=
    (hφ.hasFDerivAt.restrictScalars ℝ).comp (z, w) hasFDerivAt_fst
  have h₂ : HasFDerivAt (fun p : ℂ × ℂ ↦ g p.1 * p.2) _ (z, w) :=
    (hg.hasFDerivAt.comp (z, w) hasFDerivAt_fst).mul hasFDerivAt_snd
  refine ⟨_, h₁.prodMk h₂, fun ξ ↦ ?_⟩
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_fst', smul_eq_mul,
    add_apply, smul_apply, ContinuousLinearMap.coe_snd', Function.comp_apply]
  refine Prod.ext (mul_comm _ _) ?_
  ring

/-- The complex linearity of the derivative of the chart change on a tangent vector `ξ` is the
coefficient law, multiplied by `2 I conj ξ.1`. -/
private theorem chartChange_apply_eq_iff (φ' : ℂ) (w : ℂ) (ξ : ℂ × ℂ) :
    (φ' * (I * ξ.1), fderiv ℝ g z (I * ξ.1) * w +
        g z * (I * ξ.2 + 2 * I * (ν' z * w + μ' z * conj w) * conj ξ.1)) =
      (I * (φ' * ξ.1), I * (fderiv ℝ g z ξ.1 * w + g z * ξ.2) +
        2 * I * (ν (φ z) * (g z * w) + μ (φ z) * conj (g z * w)) * conj (φ' * ξ.1)) ↔
      2 * I * conj ξ.1 * (g z * (ν' z * w + μ' z * conj w) - conjWirtingerDeriv g z 1 * w -
        conj φ' * (ν (φ z) * (g z * w) + μ (φ z) * conj (g z * w))) = 0 := by
  rw [Prod.ext_iff, fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
  simp only [smul_eq_mul, map_mul, conj_I]
  constructor
  · rintro ⟨-, h⟩
    linear_combination h
  · intro h
    exact ⟨by ring, by linear_combination h⟩

/-- **The chart-change criterion at a point.** Let `φ` have complex derivative `φ'` at `z` and let
`g` be real differentiable at `z`. The chart change `(z, w) ↦ (φ z, g z * w)` is holomorphic at
`(z, w)` from the normal model `J_N(ν', μ')` to `J_N(ν, μ)` exactly when

`g (ν' w + μ' conj w) - ∂bar g w = conj φ' (ν(φ z) g w + μ(φ z) conj (g w))`

at `z`, where `∂bar g = conjWirtingerDeriv g z 1`. -/
theorem isJHolomorphicAt_prodMk_mul_normalModelStructure_iff (hφ : HasDerivAt φ φ' z)
    (hg : DifferentiableAt ℝ g z) (w : ℂ) :
    IsJHolomorphicAt (normalModelStructure ν' μ') (normalModelStructure ν μ)
        (fun p ↦ (φ p.1, g p.1 * p.2)) (z, w) ↔
      g z * (ν' z * w + μ' z * conj w) - conjWirtingerDeriv g z 1 * w =
        conj φ' * (ν (φ z) * (g z * w) + μ (φ z) * conj (g z * w)) := by
  obtain ⟨L, hL, hLξ⟩ := exists_hasFDerivAt_chartChange hφ hg w
  have hlin : IsComplexLinearMap (normalModelStructure ν' μ' (z, w))
        (normalModelStructure ν μ (φ z, g z * w)) L.toLinearMap ↔
      ∀ ξ : ℂ × ℂ, 2 * I * conj ξ.1 * (g z * (ν' z * w + μ' z * conj w) -
        conjWirtingerDeriv g z 1 * w -
          conj φ' * (ν (φ z) * (g z * w) + μ (φ z) * conj (g z * w))) = 0 := by
    rw [isComplexLinearMap_iff_apply]
    refine forall_congr' fun ξ ↦ ?_
    simp only [ContinuousLinearMap.coe_coe, normalModelStructure_apply, hLξ]
    exact chartChange_apply_eq_iff φ' w ξ
  constructor
  · intro h
    have hc := h.derivative_isComplexLinear
    rw [h.hasFDerivAt.unique hL] at hc
    have h₁ := (hlin.1 hc) (1, 0)
    simp only [map_one, mul_one, mul_eq_zero, two_ne_zero, I_ne_zero, or_self, false_or,
      sub_eq_zero] at h₁
    exact h₁
  · intro h
    refine isJHolomorphicAt_of_hasFDerivAt hL (hlin.2 fun ξ ↦ ?_)
    rw [h, sub_self, mul_zero]

/-- **The chart-change criterion.** Let `φ` be holomorphic and `g` real differentiable. The chart
change `(z, w) ↦ (φ z, g z * w)` is holomorphic from the normal model `J_N(ν', μ')` to
`J_N(ν, μ)` exactly when, at every point `z`, with `∂bar g = conjWirtingerDeriv g z 1`,

`g ν' - ∂bar g = conj φ' (ν ∘ φ) g`  and  `g μ' = conj φ' (μ ∘ φ) conj g`.

These are the laws by which the coefficients of `∂bar s + ν s + μ conj s` change when the section
`s` is written in the frame and coordinate of the other chart. -/
theorem isJHolomorphic_prodMk_mul_normalModelStructure_iff (hφ : Differentiable ℂ φ)
    (hg : Differentiable ℝ g) :
    IsJHolomorphic (normalModelStructure ν' μ') (normalModelStructure ν μ)
        (fun p ↦ (φ p.1, g p.1 * p.2)) ↔
      ∀ z, g z * ν' z - conjWirtingerDeriv g z 1 = conj (deriv φ z) * ν (φ z) * g z ∧
        g z * μ' z = conj (deriv φ z) * μ (φ z) * conj (g z) := by
  simp only [isJHolomorphic_iff, Prod.forall,
    isJHolomorphicAt_prodMk_mul_normalModelStructure_iff (hφ _).hasDerivAt (hg _)]
  refine forall_congr' fun z ↦ ⟨fun h ↦ ?_, fun h w ↦ ?_⟩
  · -- the coefficient law at `w = 1` and `w = I` separates the two coefficients
    have h₁ := h 1
    have h₂ := h I
    simp only [map_mul, map_one, conj_I, mul_one] at h₁ h₂
    set Y := g z * ν' z - conj (deriv φ z) * ν (φ z) * g z - g z * μ' z -
      conjWirtingerDeriv g z 1 + conj (deriv φ z) * μ (φ z) * conj (g z)
    exact ⟨by linear_combination (h₁ - I * h₂) / 2 + Y / 2 * I_sq,
      by linear_combination (h₁ + I * h₂) / 2 - Y / 2 * I_sq⟩
  · simp only [map_mul]
    linear_combination w * h.1 + conj w * h.2

/-- **A change of normal frame.** For a real differentiable, nowhere-vanishing `g`, the frame
change `(z, w) ↦ (z, g z * w)` is holomorphic from the normal model `J_N(ν, μ)` to the normal model
of the coefficients `ν - g⁻¹ ∂bar g` and `(g / conj g) μ`. These are the coefficients of the normal
operator `∂bar s + ν s + μ conj s` written for the section `g s`. -/
theorem isJHolomorphic_prodMk_fst_mul_normalModelStructure (hg : Differentiable ℝ g)
    (hg₀ : ∀ z, g z ≠ 0) :
    IsJHolomorphic (normalModelStructure ν μ)
      (normalModelStructure (fun z ↦ ν z - conjWirtingerDeriv g z 1 / g z)
        (fun z ↦ g z / conj (g z) * μ z))
      (fun p ↦ (p.1, g p.1 * p.2)) := by
  refine (isJHolomorphic_prodMk_mul_normalModelStructure_iff (φ := id) differentiable_id
    hg).2 fun z ↦ ?_
  have hc : conj (g z) ≠ 0 := (map_ne_zero _).2 (hg₀ z)
  simp only [deriv_id, map_one, one_mul, id_eq]
  constructor <;> field_simp [hg₀ z, hc]

/-- **A holomorphic change of base coordinate.** For a holomorphic `φ`, the map
`(z, w) ↦ (φ z, w)` is holomorphic from the normal model of the coefficients
`conj φ' (ν ∘ φ)` and `conj φ' (μ ∘ φ)` to the normal model `J_N(ν, μ)`: the coefficients of the
normal operator transform as `(0,1)`-forms. -/
theorem isJHolomorphic_prodMap_normalModelStructure (hφ : Differentiable ℂ φ) :
    IsJHolomorphic
      (normalModelStructure (fun z ↦ conj (deriv φ z) * ν (φ z))
        (fun z ↦ conj (deriv φ z) * μ (φ z)))
      (normalModelStructure ν μ) (Prod.map φ id) := by
  have h := (isJHolomorphic_prodMk_mul_normalModelStructure_iff (g := fun _ ↦ 1)
    (ν' := fun z ↦ conj (deriv φ z) * ν (φ z)) (μ' := fun z ↦ conj (deriv φ z) * μ (φ z))
    (ν := ν) (μ := μ) hφ (differentiable_const 1)).2 fun z ↦ by
      have h₀ : conjWirtingerDeriv (fun _ : ℂ ↦ (1 : ℂ)) z 1 = 0 := by
        simp
      simp only [h₀, map_one]
      constructor <;> ring
  simp only [one_mul] at h
  exact h

/-- The area form of the fibre pulled back by a change of frame:
`ω(g w, d w + g η) = |w|² Im (conj g d) + |g|² ω(w, η)`. -/
private theorem stdComplexSymplecticForm_mul_mul_add_mul (g d w η : ℂ) :
    stdComplexSymplecticForm (g * w) (d * w + g * η) =
      ‖w‖ ^ 2 * (conj g * d).im + ‖g‖ ^ 2 * stdComplexSymplecticForm w η := by
  simp only [stdComplexSymplecticForm_apply, mul_re, mul_im, add_re, add_im, conj_re, conj_im,
    Complex.sq_norm, normSq_apply]
  ring

/-- **The taming primitive under a unitary change of chart.** Let `φ` have complex derivative
`φ'` at `z`, and let `g` be real differentiable at `z` with `|g z| = 1`. If the connection forms
`A` and `A'` on the base satisfy

`A'(z) ξ = A(φ z)(φ' ξ) + Im (conj (g z) dg(ξ))`,

then the chart change `T(z, w) = (φ z, g z * w)` pulls the primitive `λ_A` of the taming form of the
normal model back to `λ_{A'}` at `(z, w)`. For `g = e^{iθ}` the last term is `dθ`, the gauge
transformation of a unitary connection. -/
theorem normalModelPrimitive_compContinuousLinearMap_fderiv_prodMk_mul (hφ : HasDerivAt φ φ' z)
    (hg : DifferentiableAt ℝ g z) (hg₁ : ‖g z‖ = 1) {A A' : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ}
    (hA : ∀ ξ : ℂ,
      A' z (fun _ ↦ ξ) = A (φ z) (fun _ ↦ φ' * ξ) + (conj (g z) * fderiv ℝ g z ξ).im)
    (w : ℂ) :
    (normalModelPrimitive A (φ z, g z * w)).compContinuousLinearMap
        (fderiv ℝ (fun p : ℂ × ℂ ↦ (φ p.1, g p.1 * p.2)) (z, w)) =
      normalModelPrimitive A' (z, w) := by
  obtain ⟨L, hL, hLξ⟩ := exists_hasFDerivAt_chartChange hφ hg w
  ext v
  rw [hL.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply, normalModelPrimitive_apply,
    normalModelPrimitive_apply, Function.comp_apply, hLξ, hA,
    stdComplexSymplecticForm_mul_mul_add_mul, norm_mul, hg₁]
  ring

end TauCeti
