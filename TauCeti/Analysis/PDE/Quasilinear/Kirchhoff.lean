/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Calculus.IntervalIntegral.Inverse
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Quasilinear equations on an interval with a coefficient depending on the solution alone

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(u) u')' = f + F'` in `(x₀, x₁)`, `u(x₀) = g₀`, `u(x₁) = g₁`,

whose coefficient `A` is a continuous function of the value of `u` alone, with data `f ∈ L¹` and
`F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. As for general coefficients `A(x, u)`
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`), a solution is
`u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values and satisfies

`∫ A(ū t) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

For such coefficients **Kirchhoff's transformation** `Ψ(y) = ∫_0^y A` linearizes the problem:
`(Ψ ∘ ū)' = A(ū) ū'` is the flux, so `w = Ψ ∘ ū` solves the linear equation `-w'' = f + F'`. In
one dimension that equation integrates to `w(t) = w(x₀) + k (t - x₀) - ∫_{x₀}^t G` with
`G(r) = ∫_{x₀}^r f + F(r)` and a constant `k`
(`TauCeti.PDE.exists_forall_intervalIntegral_intervalRepresentativeL_eq`). This has two
consequences.

* **Uniqueness.** If `A > 0`, then `Ψ` is strictly increasing. The boundary values of `ū` fix
  those of `w`, hence `k`, hence `w` and `ū`: the problem has at most one solution
  (`TauCeti.PDE.eq_of_intervalTraceL_eq_of_forall_setIntegral_eq`).
* **Existence without an upper bound on `A`.** If `A ≥ λ > 0`, then `Ψ` is a bijection of `ℝ`
  whose inverse is `λ⁻¹`-Lipschitz. For the solution `w` of the linear problem with boundary values
  `Ψ(g₀)` and `Ψ(g₁)`, the function `Ψ⁻¹ ∘ w` is absolutely continuous with derivative
  `(k - G) / A(Ψ⁻¹ ∘ w)`, so it represents a solution. Hence the problem has exactly one solution
  (`TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq`). Coefficients such as
  `A(y) = 1 + y²`, which are not bounded above, are allowed; Schauder's fixed-point argument for
  coefficients `A(x, u)` needs a bound `A ≤ M`.

Uniqueness rests on the transformation, which has no analogue for coefficients `A(x, u)` that
depend on both variables; for those no uniqueness is claimed.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Distributions Topology

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ENNReal} [Fact (1 ≤ p)] {A f F : ℝ → ℝ}

/-- **Kirchhoff's transformation of a solution.** Let `A` be continuous and let `f` and `F` be
integrable on `(x₀, x₁)`. If `u ∈ W^{1,p}(x₀, x₁)` solves `-(A(u) u')' = f + F'` against test
functions, then `Ψ(y) = ∫_0^y A` turns its continuous representative `ū` into a solution of the
linear equation `-w'' = f + F'`: there is a constant `k` with

`Ψ(ū t) = Ψ(ū x₀) + k (t - x₀) - ∫_{x₀}^t (∫_{x₀}^r f + F r) dr` for every `t ∈ [x₀, x₁]`. -/
theorem exists_forall_intervalIntegral_intervalRepresentativeL_eq (hx : x₀ < x₁)
    (hA : Continuous A) (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ k, ∀ t : Icc x₀ x₁,
      ∫ y in 0..W1p.intervalRepresentativeL hx u t, A y =
        (∫ y in 0..W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩, A y) +
          k * (t - x₀) - ∫ r in x₀..t, ((∫ s in x₀..r, f s) + F r) := by
  set v : ℝ → ℝ := fun t ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t) with hv_def
  have hv : Continuous v := W1p.continuous_intervalRepresentativeL_projIcc hx u
  -- The flux `A(v) u' + F` is `k - ∫_{x₀}^t f`; the coefficient `A ∘ v` is bounded on `[x₀, x₁]`.
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.comp hv).continuousOn
    (s := Icc x₀ x₁)
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral (a := fun t ↦ A (v t))
    (hA.comp hv).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ hM t (Ioo_subset_Icc_self ht)) hf hF
    hu
  refine ⟨k, fun t ↦ ?_⟩
  have htI : (t : ℝ) ∈ uIcc x₀ x₁ := Icc_subset_uIcc t.property
  -- `Ψ ∘ v` is absolutely continuous on `[x₀, t]`, with derivative the flux `A(v) v' = k - G`.
  have hac : AbsolutelyContinuousOnInterval ((fun z ↦ ∫ s in 0..z, A s) ∘ v) x₀ t :=
    ((W1p.absolutelyContinuousOnInterval_intervalRepresentativeL hx u).mono
      (uIcc_subset_uIcc left_mem_uIcc htI)).comp_of_contDiffAt fun _ _ ↦
      (hA.contDiff_one_primitive 0).contDiffAt
  have hne : ∀ᵐ r ∂volume, r ≠ x₁ := by simp [ae_iff, measure_singleton]
  have hderiv : ∀ᵐ r, r ∈ uIoc x₀ (t : ℝ) →
      deriv ((fun z ↦ ∫ s in 0..z, A s) ∘ v) r = k - ((∫ s in x₀..r, f s) + F r) := by
    filter_upwards [W1p.ae_hasDerivAt_intervalRepresentativeL hx u,
      (ae_restrict_iff' measurableSet_Ioo).1 hk, hne] with r hr hkr hr₁ hrt
    rw [uIoc_of_le t.property.1] at hrt
    have hrI : r ∈ Ioo x₀ x₁ := ⟨hrt.1, lt_of_le_of_ne (hrt.2.trans t.property.2) hr₁⟩
    rw [((hA.integral_hasStrictDerivAt 0 (v r)).hasDerivAt.comp r
      (hr (uIoc_of_le hx.le ▸ Ioo_subset_Ioc_self hrI))).deriv]
    linarith [hkr hrI]
  have hG := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2
    (integrableOn_intervalIntegral_add hx hf hF)).mono_set
    (uIcc_subset_uIcc left_mem_uIcc htI)
  have h := hac.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv,
    intervalIntegral.integral_sub intervalIntegrable_const hG, intervalIntegral.integral_const,
    smul_eq_mul] at h
  have hvt : v t = W1p.intervalRepresentativeL hx u t := by
    simp only [hv_def, projIcc_of_mem hx.le t.property]
  have hv₀ : v x₀ = W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ := by
    simp only [hv_def, projIcc_left]
  simp only [Function.comp_apply, hvt, hv₀] at h
  linarith

/-- **Uniqueness for the quasilinear Dirichlet problem with a coefficient `A(u)`.** Let `A` be
continuous and positive, and let `f` and `F` be integrable on `(x₀, x₁)`. Two solutions
`u₁, u₂ ∈ W^{1,p}(x₀, x₁)` of `-(A(u) u')' = f + F'` with the same boundary values are equal. -/
theorem eq_of_intervalTraceL_eq_of_forall_setIntegral_eq (hx : x₀ < x₁) (hA : Continuous A)
    (hA₀ : ∀ y, 0 < A y) (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u₁ u₂ : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (htr : W1p.intervalTraceL hx u₁ = W1p.intervalTraceL hx u₂)
    (hu₁ : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u₁ (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u₁ t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (hu₂ : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u₂ (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u₂ t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    u₁ = u₂ := by
  obtain ⟨k₁, h₁⟩ := exists_forall_intervalIntegral_intervalRepresentativeL_eq hx hA hf hF hu₁
  obtain ⟨k₂, h₂⟩ := exists_forall_intervalIntegral_intervalRepresentativeL_eq hx hA hf hF hu₂
  have hΨ : StrictMono fun y ↦ ∫ s in 0..y, A s := strictMono_of_deriv_pos fun y ↦ by
    rw [hA.deriv_integral _ 0]
    exact hA₀ y
  rw [W1p.intervalTraceL_apply, W1p.intervalTraceL_apply, Prod.mk.injEq] at htr
  -- The two transforms agree at both endpoints, so their slopes `k₁` and `k₂` agree.
  have hk : k₁ = k₂ := by
    have e₁ := h₁ ⟨x₁, right_mem_Icc.2 hx.le⟩
    have e₂ := h₂ ⟨x₁, right_mem_Icc.2 hx.le⟩
    rw [htr.1, htr.2] at e₁
    exact mul_right_cancel₀ (sub_ne_zero.2 hx.ne') (by linarith)
  apply W1p.intervalRepresentativeL_injective hx
  ext t
  apply hΨ.injective
  simp only [h₁ t, h₂ t, htr.1, hk]

/-- **The candidate solution.** For a continuous coefficient `A ≥ λ > 0`, let `w` solve the linear
problem `-w'' = f + F'` with boundary values `Ψ(g₀)` and `Ψ(g₁)`, where `Ψ(y) = ∫_0^y A`. Then
`v = Ψ⁻¹ ∘ w` is absolutely continuous on `[x₀, x₁]`, takes the boundary values `g₀` and `g₁`, and
for a constant `k` has derivative `(k - G) / A(v)` almost everywhere, where
`G(r) = ∫_{x₀}^r f + F(r)`. -/
private theorem exists_absolutelyContinuousOnInterval_and_ae_hasDerivAt (hx : x₀ < x₁)
    {lam : ℝ} (hlam : 0 < lam) (hA : Continuous A) (hAlam : ∀ y, lam ≤ A y)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    ∃ (v : ℝ → ℝ) (k : ℝ), AbsolutelyContinuousOnInterval v x₀ x₁ ∧ v x₀ = g₀ ∧ v x₁ = g₁ ∧
      ∀ᵐ r, r ∈ Ioo x₀ x₁ →
        HasDerivAt v ((A (v r))⁻¹ * (k - ((∫ s in x₀..r, f s) + F r))) r := by
  obtain ⟨g, -, hglip, hgΨ, -, hgd⟩ :=
    TauCeti.exists_orderIso_contDiff_inverse_intervalIntegral hA hlam hAlam 0
  set G : ℝ → ℝ := fun r ↦ (∫ s in x₀..r, f s) + F r
  have hGi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2
    (integrableOn_intervalIntegral_add hx hf hF)
  -- The solution `w` of the linear problem, `-w'' = f + F'` with boundary values `Ψ(g₀), Ψ(g₁)`.
  set k : ℝ := ((∫ s in 0..g₁, A s) - (∫ s in 0..g₀, A s) + ∫ r in x₀..x₁, G r) / (x₁ - x₀)
    with hk_def
  set w : ℝ → ℝ := fun t ↦ (∫ s in 0..g₀, A s) + k * (t - x₀) - ∫ r in x₀..t, G r with hw_def
  have hwac : AbsolutelyContinuousOnInterval w x₀ x₁ :=
    (ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)).sub
      (hGi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hwd : ∀ᵐ r, r ∈ uIcc x₀ x₁ → HasDerivAt w (k - G r) r := by
    filter_upwards [hGi.ae_hasDerivAt_integral] with r hr hrI
    convert ((((hasDerivAt_id' r).sub_const x₀).const_mul k).const_add
      (∫ s in 0..g₀, A s)).sub (hr hrI x₀ left_mem_uIcc) using 1
    ring
  have hw₁ : w x₁ = ∫ s in 0..g₁, A s := by
    simp only [hw_def, hk_def]
    field_simp [sub_ne_zero.2 hx.ne']
    ring
  refine ⟨g ∘ w, k, hglip.comp_absolutelyContinuousOnInterval hwac,
    by simp [hw_def, hgΨ _], by simp only [Function.comp_apply, hw₁, hgΨ _], ?_⟩
  -- Away from the null set where `w` is not differentiable, the chain rule applies to `Ψ⁻¹ ∘ w`.
  filter_upwards [hwd] with r hr hrI
  exact (hgd (w r)).comp r (hr (Icc_subset_uIcc (Ioo_subset_Icc_self hrI)))

/-- **Existence for the quasilinear Dirichlet problem with a coefficient `A(u) ≥ λ`.** The
solution is represented by the function `Ψ⁻¹ ∘ w` of
`exists_absolutelyContinuousOnInterval_and_ae_hasDerivAt`, whose flux `A(v) v'` is `k - G`. -/
private theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq_of_le (hx : x₀ < x₁)
    {lam : ℝ} (hlam : 0 < lam) (hA : Continuous A) (hAlam : ∀ y, lam ≤ A y)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨v, k, hvac, hv₀, hv₁, hvd⟩ := exists_absolutelyContinuousOnInterval_and_ae_hasDerivAt
    hx hlam hA hAlam hf (hF.integrable Fact.out) g₀ g₁
  -- The derivative `(k - G) / A(v)` is dominated by `|k - G| / λ`, which lies in `Lᵖ`.
  have hdv : MemLp (deriv v) p (volume.restrict (Ioo x₀ x₁)) := by
    refine ((memLp_const k).sub
      ((TauCeti.intervalIntegral.memLp_primitive hf (left_mem_Icc.2 hx.le)).add hF)).const_mul
      lam⁻¹ |>.of_le (measurable_deriv v).aestronglyMeasurable ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 hvd] with r hr
    rw [hr.deriv]
    simp only [norm_mul, norm_inv, Pi.sub_apply, Pi.add_apply, Real.norm_of_nonneg hlam.le,
      Real.norm_of_nonneg (hlam.le.trans (hAlam _))]
    gcongr
    exact hAlam _
  -- The Sobolev class represented by `v`.
  obtain ⟨u, hurep, hugrad⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq hx
    (left_mem_Icc.2 hx.le) (v x₀) hdv
  have hrep : ∀ t : Icc x₀ x₁, W1p.intervalRepresentativeL hx u t = v t := fun t ↦ by
    rw [hurep, (hvac.mono (uIcc_subset_uIcc left_mem_uIcc
      (Icc_subset_uIcc t.property))).integral_deriv_eq_sub]
    ring
  refine ⟨u, by rw [W1p.intervalTraceL_apply, hrep, hrep, hv₀, hv₁], fun φ ↦ ?_⟩
  -- The flux `A(v) v'` is `k - G`, which is the weak form of the equation.
  refine setIntegral_mul_deriv_eq_sub_of_ae_add_eq_sub_intervalIntegral (k := k)
    (q := fun t ↦ A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
      W1p.gradient u t) hf (IntegrableOn.locallyIntegrableOn (hF.integrable Fact.out)) ?_ φ
  filter_upwards [hugrad, (ae_restrict_iff' measurableSet_Ioo).2 hvd,
    ae_restrict_mem measurableSet_Ioo] with t ht hdt hmem
  rw [ht, hdt.deriv, projIcc_of_mem hx.le (Ioo_subset_Icc_self hmem), hrep,
    ← mul_assoc, mul_inv_cancel₀ (hlam.trans_le (hAlam _)).ne', one_mul]
  ring

/-- **Existence and uniqueness for the quasilinear Dirichlet problem with a coefficient `A(u)`.**
Let `x₀ < x₁`, let `A` be continuous with `λ ≤ A` for some `λ > 0`, let `f ∈ L¹(x₀, x₁)` and
`F ∈ Lᵖ(x₀, x₁)` with `1 ≤ p ≤ ∞`, and let `g₀, g₁ ∈ ℝ`. Then there is exactly one
`u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values `ū x₀ = g₀`,
`ū x₁ = g₁`, and which solves `-(A(u) u')' = f + F'` weakly:

`∫ A(ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`.

No upper bound on `A` is assumed. -/
theorem existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁) {lam : ℝ}
    (hlam : 0 < lam) (hA : Continuous A) (hAlam : ∀ y, lam ≤ A y)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃! u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨u, hu⟩ := exists_intervalTraceL_eq_and_forall_setIntegral_eq_of_le hx hlam hA hAlam hf
    hF g₀ g₁
  exact ⟨u, hu, fun u' hu' ↦ eq_of_intervalTraceL_eq_of_forall_setIntegral_eq hx hA
    (fun y ↦ hlam.trans_le (hAlam y)) hf (hF.integrable Fact.out) (hu'.1.trans hu.1.symm) hu'.2
    hu.2⟩

end TauCeti.PDE
