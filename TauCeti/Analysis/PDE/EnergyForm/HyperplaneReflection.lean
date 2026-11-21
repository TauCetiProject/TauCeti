/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.W1p.HyperplaneReflection
import TauCeti.Data.Set.Function
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Odd reflection of weak solutions across a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, `ν ≠ 0`, let `ρ` be the reflection
`TauCeti.hyperplaneReflection ν c₀` in its boundary hyperplane, with linear part `R`, and let `U`
be an open set with `ρ U ⊆ U`, such as a ball centred on the hyperplane. Let `u ∈ H¹(U)` vanish
on `U ∖ H` and let its restriction to `U ∩ H` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = ℓ` in `U ∩ H`,

tested against `H¹₀(U ∩ H)`, for a bounded linear functional `ℓ` on `H¹₀(U ∩ H)`. So `u` has zero
boundary values on the flat part `U ∩ ∂H` of the boundary of `U ∩ H`. If the reflected
coefficients `a'`, `b'`, `c'` below are essentially bounded on `U`, then the **odd reflection**
`w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H` and with `-u ∘ ρ` on the other side, is a weak
solution on all of `U` of the reflected equation

`-∂ᵢ(a'ⁱʲ ∂ⱼw) + b'ⁱ ∂ᵢw + c' w = ℓ'` in `U`
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`).

The reflected coefficients agree with `a`, `b`, `c` on the closed half-space `{c₀ ≤ ⟪x, ν⟫}` and
are their pullbacks under `ρ` on the other side: `a'(x) = R a(ρ x) R`, `b'(x) = R b(ρ x)` and
`c'(x) = c(ρ x)` there (`TauCeti.PDE.reflectPrincipal`, `TauCeti.PDE.reflectDrift`,
`TauCeti.PDE.reflectDensity`). The reflected functional is
`ℓ'(φ) = ℓ((φ - φ ∘ ρ)|_{U ∩ H})`, bounded on `H¹₀(U)` because the restriction of `φ - φ ∘ ρ`
has zero boundary values (`TauCeti.W1p0.restrictSubCompHyperplaneReflectionL`).

Measurable coefficients are allowed: no regularity of `a` is needed, and `a'` is uniformly
elliptic with the same constants as `a` (`TauCeti.PDE.UniformlyEllipticOn.reflectPrincipal`),
provided `a` is uniformly elliptic on the closed half-space.
This is the reflection that turns interior estimates for weak solutions with merely measurable
coefficients, such as De Giorgi's Hölder estimate, into estimates up to a flat boundary on which
the solution vanishes.

## The argument

Write `Q` for the energy form on `U` with the reflected coefficients. Off the hyperplane the
reflected coefficients are invariant under the change of variables `ρ`
(`TauCeti.PDE.energyIntegrand_pullback_reflectPrincipal`), so the change of variables formula for
the energy form (`TauCeti.PDE.energyFormH1_compL`) gives `Q (u ∘ ρ, φ) = Q (u, φ ∘ ρ)`. Hence
`Q (w, φ) = Q (u, φ - φ ∘ ρ)`. Since `u` and its gradient vanish almost everywhere off `H`, and
the reflected coefficients are `a`, `b`, `c` on `H`, this is the energy form on `U ∩ H` of `u` and
the restriction of `φ - φ ∘ ρ`, which lies in `H¹₀(U ∩ H)`; so it equals
`ℓ ((φ - φ ∘ ρ)|_{U ∩ H})`.

## Main declarations

* `TauCeti.PDE.reflectPrincipal`, `TauCeti.PDE.reflectDrift`, `TauCeti.PDE.reflectDensity`: the
  reflected coefficients.
* `TauCeti.PDE.energyIntegrand_pullback_reflectPrincipal`: off the hyperplane, the reflected
  coefficients are invariant under the change of variables `ρ`.
* `TauCeti.PDE.energyIntegrand_reflectPrincipal_zero_zero`: a principal coefficient that is
  already invariant under the reflection is unchanged by it.
* `TauCeti.PDE.matrixBilinearForm_reflectPrincipal_of_lt`: below the hyperplane, the reflected
  principal coefficient is `a'(x) = R a(ρ x) R`.
* `TauCeti.PDE.norm_matrixBilinearForm_reflectPrincipal_sub_le`: the reflected principal
  coefficient stays within `δ` of a reflection-invariant constant matrix `A` when `a` does, and
  `TauCeti.PDE.norm_matrixBilinearForm_reflectPrincipal_le`: it keeps the bound `Λ` of `a`.
* `TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`: the odd reflection
  of a weak solution vanishing on the flat boundary is a weak solution of the reflected equation.
* `TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral`: the
  same for a right-hand side `f ∈ L²(U ∩ H)`, which is reflected oddly, and
  `TauCeti.PDE.energyFormH1_sub_compHyperplaneReflectionL_eq_setIntegral`: for a principal
  coefficient invariant under the reflection, the reflected equation is the original one.
* `energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral`
  (in `TauCeti.PDE`): the same for a right-hand side `f + ∂ᵢFⁱ` with `f, F ∈ L²(U ∩ H)`; the field
  `F` is reflected to `F` on `H` and to `-R F(ρ x)` on the other side.
* `TauCeti.PDE.UniformlyEllipticOn.reflectPrincipal`: the reflected principal coefficient is
  uniformly elliptic and bounded with the constants of `a`, and
  `TauCeti.PDE.norm_reflectDrift_le` and `TauCeti.PDE.norm_reflectDensity_le`: the reflected
  lower-order coefficients keep the bounds of `b` and `c`.
* `TauCeti.PDE.memLp_energyIntegrand_reflectPrincipal`: the reflected coefficients are essentially
  bounded, as the reflected weak formulation requires.
* `TauCeti.PDE.reflectPrincipal_one`: the reflected Laplacian is the Laplacian.
* `TauCeti.PDE.abs_energyFormH1_sub_compHyperplaneReflectionL_le`: if `u` vanishes off `H` and
  solves `-Δu = -div F` on `U ∩ H`, the Dirichlet form of its odd reflection against `φ ∈ H¹₀(U)`
  is at most `2 ‖F‖_{L²(U ∩ H)} ‖∇φ‖_{L²(U)}`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.29 and its proof (Hölder estimates up to the boundary for weak solutions).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 9.2 (reflection across a hyperplane).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The reflected coefficients -/

section Coefficients

/-- The **reflected principal coefficient** across the hyperplane `{x | ⟪x, ν⟫ = c₀}`: equal to
`a` on the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` and to its pullback `R a(ρ x) R` under the
reflection `ρ` on the open half-space `{x | ⟪x, ν⟫ < c₀}`, where `R` is the linear part of `ρ`. -/
def reflectPrincipal (ν : EuclideanSpace ℝ ι) (c₀ : ℝ) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι → Matrix ι ι ℝ :=
  {x | ⟪x, ν⟫_ℝ < c₀}.piecewise (pullbackPrincipal (hyperplaneReflection ν c₀) a) a

/-- The **reflected drift** across the hyperplane `{x | ⟪x, ν⟫ = c₀}`: equal to `b` on the
closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` and to its pullback `R b(ρ x)` under the reflection `ρ` on
the open half-space `{x | ⟪x, ν⟫ < c₀}`. -/
def reflectDrift (ν : EuclideanSpace ℝ ι) (c₀ : ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
  {x | ⟪x, ν⟫_ℝ < c₀}.piecewise (pullbackDrift (hyperplaneReflection ν c₀) b) b

/-- The **reflected zeroth-order coefficient** across the hyperplane `{x | ⟪x, ν⟫ = c₀}`: equal
to `c` on the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` and to `c ∘ ρ` on the open half-space
`{x | ⟪x, ν⟫ < c₀}`, where `ρ` is the reflection. -/
def reflectDensity (ν : EuclideanSpace ℝ ι) (c₀ : ℝ) (c : EuclideanSpace ℝ ι → ℝ) :
    EuclideanSpace ℝ ι → ℝ :=
  {x | ⟪x, ν⟫_ℝ < c₀}.piecewise (pullbackDensity (hyperplaneReflection ν c₀) c) c

variable {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {x : EuclideanSpace ℝ ι}

theorem reflectPrincipal_of_lt (hx : ⟪x, ν⟫_ℝ < c₀) :
    reflectPrincipal ν c₀ a x = pullbackPrincipal (hyperplaneReflection ν c₀) a x :=
  piecewise_eq_of_mem _ _ _ hx

theorem reflectPrincipal_of_le (hx : c₀ ≤ ⟪x, ν⟫_ℝ) : reflectPrincipal ν c₀ a x = a x :=
  piecewise_eq_of_notMem _ _ _ (not_lt.2 hx)

theorem reflectDrift_of_lt (hx : ⟪x, ν⟫_ℝ < c₀) :
    reflectDrift ν c₀ b x = pullbackDrift (hyperplaneReflection ν c₀) b x :=
  piecewise_eq_of_mem _ _ _ hx

theorem reflectDrift_of_le (hx : c₀ ≤ ⟪x, ν⟫_ℝ) : reflectDrift ν c₀ b x = b x :=
  piecewise_eq_of_notMem _ _ _ (not_lt.2 hx)

omit [DecidableEq ι] in
theorem reflectDensity_of_lt (hx : ⟪x, ν⟫_ℝ < c₀) :
    reflectDensity ν c₀ c x = pullbackDensity (hyperplaneReflection ν c₀) c x :=
  piecewise_eq_of_mem _ _ _ hx

omit [DecidableEq ι] in
/-- Below the hyperplane, the reflected zeroth-order coefficient is `c ∘ ρ`: the reflection has
Jacobian determinant of absolute value one. -/
theorem reflectDensity_eq_comp_of_lt (hx : ⟪x, ν⟫_ℝ < c₀) :
    reflectDensity ν c₀ c x = c (hyperplaneReflection ν c₀ x) := by
  rw [reflectDensity_of_lt hx, pullbackDensity_apply, abs_det_fderiv_hyperplaneReflection,
    one_mul]

omit [DecidableEq ι] in
theorem reflectDensity_of_le (hx : c₀ ≤ ⟪x, ν⟫_ℝ) : reflectDensity ν c₀ c x = c x :=
  piecewise_eq_of_notMem _ _ _ (not_lt.2 hx)

/-- The energy integrand of the coefficients pulled back by the hyperplane reflection `ρ` is the
energy integrand at `ρ x`, with the gradient slots reflected by the linear part `R` of `ρ`. -/
theorem energyIntegrand_pullback_hyperplaneReflection (W W' : ℝ × EuclideanSpace ℝ ι) :
    energyIntegrand (pullbackPrincipal (hyperplaneReflection ν c₀) a x)
        (pullbackDrift (hyperplaneReflection ν c₀) b x)
        (pullbackDensity (hyperplaneReflection ν c₀) c x) W W' =
      energyIntegrand (a (hyperplaneReflection ν c₀ x)) (b (hyperplaneReflection ν c₀ x))
        (c (hyperplaneReflection ν c₀ x)) (W.1, (ℝ ∙ ν)ᗮ.reflection W.2)
        (W'.1, (ℝ ∙ ν)ᗮ.reflection W'.2) := by
  have hdet := abs_det_fderiv_hyperplaneReflection ν c₀ x
  have h := energyIntegrand_pullback a b c (abs_pos.1 (hdet ▸ one_pos))
    (W.1, (ℝ ∙ ν)ᗮ.reflection W.2) (W'.1, (ℝ ∙ ν)ᗮ.reflection W'.2)
  rw [hdet, one_mul] at h
  simpa only [fderiv_hyperplaneReflection, (Submodule.isSelfAdjoint_reflection _).adjoint_eq,
    LinearIsometryEquiv.coe_coe'', Submodule.reflection_reflection, Prod.mk.eta] using h

/-- **The reflected coefficients are invariant under the reflection.** Off the hyperplane
`{x | ⟪x, ν⟫ = c₀}`, pulling the reflected coefficients back by the reflection `ρ` does not change
their energy integrand. -/
theorem energyIntegrand_pullback_reflectPrincipal (hν : ν ≠ 0) (hx : ⟪x, ν⟫_ℝ ≠ c₀) :
    energyIntegrand (pullbackPrincipal (hyperplaneReflection ν c₀) (reflectPrincipal ν c₀ a) x)
        (pullbackDrift (hyperplaneReflection ν c₀) (reflectDrift ν c₀ b) x)
        (pullbackDensity (hyperplaneReflection ν c₀) (reflectDensity ν c₀ c) x) =
      energyIntegrand (reflectPrincipal ν c₀ a x) (reflectDrift ν c₀ b x)
        (reflectDensity ν c₀ c x) := by
  refine ContinuousLinearMap.ext fun W => ContinuousLinearMap.ext fun W' => ?_
  rw [energyIntegrand_pullback_hyperplaneReflection]
  rcases hx.lt_or_gt with hlt | hgt
  · -- Below the hyperplane, `ρ x` lies above it, where the reflected coefficients are the
    -- original ones.
    have hρ : c₀ ≤ ⟪hyperplaneReflection ν c₀ x, ν⟫_ℝ := by
      rw [inner_hyperplaneReflection hν]
      linarith
    rw [reflectPrincipal_of_le hρ, reflectDrift_of_le hρ, reflectDensity_of_le hρ,
      reflectPrincipal_of_lt hlt, reflectDrift_of_lt hlt, reflectDensity_of_lt hlt,
      energyIntegrand_pullback_hyperplaneReflection]
  · -- Above the hyperplane, `ρ x` lies below it, where the reflected coefficients are pulled
    -- back by `ρ`, and `ρ` is an involution.
    have hρ : ⟪hyperplaneReflection ν c₀ x, ν⟫_ℝ < c₀ :=
      (inner_hyperplaneReflection_lt_iff hν c₀).2 hgt
    rw [reflectPrincipal_of_lt hρ, reflectDrift_of_lt hρ, reflectDensity_of_lt hρ,
      energyIntegrand_pullback_hyperplaneReflection,
      hyperplaneReflection_hyperplaneReflection, Submodule.reflection_reflection,
      Submodule.reflection_reflection, reflectPrincipal_of_le hgt.le, reflectDrift_of_le hgt.le,
      reflectDensity_of_le hgt.le]

/-- **Reflection-invariant principal coefficients are their own reflection.** If the bilinear
form of `a (ρ x)` on reflected vectors is that of `a x`, that is `a (ρ x) = R a(x) R` with `R` the
linear part of the reflection `ρ`, then the reflected principal coefficient has the energy
integrand of `a` at `x`, in the absence of lower-order terms. -/
theorem energyIntegrand_reflectPrincipal_zero_zero
    (ha : ∀ η ξ, matrixBilinearForm (a (hyperplaneReflection ν c₀ x)) ((ℝ ∙ ν)ᗮ.reflection η)
      ((ℝ ∙ ν)ᗮ.reflection ξ) = matrixBilinearForm (a x) η ξ) :
    energyIntegrand (reflectPrincipal ν c₀ a x) 0 0 = energyIntegrand (a x) 0 0 := by
  by_cases hx : ⟪x, ν⟫_ℝ < c₀
  · refine ContinuousLinearMap.ext fun W => ContinuousLinearMap.ext fun W' => ?_
    have h := energyIntegrand_pullback_hyperplaneReflection (a := a)
      (b := (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) (c := (0 : EuclideanSpace ℝ ι → ℝ))
      (ν := ν) (c₀ := c₀) (x := x) W W'
    simp only [pullbackDrift_apply, pullbackDensity_apply, Pi.zero_apply, map_zero, smul_zero,
      mul_zero] at h
    rw [reflectPrincipal_of_lt hx, h, energyIntegrand_apply, energyIntegrand_apply, ha]
    simp [driftForm_apply, massForm_apply]
  · rw [reflectPrincipal_of_le (not_lt.1 hx)]

/-- Below the hyperplane, the bilinear form of the reflected principal coefficient is that of `a`
at the reflected point `ρ x`, evaluated on vectors reflected by the linear part `R` of `ρ`:
`a'(x) = R a(ρ x) R`. -/
theorem matrixBilinearForm_reflectPrincipal_of_lt (hx : ⟪x, ν⟫_ℝ < c₀) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm (reflectPrincipal ν c₀ a x) η ξ =
      matrixBilinearForm (a (hyperplaneReflection ν c₀ x)) ((ℝ ∙ ν)ᗮ.reflection η)
        ((ℝ ∙ ν)ᗮ.reflection ξ) := by
  have hR : ((ℝ ∙ ν)ᗮ.reflection : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ∘L
      fderiv ℝ (hyperplaneReflection ν c₀) x = ContinuousLinearMap.id ℝ _ := by
    ext1 v
    simp
  rw [reflectPrincipal_of_lt hx, matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a hR,
    abs_det_fderiv_hyperplaneReflection, one_smul,
    (Submodule.isSelfAdjoint_reflection _).adjoint_eq]
  rfl

/-- **The reflected coefficient stays close to a reflection-invariant matrix.** Let `A` be a
constant matrix invariant under the reflection, `A = R A R` with `R` the linear part of `ρ`. If
the bilinear form of `a` is within `δ` of that of `A`, in operator norm, at every point of the
closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, then so is that of the reflected coefficient at every
point. -/
theorem norm_matrixBilinearForm_reflectPrincipal_sub_le (hν : ν ≠ 0) {A : Matrix ι ι ℝ}
    (hA : ∀ η ξ, matrixBilinearForm A ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
      matrixBilinearForm A η ξ) {δ : ℝ}
    (ha : ∀ y, c₀ ≤ ⟪y, ν⟫_ℝ → ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ)
    (x : EuclideanSpace ℝ ι) :
    ‖matrixBilinearForm (reflectPrincipal ν c₀ a x) - matrixBilinearForm A‖ ≤ δ := by
  by_cases hx : c₀ ≤ ⟪x, ν⟫_ℝ
  · rw [reflectPrincipal_of_le hx]
    exact ha x hx
  -- Below the hyperplane, the difference is the difference at `ρ x` on reflected vectors, and the
  -- linear part of the reflection is an isometry.
  have hρ : c₀ ≤ ⟪hyperplaneReflection ν c₀ x, ν⟫_ℝ := by
    rw [inner_hyperplaneReflection hν]
    linarith [not_le.1 hx]
  have hδ := ha _ hρ
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  refine ContinuousLinearMap.opNorm_le_bound₂ _ hδ0 fun η ξ => ?_
  have h : (matrixBilinearForm (reflectPrincipal ν c₀ a x) - matrixBilinearForm A) η ξ =
      (matrixBilinearForm (a (hyperplaneReflection ν c₀ x)) - matrixBilinearForm A)
        ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) := by
    simp only [FunLike.coe_sub, Pi.sub_apply,
      matrixBilinearForm_reflectPrincipal_of_lt (not_le.1 hx), hA]
  rw [h]
  calc _ ≤ ‖matrixBilinearForm (a (hyperplaneReflection ν c₀ x)) - matrixBilinearForm A‖ *
        ‖(ℝ ∙ ν)ᗮ.reflection η‖ * ‖(ℝ ∙ ν)ᗮ.reflection ξ‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ δ * ‖η‖ * ‖ξ‖ := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
      gcongr

/-- **The reflected coefficient keeps the bound of `a`.** If the bilinear form of `a` has operator
norm at most `Λ` at every point of the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, then so has that of
the reflected coefficient at every point. -/
theorem norm_matrixBilinearForm_reflectPrincipal_le (hν : ν ≠ 0) {Lam : ℝ}
    (ha : ∀ y, c₀ ≤ ⟪y, ν⟫_ℝ → ‖matrixBilinearForm (a y)‖ ≤ Lam) (x : EuclideanSpace ℝ ι) :
    ‖matrixBilinearForm (reflectPrincipal ν c₀ a x)‖ ≤ Lam := by
  have h0 (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
      B - matrixBilinearForm (0 : Matrix ι ι ℝ) = B := by
    ext
    simp
  have h := norm_matrixBilinearForm_reflectPrincipal_sub_le (a := a) (A := 0) (δ := Lam) hν
    (fun η ξ => by simp) (fun y hy => by rw [h0]; exact ha y hy) x
  rwa [h0] at h

@[simp]
theorem reflectDrift_zero :
    reflectDrift ν c₀ (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = 0 := by
  ext1 x
  by_cases hx : ⟪x, ν⟫_ℝ < c₀
  · simp [reflectDrift_of_lt hx, pullbackDrift_apply]
  · exact reflectDrift_of_le (not_lt.1 hx)

omit [DecidableEq ι] in
@[simp]
theorem reflectDensity_zero : reflectDensity ν c₀ (0 : EuclideanSpace ℝ ι → ℝ) = 0 := by
  ext1 x
  by_cases hx : ⟪x, ν⟫_ℝ < c₀
  · simp [reflectDensity_of_lt hx]
  · exact reflectDensity_of_le (not_lt.1 hx)

/-- **The Laplacian is its own reflection.** The reflected principal coefficient of the Laplacian
`-Δ` (`a = 1`) is the identity matrix: below the hyperplane it is `R R = 1`, where `R` is the
linear part of the reflection. The reflected lower-order coefficients of `-Δ` vanish
(`TauCeti.PDE.reflectDrift_zero` and `TauCeti.PDE.reflectDensity_zero`). -/
@[simp]
theorem reflectPrincipal_one :
    reflectPrincipal ν c₀ (fun _ => (1 : Matrix ι ι ℝ)) = fun _ => 1 := by
  ext1 x
  by_cases hx : ⟪x, ν⟫_ℝ < c₀
  · -- Compare entries through the energy integrands on coordinate gradient slots.
    ext i j
    have h := energyIntegrand_pullback_hyperplaneReflection (a := fun _ => (1 : Matrix ι ι ℝ))
      (b := (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) (c := (0 : EuclideanSpace ℝ ι → ℝ))
      (ν := ν) (c₀ := c₀) (x := x) (0, EuclideanSpace.single j 1) (0, EuclideanSpace.single i 1)
    -- The linear part of the reflection preserves the inner product of the gradient slots.
    have hR := LinearIsometryEquiv.inner_map_map (ℝ ∙ ν)ᗮ.reflection
      (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hR
    rw [reflectPrincipal_of_lt hx]
    simpa [energyIntegrand_apply, driftForm_apply, massForm_apply, pullbackDrift_apply,
      pullbackDensity_apply, matrixBilinearForm_one_apply, hR, Matrix.one_apply, Pi.single_apply,
      eq_comm] using h
  · exact reflectPrincipal_of_le (not_lt.1 hx)

/-- **The reflected principal coefficient is uniformly elliptic** with the constants of `a`: if
`a` is uniformly elliptic and bounded with constants `λ, Λ` on the part of a set `s` in the closed
half-space `{x | c₀ ≤ ⟪x, ν⟫}`, and the reflection maps `s` into itself, then the reflected
coefficient is uniformly elliptic and bounded with the same constants on all of `s`. -/
theorem UniformlyEllipticOn.reflectPrincipal [Nonempty ι] (hν : ν ≠ 0)
    {s : Set (EuclideanSpace ℝ ι)} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn {x | x ∈ s ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam)
    (hs : MapsTo (hyperplaneReflection ν c₀) s s) :
    UniformlyEllipticOn s (reflectPrincipal ν c₀ a) lam Lam := by
  obtain ⟨hlam, hlamLam, ha'⟩ := uniformlyEllipticOn_iff.1 ha
  refine uniformlyEllipticOn_iff.2 ⟨hlam, hlamLam, fun x hx => ?_⟩
  by_cases hle : c₀ ≤ ⟪x, ν⟫_ℝ
  · rw [reflectPrincipal_of_le hle]
    exact ha' ⟨hx, hle⟩
  -- Below the hyperplane, the coefficient is pulled back from `ρ x`, which lies above it, by an
  -- isometry with Jacobian determinant of absolute value one.
  have hlt := not_le.1 hle
  have hpb := ha.pullbackPrincipal (Φ := hyperplaneReflection ν c₀) (s := {x}) (L := 1) (L' := 1)
    (c := 1) (fun y hy => ⟨hs (hy ▸ hx), by
      rw [hy, inner_hyperplaneReflection hν]
      linarith⟩)
    (singleton_nonempty x) (fun y _ => AffineIsometryEquiv.norm_fderiv_le _ y)
    (fun y _ v => by simp) one_pos (fun y _ => (abs_det_fderiv_hyperplaneReflection ν c₀ y).ge)
  simp only [one_mul, one_pow, div_one, mul_one] at hpb
  rw [reflectPrincipal_of_lt hlt]
  exact (uniformlyEllipticOn_iff.1 hpb).2.2 rfl

/-- **The reflected drift keeps the bound of `b`**: if `‖b‖ ≤ β` on the part of a set `s` in the
closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, and the reflection maps `s` into itself, then the
reflected drift satisfies `‖b'‖ ≤ β` on all of `s`, since the reflection is an isometry. -/
theorem norm_reflectDrift_le (hν : ν ≠ 0) {s : Set (EuclideanSpace ℝ ι)} {beta : ℝ}
    (hb : ∀ x ∈ {x | x ∈ s ∧ c₀ ≤ ⟪x, ν⟫_ℝ}, ‖b x‖ ≤ beta)
    (hs : MapsTo (hyperplaneReflection ν c₀) s s) {x : EuclideanSpace ℝ ι} (hx : x ∈ s) :
    ‖reflectDrift ν c₀ b x‖ ≤ beta := by
  by_cases hle : c₀ ≤ ⟪x, ν⟫_ℝ
  · rw [reflectDrift_of_le hle]
    exact hb x ⟨hx, hle⟩
  -- Below the hyperplane, the drift is pulled back from `ρ x`, which lies above it.
  have hlt := not_le.1 hle
  have hpb := norm_pullbackDrift_le (U := ⊤) (V := ⊤) (Ψ := hyperplaneReflection ν c₀) (L := 1)
    (L' := 1) (differentiable_hyperplaneReflection ν c₀).differentiableOn (mapsTo_univ _ _)
    (differentiable_hyperplaneReflection ν c₀).differentiableOn
    (fun y _ => hyperplaneReflection_hyperplaneReflection ν c₀ y)
    (fun y _ => hyperplaneReflection_hyperplaneReflection ν c₀ y) b (x := x) trivial
    (AffineIsometryEquiv.norm_fderiv_le _ x) (AffineIsometryEquiv.norm_fderiv_le _ _)
  rw [reflectDrift_of_lt hlt]
  refine hpb.trans ?_
  rw [one_pow, one_mul, one_mul]
  exact hb _ ⟨hs hx, by rw [inner_hyperplaneReflection hν]; linarith⟩

omit [DecidableEq ι] in
/-- **The reflected zeroth-order coefficient keeps the bound of `c`**: if `‖c‖ ≤ γ` on the part
of a set `s` in the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, and the reflection maps `s` into
itself, then the reflected coefficient satisfies `‖c'‖ ≤ γ` on all of `s`. -/
theorem norm_reflectDensity_le (hν : ν ≠ 0) {s : Set (EuclideanSpace ℝ ι)} {gamma : ℝ}
    (hc : ∀ x ∈ {x | x ∈ s ∧ c₀ ≤ ⟪x, ν⟫_ℝ}, ‖c x‖ ≤ gamma)
    (hs : MapsTo (hyperplaneReflection ν c₀) s s) {x : EuclideanSpace ℝ ι} (hx : x ∈ s) :
    ‖reflectDensity ν c₀ c x‖ ≤ gamma := by
  by_cases hle : c₀ ≤ ⟪x, ν⟫_ℝ
  · rw [reflectDensity_of_le hle]
    exact hc x ⟨hx, hle⟩
  -- Below the hyperplane, the coefficient is `c` at `ρ x`, which lies above it.
  rw [reflectDensity_eq_comp_of_lt (not_le.1 hle)]
  exact hc _ ⟨hs hx, by rw [inner_hyperplaneReflection hν]; linarith⟩

end Coefficients

/-! ### The reflected weak formulation -/

section WeakSolution

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {U H : Opens (EuclideanSpace ℝ ι)}
  {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- Testing the reflected equation against `φ ∘ ρ` is testing against `φ` after reflecting the
first argument: `Q (u ∘ ρ, φ) = Q (u, φ ∘ ρ)` for the energy form `Q` of the reflected
coefficients on a set `U` mapped into itself by the reflection `ρ`. -/
theorem energyFormH1_reflectPrincipal_compHyperplaneReflectionL (hν : ν ≠ 0)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) (u φ : W1p mu U 2) :
    energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c)
        (W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) φ =
      energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c) u
        (W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU φ) := by
  -- Off the null hyperplane the coefficients are invariant under the change of variables `ρ`.
  have hinv : energyFormH1 (pullbackPrincipal (hyperplaneReflection ν c₀) (reflectPrincipal ν c₀ a))
      (pullbackDrift (hyperplaneReflection ν c₀) (reflectDrift ν c₀ b))
      (pullbackDensity (hyperplaneReflection ν c₀) (reflectDensity ν c₀ c)) =
      energyFormH1 (mu := mu) (Omega := U) (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b)
        (reflectDensity ν c₀ c) := by
    ext w v
    rw [energyFormH1_def, energyFormH1_def]
    refine setIntegral_congr_ae U.isOpen.measurableSet ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Measure.addHaar_setOf_inner_eq mu hν c₀)] with x hx _
    rw [energyIntegrand_pullback_reflectPrincipal hν hx]
  have h := energyFormH1_compL (mu := mu)
    (differentiable_hyperplaneReflection ν c₀).differentiableOn
    (hyperplaneReflection ν c₀).injective.injOn hU
    (fun x _ => AffineIsometryEquiv.norm_fderiv_le _ x) one_pos
    (fun x _ => (abs_det_fderiv_hyperplaneReflection ν c₀ x).ge)
    (hU.image_eq_of_involutive (hyperplaneReflection_involutive ν c₀)) (reflectPrincipal ν c₀ a)
    (reflectDrift ν c₀ b) (reflectDensity ν c₀ c) u
    (W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU φ)
  rw [hinv, ← W1p.compHyperplaneReflectionL_eq_compL,
    W1p.compHyperplaneReflectionL_compHyperplaneReflectionL] at h
  exact h

/-- The reflected principal coefficient is measurable on `U` when `a` is measurable on `U ∩ H`. -/
theorem aestronglyMeasurable_reflectPrincipal (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (ha : AEStronglyMeasurable a (mu.restrict (U ⊓ H))) :
    AEStronglyMeasurable (reflectPrincipal ν c₀ a) (mu.restrict U) := by
  set P := ((toEuclideanCLM (𝕜 := ℝ)).symm ((ℝ ∙ ν)ᗮ.reflection : EuclideanSpace ℝ ι →L[ℝ] _))⁻¹
  have h : reflectPrincipal ν c₀ a = {x | ⟪x, ν⟫_ℝ < c₀}.piecewise
      (fun x => P * a (hyperplaneReflection ν c₀ x) * Pᵀ) a := by
    ext1 x
    by_cases hx : ⟪x, ν⟫_ℝ < c₀
    · rw [reflectPrincipal_of_lt hx, piecewise_eq_of_mem _ _ _ hx, pullbackPrincipal_apply,
        abs_det_fderiv_hyperplaneReflection, fderiv_hyperplaneReflection,
        one_smul]
    · rw [reflectPrincipal_of_le (not_lt.1 hx), piecewise_eq_of_notMem _ _ _ hx]
  rw [h]
  exact aestronglyMeasurable_piecewise_comp_hyperplaneReflection hν hH U.isOpen.measurableSet hU
    ((continuous_const.mul continuous_id).mul continuous_const) ha

/-- The reflected drift is measurable on `U` when `b` is measurable on `U ∩ H`. -/
theorem aestronglyMeasurable_reflectDrift (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hb : AEStronglyMeasurable b (mu.restrict (U ⊓ H))) :
    AEStronglyMeasurable (reflectDrift ν c₀ b) (mu.restrict U) := by
  set P := ((toEuclideanCLM (𝕜 := ℝ)).symm ((ℝ ∙ ν)ᗮ.reflection : EuclideanSpace ℝ ι →L[ℝ] _))⁻¹
  have h : reflectDrift ν c₀ b = {x | ⟪x, ν⟫_ℝ < c₀}.piecewise
      (fun x => toEuclideanCLM (𝕜 := ℝ) P (b (hyperplaneReflection ν c₀ x))) b := by
    ext1 x
    by_cases hx : ⟪x, ν⟫_ℝ < c₀
    · rw [reflectDrift_of_lt hx, piecewise_eq_of_mem _ _ _ hx, pullbackDrift_apply,
        abs_det_fderiv_hyperplaneReflection, fderiv_hyperplaneReflection,
        one_smul]
    · rw [reflectDrift_of_le (not_lt.1 hx), piecewise_eq_of_notMem _ _ _ hx]
  rw [h]
  exact aestronglyMeasurable_piecewise_comp_hyperplaneReflection hν hH U.isOpen.measurableSet hU
    (toEuclideanCLM (𝕜 := ℝ) P).continuous hb

omit [DecidableEq ι] in
/-- The reflected zeroth-order coefficient is measurable on `U` when `c` is measurable on
`U ∩ H`. -/
theorem aestronglyMeasurable_reflectDensity (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hc : AEStronglyMeasurable c (mu.restrict (U ⊓ H))) :
    AEStronglyMeasurable (reflectDensity ν c₀ c) (mu.restrict U) := by
  have h : reflectDensity ν c₀ c =
      {x | ⟪x, ν⟫_ℝ < c₀}.piecewise (fun x => id (c (hyperplaneReflection ν c₀ x))) c := by
    ext1 x
    by_cases hx : ⟪x, ν⟫_ℝ < c₀
    · rw [reflectDensity_of_lt hx, piecewise_eq_of_mem _ _ _ hx, pullbackDensity_apply,
        abs_det_fderiv_hyperplaneReflection, one_mul, id]
    · rw [reflectDensity_of_le (not_lt.1 hx), piecewise_eq_of_notMem _ _ _ hx]
  rw [h]
  exact aestronglyMeasurable_piecewise_comp_hyperplaneReflection hν hH U.isOpen.measurableSet hU
    continuous_id hc

/-- **The reflected coefficients are bounded.** If `a`, `b`, `c` are measurable on `U ∩ H`, with
`a` uniformly elliptic with constants `λ, Λ`, `‖b‖ ≤ β` and `‖c‖ ≤ γ` on the part of `U` in the
closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, then the reflected coefficients are essentially bounded on
`U`. This is the boundedness hypothesis of the reflected weak formulation. -/
theorem memLp_energyIntegrand_reflectPrincipal [Nonempty ι] (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    {lam Lam beta gamma : ℝ} (ha : UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam)
    (ham : AEStronglyMeasurable a (mu.restrict (U ⊓ H)))
    (hbm : AEStronglyMeasurable b (mu.restrict (U ⊓ H)))
    (hcm : AEStronglyMeasurable c (mu.restrict (U ⊓ H)))
    (hb : ∀ x ∈ {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ}, ‖b x‖ ≤ beta)
    (hc : ∀ x ∈ {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ}, ‖c x‖ ≤ gamma) :
    MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x) (reflectDrift ν c₀ b x)
      (reflectDensity ν c₀ c x)) ⊤ (mu.restrict U) := by
  have ha' := uniformlyEllipticOn_iff.1 (ha.reflectPrincipal hν hU)
  exact memLp_energyIntegrand_of_bounds (ha'.1.le.trans ha'.2.1)
    (aestronglyMeasurable_reflectPrincipal hν hH hU ham)
    (aestronglyMeasurable_reflectDrift hν hH hU hbm)
    (aestronglyMeasurable_reflectDensity hν hH hU hcm) (fun x hx => (ha'.2.2 hx).2)
    (fun x hx => norm_reflectDrift_le hν hb hU hx) (fun x hx => norm_reflectDensity_le hν hc hU hx)

omit [DecidableEq ι] in
/-- A Sobolev function on `U` vanishing on `U ∖ H` has, almost everywhere on `U ∖ H`, vanishing
value and weak gradient: the gradient vanishes off the closed half-space `closure H` and the
hyperplane `∂H` is null. -/
private theorem ae_jetField_eq_zero_of_ae_value_eq_zero (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {u : W1p mu U 2}
    (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) :
    ∀ᵐ x ∂mu.restrict U, x ∉ H → jetField u x = 0 := by
  have hgrad := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero_of_inner_lt hH hu0
  filter_upwards [hu0, hgrad, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_setOf_inner_eq mu hν c₀))] with x hv hg hx hxH
  have hlt : ⟪x, ν⟫_ℝ < c₀ :=
    lt_of_le_of_ne (not_lt.1 fun h => hxH ((hH x).2 h)) hx
  rw [jetField_apply, hv hxH, hg hlt, Prod.mk_zero_zero]

/-- For a Sobolev function `u` on `U` vanishing on `U ∖ H`, the energy form of the reflected
coefficients on `U` is the energy form of the original coefficients on `U ∩ H`. -/
theorem energyFormH1_reflectPrincipal_eq_restrictL (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {u : W1p mu U 2}
    (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) (v : W1p mu U 2) :
    energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c) u v =
      energyFormH1 a b c (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) v) := by
  have hjet := (ae_restrict_iff' U.isOpen.measurableSet).1
    (ae_jetField_eq_zero_of_ae_value_eq_zero hν hH hu0)
  rw [energyFormH1_def, energyFormH1_def, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    U.isOpen.measurableSet.nullMeasurableSet (SetLike.coe_subset_coe.2 inf_le_left)]
  · -- On `U ∩ H` the reflected coefficients are the original ones.
    refine setIntegral_congr_ae (U ⊓ H).isOpen.measurableSet
      ((ae_restrict_iff' (U ⊓ H).isOpen.measurableSet).1 ?_)
    filter_upwards [W1p.value_restrictL_ae (inf_le_left : U ⊓ H ≤ U) u,
      W1p.gradient_restrictL_ae (inf_le_left : U ⊓ H ≤ U) u,
      W1p.value_restrictL_ae (inf_le_left : U ⊓ H ≤ U) v,
      W1p.gradient_restrictL_ae (inf_le_left : U ⊓ H ≤ U) v,
      ae_restrict_mem (U ⊓ H).isOpen.measurableSet] with x h1 h2 h3 h4 hx
    have hle : c₀ ≤ ⟪x, ν⟫_ℝ := ((hH x).1 (Opens.mem_inf.1 hx).2).le
    rw [jetField_apply, jetField_apply, jetField_apply, jetField_apply, h1, h2, h3, h4,
      reflectPrincipal_of_le hle, reflectDrift_of_le hle, reflectDensity_of_le hle]
  · -- Off `H` the value and gradient of `u` vanish.
    filter_upwards [hjet] with x hx hxd
    have hxH : x ∉ H := fun h => hxd.2 (Opens.mem_inf.2 ⟨hxd.1, h⟩)
    rw [hx hxd.1 hxH, map_zero, zero_apply]

/-- **Odd reflection of a weak solution across a flat boundary.** Let `H = {x | c₀ < ⟪x, ν⟫}`
with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, and let `U` be open with
`ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to `U ∩ H` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = ℓ`, tested against `H¹₀(U ∩ H)`, for a bounded linear
functional `ℓ` on `H¹₀(U ∩ H)`. If the reflected coefficients are bounded on `U`, then the odd
reflection `u - u ∘ ρ` is a weak solution on `U` of the equation with the reflected coefficients
and the reflected functional `φ ↦ ℓ ((φ - φ ∘ ρ)|_{U ∩ H})`, tested against `H¹₀(U)`. -/
theorem energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x) (reflectDrift ν c₀ b x)
      (reflectDensity ν c₀ c x)) ⊤ (mu.restrict U))
    {u : W1p mu U 2} (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0)
    {ℓ : W1p0 mu (U ⊓ H) 2 →L[ℝ] ℝ}
    (hu : ∀ v : W1p0 mu (U ⊓ H) 2,
      energyFormH1 a b c (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (v : W1p mu (U ⊓ H) 2) =
        ℓ v)
    (φ : W1p0 mu U 2) :
    energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c)
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (φ : W1p mu U 2) =
      ℓ (W1p0.restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hU φ) := by
  rw [energyFormH1_sub_left hcoeff, energyFormH1_reflectPrincipal_compHyperplaneReflectionL hν hU,
    ← energyFormH1_sub_right hcoeff,
    ← hu (W1p0.restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hU φ)]
  exact (energyFormH1_reflectPrincipal_eq_restrictL hν hH hu0 _).trans (congrArg _
    (W1p0.coe_restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hU φ).symm)

/-- **Odd reflection of a weak solution with a right-hand side.** Let `H = {x | c₀ < ⟪x, ν⟫}`
with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, and let `U` be open with
`ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to `U ∩ H` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` with `f ∈ L²(U ∩ H)`, tested against
`H¹₀(U ∩ H)`. If the reflected coefficients are bounded on `U`, then the odd reflection
`u - u ∘ ρ` is a weak solution on `U` of the equation with the reflected coefficients and the
odd reflection `x ↦ 1_H f x - 1_H f (ρ x)` of `f` as right-hand side, tested against `H¹₀(U)`. -/
theorem energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x) (reflectDrift ν c₀ b x)
      (reflectDensity ν c₀ c x)) ⊤ (mu.restrict U))
    {u : W1p mu U 2} (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict (U ⊓ H)))
    (hu : ∀ v : W1p0 mu (U ⊓ H) 2,
      energyFormH1 a b c (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (v : W1p mu (U ⊓ H) 2) =
        ∫ x in U ⊓ H, f x * W1p.value (v : W1p mu (U ⊓ H) 2) x ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c)
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (φ : W1p mu U 2) =
      ∫ x in U, ((H : Set (EuclideanSpace ℝ ι)).indicator f x -
        (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)) *
          W1p.value (φ : W1p mu U 2) x ∂mu := by
  rw [energyFormH1_sub_left hcoeff, energyFormH1_reflectPrincipal_compHyperplaneReflectionL hν hU,
    ← energyFormH1_sub_right hcoeff, energyFormH1_reflectPrincipal_eq_restrictL hν hH hu0,
    ← W1p0.coe_restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hU φ, hu,
    W1p0.setIntegral_mul_value_restrictSubCompHyperplaneReflectionL _ hH hU hf]

/-- **Odd reflection for reflection-invariant coefficients.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, with linear part `R`, and let `U` be
open with `ρ U ⊆ U`. Let `a` be measurable on `U ∩ H`, uniformly elliptic on the part of `U` in the
closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` and invariant under the reflection, `a(ρ x) = R a(x) R` on
`U`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to `U ∩ H` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ L²(U ∩ H)`, tested against `H¹₀(U ∩ H)`. Then the odd reflection
`u - u ∘ ρ` is a weak solution on `U` of the same equation `-∂ᵢ(aⁱʲ ∂ⱼw) = g`, tested against
`H¹₀(U)`, whose right-hand side is the odd reflection `g x = 1_H f x - 1_H f (ρ x)` of `f`. -/
theorem energyFormH1_sub_compHyperplaneReflectionL_eq_setIntegral [Nonempty ι] (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    {lam Lam : ℝ} (ha : UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam)
    (ham : AEStronglyMeasurable a (mu.restrict (U ⊓ H)))
    (hinv : ∀ x ∈ U, ∀ η ξ, matrixBilinearForm (a (hyperplaneReflection ν c₀ x))
      ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) = matrixBilinearForm (a x) η ξ)
    {u : W1p mu U 2} (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict (U ⊓ H)))
    (hu : ∀ v : W1p0 mu (U ⊓ H) 2,
      energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (v : W1p mu (U ⊓ H) 2) =
        ∫ x in U ⊓ H, f x * W1p.value (v : W1p mu (U ⊓ H) 2) x ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 a 0 0 (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
        (φ : W1p mu U 2) =
      ∫ x in U, ((H : Set (EuclideanSpace ℝ ι)).indicator f x -
        (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)) *
          W1p.value (φ : W1p mu U 2) x ∂mu := by
  have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral hν hH hU
    (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0) hν hH hU
      ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
      (fun _ _ => by simp)) hu0 hf hu φ
  rw [reflectDrift_zero, reflectDensity_zero] at h
  rw [← h, energyFormH1_def, energyFormH1_def]
  -- Being invariant under the reflection, `a` is its own reflected coefficient on `U`.
  refine setIntegral_congr_fun U.isOpen.measurableSet fun x hx => ?_
  simp only [Pi.zero_apply, energyIntegrand_reflectPrincipal_zero_zero (hinv x hx)]

/-- **Odd reflection of a weak solution with a divergence-form right-hand side.** Let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, with
linear part `R`, and let `U` be open with `ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its
restriction to `U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f + ∂ᵢFⁱ` with
`f ∈ L²(U ∩ H)` and `F ∈ L²(U ∩ H; ℝⁿ)`, that is `a(u, v) = ∫ f v - ∫ ⟪F, ∇v⟫` for every
`v ∈ H¹₀(U ∩ H)`. If the reflected coefficients are bounded on `U`, then the odd reflection
`u - u ∘ ρ` is a weak solution on `U` of the equation with the reflected coefficients and the
reflected data: the odd reflection `x ↦ 1_H f x - 1_H f (ρ x)` of `f` and the field
`x ↦ 1_H F x - 1_H (R F) (ρ x)`, which is `F` on `H` and `-R F(ρ x)` on the other side. -/
theorem energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x) (reflectDrift ν c₀ b x)
      (reflectDensity ν c₀ c x)) ⊤ (mu.restrict U))
    {u : W1p mu U 2} (hu0 : ∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0)
    {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hf : MemLp f 2 (mu.restrict (U ⊓ H))) (hF : MemLp F 2 (mu.restrict (U ⊓ H)))
    (hu : ∀ v : W1p0 mu (U ⊓ H) 2,
      energyFormH1 a b c (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (v : W1p mu (U ⊓ H) 2) =
        ∫ x in U ⊓ H, f x * W1p.value (v : W1p mu (U ⊓ H) 2) x ∂mu -
          ∫ x in U ⊓ H, ⟪F x, W1p.gradient (v : W1p mu (U ⊓ H) 2) x⟫_ℝ ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 (reflectPrincipal ν c₀ a) (reflectDrift ν c₀ b) (reflectDensity ν c₀ c)
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (φ : W1p mu U 2) =
      ∫ x in U, ((H : Set (EuclideanSpace ℝ ι)).indicator f x -
        (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)) *
          W1p.value (φ : W1p mu U 2) x ∂mu -
        ∫ x in U, ⟪(H : Set (EuclideanSpace ℝ ι)).indicator F x -
          (H : Set (EuclideanSpace ℝ ι)).indicator (fun y => (ℝ ∙ ν)ᗮ.reflection (F y))
            (hyperplaneReflection ν c₀ x), W1p.gradient (φ : W1p mu U 2) x⟫_ℝ ∂mu := by
  rw [energyFormH1_sub_left hcoeff, energyFormH1_reflectPrincipal_compHyperplaneReflectionL hν hU,
    ← energyFormH1_sub_right hcoeff, energyFormH1_reflectPrincipal_eq_restrictL hν hH hu0,
    ← W1p0.coe_restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hU φ, hu,
    W1p0.setIntegral_mul_value_restrictSubCompHyperplaneReflectionL _ hH hU hf,
    W1p0.setIntegral_inner_gradient_restrictSubCompHyperplaneReflectionL _ hH hU hF]

/-- **The energy functional of the odd reflection.** Let `V` be open with `ρ V ⊆ V`, let
`u ∈ H¹(V)` vanish on `V ∖ H`, and let `u|_{V ∩ H}` solve `-Δu = -div F` weakly, tested against
`H¹₀(V ∩ H)`, with `F ∈ L²(V ∩ H)`, that is `∫_{V ∩ H} ⟨∇u, ∇v⟩ = ⟪F, ∇v⟫` for every
`v ∈ H¹₀(V ∩ H)`. Then the odd reflection `w = u - u ∘ ρ` satisfies
`|∫_V ⟨∇w, ∇φ⟩| ≤ 2 ‖F‖_{L²(V ∩ H)} ‖∇φ‖_{L²(V)}` for every `φ ∈ H¹₀(V)`. -/
theorem abs_energyFormH1_sub_compHyperplaneReflectionL_le (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {V : Opens (EuclideanSpace ℝ ι)}
    (hV : MapsTo (hyperplaneReflection ν c₀) V V) {u : W1p mu V 2}
    (hu0 : ∀ᵐ x ∂mu.restrict V, x ∉ H → W1p.value u x = 0)
    {F : Lp (EuclideanSpace ℝ ι) 2
      (mu.restrict ((V ⊓ H : Opens _) : Set (EuclideanSpace ℝ ι)))}
    (hu : ∀ v : W1p0 mu (V ⊓ H) 2, energyFormH1 (fun _ => 1) 0 0
      (W1p.restrictL (inf_le_left : V ⊓ H ≤ V) u) (v : W1p mu (V ⊓ H) 2) =
        ⟪F, W1p.gradient (v : W1p mu (V ⊓ H) 2)⟫_ℝ)
    (φ : W1p0 mu V 2) :
    |energyFormH1 (fun _ => 1) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hV u) (φ : W1p mu V 2)| ≤
        2 * ‖F‖ * ‖W1p.gradient (φ : W1p mu V 2)‖ := by
  have hℓ : ∀ v : W1p0 mu (V ⊓ H) 2, ((innerSL ℝ F).comp
      (W1p.gradientL.comp (w1p0Submodule mu (V ⊓ H) 2).toSubmodule.subtypeL)) v =
        ⟪F, W1p.gradient (v : W1p mu (V ⊓ H) 2)⟫_ℝ := fun _ => by
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, W1p.gradientL_apply,
      innerSL_apply_apply]
  -- The reflected equation for the Laplacian is the Laplacian itself.
  have hcoeff : MemLp (fun x => energyIntegrand
      (reflectPrincipal ν c₀ (fun _ => (1 : Matrix ι ι ℝ)) x)
      (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x)) ⊤ (mu.restrict V) := by
    simp only [reflectPrincipal_one, reflectDrift_zero, reflectDensity_zero, Pi.zero_apply]
    exact memLp_top_const (energyIntegrand (1 : Matrix ι ι ℝ) 0 0)
  have h := (energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL hν hH hV hcoeff hu0
    (fun v => (hu v).trans (hℓ v).symm) φ).trans (hℓ _)
  rw [reflectPrincipal_one, reflectDrift_zero, reflectDensity_zero] at h
  -- The reflected test function `(φ - φ ∘ ρ)|_{V ∩ H}` has at most twice the gradient norm.
  have hψ : ‖W1p.gradient (W1p0.restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hV φ :
      W1p mu (V ⊓ H) 2)‖ ≤ 2 * ‖W1p.gradient (φ : W1p mu V 2)‖ := by
    rw [W1p0.coe_restrictSubCompHyperplaneReflectionL]
    refine (W1p.norm_gradient_restrictL_le _ _).trans ?_
    rw [W1p.gradient_sub, two_mul]
    refine (norm_sub_le _ _).trans_eq ?_
    rw [W1p.norm_gradient_compHyperplaneReflectionL]
  refine (congrArg abs h).trans_le ((abs_real_inner_le_norm _ _).trans ?_)
  calc ‖F‖ * ‖W1p.gradient (W1p0.restrictSubCompHyperplaneReflectionL ENNReal.ofNat_ne_top hH hV φ :
        W1p mu (V ⊓ H) 2)‖ ≤ ‖F‖ * (2 * ‖W1p.gradient (φ : W1p mu V 2)‖) :=
        mul_le_mul_of_nonneg_left hψ (norm_nonneg _)
    _ = 2 * ‖F‖ * ‖W1p.gradient (φ : W1p mu V 2)‖ := by ring

end WeakSolution

end PDE

end TauCeti
