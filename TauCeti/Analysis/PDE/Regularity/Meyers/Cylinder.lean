/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Meyers.Example
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.Sobolev.WeakDeriv.LinearSurjection
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Meyers' example along a codimension-two subspace

Meyers' planar example (`TauCeti.Analysis.PDE.Regularity.Meyers.Example`), extended to `ℝ^{n+2}`
so as to be constant in the last `n` coordinates. For `0 < μ ≤ 1` let
`a = TauCeti.PDE.cylindricalMeyersCoefficient μ` be the coefficient field on `ℝ^{n+2}`

`a(x) = μ² I + (1 - μ²) y yᵀ / ‖y‖²`, where `y = (x₀, x₁, 0, …, 0)`,

whose eigenvalue in the direction `y` is `1` and in every direction orthogonal to it is `μ²`. It is
uniformly elliptic with constants `μ²` and `1`. The function
`u(x) = ‖(x₀, x₁)‖ ^ (μ - 1) x₀` (`TauCeti.PDE.cylindricalMeyersSolution μ`) is Meyers' planar
solution in the first two coordinates. It solves `div(a ∇u) = 0` weakly on every open set, across
the subspace `x₀ = x₁ = 0` where it is singular, and its gradient has size comparable to
`‖(x₀, x₁)‖ ^ (μ - 1)`. Since the singular set has codimension two, this is `p`-integrable near
the origin exactly for `p (1 - μ) < 2`, in every dimension.

Meyers' example itself is singular at a point, and in `ℝ^{n+2}` its gradient is `p`-integrable for
`p (1 - μ) < n + 2`, a range which tends to `p < n + 2`, not to `p ≤ 2`, as the ellipticity ratio
tends to infinity. The extension along the subspace is what shows, in every dimension, that the
higher integrability exponent in Meyers' theorem tends to `2` as the ellipticity ratio tends to
infinity (`TauCeti.Analysis.PDE.Regularity.Meyers.Exponent`).

## Main declarations

* `TauCeti.PDE.cylindricalMeyersCoefficient`, `TauCeti.PDE.cylindricalMeyersSolution`: the
  coefficient field and the solution.
* `TauCeti.PDE.uniformlyEllipticOn_cylindricalMeyersCoefficient`: for `0 < μ ≤ 1` the coefficient
  is uniformly elliptic with constants `μ²` and `1`;
  `TauCeti.PDE.uniformlyEllipticOn_smul_cylindricalMeyersCoefficient`: for `μ² = λ / Λ`, the field
  `Λ a` has constants `λ` and `Λ`.
* `TauCeti.PDE.energyFormH1_cylindricalMeyersCoefficient_eq_zero`: an element of `H¹(Ω)` equal to
  the solution is a weak solution of `div(a ∇u) = 0` on `Ω`.
* `TauCeti.PDE.exists_w1p_value_ae_eq_cylindricalMeyersSolution`: on a bounded open set the
  solution lies in `W^{1,p}` when `p (1 - μ) < 2`.
* `TauCeti.PDE.toReal_mul_one_sub_lt_two_of_memLp_gradient_cylindricalMeyersSolution`: if the weak
  gradient of the solution is `p`-integrable near the origin, then `p (1 - μ) < 2`.

## The argument

Write `P x = (x₀, x₁)` and `Rᵥ(x) = ‖P x‖ ^ (μ - 1) ⟪P x, v⟫` for `v` in the plane, so that
`u = R_{e₀}`. Each `Rᵥ` is a planar function composed with the surjective linear map `P`, so it is
weakly differentiable with its classical derivative by the weak chain rule along surjective linear
maps (`TauCeti.HasWeakFDerivOn.comp_surjective`). As for Meyers' planar example, away from the
singular subspace the pointwise identity

`ηᵀ a ∇u = μ (η₀ ∂₁R_{e₁} - η₁ ∂₀R_{e₁})`

exhibits `a ∇u` as `μ` times the rotated gradient of the stream function `R_{e₁}`, so the weak form
`∫ ⟨a ∇u, ∇φ⟩` vanishes because the mixed derivatives of the test function `φ` commute.
Integrability near the singular subspace is transferred to and from the plane along `P`
(`MeasureTheory.LocallyIntegrableOn.comp_surjective`,
`MeasureTheory.IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective`), where `‖y‖ ^ s` is
integrable near the origin exactly for `s > -2` (`TauCeti.integrableOn_norm_rpow_ball_iff`).

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5 (the planar
  example).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace LineDeriv Filter
open scoped NNReal ENNReal Topology InnerProductSpace Distributions Matrix Gradient

namespace TauCeti

namespace PDE

variable {n : ℕ} {μ : ℝ}

/-! ### The first two coordinates -/

/-- The projection `x ↦ (x₀, x₁)` onto the plane of the first two coordinates. -/
private def proj (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => !₂[x 0, x 1]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp }

private theorem proj_apply (x : EuclideanSpace ℝ (Fin (n + 2))) : proj n x = !₂[x 0, x 1] :=
  rfl

/-- The map `x ↦ (x₀, x₁, 0, …, 0)`. -/
private def lift (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1)
      map_add' := fun x y => by
        ext i
        simp only [PiLp.add_apply, PiLp.single_apply]
        split_ifs <;> ring
      map_smul' := fun c x => by
        ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring }

private theorem lift_apply (x : EuclideanSpace ℝ (Fin (n + 2))) :
    lift n x = EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1) :=
  rfl

private theorem proj_surjective : Function.Surjective (proj n) := fun y =>
  ⟨EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1), by
    ext i
    fin_cases i <;> simp [proj_apply]⟩

private theorem inner_proj (x w : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪proj n x, proj n w⟫_ℝ = x 0 * w 0 + x 1 * w 1 := by
  simp [proj_apply, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem inner_proj_single_zero (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪proj n x, EuclideanSpace.single 0 (1 : ℝ)⟫_ℝ = x 0 := by
  simp [proj_apply, EuclideanSpace.inner_single_right]

private theorem inner_proj_single_one (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪proj n x, EuclideanSpace.single 1 (1 : ℝ)⟫_ℝ = x 1 := by
  simp [proj_apply, EuclideanSpace.inner_single_right]

private theorem lift_apply_zero (x : EuclideanSpace ℝ (Fin (n + 2))) : lift n x 0 = x 0 := by
  simp [lift_apply]

private theorem lift_apply_one (x : EuclideanSpace ℝ (Fin (n + 2))) : lift n x 1 = x 1 := by
  simp [lift_apply]

private theorem inner_lift (x w : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪lift n x, w⟫_ℝ = x 0 * w 0 + x 1 * w 1 := by
  simp [lift_apply, inner_add_left, EuclideanSpace.inner_single_left]

private theorem norm_proj_sq (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖proj n x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_proj, sq, sq]

private theorem norm_lift (x : EuclideanSpace ℝ (Fin (n + 2))) : ‖lift n x‖ = ‖proj n x‖ := by
  have h : ‖lift n x‖ ^ 2 = ‖proj n x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_lift, norm_proj_sq]
    simp [lift_apply, sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

private theorem norm_proj_le (x : EuclideanSpace ℝ (Fin (n + 2))) : ‖proj n x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_proj_sq, EuclideanSpace.real_norm_sq_eq]
  have : ∑ i ∈ ({0, 1} : Finset (Fin (n + 2))), x i ^ 2 ≤ ∑ i, x i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  simpa [Finset.sum_pair (show (0 : Fin (n + 2)) ≠ 1 by simp), sq_abs] using this

/-- Almost every point lies off the subspace `x₀ = x₁ = 0`. -/
private theorem ae_proj_ne_zero :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 2)))), proj n x ≠ 0 := by
  have h := (ae_comp_linearMap_mem_iff
    ((proj n : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) volume volume proj_surjective
    (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 2))).compl).2
      (compl_mem_ae_iff.2 (measure_singleton _))
  simpa using h

/-! ### The coefficient field -/

/-- **Meyers' coefficient field along a codimension-two subspace** on `ℝ^{n+2}`,
`a(x) = μ² I + (1 - μ²) y yᵀ / ‖y‖²` with `y = (x₀, x₁, 0, …, 0)`. Its eigenvalue in the direction
`y` is `1` and in the directions orthogonal to `y` is `μ²`; on the subspace `x₀ = x₁ = 0`, where
the direction is undefined, it is `μ² I`. It is the radial coefficient field
`TauCeti.PDE.radialCoefficient (μ ^ 2) (1 - μ ^ 2)` evaluated at `y`, and depends only on
`(x₀, x₁)`. -/
def cylindricalMeyersCoefficient (μ : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  radialCoefficient (μ ^ 2) (1 - μ ^ 2)
    (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1))

/-- Unfolding `TauCeti.PDE.cylindricalMeyersCoefficient`. -/
theorem cylindricalMeyersCoefficient_apply (x : EuclideanSpace ℝ (Fin (n + 2))) :
    cylindricalMeyersCoefficient μ x = radialCoefficient (μ ^ 2) (1 - μ ^ 2)
      (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1)) :=
  (rfl)

/-- The bilinear form of the cylindrical Meyers coefficient: with `y = (x₀, x₁, 0, …, 0)`,
`ηᵀ a(x) ξ = μ² ⟪η, ξ⟫ + (1 - μ²) ⟪η, y⟫ ⟪y, ξ⟫ / ‖y‖²`. -/
theorem dotProduct_cylindricalMeyersCoefficient_mulVec (x η ξ : EuclideanSpace ℝ (Fin (n + 2))) :
    η ⬝ᵥ (cylindricalMeyersCoefficient μ x *ᵥ ξ) = μ ^ 2 * ⟪η, ξ⟫_ℝ +
      (1 - μ ^ 2) / (x 0 ^ 2 + x 1 ^ 2) * ((η 0 * x 0 + η 1 * x 1) * (x 0 * ξ 0 + x 1 * ξ 1)) := by
  rw [cylindricalMeyersCoefficient_apply, dotProduct_radialCoefficient_mulVec]
  change _ + _ / ‖lift n x‖ ^ 2 * (⟪η, lift n x⟫_ℝ * ⟪lift n x, ξ⟫_ℝ) = _
  rw [norm_lift, norm_proj_sq, real_inner_comm (lift n x) η, inner_lift, inner_lift]
  ring

/-- For `0 < μ ≤ 1` the cylindrical Meyers coefficient is uniformly elliptic with constants `μ²`
and `1`, so its ellipticity ratio is `1 / μ²`. -/
theorem uniformlyEllipticOn_cylindricalMeyersCoefficient (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :
    UniformlyEllipticOn Ω (cylindricalMeyersCoefficient μ) (μ ^ 2) 1 := by
  have h := uniformlyEllipticOn_radialCoefficient (n := n + 2) (α := μ ^ 2) (β := 1 - μ ^ 2)
    (pow_pos hμ0 2) (sub_nonneg.2 (pow_le_one₀ (n := 2) hμ0.le hμ1)) univ
  rw [add_sub_cancel] at h
  rw [uniformlyEllipticOn_iff] at h ⊢
  exact ⟨h.1, h.2.1, fun x _ => h.2.2 (mem_univ _)⟩

/-- **The cylindrical Meyers coefficient at prescribed ellipticity constants.** Let
`0 < λ ≤ Λ` and let `μ > 0` satisfy `μ² = λ / Λ`. Then `Λ a`, for the cylindrical Meyers
coefficient `a`, is uniformly elliptic with constants `λ` and `Λ`. -/
theorem uniformlyEllipticOn_smul_cylindricalMeyersCoefficient (hμ0 : 0 < μ) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hμ : μ ^ 2 = lam / Lam)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :
    UniformlyEllipticOn Ω (Lam • cylindricalMeyersCoefficient μ) lam Lam := by
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  have hμ1 : μ ≤ 1 := by
    have h1 : μ ^ 2 ≤ 1 := by rw [hμ]; exact (div_le_one hLam0).2 hLam
    nlinarith
  have := (uniformlyEllipticOn_cylindricalMeyersCoefficient hμ0 hμ1 Ω).const_smul hLam0
  rwa [hμ, mul_div_cancel₀ _ hLam0.ne', mul_one] at this

/-- The cylindrical Meyers coefficient is strongly measurable. -/
theorem stronglyMeasurable_cylindricalMeyersCoefficient :
    StronglyMeasurable (cylindricalMeyersCoefficient (n := n) μ) :=
  stronglyMeasurable_radialCoefficient.comp_measurable (lift n).continuous.measurable

/-! ### The solution and its weak derivatives -/

/-- **Meyers' solution along a codimension-two subspace**, `u(x) = ‖(x₀, x₁)‖ ^ (μ - 1) x₀`: Meyers'
planar solution `TauCeti.PDE.meyersSolution` in the first two coordinates, constant in the others.
It solves `div(a ∇u) = 0` for `a = TauCeti.PDE.cylindricalMeyersCoefficient μ`. -/
def cylindricalMeyersSolution (μ : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) : ℝ :=
  meyersSolution (n := 0) μ !₂[x 0, x 1]

/-- Unfolding `TauCeti.PDE.cylindricalMeyersSolution`. -/
theorem cylindricalMeyersSolution_apply (x : EuclideanSpace ℝ (Fin (n + 2))) :
    cylindricalMeyersSolution μ x = meyersSolution (n := 0) μ !₂[x 0, x 1] :=
  (rfl)

/-- The function `Rᵥ(x) = ‖P x‖ ^ (μ - 1) ⟪P x, v⟫`, with `P x = (x₀, x₁)`. -/
private def cylCoord (μ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ℝ :=
  ‖proj n x‖ ^ (μ - 1) * ⟪proj n x, v⟫_ℝ

/-- The weak derivative of `TauCeti.PDE.cylCoord`, its classical derivative off `x₀ = x₁ = 0`. -/
private def cylCoordDeriv (μ : ℝ) (v : EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] ℝ :=
  (‖proj n x‖ ^ (μ - 1) • innerSL ℝ v +
    ((μ - 1) * ‖proj n x‖ ^ (μ - 1 - 2) * ⟪proj n x, v⟫_ℝ) • innerSL ℝ (proj n x)).comp (proj n)

private theorem hasWeakFDerivOn_cylCoord (hμ0 : 0 < μ) (v : EuclideanSpace ℝ (Fin 2))
    (Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))) :
    HasWeakFDerivOn volume Ω (cylCoord μ v) (cylCoordDeriv μ v) := by
  have h := (hasWeakFDerivOn_norm_rpow_mul_inner (μ := volume) (s := μ - 1)
    (by rw [finrank_euclideanSpace_fin]; push_cast; linarith) v ⊤).comp_surjective
    (μ := volume) (proj_surjective (n := n))
  exact h.mono fun x _ => trivial

/-- The candidate gradient `‖P x‖ ^ (μ - 1) e₀ + (μ - 1) ‖P x‖ ^ (μ - 3) x₀ (x₀, x₁, 0, …, 0)`. -/
private def cylGrad (μ : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  ‖proj n x‖ ^ (μ - 1) • EuclideanSpace.single 0 1 +
    ((μ - 1) * ‖proj n x‖ ^ (μ - 1 - 2) * x 0) • lift n x

private theorem cylCoordDeriv_zero (x : EuclideanSpace ℝ (Fin (n + 2))) :
    cylCoordDeriv μ (EuclideanSpace.single 0 1) x = innerSL ℝ (cylGrad μ x) := by
  ext w
  have h1 : ⟪EuclideanSpace.single 0 (1 : ℝ), proj n w⟫_ℝ = w 0 := by
    rw [real_inner_comm, inner_proj_single_zero]
  have h2 : ⟪EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ), w⟫_ℝ = w 0 := by
    simp [EuclideanSpace.inner_single_left]
  simp only [cylCoordDeriv, cylGrad, ContinuousLinearMap.coe_comp, Function.comp_apply,
    add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, inner_add_left,
    real_inner_smul_left, inner_proj, inner_lift, inner_proj_single_zero, h1, h2]

private theorem cylCoord_zero :
    cylCoord μ (EuclideanSpace.single 0 1) = cylindricalMeyersSolution (n := n) μ := by
  funext x
  rw [cylCoord, inner_proj_single_zero, cylindricalMeyersSolution_apply, meyersSolution_apply,
    proj_apply]
  simp

private theorem hasWeakFDerivOn_cylindricalMeyersSolution (hμ0 : 0 < μ)
    (Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))) :
    HasWeakFDerivOn volume Ω (cylindricalMeyersSolution μ) fun x => innerSL ℝ (cylGrad μ x) := by
  have h := hasWeakFDerivOn_cylCoord (n := n) hμ0 (EuclideanSpace.single 0 1) Ω
  rwa [cylCoord_zero, show cylCoordDeriv μ (EuclideanSpace.single 0 1) =
    fun x => innerSL ℝ (cylGrad (n := n) μ x) from funext cylCoordDeriv_zero] at h

/-- The weak gradient of an element of `W^{1,p}(Ω)` equal to the cylindrical solution. -/
private theorem gradient_ae_eq_cylGrad (hμ0 : 0 < μ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω p)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      cylindricalMeyersSolution μ) :
    W1p.gradient u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))] cylGrad μ := by
  filter_upwards [((W1p.hasWeakFDerivOn u).congr_ae hu).ae_eq
    (hasWeakFDerivOn_cylindricalMeyersSolution hμ0 Ω)] with x hx
  exact innerSL_inj.1 hx

/-! ### The weak equation -/

/-- Off the subspace `x₀ = x₁ = 0` the coefficient maps the gradient of `u = R_{e₀}` to `μ` times
the rotated gradient of the stream function `R_{e₁}`: `ηᵀ a ∇u = μ (η₀ ∂₁R_{e₁} - η₁ ∂₀R_{e₁})`. -/
private theorem dotProduct_coeff_mulVec_cylGrad {x : EuclideanSpace ℝ (Fin (n + 2))}
    (hx : proj n x ≠ 0) (η : EuclideanSpace ℝ (Fin (n + 2))) :
    η ⬝ᵥ (cylindricalMeyersCoefficient μ x *ᵥ cylGrad μ x) =
      μ * (η 0 * cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 1 1) -
        η 1 * cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 0 1)) := by
  have hρ : 0 < ‖proj n x‖ := norm_pos_iff.2 hx
  have hab : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by rw [← norm_proj_sq]; positivity
  have hs : ‖proj n x‖ ^ (μ - 1) = ‖proj n x‖ ^ (μ - 1 - 2) * (x 0 ^ 2 + x 1 ^ 2) := by
    rw [← norm_proj_sq, ← Real.rpow_natCast, ← Real.rpow_add hρ]
    norm_num
  have hP : ∀ w : EuclideanSpace ℝ (Fin (n + 2)),
      ⟪EuclideanSpace.single (1 : Fin 2) (1 : ℝ), proj n w⟫_ℝ = w 1 := fun w => by
    rw [real_inner_comm, inner_proj_single_one]
  have hηl : ⟪η, lift n x⟫_ℝ = η 0 * x 0 + η 1 * x 1 := by
    rw [real_inner_comm, inner_lift]
    ring
  have hη0 : ⟪η, EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)⟫_ℝ = η 0 := by
    simp [EuclideanSpace.inner_single_right]
  simp only [dotProduct_cylindricalMeyersCoefficient_mulVec, cylGrad, cylCoordDeriv,
    inner_add_right, real_inner_smul_right, hηl, hη0, ContinuousLinearMap.coe_comp,
    Function.comp_apply, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, hP,
    inner_proj, inner_proj_single_one, PiLp.add_apply, PiLp.smul_apply, lift_apply_zero,
    lift_apply_one, PiLp.single_apply]
  simp only [show (0 : Fin (n + 2)) ≠ 1 by simp, show (1 : Fin (n + 2)) ≠ 0 by simp, ite_true,
    ite_false]
  rw [hs]
  generalize ‖proj n x‖ ^ (μ - 1 - 2) = t
  field_simp
  ring

/-- The mixed derivatives of a test function `φ` commute, so, by the weak derivative identities of
the stream function `R_{e₁}`, `∫ ∂₀φ ∂₁R_{e₁} = ∫ ∂₁φ ∂₀R_{e₁}`. -/
private theorem integral_lineDeriv_smul_cylCoordDeriv_comm (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (φ : 𝓓(Ω, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single 0 1) •
        cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 1 1) =
      ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single 1 1) •
        cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 0 1) := by
  have hψ := hasWeakFDerivOn_cylCoord (n := n) hμ0 (EuclideanSpace.single 1 1) Ω
  have h1 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single 1 (1 : ℝ)))
    (∂_{EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)} φ)
  have h0 := HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (hψ.hasWeakLineDerivOn (EuclideanSpace.single 0 (1 : ℝ)))
    (∂_{EuclideanSpace.single (1 : Fin (n + 2)) (1 : ℝ)} φ)
  simp only [TestFunction.lineDeriv_lineDerivOp_comm φ
    (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) (EuclideanSpace.single 1 (1 : ℝ))] at h1
  rw [h0] at h1
  simpa [TestFunction.lineDerivOp_apply] using h1.symm

/-- The weak equation against a test function: by the pointwise identity
`a ∇u = μ (∂₁R_{e₁}, -∂₀R_{e₁}, 0, …, 0)`, the energy form is
`μ ∫ (∂₀φ ∂₁R_{e₁} - ∂₁φ ∂₀R_{e₁}) = 0`. -/
private theorem energyFormH1_cylindricalMeyersCoefficient_ofTestFunctionₗ_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      cylindricalMeyersSolution μ)
    (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 (cylindricalMeyersCoefficient μ) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) = 0 := by
  have hloc : ∀ j : Fin (n + 2), LocallyIntegrableOn
      (fun x => cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single j 1)) Ω
      volume := fun j =>
    ((hasWeakFDerivOn_cylCoord hμ0 (EuclideanSpace.single 1 1) Ω).hasWeakLineDerivOn
      (EuclideanSpace.single j (1 : ℝ))).locallyIntegrableOn_deriv
  have hd : ∀ x i, (∇ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x) i =
      lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x i
    rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, ← inner_gradient_left,
      EuclideanSpace.inner_single_right]
    simp
  -- The two integrands `∂₀φ ∂₁R_{e₁}` and `∂₁φ ∂₀R_{e₁}`, integrable on `Ω`.
  set A : EuclideanSpace ℝ (Fin (n + 2)) → ℝ := fun x =>
    lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single 0 1) •
      cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 1 1) with hA
  set B : EuclideanSpace ℝ (Fin (n + 2)) → ℝ := fun x =>
    lineDeriv ℝ (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℝ) x (EuclideanSpace.single 1 1) •
      cylCoordDeriv μ (EuclideanSpace.single 1 1) x (EuclideanSpace.single 0 1) with hB
  have hAi : Integrable A := integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc 1) φ _
  have hBi : Integrable B := integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc 0) φ _
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Ω, matrixBilinearForm (cylindricalMeyersCoefficient μ x)
        (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 φ) x) (W1p.gradient u x)
      = ∫ x in Ω, μ * (A x - B x) := by
        refine integral_congr_ae ?_
        filter_upwards [gradient_ae_eq_cylGrad hμ0 u hu,
          gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
          ae_restrict_of_ae ae_proj_ne_zero] with x hx hφ h0
        rw [W1p.gradient_ofTestFunctionₗ, hφ, hx, matrixBilinearForm_apply,
          dotProduct_coeff_mulVec_cylGrad h0]
        simp only [hA, hB, hd, smul_eq_mul]
    _ = μ * ((∫ x, A x) - ∫ x, B x) := by
        rw [integral_const_mul, integral_sub hAi.restrict hBi.restrict, hA, hB,
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
          setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
    _ = 0 := by
        rw [hA, hB, integral_lineDeriv_smul_cylCoordDeriv_comm hμ0 φ, sub_self, mul_zero]

/-- **The cylindrical Meyers solution is a weak solution.** For `μ > 0` and every open
`Ω ⊆ ℝ^{n+2}`, an element `u ∈ H¹(Ω)` equal to `‖(x₀, x₁)‖ ^ (μ - 1) x₀` almost everywhere on `Ω`
is a weak solution of `div(a ∇u) = 0` for the cylindrical Meyers coefficient `a`:
`∫_Ω ⟨a ∇u, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`. The equation also holds across the subspace
`x₀ = x₁ = 0`, where, for `μ ≠ 1`, `a` is discontinuous, and for `μ < 1` also `∇u` is
unbounded. -/
theorem energyFormH1_cylindricalMeyersCoefficient_eq_zero (hμ0 : 0 < μ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      cylindricalMeyersSolution μ)
    (v : W1p0 volume Ω 2) :
    energyFormH1 (cylindricalMeyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := by
  have hcoeff := memLp_energyIntegrand_of_bounds (Omega := Ω) (mu := volume)
    (b := 0) (c := 0) (Lam := |μ ^ 2| + |1 - μ ^ 2|) (beta := 0) (gamma := 0) (by positivity)
    stronglyMeasurable_cylindricalMeyersCoefficient.aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x _ η ξ => by
      rw [cylindricalMeyersCoefficient_apply]
      exact abs_dotProduct_radialCoefficient_mulVec_le (α := μ ^ 2) (β := 1 - μ ^ 2) _ η ξ)
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hclosed : IsClosed {w : W1p volume Ω 2 | energyFormH1L hcoeff u w = 0} :=
    isClosed_eq (energyFormH1L hcoeff u).continuous continuous_const
  refine (energyFormH1L_apply hcoeff u _).symm.trans
    (w1p0Submodule_subset_of_isClosed hclosed (fun φ => ?_) v.property)
  rw [Set.mem_ofPred_eq, energyFormH1L_apply]
  exact energyFormH1_cylindricalMeyersCoefficient_ofTestFunctionₗ_eq_zero hμ0 u hu φ

/-- **The cylindrical Meyers solution solves the equation of every multiple of the coefficient.**
For `μ > 0`, every `c` and every open `Ω ⊆ ℝ^{n+2}`, an element `u ∈ H¹(Ω)` equal to
`‖(x₀, x₁)‖ ^ (μ - 1) x₀` almost everywhere on `Ω` satisfies `∫_Ω ⟨c a ∇u, ∇v⟩ = 0` for every
`v ∈ H¹₀(Ω)`, where `a` is the cylindrical Meyers coefficient. -/
theorem energyFormH1_smul_cylindricalMeyersCoefficient_eq_zero (hμ0 : 0 < μ) (c : ℝ)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω 2)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      cylindricalMeyersSolution μ)
    (v : W1p0 volume Ω 2) :
    energyFormH1 (c • cylindricalMeyersCoefficient μ) 0 0 u (v : W1p volume Ω 2) = 0 := by
  have := energyFormH1_smul_coefficients (cylindricalMeyersCoefficient μ) 0 0 c u
    (v : W1p volume Ω 2)
  rw [smul_zero, smul_zero] at this
  rw [this, energyFormH1_cylindricalMeyersCoefficient_eq_zero hμ0 u hu v, mul_zero]

/-! ### Integrability of the gradient -/

/-- Off the subspace `x₀ = x₁ = 0`, the candidate gradient has the length of the gradient of
Meyers' planar solution at `(x₀, x₁)`. -/
private theorem norm_cylGrad {x : EuclideanSpace ℝ (Fin (n + 2))} (hx : proj n x ≠ 0) :
    ‖cylGrad μ x‖ = ‖∇ (meyersSolution (n := 0) μ) (proj n x)‖ := by
  have hl : ⟪EuclideanSpace.single 0 (1 : ℝ), lift n x⟫_ℝ = x 0 := by
    rw [real_inner_comm, inner_lift]
    simp
  have hp : ⟪EuclideanSpace.single 0 (1 : ℝ), proj n x⟫_ℝ = x 0 := by
    rw [real_inner_comm, inner_proj_single_zero]
  have h0 : proj n x 0 = x 0 := by simp [proj_apply]
  rw [gradient_meyersSolution hx, h0, show μ - 3 = μ - 1 - 2 by ring]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [cylGrad, norm_add_sq_real, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, hl, hp, norm_smul, norm_smul, norm_smul,
    norm_smul, norm_lift, PiLp.norm_single, PiLp.norm_single]

private theorem measurable_cylGrad : Measurable (cylGrad (n := n) μ) := by
  unfold cylGrad
  fun_prop

/-- **Sobolev integrability of the cylindrical Meyers solution.** Let `0 < μ`, `1 ≤ p < ∞`, and
let `Ω ⊆ ℝ^{n+2}` be a bounded open set. If `p (1 - μ) < 2`, in particular for every `p` if
`μ ≥ 1`, then `‖(x₀, x₁)‖ ^ (μ - 1) x₀` lies in `W^{1,p}(Ω)`: its gradient is bounded by a
multiple of `‖(x₀, x₁)‖ ^ (μ - 1)`, which is `p`-integrable near the subspace `x₀ = x₁ = 0` in
this range. -/
theorem exists_w1p_value_ae_eq_cylindricalMeyersSolution (hμ0 : 0 < μ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))))
    (h : p.toReal * (1 - μ) < 2) :
    ∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
        cylindricalMeyersSolution μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : EuclideanSpace ℝ (Fin (n + 2)))
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  -- The solution is bounded by `R ^ μ` on `Ω`.
  have hsol : cylindricalMeyersSolution (n := n) μ = meyersSolution μ ∘ proj n := rfl
  have hu : MemLp (cylindricalMeyersSolution μ) p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) := by
    refine MemLp.of_bound (hsol ▸ ((continuous_meyersSolution hμ0).comp
      (proj n).continuous).aestronglyMeasurable) (R ^ μ) ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs, hsol, Function.comp_apply]
    refine (abs_meyersSolution_le _).trans (Real.rpow_le_rpow (norm_nonneg _) ?_ hμ0.le)
    exact (norm_proj_le x).trans (mem_closedBall_zero_iff.1 (hR hx))
  -- `‖(x₀, x₁)‖ ^ (p (μ - 1))` is locally integrable, as the pullback of a planar function.
  have hloc : LocallyIntegrable (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ (p.toReal * (μ - 1)))
      volume :=
    locallyIntegrable_of_norm_le_rpow (by simp) (C := 1) (α := -(p.toReal * (μ - 1)))
      (by rw [finrank_euclideanSpace_fin]; push_cast; nlinarith)
      (ae_of_all _ fun y => by
        rw [neg_neg, one_mul, Real.norm_of_nonneg (by positivity)])
      (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin 2) =>
        ‖y‖ ^ (p.toReal * (μ - 1))).aestronglyMeasurable
  have hlocP := (hloc.locallyIntegrableOn univ).comp_surjective isOpen_univ
    (proj_surjective (n := n)) (μ := volume)
  rw [preimage_univ, locallyIntegrableOn_univ] at hlocP
  have hker : IntegrableOn (fun x => ‖proj n x‖ ^ (p.toReal * (μ - 1)))
      (Ω : Set (EuclideanSpace ℝ (Fin (n + 2)))) :=
    (hlocP.integrableOn_isCompact (isCompact_closedBall 0 R)).mono_set hR
  have hg : MemLp (cylGrad μ) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))) := by
    refine (integrable_norm_rpow_iff measurable_cylGrad.aestronglyMeasurable hp0 hp).1 ?_
    refine (hker.const_mul ((1 + |μ - 1|) ^ p.toReal)).mono'
      (measurable_cylGrad.norm.pow_const _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae ae_proj_ne_zero] with x hx
    rw [Real.norm_of_nonneg (by positivity), mul_comm p.toReal, Real.rpow_mul (norm_nonneg _),
      ← Real.mul_rpow (by positivity) (by positivity), norm_cylGrad hx]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_gradient_meyersSolution_le hx) hpr.le
  refine ⟨W1p.mk hu.toLp hg.toLp
    (((hasWeakFDerivOn_cylindricalMeyersSolution hμ0 Ω).congr_ae hu.coeFn_toLp.symm).congr_ae_deriv
      (hg.coeFn_toLp.mono fun x hx => by simp only [hx])), ?_⟩
  rw [W1p.value_mk]
  exact hu.coeFn_toLp

/-- **The gradient of the cylindrical Meyers solution is not `p`-integrable near the origin for
large `p`.** Let `μ > 0` and let `u ∈ W^{1,q}(Ω)` be equal to `‖(x₀, x₁)‖ ^ (μ - 1) x₀` almost
everywhere on an open set `Ω` containing the origin. If its weak gradient is `p`-integrable on a
neighbourhood of the origin, then `p (1 - μ) < 2`. For finite `p` and `μ < 1` this says
`p < 2 / (1 - μ)`: near the subspace `x₀ = x₁ = 0` the gradient is bounded below by
`μ ‖(x₀, x₁)‖ ^ (μ - 1)`, which is `p`-integrable in the transverse plane only in this range. For
`p = ∞` the conclusion is trivial, since `p.toReal = 0`. -/
theorem toReal_mul_one_sub_lt_two_of_memLp_gradient_cylindricalMeyersSolution (hμ0 : 0 < μ)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {Ω : Opens (EuclideanSpace ℝ (Fin (n + 2)))} (u : W1p volume Ω q)
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 2))))]
      cylindricalMeyersSolution μ)
    (h0 : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ Ω) {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (hs : s ∈ 𝓝 0) {p : ℝ≥0∞} (hmem : MemLp (W1p.gradient u) p (volume.restrict s)) :
    p.toReal * (1 - μ) < 2 := by
  rcases le_or_gt 1 μ with hμ1 | hμ1
  · nlinarith [ENNReal.toReal_nonneg (a := p)]
  rcases (ENNReal.toReal_nonneg (a := p)).eq_or_lt with hpr | hpr
  · rw [← hpr, zero_mul]
    positivity
  obtain ⟨hp0, hp⟩ := ENNReal.toReal_pos_iff.1 hpr
  have hs' : s ∩ Ω ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin (n + 2))) := inter_mem hs (Ω.isOpen.mem_nhds h0)
  -- On `s ∩ Ω` the weak gradient is the candidate gradient.
  have hG : MemLp (cylGrad μ) p (volume.restrict (s ∩ Ω)) :=
    (hmem.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).ae_eq
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right (gradient_ae_eq_cylGrad hμ0 u hu))
  have hint : IntegrableOn (fun x => ‖cylGrad μ x‖ ^ p.toReal) (s ∩ Ω) :=
    hG.integrable_norm_rpow hp0.ne' hp.ne
  -- `‖(x₀, x₁)‖ ^ (p (μ - 1)) ≤ μ ^ (-p) ‖∇u‖ ^ p` off the subspace `x₀ = x₁ = 0`.
  have hpow : IntegrableOn ((fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ (p.toReal * (μ - 1))) ∘
      proj n) (s ∩ Ω) := by
    refine (hint.const_mul (μ ^ (-p.toReal))).mono'
      (by fun_prop : Measurable ((fun y : EuclideanSpace ℝ (Fin 2) =>
        ‖y‖ ^ (p.toReal * (μ - 1))) ∘ proj n)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae ae_proj_ne_zero] with x hx
    rw [Function.comp_apply, Real.norm_of_nonneg (by positivity), mul_comm p.toReal,
      Real.rpow_mul (norm_nonneg _), Real.rpow_neg hμ0.le, le_inv_mul_iff₀ (by positivity),
      ← Real.mul_rpow hμ0.le (by positivity)]
    rw [norm_cylGrad hx]
    exact Real.rpow_le_rpow (by positivity) (mul_rpow_le_norm_gradient_meyersSolution hμ0 hμ1.le hx)
      hpr.le
  obtain ⟨t, ht, hgt⟩ := hpow.exists_mem_nhds_integrableOn_of_comp_surjective (ν := volume) hs'
    proj_surjective
  rw [map_zero] at ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ht
  have := (integrableOn_norm_rpow_ball_iff hr).1 (hgt.mono_set hball)
  rw [finrank_euclideanSpace_fin] at this
  push_cast at this
  nlinarith

end PDE

end TauCeti
