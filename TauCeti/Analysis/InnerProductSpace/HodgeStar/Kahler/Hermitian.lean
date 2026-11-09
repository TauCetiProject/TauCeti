/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.ComplexStructure

/-!
# The Hermitian part of a two-form and its extreme eigenvalues in dimension four

Let `V` be a real inner product space with an orthogonal almost complex structure `J`, and let
`F ∈ ⋀² V` represent the two-form `F(u, w) = ⟪F, u ∧ w⟫`. The **Hermitian part** of `F` is the
symmetric bilinear form

`B(v, w) = (F(v, J w) + F(w, J v)) / 2`

(`TauCeti.AlmostComplexStructure.hermitianForm`). Its quadratic form is `B(v, v) = F(v, J v)`.
For the Kähler two-vector `ω` of `J`, `B` is the metric (`hermitianForm_kahlerForm`).

In dimension four, for the complex orientation, the two-forms split as
`⋀² = ℝ ω ⊕ (ℝ ω)ᗮ ∩ Λ⁺ ⊕ Λ⁻`. The Hermitian part only sees the first and last summands:

* a self-dual `η` has `B = (⟪ω, η⟫ / 2) g`, so the anti-`J`-invariant self-dual forms
  `(ℝ ω)ᗮ ∩ Λ⁺` contribute zero (`hermitianForm_eq_zero_of_hodgeStar_eq_self_of_inner_eq_zero`);
* an anti-self-dual `η` is `J`-invariant (`AlmostComplexStructure.lieMap_of_hodgeStar_eq_neg`), so
  its contraction `A u = u ⌟ η` commutes with `J`, and `B(v, w) = ⟪A v, J w⟫ = -⟪J A v, w⟫`.
  Since `(J A)² = -A² = ‖η‖² / 2`, the values of `B(v, v)` on the unit sphere range over
  `[-‖η‖ / √2, ‖η‖ / √2]`. The bound `|B(v, v)| ≤ (‖η‖ / √2) ‖v‖²` holds more generally for
  every `η` orthogonal to `ω` (`abs_hermitianForm_apply_self_le_of_inner_kahlerForm_eq_zero`),
  by pairing `η` with `2 v ∧ J v - ‖v‖² ω`.

Write `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. Then `B(v, w) = c ⟪v, w⟫ + F⁻(v, J w)`
(`hermitianForm_apply_eq`), and the smallest and largest values of `B(v, v)` on the unit sphere
are `c - ‖F⁻‖ / √2` and `c + ‖F⁻‖ / √2` (`isLeast_hermitianForm_apply_self`,
`isGreatest_hermitianForm_apply_self`). Hence a lower bound `B ≥ -C g` controls the
anti-self-dual part by the `ω`-component, `‖F⁻‖ ≤ √2 (c + C)`
(`norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self`).

This is the pointwise algebra of Taubes's estimate for the anti-self-dual curvature of solutions
of the large-parameter Seiberg–Witten equations on a symplectic four-manifold: there `F` is the
real curvature form `i F_a`, the curvature equation determines `c` up to bounded terms, and a lower
bound on the Hermitian part `B` therefore bounds `|F_a⁻|`.

As in `TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic`, the four-dimensional results
take a positively oriented orthonormal basis `e` with `J e₀ = e₁` and `J e₂ = e₃` as a witness
that the orientation is the complex one.

## Main definitions

* `TauCeti.AlmostComplexStructure.hermitianForm J F`: the Hermitian part `B` of `F`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `hermitianForm_apply_self`: `B(v, v) = F(v, J v)`.
* `hermitianForm_kahlerForm`: the Hermitian part of `ω` is the inner product.
* `twoVectorContraction_apply_apply_of_lieMap_eq_zero`, `hermitianForm_apply_of_lieMap_eq_zero`:
  for an orthogonal `J` and a `J`-invariant `η`, the contraction by `η` commutes with `J` and
  `B(v, w) = η(v, J w)`.
* `hermitianForm_lieMap`: the anti-`J`-invariant part `D_J ξ` of a two-form has zero Hermitian
  part.
* `abs_hermitianForm_apply_self_le_of_inner_kahlerForm_eq_zero`: `|B(v, v)| ≤ (‖η‖ / √2) ‖v‖²`
  for `η` orthogonal to `ω`.
* `inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`: `ω` is orthogonal to every anti-self-dual form.
* `hermitianForm_apply_of_hodgeStar_eq_self`: `B = (⟪ω, η⟫ / 2) g` for self-dual `η`.
* `twoVectorContraction_apply_apply_of_hodgeStar_eq_neg`: the contraction by an anti-self-dual
  two-vector commutes with `J`.
* `hermitianForm_apply_eq`: `B(v, w) = c ⟪v, w⟫ + F⁻(v, J w)`.
* `abs_hermitianForm_apply_self_sub_le`: `|B(v, v) - c ‖v‖²| ≤ (‖F⁻‖ / √2) ‖v‖²`.
* `isLeast_hermitianForm_apply_self`, `isGreatest_hermitianForm_apply_self`: the extreme values
  `c ∓ ‖F⁻‖ / √2` of `B` on the unit sphere are attained.
* `norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self`,
  `forall_le_hermitianForm_apply_self_iff`: `B ≥ -C g` holds exactly when `‖F⁻‖ ≤ √2 (c + C)`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990),
  Section 1.1.
-/

public section

noncomputable section

open Module exteriorPower Metric
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-- The **Hermitian part** of the two-form `F(u, w) = ⟪F, u ∧ w⟫` represented by `F ∈ ⋀² V`, with
respect to an almost complex structure `J`: the symmetric bilinear form
`B(v, w) = (F(v, J w) + F(w, J v)) / 2` (`hermitianForm_apply`), linear in `F`. It is the
symmetric bilinear form `QuadraticMap.associated` to the quadratic form `B(v, v) = F(v, J v)`. -/
def hermitianForm (J : AlmostComplexStructure V) : ⋀[ℝ]^2 V →ₗ[ℝ] LinearMap.BilinForm ℝ V :=
  QuadraticMap.associated ∘ₗ LinearMap.BilinMap.toQuadraticMapLinearMap ℝ ℝ V ∘ₗ
    LinearMap.compRight ℝ ((innerₗ V).compl₂ J.toLinearMap) ∘ₗ
      ⟨⟨twoVectorContraction, twoVectorContraction_add⟩, twoVectorContraction_smul⟩

/-- The Hermitian part is `B(v, w) = (F(v, J w) + F(w, J v)) / 2`. -/
theorem hermitianForm_apply (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) (v w : V) :
    J.hermitianForm F v w = (⟪F, ιMulti ℝ 2 ![v, J w]⟫ + ⟪F, ιMulti ℝ 2 ![w, J v]⟫) / 2 := by
  simp [hermitianForm, QuadraticMap.associated_toQuadraticMap, inner_twoVectorContraction_apply]
  ring

/-- The quadratic form of the Hermitian part is `B(v, v) = F(v, J v)`. -/
@[simp]
theorem hermitianForm_apply_self (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) (v : V) :
    J.hermitianForm F v v = ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  rw [hermitianForm, LinearMap.comp_apply, QuadraticMap.associated_eq_self_apply]
  simp only [LinearMap.comp_apply, LinearMap.BilinMap.toQuadraticMapLinearMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compRight_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.compl₂_apply, innerₗ_apply_apply, inner_twoVectorContraction_apply]

omit [FiniteDimensional ℝ V] in
/-- The Hermitian part of a two-form is symmetric. -/
theorem isSymm_hermitianForm (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) :
    (J.hermitianForm F).IsSymm :=
  ⟨QuadraticMap.associated_isSymm ℝ _⟩

/-- **The Hermitian part of the Kähler form is the metric**: for an orthogonal `J`,
`ω(v, J w) = ⟪v, w⟫`. -/
theorem hermitianForm_kahlerForm {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) : J.hermitianForm J.kahlerForm = innerₗ V := by
  ext v w
  rw [hermitianForm_apply, inner_kahlerForm_ιMulti hJ, inner_kahlerForm_ιMulti hJ, hJ, hJ,
    innerₗ_apply_apply, real_inner_comm w v, add_self_div_two]

/-- **The contraction by a `J`-invariant two-vector commutes with `J`**: for an orthogonal `J` and
`D_J η = 0`, `(J u) ⌟ η = J (u ⌟ η)`. -/
theorem twoVectorContraction_apply_apply_of_lieMap_eq_zero {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {η : ⋀[ℝ]^2 V}
    (hη : exteriorPower.lieMap 2 J.toLinearMap η = 0) (u : V) :
    twoVectorContraction η (J u) = J (twoVectorContraction η u) := by
  have h := congrArg (⟪·, ιMulti ℝ 2 ![u, ·]⟫) hη
  refine ext_inner_right ℝ fun w ↦ ?_
  have hw := congrFun h w
  simp only [inner_zero_left, inner_lieMap_left (inner_apply_left hJ),
    exteriorPower.lieMap_two_apply_ιMulti, inner_add_right, neg_add] at hw
  rw [inner_twoVectorContraction_apply, inner_apply_left hJ, inner_twoVectorContraction_apply]
  linarith

/-- The Hermitian part of a `J`-invariant two-form: for an orthogonal `J` and `D_J η = 0`, the two
terms of `B` agree, `B(v, w) = η(v, J w)`. -/
theorem hermitianForm_apply_of_lieMap_eq_zero {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {η : ⋀[ℝ]^2 V}
    (hη : exteriorPower.lieMap 2 J.toLinearMap η = 0) (v w : V) :
    J.hermitianForm η v w = ⟪η, ιMulti ℝ 2 ![v, J w]⟫ := by
  have h : ⟪η, ιMulti ℝ 2 ![w, J v]⟫ = ⟪η, ιMulti ℝ 2 ![v, J w]⟫ := by
    rw [← inner_twoVectorContraction_apply, ← inner_twoVectorContraction_apply,
      inner_twoVectorContraction_apply_left,
      twoVectorContraction_apply_apply_of_lieMap_eq_zero hJ hη, real_inner_comm _ w,
      inner_apply_left hJ, neg_neg]
  rw [hermitianForm_apply, h, add_self_div_two]

/-- `D_J (v ∧ J w) + D_J (w ∧ J v) = 0`. -/
private theorem lieMap_ιMulti_add_lieMap_ιMulti (J : AlmostComplexStructure V) (v w : V) :
    lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![v, J w]) +
      lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![w, J v]) = 0 := by
  refine ext_inner_ιMulti_two fun a b ↦ ?_
  simp only [lieMap_two_apply_ιMulti, inner_add_left, inner_ιMulti_two, inner_zero_left,
    apply_apply, inner_neg_left]
  ring

/-- **The anti-`J`-invariant part of a two-form has zero Hermitian part**: `B(D_J ξ) = 0` for an
orthogonal `J`, because `D_J` is skew-adjoint. -/
theorem hermitianForm_lieMap {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (ξ : ⋀[ℝ]^2 V) : J.hermitianForm (lieMap 2 J.toLinearMap ξ) = 0 := by
  ext v w
  rw [hermitianForm_apply, inner_lieMap_left (inner_apply_left hJ),
    inner_lieMap_left (inner_apply_left hJ), ← neg_add, ← inner_add_right,
    lieMap_ιMulti_add_lieMap_ιMulti, inner_zero_right, neg_zero, zero_div, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-- **The Hermitian part of a form orthogonal to `ω` is bounded by `‖μ‖ / √2`** in dimension
four: if `⟪ω, μ⟫ = 0`, then `|B(v, v)| ≤ (‖μ‖ / √2) ‖v‖²`. This applies to every anti-self-dual
`μ` (`inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`), for which the bound is sharp
(`isLeast_hermitianForm_apply_self`). -/
theorem abs_hermitianForm_apply_self_le_of_inner_kahlerForm_eq_zero [Fact (finrank ℝ V = 4)]
    {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {μ : ⋀[ℝ]^2 V}
    (hμ : ⟪J.kahlerForm, μ⟫ = 0) (v : V) : |J.hermitianForm μ v v| ≤ ‖μ‖ / √2 * ‖v‖ ^ 2 := by
  rw [hermitianForm_apply_self]
  -- Pair `μ` with `y = 2 (v ∧ J v) - ‖v‖² ω`, which has the same pairing as `2 (v ∧ J v)` and
  -- norm `√2 ‖v‖²`.
  set x := ιMulti ℝ 2 ![v, J v]
  set y := (2 : ℝ) • x - ‖v‖ ^ 2 • J.kahlerForm
  have hxω : ⟪x, J.kahlerForm⟫ = ‖v‖ ^ 2 := by
    rw [real_inner_comm, inner_kahlerForm_ιMulti hJ, hJ, real_inner_self_eq_norm_sq]
  have hω : ‖J.kahlerForm‖ ^ 2 = 2 := by
    rw [norm_kahlerForm_sq hJ, (Fact.out : finrank ℝ V = 4)]
    norm_num
  have hx : ‖x‖ ^ 2 = ‖v‖ ^ 4 := norm_ιMulti_apply_sq hJ v
  have hy : ‖y‖ ^ 2 = (√2 * ‖v‖ ^ 2) ^ 2 := by
    simp only [y, norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, abs_two, abs_pow, sq_abs, mul_pow, hxω, hx, hω, Real.sq_sqrt zero_le_two]
    ring
  have hy' : ‖y‖ = √2 * ‖v‖ ^ 2 :=
    (pow_left_inj₀ (norm_nonneg y) (by positivity) two_ne_zero).1 hy
  have hμy : ⟪μ, y⟫ = 2 * ⟪μ, x⟫ := by
    have hμω : ⟪μ, J.kahlerForm⟫ = 0 := by rw [real_inner_comm]; exact hμ
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hμω]
    ring
  have hle := abs_real_inner_le_norm μ y
  rw [hμy, hy', abs_mul, abs_two] at hle
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  nlinarith [abs_nonneg ⟪μ, x⟫, norm_nonneg μ, sq_nonneg ‖v‖]

/-! ### Dimension four -/

section Four

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)
include h₀ h₂ he

/-- **The Hermitian part of a self-dual two-form is a multiple of the metric**: for `⋆η = η`,
`B(v, w) = (⟪ω, η⟫ / 2) ⟪v, w⟫`. -/
theorem hermitianForm_apply_of_hodgeStar_eq_self {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η)
    (v w : V) : J.hermitianForm η v w = ⟪J.kahlerForm, η⟫ / 2 * ⟪v, w⟫ := by
  -- Pair `η` with the identity `z + ⋆z = 2 ⟪v, w⟫ ω` for `z = v ∧ J w - J v ∧ w`.
  have h := congrArg (⟪η, ·⟫) (ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he v w)
  have hs := o.isSymmetric_hodgeStar_of_even even_two hkl η
    (ιMulti ℝ 2 ![v, J w] - ιMulti ℝ 2 ![J v, w])
  simp only [LinearEquiv.coe_coe, hη] at hs
  simp only [inner_add_right, ← hs, inner_sub_right, real_inner_smul_right] at h
  -- Antisymmetry `η(w, J v) = -η(J v, w)`, read through the skew contraction by `η`.
  rw [hermitianForm_apply, ← inner_twoVectorContraction_apply η w,
    inner_twoVectorContraction_apply_left, real_inner_comm _ w, inner_twoVectorContraction_apply,
    real_inner_comm η]
  linarith

/-- **The anti-`J`-invariant self-dual forms do not contribute to the Hermitian part**: a
self-dual `η` orthogonal to `ω` has `B = 0`. -/
theorem hermitianForm_eq_zero_of_hodgeStar_eq_self_of_inner_eq_zero {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = η) (hηω : ⟪J.kahlerForm, η⟫ = 0) : J.hermitianForm η = 0 := by
  ext v w
  rw [hermitianForm_apply_of_hodgeStar_eq_self h₀ h₂ hkl he hη, hηω, LinearMap.zero_apply,
    LinearMap.zero_apply, zero_div, zero_mul]

/-- **The contraction by an anti-self-dual two-vector commutes with `J`**: for `⋆η = -η`,
`(J u) ⌟ η = J (u ⌟ η)`. This is the `J`-invariance of anti-self-dual forms. -/
theorem twoVectorContraction_apply_apply_of_hodgeStar_eq_neg {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = -η) (u : V) :
    twoVectorContraction η (J u) = J (twoVectorContraction η u) :=
  twoVectorContraction_apply_apply_of_lieMap_eq_zero (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hη) u

/-- The Hermitian part of an anti-self-dual two-form: for `⋆η = -η`, the two terms of `B` agree,
`B(v, w) = η(v, J w)`. -/
theorem hermitianForm_apply_of_hodgeStar_eq_neg {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = -η)
    (v w : V) : J.hermitianForm η v w = ⟪η, ιMulti ℝ 2 ![v, J w]⟫ :=
  hermitianForm_apply_of_lieMap_eq_zero (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hη) v w

/-- **The Hermitian part splits into a multiple of the metric and an anti-self-dual part**:
`B(v, w) = c ⟪v, w⟫ + F⁻(v, J w)` with `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. The
anti-`J`-invariant self-dual part of `F` does not contribute. -/
theorem hermitianForm_apply_eq (F : ⋀[ℝ]^2 V) (v w : V) :
    J.hermitianForm F v w = ⟪J.kahlerForm, F⟫ / 2 * ⟪v, w⟫ +
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J w]⟫ := by
  -- `⟪ω, ⋆F⟫ = ⟪⋆ω, F⟫ = ⟪ω, F⟫`, so the self-dual part of `F` has the same `ω`-component.
  have hω : ⟪J.kahlerForm, o.hodgeStar hkl F⟫ = ⟪J.kahlerForm, F⟫ := by
    have h := o.isSymmetric_hodgeStar_of_even even_two hkl J.kahlerForm F
    simp only [LinearEquiv.coe_coe] at h
    rw [← h, hodgeStar_kahlerForm h₀ h₂ hkl he]
  have hF : F = (2⁻¹ : ℝ) • (F + o.hodgeStar hkl F) + (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F) := by
    module
  conv_lhs => rw [hF]
  rw [map_add, LinearMap.add_apply, LinearMap.add_apply,
    hermitianForm_apply_of_hodgeStar_eq_self h₀ h₂ hkl he
      (o.hodgeStar_smul_add_hodgeStar even_two hkl F),
    hermitianForm_apply_of_hodgeStar_eq_neg h₀ h₂ hkl he
      (o.hodgeStar_smul_sub_hodgeStar even_two hkl F),
    real_inner_smul_right, inner_add_right, hω]
  ring

/-- For anti-self-dual `η`, `|η(v, J v)| ≤ (‖η‖ / √2) ‖v‖²`, since `η` is orthogonal to `ω`. -/
private theorem abs_inner_ιMulti_apply_le {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = -η) (v : V) :
    |⟪η, ιMulti ℝ 2 ![v, J v]⟫| ≤ ‖η‖ / √2 * ‖v‖ ^ 2 := by
  rw [← hermitianForm_apply_self]
  exact abs_hermitianForm_apply_self_le_of_inner_kahlerForm_eq_zero
    (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hη) v

/-- For anti-self-dual `η`, the bound `η(v, J v) ≥ -(‖η‖ / √2) ‖v‖²` is attained on the unit
sphere: an eigenvector of the self-adjoint `J A`, `A u = u ⌟ η`, for its eigenvalue `‖η‖ / √2`. -/
private theorem exists_norm_eq_one_inner_ιMulti_apply_eq_neg {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = -η) :
    ∃ v : V, ‖v‖ = 1 ∧ ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = -(‖η‖ / √2) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  rcases eq_or_ne η 0 with rfl | hη₀
  · exact ⟨e 0, e.orthonormal.1 0, by simp⟩
  set A := twoVectorContraction η
  set l := ‖η‖ / √2 with hl
  have hl₀ : 0 < l := by positivity
  have hl₂ : l ^ 2 = ‖η‖ ^ 2 / 2 := by rw [hl, div_pow, Real.sq_sqrt zero_le_two]
  have hcomm (u : V) : A (J u) = J (A u) :=
    twoVectorContraction_apply_apply_of_hodgeStar_eq_neg h₀ h₂ hkl he hη u
  -- `(J A)² = l²`, since `J` and `A` commute and `A² = -l²`.
  have hsq (u : V) : J (A (J (A u))) = l ^ 2 • u := by
    have h := LinearMap.congr_fun (twoVectorContraction_comp_self o hkl (Or.inr hη)) u
    rw [LinearMap.comp_apply] at h
    rw [hcomm, J.apply_apply, h, hl₂, LinearMap.smul_apply, LinearMap.id_apply, neg_smul,
      neg_neg]
  -- `J A ≠ -l`: otherwise `A = l J`, so `η = l ω` would be self-dual, hence zero.
  obtain ⟨w, hw⟩ : ∃ w, J (A w) + l • w ≠ 0 := by
    by_contra! h
    have hA (u : V) : A u = l • J u := by
      have hu := congrArg J (h u)
      rwa [map_add, J.apply_apply, J.apply_smul, J.apply_zero, neg_add_eq_zero] at hu
    have hηω : η = l • J.kahlerForm := ext_inner_ιMulti_two fun u w ↦ by
      rw [← inner_twoVectorContraction_apply, hA, real_inner_smul_left, real_inner_smul_left,
        inner_kahlerForm_ιMulti hJ]
    have h2 := hη
    rw [hηω, map_smul, hodgeStar_kahlerForm h₀ h₂ hkl he, ← hηω, eq_neg_iff_add_eq_zero,
      ← two_smul ℝ, smul_eq_zero] at h2
    exact hη₀ (h2.resolve_left two_ne_zero)
  set v := J (A w) + l • w
  have hv : J (A v) = l • v := by
    simp only [v, map_add, map_smul, J.apply_add, J.apply_smul, hsq, smul_add, smul_smul, sq]
    abel
  -- Hence `η(v, J v) = ⟪A v, J v⟫ = -⟪J A v, v⟫ = -l ‖v‖²`; normalize `v`.
  have key : ⟪A v, J v⟫ = -(l * ‖v‖ ^ 2) := by
    rw [← neg_neg ⟪A v, J v⟫, ← inner_apply_left hJ, hv, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  have hv₀ : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hw
  refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv₀], ?_⟩
  rw [← inner_twoVectorContraction_apply, map_smul, J.apply_smul, real_inner_smul_left,
    real_inner_smul_right, key]
  field_simp

/-- **The Hermitian part deviates from `c g` by at most `‖F⁻‖ / √2`**: with `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2`, `|B(v, v) - c ‖v‖²| ≤ (‖F⁻‖ / √2) ‖v‖²`. -/
theorem abs_hermitianForm_apply_self_sub_le (F : ⋀[ℝ]^2 V) (v : V) :
    |J.hermitianForm F v v - ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2| ≤
      ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2 * ‖v‖ ^ 2 := by
  rw [hermitianForm_apply_eq h₀ h₂ hkl he, real_inner_self_eq_norm_sq, add_sub_cancel_left]
  exact abs_inner_ιMulti_apply_le h₀ h₂ hkl he (o.hodgeStar_smul_sub_hodgeStar even_two hkl F) v

/-- **The smallest eigenvalue of the Hermitian part**: on the unit sphere, the minimum of
`B(v, v)` is `c - ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem isLeast_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) :
    IsLeast ((fun v ↦ J.hermitianForm F v v) '' sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_norm_eq_one_inner_ιMulti_apply_eq_neg h₀ h₂ hkl he
      (o.hodgeStar_smul_sub_hodgeStar even_two hkl F)
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    dsimp only
    rw [hermitianForm_apply_eq h₀ h₂ hkl he, real_inner_self_eq_norm_sq, hv, hv']
    ring
  · rintro _ ⟨v, hv, rfl⟩
    have h := abs_hermitianForm_apply_self_sub_le h₀ h₂ hkl he F v
    rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, mul_one] at h
    linarith [(abs_le.1 h).1]

/-- **The largest eigenvalue of the Hermitian part**: on the unit sphere, the maximum of
`B(v, v)` is `c + ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem isGreatest_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) :
    IsGreatest ((fun v ↦ J.hermitianForm F v v) '' sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · have hneg : o.hodgeStar hkl (-((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))) =
        -(-((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))) := by
      rw [map_neg, o.hodgeStar_smul_sub_hodgeStar even_two hkl F]
    obtain ⟨v, hv, hv'⟩ := exists_norm_eq_one_inner_ιMulti_apply_eq_neg h₀ h₂ hkl he hneg
    rw [inner_neg_left, norm_neg, neg_inj] at hv'
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    dsimp only
    rw [hermitianForm_apply_eq h₀ h₂ hkl he, real_inner_self_eq_norm_sq, hv, hv']
    ring
  · rintro _ ⟨v, hv, rfl⟩
    have h := abs_hermitianForm_apply_self_sub_le h₀ h₂ hkl he F v
    rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, mul_one] at h
    linarith [(abs_le.1 h).2]

/-- **A lower bound on the Hermitian part bounds the anti-self-dual part**: if `B ≥ -C g`, then
`‖F⁻‖ ≤ √2 (c + C)`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) {C : ℝ}
    (hC : ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤ √2 * (⟪J.kahlerForm, F⟫ / 2 + C) := by
  obtain ⟨v, hv, hBv⟩ := (isLeast_hermitianForm_apply_self h₀ h₂ hkl he F).1
  dsimp only at hBv
  have h := hC v
  rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, hBv] at h
  rw [mul_comm, ← div_le_iff₀ (by positivity)]
  linarith

/-- **Lower bounds on the Hermitian part are bounds on the anti-self-dual part**: `B ≥ -C g`
holds exactly when `‖F⁻‖ ≤ √2 (c + C)`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem forall_le_hermitianForm_apply_self_iff (F : ⋀[ℝ]^2 V) {C : ℝ} :
    (∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) ↔
      ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤ √2 * (⟪J.kahlerForm, F⟫ / 2 + C) := by
  refine ⟨norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self h₀ h₂ hkl he F,
    fun hC v ↦ ?_⟩
  have h := abs_hermitianForm_apply_self_sub_le h₀ h₂ hkl he F v
  have hle : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2 ≤ ⟪J.kahlerForm, F⟫ / 2 + C := by
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact hC
  have hv := sq_nonneg ‖v‖
  nlinarith [neg_abs_le (J.hermitianForm F v v - ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2)]

end Four

end TauCeti.AlmostComplexStructure
