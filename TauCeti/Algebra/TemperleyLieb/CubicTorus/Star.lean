/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# The adjoint on the cubic quantum torus

The cubic quantum torus `G_N = CubicTorus N` of `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`
has basis `W(a)`, `a : Fin N → ZMod 3`, with `W(a) W(b) = α(a, b) W(a + b)` for the factor set
`α(a, b) = ω ^ (2 B(a, b))`, where `B` is the alternating chain form and `ω = exp (2 π i / 3)`.
This file equips `G_N` with its *adjoint*, the conjugate-linear map
`(Σ z_a W(a))⋆ = Σ conj(z_a) W(-a)`. It is an anti-multiplicative involution because
`conj (α(a, b)) = ω ^ (-2 B(a, b)) = α(-b, -a)`, so `G_N` is a star algebra in which every `W(a)`,
in particular every site unitary `U_j`, is unitary, and every `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)` is a
self-adjoint idempotent. The inversion `θ_N : W(a) ↦ W(-a)` commutes with the adjoint, so the
inversion-fixed subalgebra `C_N` is closed under it, and so does the inclusion
`I_N : W(a) ↦ W(a, 0)` of `G_N` in `G_(N+1)`.

The scalar coefficient `s_N`, the coefficient of `W(0) = 1`, is compatible with the adjoint and
satisfies the Parseval identity `s_N(x⋆ x) = Σ_a conj(x_a) x_a`. Hence `s_N` is a positive
functional with trivial null space (`cubicStarPositiveFunctional`,
`nullSubmodule_cubicStarPositiveFunctional`): a faithful normalized positive trace on `G_N`. This
is what identifies the kernel of the comparison map from the Temperley–Lieb algebra at `δ = √3`
with the trace radical, in `TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.instStarRingCubicTorus` and
  `TauCeti.TemperleyLieb.instStarModuleCubicTorus`: the conjugate-linear adjoint on `G_N`.
* `TauCeti.TemperleyLieb.cubicStarPositiveFunctional`: the scalar coefficient as a positive
  functional.

## Main results

* `TauCeti.TemperleyLieb.star_weyl` and `TauCeti.TemperleyLieb.repr_star`: the adjoint on the basis
  and on coefficients.
* `TauCeti.TemperleyLieb.weyl_mem_unitary`, `TauCeti.TemperleyLieb.star_cubicSite` and
  `TauCeti.TemperleyLieb.isStarProjection_cubicProjection`: the basis elements are unitary,
  `U_j⋆ = U_j ^ 2`, and the `p_j` are projections.
* `TauCeti.TemperleyLieb.cubicInversion_star`, `TauCeti.TemperleyLieb.star_mem_cubicFixed` and
  `TauCeti.TemperleyLieb.cubicIncl_star`: the inversion and the inclusions commute with the
  adjoint, and `C_N` is star-closed.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul_self` and
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul_self_eq_zero_iff`: the Parseval identity
  and faithfulness of the scalar coefficient.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), §4.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra

variable {N : ℕ}

/-! ### The adjoint -/

section Adjoint

variable (N) in
/-- The conjugate-linear map `Σ z_g W(g) ↦ Σ conj(z_g) W(g⁻¹)` underlying the adjoint. -/
private noncomputable def cubicStarₗ : CubicTorus N →ₗ⋆[ℂ] CubicTorus N where
  toFun x := ∑ g, star ((basis ℂ _ (cubicFactor N)).repr x g) • of g⁻¹
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply, star_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, star_mul', mul_smul, Finset.smul_sum,
      starRingEnd_apply]

private theorem cubicStarₗ_of (g : Multiplicative (Fin N → ZMod 3)) :
    cubicStarₗ N (of g) = of g⁻¹ := by
  classical
  simp only [cubicStarₗ, LinearMap.coe_mk, AddHom.coe_mk, repr_of]
  rw [Finset.sum_eq_single g (fun h _ hh ↦ by simp [Ne.symm hh])
    (by simp)]
  simp

/-- Conjugating the factor set reverses and inverts its arguments:
`conj (α(g, h)) = α(h⁻¹, g⁻¹)`. -/
private theorem star_cubicFactor (g h : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N g h : ℂ) = cubicFactor N h⁻¹ g⁻¹ := by
  rw [cubicFactor_apply, cubicFactor_apply, coe_cubeRootPow, coe_cubeRootPow, toAdd_inv,
    toAdd_inv, LinearMap.map_neg₂, map_neg, neg_neg, chainForm_swap, mul_neg,
    AddChar.map_neg_eq_conj, starRingEnd_apply, star_star]

private theorem cubicStarₗ_mul (x y : CubicTorus N) :
    cubicStarₗ N (x * y) = cubicStarₗ N y * cubicStarₗ N x := by
  -- Both sides are conjugate-linear in each argument, so compare them on basis elements.
  have hof (g : Multiplicative (Fin N → ZMod 3)) :
      (cubicStarₗ N).comp (LinearMap.mulLeft ℂ (of g)) =
        (LinearMap.mulRight ℂ (of g⁻¹)).comp (cubicStarₗ N) :=
    (basis ℂ _ (cubicFactor N)).ext fun h ↦ by
      simp [cubicStarₗ_of, starRingEnd_apply, star_cubicFactor]
  have key : (cubicStarₗ N).comp (LinearMap.mulRight ℂ y) =
      (LinearMap.mulLeft ℂ (cubicStarₗ N y)).comp (cubicStarₗ N) :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      simpa [cubicStarₗ_of] using LinearMap.congr_fun (hof g) y
  simpa using LinearMap.congr_fun key x

private theorem cubicStarₗ_cubicStarₗ (x : CubicTorus N) :
    cubicStarₗ N (cubicStarₗ N x) = x := by
  have key : (cubicStarₗ N).comp (cubicStarₗ N) = LinearMap.id :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by simp [cubicStarₗ_of]
  exact LinearMap.congr_fun key x

/-- The **adjoint** on the cubic quantum torus: the conjugate-linear, product-reversing involution
`(Σ z_a W(a))⋆ = Σ conj(z_a) W(-a)`. -/
@[no_expose]
noncomputable instance instStarRingCubicTorus : StarRing (CubicTorus N) where
  star := cubicStarₗ N
  star_involutive := cubicStarₗ_cubicStarₗ
  star_mul := cubicStarₗ_mul
  star_add := map_add (cubicStarₗ N)

private theorem star_eq_cubicStarₗ (x : CubicTorus N) : star x = cubicStarₗ N x :=
  (rfl)

/-- The adjoint on the cubic quantum torus is conjugate-linear. -/
instance instStarModuleCubicTorus : StarModule ℂ (CubicTorus N) where
  star_smul c x := by
    simpa only [star_eq_cubicStarₗ, starRingEnd_apply] using map_smulₛₗ (cubicStarₗ N) c x

/-- The adjoint on the basis: `W(a)⋆ = W(-a)`. -/
@[simp]
theorem star_weyl (a : Fin N → ZMod 3) : star (weyl N a) = weyl N (-a) := by
  rw [star_eq_cubicStarₗ, weyl_def, cubicStarₗ_of, weyl_def, ofAdd_neg]

/-- The coefficients of the adjoint: the coefficient of `x⋆` at `g` is the conjugate of the
coefficient of `x` at `g⁻¹`. -/
@[simp]
theorem repr_star (x : CubicTorus N) (g : Multiplicative (Fin N → ZMod 3)) :
    (basis ℂ _ (cubicFactor N)).repr (star x) g =
      star ((basis ℂ _ (cubicFactor N)).repr x g⁻¹) := by
  have key : (LinearMap.proj g ∘ₗ (basis ℂ _ (cubicFactor N)).equivFun.toLinearMap).comp
      (cubicStarₗ N) =
        ((starLinearEquiv ℂ (A := ℂ)).toLinearMap.comp (LinearMap.proj g⁻¹ ∘ₗ
          (basis ℂ _ (cubicFactor N)).equivFun.toLinearMap)) :=
    (basis ℂ _ (cubicFactor N)).ext fun h ↦ by
      classical
      simp [cubicStarₗ_of, Finsupp.single_apply, inv_eq_iff_eq_inv]
  simpa [star_eq_cubicStarₗ] using LinearMap.congr_fun key x

/-- Every basis element `W(a)` is unitary. -/
theorem weyl_mem_unitary (a : Fin N → ZMod 3) : weyl N a ∈ unitary (CubicTorus N) := by
  rw [Unitary.mem_iff, star_weyl]
  constructor <;> simp

/-- The adjoint of a site unitary is its inverse `U_j ^ 2`. -/
@[simp]
theorem star_cubicSite (j : Fin N) : star (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [← cubicInversion_cubicSite, cubicSite_def, star_weyl, cubicInversion_weyl]

/-- Every site unitary `U_j` is unitary. -/
theorem cubicSite_mem_unitary (j : Fin N) : cubicSite N j ∈ unitary (CubicTorus N) := by
  rw [cubicSite_def]
  exact weyl_mem_unitary _

/-- The cubic projections are self-adjoint. -/
@[simp]
theorem star_cubicProjection (j : Fin N) : star (cubicProjection N j) = cubicProjection N j := by
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by
    rw [pow_succ, cubicSite_pow_three, one_mul]
  simp [cubicProjection_def, star_pow, ← pow_mul, h4, add_right_comm]

/-- The cubic projections are projections: self-adjoint idempotents. -/
theorem isStarProjection_cubicProjection (j : Fin N) : IsStarProjection (cubicProjection N j) :=
  ⟨cubicProjection_mul_self j, star_cubicProjection j⟩

/-- The inversion commutes with the adjoint. -/
theorem cubicInversion_star (x : CubicTorus N) :
    cubicInversion N (star x) = star (cubicInversion N x) := by
  have key : (cubicInversion N).toLinearMap.comp (cubicStarₗ N) =
      (cubicStarₗ N).comp (cubicInversion N).toLinearMap :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      simp only [LinearMap.comp_apply, basis_apply, AlgHom.toLinearMap_apply, of_eq_weyl,
        ← star_eq_cubicStarₗ, star_weyl, cubicInversion_weyl]
  simpa only [star_eq_cubicStarₗ, LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
    LinearMap.congr_fun key x

/-- The inversion-fixed subalgebra `C_N` is closed under the adjoint. -/
theorem star_mem_cubicFixed {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    star x ∈ cubicFixed N := by
  rw [mem_cubicFixed] at hx ⊢
  rw [cubicInversion_star, hx]

/-- The inclusion `I_N : W(a) ↦ W(a, 0)` of cubic quantum tori commutes with the adjoints. -/
theorem cubicIncl_star (x : CubicTorus N) : cubicIncl N (star x) = star (cubicIncl N x) := by
  have key : (cubicIncl N).toLinearMap.comp (cubicStarₗ N) =
      (cubicStarₗ (N + 1)).comp (cubicIncl N).toLinearMap :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      simp only [LinearMap.comp_apply, basis_apply, AlgHom.toLinearMap_apply, of_eq_weyl,
        ← star_eq_cubicStarₗ]
      rw [star_weyl, ← cubicInversion_weyl, ← cubicInversion_cubicIncl, cubicIncl_weyl,
        cubicInversion_weyl, star_weyl]
  simpa only [star_eq_cubicStarₗ, LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
    LinearMap.congr_fun key x

end Adjoint

/-! ### The scalar coefficient is a faithful positive trace -/

section ScalarCoefficient

/-- The scalar coefficient commutes with the adjoint: `s_N(x⋆) = conj (s_N(x))`. -/
@[simp]
theorem cubicScalarCoefficient_star (x : CubicTorus N) :
    cubicScalarCoefficient N (star x) = star (cubicScalarCoefficient N x) := by
  have key : (cubicScalarCoefficient N).comp (cubicStarₗ N) =
      (starLinearEquiv ℂ (A := ℂ)).toLinearMap.comp (cubicScalarCoefficient N) :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      simp only [LinearMap.comp_apply, basis_apply, of_eq_weyl, ← star_eq_cubicStarₗ, star_weyl,
        cubicScalarCoefficient_weyl, neg_eq_zero, LinearEquiv.coe_coe, starLinearEquiv_apply]
      split_ifs <;> simp
  simpa only [star_eq_cubicStarₗ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    starLinearEquiv_apply] using LinearMap.congr_fun key x

/-- **The Parseval identity**: `s_N(x⋆ x)` is the sum of the squared moduli `conj(x_g) x_g` of the
coefficients of `x`. -/
theorem cubicScalarCoefficient_star_mul_self (x : CubicTorus N) :
    cubicScalarCoefficient N (star x * x) =
      ∑ g, star ((basis ℂ _ (cubicFactor N)).repr x g) * (basis ℂ _ (cubicFactor N)).repr x g := by
  classical
  conv_lhs => rw [← (basis ℂ _ (cubicFactor N)).sum_repr x]
  simp only [star_sum, star_smul, basis_apply, of_eq_weyl, star_weyl, Finset.sum_mul_sum,
    smul_mul_smul_comm, map_sum, map_smul, cubicScalarCoefficient_weyl_mul_weyl, smul_eq_mul,
    neg_add_eq_zero, mul_ite, mul_one, mul_zero, EmbeddingLike.apply_eq_iff_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The scalar coefficient is nonnegative on squares. -/
theorem cubicScalarCoefficient_star_mul_self_nonneg (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (star x * x) := by
  rw [cubicScalarCoefficient_star_mul_self]
  exact Finset.sum_nonneg fun g _ ↦ star_mul_self_nonneg _

/-- **The scalar coefficient is faithful**: `s_N(x⋆ x) = 0` only for `x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_star_mul_self_eq_zero_iff (x : CubicTorus N) :
    cubicScalarCoefficient N (star x * x) = 0 ↔ x = 0 := by
  rw [cubicScalarCoefficient_star_mul_self,
    Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ star_mul_self_nonneg _,
    ← (basis ℂ _ (cubicFactor N)).forall_coord_eq_zero_iff]
  simp [mul_eq_zero]

variable (N) in
/-- The scalar coefficient `s_N` of the cubic quantum torus, as a positive functional. -/
noncomputable def cubicStarPositiveFunctional : StarPositiveFunctional (CubicTorus N) where
  toLinearMap := cubicScalarCoefficient N
  square_nonneg := cubicScalarCoefficient_star_mul_self_nonneg

@[simp]
theorem toLinearMap_cubicStarPositiveFunctional :
    (cubicStarPositiveFunctional N).toLinearMap = cubicScalarCoefficient N :=
  (rfl)

@[simp]
theorem cubicStarPositiveFunctional_apply (x : CubicTorus N) :
    cubicStarPositiveFunctional N x = cubicScalarCoefficient N x :=
  (rfl)

/-- The positive functional `s_N` has trivial null space. -/
theorem nullSubmodule_cubicStarPositiveFunctional :
    (cubicStarPositiveFunctional N).nullSubmodule = ⊥ := by
  ext x
  simp

end ScalarCoefficient

end TauCeti.TemperleyLieb
