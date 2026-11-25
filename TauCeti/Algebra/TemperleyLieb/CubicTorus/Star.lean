/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Algebra.Group.Fin.Tuple

/-!
# The adjoint on the cubic quantum torus

The cubic quantum torus `G_N = CubicTorus N` of `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`
has basis `W(a)`, `a : Fin N → ZMod 3`, with `W(a) W(b) = α(a, b) W(a + b)` for the factor set
`α(a, b) = ω ^ (2 B(a, b))`, where `B` is the alternating chain form and `ω = exp (2 π i / 3)`.
This file equips `G_N` with its *adjoint*, the conjugate-linear map
`(Σ z_a W(a))⋆ = Σ conj(z_a) W(-a)`. It is the adjoint of a twisted group algebra from
`TauCeti.Algebra.MonoidAlgebra.Twisted.Star`, which applies because
`conj (α(a, b)) = ω ^ (-2 B(a, b)) = α(-b, -a)`, so `G_N` is a star algebra in which every `W(a)`,
in particular every site unitary `U_j`, is unitary, and every `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)` is a
self-adjoint idempotent. The inversion `θ_N : W(a) ↦ W(-a)` commutes with the adjoint, so the
inversion-fixed subalgebra `C_N` is closed under it and is a star subalgebra
(`cubicFixedStarSubalgebra`), and so does the inclusion `I_N : W(a) ↦ W(a, 0)` of `G_N` in
`G_(N+1)`.

The scalar coefficient `s_N`, the coefficient of `W(0) = 1`, is compatible with the adjoint.
Since `α(-a, a) = 1`, it satisfies the Parseval identity `s_N(x⋆ x) = Σ_a conj(x_a) x_a`. Hence
`s_N` is a positive functional with trivial null space (`cubicStarPositiveFunctional`,
`nullSubmodule_cubicStarPositiveFunctional`): a faithful normalized positive trace on `G_N`. This
is what identifies the kernel of the comparison map from the Temperley–Lieb algebra at `δ = √3`
with the trace radical, in `TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.instIsStarFactorSetCubicFactor`: the factor set of `G_N` is compatible
  with conjugation, so `G_N` carries the conjugate-linear adjoint.
* `TauCeti.TemperleyLieb.cubicFixedStarSubalgebra`: the inversion-fixed subalgebra `C_N` as a
  star subalgebra.
* `TauCeti.TemperleyLieb.cubicStarPositiveFunctional`: the scalar coefficient as a positive
  functional.

## Main results

* `TauCeti.TemperleyLieb.star_weyl`: the adjoint on the basis.
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

private theorem star_cubicFactor (g h : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N g h : ℂ) = cubicFactor N h⁻¹ g⁻¹ := by
  simp [cubicFactor_apply, chainForm_swap g.toAdd h.toAdd]

/-- Conjugating the factor set reverses and inverts its arguments:
`conj (α(g, h)) = α(h⁻¹, g⁻¹)`. So the cubic quantum torus carries the adjoint
`(Σ z_a W(a))⋆ = Σ conj(z_a) W(-a)` of `TauCeti.Algebra.MonoidAlgebra.Twisted.Star`. -/
instance instIsStarFactorSetCubicFactor : IsStarFactorSet (cubicFactor N) where
  star_apply := star_cubicFactor

/-- The adjoint on the basis: `W(a)⋆ = W(-a)`. -/
@[simp]
theorem star_weyl (a : Fin N → ZMod 3) : star (weyl N a) = weyl N (-a) := by
  rw [weyl_def, star_of, weyl_def, ofAdd_neg]

/-- Every basis element `W(a)` is unitary. -/
theorem weyl_mem_unitary (a : Fin N → ZMod 3) : weyl N a ∈ unitary (CubicTorus N) := by
  rw [weyl_def]
  exact of_mem_unitary (cubicFactor_inv_self _)

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
@[simp]
theorem cubicInversion_star (x : CubicTorus N) :
    cubicInversion N (star x) = star (cubicInversion N x) :=
  map_star_of_map_of_inv (cubicInversion N).toLinearMap
    (fun g ↦ by simp [of_eq_weyl, cubicInversion_weyl]) x

/-- The inversion-fixed subalgebra `C_N` is closed under the adjoint. -/
theorem star_mem_cubicFixed {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    star x ∈ cubicFixed N := by
  rw [mem_cubicFixed] at hx ⊢
  rw [cubicInversion_star, hx]

variable (N) in
/-- The inversion-fixed subalgebra `C_N`, as a star subalgebra of the cubic quantum torus. -/
noncomputable def cubicFixedStarSubalgebra : StarSubalgebra ℂ (CubicTorus N) where
  toSubalgebra := cubicFixed N
  star_mem' := star_mem_cubicFixed

@[simp]
theorem toSubalgebra_cubicFixedStarSubalgebra :
    (cubicFixedStarSubalgebra N).toSubalgebra = cubicFixed N :=
  (rfl)

@[simp]
theorem mem_cubicFixedStarSubalgebra {x : CubicTorus N} :
    x ∈ cubicFixedStarSubalgebra N ↔ x ∈ cubicFixed N :=
  Iff.rfl

/-- The inclusion `I_N : W(a) ↦ W(a, 0)` of cubic quantum tori commutes with the adjoints. -/
@[simp]
theorem cubicIncl_star (x : CubicTorus N) : cubicIncl N (star x) = star (cubicIncl N x) :=
  map_star_of_map_of_inv (cubicIncl N).toLinearMap
    (fun g ↦ by simp [of_eq_weyl, cubicIncl_weyl, Fin.neg_snoc]) x

end Adjoint

/-! ### The scalar coefficient is a faithful positive trace -/

section ScalarCoefficient

/-- The scalar coefficient commutes with the adjoint: `s_N(x⋆) = conj (s_N(x))`. -/
@[simp]
theorem cubicScalarCoefficient_star (x : CubicTorus N) :
    cubicScalarCoefficient N (star x) = star (cubicScalarCoefficient N x) :=
  map_star_of_map_of_inv (cubicScalarCoefficient N) (fun g ↦ by
    simp only [of_eq_weyl, toAdd_inv, cubicScalarCoefficient_weyl, neg_eq_zero]
    split_ifs <;> simp) x

/-- **The Parseval identity**: `s_N(x⋆ x)` is the sum of the squared moduli `conj(x_g) x_g` of the
coefficients of `x`. -/
theorem cubicScalarCoefficient_star_mul_self (x : CubicTorus N) :
    cubicScalarCoefficient N (star x * x) =
      ∑ g, star ((basis ℂ _ (cubicFactor N)).repr x g) * (basis ℂ _ (cubicFactor N)).repr x g := by
  rw [cubicScalarCoefficient_eq_repr_one, repr_star_mul_self_apply_one cubicFactor_inv_self,
    Finsupp.sum_fintype _ _ (by simp)]

/-- The scalar coefficient is nonnegative on squares. -/
theorem cubicScalarCoefficient_star_mul_self_nonneg (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (star x * x) := by
  rw [cubicScalarCoefficient_eq_repr_one]
  exact repr_star_mul_self_apply_one_nonneg cubicFactor_inv_self x

/-- **The scalar coefficient is faithful**: `s_N(x⋆ x) = 0` only for `x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_star_mul_self_eq_zero_iff (x : CubicTorus N) :
    cubicScalarCoefficient N (star x * x) = 0 ↔ x = 0 := by
  rw [cubicScalarCoefficient_eq_repr_one]
  exact repr_star_mul_self_apply_one_eq_zero_iff cubicFactor_inv_self x

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
