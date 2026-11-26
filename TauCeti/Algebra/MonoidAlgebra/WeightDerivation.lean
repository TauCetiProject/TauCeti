/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Finsupp.Pointwise

/-!
# The derivation of a monoid algebra attached to an additive weight

Let `R` be a commutative semiring and `G` an additive commutative monoid. An additive map
`w : G →+ R` assigns a weight to each monomial of `R[G]`, and multiplying every monomial by its
weight, `single g r ↦ single g (w g * r)`, is a derivation of `R[G]`
(`AddMonoidAlgebra.weightDerivation`): the Leibniz rule on two monomials is the additivity
`w (g + h) = w g + w h`. All these derivations are diagonal in the monomial basis, so any two of
them commute (`AddMonoidAlgebra.commute_weightDerivation`). This is the monoid-algebra
counterpart of `HahnSeries.weightDerivation` for Hahn series.

For the Laurent polynomial ring `R[x₁^{±1}, …, x_n^{±1}] = R[ℤⁿ]` and the `i`-th coordinate
`m ↦ m i`, the weight derivation is the Euler derivation `x_i ∂/∂x_i` of the torus; for
`G = ℕ` and the cast `ℕ →+ R` it is the Euler operator `x d/dx` of the polynomial ring.

## Main definitions

* `AddMonoidAlgebra.weightDerivation w`: the derivation `single g r ↦ single g (w g * r)`.

## Main results

* `AddMonoidAlgebra.weightDerivation_single` and `AddMonoidAlgebra.coeff_weightDerivation`: the
  weight derivation multiplies the coefficient of `g` by `w g`.
* `AddMonoidAlgebra.commute_weightDerivation`: two weight derivations commute as linear
  endomorphisms.
-/

public section

namespace AddMonoidAlgebra

variable {R G : Type*} [CommSemiring R] [AddCommMonoid G]

/-- The linear endomorphism of `R[G]` multiplying the coefficient of `g` by the weight `w g`. -/
private noncomputable def weightLinearMap (w : G →+ R) : R[G] →ₗ[R] R[G] where
  toFun f := ofCoeff ((⇑w : G → R) • f.coeff)
  map_add' f f' := by ext; simp
  map_smul' r f := by ext; simp [mul_left_comm]

private theorem coeff_weightLinearMap (w : G →+ R) (f : R[G]) (g : G) :
    (weightLinearMap w f).coeff g = w g * f.coeff g :=
  (rfl)

private theorem weightLinearMap_single (w : G →+ R) (g : G) (r : R) :
    weightLinearMap w (single g r) = single g (w g * r) := by
  classical
  ext h
  simp only [coeff_weightLinearMap, coeff_single, Finsupp.single_apply]
  split_ifs with hgh
  · rw [hgh]
  · rw [mul_zero]

private theorem weightLinearMap_mul (w : G →+ R) (a b : R[G]) :
    weightLinearMap w (a * b) = a • weightLinearMap w b + b • weightLinearMap w a := by
  induction a using induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_smul, smul_add]; abel
  | single g r =>
    induction b using induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', smul_add, add_smul]; abel
    | single h s =>
      simp only [single_mul_single, weightLinearMap_single, smul_eq_mul, map_add]
      rw [add_comm h g, ← single_add]
      congr 1
      ring

/-- The **weight derivation** of `R[G]` attached to an additive weight `w : G →+ R`: it
multiplies each monomial `single g r` by its weight `w g`. For the Laurent polynomial ring and a
coordinate weight it is an Euler derivation `x_i ∂/∂x_i`. -/
noncomputable def weightDerivation (w : G →+ R) : Derivation R R[G] R[G] :=
  { weightLinearMap w with
    map_one_eq_zero' := by
      rw [one_def, weightLinearMap_single, map_zero, zero_mul, single_zero]
    leibniz' := weightLinearMap_mul w }

/-- The coefficient of `g` in `weightDerivation w f` is `w g` times that of `f`. -/
@[simp]
theorem coeff_weightDerivation (w : G →+ R) (f : R[G]) (g : G) :
    (weightDerivation w f).coeff g = w g * f.coeff g :=
  coeff_weightLinearMap w f g

/-- The weight derivation sends the monomial `single g r` to `single g (w g * r)`. -/
@[simp]
theorem weightDerivation_single (w : G →+ R) (g : G) (r : R) :
    weightDerivation w (single g r) = single g (w g * r) :=
  weightLinearMap_single w g r

/-- Any two weight derivations commute, since both are diagonal in the monomial basis. -/
theorem commute_weightDerivation (w v : G →+ R) :
    Commute (weightDerivation w : Module.End R R[G]) (weightDerivation v : Module.End R R[G]) := by
  refine LinearMap.ext fun f ↦ ?_
  ext g
  simp only [mul_apply_eq_comp, Derivation.coeFn_coe, coeff_weightDerivation]
  ring

end AddMonoidAlgebra
