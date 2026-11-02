/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
public import TauCeti.NumberTheory.QuadraticOrder.Embedding
import TauCeti.Algebra.QuadraticAlgebra.Discriminant

/-!
# The squarefree radicand of a quadratic field

A quadratic number field `K` has a presentation `K = ℚ(θ)` with `θ² = d` for a squarefree integer
`d` (`NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top`). This file shows that the
radicand `d` is an isomorphism invariant: it classifies quadratic fields up to `ℚ`-algebra
isomorphism, and the rational quadratic algebra `QuadraticAlgebra ℚ d 0` is the corresponding
model. For an imaginary quadratic field the radicand is negative
(`NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top_of_isTotallyComplex`), so imaginary
quadratic fields up to isomorphism are in bijection with the negative squarefree integers, and
statements about imaginary quadratic fields up to isomorphism may be read off their radicands.

The comparison of models reuses the classification of the models themselves,
`QuadraticAlgebra.nonempty_algEquiv_iff_of_squarefree`: for squarefree integers `d` and `e`,
`ℚ(√d) ≃ₐ[ℚ] ℚ(√e)` exactly when `d = e`. A presented field is identified with its model by
`TauCeti.QuadraticOrder.algEquivOfSqrt`, evaluation at the chosen square root.

## Main results

* `NumberField.nonempty_algEquiv_quadraticAlgebra`: a quadratic field presented by a square root
  of `d` is isomorphic to `QuadraticAlgebra ℚ d 0`.
* `NumberField.nonempty_algEquiv_iff_of_squarefree`: two quadratic fields presented by squarefree
  radicands `d` and `e` are isomorphic exactly when `d = e`.
* `NumberField.eq_of_sq_eq_intCast_of_squarefree`: the squarefree radicand is the only
  squarefree integer other than `1` with a square root in `K`.
* `NumberField.existsUnique_squarefree_algEquiv`: every quadratic field is isomorphic to
  `QuadraticAlgebra ℚ d 0` for exactly one squarefree integer `d`.
* `NumberField.existsUnique_neg_squarefree_algEquiv`: every imaginary quadratic field is
  isomorphic to `QuadraticAlgebra ℚ d 0` for exactly one negative squarefree integer `d`.
-/

public section

open Polynomial NumberField Module

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] {d e : ℤ}

/-- **A presented quadratic field is isomorphic to its model.** If `[K : ℚ] = 2` and `θ ∈ 𝓞 K` has
minimal polynomial `X² - d`, then `K ≃ₐ[ℚ] QuadraticAlgebra ℚ d 0`. The isomorphism is the
inverse of evaluation at `θ`, `TauCeti.QuadraticOrder.algEquivOfSqrt`; no generation hypothesis is
needed, since an irrational element of a quadratic field generates it. -/
theorem nonempty_algEquiv_quadraticAlgebra (hK : finrank ℚ K = 2) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) : Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  have : Fact (¬ IsSquare d) := ⟨Rat.isSquare_intCast_iff.not.mp (not_isSquare_radicand hmin)⟩
  have hθ : (θ : K) ^ 2 = (d : K) := by rw [coe_gen_sq hmin, eq_intCast]
  exact ⟨(TauCeti.QuadraticOrder.algEquivOfSqrt d (θ : K) hθ hK).symm⟩

/-- **The squarefree radicand is an isomorphism invariant.** Two quadratic fields presented by
square roots of squarefree integers `d` and `e` are `ℚ`-isomorphic exactly when `d = e`. Taking
`L = K` and the identity shows that the squarefree radicand of a quadratic field does not depend on
the presentation. -/
theorem nonempty_algEquiv_iff_of_squarefree (hK : finrank ℚ K = 2) (hL : finrank ℚ L = 2)
    {θ : 𝓞 K} {η : 𝓞 L} (hθ : minpoly ℤ θ = X ^ 2 - C d) (hη : minpoly ℤ η = X ^ 2 - C e)
    (hd : Squarefree d) (he : Squarefree e) : Nonempty (K ≃ₐ[ℚ] L) ↔ d = e := by
  obtain ⟨φ⟩ := nonempty_algEquiv_quadraticAlgebra hK hθ
  obtain ⟨ψ⟩ := nonempty_algEquiv_quadraticAlgebra hL hη
  rw [← QuadraticAlgebra.nonempty_algEquiv_iff_of_squarefree hd he]
  exact ⟨fun ⟨σ⟩ => ⟨(φ.symm.trans σ).trans ψ⟩, fun ⟨τ⟩ => ⟨(φ.trans τ).trans ψ.symm⟩⟩

/-- **The radicand is the only squarefree square class in `K`.** If `K` is presented by a square
root of the squarefree integer `d`, and `z ∈ K` squares to a squarefree integer `n ≠ 1`, then
`n = d`. Such a `z` is irrational, so it presents `K` with radicand `n`, and the radicand does not
depend on the presentation. -/
theorem eq_of_sq_eq_intCast_of_squarefree (hK : finrank ℚ K = 2) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : Squarefree d) {z : K} {n : ℤ}
    (hz : z ^ 2 = (n : K)) (hn : Squarefree n) (hn1 : n ≠ 1) : n = d := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  -- A rational square root would make `n` a square, hence `1` since it is squarefree.
  have hzQ : z ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, rfl⟩
    have hq : (n : ℚ) = q * q := by
      rw [← sq]
      exact_mod_cast ((algebraMap ℚ K).injective (by simpa using hz)).symm
    obtain ⟨m, rfl⟩ := Rat.isSquare_intCast_iff.1 ⟨q, hq⟩
    rcases Int.isUnit_iff.1 (hn m dvd_rfl) with rfl | rfl <;> exact hn1 rfl
  obtain ⟨η, hη, -⟩ := exists_gen_of_sq_eq_intCast hz hzQ
  exact (nonempty_algEquiv_iff_of_squarefree hK hK hη hmin hn hd).1 ⟨AlgEquiv.refl⟩

/-- **The squarefree model of a quadratic field.** Every number field of degree `2` over `ℚ` is
isomorphic to `QuadraticAlgebra ℚ d 0` for exactly one squarefree integer `d`. -/
theorem existsUnique_squarefree_algEquiv (hK : finrank ℚ K = 2) :
    ∃! d : ℤ, Squarefree d ∧ Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  obtain ⟨θ, d, hmin, -, hd⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  refine ⟨d, ⟨hd, nonempty_algEquiv_quadraticAlgebra hK hmin⟩, fun e ⟨he, ⟨ψ⟩⟩ => ?_⟩
  obtain ⟨φ⟩ := nonempty_algEquiv_quadraticAlgebra hK hmin
  exact ((QuadraticAlgebra.nonempty_algEquiv_iff_of_squarefree hd he).mp
    ⟨φ.symm.trans ψ⟩).symm

/-- **The radicand classification of imaginary quadratic fields.** Every totally complex number
field of degree `2` over `ℚ` is isomorphic to `QuadraticAlgebra ℚ d 0` for exactly one negative
squarefree integer `d`. -/
theorem existsUnique_neg_squarefree_algEquiv [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    ∃! d : ℤ, d < 0 ∧ Squarefree d ∧ Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  obtain ⟨θ, d, hmin, -, hd, hneg⟩ :=
    exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top_of_isTotallyComplex hK
  refine ⟨d, ⟨hneg, hd, nonempty_algEquiv_quadraticAlgebra hK hmin⟩,
    fun e ⟨_, he, hψ⟩ => ?_⟩
  exact (existsUnique_squarefree_algEquiv hK).unique ⟨he, hψ⟩
    ⟨hd, nonempty_algEquiv_quadraticAlgebra hK hmin⟩

end NumberField
