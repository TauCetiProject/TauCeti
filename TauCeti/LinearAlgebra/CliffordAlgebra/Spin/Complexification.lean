/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange

/-!
# The positive-form adjoint of a complexified Spin group

For a real quadratic form `Q`, the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` carries the
positive-form adjoint

  `a† = complexConj (reverse a)`,

complex conjugation of the coefficients after reversal. On the Spin group of `Q_ℂ` the adjoint is
the inverse of the complex conjugate, `g† = (conj g)⁻¹`: a Spin element is even and
`star g * g = 1`, and complex conjugation of the coefficients preserves the Spin group
(`CliffordAlgebra.spinGroupBaseChangeCongr`). In particular `g†` and `g† * g` lie in the Spin
group. This is the algebraic input for the polar decomposition
`g = (g (g† g)^(-1/2)) (g† g)^(1/2)` of complex Spin elements.

## Main results

* `CliffordAlgebra.complexConj_reverse_eq_coe_inv`: for `g` in the Spin group,
  `complexConj (reverse g)` is the inverse of the complex conjugate of `g` in the Spin group.
* `CliffordAlgebra.complexConj_reverse_mem_spinGroup`: the positive-form adjoint preserves the
  Spin group.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- **The adjoint of a Spin element is the inverse of its complex conjugate.** For `g` in the Spin
group of a complexified real quadratic form, `complexConj (reverse g)` is the inverse, in the Spin
group, of the coefficientwise complex conjugate of `g`; in particular it is again a Spin
element. -/
theorem complexConj_reverse_eq_coe_inv (g : spinGroup (Q.baseChange ℂ)) :
    complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) =
      ((spinGroupBaseChangeCongr Complex.conjAe Q g)⁻¹ : spinGroup (Q.baseChange ℂ)) := by
  conv_lhs => rw [← spinGroup.involute_eq g.2]
  simp [← spinGroup.star_eq_inv, complexConj_apply, star_def]

/-- The positive-form adjoint preserves the Spin group of a complexified real quadratic form. -/
theorem complexConj_reverse_mem_spinGroup {g : CliffordAlgebra (Q.baseChange ℂ)}
    (hg : g ∈ spinGroup (Q.baseChange ℂ)) :
    complexConj Q (reverse g) ∈ spinGroup (Q.baseChange ℂ) := by
  rw [complexConj_reverse_eq_coe_inv ⟨g, hg⟩]
  exact SetLike.coe_mem _

end CliffordAlgebra
