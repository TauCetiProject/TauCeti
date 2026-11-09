/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

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

The unitary part `{g | g† * g = 1}` of the complex Spin group is therefore the subgroup fixed by
complex conjugation. For a nondegenerate form on a finite-dimensional space it is exactly the real
Spin group of `Q`, embedded by extension of scalars: a real Clifford element whose
complexification is a Spin element is itself a Spin element, because evenness, unitarity and the
preservation of vectors under twisted conjugation all descend along the injective map
`CliffordAlgebra.ofBaseChangeAux`. For the positive-definite form this identifies the unitary part
with the compact group `Spin(n)`, the compact factor in the polar decomposition of the complex
Spin group.

## Main results

* `CliffordAlgebra.complexConj_reverse_eq_coe_inv`: for `g` in the Spin group,
  `complexConj (reverse g)` is the inverse of the complex conjugate of `g` in the Spin group.
* `CliffordAlgebra.complexConj_reverse_mem_spinGroup`: the positive-form adjoint preserves the
  Spin group.
* `CliffordAlgebra.complexConj_reverse_mul_self_eq_one_iff`: a Spin element is unitary,
  `g† * g = 1`, exactly when it is fixed by complex conjugation.
* `CliffordAlgebra.ofBaseChangeAux_mem_spinGroup_iff`: a real Clifford element is a Spin element
  exactly when its complexification is.
* `CliffordAlgebra.mem_range_spinGroupBaseChange_iff`: the real Spin group is the unitary part of
  the complex Spin group.

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

/-- **The unitary Spin elements are the real ones.** A Spin element `g` of a complexified real
quadratic form satisfies `g† * g = 1` exactly when it is fixed by complex conjugation of the
coefficients, since `g†` is the inverse of the conjugate of `g`. -/
theorem complexConj_reverse_mul_self_eq_one_iff (g : spinGroup (Q.baseChange ℂ)) :
    complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1 ↔
      complexConj Q g = g := by
  rw [complexConj_reverse_eq_coe_inv, ← MulMemClass.coe_mul, OneMemClass.coe_eq_one,
    inv_mul_eq_one, Subtype.ext_iff, coe_spinGroupBaseChangeCongr_apply, ← complexConj_apply,
    eq_comm]

/-- **Spin membership descends from the complexification.** For a nondegenerate real quadratic
form on a finite-dimensional space, a real Clifford element is a Spin element exactly when its
image in the complexified Clifford algebra is a Spin element of `Q_ℂ`. -/
@[simp]
theorem ofBaseChangeAux_mem_spinGroup_iff [FiniteDimensional ℝ V] (hQ : Q.Nondegenerate)
    {x : CliffordAlgebra Q} :
    ofBaseChangeAux ℂ Q x ∈ spinGroup (Q.baseChange ℂ) ↔ x ∈ spinGroup Q := by
  refine ⟨fun hx => ?_, fun hx => by simpa using (spinGroupBaseChange (A := ℂ) Q ⟨x, hx⟩).2⟩
  have hinj := ofBaseChangeAux_injective (A := ℂ) Q
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- On the zero space the Lipschitz group of `Q_ℂ` is trivial, so `x = 1`.
    obtain ⟨u, hu, hux⟩ := pinGroup.mem_lipschitzGroup (spinGroup.mem_pin hx)
    simp only [SetLike.mem_coe, Subgroup.mem_toSubmonoid, lipschitzGroup_eq_bot,
      Subgroup.mem_bot] at hu
    subst hu
    rw [Units.coeHom_apply, Units.val_one, ← map_one (ofBaseChangeAux ℂ Q)] at hux
    rw [hinj hux.symm]
    exact one_mem _
  -- Otherwise check that `x` is unitary, even, and preserves the vectors under twisted
  -- conjugation; each condition holds after the injective map `ofBaseChangeAux`.
  rw [mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit,
    Unitary.mem_iff]
  refine ⟨⟨hinj ?_, hinj ?_⟩, ?_, fun m => ?_⟩
  · rw [map_mul, ofBaseChangeAux_star, spinGroup.star_mul_self_of_mem hx, map_one]
  · rw [map_mul, ofBaseChangeAux_star, spinGroup.mul_star_self_of_mem hx, map_one]
  · rw [← Subalgebra.mem_toSubmodule, even_toSubmodule, ← involute_eq_self_iff]
    exact hinj (by rw [ofBaseChangeAux_involute, spinGroup.involute_eq hx])
  · rw [← ofBaseChangeAux_mem_range_ι_iff, map_mul, map_mul, ofBaseChangeAux_involute,
      ofBaseChangeAux_ι, ofBaseChangeAux_star]
    have h := spinGroup.involute_act_ι_mem_range_ι (x := spinGroup.toUnits ⟨_, hx⟩) hx (1 ⊗ₜ m)
    have hinv : (((spinGroup.toUnits ⟨_, hx⟩)⁻¹ : (CliffordAlgebra (Q.baseChange ℂ))ˣ) :
        CliffordAlgebra (Q.baseChange ℂ)) = star (ofBaseChangeAux ℂ Q x) :=
      Units.inv_eq_of_mul_eq_one_right (spinGroup.mul_star_self_of_mem hx)
    rwa [hinv] at h

/-- **The real Spin group is the unitary part of the complex Spin group.** For a nondegenerate
real quadratic form on a finite-dimensional space, a Spin element `g` of `Q_ℂ` comes from the
real Spin group of `Q` by extension of scalars exactly when `g† * g = 1`. -/
theorem mem_range_spinGroupBaseChange_iff [FiniteDimensional ℝ V] (hQ : Q.Nondegenerate)
    (g : spinGroup (Q.baseChange ℂ)) :
    g ∈ (spinGroupBaseChange (A := ℂ) Q).range ↔
      complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1 := by
  rw [complexConj_reverse_mul_self_eq_one_iff, complexConj_eq_self_iff]
  refine ⟨fun ⟨h, hg⟩ => ⟨h, by rw [← coe_spinGroupBaseChange_apply, hg]⟩, fun ⟨y, hy⟩ => ?_⟩
  exact ⟨⟨y, (ofBaseChangeAux_mem_spinGroup_iff hQ).1 (hy ▸ g.2)⟩,
    Subtype.ext (by rw [coe_spinGroupBaseChange_apply, hy])⟩

end CliffordAlgebra
