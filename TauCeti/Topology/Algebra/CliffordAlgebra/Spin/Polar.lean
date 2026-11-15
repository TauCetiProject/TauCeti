/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.RealPower
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealPower
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# The polar deformation retraction of a complex Spin group

Let `Q` be a real quadratic form with a real orthonormal basis `b`, so `Q (b i) = 1` for every `i`,
and let `e_s` be the ordered-product basis of the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`
for `1 ⊗ b`. The positive-form adjoint `x† = complexConj (reverse x)` is the matrix adjoint of left
multiplication in the orthonormal basis `e_s`
(`CliffordAlgebra.toMatrix_mulLeft_complexConj_reverse`), so for a unit `g` the element
`a = g† g` has a positive definite matrix and real powers `a ^ t`, computed by the continuous
functional calculus of its matrix (`Algebra.leftMulMatrixRpow`). For `g` in the Spin group these
powers are Spin elements
(`CliffordAlgebra.leftMulMatrixRpow_complexConj_reverse_mul_self_mem_spinGroup`), and they are
self-adjoint
(`CliffordAlgebra.complexConj_reverse_leftMulMatrixRpow_complexConj_reverse_mul_self`). They are
jointly continuous in `g` and `t`
(`CliffordAlgebra.continuousOn_leftMulMatrixRpow_complexConj_reverse_mul_self`).

This file proves that the polar deformation

  `H(t, g) = g (g† g) ^ (-t / 2)`,  `0 ≤ t ≤ 1`,

is a strong deformation retraction of the Spin group of `Q_ℂ` onto its unitary part
`{g | g† g = 1}`. The real powers are self-adjoint, `((g† g) ^ s)† = (g† g) ^ s`, so
`H(t, g)† H(t, g) = (g† g) ^ (1 - t)`. At `t = 0` the deformation is the identity, at `t = 1` it
lands in the unitary part, and it fixes the unitary part throughout, where `g† g = 1`. The
inclusion of the unitary part is therefore a homotopy equivalence. On the Spin group
`g† = (conj g)⁻¹` (`CliffordAlgebra.complexConj_reverse_eq_coe_inv`), so the unitary part consists
of the Spin elements fixed by complex conjugation of the coefficients.

## Main results

* `CliffordAlgebra.spinPolarRetraction`: the retraction `g ↦ g (g† g) ^ (-1/2)` of the Spin group
  onto its unitary part.
* `CliffordAlgebra.spinPolarHomotopyRel`: the polar deformation, a homotopy from the identity to
  the retraction fixing the unitary part.
* `CliffordAlgebra.spinPolarHomotopyEquiv`: the inclusion of the unitary part into the Spin group
  is a homotopy equivalence.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002, Chapter VI,
  §1 (the global Cartan decomposition of a linear reductive group).
-/

public section

open scoped MatrixOrder ComplexOrder ComplexConjugate ContinuousMap

namespace CliffordAlgebra

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder I] [Fintype I]
  {Q : QuadraticForm ℝ V} {b : Module.Basis I ℝ V}

/-! ### The polar deformation of the Spin group -/

section Spin

variable (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
include hb hQ

/-- `g (g† g) ^ s` is a Spin element for every Spin element `g`. -/
private theorem mul_leftMulMatrixRpow_mem_spinGroup (g : spinGroup (Q.baseChange ℂ)) (s : ℝ) :
    (g : CliffordAlgebra (Q.baseChange ℂ)) * Algebra.leftMulMatrixRpow
        (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g) s ∈
      spinGroup (Q.baseChange ℂ) :=
  mul_mem g.2 (leftMulMatrixRpow_complexConj_reverse_mul_self_mem_spinGroup hb hQ g s)

/-- `(g, s) ↦ g (g† g) ^ s` is jointly continuous on the Spin group. -/
private theorem continuous_mul_leftMulMatrixRpow :
    Continuous fun p : spinGroup (Q.baseChange ℂ) × ℝ ↦
      (p.1 : CliffordAlgebra (Q.baseChange ℂ)) * Algebra.leftMulMatrixRpow
        (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse (p.1 : CliffordAlgebra (Q.baseChange ℂ))) * p.1) p.2 := by
  have : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  have hf : Continuous fun p : spinGroup (Q.baseChange ℂ) × ℝ ↦
      ((p.1 : CliffordAlgebra (Q.baseChange ℂ)), p.2) := by fun_prop
  exact (continuous_subtype_val.comp continuous_fst).mul
    ((continuousOn_leftMulMatrixRpow_complexConj_reverse_mul_self hb hQ).comp_continuous hf
      fun p ↦ ⟨spinGroup.isUnit_coe p.1, trivial⟩)

/-- **The polar retraction of a complex Spin group** onto its unitary part `{g | g† g = 1}`: the
continuous map `g ↦ g (g† g) ^ (-1/2)`, where `g† = complexConj (reverse g)` and the power is taken
through the matrix of `g† * g` in the ordered-product basis of a real orthonormal basis. -/
noncomputable def spinPolarRetraction :
    C(spinGroup (Q.baseChange ℂ), spinGroup (Q.baseChange ℂ)) where
  toFun g := ⟨_, mul_leftMulMatrixRpow_mem_spinGroup hb hQ g (-1 / 2)⟩
  continuous_toFun := ((continuous_mul_leftMulMatrixRpow hb hQ).comp
    (continuous_id.prodMk continuous_const)).subtype_mk _

/-- The polar retraction sends `g` to `g (g† g) ^ (-1/2)`. -/
@[simp]
theorem coe_spinPolarRetraction_apply (g : spinGroup (Q.baseChange ℂ)) :
    (spinPolarRetraction hb hQ g : CliffordAlgebra (Q.baseChange ℂ)) =
      g * Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g) (-1 / 2) :=
  (rfl)

/-- **The polar retraction lands in the unitary part**: `r(g)† r(g) = 1`. -/
theorem complexConj_reverse_mul_self_spinPolarRetraction (g : spinGroup (Q.baseChange ℂ)) :
    complexConj Q (reverse (spinPolarRetraction hb hQ g : CliffordAlgebra (Q.baseChange ℂ))) *
      spinPolarRetraction hb hQ g = 1 := by
  rw [coe_spinPolarRetraction_apply, complexConj_reverse_mul_self_mul_leftMulMatrixRpow hb hQ
    (spinGroup.isUnit_coe g), show (-1 / 2 : ℝ) + 1 + -1 / 2 = 0 by norm_num]
  exact Algebra.leftMulMatrixRpow_zero
    (isStrictlyPositive_leftMulMatrix_complexConj_reverse_mul_self hb hQ
      (spinGroup.isUnit_coe g)).nonneg

/-- **The polar retraction fixes the unitary part**: `r(g) = g` when `g† g = 1`. -/
theorem spinPolarRetraction_of_complexConj_reverse_mul_self_eq_one
    {g : spinGroup (Q.baseChange ℂ)}
    (hg : complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1) :
    spinPolarRetraction hb hQ g = g := by
  ext
  rw [coe_spinPolarRetraction_apply, hg, Algebra.leftMulMatrixRpow_one_left, mul_one]

/-- **The polar deformation of a complex Spin group**, `H(t, g) = g (g† g) ^ (-t/2)`: a homotopy
from the identity to the polar retraction `CliffordAlgebra.spinPolarRetraction` that fixes the
unitary part `{g | g† g = 1}`. Here `g† = complexConj (reverse g)` and the powers are taken
through the matrix of `g† * g` in the ordered-product basis of a real orthonormal basis. Together
with `CliffordAlgebra.complexConj_reverse_mul_self_spinPolarRetraction` this makes the unitary
part a strong deformation retract of the Spin group. -/
noncomputable def spinPolarHomotopyRel :
    (ContinuousMap.id (spinGroup (Q.baseChange ℂ))).HomotopyRel (spinPolarRetraction hb hQ)
      {g | complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1} where
  toFun p := ⟨_, mul_leftMulMatrixRpow_mem_spinGroup hb hQ p.2 (-(p.1 : ℝ) / 2)⟩
  continuous_toFun := ((continuous_mul_leftMulMatrixRpow hb hQ).comp (continuous_snd.prodMk
    ((continuous_subtype_val.comp continuous_fst).neg.div_const 2))).subtype_mk _
  map_zero_left g := by
    ext
    simp only [Set.Icc.coe_zero, neg_zero, zero_div, ContinuousMap.id_apply]
    rw [Algebra.leftMulMatrixRpow_zero
      (isStrictlyPositive_leftMulMatrix_complexConj_reverse_mul_self hb hQ
        (spinGroup.isUnit_coe g)).nonneg, mul_one]
  map_one_left g := by
    ext
    simp only [Set.Icc.coe_one, coe_spinPolarRetraction_apply]
  prop' t g hg := by
    ext
    simp only [ContinuousMap.coe_mk, ContinuousMap.id_apply]
    rw [Set.mem_ofPred_eq] at hg
    rw [hg, Algebra.leftMulMatrixRpow_one_left, mul_one]

/-- The polar deformation at time `t` sends `g` to `g (g† g) ^ (-t/2)`. -/
@[simp]
theorem coe_spinPolarHomotopyRel_apply (p : unitInterval × spinGroup (Q.baseChange ℂ)) :
    (spinPolarHomotopyRel hb hQ p : CliffordAlgebra (Q.baseChange ℂ)) =
      p.2 * Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse (p.2 : CliffordAlgebra (Q.baseChange ℂ))) * p.2)
        (-(p.1 : ℝ) / 2) :=
  (rfl)

/-- **The unitary part of a complex Spin group is homotopy equivalent to the whole group**: the
inclusion of `{g | g† g = 1}` is a homotopy equivalence, with homotopy inverse the polar
retraction. -/
noncomputable def spinPolarHomotopyEquiv :
    {g : spinGroup (Q.baseChange ℂ) //
        complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1} ≃ₕ
      spinGroup (Q.baseChange ℂ) where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := ⟨fun g ↦ ⟨spinPolarRetraction hb hQ g,
      complexConj_reverse_mul_self_spinPolarRetraction hb hQ g⟩,
    (spinPolarRetraction hb hQ).continuous.subtype_mk _⟩
  left_inv := by
    -- The retraction fixes the unitary part, so it is a left inverse of the inclusion.
    refine ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id _)).cast ?_ rfl⟩
    ext g
    exact congrArg Subtype.val
      (spinPolarRetraction_of_complexConj_reverse_mul_self_eq_one hb hQ g.2).symm
  right_inv := by
    -- Composing the corestricted retraction with the inclusion recovers the retraction.
    refine ⟨(spinPolarHomotopyRel hb hQ).toHomotopy.symm.cast ?_ rfl⟩
    ext g
    rfl

/-- The homotopy equivalence `CliffordAlgebra.spinPolarHomotopyEquiv` is the inclusion. -/
@[simp]
theorem coe_spinPolarHomotopyEquiv_apply
    (g : {g : spinGroup (Q.baseChange ℂ) //
      complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g = 1}) :
    spinPolarHomotopyEquiv hb hQ g = g :=
  (rfl)

/-- The homotopy inverse of `CliffordAlgebra.spinPolarHomotopyEquiv` is the polar retraction. -/
@[simp]
theorem coe_spinPolarHomotopyEquiv_symm_apply (g : spinGroup (Q.baseChange ℂ)) :
    ((spinPolarHomotopyEquiv hb hQ).symm g : spinGroup (Q.baseChange ℂ)) =
      spinPolarRetraction hb hQ g :=
  (rfl)

end Spin

end CliffordAlgebra
