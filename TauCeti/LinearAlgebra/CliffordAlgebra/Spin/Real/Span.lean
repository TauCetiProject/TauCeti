/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
-- Private: the definiteness of a real anisotropic form is used only inside proofs.
import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Definite real Spin groups span the even Clifford algebra

Over `ℝ`, an anisotropic quadratic form is positive or negative definite
(`QuadraticForm.anisotropic_iff_posDef_or_negDef`). Two vectors of nonzero norm therefore have
norms of the same sign, so `(Q v)⁻¹ * (Q w)⁻¹` is positive and hence a real square. This is the
square normalization under which `CliffordAlgebra.span_spinGroup_eq_even_of_isSquare`
lifts every product `ι v * ι w` of vectors into the linear span of the Spin group. No
`IsSepClosed ℝ` is involved: the compact group `Spin(n)` of the positive-definite form is not the
Spin group of a split form, but it spans the real even Clifford algebra all the same. In
dimension zero the Spin group is `{1}` and the even Clifford algebra is `ℝ`.

The same span survives complexification. By `CliffordAlgebra.span_spinGroupBaseChange_eq_even`,
the `ℂ`-linear span of the image of the real Spin group under extension of scalars is the even
Clifford algebra of the complexified form. Representations of the complex even Clifford algebra,
such as the half-spin modules, therefore have the same invariant subspaces and intertwiners under
the compact real group as under the whole even algebra.

## Main results

* `CliffordAlgebra.span_spinGroup_eq_even_of_anisotropic`: the Spin group of an anisotropic real
  quadratic form spans its even Clifford algebra.
* `CliffordAlgebra.span_spinGroupBaseChange_eq_even_of_anisotropic`: after extension of scalars to
  any real algebra, such as `ℂ`, the image of that Spin group spans the even Clifford algebra of
  the extended form.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- Two vectors of nonzero norm for an anisotropic real form have norms of the same sign, so the
product of the inverse norms is a real square. -/
private theorem isSquare_inv_mul_inv_of_anisotropic (hQ : Q.Anisotropic) {v w : V}
    (hv : Q v ≠ 0) (hw : Q w ≠ 0) : IsSquare ((Q v)⁻¹ * (Q w)⁻¹) := by
  have hv0 : v ≠ 0 := fun h ↦ hv (h ▸ QuadraticMap.map_zero Q)
  have hw0 : w ≠ 0 := fun h ↦ hw (h ▸ QuadraticMap.map_zero Q)
  rw [Real.isSquare_iff]
  rcases (QuadraticForm.anisotropic_iff_posDef_or_negDef Q).1 hQ with h | h
  · exact (mul_pos (inv_pos.2 (h v hv0)) (inv_pos.2 (h w hw0))).le
  · have hv' : Q v < 0 := neg_pos.1 (h v hv0)
    have hw' : Q w < 0 := neg_pos.1 (h w hw0)
    exact (mul_pos_of_neg_of_neg (inv_lt_zero.2 hv') (inv_lt_zero.2 hw')).le

/-- **The Spin group of an anisotropic real quadratic form spans its even Clifford algebra.** This
covers the compact group `Spin(n)` of a positive-definite form, and of a negative-definite one;
the span includes the scalars, which is the whole even algebra in dimension zero. -/
theorem span_spinGroup_eq_even_of_anisotropic (hQ : Q.Anisotropic) :
    Submodule.span ℝ (spinGroup Q : Set (CliffordAlgebra Q)) = (even Q).toSubmodule :=
  span_spinGroup_eq_even_of_isSquare Q hQ.nondegenerate fun _ _ hv hw ↦
    isSquare_inv_mul_inv_of_anisotropic hQ hv hw

/-- **The complexified real Spin group spans the complex even Clifford algebra.** For an
anisotropic real quadratic form, the `A`-linear span of the image of `spinGroup Q` in the Spin group
of `Q_A` is the even Clifford algebra of `Q_A`; for `A = ℂ` and a positive-definite `Q` this is the
complex-linear span of the compact group `Spin(n)` acting on complex spinors. -/
theorem span_spinGroupBaseChange_eq_even_of_anisotropic {A : Type*} [CommRing A] [Algebra ℝ A]
    (hQ : Q.Anisotropic) :
    Submodule.span A (Set.range fun g : spinGroup Q ↦
        (spinGroupBaseChange (A := A) Q g : CliffordAlgebra (Q.baseChange A))) =
      (even (Q.baseChange A)).toSubmodule :=
  span_spinGroupBaseChange_eq_even (span_spinGroup_eq_even_of_anisotropic hQ)

end CliffordAlgebra
