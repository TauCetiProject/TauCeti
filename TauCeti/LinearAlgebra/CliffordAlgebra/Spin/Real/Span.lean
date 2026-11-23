/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
-- Private: the spanning criterion under the square normalization is used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift
-- Private: the definiteness of a real anisotropic form is used only inside proofs.
import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Definite real Spin groups span the even Clifford algebra

Over `ℝ`, an anisotropic quadratic form is positive or negative definite
(`QuadraticForm.anisotropic_iff_posDef_or_negDef`). Two nonzero vectors therefore have norms of the
same sign, so `(Q v)⁻¹ * (Q w)⁻¹` is nonnegative and hence a real square
(`QuadraticMap.Anisotropic.isSquare_inv_mul_inv`). This is the
square normalization under which `CliffordAlgebra.span_spinGroup_eq_even_of_isSquare`
lifts every product `ι v * ι w` of vectors into the linear span of the Spin group. No
`IsSepClosed ℝ` is involved: the compact group `Spin(n)` of the positive-definite form spans the
real even Clifford algebra. In dimension zero the Spin group is `{1}` and the even Clifford
algebra is `ℝ`.

The same span survives complexification. By `TauCeti.span_range_spinGroupBaseChange_eq_even`,
the `ℂ`-linear span of the image of the real Spin group under extension of scalars is the even
Clifford algebra of the complexified form. Representations of the complex even Clifford algebra,
such as the half-spin modules, therefore have the same invariant subspaces and intertwiners under
the compact real group as under the whole even algebra.

## Main results

* `QuadraticMap.Anisotropic.span_spinGroup_eq_even`: the Spin group of an anisotropic real
  quadratic form spans its even Clifford algebra.
* `QuadraticMap.Anisotropic.span_range_spinGroupBaseChange_eq_even`: after extension of scalars to
  any commutative real algebra, such as `ℂ`, the image of that Spin group spans the even Clifford
  algebra of the extended form.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

open CliffordAlgebra

namespace QuadraticMap.Anisotropic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- **The Spin group of an anisotropic real quadratic form spans its even Clifford algebra.** This
covers the compact group `Spin(n)` of a positive-definite form, and of a negative-definite one;
the span includes the scalars, which is the whole even algebra in dimension zero. -/
theorem span_spinGroup_eq_even (hQ : Q.Anisotropic) :
    Submodule.span ℝ (spinGroup Q : Set (CliffordAlgebra Q)) = (even Q).toSubmodule :=
  span_spinGroup_eq_even_of_isSquare Q hQ.nondegenerate fun v w _ _ ↦
    hQ.isSquare_inv_mul_inv v w

/-- **The scalar-extended Clifford values of a real Spin group span the even Clifford algebra.**
For an anisotropic real quadratic form and any commutative real algebra `A`, the `A`-linear span of
the image of the real group `spinGroup Q` in the Spin group of `Q_A` is the even Clifford algebra
of `Q_A`; this image is in general smaller than the Spin group of `Q_A`. For `A = ℂ` and a
positive-definite `Q`, the image of the compact group `Spin(n)` spans the even Clifford algebra
inside the complexified Clifford algebra; applying a spinor action then gives the image of that
algebra in the endomorphism ring. -/
theorem span_range_spinGroupBaseChange_eq_even (hQ : Q.Anisotropic) {A : Type*} [CommRing A]
    [Algebra ℝ A] :
    Submodule.span A (Set.range fun g : spinGroup Q ↦
        (spinGroupBaseChange (A := A) Q g : CliffordAlgebra (Q.baseChange A))) =
      (even (Q.baseChange A)).toSubmodule :=
  TauCeti.span_range_spinGroupBaseChange_eq_even hQ.span_spinGroup_eq_even

end QuadraticMap.Anisotropic
