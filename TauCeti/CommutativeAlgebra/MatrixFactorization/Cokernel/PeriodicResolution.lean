/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Projective
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Basic
public import TauCeti.Algebra.Homology.Periodic.Resolution

/-!
# The periodic resolution of the cokernel of a matrix factorization

Let `X = (X₀ --d₀--> X₁ --d₁--> X₀)` be a finite-projective matrix factorization of a
non-zero-divisor `w` of a commutative ring `S`, and let `X'` be its reduction modulo `w`, with
differentials `d₀'` and `d₁'` over the hypersurface ring `R = S/(w)`. The reduced two-periodic
complex is acyclic (`TauCeti.MatrixFactorization.quotientPeriodicComplex_acyclic`), so

`⋯ ⟶ X₀' --d₀'--> X₁' --d₁'--> X₀' --d₀'--> X₁' ⟶ coker d₀' ⟶ 0`

is a projective resolution of the cokernel of `d₀'`, periodic of period two from the start
(`TauCeti.MatrixFactorization.quotientCokernelProjectiveResolution`). This is Eisenbud's
periodic resolution attached to a matrix factorization. Its complex is
`TauCeti.PeriodicComplex.resolutionComplex` of the reduced complex, so it has a periodic tail
of period two with empty preperiod
(`TauCeti.MatrixFactorization.quotientCokernelProjectiveResolution_complex_hasPeriodicTail`).

Only the non-zero-divisor hypothesis on `w` is used. Eisenbud's theorem that every finitely
generated module over a hypersurface has an eventually two-periodic minimal resolution of this
form needs a regular local ring `S` and is not stated here.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

/-- **The periodic resolution of a matrix factorization.** For a non-zero-divisor `w`, the
reduction modulo `w` of a finite-projective matrix factorization `X` is a two-periodic
projective resolution
`⋯ ⟶ X₀' --d₀'--> X₁' --d₁'--> X₀' --d₀'--> X₁' ⟶ coker d₀'`
of the cokernel of its reduced even-to-odd differential, augmented by the cokernel projection. -/
@[expose]
def quotientCokernelProjectiveResolution (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    ProjectiveResolution
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  PeriodicComplex.projectiveResolution (quotientPeriodicComplex.obj X)
    (quotientPeriodicComplex_acyclic hw X) 1 Int.cast_one (zero_add 1)
    (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))
    (d₀_cokernelπ _) (isColimitCokernelπ _)

/-- The complex of `TauCeti.MatrixFactorization.quotientCokernelProjectiveResolution` unfolds
the reduced two-periodic complex, with the odd component `X₁'` in degree `0`. -/
@[simp]
theorem quotientCokernelProjectiveResolution_complex (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).complex =
      PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) 1 :=
  (rfl)

/-- The augmentation of `TauCeti.MatrixFactorization.quotientCokernelProjectiveResolution` is
the cokernel projection. -/
@[simp]
theorem quotientCokernelProjectiveResolution_π_f_zero (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).π.f 0 =
      (PeriodicComplex.resolutionComplexXZeroIso (quotientPeriodicComplex.obj X)
        (Int.cast_one (R := ZMod 2))).hom ≫
        cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) :=
  PeriodicComplex.projectiveResolution_π_f_zero ..

/-- The resolution `TauCeti.MatrixFactorization.quotientCokernelProjectiveResolution` is
two-periodic from the start: it has a periodic tail of period two with empty preperiod. -/
theorem quotientCokernelProjectiveResolution_complex_hasPeriodicTail
    (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).complex.HasPeriodicTail 2 0 :=
  PeriodicComplex.resolutionComplex_hasPeriodicTail _ _

end TauCeti.MatrixFactorization
