/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Laurent

/-!
# The PBW Rees algebra with the parameter inverted

The PBW Rees algebra `reesAlgebra R L` is a family over the parameter line `R[t]` whose fibre at
`t = 1` is the enveloping algebra `U_R(L)` and whose fibre at `t = 0` is, for `L` free over `R`,
the symmetric algebra.
Away from `t = 0` the family is constant: after scalar extension along `R[t] → R[t, t⁻¹]` it
becomes `R[t, t⁻¹] ⊗[R] U_R(L)`, with the Rees generator `j(x) = ι(x) t` going to `t ⊗ ι(x)`
and the parameter going to `t ⊗ 1`. Only the scalar extension along the commutative parameter
ring is used; no noncommutative localization is involved.

This comparison holds over every commutative ring and for every Lie algebra; it requires neither
freeness of the Lie algebra nor a characteristic hypothesis, only the exhaustive PBW filtration.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reesLaurentEquiv`: the `R[t, t⁻¹]`-algebra isomorphism
  `R[t, t⁻¹] ⊗[R[t]] reesAlgebra R L ≃ R[t, t⁻¹] ⊗[R] U_R(L)`.

## References

* J. Dixmier, *Enveloping Algebras*, for the Rees construction of a filtered enveloping algebra.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Inverting the parameter of the PBW Rees algebra gives the constant family: the scalar
extension along `R[t] → R[t, t⁻¹]` is `R[t, t⁻¹] ⊗[R] U_R(L)`. -/
noncomputable def reesLaurentEquiv :
    (R[T;T⁻¹] ⊗[R[X]] reesAlgebra R L) ≃ₐ[R[T;T⁻¹]] R[T;T⁻¹] ⊗[R] U :=
  coeffSubalgebra.baseChangeLaurentEquiv (pbwFiltration R L) (one_mem_pbwFiltration R L 1)
    (iSup_pbwFiltration_eq_top R L)

variable {R L}

/-- The comparison multiplies the image of the Rees factor under `toLaurentTensor` by the scalar
factor. -/
@[simp]
theorem reesLaurentEquiv_tmul (f : R[T;T⁻¹]) (p : reesAlgebra R L) :
    reesLaurentEquiv R L (f ⊗ₜ[R[X]] p) = f • toLaurentTensor R U p :=
  coeffSubalgebra.baseChangeLaurentEquiv_tmul _ _ _ f p

/-- The comparison sends the Rees generator `j(x)` to `t ⊗ ι(x)`. -/
theorem reesLaurentEquiv_one_tmul_reesGenerator (x : L) :
    reesLaurentEquiv R L (1 ⊗ₜ[R[X]] reesGenerator R L x) =
      T 1 ⊗ₜ _root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [reesLaurentEquiv_tmul, coe_reesGenerator, toLaurentTensor_monomial, one_smul,
    Nat.cast_one]

/-- The inverse comparison sends the image `toLaurentTensor p` to `1 ⊗ p`. -/
@[simp]
theorem reesLaurentEquiv_symm_toLaurentTensor (p : reesAlgebra R L) :
    (reesLaurentEquiv R L).symm (toLaurentTensor R U p) = 1 ⊗ₜ[R[X]] p :=
  coeffSubalgebra.baseChangeLaurentEquiv_symm_toLaurentTensor _ _ _ p

/-- The inverse comparison sends `f ⊗ ι(x)` to `f t⁻¹ ⊗ j(x)`. -/
-- Rewrite before the simplifier expands the canonical enveloping generator.
@[simp↓]
theorem reesLaurentEquiv_symm_tmul_ι (f : R[T;T⁻¹]) (x : L) :
    (reesLaurentEquiv R L).symm (f ⊗ₜ _root_.UniversalEnvelopingAlgebra.ι R x) =
      (f * T (-1)) ⊗ₜ[R[X]] reesGenerator R L x := by
  have hx := ι_mem_pbwFiltration_one R L x
  have h : reesGenerator R L x = coeffSubalgebra.monomial (pbwFiltration R L) 1 _ hx :=
    Subtype.ext (by rw [coe_reesGenerator, coeffSubalgebra.coe_monomial])
  rw [h, reesLaurentEquiv, coeffSubalgebra.baseChangeLaurentEquiv_symm_tmul_of_mem _ _ _ f hx,
    Nat.cast_one]

end TauCeti.UniversalEnvelopingAlgebra
