/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Tensor
public import TauCeti.Algebra.Lie.HighestWeight.Weyl.Inversion

/-!
# The Racah–Speiser / Brauer–Klimyk formula

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, `H` a Cartan subalgebra, and `b` a base of its root system.

Weyl-alternating inversion reads the isotypic multiplicities of a finite-dimensional `L`-module `M`
from `ch M · Δ`. Specializing `M` to the tensor product `L(λ) ⊗ L(μ)` of two finite-dimensional
irreducibles turns Weyl-alternating inversion into a closed form for the tensor multiplicity
`c^ν_{λμ} = TauCeti.tensorMultiplicity b λ μ ν`. Formal characters are multiplicative on tensor
products (`TauCeti.formalCharacter_tensor`), and the Weyl character formula rewrites the first
factor as `ch L(λ) · Δ = N(λ)` (`TauCeti.formalCharacter_mul_weylDenominator_eq_weylNumerator`), so

`c^ν_{λμ} = [e^ν] (ch L(μ) · N(λ)) = ∑_{w ∈ W} sgn(w) · [e^{ν - w ⬝ λ}] ch L(μ)`

(`TauCeti.tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator` and
`TauCeti.tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff`). This is the
**Racah–Speiser** (or **Brauer–Klimyk**) formula: to compute the multiplicity of `L(ν)` in
`L(λ) ⊗ L(μ)`, shift the weights of `L(μ)` by `λ`, fold those that land outside the dominant
chamber back into it by the dot action of the Weyl group with signs `sgn(w)`, and read off the
resulting coefficient at `ν`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VIII, §9, Exercise 2 (the Brauer–Klimyk formula
  and its specialization to minuscule weights).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24,
  Exercise 9.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra _root_.LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

section RacahSpeiser

variable (b : (IsKilling.rootSystem H).Base)

/-- **The Racah–Speiser (or Brauer–Klimyk) formula, in group-algebra form**: for dominant integral
weights `lam`, `mu`, and `nu`, the tensor multiplicity `c^nu_{lam mu}` of `L(nu)` in
`L(lam) ⊗ L(mu)` is the coefficient at `nu` of `ch L(mu) · N(lam)`.

This combines Weyl-alternating inversion
(`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`) on `L(lam) ⊗ L(mu)`,
multiplicativity of formal characters (`TauCeti.formalCharacter_tensor`), and the Weyl character
formula `ch L(lam) · Δ = N(lam)`. -/
theorem tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsDominantIntegral b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
    (tensorMultiplicity b lam mu nu : ℤ) =
      (formalCharacter K H (irreducibleQuotient b mu) *
        weylNumerator (IsKilling.rootSystem H) b lam).coeff nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  have hchar : formalCharacter K H (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) =
      formalCharacter K H (irreducibleQuotient b lam) *
        formalCharacter K H (irreducibleQuotient b mu) :=
    formalCharacter_tensor
  rw [tensorMultiplicity_def,
    ← coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity b hnu,
    hchar, mul_comm (formalCharacter K H (irreducibleQuotient b lam)),
    mul_assoc,
    formalCharacter_mul_weylDenominator_eq_weylNumerator
      (isHighestWeightVector_irreducibleQuotientGenerator b lam)
      (lieSpan_irreducibleQuotientGenerator_eq_top b lam)]

/-- **The Racah–Speiser (or Brauer–Klimyk) formula, expanded over the Weyl group**: for dominant
integral weights `lam`, `mu`, and `nu`,
`c^nu_{lam mu} = ∑_{w ∈ W} sgn(w) · [e^{nu - w ⬝ lam}] ch L(mu)`. -/
theorem tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsDominantIntegral b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
    (tensorMultiplicity b lam mu nu : ℤ) =
      ∑ w : (IsKilling.rootSystem H).weylGroup,
        (weylSign (IsKilling.rootSystem H) b w : ℤ) *
          (formalCharacter K H (irreducibleQuotient b mu)).coeff
            (nu - dotAction (IsKilling.rootSystem H) b w lam) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  rw [tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator b hlam hmu hnu,
    weylNumerator_def, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_mul_single_apply, ← sub_eq_add_neg, mul_comm]

end RacahSpeiser

end TauCeti
