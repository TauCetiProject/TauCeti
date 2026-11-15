/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Tensor
public import TauCeti.Algebra.Lie.HighestWeight.Weyl.Inversion

/-!
# The Brauer–Klimyk and Racah–Speiser formulas

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, `H` a Cartan subalgebra, and `b` a base of its root system.

Weyl-alternating inversion reads the isotypic multiplicities of a finite-dimensional `L`-module from
its formal character times the Weyl denominator `Δ`. Applied to the tensor product `L(λ) ⊗ M` of a
finite-dimensional irreducible `L(λ)` with an arbitrary finite-dimensional `L`-module `M`, it gives
a closed form for the multiplicity `[L(λ) ⊗ M : L(ν)]` of `L(ν)` in `L(λ) ⊗ M`. Formal characters
are multiplicative on tensor products (`TauCeti.formalCharacter_tensor`), and the Weyl character
formula rewrites the first factor as `ch L(λ) · Δ = N(λ)`
(`TauCeti.formalCharacter_mul_weylDenominator_eq_weylNumerator`), so

`[L(λ) ⊗ M : L(ν)] = [e^ν] (ch M · N(λ)) = ∑_{w ∈ W} sgn(w) · [e^{ν - w ⬝ λ}] ch M`.

This is the **Brauer–Klimyk** formula: to compute the multiplicity of `L(ν)` in `L(λ) ⊗ M`, shift
the weights of `M` by `λ`, fold those that land outside the dominant chamber back into it by the dot
action of the Weyl group with signs `sgn(w)`, and read off the resulting coefficient at `ν`. Its
case `M = L(μ)` is the **Racah–Speiser** formula for the tensor multiplicity
`c^ν_{λμ} = TauCeti.tensorMultiplicity b λ μ ν`.

## Main results

* `TauCeti.isotypicMultiplicity_tensor_eq_coeff_formalCharacter_mul_weylNumerator` and
  `TauCeti.isotypicMultiplicity_tensor_eq_sum_weylSign_mul_formalCharacter_coeff`: the
  Brauer–Klimyk formula for `L(λ) ⊗ M`, in group-algebra form and expanded over the Weyl group.
* `TauCeti.tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator` and
  `TauCeti.tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff`: the Racah–Speiser
  formula, the case `M = L(μ)`.

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

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable (b : (IsKilling.rootSystem H).Base)

section BrauerKlimyk

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- **The Brauer–Klimyk formula, in group-algebra form**: for dominant integral weights `lam` and
`nu` and a finite-dimensional `L`-module `M`, the multiplicity of `L(nu)` in `L(lam) ⊗ M` is the
coefficient at `nu` of `ch M · N(lam)`.

This combines Weyl-alternating inversion
(`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`) on `L(lam) ⊗ M`,
multiplicativity of formal characters (`TauCeti.formalCharacter_tensor`), and the Weyl character
formula `ch L(lam) · Δ = N(lam)`. -/
theorem isotypicMultiplicity_tensor_eq_coeff_formalCharacter_mul_weylNumerator
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam nu : Dual K H} (hlam : IsDominantIntegral b lam) (hnu : IsDominantIntegral b nu) :
    (LieModule.isotypicMultiplicity K L (irreducibleQuotient b lam ⊗[K] M)
        (irreducibleQuotient b nu) : ℤ) =
      (formalCharacter K H M * weylNumerator (IsKilling.rootSystem H) b lam).coeff nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  have hchar : formalCharacter K H (irreducibleQuotient b lam ⊗[K] M) =
      formalCharacter K H (irreducibleQuotient b lam) * formalCharacter K H M :=
    formalCharacter_tensor
  rw [← coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity b hnu,
    hchar, mul_comm (formalCharacter K H (irreducibleQuotient b lam)), mul_assoc,
    formalCharacter_mul_weylDenominator_eq_weylNumerator
      (isHighestWeightVector_irreducibleQuotientGenerator b lam)
      (lieSpan_irreducibleQuotientGenerator_eq_top b lam)]

/-- **The Brauer–Klimyk formula, expanded over the Weyl group**: for dominant integral weights
`lam` and `nu` and a finite-dimensional `L`-module `M`, the multiplicity of `L(nu)` in
`L(lam) ⊗ M` is `∑_{w ∈ W} sgn(w) · [e^{nu - w ⬝ lam}] ch M`. -/
theorem isotypicMultiplicity_tensor_eq_sum_weylSign_mul_formalCharacter_coeff
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam nu : Dual K H} (hlam : IsDominantIntegral b lam) (hnu : IsDominantIntegral b nu) :
    (LieModule.isotypicMultiplicity K L (irreducibleQuotient b lam ⊗[K] M)
        (irreducibleQuotient b nu) : ℤ) =
      ∑ w : (IsKilling.rootSystem H).weylGroup,
        (weylSign (IsKilling.rootSystem H) b w : ℤ) *
          (formalCharacter K H M).coeff (nu - dotAction (IsKilling.rootSystem H) b w lam) := by
  rw [isotypicMultiplicity_tensor_eq_coeff_formalCharacter_mul_weylNumerator b hlam hnu,
    weylNumerator_def, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_mul_single_apply, ← sub_eq_add_neg, mul_comm]

end BrauerKlimyk

section RacahSpeiser

/-- **The Racah–Speiser formula, in group-algebra form**: for dominant integral weights `lam`,
`mu`, and `nu`, the tensor multiplicity `c^nu_{lam mu}` of `L(nu)` in `L(lam) ⊗ L(mu)` is the
coefficient at `nu` of `ch L(mu) · N(lam)`.

This is the Brauer–Klimyk formula
`TauCeti.isotypicMultiplicity_tensor_eq_coeff_formalCharacter_mul_weylNumerator` for
`M = L(mu)`. -/
theorem tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsDominantIntegral b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
    (tensorMultiplicity b lam mu nu : ℤ) =
      (formalCharacter K H (irreducibleQuotient b mu) *
        weylNumerator (IsKilling.rootSystem H) b lam).coeff nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  rw [tensorMultiplicity_def]
  exact isotypicMultiplicity_tensor_eq_coeff_formalCharacter_mul_weylNumerator b hlam hnu

/-- **The Racah–Speiser formula, expanded over the Weyl group**: for dominant integral weights
`lam`, `mu`, and `nu`, `c^nu_{lam mu} = ∑_{w ∈ W} sgn(w) · [e^{nu - w ⬝ lam}] ch L(mu)`.

This is the Brauer–Klimyk formula
`TauCeti.isotypicMultiplicity_tensor_eq_sum_weylSign_mul_formalCharacter_coeff` for
`M = L(mu)`. -/
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
  rw [tensorMultiplicity_def]
  exact isotypicMultiplicity_tensor_eq_sum_weylSign_mul_formalCharacter_coeff b hlam hnu

end RacahSpeiser

end TauCeti
