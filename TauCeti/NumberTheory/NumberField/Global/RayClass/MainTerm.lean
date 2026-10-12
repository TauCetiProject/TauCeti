/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The main term of the ray class ideal count

This file defines the main term of the ray class ideal count and proves it positive: the number
of integral ideals of a fixed ray class with absolute norm at most `x` is this coefficient times
`x`, up to a power-saving error; this is
`TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`.

The coefficient is the Dedekind-zeta residue divided by the order of the ray class group, times
one correction factor `1 - (N 𝔭)⁻¹` for each prime `𝔭` in the support of the modulus.  The Euler
factor of `ζ_K` at `𝔭` is `(1 - N 𝔭 ^ (-s))⁻¹`, so deleting `𝔭` from the Euler product multiplies
`ζ_K s` by its reciprocal `1 - N 𝔭 ^ (-s)`; the factor above is that reciprocal at `s = 1`.  The
intended count runs over the ideals prime to the finite part of the modulus, which is what makes
those corrections the right ones.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm`: the coefficient.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq`: the coefficient written out.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_one`: at the trivial modulus it is the
  Dedekind-zeta residue over the class number.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_pos`: it is positive.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficient intended as the main term of the ray class ideal count: the Dedekind-zeta
residue of `K`, divided by the order of the ray class group of `𝔪`, times one correction factor
`1 - (N 𝔭)⁻¹` — the reciprocal Euler factor at `s = 1` — for each prime `𝔭` in the support of
`𝔪`. -/
noncomputable def rayClassIdealMainTerm (𝔪 : Modulus K) : ℝ :=
  dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
    ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

/-- **The coefficient, written out.**  The Dedekind-zeta residue divided by the order of the ray
class group, times the correction factors at the primes dividing the finite part of the modulus. -/
theorem rayClassIdealMainTerm_eq (𝔪 : Modulus K) :
    rayClassIdealMainTerm 𝔪 = dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
      ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :=
  (rfl)

/-- **The trivial modulus gives the classical coefficient.**  Its support is empty, so the
correction product is `1`, and its ray class group is the class group; what is left is the
Dedekind-zeta residue over the class number. -/
@[simp]
theorem rayClassIdealMainTerm_one :
    rayClassIdealMainTerm (Modulus.one K) =
      dedekindZeta_residue K / (Nat.card (ClassGroup (𝓞 K)) : ℝ) := by
  rw [rayClassIdealMainTerm_eq, Modulus.support_one, Finset.prod_empty, mul_one,
    Nat.card_congr oneEquivClassGroup.toEquiv]

/-- **The main term is positive.** -/
theorem rayClassIdealMainTerm_pos (𝔪 : Modulus K) : 0 < rayClassIdealMainTerm 𝔪 := by
  rw [rayClassIdealMainTerm_eq]
  refine mul_pos (div_pos (dedekindZeta_residue_pos K) (mod_cast Nat.card_pos))
    (Finset.prod_pos fun v _ ↦ ?_)
  -- a height-one prime has absolute norm at least two, so its correction factor is positive
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast HeightOneSpectrum.one_lt_absNorm v))

end TauCeti.GlobalNumberFields
