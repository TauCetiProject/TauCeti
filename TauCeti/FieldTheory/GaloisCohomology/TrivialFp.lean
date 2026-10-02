/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Zero
public import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# Absolute Galois cohomology with trivial `ZMod p` coefficients

Zeroth continuous cohomology of the absolute Galois group with trivial coefficients has
dimension one. The canonical coefficient identification is
`TauCeti.cohomFpZeroLinearEquiv p (Field.absoluteGaloisGroup K)`, and finite generation is
provided by the corresponding `Module.Finite` instance. At prime `p`, this is the
finite-dimensional `𝔽_p`-vector space `H⁰(G_K, 𝔽_p)`.

When `K` contains a primitive `n`th root of unity, the coefficient dictionary of
`ClassFieldTheory.muNRep` identifies the cardinality of `H¹(G_K, ℤ/n)` with the number of
`n`th-power classes. This works for arbitrary nonzero `n`, not just primes, and makes no
finiteness assumption. It is useful for extracting cohomology dimensions from arithmetic
power-class counts.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (K : Type u) [Field K]

/-- Zeroth absolute Galois cohomology with trivial `ZMod p` coefficients has dimension one. -/
theorem finrank_cohomFp_zero_absoluteGaloisGroup :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 0) = 1 :=
  (cohomFpZeroLinearEquiv p (Field.absoluteGaloisGroup K)).finrank_eq.trans
    (CommSemiring.finrank_self (ZMod p))

attribute [local instance] TopRep.distribMulAction continuousSMul_trivialFp

open ContCohomology ClassFieldTheory

/-- If `K` contains a primitive `n`th root, the cardinality of `H¹(G_K, ℤ/n)` equals the
number of `n`th-power classes. This equality of `Nat.card` also holds when both groups are
infinite; it does not assert finiteness. -/
theorem natCard_cohomFp_one_absoluteGaloisGroup_of_isPrimitiveRoot [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Nat.card (cohomFp p (Field.absoluteGaloisGroup K) 1) =
      Nat.card (powerClassQuotient Kˣ p) := by
  have := hζ.neZero'
  let ζu := Units.mk0 ζ (hζ.ne_zero (NeZero.ne p))
  have hζu : IsPrimitiveRoot
      (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom ζu) p :=
    (IsPrimitiveRoot.coe_units_iff.mp hζ).map_of_injective
      (Units.map_injective (algebraMap K (SeparableClosure K)).injective)
  let e : (muNRep p K).V ≃+ ZMod p :=
    (kummerCoeffEquivMuNRep p K).symm.trans hζu.zmodEquivRootsOfUnity.symm
  let h1 := explicitMap1Equiv (Field.absoluteGaloisGroup K) (muNRep p K).V
    (Field.absoluteGaloisGroup K) (trivialFp p (Field.absoluteGaloisGroup K)).V
    (ContinuousMulEquiv.refl _) (e.trans (trivialFpEquiv p _).symm.toAddEquiv)
    continuous_of_discreteTopology continuous_of_discreteTopology (fun g x ↦ by
      rw [TopRep.distribMulAction_smul, muNRep_ρ_apply_eq_self hζ, smul_trivialFp_V])
  let E := (kummerEquiv K (NeZero.ne (p : K)).isUnit).trans
    ((muNRep p K).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.trans
      (h1.trans (trivialFp p _).explicitH1AddEquivContinuousCohomologyOfDiscrete))
  exact (Nat.card_congr E.toEquiv).symm.trans (Nat.card_congr Additive.toMul)

end TauCeti
