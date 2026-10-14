/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic

/-!
# The ramification indices of the primes in the double coset law

Let `M / K` be a finite Galois extension of number fields with group `G`, let `H` be a subgroup of
`G` with fixed field `E = M ^ H`, and let `Q` be a prime of `𝓞 M` above a prime `p` of `𝓞 K`, with
decomposition group `D` and inertia group `I`. The double coset law
(`Ideal.doubleCosetQuotientEquivPrimesOver`) indexes the primes of `𝓞 E` above `p` by
`H \\ G / D`, the class of `σ` corresponding to `𝔮_σ = σ Q ∩ 𝓞 E`. This file reads the
ramification index of `𝔮_σ` over `p` off the conjugate inertia group:

`e(𝔮_σ / p) = [σIσ⁻¹ : H ∩ σIσ⁻¹]`.

The conjugate `σIσ⁻¹` is written `MulAut.conj σ • I`. The residue degree is not obtained by the
same recipe with `D/I` in place of `D`: the image of `H ∩ σDσ⁻¹` in `D/I` need not be the
intersection of the image of `H` with `σ(D/I)σ⁻¹`.

## Main results

* `Ideal.ramificationIdx_under_fixedField_smul_eq_relIndex`: `e(𝔮_σ) =
  [σIσ⁻¹ : H ∩ σIσ⁻¹]`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, page 55, where the
  double coset law is recorded and its proof left to the reader.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

/-- **The ramification index of `σ Q ∩ 𝓞 (M ^ H)` is an index of inertia groups**:
`e = [σIσ⁻¹ : H ∩ σIσ⁻¹]`, where `I` is the inertia group of `Q`. -/
theorem ramificationIdx_under_fixedField_smul_eq_relIndex (Q : Ideal (𝓞 M)) [Q.IsPrime]
    (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    ((σ • Q).under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K) =
      H.relIndex (MulAut.conj σ • Q.inertia (M ≃ₐ[K] M)) := by
  rw [ramificationIdx_under_fixedField_eq_relIndex, inertia_smul, TauCeti.map_conj_eq_conj_smul]

end Ideal
