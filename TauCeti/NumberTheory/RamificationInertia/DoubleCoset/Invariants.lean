/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup

/-!
# The local invariants of the primes in the double coset law

Let `M / K` be a finite Galois extension of number fields with group `G`, let `H` be a subgroup of
`G` with fixed field `E = M ^ H`, and let `Q` be a prime of `𝓞 M` above a prime `p` of `𝓞 K`, with
decomposition group `D` and inertia group `I`. The double coset law
(`Ideal.doubleCosetQuotientEquivPrimesOver`) indexes the primes of `𝓞 E` above `p` by
`H \ G / D`, the class of `σ` corresponding to `𝔮_σ = σ Q ∩ 𝓞 E`. This file reads the
ramification index and the residue degree of `𝔮_σ` over `p` off the double coset:

* `e(𝔮_σ / p) · f(𝔮_σ / p) = [σDσ⁻¹ : H ∩ σDσ⁻¹] = |HσD| / |H|`;
* `e(𝔮_σ / p) = [σIσ⁻¹ : H ∩ σIσ⁻¹]`.

The conjugate `σDσ⁻¹` is written `MulAut.conj σ • D`. The first index formula is the
decomposition-group index formula
`Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex` at the translate `σ Q`, whose
decomposition group is `σDσ⁻¹`; the second form of it is the double-coset size formula
`TauCeti.card_doubleCoset_eq_card_mul_relIndex`. In that second form the local degree of the
prime attached to a double coset depends on the double coset alone, not on a representative
(`Ideal.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_mul_card`).

The numbers `|HσD| / |H|` add up, over `H \ G / D`, to the index `[G : H] = [E : K]`
(`TauCeti.sum_card_quotToDoubleCoset_div_card_eq_index`). Read through the formulas here, that
count is the fundamental identity `Σ e f = [E : K]` over the primes of `𝓞 E` above `p`, which
Mathlib proves directly as `Ideal.sum_ramification_inertia`.

Only the product `e · f` and the ramification index `e` are read here as subgroup indices. The
residue degree is not obtained by the same recipe with `D/I` in place of `D`: the image of
`H ∩ σDσ⁻¹` in `D/I` need not be the intersection of the image of `H` with `σ(D/I)σ⁻¹`.

Finally the bijection is compatible with the action of `G` on the primes above `p`: replacing `Q`
by `τ Q` replaces the class of `σ` by the class of `σ τ`
(`Ideal.doubleCosetQuotientEquivPrimesOver_smul_mk`).

## Main results

* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_smul_eq_relIndex`:
  `e(𝔮_σ) f(𝔮_σ) = [σDσ⁻¹ : H ∩ σDσ⁻¹]`.
* `Ideal.ramificationIdx_under_fixedField_smul_eq_relIndex`: `e(𝔮_σ) = [σIσ⁻¹ : H ∩ σIσ⁻¹]`.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_smul_mul_card`:
  `e(𝔮_σ) f(𝔮_σ) · |H| = |HσD|`.
* `Ideal.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_mul_card` and
  `Ideal.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_eq_card_div`: the same
  formula for the prime attached to a double coset, read on the double coset itself.
* `Ideal.doubleCosetQuotientEquivPrimesOver_smul_mk`: compatibility with the action of `G`.

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

/-- **The local degree of `σ Q ∩ 𝓞 (M ^ H)` is an index of decomposition groups**:
`e · f = [σDσ⁻¹ : H ∩ σDσ⁻¹]`, where `D` is the decomposition group of `Q`. -/
theorem ramificationIdx_mul_inertiaDeg_under_fixedField_smul_eq_relIndex (Q : Ideal (𝓞 M))
    [Q.IsPrime] (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    ((σ • Q).under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
        * ((σ • Q).under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) =
      H.relIndex (MulAut.conj σ • stabilizer (M ≃ₐ[K] M) Q) := by
  rw [ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex,
    stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    TauCeti.map_conj_eq_conj_smul]

/-- **The ramification index of `σ Q ∩ 𝓞 (M ^ H)` is an index of inertia groups**:
`e = [σIσ⁻¹ : H ∩ σIσ⁻¹]`, where `I` is the inertia group of `Q`. -/
theorem ramificationIdx_under_fixedField_smul_eq_relIndex (Q : Ideal (𝓞 M)) [Q.IsPrime]
    (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    ((σ • Q).under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K) =
      H.relIndex (MulAut.conj σ • Q.inertia (M ≃ₐ[K] M)) := by
  rw [ramificationIdx_under_fixedField_eq_relIndex, inertia_smul, TauCeti.map_conj_eq_conj_smul]

/-- **The local degree of `σ Q ∩ 𝓞 (M ^ H)` counts the double coset `HσD`**:
`e · f · |H| = |HσD|`, where `D` is the decomposition group of `Q`. -/
theorem ramificationIdx_mul_inertiaDeg_under_fixedField_smul_mul_card (Q : Ideal (𝓞 M))
    [Q.IsPrime] (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    ((σ • Q).under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
        * ((σ • Q).under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) * Nat.card H =
      Nat.card (DoubleCoset.doubleCoset σ (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M))) := by
  rw [ramificationIdx_mul_inertiaDeg_under_fixedField_smul_eq_relIndex,
    TauCeti.card_doubleCoset_eq_card_mul_relIndex, mul_comm]

variable (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
  (H : Subgroup (M ≃ₐ[K] M))

/-- **The local degree of the prime attached to a double coset counts that double coset.** For
`q` in `H \ G / D`, the ramification index times the residue degree over `p` of the prime of
`𝓞 (M ^ H)` that the double coset law attaches to `q`, multiplied by `|H|`, is the number of
elements of `q`. -/
theorem ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_mul_card
    (q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
      (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M))) :
    (doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
        * (doubleCosetQuotientEquivPrimesOver p Q H q :
            Ideal (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) * Nat.card H =
      Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer (M ≃ₐ[K] M) Q) q) := by
  conv_lhs => rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOver_mk]
  rw [ramificationIdx_mul_inertiaDeg_under_fixedField_smul_mul_card,
    DoubleCoset.quotToDoubleCoset]

/-- **The double-coset formula for the local degree**: the prime of `𝓞 (M ^ H)` above `p`
attached to a double coset `q` in `H \ G / D` has `e · f = |q| / |H|`. -/
theorem ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_eq_card_div
    (q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
      (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M))) :
    (doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K)
        * (doubleCosetQuotientEquivPrimesOver p Q H q :
            Ideal (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) =
      Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer (M ≃ₐ[K] M) Q) q) / Nat.card H := by
  rw [← ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_mul_card p Q H q,
    Nat.mul_div_cancel _ Nat.card_pos]

/-- **The double coset law is compatible with the action of `G`.** Indexing the primes of
`𝓞 (M ^ H)` above `p` through the translate `τ Q` instead of `Q` sends the class of `σ` to the
prime that the indexing through `Q` attaches to the class of `σ τ`. -/
theorem doubleCosetQuotientEquivPrimesOver_smul_mk (τ σ : M ≃ₐ[K] M) :
    doubleCosetQuotientEquivPrimesOver p (τ • Q) H (DoubleCoset.mk H _ σ) =
      doubleCosetQuotientEquivPrimesOver p Q H (DoubleCoset.mk H _ (σ * τ)) :=
  Subtype.ext <| by simp only [doubleCosetQuotientEquivPrimesOver_mk, mul_smul]

end Ideal
