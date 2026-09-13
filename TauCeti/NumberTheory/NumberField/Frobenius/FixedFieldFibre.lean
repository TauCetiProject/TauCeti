/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedFieldInertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower
public import TauCeti.NumberTheory.NumberField.FixedField

/-!
# Contracting a Frobenius fibre to the fixed field

Fix `σ ∈ Gal(L/K)` and let `E = L ^ ⟨σ⟩`. Among the primes `Q` of `𝓞 L` above an unramified prime
of `𝓞 K`, those admitting `σ` as an arithmetic Frobenius are exactly the ones whose contraction to
`𝓞 E` has residue degree one over `𝓞 K` and carries a relative Frobenius restricting to `σ`; and
distinct such `Q` have distinct contractions.

Both halves are needed to count primes of `E` by counting primes of `L`. The forward direction
supplies the contraction, the converse recognises which primes of `E` arise, and injectivity makes
the two counts equal.

## Main results

* `Ideal.exists_isArithFrobAt_restrictScalars_eq`: a prime carrying `σ` has, over the fixed field,
  a relative Frobenius restricting to `σ`.
* `Ideal.isArithFrobAt_of_restrictScalars_eq`: conversely, at residue degree one such a relative
  Frobenius forces `σ` to be the absolute Frobenius.
* `Ideal.under_fixedField_injOn`: contraction to the fixed field is injective on the primes
  carrying `σ`.

## Implementation notes

Injectivity is not a counting argument: a Frobenius at `Q` fixes `Q`, so
`Ideal.eq_of_smul_eq_of_liesOver_under_fixedField` already says `Q` is the *only* prime of `𝓞 L`
above its contraction. It needs neither `L / K` Galois nor unramifiedness.

The two Frobenius statements are the two directions of Layer 8.1's second restriction law at
exponent one, through `NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open scoped NumberField Pointwise

open IntermediateField NumberField

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **A Frobenius fibre has a relative Frobenius over the fixed field.** If `σ` is an arithmetic
Frobenius at an unramified nonzero prime `Q`, then over `L ^ ⟨σ⟩` there is an arithmetic Frobenius
at `Q` whose restriction to `Gal(L/K)` is `σ` itself.

The prime below `Q` in the fixed field has residue degree one, so the tower law's exponent is one
and the restriction moves nothing. -/
theorem exists_isArithFrobAt_restrictScalars_eq (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L,
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q
        ∧ AlgEquiv.restrictScalars K τ = σ := by
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt
    (K := ↥(fixedField (Subgroup.zpowers σ))) Q hQ
  exact ⟨τ, hτ, NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hσ hτ
    (inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q hQ hσ)⟩

/-- **Recognising the fibre from the fixed field.** If the prime below `Q` in `L ^ ⟨σ⟩` has residue
degree one over `𝓞 K` and a relative Frobenius there restricts to `σ`, then `σ` is an arithmetic
Frobenius at `Q` over `𝓞 K`.

This is the converse of `exists_isArithFrobAt_restrictScalars_eq`, and the residue-degree
hypothesis is what the forward direction produces. -/
theorem isArithFrobAt_of_restrictScalars_eq (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q)
    (hf : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1)
    (hres : AlgEquiv.restrictScalars K τ = σ) :
    IsArithFrobAt (𝓞 K) σ Q := by
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt (K := K) Q hQ
  have hrestr : AlgEquiv.restrictScalars K τ = φ :=
    NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hφ hτ hf
  rwa [← hres, hrestr]

omit [IsGalois K L] in
/-- **Contraction to the fixed field is injective on a Frobenius fibre.** Distinct primes of `𝓞 L`
admitting `σ` as an arithmetic Frobenius have distinct contractions to `𝓞 (L ^ ⟨σ⟩)`.

A Frobenius at `Q` fixes `Q`, and `Ideal.eq_of_smul_eq_of_liesOver_under_fixedField` then says `Q`
is the only prime of `𝓞 L` above its contraction. Neither unramifiedness nor `L / K` Galois is
needed. -/
theorem under_fixedField_injOn (𝔭 : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    Set.InjOn (fun Q : Ideal (𝓞 L) ↦ Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))))
      {Q : Ideal (𝓞 L) | ∃ (_ : Q.IsPrime) (_ : Q.LiesOver 𝔭) (_ : Q ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ Q} := by
  rintro Q₁ ⟨_, _, -, h₁⟩ Q₂ ⟨_, _, -, h₂⟩ hEq
  have hstab : σ • Q₁ = Q₁ := h₁.mem_stabilizer
  have : Q₂.LiesOver (Q₁.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))) := ⟨hEq⟩
  exact (eq_of_smul_eq_of_liesOver_under_fixedField hstab Q₂).symm

end Ideal
