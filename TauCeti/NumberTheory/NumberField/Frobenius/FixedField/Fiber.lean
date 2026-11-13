/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-!
# Contracting a Frobenius fiber to the fixed field

Fix `σ ∈ Gal(L/K)` and let `E = L ^ ⟨σ⟩`. If `σ` is an arithmetic Frobenius at a prime `Q` of
`𝓞 L` unramified over `𝓞 K`, then over `E` there is a relative Frobenius at `Q` restricting to
`σ`. That is the direction a fixed-field count needs from this file.

The converse — recovering `σ` from a relative Frobenius at residue degree one — holds for any
intermediate field, so it lives in `Frobenius/Tower.lean` as
`NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one`. Injectivity of contraction comes
from `Ideal.eq_of_smul_eq_of_liesOver_under_fixedField`.

## Main results

* `Ideal.exists_isArithFrobAt_and_restrictScalars_eq`: a prime carrying `σ` has, over the
  fixed field, a relative Frobenius restricting to `σ`.
* `Ideal.inertiaDeg_under_eq_one_and_isArithFrobAt_fixedField`: a relative Frobenius `τ` over the
  fixed field restricting to a Frobenius over `K` gives residue degree one below and a relative
  Frobenius.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open scoped NumberField Pointwise

open IntermediateField NumberField

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **A Frobenius fiber has a relative Frobenius over the fixed field.** If `σ` is an arithmetic
Frobenius at an unramified prime `Q`, then over `L ^ ⟨σ⟩` there is an arithmetic Frobenius at `Q`
whose restriction to `Gal(L/K)` is `σ` itself. -/
theorem exists_isArithFrobAt_and_restrictScalars_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L,
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q
        ∧ AlgEquiv.restrictScalars K τ = σ := by
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt
    (K := ↥(fixedField (Subgroup.zpowers σ))) Q hσ.ne_bot
  exact ⟨τ, hτ, NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hσ hτ
    (inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q hσ)⟩

/-- Below a prime `Q` of `L` unramified over `K` at which `τ`, read over `K`, is an arithmetic
Frobenius lies a prime of `E = L ^ ⟨σ⟩` of residue degree one over `K`, and `τ` is an arithmetic
Frobenius at `Q` over `E`. -/
theorem inertiaDeg_under_eq_one_and_isArithFrobAt_fixedField (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L)
    (τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L)
    (hQ : IsArithFrobAt (𝓞 K) (AlgEquiv.restrictScalars K τ) Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 ∧
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q := by
  have hdeg := (inertiaDeg_under_fixedField_eq_one_iff Q _ hQ).2
    (σ.restrictScalars_mem_zpowers τ)
  exact ⟨hdeg, (NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg hQ τ).mpr
    (by rw [hdeg, pow_one])⟩

end Ideal
