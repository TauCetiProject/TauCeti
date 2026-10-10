/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient.Cohomology
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.DegreeTwo
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Formula

/-!
# The local Euler characteristic of an inflated representation

Let `F` be a finite extension of `ℚ_p`, `V` an open normal subgroup of `G_F` with finite quotient
`G = G_F ⧸ V`, and `A` a finite-dimensional representation of `G` over `𝔽_ℓ`, `ℓ` a prime not
dividing `#G`, inflated to `G_F` by `fdGalRepOfQuotient`. The cohomology of the inflation is
computed in degrees zero and one by `finrank_continuousCohomology_zero_fdGalRepOfQuotient` and
`finrank_continuousCohomology_one_fdGalRepOfQuotient`, and in degree two by local duality
(`finrank_continuousCohomology_two_fdGalRepOfQuotient`). Together, these turn Tate's local Euler
characteristic formula `χ_F(A) = φ_F(A)` for the inflation of `A` into an identity between
invariant dimensions of representations of the finite group `G`: if `M` is a representation of `G`
inflating to `μ_ℓ`, then `χ_F(A) = φ_F(A)` holds exactly when

```text
dim (H¹(V, 𝔽_ℓ) ⊗ A)^G = dim A^G + dim (M^∨ ⊗ A)^G + [F : ℚ_p] v_p(#A)
```

(`localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff`), where `G` acts on
`H¹(V, 𝔽_ℓ)` by conjugation (`h1ConjRepresentation`). The left side is then computed by
equivariant Kummer theory (`kummerH1ConjRepresentationEquiv`), which identifies `H¹(V, 𝔽_ℓ)` with
`M^∨ ⊗ Lˣ ⧸ (Lˣ)^ℓ` for the fixed field `L` of `V`.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff`:
  `χ_F(A) = φ_F(A)` for the inflation of `A` as an identity of invariant dimensions.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology Module

variable {F : Type} [Field F] {V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}

variable (p : ℕ) [Fact p.Prime] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **Tate's local Euler characteristic formula for an inflated representation, as an identity
of invariant dimensions.** Let `F/ℚ_p` be finite, `ℓ` a prime not dividing the index of `V`, and
`M` a representation of `G = G_F ⧸ V` inflating to `μ_ℓ`. For every finite-dimensional
representation `A` of `G` over `𝔽_ℓ`, the formula `χ_F(A) = φ_F(A)` for the inflation of `A` holds
exactly when `dim (H¹(V, 𝔽_ℓ) ⊗ A)^G = dim A^G + dim (M^∨ ⊗ A)^G + [F : ℚ_p] v_p(#A)`. -/
theorem localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (hV : V.toSubgroup.index.Coprime ℓ)
    {M : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient ℓ F V).obj M ≅ muNRep ℓ F)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ))
        ((fdGalRepOfQuotient ℓ F V).obj A) = localCardNorm p ((fdGalRepOfQuotient ℓ F V).obj A) ↔
      finrank (ZMod ℓ) (Representation.invariants
          ((h1ConjRepresentation (p := ℓ) (G := Field.absoluteGaloisGroup F)
            (N := V.toSubgroup)).tprod A.ρ)) =
        finrank (ZMod ℓ) (Representation.invariants A.ρ) +
          finrank (ZMod ℓ) (Representation.invariants
            (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) M) A)
            ((Representation.dual M.ρ).tprod A.ρ)) +
            finrank ℚ_[p] F * padicValNat p (Nat.card A) := by
  have hcard : Nat.card ((fdGalRepOfQuotient ℓ F V).obj A).V = Nat.card A := by
    rw [fdGalRepOfQuotient_obj, galRepOfQuotient_obj_V]
    -- `forget₂ (FDRep _ _) (Rep _ _)` keeps the carrier of `A`.
    rfl
  rw [localEulerCharacteristic_eq_localCardNorm_iff_finrank, hcard,
    finrank_continuousCohomology_zero_fdGalRepOfQuotient,
    finrank_continuousCohomology_one_fdGalRepOfQuotient hV,
    finrank_continuousCohomology_two_fdGalRepOfQuotient (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit
      hV e]

end TauCeti.ClassFieldTheory
