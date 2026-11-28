/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AlgebraicModularForm
public import TauCeti.RepresentationTheory.Coinduced.Pairing

/-!
# The invariant pairing of algebraic modular forms

Let `V = (J, x)` be a hermitian space with an adelic frame over a CM field `E`, `G_f` the finite
adelic unitary group, `Γ_{V,f} ⊂ G_f` the finite rational points and `K₀ = G_f ∩ GL_n(Ô)`. Let `ρ`
be a representation of `G_∞(s)` on a module `W` over a commutative star ring `R` that is a
`ℚ`-vector space, and `B` a sesquilinear form on `W` invariant under the coefficient
representation `γ ↦ ρ((x⁻¹ γ x)_∞)` of `U(J)(E⁺)`. When `(Γ_{V,f}, K₀)` has finite type, the
**invariant pairing** of algebraic modular forms of coefficients `ρ` is

  `⟨φ, φ'⟩_B = I_{Γ_{V,f},K₀}(g ↦ B (φ g) (φ' g))`,

the class integral of `TauCeti.classIntegral`, which is the integral over `Γ_{V,f} \ G_f` for the
Haar measure giving `K₀` mass one. It is sesquilinear, invariant under right translation by `G_f`,
and hermitian when `B` is. It is the case of `Representation.coindPairing` where the coinduced
representation is that of the algebraic modular forms and `K = K₀`.

For a definite space, `(Γ_{V,f}, K₀)` has finite type by reduction theory, and for `ρ` the
representation of a weight `(κ, e)` with its invariant inner product this is Gross's positive
definite pairing of algebraic modular forms; positivity is not treated here.

## Main definitions

* `TauCeti.FramedHermitianSpace.algebraicModularFormPairing V ρ B hK hB`: the pairing
  `⟨φ, φ'⟩_B`.

## Main results

* `TauCeti.FramedHermitianSpace.algebraicModularFormPairing_apply`: its value is the class
  integral of `g ↦ B (φ g) (φ' g)`.
* `TauCeti.FramedHermitianSpace.isInvariantSesqForm_algebraicModularFormPairing`: it is invariant
  under right translation by `G_f`.
* `TauCeti.FramedHermitianSpace.isSymm_algebraicModularFormPairing`: it is hermitian when `B` is.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.

## Attribution

The pairing follows `New.smoothPairing`, `New.smoothPairing_apply` and
`New.smoothPairing_formTranslation` in `src/Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section
noncomputable section

open NumberField Representation

namespace TauCeti

namespace FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ} (V : FramedHermitianSpace E s)
  {R W : Type*} [CommRing R] [StarRing R] [Module ℚ R] [AddCommMonoid W] [Module R W]
  (ρ : Representation R (infiniteAdelicUnitaryGroup E s) W) (B : W →ₗ⋆[R] W →ₗ[R] R)

/-- The **invariant pairing** `⟨φ, φ'⟩_B = I_{Γ_{V,f},K₀}(g ↦ B (φ g) (φ' g))` of algebraic modular
forms of coefficients `ρ`, for `(Γ_{V,f}, K₀)` of finite type and `B` a sesquilinear form invariant
under the coefficient representation (`algebraicModularFormPairing_apply`). It is
conjugate-linear in `φ` and linear in `φ'`. -/
def algebraicModularFormPairing
    (hK : HasFiniteType V.finiteRationalPoints (integralAdelicUnitaryGroup E ι))
    (hB : IsInvariantSesqForm (V.coefficientRep ρ) B) :
    (V.algebraicModularForms ρ).toSubmodule →ₗ⋆[R]
      (V.algebraicModularForms ρ).toSubmodule →ₗ[R] R :=
  coindPairing B (V.algebraicModularForms ρ) (V.algebraicModularForms_def ρ).le
    (V.finiteRationalPoints_def ▸ hK) hB

variable {V ρ B}

/-- `⟨φ, φ'⟩_B = I_{Γ_{V,f},K₀}(g ↦ B (φ g) (φ' g))`. -/
@[simp]
theorem algebraicModularFormPairing_apply
    (hK : HasFiniteType V.finiteRationalPoints (integralAdelicUnitaryGroup E ι))
    (hB : IsInvariantSesqForm (V.coefficientRep ρ) B)
    (φ φ' : (V.algebraicModularForms ρ).toSubmodule) :
    V.algebraicModularFormPairing ρ B hK hB φ φ' =
      classIntegral V.finiteRationalPoints (integralAdelicUnitaryGroup E ι) fun g ↦
        B ((φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)).val g)
          ((φ' : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)).val g) := by
  rw [algebraicModularFormPairing, coindPairing_apply, finiteRationalPoints_def]

/-- **The pairing is invariant under right translation by `G_f`**:
`⟨φ(· u), φ'(· u)⟩_B = ⟨φ, φ'⟩_B` for every `u ∈ G_f`. -/
theorem isInvariantSesqForm_algebraicModularFormPairing
    (hK : HasFiniteType V.finiteRationalPoints (integralAdelicUnitaryGroup E ι))
    (hB : IsInvariantSesqForm (V.coefficientRep ρ) B) :
    IsInvariantSesqForm (V.algebraicModularForms ρ).toRepresentation
      (V.algebraicModularFormPairing ρ B hK hB) :=
  isInvariantSesqForm_coindPairing _ _ _ hB

/-- **The pairing is hermitian when `B` is**: `star ⟨φ, φ'⟩_B = ⟨φ', φ⟩_B`. -/
theorem isSymm_algebraicModularFormPairing
    (hK : HasFiniteType V.finiteRationalPoints (integralAdelicUnitaryGroup E ι))
    (hB : IsInvariantSesqForm (V.coefficientRep ρ) B) (hBs : B.IsSymm) :
    (V.algebraicModularFormPairing ρ B hK hB).IsSymm :=
  isSymm_coindPairing _ _ _ hB hBs

end FramedHermitianSpace

end TauCeti
