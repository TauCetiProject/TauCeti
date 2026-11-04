/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.RingHom.Flat

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Flatness of variable renaming in multivariate polynomial rings

For any injective map `f : τ → σ` between variable index types over a commutative ring `R`,
splitting `σ` into `Set.range f` and its complement identifies `MvPolynomial σ R` with a
multivariate polynomial algebra over `MvPolynomial τ R`. Since every polynomial algebra is free as
a module over its base ring, renaming variables along `f` defines a flat ring homomorphism.

## Main results

* `MvPolynomial.flat_rename`: for any injective map `f : τ → σ`, renaming variables gives a flat
  ring homomorphism `MvPolynomial τ R →+* MvPolynomial σ R`.
-/

public section

namespace MvPolynomial

/-- Renaming variables along an injective map `f : τ → σ` defines a flat ring homomorphism
`MvPolynomial τ R →+* MvPolynomial σ R`. -/
theorem flat_rename {R σ τ : Type*} [CommRing R] {f : τ → σ} (hf : Function.Injective f) :
    (MvPolynomial.rename f : MvPolynomial τ R →ₐ[R] MvPolynomial σ R).toRingHom.Flat := by
  -- Split `σ` into `Set.range f` and its complement to realize `MvPolynomial σ R` as a polynomial
  -- algebra over `MvPolynomial τ R`, which is free and hence flat.
  classical
  let S₁ := {x : σ // x ∉ Set.range f}
  let e : S₁ ⊕ τ ≃ σ :=
    ((Equiv.refl S₁).sumCongr (Equiv.ofInjective f hf)).trans
      ((Equiv.sumComm S₁ _).trans (Equiv.sumCompl (· ∈ Set.range f)))
  let ψ : MvPolynomial S₁ (MvPolynomial τ R) ≃ₐ[R] MvPolynomial σ R :=
    (MvPolynomial.sumAlgEquiv R S₁ τ).symm.trans (MvPolynomial.renameEquiv R e)
  let φ₀ : MvPolynomial τ R →ₐ[R] MvPolynomial S₁ (MvPolynomial τ R) :=
    IsScalarTower.toAlgHom R (MvPolynomial τ R) (MvPolynomial S₁ (MvPolynomial τ R))
  have hφ₀ : φ₀.toRingHom.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have heq : MvPolynomial.rename f = ψ.toAlgHom.comp φ₀ :=
    MvPolynomial.algHom_ext fun t ↦ by
      simp [ψ, φ₀, e, MvPolynomial.algebraMap_eq]
      rfl
  rw [heq]
  exact hφ₀.comp (RingHom.Flat.of_bijective ψ.bijective)

end MvPolynomial
