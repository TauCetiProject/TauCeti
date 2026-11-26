/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Module

/-!
# The strict transform of `R[t]/(t)` with witness `𝔾_m`

On `𝔸¹ = Spec R[t]`, take the identity modification with witness `U = 𝔾_m = D(t)` and the module
`M = R[t]/(t)`. The strict transform of `M` (`AlgebraicGeometry.Scheme.Hom.strictTransformModule`)
is zero: `t` kills `M`, so the sheaf `M~` restricts to zero on `D(t)`
(`TauCeti.AlgebraicGeometry.isZero_tilde_restrict_of_le_basicOpen_of_smul_eq_zero`), and the
strict transform of a module only sees it over the preimage of the witness
(`AlgebraicGeometry.Scheme.Hom.isZero_strictTransformModule_of_isZero_restrict`).
-/

public section

noncomputable section

open CategoryTheory Limits Polynomial AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti.StrictTransformModuleExample

universe u

variable (R : Type u) [CommRing R]

/-- The `R[t]`-module `M = R[t]/(t)`. -/
abbrev M : ModuleCat.{u} (CommRingCat.of R[X]) :=
  ModuleCat.of _ (R[X] ⧸ Ideal.span {(X : R[X])})

/-- `t` kills `M = R[t]/(t)`. -/
theorem X_smul (m : M R) : (X : R[X]) • m = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ (m : R[X] ⧸ Ideal.span {(X : R[X])})
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- **The strict transform of `R[t]/(t)` along the identity of `𝔸¹` with witness `𝔾_m` is zero.** -/
theorem isZero_strictTransformModule :
    IsZero (Scheme.Hom.strictTransformModule (𝟙 (Spec (CommRingCat.of R[X])))
      (𝟙 _) (PrimeSpectrum.basicOpen (X : R[X])) (tilde (M R))) :=
  Scheme.Hom.isZero_strictTransformModule_of_isZero_restrict _ _ _ _
    (isZero_tilde_restrict_of_le_basicOpen_of_smul_eq_zero X (X_smul R)
      (Scheme.Hom.id_preimage _).le)

end TauCeti.StrictTransformModuleExample
