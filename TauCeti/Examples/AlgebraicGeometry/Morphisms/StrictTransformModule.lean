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
is zero: `M` is `t`-power torsion, so its localization at every prime of `D(t)` vanishes, the sheaf
`M~` restricts to zero on `D(t)`, and the strict transform of a module only sees it over the
preimage of the witness
(`AlgebraicGeometry.Scheme.Hom.isZero_strictTransformModule_of_isZero_restrict`).
-/

public section

noncomputable section

open CategoryTheory Limits Polynomial AlgebraicGeometry

namespace TauCeti.StrictTransformModuleExample

universe u

variable (R : Type u) [CommRing R]

/-- The `R[t]`-module `M = R[t]/(t)`. -/
abbrev M : ModuleCat.{u} (CommRingCat.of R[X]) :=
  ModuleCat.of _ (R[X] ⧸ Ideal.span {(X : R[X])})

/-- `t` kills `M = R[t]/(t)`. -/
theorem X_smul (m : M R) : (X : R[X]) • m = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (m : R[X] ⧸ Ideal.span {(X : R[X])})
  change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ a = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sections of `M~` over any open contained in `𝔾_m = D(t)` vanish: they are families of
elements of the localizations `M_p` with `t ∉ p`, which are zero. -/
theorem subsingleton_sections {W : (Spec (CommRingCat.of R[X])).Opens}
    (hW : W ≤ PrimeSpectrum.basicOpen (X : R[X])) : Subsingleton Γ(tilde (M R), W) := by
  refine ⟨fun s t ↦ Subtype.ext (funext fun p ↦ ?_)⟩
  have : Subsingleton (LocalizedModule p.val.asIdeal.primeCompl (M R)) :=
    (IsLocalizedModule.subsingleton_iff p.val.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ _)).2
      fun m ↦ ⟨X, (PrimeSpectrum.mem_basicOpen _ _).1 (hW p.property), X_smul R m⟩
  exact Subsingleton.elim _ _

/-- `M~` restricts to zero on the preimage of `𝔾_m` under the identity of `𝔸¹`. -/
theorem isZero_restrict :
    IsZero ((tilde (M R)).restrict
      ((𝟙 (Spec (CommRingCat.of R[X]))) ⁻¹ᵁ PrimeSpectrum.basicOpen (X : R[X])).ι) := by
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext s
  simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_id,
    AddCommGrpCat.hom_zero, AddMonoidHom.id_apply, AddMonoidHom.zero_apply]
  have := subsingleton_sections R (W := Scheme.Opens.ι _ ''ᵁ V)
    ((Scheme.Hom.image_le_opensRange _ _).trans (by simp; rfl))
  rw [← Iso.hom_inv_id_apply (Scheme.Modules.restrictAppIso _ (tilde (M R)) V) s,
    Subsingleton.elim ((Scheme.Modules.restrictAppIso _ (tilde (M R)) V).hom s) 0, map_zero]

/-- **The strict transform of `R[t]/(t)` along the identity of `𝔸¹` with witness `𝔾_m` is zero.** -/
theorem isZero_strictTransformModule :
    IsZero (Scheme.Hom.strictTransformModule (𝟙 (Spec (CommRingCat.of R[X])))
      (𝟙 _) (PrimeSpectrum.basicOpen (X : R[X])) (tilde (M R))) :=
  Scheme.Hom.isZero_strictTransformModule_of_isZero_restrict _ _ _ _ (isZero_restrict R)

end TauCeti.StrictTransformModuleExample
