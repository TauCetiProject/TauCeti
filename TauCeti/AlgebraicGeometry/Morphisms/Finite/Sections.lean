/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs

/-!
# Recovering finite algebras from sections away from the closed fibre

Let `A` be a Noetherian local ring and `B` a finite `A`-algebra. If `B` has depth at least two
at each maximal ideal, the sections of `Spec B` away from the closed fibre recover `B`. In
particular, the spectrum of those sections is canonically isomorphic to `Spec B`. This is the
affine form of the reconstruction of a finite scheme over a local spectrum from its puncture.
A finite scheme over an affine base is affine, so the result applies to its coordinate algebra.

The depth assumption is imposed on the local rings of `B`, not on `B` as an `A`-module. No
normality, reducedness, flatness or torsion-freeness assumption is needed. The argument uses the
Hartogs theorem for the structure sheaf: every point omitted from the inverse image of the
punctured spectrum is closed, by integrality.

## References

* [Stacks Project, Lemma 58.20.1](https://stacks.math.columbia.edu/tag/0BM8).
* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

variable {A B : CommRingCat.{u}} [IsNoetherianRing A] [Algebra A B] [Module.Finite A B]

namespace AlgebraicGeometry.Scheme.Opens

/-- Let `B` be finite over a Noetherian ring `A`. If the complement of `U ⊆ Spec A` consists
of closed points, and `B` has depth at least two at every maximal ideal, its sections over the
inverse image of `U` recover `B`. -/
theorem algebraMap_preimage_bijective_of_finite_of_two_le_depth (U : (Spec A).Opens)
    (hU : ∀ p : PrimeSpectrum A, p ∉ U → p.asIdeal.IsMaximal)
    (hdepth : ∀ (q : Ideal B) [q.IsMaximal],
      2 ≤ depth (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))) :
    Function.Bijective
      (algebraMap B Γ(Spec B, (Spec.algebraMap A B) ⁻¹ᵁ U)) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  apply Scheme.Opens.algebraMap_bijective_of_two_le_depth
  intro q hq
  have : q.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    q.asIdeal (hU (PrimeSpectrum.comap (algebraMap A B) q) hq)
  exact hdepth q.asIdeal

end AlgebraicGeometry.Scheme.Opens

namespace TauCeti.AlgebraicGeometry

/-- **Reconstruction from the puncture.** For a finite algebra `B` over a Noetherian local ring
`A`, if every local ring of `B` at a maximal ideal has depth at least two, the canonical map
from the spectrum of the sections away from the closed fibre to `Spec B` is an isomorphism.
This is Stacks, Lemma 58.20.1, for the affine presentation of a finite scheme over `Spec A`. -/
@[stacks 0BM8 "affine presentation"]
theorem spec_sections_of_depth [IsLocalRing A]
    (hdepth : ∀ (q : Ideal B) [q.IsMaximal],
      2 ≤ depth (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))) :
    let U : (Spec A).Opens :=
      ⟨{closedPoint A}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩
    IsIso (Spec.algebraMap B Γ(Spec B, (Spec.algebraMap A B) ⁻¹ᵁ U)) := by
  dsimp only
  have hbij := Scheme.Opens.algebraMap_preimage_bijective_of_finite_of_two_le_depth
    (B := B) ⟨{closedPoint A}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩
    (fun p hp ↦ by
      have hp : p = closedPoint A := Classical.not_not.mp hp
      simpa [hp, closedPoint] using maximalIdeal.isMaximal A) hdepth
  have : IsIso (CommRingCat.ofHom
      (algebraMap B Γ(Spec B, (Spec.algebraMap A B) ⁻¹ᵁ
        ⟨{closedPoint A}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

end TauCeti.AlgebraicGeometry
