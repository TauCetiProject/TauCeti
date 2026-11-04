/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Extension
import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus
import TauCeti.RingTheory.CohenMacaulay.Normal

/-!
# Finite algebras étale over the punctured spectrum, when purity holds

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, and let `B` be a finite `A`-algebra
which is étale over `A` at every prime not lying over `𝔪`. Restricting `Spec B ⟶ Spec A` to the
punctured spectrum `U = Spec A ∖ {𝔪}` gives a finite étale cover `V` of `U`. If purity holds for
`A` (`TauCeti.IsLocalRing.PurityHolds A`), then `V` extends to a finite étale scheme over
`Spec A`, so its ring of sections is finite étale over `A` when `A` has depth at least two
(Stacks, Lemma 58.20.2 (0BLK)). When `B` is recovered from its sections over the preimage of `U`,
this shows that `B` itself is étale over `A`.

For a finite torsion-free algebra `B` whose localizations at maximal ideals are normal domains,
over a Noetherian normal local domain `A` of dimension at least two, both the depth bound and the
recovery of `B` from its sections hold (Stacks, Lemma 58.20.3 (0BM9), with the torsion-freeness
hypothesis that its statement omits). So purity for the punctured spectrum of `A` implies purity
for finite normal `A`-algebras: this is how part (2) of Stacks, Lemma 58.21.3 (0BMA), purity for
regular local rings in its algebraic form, follows from part (1), purity of the punctured
spectrum.

## Main results

* `TauCeti.Algebra.etale_of_purityHolds_of_bijective`: over a Noetherian local ring of depth at
  least two for which purity holds, a finite algebra is étale, provided it is étale at every prime
  not lying over the closed point and is recovered from its sections over the preimage of the
  punctured spectrum.
* `TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds`: over a Noetherian normal local domain of
  dimension at least two for which purity holds, a finite torsion-free algebra with normal
  localizations at maximal ideals, étale at every prime not lying over the closed point, is
  étale.

## References

* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA).
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
  [IsNoetherianRing A] [Module.Finite A B]

/-- Let `A` be a Noetherian local ring of depth at least two for which purity holds, and let `B`
be a finite `A`-algebra which is étale over `A` at every prime not lying over the maximal ideal.
If restriction of sections from `Spec B` to the preimage of the punctured spectrum of `A` is
bijective, then `B` is étale over `A`. -/
theorem etale_of_purityHolds_of_bijective (hpurity : IsLocalRing.PurityHolds A)
    (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (hsections : Function.Bijective (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ
      IsLocalRing.puncturedSpectrum A).ι.appTop)
    (hetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  let U := IsLocalRing.puncturedSpectrum A
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let W := g ⁻¹ᵁ U
  have : IsFinite g := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr ‹_›)
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- Every point of `Spec B` over the punctured spectrum has an open neighbourhood on which
  -- `Spec B ⟶ Spec A` is étale, so the restriction `V` of `Spec B` to the punctured spectrum is
  -- finite étale over it.
  have : Etale (g ∣_ U) := (g.etale_morphismRestrict_iff U).mpr <|
    Set.disjoint_left.mpr fun (q : PrimeSpectrum B) hq hne ↦
      Scheme.Hom.mem_nonEtaleLocus_iff.mp hne <| (Scheme.Hom.etaleAt_spec_iff q).mpr <|
        hetale q.asIdeal fun he ↦
          (IsLocalRing.mem_puncturedSpectrum_iff A (g q)).mp hq (PrimeSpectrum.ext he)
  let V := FiniteEtaleScheme.ofHom (g ∣_ U)
  -- By purity `V` extends across the closed point, so its sections are finite étale over `A`.
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ U.ι).appTop
  have hφ : φ.hom.Finite ∧ φ.hom.Etale :=
    (IsLocalRing.extends_iff_sections_finiteEtale A hdepth V).mp
      ((IsLocalRing.purityHolds_iff A).mp hpurity V)
  -- The sections of `V` are those of `Spec B` over `W`, which recover `B`.
  let e := (Over.forget U.toScheme).mapIso (eqToIso (FiniteEtaleScheme.ofHom_obj (g ∣_ U)))
  have he : e.hom ≫ g ∣_ U = V.obj.hom :=
    Over.w (eqToHom (FiniteEtaleScheme.ofHom_obj (g ∣_ U)))
  have : IsIso W.ι.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hsections
  have : IsIso e.hom.appTop := Scheme.Γ.map_isIso e.hom.op
  have hcomp : φ = CommRingCat.ofHom (algebraMap A B) ≫
      (Scheme.ΓSpecIso (.of B)).inv ≫ W.ι.appTop ≫ e.hom.appTop := by
    simp only [φ, ← he, Category.assoc, morphismRestrict_ι, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc, g, W]
  rw [← RingHom.etale_algebraMap]
  refine (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom (algebraMap A B))
    ((Scheme.ΓSpecIso (.of B)).inv ≫ W.ι.appTop ≫ e.hom.appTop)).mp ?_
  rw [← CommRingCat.hom_comp, ← hcomp]
  exact hφ.2

/-- **Purity for finite normal algebras from purity of the punctured spectrum.** Let `A` be a
Noetherian normal local domain of dimension at least two for which purity holds: every finite
étale cover of its punctured spectrum extends to a finite étale scheme over `Spec A`. Then a finite
torsion-free `A`-algebra whose localizations at maximal ideals are normal domains, and which is
étale over `A` at every prime not lying over the maximal ideal, is étale over `A`. -/
@[stacks 0BMA "(1) implies (2), with B torsion free over A"]
theorem etale_of_finiteNormal_of_purityHolds [IsDomain A] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A B] (hpurity : IsLocalRing.PurityHolds A)
    (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  let W := Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ IsLocalRing.puncturedSpectrum A
  refine etale_of_purityHolds_of_bijective hpurity (two_le_depth_of_isIntegrallyClosed hdim)
    ?_ hetale
  rw [Scheme.Opens.ι_appTop]
  refine AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed hdim hnormal
    (W.ι ''ᵁ ⊤) fun p hp ↦ ?_
  rw [Scheme.Opens.ι_image_top]
  exact (IsLocalRing.mem_puncturedSpectrum_iff A _).mpr fun he ↦
    hp (congrArg PrimeSpectrum.asIdeal he)

end TauCeti.Algebra
