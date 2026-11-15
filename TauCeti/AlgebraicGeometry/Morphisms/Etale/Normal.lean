/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.AlgebraicGeometry.Scheme.IntegrallyClosed
public import TauCeti.RingTheory.Etale.Normal

/-!
# Normal local rings under étale morphisms

An étale morphism `f : X ⟶ Y` preserves and reflects normality of the local ring at a
chosen point: `𝒪_{Y, f x}` is an integrally closed domain if and only if `𝒪_{X, x}` is.
Neither scheme needs to be locally Noetherian or globally normal.

This pointwise form is needed when replacing a morphism by an open subscheme of an étale
base change in local purity arguments. In particular it applies to the composite of the
open inclusion with the projection to the original source, even when normality is known
only at the distinguished point.

The ascent uses the localizations of an étale map on affine sections, via
`TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under` and its
integral-closedness counterpart. Descent uses faithful flatness of a flat local map.

## References

* [Stacks Project, Proposition 41.19.7](https://stacks.math.columbia.edu/tag/025P),
  normality under étale homomorphisms of local rings.
* [Stacks Project, Lemma 58.21.4](https://stacks.math.columbia.edu/tag/0BMB),
  the étale-localization reduction in purity of the branch locus.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- An étale morphism preserves and reflects normality at a point, with normality expressed
as being an integrally closed domain. No Noetherian hypothesis is needed. -/
@[stacks 025P "pointwise scheme form, without Noetherian hypotheses"]
theorem isDomain_and_isIntegrallyClosed_stalk_iff_of_etale (f : X ⟶ Y) [Etale f] (x : X) :
    (IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x))) ↔
      (IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) := by
  constructor
  · rintro ⟨_, _⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
    have het := f.etale_appLE hU hV hVU
    algebraize [(f.appLE U V hVU).hom]
    set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    have hqp : (⟨q.under Γ(Y, U), inferInstance⟩ : PrimeSpectrum Γ(Y, U)) =
        hU.primeIdealOf ⟨f x, hVU hxV⟩ :=
      IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV
    have hY : IsDomain (Localization.AtPrime (q.under Γ(Y, U))) ∧
        IsIntegrallyClosed (Localization.AtPrime (q.under Γ(Y, U))) :=
      (congrArg (fun p : PrimeSpectrum Γ(Y, U) ↦
        IsDomain (Localization.AtPrime p.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) hqp).mpr <|
        (hU.isDomain_and_isIntegrallyClosed_stalk_iff ⟨f x, hVU hxV⟩).mp
          ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hY
    have := TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under Γ(Y, U) q
    have := TauCeti.Algebra.Etale.isIntegrallyClosed_localization_atPrime_of_localization_under
      Γ(Y, U) q
    exact (hV.isDomain_and_isIntegrallyClosed_stalk_iff ⟨x, hxV⟩).mpr
      ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, _⟩
    let := (f.stalkMap x).hom.toAlgebra
    have := f.isLocalHom_stalkMap_toAlgebra x
    have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      .of_flat_of_isLocalHom
    exact ⟨IsDomain.of_faithfulSMul _ (X.presheaf.stalk x),
      TauCeti.IsIntegrallyClosed.of_faithfullyFlat _ (X.presheaf.stalk x)⟩

end AlgebraicGeometry.Scheme.Hom
