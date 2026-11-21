/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Descent
public import TauCeti.AlgebraicGeometry.Limits.Noetherian.Approximation

/-!
# Noetherian models of finitely presented families

A finitely presented scheme over an affine base is the Cartesian base change of a
finitely presented scheme over a Noetherian affine base. The model scheme is Noetherian as well.
The base may be arbitrary: it need not be Noetherian. If the original source is affine,
the model can also be chosen affine.

References: The Stacks Project, Proposition 32.5.4 (Tag 01ZA) and Lemma 32.10.1 (Tag 01ZM).
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An affine finitely presented family over an affine base has an affine Noetherian model. -/
theorem Scheme.Hom.exists_isPullback_over_noetherian_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (_ : IsNoetherian S₀)
      (X₀ : Scheme.{u}) (_ : IsAffine X₀) (_ : IsNoetherian X₀) (f₀ : X₀ ⟶ S₀)
      (_ : LocallyOfFinitePresentation f₀) (a : X ⟶ X₀) (b : S ⟶ S₀),
      IsPullback a f f₀ b := by
  obtain ⟨I, hI, hcof, D, π, ⟨hc⟩, _htrans, hstage⟩ :=
    S.exists_isLimit_noetherian_of_isAffine
  let := hI
  let := hcof
  have (i : I) : IsAffine (D.obj i) := (hstage i).1
  have (i : I) : IsNoetherian (D.obj i) := (hstage i).2
  obtain ⟨i, X₀, haff, f₀, hfp, a, hsquare⟩ :=
    CategoryTheory.Functor.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine D _ hc f
  have := haff
  have := hfp
  exact ⟨D.obj i, inferInstance, inferInstance, X₀, haff,
    TauCeti.AlgebraicGeometry.isNoetherian_of_finiteType f₀, f₀, hfp, a, π.app i, hsquare⟩

/-- Every finitely presented family over an affine base has a finitely presented model over a
Noetherian affine base, and the model itself is Noetherian. -/
theorem Scheme.Hom.exists_isPullback_over_noetherian_of_finitePresentation
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (_ : IsNoetherian S₀)
      (X₀ : Scheme.{u}) (_ : IsNoetherian X₀) (f₀ : X₀ ⟶ S₀)
      (_ : LocallyOfFinitePresentation f₀) (_ : QuasiCompact f₀) (_ : QuasiSeparated f₀)
      (a : X ⟶ X₀) (b : S ⟶ S₀), IsPullback a f f₀ b := by
  obtain ⟨I, hI, hcof, D, π, ⟨hc⟩, htrans, hstage⟩ :=
    S.exists_isLimit_noetherian_of_isAffine
  let := hI
  let := hcof
  let := htrans
  have (i : I) : IsAffine (D.obj i) := (hstage i).1
  have (i : I) : IsNoetherian (D.obj i) := (hstage i).2
  obtain ⟨baseStage⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨i, X₀, f₀, hfp, hqc, hqs, a, hsquare⟩ :=
    CategoryTheory.Limits.IsLimit.exists_isPullback_of_finitePresentation hc baseStage f
  have := hfp
  have := hqc
  exact ⟨D.obj i, inferInstance, inferInstance, X₀,
    TauCeti.AlgebraicGeometry.isNoetherian_of_finiteType f₀,
    f₀, hfp, hqc, hqs, a, π.app i, hsquare⟩

end AlgebraicGeometry
