/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.Basic
public import TauCeti.Algebra.Homology.Single.Cokernel
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation

/-!
# Pseudo-coherent sheaves are finitely presented

The first two terms of a finite free resolution give a finite presentation. Applying this
locally shows that a pseudo-coherent module sheaf on an arbitrary scheme is finitely
presented, and in particular quasi-coherent. Thus the local resolution condition excludes
non-quasi-coherent sheaves even if their modules of sections happen to be pseudo-coherent.

We use Mathlib's `SheafOfModules.presentationOfIsCokernelFree` and transport the resulting
presentations to the slice sites of the resolving opens, using `Scheme.Modules.overEquiv`.

## References

* The Stacks Project, Section 36.10 (Tag 08E4), pseudo-coherent complexes on schemes.
* The Stacks Project, Lemma 15.66.4 (Tag 064T), finite presentation of pseudo-coherent modules.
-/

public section

open CategoryTheory Limits HomologicalComplex TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} {F : X.Modules}

/-- A sheaf with a finite free resolution admits a global presentation with finitely many
generators and relations, extracted from the first two resolving terms. -/
theorem HasFiniteFreeResolution.exists_isFinite_presentation (h : F.HasFiniteFreeResolution) :
    ∃ p : F.Presentation, p.IsFinite := by
  obtain ⟨K, π, hK, hπ⟩ := hasFiniteFreeResolution_iff.mp h
  obtain ⟨ι, hι, ⟨e₁⟩⟩ := hK 1
  obtain ⟨σ, hσ, ⟨e₀⟩⟩ := hK 0
  let f : (SheafOfModules.free (R := X.ringCatSheaf) ι : X.Modules) ⟶
      SheafOfModules.free σ := e₁.inv ≫ K.d 1 0 ≫ e₀.hom
  let e : cokernel (C := X.Modules) f ≅ F :=
    cokernel.mapIso (C := X.Modules) f (K.d 1 0) e₁.symm e₀.symm
      (e₀.comp_inv_eq.mpr (Category.assoc _ _ _).symm) ≪≫
      (cokernelIsCokernel (K.d 1 0)).coconePointUniqueUpToIso
        (K.isColimitCokernelCoforkOfQuasiIsoAt π)
  let p := SheafOfModules.presentationOfIsCokernelFree f (cokernel.π f)
    (cokernel.condition f) (cokernelIsCokernel f)
  have hp : p.IsFinite :=
    { isFiniteType_generators := ⟨hσ⟩
      isFiniteType_relations := ⟨hι⟩ }
  -- Presentations use the sheaf category, whereas `e` uses the scheme-module category.
  -- Pass the isomorphism instance explicitly across these two instance heads.
  let p' := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    e.hom (Iso.isIso_hom e) p
  exact ⟨p', @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _
    (Iso.isIso_hom e) p hp⟩

/-- Every pseudo-coherent module sheaf on a scheme is finitely presented. No Noetherian
hypothesis is required. -/
theorem IsPseudoCoherent.isFinitePresentation (h : F.IsPseudoCoherent) :
    F.IsFinitePresentation := by
  choose U hx hU using isPseudoCoherent_iff.mp h
  have (x : X) : (F.over (U x)).IsFinitePresentation := by
    obtain ⟨p, hp⟩ := (hU x).exists_isFinite_presentation
    obtain ⟨q, hq⟩ := F.exists_isFinite_presentation_over_of_restrict (U x) p
    exact q.isFinitePresentation
  exact SheafOfModules.IsFinitePresentation.of_coversTop F U (by
    rw [Opens.coversTop_iff]
    exact top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)

/-- Every pseudo-coherent module sheaf on a scheme is quasi-coherent. -/
theorem IsPseudoCoherent.isQuasicoherent (h : F.IsPseudoCoherent) : F.IsQuasicoherent := by
  have : F.IsFinitePresentation := h.isFinitePresentation
  -- Instance search does not match the scheme-module wrapper to Mathlib's sheaf-module
  -- instance, even with an explicit sheaf-category target. Supply the object explicitly.
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F

end

end AlgebraicGeometry.Scheme.Modules
