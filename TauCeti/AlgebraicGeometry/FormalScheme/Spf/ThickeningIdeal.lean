/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.IdealKernel
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

/-!
# Ideals of definition on the formal spectrum

`TauCeti.FormalScheme.Spf.idealSheaf` is the kernel of the structure sheaf map of
`TauCeti.FormalScheme.Spf.fromSpecQuotient`. Its global sections recover the original ideal.
On basic opens, `idealSheaf_basic` computes its sections using
`basicOpenSectionsAdicCompletionIso` and `AdicCompletion.ker_toQuotient`.

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.3.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, Ch. I, Proposition 1.1.19.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.SheafOfModules

namespace TauCeti.FormalScheme.Spf

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  {J : Ideal A}

/-- The ideal sheaf `J^Δ` on `Spf A` is the kernel of the map to the pushed-forward
structure sheaf of `Spec (A ⧸ J)`, for an ideal of definition `J`. -/
noncomputable def idealSheaf (hJ : IsAdic J) :
    (SheafOfModules.unit
      (ringCatSheaf (structureSheaf (IsAdicRing.ideal_spec A).2.1))).Submodule :=
  Sheaf.idealKernel (J := Opens.grothendieckTopology (carrier A))
    (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ)

/-- On each open, the sections of `J^Δ` are the kernel of the quotient projection's
map on sections. -/
@[simp]
theorem idealSheaf_sections (hJ : IsAdic J) (U : Opens (carrier A)) :
    (idealSheaf hJ).toSubmodule.obj (op U) =
      RingHom.ker ((toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ).hom.app (op U)).hom :=
  Sheaf.idealKernel_obj (J := Opens.grothendieckTopology (carrier A))
    (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ) (op U)

/-- Under the identification of global sections of `Spf A` with `A`, the ideal
of global sections of `J^Δ` is `J`. -/
@[simp]
theorem idealSheaf_global (hJ : IsAdic J) :
    have := (IsAdicRing.ideal_spec A).2.2
    Ideal.comap (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv.hom
      ((idealSheaf hJ).toSubmodule.obj (op ⊤)) = J := by
  intro
  rw [idealSheaf_sections, RingHom.comap_ker]
  have h := globalSectionsIso_inv_comp_toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ
  have hh := congrArg CommRingCat.Hom.hom h
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hh
  rw [hh, RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (quotientSheafGlobalSectionsIso hJ).inv).injective,
    Ideal.mk_ker]

/-- In the completed localization coordinates on `D(f)`, the sections of `J^Δ` are the
extension of `J` to the completed localization. -/
theorem idealSheaf_basic (hJ : IsAdic J) (f : A) :
    Ideal.map (basicOpenSectionsAdicCompletionIso (IsAdicRing.ideal_spec A).2.1 f).hom.hom
      ((idealSheaf hJ).toSubmodule.obj (op (basicOpen f))) =
        J.map (algebraMap A (AdicCompletion
          ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
            (Localization.Away f))) := by
  let hI := (IsAdicRing.ideal_spec A).2.1
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hJ.isOpen_pow 1)
  have h := congrArg CommRingCat.Hom.hom
    (toQuotientSheaf_app_basicOpen_comp_quotientSheafBasicOpenIso_hom hI hJ f hn)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
  have hsurj : Function.Surjective (basicOpenSectionsAdicCompletionIso hI f).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (basicOpenSectionsAdicCompletionIso hI f).hom).surjective
  -- Transport the section kernel across the two section isomorphisms.
  rw [idealSheaf_sections, ← RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hJ f).hom).injective,
    h, ← RingHom.comap_ker, Ideal.map_comap_of_surjective _ hsurj,
    AdicCompletion.ker_toQuotient _ _ ((IsAdicRing.ideal_spec A).1.map _), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

end TauCeti.FormalScheme.Spf
