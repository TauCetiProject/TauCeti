/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.IdealKernel
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.StructureSheaf
import TauCeti.RingTheory.Ideal.Maps

/-!
# Ideals of definition on the formal spectrum

`TauCeti.FormalScheme.Spf.idealSheaf` is the kernel of `toQuotientSheaf`, formed by
`Sheaf.idealKernel`. Its global sections recover the original ideal by `idealSheaf_global`.
On basic opens, `idealSheaf_basic_kernel` identifies its sections in completed localization
coordinates, and `idealSheaf_basic` evaluates the kernel using `AdicCompletion.ker_toQuotient`.

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.3.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, Ch. I, Proposition 1.1.19.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.SheafOfModules

namespace TauCeti.FormalScheme.Spf

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {I J : Ideal A}

/-- The ideal sheaf `J^Δ` on `Spf A` is the kernel of the map to the pushed-forward
structure sheaf of `Spec (A ⧸ J)`, for ideals of definition `I` and `J`. -/
noncomputable def idealSheaf (hI : IsAdic I) (hJ : IsAdic J) :
    (SheafOfModules.unit (ringCatSheaf (structureSheaf hI))).Submodule :=
  Sheaf.idealKernel (J := Opens.grothendieckTopology (carrier A)) (toQuotientSheaf hI hJ)

/-- The ideal sheaf of the thickening is the bundled kernel of the quotient projection. -/
theorem idealSheaf_def (hI : IsAdic I) (hJ : IsAdic J) :
    idealSheaf hI hJ =
      Sheaf.idealKernel (J := Opens.grothendieckTopology (carrier A)) (toQuotientSheaf hI hJ) :=
  (rfl)

/-- On each open, the sections of `J^Δ` are the kernel of the quotient projection's
map on sections. -/
@[simp]
theorem idealSheaf_sections (hI : IsAdic I) (hJ : IsAdic J) (U : Opens (carrier A)) :
    (idealSheaf hI hJ).toSubmodule.obj (op U) =
      RingHom.ker ((toQuotientSheaf hI hJ).hom.app (op U)).hom := by
  rw [idealSheaf_def]
  exact Sheaf.idealKernel_obj (J := Opens.grothendieckTopology (carrier A))
    (toQuotientSheaf hI hJ) (op U)

/-- When `A` is `I`-adically complete, under the identification of global sections of
`Spf A` with `A`, the ideal of global sections of `J^Δ` is `J`. -/
@[simp]
theorem idealSheaf_global [IsAdicComplete I A] (hI : IsAdic I) (hJ : IsAdic J) :
    Ideal.comap (globalSectionsIso hI).inv.hom
      ((idealSheaf hI hJ).toSubmodule.obj (op ⊤)) = J := by
  rw [idealSheaf_sections]
  refine (RingHom.comap_ker_eq_of_comp_eq (g := Ideal.Quotient.mk J) ?_
    (ConcreteCategory.bijective_of_isIso (quotientSheafGlobalSectionsIso hJ).inv).injective).trans
      Ideal.mk_ker
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
    congrArg CommRingCat.Hom.hom (globalSectionsIso_inv_comp_toQuotientSheaf hI hJ)

/-- In the completed localization coordinates on `D(f)`, the sections of `J^Δ` are the
kernel of the projection onto `A_f / J A_f` at any index with `I ^ (n + 1) ≤ J`. -/
theorem idealSheaf_basic_kernel (hI : IsAdic I) (hJ : IsAdic J) (f : A)
    {n : ℕ} (hn : I ^ (n + 1) ≤ J) :
    Ideal.map (basicOpenSectionsAdicCompletionIso hI f).hom.hom
      ((idealSheaf hI hJ).toSubmodule.obj (op (basicOpen f))) =
        RingHom.ker (AdicCompletion.toQuotient (I.map (algebraMap A (Localization.Away f)))
          ⟨n + 1, (Ideal.map_pow _ _ _).ge.trans (Ideal.map_mono hn)⟩) := by
  have h := congrArg CommRingCat.Hom.hom
    (toQuotientSheaf_app_basicOpen_comp_quotientSheafBasicOpenIso_hom hI hJ f hn)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
  have hpullback := RingHom.comap_ker_eq_of_comp_eq h.symm
    (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hJ f).hom).injective
  rw [idealSheaf_sections, ← hpullback, Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (basicOpenSectionsAdicCompletionIso hI f).hom).surjective]

/-- For finitely generated `I`, in the completed localization coordinates on `D(f)`,
the sections of `J^Δ` are the extension of `J` to the completed localization. -/
theorem idealSheaf_basic (hI : IsAdic I) (hJ : IsAdic J) (hIfg : I.FG) (f : A) :
    Ideal.map (basicOpenSectionsAdicCompletionIso hI f).hom.hom
      ((idealSheaf hI hJ).toSubmodule.obj (op (basicOpen f))) =
        J.map (algebraMap A
          (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))) := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hJ.isOpen_pow 1)
  rw [idealSheaf_basic_kernel hI hJ f hn, AdicCompletion.ker_toQuotient _ _ (hIfg.map _),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end TauCeti.FormalScheme.Spf
