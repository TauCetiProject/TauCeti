/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Cohomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Homotopy

/-!
# Quasi-isomorphism invariance of linear Hom complexes into K-injective complexes

Let `C` be an `R`-linear abelian category over an arbitrary ring `R`. Precomposition by a
quasi-isomorphism `K' ⟶ K` induces a quasi-isomorphism on `R`-linear Hom complexes into any
K-injective complex `L`, and postcomposition by a quasi-isomorphism between K-injective complexes
induces a homotopy equivalence (hence a quasi-isomorphism) out of any complex `K`. Together with
`CochainComplex.IsKInjective.exists_homotopyEquiv`, this shows that `linearHomComplex R K I`
depends on a K-injective replacement `K ⟶ I` only up to homotopy equivalence.
-/

public section

open CategoryTheory CochainComplex DerivedCategory

namespace TauCeti

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Precomposition by a quasi-isomorphism induces a quasi-isomorphism on `R`-linear Hom complexes
into any K-injective complex. -/
theorem quasiIso_linearHomComplexPrecomp_of_isKInjective {K' K L : CochainComplex C ℤ}
    (f : K' ⟶ K) [QuasiIso f] [L.IsKInjective] :
    QuasiIso (linearHomComplexPrecomp R f L) := by
  let := HasDerivedCategory.standard C
  have hf : IsIso (Qh.map ((HomotopyCategory.quotient C _).map f)) := by
    rw [isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff f).2 inferInstance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  rw [← (linearHomComplexHomologyLinearEquiv R K' L n).bijective.of_comp_iff']
  have hcomm : (linearHomComplexHomologyLinearEquiv R K' L n) ∘
      (HomologicalComplex.homologyMap (linearHomComplexPrecomp R f L) n).hom =
      (fun g ↦ (HomotopyCategory.quotient C _).map f ≫ g) ∘
        (linearHomComplexHomologyLinearEquiv R K L n) := by
    ext z
    exact linearHomComplexHomologyLinearEquiv_homologyMap_precomp R f z
  rw [hcomm]
  refine Function.Bijective.comp ?_ (linearHomComplexHomologyLinearEquiv R K L n).bijective
  rw [← (IsKInjective.Qh_map_bijective _ (L⟦n⟧)).of_comp_iff']
  have hQ : Qh.map ∘ (fun g : (HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (L⟦n⟧) ↦ (HomotopyCategory.quotient C _).map f ≫ g) =
      (Iso.homCongr (asIso (Qh.map ((HomotopyCategory.quotient C _).map f))).symm
        (Iso.refl _)) ∘ Qh.map := by
    ext g
    simp [Iso.homCongr_apply]
  rw [hQ]
  exact (Iso.homCongr _ _).bijective.comp (IsKInjective.Qh_map_bijective _ (L⟦n⟧))

/-- Postcomposition by a quasi-isomorphism between K-injective complexes induces a
quasi-isomorphism on `R`-linear Hom complexes from any complex `K`. -/
theorem quasiIso_linearHomComplexPostcomp_of_isKInjective (K : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') [QuasiIso g] [L.IsKInjective] [L'.IsKInjective] :
    QuasiIso (linearHomComplexPostcomp R K g) := by
  obtain ⟨e, rfl⟩ := (IsKInjective.quasiIso_iff g).1 inferInstance
  rw [← linearHomComplexPostcompHomotopyEquiv_hom]
  exact (linearHomComplexPostcompHomotopyEquiv R K e).quasiIso_hom

end TauCeti
