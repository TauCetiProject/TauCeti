/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Comparison

/-!
# Uniqueness of complete resolutions of Gorenstein-projective modules

A totally acyclic complex `P` of finitely generated projective modules is a complete resolution in
the Frobenius exact category of finitely generated Gorenstein-projective modules. Its cycle
sequences `Zⁿ(P) ↪ Pⁿ ↠ Zⁿ⁺¹(P)` are conflations there, and its terms are projective-injective.
The comparison theorem for complete resolutions in an exact category therefore applies to totally
acyclic complexes. A morphism `Z⁰(P) ⟶ Z⁰(Q)` lifts to a map of complexes `P ⟶ Q`, any two lifts
are homotopic, and totally acyclic complexes with isomorphic cycles in degree zero are homotopy
equivalent. In particular the complete resolution of a Gorenstein-projective module, the complex
in the definition of `TauCeti.IsGorensteinProjective`, is unique up to homotopy equivalence.

## Main definitions

* `CochainComplex.IsTotallyAcyclic.completeResolution`: a totally acyclic complex as a complete
  resolution in `TauCeti.GorensteinProjectiveModuleCat.exactStructure`.
* `CochainComplex.IsTotallyAcyclic.completeResolutionComplexIso`: its spliced complex, as a
  complex of modules, is the given complex.
* `CochainComplex.IsTotallyAcyclic.lift`: the map of totally acyclic complexes lifting a morphism
  of the cycles in degree zero.
* `CochainComplex.IsTotallyAcyclic.liftHomotopy`: two lifts of the same morphism are homotopic.
* `CochainComplex.IsTotallyAcyclic.homotopyEquiv`: totally acyclic complexes with isomorphic
  cycles in degree zero are homotopy equivalent.

## Main results

* `CochainComplex.IsTotallyAcyclic.iCycles_lift_f_zero`: the lift induces the given morphism on
  the cycles in degree zero.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4, for the
  uniqueness of complete resolutions up to homotopy.
-/

public section

open CategoryTheory TauCeti TauCeti.ExactStructure

universe v u

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] [Small.{v} A] {P Q : CochainComplex (ModuleCat.{v} A) ℤ}

/-- A totally acyclic complex as a complete resolution in the exact category of finitely
generated Gorenstein-projective modules: the conflations are the cycle sequences
`Zⁿ(P) ↪ Pⁿ ↠ Zⁿ⁺¹(P)`. -/
noncomputable def completeResolution (hP : P.IsTotallyAcyclic) :
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).CompleteResolution where
  Z n := ⟨P.cycles n, hP.isGorensteinProjective_cycles n⟩
  X n := ⟨P.X n, have := hP.finite n; have := hP.projective n
    isGorensteinProjective_of_projective _⟩
  ι n := ObjectProperty.homMk (P.iCycles n)
  π n := ObjectProperty.homMk (P.toCycles n (n + 1))
  ι_π n := ObjectProperty.hom_ext _ (P.iCycles_toCycles n (n + 1))
  conflation n := by
    rw [GorensteinProjectiveModuleCat.exactStructure_conflation_iff]
    have h := P.cyclesShortComplex_shortExact n (n + 1) rfl (hP.acyclic (n + 1))
    rw [HomologicalComplex.cyclesShortComplex_def] at h
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) h
  projectiveInjective n := (projectiveInjective_iff _ _).mpr
    ⟨(GorensteinProjectiveModuleCat.exactStructure_isProjective_iff _).mpr (hP.projective n),
      (GorensteinProjectiveModuleCat.exactStructure_isInjective_iff _).mpr (hP.projective n)⟩

/-- The complex of `CochainComplex.IsTotallyAcyclic.completeResolution`, as a complex of modules,
is the given totally acyclic complex. -/
noncomputable def completeResolutionComplexIso (hP : P.IsTotallyAcyclic) :
    ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).obj
      hP.completeResolution.complex ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j rfl
    simp [completeResolution])

/-- A map of totally acyclic complexes as a map of the complexes of their complete resolutions in
the exact category of Gorenstein-projective modules. -/
private noncomputable def homOfHom (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (φ : P ⟶ Q) : hP.completeResolution.complex ⟶ hQ.completeResolution.complex where
  f n := ObjectProperty.homMk (φ.f n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext1
    simp [completeResolution]

private theorem map_homOfHom (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic) (φ : P ⟶ Q) :
    ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).map (homOfHom hP hQ φ) =
      (completeResolutionComplexIso hP).hom ≫ φ ≫ (completeResolutionComplexIso hQ).inv := by
  ext n : 1
  exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- **The comparison map** for totally acyclic complexes: the map `P ⟶ Q` lifting a morphism
`f : Z⁰(P) ⟶ Z⁰(Q)` of the cycles in degree zero. -/
noncomputable def lift (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (f : P.cycles 0 ⟶ Q.cycles 0) : P ⟶ Q :=
  (completeResolutionComplexIso hP).inv ≫
    ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).map
      (CompleteResolution.lift hP.completeResolution hQ.completeResolution
        (ObjectProperty.homMk f)) ≫
    (completeResolutionComplexIso hQ).hom

/-- The lift induces the given morphism on the cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem iCycles_lift_f_zero (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (f : P.cycles 0 ⟶ Q.cycles 0) : P.iCycles 0 ≫ (lift hP hQ f).f 0 = f ≫ Q.iCycles 0 := by
  have h := (IsGorensteinProjective.{v} A).ι.congr_map
    (CompleteResolution.ι_lift_f_zero hP.completeResolution hQ.completeResolution
      (ObjectProperty.homMk f))
  simpa [lift, completeResolutionComplexIso, completeResolution] using h

/-- Two maps of totally acyclic complexes lifting the same morphism of the cycles in degree zero
are homotopic. -/
noncomputable def liftHomotopy (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (f : P.cycles 0 ⟶ Q.cycles 0) (φ ψ : P ⟶ Q) (hφ : P.iCycles 0 ≫ φ.f 0 = f ≫ Q.iCycles 0)
    (hψ : P.iCycles 0 ≫ ψ.f 0 = f ≫ Q.iCycles 0) : Homotopy φ ψ :=
  -- The homotopy between the lifts in the exact category, carried to modules by the inclusion
  -- and transported along the identifications of the complexes.
  let H := (IsGorensteinProjective.{v} A).ι.mapHomotopy
    (CompleteResolution.liftHomotopy (ObjectProperty.homMk f) (homOfHom hP hQ φ)
      (homOfHom hP hQ ψ) (ObjectProperty.hom_ext _ (by simpa [homOfHom, completeResolution]))
      (ObjectProperty.hom_ext _ (by simpa [homOfHom, completeResolution])))
  (Homotopy.ofEq (by simp [map_homOfHom])).trans
    (((H.compLeft (completeResolutionComplexIso hP).inv).compRight
      (completeResolutionComplexIso hQ).hom).trans (Homotopy.ofEq (by simp [map_homOfHom])))

/-- **Uniqueness of complete resolutions up to homotopy.** Totally acyclic complexes with
isomorphic cycles in degree zero are homotopy equivalent; in particular any two complete
resolutions of a Gorenstein-projective module are. -/
noncomputable def homotopyEquiv (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (e : P.cycles 0 ≅ Q.cycles 0) : HomotopyEquiv P Q :=
  (HomotopyEquiv.ofIso (completeResolutionComplexIso hP).symm).trans
    (((IsGorensteinProjective.{v} A).ι.mapHomotopyEquiv
      (CompleteResolution.homotopyEquiv hP.completeResolution hQ.completeResolution
        (ObjectProperty.isoMk _ e))).trans
      (HomotopyEquiv.ofIso (completeResolutionComplexIso hQ)))

end CochainComplex.IsTotallyAcyclic
