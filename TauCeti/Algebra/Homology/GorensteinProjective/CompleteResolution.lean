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
* `CochainComplex.IsTotallyAcyclic.iCycles_homotopyEquiv_hom_f_zero` and
  `CochainComplex.IsTotallyAcyclic.iCycles_homotopyEquiv_inv_f_zero`: the homotopy equivalence
  induces the given isomorphism on the cycles in degree zero.

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
`Zⁿ(P) ↪ Pⁿ ↠ Zⁿ⁺¹(P)`. Its body is exposed so that its fields are the cycles, terms and maps of
`P` by definition, as the lemmas below record. -/
@[expose] noncomputable def completeResolution (hP : P.IsTotallyAcyclic) :
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).CompleteResolution where
  Z n := ⟨P.cycles n, hP.isGorensteinProjective_cycles n⟩
  X n := ⟨P.X n, have := hP.finite n; have := hP.projective n
    isGorensteinProjective_of_projective _⟩
  ι n := ObjectProperty.homMk (P.iCycles n)
  π n := ObjectProperty.homMk (P.toCycles n (n + 1))
  ι_π n := ObjectProperty.hom_ext _ (P.iCycles_toCycles n (n + 1))
  conflation n := by
    rw [GorensteinProjectiveModuleCat.exactStructure_conflation_iff]
    exact P.cyclesShortComplex_shortExact_of_iso rfl (hP.acyclic (n + 1)) (Iso.refl _)
      (Iso.refl _)
  projectiveInjective n := (projectiveInjective_iff _ _).mpr
    ⟨(GorensteinProjectiveModuleCat.exactStructure_isProjective_iff _).mpr (hP.projective n),
      (GorensteinProjectiveModuleCat.exactStructure_isInjective_iff _).mpr (hP.projective n)⟩

@[simp]
theorem completeResolution_Z_obj (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (hP.completeResolution.Z n).obj = P.cycles n :=
  rfl

@[simp]
theorem completeResolution_X_obj (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (hP.completeResolution.X n).obj = P.X n :=
  rfl

@[simp]
theorem completeResolution_ι_hom (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (hP.completeResolution.ι n).hom = P.iCycles n :=
  rfl

@[simp]
theorem completeResolution_π_hom (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (hP.completeResolution.π n).hom = P.toCycles n (n + 1) :=
  rfl

/-- The complex of `CochainComplex.IsTotallyAcyclic.completeResolution`, as a complex of modules,
is the given totally acyclic complex; its components are identities. -/
@[expose] noncomputable def completeResolutionComplexIso (hP : P.IsTotallyAcyclic) :
    ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).obj
      hP.completeResolution.complex ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j rfl
    simp)

@[simp]
theorem completeResolutionComplexIso_hom_f (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (completeResolutionComplexIso hP).hom.f n = 𝟙 _ :=
  rfl

@[simp]
theorem completeResolutionComplexIso_inv_f (hP : P.IsTotallyAcyclic) (n : ℤ) :
    (completeResolutionComplexIso hP).inv.f n = 𝟙 _ :=
  rfl

/-- A map of totally acyclic complexes as a map of the complexes of their complete resolutions,
by the fullness of the inclusion of Gorenstein-projective modules on complexes. -/
private noncomputable def preimageHom (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (φ : P ⟶ Q) : hP.completeResolution.complex ⟶ hQ.completeResolution.complex :=
  ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).preimage
    ((completeResolutionComplexIso hP).hom ≫ φ ≫ (completeResolutionComplexIso hQ).inv)

private theorem map_preimageHom (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic) (φ : P ⟶ Q) :
    ((IsGorensteinProjective.{v} A).ι.mapHomologicalComplex _).map (preimageHom hP hQ φ) =
      (completeResolutionComplexIso hP).hom ≫ φ ≫ (completeResolutionComplexIso hQ).inv :=
  Functor.map_preimage _ _

private theorem preimageHom_f_hom (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (φ : P ⟶ Q) (n : ℤ) : ((preimageHom hP hQ φ).f n).hom = φ.f n := by
  simpa using congrArg (fun g => g.f n) (map_preimageHom hP hQ φ)

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
  rw [Functor.map_comp, Functor.map_comp] at h
  simp only [lift, HomologicalComplex.comp_f, completeResolutionComplexIso_hom_f,
    completeResolutionComplexIso_inv_f, Functor.mapHomologicalComplex_map_f]
  -- The goal is `h` up to `ObjectProperty.ι_map` and a composite with the identity component of
  -- `completeResolutionComplexIso hQ`, both of which hold by definition.
  exact h

/-- Two maps of totally acyclic complexes lifting the same morphism of the cycles in degree zero
are homotopic. -/
noncomputable def liftHomotopy (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (f : P.cycles 0 ⟶ Q.cycles 0) (φ ψ : P ⟶ Q) (hφ : P.iCycles 0 ≫ φ.f 0 = f ≫ Q.iCycles 0)
    (hψ : P.iCycles 0 ≫ ψ.f 0 = f ≫ Q.iCycles 0) : Homotopy φ ψ :=
  -- The homotopy between the preimages in the exact category, carried to modules by the
  -- inclusion and transported along the identifications of the complexes.
  let H := (IsGorensteinProjective.{v} A).ι.mapHomotopy
    (CompleteResolution.liftHomotopy (ObjectProperty.homMk f) (preimageHom hP hQ φ)
      (preimageHom hP hQ ψ) (ObjectProperty.hom_ext _ (by simpa [preimageHom_f_hom]))
      (ObjectProperty.hom_ext _ (by simpa [preimageHom_f_hom])))
  (Homotopy.ofEq (by simp [map_preimageHom])).trans
    (((H.compLeft (completeResolutionComplexIso hP).inv).compRight
      (completeResolutionComplexIso hQ).hom).trans (Homotopy.ofEq (by simp [map_preimageHom])))

/-- **Uniqueness of complete resolutions up to homotopy.** Totally acyclic complexes with
isomorphic cycles in degree zero are homotopy equivalent; in particular any two complete
resolutions of a Gorenstein-projective module are. -/
noncomputable def homotopyEquiv (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (e : P.cycles 0 ≅ Q.cycles 0) : HomotopyEquiv P Q where
  hom := lift hP hQ e.hom
  inv := lift hQ hP e.inv
  homotopyHomInvId := liftHomotopy hP hP (𝟙 _) _ _ (by simp) (by simp)
  homotopyInvHomId := liftHomotopy hQ hQ (𝟙 _) _ _ (by simp) (by simp)

/-- The homotopy equivalence induces `e.hom` on the cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem iCycles_homotopyEquiv_hom_f_zero (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (e : P.cycles 0 ≅ Q.cycles 0) :
    P.iCycles 0 ≫ (homotopyEquiv hP hQ e).hom.f 0 = e.hom ≫ Q.iCycles 0 :=
  iCycles_lift_f_zero hP hQ e.hom

/-- The homotopy equivalence induces `e.inv` on the cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem iCycles_homotopyEquiv_inv_f_zero (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic)
    (e : P.cycles 0 ≅ Q.cycles 0) :
    Q.iCycles 0 ≫ (homotopyEquiv hP hQ e).inv.f 0 = e.inv ≫ P.iCycles 0 :=
  iCycles_lift_f_zero hQ hP e.inv

end CochainComplex.IsTotallyAcyclic
