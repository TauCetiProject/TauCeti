/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.DifferentialModule.Basic
public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Frobenius

/-!
# Differential modules with the componentwise split exact structure are Frobenius

An exact structure `E` on an additive category `C` induces the **underlying exact structure**
`E.differentialModule` on differential modules in `C`: a short complex of differential modules
is a conflation when its underlying short complex in `C` is a conflation of `E`. It is the
exact structure transported from the degreewise exact structure on one-periodic complexes along
`TauCeti.DifferentialModule.onePeriodicComplexEquivalence`, so that equivalence and its inverse
preserve conflations.

For the split exact structure on `C`, the conflations are the short complexes of differential
modules which split on underlying objects, not necessarily compatibly with the differentials.
This exact structure is Frobenius, and its projective and injective objects are exactly the
**contractible** differential modules: those `M` with an endomorphism `h` of the underlying
object such that `h ≫ M.d + M.d ≫ h = 𝟙 M.X`. Its stable category, obtained by killing the
morphisms which factor through a contractible differential module, is therefore triangulated by
Happel's theorem `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`. It is a model of the
homotopy category of differential modules, the one-periodic homotopy category `K₁(C)`.

## Main definitions

* `TauCeti.ExactStructure.differentialModule`: the exact structure on differential modules whose
  conflations are the underlying conflations.

## Main results

* `TauCeti.ExactStructure.differentialModule_conflation_iff`,
  `TauCeti.ExactStructure.differentialModule_isInflation_iff` and
  `TauCeti.ExactStructure.differentialModule_isDeflation_iff`: conflations, inflations and
  deflations are detected on underlying objects.
* `TauCeti.ExactStructure.differentialModule_split_conflation_iff`: for the split exact
  structure, they are the short complexes which split on underlying objects.
* `TauCeti.DifferentialModule.nonempty_homotopy_toOnePeriodicComplex_iff`: the one-periodic
  complex of a differential module is contractible exactly when the differential module is.
* `TauCeti.ExactStructure.differentialModule_split_isProjective_iff` and
  `TauCeti.ExactStructure.differentialModule_split_isInjective_iff`: the relatively projective
  and relatively injective differential modules are the contractible ones.
* `TauCeti.ExactStructure.differentialModule_split_isFrobenius`: the componentwise split exact
  structure on differential modules is Frobenius.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of
  differential modules*, Invent. Math. **169** (2007), 1–35, Section 1.
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1, for the corresponding Frobenius structure on complexes.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits DifferentialModule

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace DifferentialModule

/-- The one-periodic complex of a differential module `M` is contractible exactly when `M` is:
when some endomorphism `h` of the underlying object satisfies `h ≫ M.d + M.d ≫ h = 𝟙 M.X`. -/
theorem nonempty_homotopy_toOnePeriodicComplex_iff (M : DifferentialModule C) :
    Nonempty (Homotopy (𝟙 ((toOnePeriodicComplex C).obj M)) 0) ↔
      ∃ h : M.X ⟶ M.X, h ≫ M.d + M.d ≫ h = 𝟙 M.X := by
  -- In `ZMod 1` every index is related to every other one.
  have hrel (i j : ZMod 1) : (ComplexShape.up (ZMod 1)).Rel i j := Subsingleton.elim _ _
  constructor
  · rintro ⟨H⟩
    refine ⟨H.hom 0 0, ?_⟩
    have := H.comm 0
    rw [dNext_eq _ (hrel 0 0), prevD_eq _ (hrel 0 0)] at this
    simpa [add_comm] using this.symm
  · rintro ⟨h, hh⟩
    refine ⟨{ hom := fun _ _ ↦ h, zero := fun i j hij ↦ absurd (hrel j i) hij, comm := ?_ }⟩
    intro i
    rw [dNext_eq _ (hrel i i), prevD_eq _ (hrel i i)]
    simpa [add_comm] using hh.symm

end DifferentialModule

variable [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The additivity instance needed to transport exact structures from one-periodic complexes to
differential modules. -/
private theorem additive_onePeriodicComplexEquivalence_symm :
    (onePeriodicComplexEquivalence C).symm.functor.Additive := by
  rw [Equivalence.symm_functor, onePeriodicComplexEquivalence_inverse]
  infer_instance

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The additivity instance needed to compare relative projectives along the equivalence with
one-periodic complexes. -/
private theorem additive_onePeriodicComplexEquivalence :
    (onePeriodicComplexEquivalence C).functor.Additive := by
  rw [onePeriodicComplexEquivalence_functor]
  infer_instance

attribute [local instance] additive_onePeriodicComplexEquivalence_symm
  additive_onePeriodicComplexEquivalence

/-- The **underlying exact structure** on differential modules: a short complex of differential
modules is a conflation when its underlying short complex is a conflation of `E`
(`differentialModule_conflation_iff`). It is transported from the degreewise exact structure on
one-periodic complexes. -/
noncomputable def differentialModule : ExactStructure (DifferentialModule C) :=
  (E.homologicalComplex (ComplexShape.up (ZMod 1))).transport
    (onePeriodicComplexEquivalence C).symm

/-- A short complex of differential modules is a conflation for the underlying exact structure
exactly when its underlying short complex is a conflation. -/
@[simp]
theorem differentialModule_conflation_iff (S : ShortComplex (DifferentialModule C)) :
    E.differentialModule.Conflation S ↔ E.Conflation (S.map (forget C)) := by
  rw [differentialModule, transport_conflation_iff]
  simp only [Equivalence.symm_inverse, onePeriodicComplexEquivalence_functor,
    homologicalComplex_conflation_iff]
  exact ⟨fun h ↦ h 0, fun h i ↦ Subsingleton.elim i 0 ▸ h⟩

/-- A morphism of differential modules is an inflation for the underlying exact structure
exactly when its underlying morphism is an inflation. -/
@[simp]
theorem differentialModule_isInflation_iff {M N : DifferentialModule C} (f : M ⟶ N) :
    E.differentialModule.IsInflation f ↔ E.IsInflation f.f := by
  rw [differentialModule, transport_isInflation_iff, homologicalComplex_isInflation_iff,
    Equivalence.symm_inverse, onePeriodicComplexEquivalence_functor]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- A morphism of differential modules is a deflation for the underlying exact structure
exactly when its underlying morphism is a deflation. -/
@[simp]
theorem differentialModule_isDeflation_iff {M N : DifferentialModule C} (f : M ⟶ N) :
    E.differentialModule.IsDeflation f ↔ E.IsDeflation f.f := by
  rw [differentialModule, transport_isDeflation_iff, homologicalComplex_isDeflation_iff,
    Equivalence.symm_inverse, onePeriodicComplexEquivalence_functor]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- The forgetful functor from differential modules preserves conflations. -/
theorem isConflationExact_forget_differentialModule :
    E.differentialModule.IsConflationExact E (forget C) :=
  ⟨fun hS ↦ (E.differentialModule_conflation_iff _).1 hS⟩

/-- Passing from a differential module to its one-periodic complex preserves conflations. -/
theorem isConflationExact_toOnePeriodicComplex :
    E.differentialModule.IsConflationExact (E.homologicalComplex (ComplexShape.up (ZMod 1)))
      (toOnePeriodicComplex C) :=
  ⟨fun hS ↦ (E.homologicalComplex_conflation_iff _ _).2 fun _ ↦
    (E.differentialModule_conflation_iff _).1 hS⟩

/-- Passing from a one-periodic complex to its differential module preserves conflations. -/
theorem isConflationExact_ofOnePeriodicComplex :
    (E.homologicalComplex (ComplexShape.up (ZMod 1))).IsConflationExact E.differentialModule
      (ofOnePeriodicComplex C) :=
  ⟨fun hS ↦ (E.differentialModule_conflation_iff _).2
    ((E.homologicalComplex_conflation_iff _ _).1 hS 0)⟩

/-- For the split exact structure, a short complex of differential modules is a conflation
exactly when its underlying short complex splits, not necessarily compatibly with the
differentials. -/
theorem differentialModule_split_conflation_iff (S : ShortComplex (DifferentialModule C)) :
    (split C).differentialModule.Conflation S ↔ Nonempty (S.map (forget C)).Splitting := by
  simp

/-- A differential module is relatively projective for the componentwise split exact structure
exactly when it is contractible: some endomorphism `h` of the underlying object satisfies
`h ≫ M.d + M.d ≫ h = 𝟙 M.X`. -/
theorem differentialModule_split_isProjective_iff (M : DifferentialModule C) :
    (split C).differentialModule.isProjective M ↔
      ∃ h : M.X ⟶ M.X, h ≫ M.d + M.d ≫ h = 𝟙 M.X := by
  rw [← nonempty_homotopy_toOnePeriodicComplex_iff,
    ← homologicalComplex_split_isProjective_iff (fun i ↦ ⟨i + 1, rfl⟩)]
  have := (split C).differentialModule.isProjective_map_equivalence_iff _
    (onePeriodicComplexEquivalence C)
    (by simpa using (split C).isConflationExact_toOnePeriodicComplex)
    (by simpa using (split C).isConflationExact_ofOnePeriodicComplex) M
  simpa using this.symm

/-- The componentwise split exact structure on differential modules is Frobenius. -/
theorem differentialModule_split_isFrobenius : (split C).differentialModule.IsFrobenius :=
  (homologicalComplex_split_isFrobenius (c := ComplexShape.up (ZMod 1))
    (fun j ↦ ⟨j, Subsingleton.elim _ _⟩) (fun i ↦ ⟨i, Subsingleton.elim _ _⟩)).of_equivalence
    (onePeriodicComplexEquivalence C).symm
    (isConflationExact_functor_transport _ _) (isConflationExact_inverse_transport _ _)

/-- A differential module is relatively injective for the componentwise split exact structure
exactly when it is contractible. -/
theorem differentialModule_split_isInjective_iff (M : DifferentialModule C) :
    (split C).differentialModule.isInjective M ↔
      ∃ h : M.X ⟶ M.X, h ≫ M.d + M.d ≫ h = 𝟙 M.X := by
  rw [differentialModule_split_isFrobenius.injective_iff_projective,
    differentialModule_split_isProjective_iff]

end ExactStructure

end TauCeti
