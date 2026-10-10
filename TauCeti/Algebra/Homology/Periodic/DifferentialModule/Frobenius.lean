/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.DifferentialModule.Basic
public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.HomotopyCategory

/-!
# Differential modules form a Frobenius exact category

Let `E` be a Quillen exact structure on an additive category `C`. The category
`DifferentialModule C` of objects with a square-zero endomorphism carries the **componentwise**
exact structure `E.differentialModule`: a short complex of differential modules is a conflation
when its underlying short complex in `C` is a conflation of `E`, with no compatibility with the
differentials required of the splittings or of the exactness data. It is obtained by transporting
the degreewise exact structure on one-periodic complexes along
`TauCeti.DifferentialModule.onePeriodicComplexEquivalence`, so it is the exact structure under
which differential modules and one-periodic complexes are the same exact category.

For the split exact structure on `C`, the result is a Frobenius exact category whose
projective-injective objects are the **contractible** differential modules, those `M` admitting
`h : M.X ⟶ M.X` with `d h + h d = 1`. A morphism factors through such an object exactly when it
is null-homotopic, `φ = d h + h d`. These are the inputs for identifying the stable category of
differential modules with their homotopy category.

## Main definitions

* `TauCeti.ExactStructure.differentialModule`: the componentwise exact structure on
  `DifferentialModule C`.

## Main results

* `TauCeti.ExactStructure.differentialModule_conflation_iff`,
  `TauCeti.ExactStructure.differentialModule_isInflation_iff` and
  `TauCeti.ExactStructure.differentialModule_isDeflation_iff`: conflations, inflations and
  deflations are detected on underlying objects.
* `TauCeti.ExactStructure.differentialModule_split_isProjective_iff` and
  `TauCeti.ExactStructure.differentialModule_split_isInjective_iff`: for the componentwise split
  structure, the relatively projective and the relatively injective differential modules are
  the contractible ones.
* `TauCeti.ExactStructure.differentialModule_split_isFrobenius`: the componentwise split
  structure on differential modules is Frobenius.
* `TauCeti.ExactStructure.differentialModule_split_factorsThrough_iff`: a morphism factors
  through a relative projective exactly when it is null-homotopic.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of
  differential modules*, Invent. Math. **169** (2007), 1–35, Section 1.
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, for the Frobenius exact category of complexes with degreewise
  split conflations.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

open DifferentialModule

/-- The reversed equivalence between one-periodic complexes and differential modules is
additive. -/
private instance : (onePeriodicComplexEquivalence C).symm.functor.Additive :=
  inferInstanceAs (onePeriodicComplexEquivalence C).inverse.Additive

variable (E : ExactStructure C)

/-- The **componentwise exact structure** on differential modules: a short complex of
differential modules is a conflation when its underlying short complex is a conflation of `E`
(`TauCeti.ExactStructure.differentialModule_conflation_iff`). It is the degreewise exact
structure on one-periodic complexes, transported along
`TauCeti.DifferentialModule.onePeriodicComplexEquivalence`. -/
noncomputable def differentialModule : ExactStructure (DifferentialModule C) :=
  (E.homologicalComplex (ComplexShape.up (ZMod 1))).transport
    (onePeriodicComplexEquivalence C).symm

/-- A short complex of differential modules is a conflation for the componentwise exact
structure exactly when its underlying short complex is a conflation. -/
@[simp]
theorem differentialModule_conflation_iff (S : ShortComplex (DifferentialModule C)) :
    E.differentialModule.Conflation S ↔ E.Conflation (S.map (forget C)) := by
  rw [differentialModule, transport_conflation_iff]
  refine ((E.homologicalComplex _).conflation_iff_of_iso
    (S.mapNatIso (eqToIso onePeriodicComplexEquivalence_functor))).trans ?_
  rw [homologicalComplex_conflation_iff]
  -- In the unique degree, the one-periodic complex of `S` is its underlying short complex.
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- A morphism of differential modules is an inflation for the componentwise exact structure
exactly when its underlying morphism is an inflation. -/
@[simp]
theorem differentialModule_isInflation_iff {M N : DifferentialModule C} (φ : M ⟶ N) :
    E.differentialModule.IsInflation φ ↔ E.IsInflation φ.f := by
  rw [differentialModule, transport_isInflation_iff, Equivalence.symm_inverse,
    onePeriodicComplexEquivalence_functor, homologicalComplex_isInflation_iff]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- A morphism of differential modules is a deflation for the componentwise exact structure
exactly when its underlying morphism is a deflation. -/
@[simp]
theorem differentialModule_isDeflation_iff {M N : DifferentialModule C} (φ : M ⟶ N) :
    E.differentialModule.IsDeflation φ ↔ E.IsDeflation φ.f := by
  rw [differentialModule, transport_isDeflation_iff, Equivalence.symm_inverse,
    onePeriodicComplexEquivalence_functor, homologicalComplex_isDeflation_iff]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- The forgetful functor from differential modules preserves conflations. -/
theorem isConflationExact_forget_differentialModule :
    E.differentialModule.IsConflationExact E (forget C) :=
  ⟨fun hS ↦ (E.differentialModule_conflation_iff _).1 hS⟩

/-- Passing to one-periodic complexes preserves conflations. -/
theorem isConflationExact_toOnePeriodicComplex_differentialModule :
    E.differentialModule.IsConflationExact (E.homologicalComplex (ComplexShape.up (ZMod 1)))
      (toOnePeriodicComplex C) :=
  ⟨fun hS ↦ (homologicalComplex_conflation_iff _ _ _).2
    fun _ ↦ (E.differentialModule_conflation_iff _).1 hS⟩

/-- Passing from one-periodic complexes to differential modules preserves conflations. -/
theorem isConflationExact_ofOnePeriodicComplex_differentialModule :
    (E.homologicalComplex (ComplexShape.up (ZMod 1))).IsConflationExact E.differentialModule
      (ofOnePeriodicComplex C) :=
  ⟨fun hS ↦ (E.differentialModule_conflation_iff _).2
    ((homologicalComplex_conflation_iff _ _ _).1 hS 0)⟩

/-- The functor of `onePeriodicComplexEquivalence` preserves conflations. -/
private theorem isConflationExact_functor :
    E.differentialModule.IsConflationExact (E.homologicalComplex (ComplexShape.up (ZMod 1)))
      (onePeriodicComplexEquivalence C).functor :=
  E.isConflationExact_toOnePeriodicComplex_differentialModule.of_iso
    (eqToIso onePeriodicComplexEquivalence_functor.symm)

/-- The inverse of `onePeriodicComplexEquivalence` preserves conflations. -/
private theorem isConflationExact_inverse :
    (E.homologicalComplex (ComplexShape.up (ZMod 1))).IsConflationExact E.differentialModule
      (onePeriodicComplexEquivalence C).inverse :=
  E.isConflationExact_ofOnePeriodicComplex_differentialModule.of_iso
    (eqToIso onePeriodicComplexEquivalence_inverse.symm)

/-- Relative projectivity of a differential module is relative projectivity of its one-periodic
complex. -/
theorem differentialModule_isProjective_iff (M : DifferentialModule C) :
    E.differentialModule.isProjective M ↔
      (E.homologicalComplex (ComplexShape.up (ZMod 1))).isProjective
        ((toOnePeriodicComplex C).obj M) := by
  rw [← E.differentialModule.isProjective_map_equivalence_iff _ (onePeriodicComplexEquivalence C)
    E.isConflationExact_functor E.isConflationExact_inverse M,
    onePeriodicComplexEquivalence_functor]

/-- Relative injectivity of a differential module is relative injectivity of its one-periodic
complex. -/
theorem differentialModule_isInjective_iff (M : DifferentialModule C) :
    E.differentialModule.isInjective M ↔
      (E.homologicalComplex (ComplexShape.up (ZMod 1))).isInjective
        ((toOnePeriodicComplex C).obj M) := by
  rw [← E.differentialModule.isInjective_map_equivalence_iff _ (onePeriodicComplexEquivalence C)
    E.isConflationExact_functor E.isConflationExact_inverse M,
    onePeriodicComplexEquivalence_functor]

/-- The differential module of a relatively projective one-periodic complex is relatively
projective. -/
private theorem isProjective_ofOnePeriodicComplex_obj
    {Q : HomologicalComplex C (ComplexShape.up (ZMod 1))}
    (hQ : (E.homologicalComplex (ComplexShape.up (ZMod 1))).isProjective Q) :
    E.differentialModule.isProjective ((ofOnePeriodicComplex C).obj Q) := by
  have h := (E.homologicalComplex _).isProjective_map_equivalence_iff E.differentialModule
    (onePeriodicComplexEquivalence C).symm E.isConflationExact_inverse
    E.isConflationExact_functor Q
  rw [Equivalence.symm_functor, onePeriodicComplexEquivalence_inverse] at h
  exact h.2 hQ

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The one-periodic complex of a differential module `M` is contractible exactly when `M` admits
a contraction `h` with `d h + h d = 1`. -/
private theorem nonempty_homotopy_id_zero_iff (M : DifferentialModule C) :
    Nonempty (Homotopy (𝟙 ((toOnePeriodicComplex C).obj M)) 0) ↔
      ∃ h : M.X ⟶ M.X, M.d ≫ h + h ≫ M.d = 𝟙 M.X := by
  rw [← (toOnePeriodicComplex C).map_id, ← (toOnePeriodicComplex C).map_zero M M,
    nonempty_homotopy_toOnePeriodicComplex_map_iff]
  simp only [id_f, zero_f, add_zero, eq_comm]

/-- **The relatively projective differential modules are the contractible ones.** For the
componentwise split exact structure, a differential module `M` is relatively projective exactly
when there is `h : M.X ⟶ M.X` with `d h + h d = 1`. -/
theorem differentialModule_split_isProjective_iff (M : DifferentialModule C) :
    (split C).differentialModule.isProjective M ↔
      ∃ h : M.X ⟶ M.X, M.d ≫ h + h ≫ M.d = 𝟙 M.X := by
  rw [differentialModule_isProjective_iff,
    homologicalComplex_split_isProjective_iff (fun i ↦ ⟨i, Subsingleton.elim _ _⟩),
    nonempty_homotopy_id_zero_iff]

/-- **The relatively injective differential modules are the contractible ones.** For the
componentwise split exact structure, a differential module `M` is relatively injective exactly
when there is `h : M.X ⟶ M.X` with `d h + h d = 1`. -/
theorem differentialModule_split_isInjective_iff (M : DifferentialModule C) :
    (split C).differentialModule.isInjective M ↔
      ∃ h : M.X ⟶ M.X, M.d ≫ h + h ≫ M.d = 𝟙 M.X := by
  rw [differentialModule_isInjective_iff,
    homologicalComplex_split_isInjective_iff (fun i ↦ ⟨i, Subsingleton.elim _ _⟩),
    nonempty_homotopy_id_zero_iff]

/-- **Differential modules form a Frobenius exact category.** The componentwise split exact
structure on `DifferentialModule C` is Frobenius, and its projective-injective objects are the
contractible differential modules (`differentialModule_split_isProjective_iff`). -/
theorem differentialModule_split_isFrobenius : (split C).differentialModule.IsFrobenius :=
  (homologicalComplex_split_isFrobenius (fun j ↦ ⟨j, Subsingleton.elim _ _⟩)
    (fun i ↦ ⟨i, Subsingleton.elim _ _⟩)).of_equivalence
    (onePeriodicComplexEquivalence C).symm (split C).isConflationExact_inverse
    (split C).isConflationExact_functor

/-- For the componentwise split exact structure, a morphism `φ : M ⟶ N` of differential modules
factors through a relatively projective differential module exactly when it is null-homotopic:
`φ = d h + h d` for some `h : M.X ⟶ N.X`. -/
theorem differentialModule_split_factorsThrough_iff {M N : DifferentialModule C} (φ : M ⟶ N) :
    (split C).differentialModule.isProjective.FactorsThrough φ ↔
      ∃ h : M.X ⟶ N.X, φ.f = M.d ≫ h + h ≫ N.d := by
  constructor
  · intro hφ
    obtain ⟨P, hP, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff _ _).1 hφ
    obtain ⟨h, hh⟩ := (differentialModule_split_isProjective_iff P).1 hP
    -- A contraction of the middle term, conjugated by the two factors, is a null-homotopy.
    refine ⟨i.f ≫ h ≫ p.f, ?_⟩
    calc (i ≫ p).f = i.f ≫ (P.d ≫ h + h ≫ P.d) ≫ p.f := by rw [hh, Category.id_comp, comp_f]
      _ = _ := by
        simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Hom.comm,
          Hom.comm_assoc]
  · rintro ⟨h, hh⟩
    -- Transfer the null-homotopy to one-periodic complexes, where it factors through a
    -- contractible complex, and bring the factorization back.
    have hφ : Nonempty (Homotopy ((toOnePeriodicComplex C).map φ) 0) := by
      rw [← (toOnePeriodicComplex C).map_zero M N,
        nonempty_homotopy_toOnePeriodicComplex_map_iff]
      exact ⟨h, by simpa using hh⟩
    obtain ⟨Q, hQ, a, b, hab⟩ := (ObjectProperty.factorsThrough_iff _ _).1
      (homologicalComplex_split_factorsThrough_of_homotopy (fun i ↦ ⟨i, Subsingleton.elim _ _⟩)
        hφ.some)
    let eM : M ≅ (ofOnePeriodicComplex C).obj ((toOnePeriodicComplex C).obj M) :=
      isoMk (Iso.refl _) (by simp)
    let eN : N ≅ (ofOnePeriodicComplex C).obj ((toOnePeriodicComplex C).obj N) :=
      isoMk (Iso.refl _) (by simp)
    refine (ObjectProperty.factorsThrough_iff _ _).2 ⟨_,
      (split C).isProjective_ofOnePeriodicComplex_obj hQ,
      eM.hom ≫ (ofOnePeriodicComplex C).map a, (ofOnePeriodicComplex C).map b ≫ eN.inv, ?_⟩
    ext
    simp [eM, eN, ← HomologicalComplex.comp_f, ← hab]

end ExactStructure

end TauCeti
