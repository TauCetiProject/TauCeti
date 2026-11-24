/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# The K-flat left derivability structure from functorial flat covers

Let `C` be an abelian monoidal preadditive category in which cochain tensor products exist. This
file defines the object property `CochainComplex.kFlat C` and full subcategory
`CochainComplex.KFlat C` of K-flat cochain complexes in `C`, together with the class
`CochainComplex.KFlat.quasiIso C` of quasi-isomorphisms between K-flat complexes and the inclusion
localizer morphism `CochainComplex.KFlat.localizerMorphism C`.

Suppose countable coproducts and sequential colimits in `C` are exact and commute with tensoring on
the right, and `C` carries a functor `E : C ⥤ C` and a natural transformation `p : E ⟶ 𝟭 C` such
that every `p.app X` is an epimorphism and every `E.obj X` is flat. Then the functorial
cell-attachment resolution `CochainComplex.kFlatResolutionFunctor E p` from
`TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution` lands in `CochainComplex.KFlat C`, and every
component of `CochainComplex.kFlatResolutionNatTrans E p` is a quasi-isomorphism. Consequently,
`CochainComplex.KFlat.localizerMorphism C` admits left resolutions of arrows, induces an equivalence
on localized categories, has connected left-resolution categories, and forms a left derivability
structure.

## Main definitions

* `CochainComplex.kFlat`, `CochainComplex.KFlat`: the object property and full subcategory of
  K-flat cochain complexes in `C`.
* `CochainComplex.KFlat.quasiIso`, `CochainComplex.KFlat.localizerMorphism`: quasi-isomorphisms of
  K-flat complexes and the induced localizer morphism to `CochainComplex C ℤ`.

## Main results

* `CochainComplex.KFlat.hasLeftResolutions_arrow_localizerMorphism`,
  `CochainComplex.KFlat.isLocalizedEquivalence_localizerMorphism`,
  `CochainComplex.KFlat.isConnected_leftResolution_localizerMorphism`,
  `CochainComplex.KFlat.isLeftDerivabilityStructure_localizerMorphism`: when countable coproducts
  and sequential colimits in `C` are exact and commute with tensoring on the right and `C` admits a
  functorial flat epimorphic cover `(E, p)`, `CochainComplex.KFlat.localizerMorphism C` is a left
  derivability structure.
* `CochainComplex.exists_quasiIso_isKFlat_of_hasLeftResolutions`: when the K-flat localizer
  morphism has left resolutions, every cochain complex receives a quasi-isomorphism from a K-flat
  complex.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* Joël Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42.
* [The Stacks Project][stacks], Section 15.60, Lemmas 15.60.5 and 15.60.10 (Tags 06Y2 and 06Y4).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The object property on `CochainComplex C ℤ` selecting K-flat complexes. -/
protected def kFlat : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ K.IsKFlat

@[simp]
lemma kFlat_iff {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L] (K : CochainComplex C ℤ) :
    CochainComplex.kFlat C K ↔ K.IsKFlat := (Iff.rfl)

instance : (CochainComplex.kFlat C).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    rw [kFlat_iff] at hK ⊢
    exact isKFlat_of_iso e

instance : (CochainComplex.kFlat C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    rw [kFlat_iff] at hK
    rw [ObjectProperty.prop_shift_iff, kFlat_iff]
    infer_instance⟩

/-- The full subcategory of `CochainComplex C ℤ` consisting of K-flat complexes. -/
abbrev KFlat := (CochainComplex.kFlat C).FullSubcategory

namespace KFlat

/-- Bundle a K-flat cochain complex as an object of `CochainComplex.KFlat C`. -/
def mk {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    (K : CochainComplex C ℤ) [hK : K.IsKFlat] : KFlat C :=
  ⟨K, hK⟩

@[simp]
lemma mk_obj {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    (K : CochainComplex C ℤ) [K.IsKFlat] :
    (mk K).obj = K := (rfl)

/-- The fully faithful inclusion of K-flat cochain complexes into all cochain complexes. -/
abbrev ι : KFlat C ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι (CochainComplex.kFlat C)

instance {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L] (K : KFlat C) : K.obj.IsKFlat :=
  K.property

/-- Quasi-isomorphisms in the full subcategory of K-flat cochain complexes. -/
def quasiIso : MorphismProperty (KFlat C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (ι C)

@[simp]
lemma quasiIso_iff {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [∀ K L : CochainComplex C ℤ, HasTensor K L]
    {K L : KFlat C} (f : K ⟶ L) :
    quasiIso C f ↔ QuasiIso f.hom := (Iff.rfl)

instance : (quasiIso C).ContainsIdentities := by
  dsimp [quasiIso]
  infer_instance

instance : (quasiIso C).IsMultiplicative := by
  dsimp [quasiIso]
  infer_instance

instance : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

/-- The localizer morphism given by the inclusion `CochainComplex.KFlat C ⥤ CochainComplex C ℤ`
with respect to quasi-isomorphisms. -/
def localizerMorphism :
    LocalizerMorphism (quasiIso C) (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := ι C
  map _ _ _ h := h

@[simp]
lemma localizerMorphism_functor :
    (localizerMorphism C).functor = ι C := (rfl)

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance : (localizerMorphism C).functor.Full := by
  rw [localizerMorphism_functor]
  infer_instance

instance : (localizerMorphism C).functor.Faithful := by
  rw [localizerMorphism_functor]
  infer_instance

section DerivabilityStructure

variable {C}
variable (E : C ⥤ C) (p : E ⟶ 𝟭 C)
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
  [∀ X : C, Epi (p.app X)]
  [∀ X : C, PreservesFiniteLimits (tensorLeft (E.obj X))]
  [∀ X : C, PreservesFiniteColimits (tensorLeft (E.obj X))]

private def liftedResolutionFunctor : CochainComplex C ℤ ⥤ KFlat C :=
  (CochainComplex.kFlat C).lift (kFlatResolutionFunctor E p) fun K ↦ by
    rw [kFlat_iff]
    infer_instance

include E p

/-- When countable coproducts and sequential colimits in `C` are exact and commute with tensoring on
the right and `(E, p)` is a functorial flat epimorphic cover, the K-flat localizer morphism admits
left resolutions in the category of arrows. -/
theorem hasLeftResolutions_arrow_localizerMorphism :
    (localizerMorphism C).arrow.HasLeftResolutions :=
  (localizerMorphism C).hasLeftResolutions_arrow_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    fun K ↦ (HomologicalComplex.mem_quasiIso_iff _).2 (quasiIso_kFlatResolutionNatTrans_app E p K)

/-- When countable coproducts and sequential colimits in `C` are exact and commute with tensoring on
the right and `(E, p)` is a functorial flat epimorphic cover, the inclusion of K-flat complexes
induces an equivalence on localized categories with respect to quasi-isomorphisms. -/
theorem isLocalizedEquivalence_localizerMorphism :
    (localizerMorphism C).IsLocalizedEquivalence :=
  (localizerMorphism C).isLocalizedEquivalence_of_functorial_left_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (fun K ↦ (HomologicalComplex.mem_quasiIso_iff _).2
      (quasiIso_kFlatResolutionNatTrans_app E p K)) rfl

/-- When countable coproducts and sequential colimits in `C` are exact and commute with tensoring on
the right and `(E, p)` is a functorial flat epimorphic cover, the category of K-flat left
resolutions of every cochain complex `K` is connected. -/
theorem isConnected_leftResolution_localizerMorphism (K : CochainComplex C ℤ) :
    IsConnected ((localizerMorphism C).LeftResolution K) :=
  (localizerMorphism C).isConnected_leftResolution_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (fun L ↦ (HomologicalComplex.mem_quasiIso_iff _).2
      (quasiIso_kFlatResolutionNatTrans_app E p L)) K

/-- **The K-flat left derivability structure.** When countable coproducts and sequential colimits in
`C` are exact and commute with tensoring on the right and `(E, p)` is a functorial flat epimorphic
cover, `CochainComplex.KFlat.localizerMorphism C` is a left derivability structure. -/
theorem isLeftDerivabilityStructure_localizerMorphism :
    (localizerMorphism C).IsLeftDerivabilityStructure :=
  (localizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (fun K ↦ (HomologicalComplex.mem_quasiIso_iff _).2
      (quasiIso_kFlatResolutionNatTrans_app E p K)) rfl

end DerivabilityStructure

end KFlat

variable {C} in
/-- If the K-flat localizer morphism has left resolutions, every cochain complex receives a
quasi-isomorphism from a K-flat complex. -/
theorem exists_quasiIso_isKFlat_of_hasLeftResolutions
    [(KFlat.localizerMorphism C).HasLeftResolutions] (K : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ K), QuasiIso π ∧ P.IsKFlat := by
  obtain ⟨@⟨X₁, π, hπ⟩⟩ := ‹(KFlat.localizerMorphism C).HasLeftResolutions› K
  exact ⟨X₁.obj, π, (mem_quasiIso_iff π).1 hπ, X₁.property⟩

end CochainComplex
