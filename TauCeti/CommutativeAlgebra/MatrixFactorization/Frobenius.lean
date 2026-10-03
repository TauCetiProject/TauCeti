/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Exact
public import TauCeti.CommutativeAlgebra.MatrixFactorization.DiskFactorization
public import TauCeti.Algebra.Homology.Curved.Frobenius
public import TauCeti.CategoryTheory.Exact.FullSubcategory

/-!
# Matrix factorizations form a Frobenius exact category

The componentwise split exact structure on finite-projective matrix factorizations has enough
relative projectives and injectives, and both classes consist precisely of the contractible
factorizations. The disk sum on the components of a factorization supplies its injective
presentation; the disk sum on its parity shift supplies its projective presentation.
The kernels and cokernels stay finite projective because their components are direct summands
of the disk components.

A morphism factors through a relative projective exactly when it is null-homotopic.
Thus the stable category is additively and scalar-linearly equivalent to `HMF(S,w)`, here
`MatrixFactorization.HomotopyCategory`. This is an equivalence of additive categories; no
compatibility with a prescribed shift or cone triangulation is asserted here.

## References

* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and
  Weyl group actions*, Compos. Math. **141** (2005), Sections 2–3.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Sections 1.2 and 3.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, for the stable triangulation this Frobenius structure supports.

The construction restricts the disk presentations of
`TauCeti.Algebra.Homology.Curved.Frobenius` and uses `MorphismIdeal.lift` for the comparison.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Contractible matrix factorizations are relatively injective for the componentwise split
exact structure. -/
theorem splitExact_isInjective_of_mem_nullHomotopic {X : MatrixFactorization S w}
    (hX : 𝟙 X ∈ (nullHomotopic (S := S) (w := w)).hom X X) :
    (splitExact S w).isInjective X := by
  rw [splitExact_def]
  apply ExactStructure.isInjective_fullSubcategory_of_isInjective isExtensionClosed_isProjective
  apply ExactStructure.curvedDuplex_split_isInjective_of_mem_nullHomotopic
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff (𝟙 X)).mp hX
  exact CurvedDuplex.mem_nullHomotopic_iff.mpr
    ⟨h₀, h₁, by simpa only [ObjectProperty.FullSubcategory.id_hom] using hh⟩

/-- Contractible matrix factorizations are relatively projective for the componentwise split
exact structure. -/
theorem splitExact_isProjective_of_mem_nullHomotopic {X : MatrixFactorization S w}
    (hX : 𝟙 X ∈ (nullHomotopic (S := S) (w := w)).hom X X) :
    (splitExact S w).isProjective X := by
  rw [splitExact_def]
  apply ExactStructure.isProjective_fullSubcategory_of_isProjective isExtensionClosed_isProjective
  apply ExactStructure.curvedDuplex_split_isProjective_of_mem_nullHomotopic
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff (𝟙 X)).mp hX
  exact CurvedDuplex.mem_nullHomotopic_iff.mpr
    ⟨h₀, h₁, by simpa only [ObjectProperty.FullSubcategory.id_hom] using hh⟩

/-- The canonical embedding into the disk sum is a componentwise split inflation. -/
theorem splitExact_isInflation_toDiskSum (X : MatrixFactorization S w) :
    (splitExact S w).IsInflation (toDiskSum X) := by
  rw [splitExact_isInflation_iff]
  simpa only [toDiskSum_hom, diskSum_obj] using
    ExactStructure.curvedDuplex_split_isInflation_toDiskSum X.obj

private theorem exists_splitExact_isDeflation (X : MatrixFactorization S w) :
    ∃ (P : MatrixFactorization S w) (p : P ⟶ X),
      (splitExact S w).IsDeflation p ∧
        𝟙 P ∈ (nullHomotopic (S := S) (w := w)).hom P P := by
  refine ⟨diskSum (parityShift.obj X),
    fromDiskSum (X := parityShift.obj X) (-𝟙 X.obj.X₁) (𝟙 X.obj.X₀), ?_,
    id_diskSum_mem_nullHomotopic _⟩
  rw [splitExact_isDeflation_iff, ExactStructure.curvedDuplex_isDeflation_iff,
    fromDiskSum_hom_f₀, fromDiskSum_hom_f₁]
  simp only [parityShift_obj_X₀, parityShift_obj_X₁, Preadditive.neg_comp, Category.id_comp,
    neg_neg]
  exact ⟨ExactStructure.split_isDeflation_biprod_desc_id_left _,
    ExactStructure.split_isDeflation_biprod_desc_id_right _⟩

variable (S w)

/-- Every finite-projective matrix factorization embeds componentwise split into a
contractible finite-projective factorization. -/
theorem splitExact_enoughInjectives : (splitExact S w).EnoughInjectives := by
  refine ⟨fun X => ?_⟩
  obtain ⟨Z, p, hzero, hT⟩ :=
    (ConflationClass.isInflation_iff _ _).mp (splitExact_isInflation_toDiskSum X)
  exact ⟨⟨_, Z, _, p, hzero, hT,
    splitExact_isInjective_of_mem_nullHomotopic (id_diskSum_mem_nullHomotopic X)⟩⟩

/-- Every finite-projective matrix factorization is a componentwise split quotient of a
contractible finite-projective factorization. -/
theorem splitExact_enoughProjectives : (splitExact S w).EnoughProjectives := by
  refine ⟨fun X => ?_⟩
  obtain ⟨P, p, hp, hP⟩ := exists_splitExact_isDeflation X
  obtain ⟨Z, i, hzero, hT⟩ := (ConflationClass.isDeflation_iff _ _).mp hp
  exact ⟨⟨Z, _, i, p, hzero, hT, splitExact_isProjective_of_mem_nullHomotopic hP⟩⟩

variable {S w}

/-- The relative injectives are exactly the contractible finite-projective factorizations. -/
theorem splitExact_isInjective_iff (X : MatrixFactorization S w) :
    (splitExact S w).isInjective X ↔
      𝟙 X ∈ (nullHomotopic (S := S) (w := w)).hom X X := by
  refine ⟨fun hX => ?_, splitExact_isInjective_of_mem_nullHomotopic⟩
  obtain ⟨r, hr⟩ := ExactStructure.isInjective_iff.mp hX
    (splitExact_isInflation_toDiskSum X) (𝟙 X)
  exact (mem_nullHomotopic_iff_factors_diskSum _).mpr ⟨_, r, hr⟩

/-- The relative projectives are exactly the contractible finite-projective factorizations. -/
theorem splitExact_isProjective_iff (X : MatrixFactorization S w) :
    (splitExact S w).isProjective X ↔
      𝟙 X ∈ (nullHomotopic (S := S) (w := w)).hom X X := by
  refine ⟨fun hX => ?_, splitExact_isProjective_of_mem_nullHomotopic⟩
  obtain ⟨P, p, hp, hP⟩ := exists_splitExact_isDeflation X
  obtain ⟨s, hs⟩ := ExactStructure.isProjective_iff.mp hX hp (𝟙 X)
  simpa only [← hs, Category.id_comp, Category.comp_id] using
    (nullHomotopic (S := S) (w := w)).comp_mem_right p
      ((nullHomotopic (S := S) (w := w)).comp_mem_left s hP)

variable (S w)

/-- Finite-projective matrix factorizations form a Frobenius exact category, with contractible
factorizations as the projective-injective objects. No regularity assumption is needed. -/
theorem splitExact_isFrobenius : (splitExact S w).IsFrobenius where
  enoughProjectives := splitExact_enoughProjectives S w
  enoughInjectives := splitExact_enoughInjectives S w
  projective_iff_injective X := by
    rw [splitExact_isProjective_iff, splitExact_isInjective_iff]

/-- Stable factorization through a relative projective is exactly null-homotopy. -/
theorem splitExact_projectiveStableIdeal_eq :
    (splitExact S w).projectiveStableIdeal = nullHomotopic (S := S) (w := w) := by
  ext X Y f
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩
    simpa only [Category.comp_id] using
      (nullHomotopic (S := S) (w := w)).comp_mem_right p
        ((nullHomotopic (S := S) (w := w)).comp_mem_left i
          ((splitExact_isProjective_iff P).mp hP))
  · intro hf
    obtain ⟨a, b, rfl⟩ := (mem_nullHomotopic_iff_factors_diskSum f).mp hf
    exact ⟨diskSum X, splitExact_isProjective_of_mem_nullHomotopic
      (id_diskSum_mem_nullHomotopic X), a, b, rfl⟩

/-- The canonical stable-to-homotopy comparison sends a stable class to its homotopy class. -/
noncomputable def stableToHomotopy :
    (splitExact S w).ProjectiveStableCategory ⥤ HomotopyCategory (S := S) (w := w) :=
  (splitExact S w).projectiveStableIdeal.lift
    (nullHomotopic (S := S) (w := w)).quotientFunctor
    (by rw [MorphismIdeal.kerIdeal_quotientFunctor, splitExact_projectiveStableIdeal_eq])

/-- The comparison agrees with the homotopy quotient on matrix factorizations. -/
theorem projectiveStableFunctor_comp_stableToHomotopy :
    (splitExact S w).projectiveStableFunctor ⋙ stableToHomotopy S w =
      (nullHomotopic (S := S) (w := w)).quotientFunctor := by
  rw [stableToHomotopy, Quotient.lift_spec]

/-- On objects the comparison preserves the represented matrix factorization. -/
@[simp] theorem stableToHomotopy_obj (X : MatrixFactorization S w) :
    (stableToHomotopy S w).obj ((splitExact S w).projectiveStableFunctor.obj X) =
      (nullHomotopic (S := S) (w := w)).quotientFunctor.obj X := by
  rw [stableToHomotopy, Quotient.lift_obj_functor_obj]

/-- On morphisms the comparison takes the stable class to the homotopy class of the same map. -/
@[simp] theorem stableToHomotopy_map {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (stableToHomotopy S w).map ((splitExact S w).projectiveStableFunctor.map f) ≫
        eqToHom (stableToHomotopy_obj S w Y) =
      eqToHom (stableToHomotopy_obj S w X) ≫
        (nullHomotopic (S := S) (w := w)).quotientFunctor.map f := by
  rw [← Functor.comp_map,
    Functor.congr_hom (projectiveStableFunctor_comp_stableToHomotopy S w) f]
  simp

/-- The stable-to-homotopy comparison is additive. -/
instance : (stableToHomotopy S w).Additive := by
  unfold stableToHomotopy
  infer_instance

/-- The stable-to-homotopy comparison is scalar-linear. -/
instance : (stableToHomotopy S w).Linear S := by
  unfold stableToHomotopy
  infer_instance

/-- The comparison is an equivalence because the two quotients kill the same ideal. -/
instance : (stableToHomotopy S w).IsEquivalence := by
  unfold stableToHomotopy
  apply MorphismIdeal.isEquivalence_lift
  rw [MorphismIdeal.kerIdeal_quotientFunctor, splitExact_projectiveStableIdeal_eq]

/-- The stable category of finite-projective matrix factorizations with componentwise split
conflations is equivalent to their homotopy category `HMF(S,w)`. -/
noncomputable def stableHomotopyEquivalence :
    (splitExact S w).ProjectiveStableCategory ≌ HomotopyCategory (S := S) (w := w) :=
  (stableToHomotopy S w).asEquivalence

@[simp] theorem stableHomotopyEquivalence_functor :
    (stableHomotopyEquivalence S w).functor = stableToHomotopy S w := (rfl)

instance : (stableHomotopyEquivalence S w).functor.Additive := by
  rw [stableHomotopyEquivalence_functor]
  infer_instance

instance : (stableHomotopyEquivalence S w).functor.Linear S := by
  rw [stableHomotopyEquivalence_functor]
  infer_instance

/-- The inverse comparison sends the homotopy class of a factorization back to its stable
class, naturally in matrix factorizations. -/
noncomputable def homotopyQuotientCompStableInverseIso :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        (stableHomotopyEquivalence S w).inverse ≅
      (splitExact S w).projectiveStableFunctor :=
  (eqToIso (projectiveStableFunctor_comp_stableToHomotopy S w).symm).compInverseIso

end TauCeti.MatrixFactorization
