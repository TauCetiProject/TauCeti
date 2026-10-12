/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.DiskFactorization
public import TauCeti.Algebra.Homology.Curved.Exact
public import TauCeti.CategoryTheory.Exact.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Curved duplexes with the componentwise split exact structure are Frobenius

Let `C` be an `R`-linear additive category and `w : R`. The componentwise split exact structure
`(ExactStructure.split C).curvedDuplex w` on curved duplexes of curvature `w` has as conflations
the short complexes of curved duplexes which split in both components, not necessarily
compatibly with the differentials. This file proves that it is a Frobenius exact structure whose
projective and injective objects are exactly the contractible duplexes, those whose identity is
null-homotopic, and that its stable category is the homotopy category
`CurvedDuplex.HomotopyCategory C w`.

The proofs use the elementary disks of `TauCeti.Algebra.Homology.Curved.DiskFactorization`.
Every duplex `X` embeds by a componentwise split inflation into the contractible disk sum
`CurvedDuplex.diskSum X`, and the disk sum of its parity shift maps onto it by a componentwise
split deflation. A contractible duplex extends maps across componentwise split inflations and
lifts them along componentwise split deflations, through the null-homotopic map built from a
contraction and the componentwise retractions or sections.

Since the structure is Frobenius, its stable category is triangulated by Happel's theorem
`TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`. Matrix factorizations of `w` over a
commutative ring `S` are the curved duplexes in `ModuleCat S` with finitely generated projective
components, and the disks on such components are again matrix factorizations. At `w = 0` the
result is the curved-duplex counterpart of the two-periodic case of
`TauCeti.ExactStructure.homologicalComplex_split_isFrobenius`.

## Main results

* `TauCeti.ExactStructure.curvedDuplex_split_isInjective_iff` and
  `TauCeti.ExactStructure.curvedDuplex_split_isProjective_iff`: the relatively injective and
  relatively projective curved duplexes are the contractible ones.
* `TauCeti.ExactStructure.curvedDuplex_split_isFrobenius`: the componentwise split exact
  structure on curved duplexes is Frobenius.
* `TauCeti.ExactStructure.curvedDuplex_split_projectiveStableIdeal_eq`: a morphism of curved
  duplexes factors through a relative projective exactly when it is null-homotopic.
* `TauCeti.ExactStructure.curvedDuplexSplitStableHomotopyEquivalence`: the stable category of
  the componentwise split exact structure is equivalent to the homotopy category of curved
  duplexes, through the comparison `TauCeti.ExactStructure.curvedDuplexSplitStableToHomotopy`
  which sends the stable class of a morphism to its homotopy class.

## References

* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3, for curved complexes and
  duplexes, their disks and their homotopy categories.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1, for the corresponding statement on complexes with the
  componentwise split exact structure.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CurvedDuplex

universe w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R}

namespace ExactStructure

/-- A contractible curved duplex is relatively injective for the componentwise split exact
structure. -/
theorem curvedDuplex_split_isInjective_of_mem_nullHomotopic {X : CurvedDuplex C w}
    (h : 𝟙 X ∈ (nullHomotopic C w).hom X X) : ((split C).curvedDuplex w).isInjective X := by
  obtain ⟨h₀, h₁, hh⟩ := mem_nullHomotopic_iff.1 h
  refine isInjective_iff.2 fun A B i hi g => ?_
  rw [curvedDuplex_isInflation_iff] at hi
  have := isSplitMono_of_split_isInflation hi.1
  have := isSplitMono_of_split_isInflation hi.2
  -- The retractions of the components of `i` need not commute with the differentials, but
  -- composing them with a contraction of `X` gives a morphism of curved duplexes.
  refine ⟨nullHomotopicMap (retraction i.f₀ ≫ g.f₀ ≫ h₀) (retraction i.f₁ ≫ g.f₁ ≫ h₁), ?_⟩
  simp only [comp_nullHomotopicMap, IsSplitMono.id_assoc]
  rw [← comp_nullHomotopicMap, hh, Category.comp_id]

/-- A contractible curved duplex is relatively projective for the componentwise split exact
structure. -/
theorem curvedDuplex_split_isProjective_of_mem_nullHomotopic {X : CurvedDuplex C w}
    (h : 𝟙 X ∈ (nullHomotopic C w).hom X X) : ((split C).curvedDuplex w).isProjective X := by
  obtain ⟨h₀, h₁, hh⟩ := mem_nullHomotopic_iff.1 h
  refine isProjective_iff.2 fun A B p hp g => ?_
  rw [curvedDuplex_isDeflation_iff] at hp
  have := isSplitEpi_of_split_isDeflation hp.1
  have := isSplitEpi_of_split_isDeflation hp.2
  -- The sections of the components of `p` need not commute with the differentials, but
  -- composing them with a contraction of `X` gives a morphism of curved duplexes.
  refine ⟨nullHomotopicMap (h₀ ≫ g.f₁ ≫ section_ p.f₁) (h₁ ≫ g.f₀ ≫ section_ p.f₀), ?_⟩
  simp only [nullHomotopicMap_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]
  rw [← nullHomotopicMap_comp, hh, Category.id_comp]

/-- The canonical map from a curved duplex into the disk sum on its components is a
componentwise split inflation. -/
theorem curvedDuplex_split_isInflation_toDiskSum (X : CurvedDuplex C w) :
    ((split C).curvedDuplex w).IsInflation (toDiskSum X) := by
  rw [curvedDuplex_isInflation_iff, toDiskSum_f₀, toDiskSum_f₁]
  exact ⟨split_isInflation_biprod_lift_id_right _, split_isInflation_biprod_lift_id_left _⟩

/-- Every curved duplex is a componentwise split quotient of a contractible one, the disk sum
on the components of its parity shift. -/
theorem exists_curvedDuplex_split_isDeflation (X : CurvedDuplex C w) :
    ∃ (P : CurvedDuplex C w) (p : P ⟶ X),
      ((split C).curvedDuplex w).IsDeflation p ∧ 𝟙 P ∈ (nullHomotopic C w).hom P P := by
  refine ⟨diskSum ((parityShift C w).obj X),
    fromDiskSum (X := (parityShift C w).obj X) (-𝟙 X.X₁) (𝟙 X.X₀), ?_,
    id_diskSum_mem_nullHomotopic _⟩
  rw [curvedDuplex_isDeflation_iff, fromDiskSum_f₀, fromDiskSum_f₁]
  simp only [parityShift_obj_X₀, parityShift_obj_X₁, Preadditive.neg_comp, Category.id_comp,
    neg_neg]
  exact ⟨split_isDeflation_biprod_desc_id_left _, split_isDeflation_biprod_desc_id_right _⟩

variable (C w)

/-- Every curved duplex is a componentwise split subobject of a contractible one, the disk sum on
its components. -/
theorem curvedDuplex_split_enoughInjectives : ((split C).curvedDuplex w).EnoughInjectives := by
  refine ⟨fun X => ?_⟩
  obtain ⟨Z, p, zero, hS⟩ :=
    (ConflationClass.isInflation_iff _ _).1 (curvedDuplex_split_isInflation_toDiskSum X)
  exact ⟨⟨_, Z, _, p, zero, hS,
    curvedDuplex_split_isInjective_of_mem_nullHomotopic (id_diskSum_mem_nullHomotopic X)⟩⟩

/-- Every curved duplex is a componentwise split quotient of a contractible one. -/
theorem curvedDuplex_split_enoughProjectives : ((split C).curvedDuplex w).EnoughProjectives := by
  refine ⟨fun X => ?_⟩
  obtain ⟨P, p, hp, h⟩ := exists_curvedDuplex_split_isDeflation X
  obtain ⟨Z, i, zero, hS⟩ := (ConflationClass.isDeflation_iff _ _).1 hp
  exact ⟨⟨Z, _, i, p, zero, hS, curvedDuplex_split_isProjective_of_mem_nullHomotopic h⟩⟩

variable {C w}

/-- **The relatively injective curved duplexes are the contractible ones.** For the
componentwise split exact structure, a curved duplex is relatively injective exactly when its
identity is null-homotopic. -/
theorem curvedDuplex_split_isInjective_iff (X : CurvedDuplex C w) :
    ((split C).curvedDuplex w).isInjective X ↔ 𝟙 X ∈ (nullHomotopic C w).hom X X := by
  refine ⟨fun hX => ?_, curvedDuplex_split_isInjective_of_mem_nullHomotopic⟩
  -- `X` is a retract of the disk sum on its components, which is contractible.
  obtain ⟨r, hr⟩ := isInjective_iff.1 hX (curvedDuplex_split_isInflation_toDiskSum X) (𝟙 X)
  exact (mem_nullHomotopic_iff_factors_diskSum _).2 ⟨_, r, hr⟩

/-- **The relatively projective curved duplexes are the contractible ones.** For the
componentwise split exact structure, a curved duplex is relatively projective exactly when its
identity is null-homotopic. -/
theorem curvedDuplex_split_isProjective_iff (X : CurvedDuplex C w) :
    ((split C).curvedDuplex w).isProjective X ↔ 𝟙 X ∈ (nullHomotopic C w).hom X X := by
  refine ⟨fun hX => ?_, curvedDuplex_split_isProjective_of_mem_nullHomotopic⟩
  -- `X` is a retract of a contractible duplex covering it.
  obtain ⟨P, p, hp, h⟩ := exists_curvedDuplex_split_isDeflation X
  obtain ⟨s, hs⟩ := isProjective_iff.1 hX hp (𝟙 X)
  simpa only [← hs, Category.id_comp, Category.comp_id] using
    (nullHomotopic C w).comp_mem_right p ((nullHomotopic C w).comp_mem_left s h)

variable (C w)

/-- **Curved duplexes form a Frobenius exact category.** The componentwise split exact
structure on curved duplexes of curvature `w` is Frobenius, and its projective-injective objects
are the contractible duplexes (`curvedDuplex_split_isProjective_iff`). -/
theorem curvedDuplex_split_isFrobenius : ((split C).curvedDuplex w).IsFrobenius where
  enoughProjectives := curvedDuplex_split_enoughProjectives C w
  enoughInjectives := curvedDuplex_split_enoughInjectives C w
  projective_iff_injective X := by
    rw [curvedDuplex_split_isProjective_iff, curvedDuplex_split_isInjective_iff]

/-- A morphism of curved duplexes factors through a relative projective of the componentwise
split exact structure exactly when it is null-homotopic: the projective stable ideal is the
ideal of null-homotopic morphisms. -/
theorem curvedDuplex_split_projectiveStableIdeal_eq :
    ((split C).curvedDuplex w).projectiveStableIdeal = nullHomotopic C w := by
  ext X Y f
  rw [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩
    simpa only [Category.comp_id] using (nullHomotopic C w).comp_mem_right p
      ((nullHomotopic C w).comp_mem_left i ((curvedDuplex_split_isProjective_iff P).1 hP))
  · intro hf
    obtain ⟨a, b, rfl⟩ := (mem_nullHomotopic_iff_factors_diskSum f).1 hf
    exact ⟨diskSum X, curvedDuplex_split_isProjective_of_mem_nullHomotopic
      (id_diskSum_mem_nullHomotopic X), a, b, rfl⟩

/-- The projective stable ideal of the componentwise split exact structure is the kernel of the
quotient functor to the homotopy category of curved duplexes. -/
theorem curvedDuplex_split_projectiveStableIdeal_eq_kerIdeal :
    ((split C).curvedDuplex w).projectiveStableIdeal =
      (nullHomotopic C w).quotientFunctor.kerIdeal := by
  rw [MorphismIdeal.kerIdeal_quotientFunctor, curvedDuplex_split_projectiveStableIdeal_eq]

/-- The canonical comparison from the componentwise split stable category of curved duplexes to
their homotopy category, sending the stable class of a morphism to its homotopy class. -/
noncomputable def curvedDuplexSplitStableToHomotopy :
    ((split C).curvedDuplex w).ProjectiveStableCategory ⥤ CurvedDuplex.HomotopyCategory C w :=
  ((split C).curvedDuplex w).projectiveStableIdeal.lift (nullHomotopic C w).quotientFunctor
    (curvedDuplex_split_projectiveStableIdeal_eq_kerIdeal C w).le

/-- The comparison restricts to the homotopy quotient on curved duplexes. -/
theorem projectiveStableFunctor_comp_curvedDuplexSplitStableToHomotopy :
    ((split C).curvedDuplex w).projectiveStableFunctor ⋙ curvedDuplexSplitStableToHomotopy C w =
      (nullHomotopic C w).quotientFunctor := by
  rw [curvedDuplexSplitStableToHomotopy, Quotient.lift_spec]

/-- The comparison sends the stable image of a curved duplex to its image in the homotopy
category. -/
@[simp]
theorem curvedDuplexSplitStableToHomotopy_obj_projectiveStableFunctor_obj (X : CurvedDuplex C w) :
    (curvedDuplexSplitStableToHomotopy C w).obj
        (((split C).curvedDuplex w).projectiveStableFunctor.obj X) =
      (nullHomotopic C w).quotientFunctor.obj X :=
  Functor.congr_obj (projectiveStableFunctor_comp_curvedDuplexSplitStableToHomotopy C w) X

/-- The comparison sends the stable class of a morphism to its homotopy class, up to the
identification of objects `curvedDuplexSplitStableToHomotopy_obj_projectiveStableFunctor_obj`. -/
theorem curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map {X Y : CurvedDuplex C w}
    (f : X ⟶ Y) :
    (curvedDuplexSplitStableToHomotopy C w).map
        (((split C).curvedDuplex w).projectiveStableFunctor.map f) =
      eqToHom (curvedDuplexSplitStableToHomotopy_obj_projectiveStableFunctor_obj C w X) ≫
        (nullHomotopic C w).quotientFunctor.map f ≫
          eqToHom (curvedDuplexSplitStableToHomotopy_obj_projectiveStableFunctor_obj C w Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_curvedDuplexSplitStableToHomotopy C w) f

/-- The stable-to-homotopy comparison preserves addition of morphisms. -/
instance : (curvedDuplexSplitStableToHomotopy C w).Additive := by
  unfold curvedDuplexSplitStableToHomotopy
  infer_instance

/-- The stable-to-homotopy comparison preserves the scalars of the linear structure. -/
instance : (curvedDuplexSplitStableToHomotopy C w).Linear R := by
  unfold curvedDuplexSplitStableToHomotopy
  infer_instance

/-- The comparison is an equivalence: the stable quotient and the homotopy quotient kill the same
morphisms. -/
instance : (curvedDuplexSplitStableToHomotopy C w).IsEquivalence := by
  unfold curvedDuplexSplitStableToHomotopy
  exact MorphismIdeal.isEquivalence_lift _ _ _
    (curvedDuplex_split_projectiveStableIdeal_eq_kerIdeal C w).ge

/-- The stable category of the componentwise split exact structure on curved duplexes is
equivalent to the homotopy category of curved duplexes. -/
noncomputable def curvedDuplexSplitStableHomotopyEquivalence :
    ((split C).curvedDuplex w).ProjectiveStableCategory ≌ CurvedDuplex.HomotopyCategory C w :=
  (curvedDuplexSplitStableToHomotopy C w).asEquivalence

/-- The functor of the stable/homotopy equivalence is the canonical comparison. -/
@[simp]
theorem curvedDuplexSplitStableHomotopyEquivalence_functor :
    (curvedDuplexSplitStableHomotopyEquivalence C w).functor =
      curvedDuplexSplitStableToHomotopy C w :=
  (rfl)

end ExactStructure

end TauCeti
