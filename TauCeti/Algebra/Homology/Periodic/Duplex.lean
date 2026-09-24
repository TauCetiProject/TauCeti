/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.Curved.Duplex

/-!
# Two-periodic complexes are curved duplexes of curvature zero

A curved duplex `X₀ --d₀--> X₁ --d₁--> X₀` of curvature `0` has both composites `d₀ ≫ d₁` and
`d₁ ≫ d₀` equal to zero, so it is the same datum as a two-periodic complex, that is a
`ZMod 2`-indexed complex for the shape `ComplexShape.up (ZMod 2)`, with `X₀` in degree `0`,
`X₁` in degree `1`, and `d₀`, `d₁` the two differentials. This file makes the identification
precise, so that the curvature-zero specialization of curved duplexes inherits Mathlib's
homological-complex vocabulary instead of duplicating it:

* `CurvedDuplex.periodicComplexEquivalence` is the equivalence between curved duplexes of
  curvature zero and two-periodic complexes, with functor `CurvedDuplex.toPeriodicComplex` and
  inverse `CurvedDuplex.ofPeriodicComplex`;
* `CurvedDuplex.nonempty_homotopy_toPeriodicComplex_map_iff` identifies the null-homotopic
  morphisms `d h + h d` of duplexes with the morphisms of two-periodic complexes homotopic to
  zero in Mathlib's sense, and `CurvedDuplex.kerIdeal_toPeriodicComplex_comp_quotient` restates
  this as an equality of ideals;
* `CurvedDuplex.HomotopyCategory.periodicComplexEquivalence` is the induced equivalence between
  the homotopy category of curved duplexes of curvature zero and Mathlib's homotopy category
  `HomotopyCategory C (ComplexShape.up (ZMod 2))` of two-periodic complexes; it restricts to
  `CurvedDuplex.toPeriodicComplex` along the quotient functors, and its inverse restricts to
  `CurvedDuplex.ofPeriodicComplex` up to the isomorphism
  `CurvedDuplex.HomotopyCategory.quotientCompPeriodicComplexEquivalenceInverseIso`.

A curved duplex of nonzero curvature is not a complex, and no such comparison is made for it.

## References

* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3 (curved complexes and
  duplexes and their homotopy categories).
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory Limits

namespace CurvedDuplex

variable (C : Type u) [Category.{v} C] [Preadditive C] (R : Type w') [Semiring R] [Linear R C]

-- The two functors are exposed, as is the category structure of curved duplexes: the components
-- of `toPeriodicComplex` in degrees `0` and `1` must unfold to those of the duplex, so that the
-- component lemmas below typecheck downstream.
@[expose] public section

/-- The two-periodic complex attached to a curved duplex of curvature zero: the even component
sits in degree `0`, the odd component in degree `1`, and the differentials are `d₀` and `d₁`. -/
@[implicit_reducible]
def toPeriodicComplex :
    CurvedDuplex C (0 : R) ⥤ HomologicalComplex C (ComplexShape.up (ZMod 2)) where
  obj X :=
    { X := fun
        | 0 => X.X₀
        | 1 => X.X₁
      d := fun
        | 0, 0 => 0
        | 0, 1 => X.d₀
        | 1, 0 => X.d₁
        | 1, 1 => 0
      shape := fun
        | 0, 0, _ => rfl
        | 0, 1, h => absurd rfl h
        | 1, 0, h => absurd rfl h
        | 1, 1, _ => rfl
      d_comp_d' := fun
        | 0, 0, _, _, _ => zero_comp
        | 0, 1, 0, _, _ => by simp
        | 0, 1, 1, _, _ => comp_zero
        | 1, 0, 0, _, _ => comp_zero
        | 1, 0, 1, _, _ => by simp
        | 1, 1, _, _, _ => zero_comp }
  map f :=
    { f := fun
        | 0 => f.f₀
        | 1 => f.f₁
      comm' := fun
        | 0, 0, _ => by simp
        | 0, 1, _ => f.comm₀
        | 1, 0, _ => f.comm₁
        | 1, 1, _ => by simp }
  map_id _ := by
    ext i
    match i with
    | 0 => rfl
    | 1 => rfl
  map_comp _ _ := by
    ext i
    match i with
    | 0 => rfl
    | 1 => rfl

/-- The curved duplex of curvature zero attached to a two-periodic complex `K`: its components
are `K.X 0` and `K.X 1`, and its differentials are `K.d 0 1` and `K.d 1 0`. -/
@[implicit_reducible, simps]
def ofPeriodicComplex :
    HomologicalComplex C (ComplexShape.up (ZMod 2)) ⥤ CurvedDuplex C (0 : R) where
  obj K :=
    { X₀ := K.X 0
      X₁ := K.X 1
      d₀ := K.d 0 1
      d₁ := K.d 1 0
      d₀_comp_d₁ := by simp
      d₁_comp_d₀ := by simp }
  map φ :=
    { f₀ := φ.f 0
      f₁ := φ.f 1 }

end

variable {C R}

@[simp]
theorem toPeriodicComplex_obj_X_zero (X : CurvedDuplex C (0 : R)) :
    ((toPeriodicComplex C R).obj X).X 0 = X.X₀ :=
  rfl

@[simp]
theorem toPeriodicComplex_obj_X_one (X : CurvedDuplex C (0 : R)) :
    ((toPeriodicComplex C R).obj X).X 1 = X.X₁ :=
  rfl

@[simp]
theorem toPeriodicComplex_obj_d_zero_one (X : CurvedDuplex C (0 : R)) :
    ((toPeriodicComplex C R).obj X).d 0 1 = X.d₀ :=
  rfl

@[simp]
theorem toPeriodicComplex_obj_d_one_zero (X : CurvedDuplex C (0 : R)) :
    ((toPeriodicComplex C R).obj X).d 1 0 = X.d₁ :=
  rfl

@[simp]
theorem toPeriodicComplex_map_f_zero {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    ((toPeriodicComplex C R).map f).f 0 = f.f₀ :=
  rfl

@[simp]
theorem toPeriodicComplex_map_f_one {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    ((toPeriodicComplex C R).map f).f 1 = f.f₁ :=
  rfl

instance : (toPeriodicComplex C R).Additive where
  map_add {_ _ _ _} := by
    ext i
    match i with
    | 0 => simp
    | 1 => simp

instance : (toPeriodicComplex C R).Linear R where
  map_smul {_ _ _ _} := by
    ext i
    match i with
    | 0 => simp
    | 1 => simp

instance : (ofPeriodicComplex C R).Additive where

instance : (ofPeriodicComplex C R).Linear R where

variable (C R)

-- The equivalence is exposed so that its functor and inverse unfold to `toPeriodicComplex` and
-- `ofPeriodicComplex`.
@[expose] public section

/-- **Curved duplexes of curvature zero are two-periodic complexes**: the functors
`toPeriodicComplex` and `ofPeriodicComplex` are mutually inverse equivalences. -/
@[simps functor inverse]
def periodicComplexEquivalence :
    CurvedDuplex C (0 : R) ≌ HomologicalComplex C (ComplexShape.up (ZMod 2)) where
  functor := toPeriodicComplex C R
  inverse := ofPeriodicComplex C R
  unitIso := NatIso.ofComponents (fun X ↦ isoMk (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  counitIso := NatIso.ofComponents
    (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun
        | 0 => Iso.refl _
        | 1 => Iso.refl _)
      (fun
        | 0, 0, h => absurd h (by decide)
        | 0, 1, _ => by simp
        | 1, 0, _ => by simp
        | 1, 1, h => absurd h (by decide)))
    (fun _ ↦ by
      ext i
      match i with
      | 0 => simp [HomologicalComplex.Hom.isoOfComponents]
      | 1 => simp [HomologicalComplex.Hom.isoOfComponents])
  functor_unitIso_comp _ := by
    ext i
    match i with
    | 0 => simp [HomologicalComplex.Hom.isoOfComponents]
    | 1 => simp [HomologicalComplex.Hom.isoOfComponents]

end

variable {C R}

instance : (toPeriodicComplex C R).IsEquivalence :=
  (periodicComplexEquivalence C R).isEquivalence_functor

instance : (ofPeriodicComplex C R).IsEquivalence :=
  (periodicComplexEquivalence C R).isEquivalence_inverse

/-! ### Homotopies -/

/-- A morphism of curved duplexes of curvature zero is null-homotopic, that is of the form
`d h + h d` for an odd map `h`, exactly when the corresponding morphism of two-periodic complexes
is homotopic to zero. -/
theorem nonempty_homotopy_toPeriodicComplex_map_iff {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    Nonempty (Homotopy ((toPeriodicComplex C R).map f) 0) ↔
      ∃ h₀ h₁, nullHomotopicMap h₀ h₁ = f := by
  have r₀₁ : (ComplexShape.up (ZMod 2)).Rel 0 1 := rfl
  have r₁₀ : (ComplexShape.up (ZMod 2)).Rel 1 0 := rfl
  constructor
  · rintro ⟨H⟩
    refine ⟨H.hom 0 1, H.hom 1 0, ?_⟩
    have h₀ := H.comm 0
    have h₁ := H.comm 1
    rw [dNext_eq _ r₀₁, prevD_eq _ r₁₀] at h₀
    rw [dNext_eq _ r₁₀, prevD_eq _ r₀₁] at h₁
    ext
    · simpa using h₀.symm
    · simpa using h₁.symm
  · rintro ⟨h₀, h₁, rfl⟩
    refine ⟨{ hom := fun
                | 0, 0 => 0
                | 0, 1 => h₀
                | 1, 0 => h₁
                | 1, 1 => 0
              zero := fun
                | 0, 0, _ => rfl
                | 0, 1, h => absurd r₁₀ h
                | 1, 0, h => absurd r₀₁ h
                | 1, 1, _ => rfl
              comm := fun
                | 0 => by rw [dNext_eq _ r₀₁, prevD_eq _ r₁₀]; simp
                | 1 => by rw [dNext_eq _ r₁₀, prevD_eq _ r₀₁]; simp }⟩

/-- The null-homotopic morphisms of curved duplexes of curvature zero are exactly the morphisms
sent to zero in Mathlib's homotopy category of two-periodic complexes. -/
theorem kerIdeal_toPeriodicComplex_comp_quotient :
    (toPeriodicComplex C R ⋙
        _root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).kerIdeal =
      nullHomotopic C (0 : R) := by
  ext X Y f
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map, _root_.HomotopyCategory.quotient_map_eq_zero_iff,
    nonempty_homotopy_toPeriodicComplex_map_iff, mem_nullHomotopic_iff]

/-! ### The homotopy category -/

namespace HomotopyCategory

variable (C R) in
/-- The functor from the homotopy category of curved duplexes of curvature zero to the homotopy
category of two-periodic complexes induced by `toPeriodicComplex`. -/
noncomputable abbrev toPeriodicComplex :
    HomotopyCategory C (0 : R) ⥤ _root_.HomotopyCategory C (ComplexShape.up (ZMod 2)) :=
  (nullHomotopic C (0 : R)).lift _ kerIdeal_toPeriodicComplex_comp_quotient.ge

instance : (toPeriodicComplex C R).Faithful := by
  refine Functor.faithful_of_comp_essSurj _ (nullHomotopic C (0 : R)).quotientFunctor
    fun X Y f g hfg ↦ ?_
  obtain ⟨f, rfl⟩ := (nullHomotopic C (0 : R)).quotientFunctor.map_surjective f
  obtain ⟨g, rfl⟩ := (nullHomotopic C (0 : R)).quotientFunctor.map_surjective g
  simp only [Quotient.lift_map_functor_map] at hfg
  rw [MorphismIdeal.quotientFunctor_map_eq_iff, ← kerIdeal_toPeriodicComplex_comp_quotient,
    Functor.mem_kerIdeal_hom, Functor.map_sub, hfg, sub_self]

instance : (toPeriodicComplex C R).Full :=
  Functor.full_of_comp_essSurj _ (nullHomotopic C (0 : R)).quotientFunctor fun _ _ φ ↦
    ⟨(nullHomotopic C (0 : R)).quotientFunctor.map
      ((CurvedDuplex.toPeriodicComplex C R ⋙ _root_.HomotopyCategory.quotient _ _).preimage φ),
      (CurvedDuplex.toPeriodicComplex C R ⋙ _root_.HomotopyCategory.quotient _ _).map_preimage φ⟩

instance : (toPeriodicComplex C R).EssSurj where
  mem_essImage K := by
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (CurvedDuplex.toPeriodicComplex C R ⋙ _root_.HomotopyCategory.quotient _ _) K
    exact ⟨(nullHomotopic C (0 : R)).quotientFunctor.obj X, ⟨e⟩⟩

instance : (toPeriodicComplex C R).IsEquivalence where

variable (C R) in
/-- The homotopy category of curved duplexes of curvature zero is equivalent to Mathlib's
homotopy category of two-periodic complexes, through the functor induced by
`CurvedDuplex.toPeriodicComplex`. -/
noncomputable def periodicComplexEquivalence :
    HomotopyCategory C (0 : R) ≌ _root_.HomotopyCategory C (ComplexShape.up (ZMod 2)) :=
  (toPeriodicComplex C R).asEquivalence

/-- The equivalence of homotopy categories is induced by `CurvedDuplex.toPeriodicComplex`. -/
theorem quotientFunctor_comp_periodicComplexEquivalence_functor :
    (nullHomotopic C (0 : R)).quotientFunctor ⋙ (periodicComplexEquivalence C R).functor =
      CurvedDuplex.toPeriodicComplex C R ⋙
        _root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2)) :=
  Quotient.lift_spec _ _ fun _ _ _ _ h ↦
    (nullHomotopic C (0 : R)).map_eq_of_rel _ kerIdeal_toPeriodicComplex_comp_quotient.ge h

/-- The inverse of the equivalence of homotopy categories is induced by
`CurvedDuplex.ofPeriodicComplex`. -/
noncomputable def quotientCompPeriodicComplexEquivalenceInverseIso :
    _root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2)) ⋙
        (periodicComplexEquivalence C R).inverse ≅
      ofPeriodicComplex C R ⋙ (nullHomotopic C (0 : R)).quotientFunctor :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (CurvedDuplex.periodicComplexEquivalence C R).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ofPeriodicComplex C R)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (eqToIso quotientFunctor_comp_periodicComplexEquivalence_functor.symm) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (periodicComplexEquivalence C R).unitIso.symm ≪≫
        Functor.rightUnitor _)

end HomotopyCategory

end CurvedDuplex

end TauCeti
