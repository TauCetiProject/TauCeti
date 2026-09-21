/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Opposite
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# Relative injectives in an exact category

This file develops injectivity relative to a Quillen exact structure. An object is injective when
maps into it extend across the inflations of the chosen structure. Thus the notion depends on the
exact structure: every object is injective for the split structure, while the canonical structure
on an abelian category recovers Mathlib's ordinary injective objects.

Relative injectivity is the formal dual of relative projectivity. The equivalence is made explicit
by `TauCeti.ExactStructure.isInjective_iff_isProjective_op`, so results about projectives can be
transported through the opposite exact structure without maintaining parallel hypotheses.

The splitting API is also dual. A conflation whose first term is injective splits because its
inflation has a retraction.

The bundled `TauCeti.ExactStructure.InjectivePresentation` records a conflation into a relatively
injective object, and `TauCeti.ExactStructure.EnoughInjectives` says that every object admits one.
A morphism of the presented objects extends to the injective middle terms and hence induces a
morphism of the cokernel terms; both are recorded as
`TauCeti.ExactStructure.InjectivePresentation.middleMap` and
`TauCeti.ExactStructure.InjectivePresentation.cokernelMap`. They depend on a choice of extension,
which only the stable quotient removes.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Sections 11–12.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

/-- The objects injective relative to `E`: maps into such an object extend across every inflation
of the exact structure. -/
def isInjective (E : ExactStructure C) : ObjectProperty C := fun I =>
  ∀ ⦃X Y : C⦄ {i : X ⟶ Y}, E.IsInflation i → ∀ f : X ⟶ I, ∃ g : Y ⟶ I, i ≫ g = f

/-- The defining extension property for relative injectivity. -/
theorem isInjective_iff {I : C} :
    E.isInjective I ↔
      ∀ ⦃X Y : C⦄ {i : X ⟶ Y}, E.IsInflation i → ∀ f : X ⟶ I, ∃ g : Y ⟶ I, i ≫ g = f :=
  Iff.rfl

namespace isInjective

/-- The chosen extension of `f : X ⟶ I` across an inflation `i : X ⟶ Y`. -/
noncomputable def factorThru {I : C} (hI : E.isInjective I) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (f : X ⟶ I) : Y ⟶ I :=
  (hI hi f).choose

@[reassoc (attr := simp)]
theorem comp_factorThru {I : C} (hI : E.isInjective I) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (f : X ⟶ I) : i ≫ hI.factorThru hi f = f :=
  (hI hi f).choose_spec

end isInjective

/-- Relative injectives are closed under retracts. -/
instance : (E.isInjective).IsStableUnderRetracts where
  of_retract r hI _ _ _ hi f :=
    ⟨hI.factorThru hi (f ≫ r.i) ≫ r.r, by simp⟩

/-- A zero object is injective relative to every exact structure. -/
instance : (E.isInjective).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    intro _ _ _ _ f
    exact ⟨0, (isZero_zero C).eq_of_tgt _ f⟩⟩

/-- A binary direct sum of relatively injective objects is relatively injective. -/
theorem isInjective_biprod {I₁ I₂ : C} (h₁ : E.isInjective I₁) (h₂ : E.isInjective I₂) :
    E.isInjective (I₁ ⊞ I₂) := by
  intro X Y i hi f
  refine ⟨biprod.lift (h₁.factorThru hi (f ≫ biprod.fst))
    (h₂.factorThru hi (f ≫ biprod.snd)), ?_⟩
  apply biprod.hom_ext <;> simp

/-- Relative injectives are closed under binary products; in a preadditive category these are
biproducts. -/
instance : (E.isInjective).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod (E.isInjective)
    fun _ _ h₁ h₂ ↦ isInjective_biprod h₁ h₂

/-- A conflation with injective first term splits. The retraction of its inflation is the extension
of the identity of that term. -/
noncomputable def splittingOfInjective (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) : S.Splitting :=
  let r := h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁)
  let h := E.isKernelCokernelPair S hS
  {
    r := r
    s := h.desc (𝟙 S.X₂ - r ≫ S.f) (by
      dsimp only [r]
      simp)
    f_r := h₁.comp_factorThru (E.isInflation_f hS) (𝟙 S.X₁)
    s_g := by
      have := h.epi_g
      rw [← cancel_epi S.g]
      simp
    id := by simp
  }

@[simp]
theorem splittingOfInjective_r (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) :
    (E.splittingOfInjective hS h₁).r =
      h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁) :=
  (rfl)

@[simp]
theorem splittingOfInjective_s (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.isInjective S.X₁) :
    (E.splittingOfInjective hS h₁).s = (E.isKernelCokernelPair S hS).desc
      (𝟙 S.X₂ - h₁.factorThru (E.isInflation_f hS) (𝟙 S.X₁) ≫ S.f) (by simp) :=
  (rfl)

/-- Every object is injective for the split exact structure. -/
@[simp]
theorem split_isInjective (X : C) : (ExactStructure.split C).isInjective X := by
  intro Y Z i hi f
  obtain ⟨W, e, he⟩ := (ExactStructure.split_isInflation_iff i).mp hi
  exact ⟨e.hom ≫ biprod.fst ≫ f, by simp only [← Category.assoc, he, biprod.inl_fst,
    Category.id_comp]⟩

/-- For the canonical exact structure of an abelian category, relative injectivity is Mathlib's
ordinary categorical injectivity. -/
@[simp]
theorem abelian_isInjective_iff {A : Type u} [Category.{v} A] [Abelian A] (X : A) :
    (ExactStructure.abelian A).isInjective X ↔ Injective X := by
  constructor
  · exact fun h ↦ ⟨fun f i hi ↦ h ((abelian_isInflation_iff i).mpr hi) f⟩
  · intro h Y Z i hi f
    have : Mono i := (abelian_isInflation_iff i).mp hi
    exact h.factors f i

/-- An injective presentation of `X` relative to `E` is a conflation `X → I → K` whose
middle term is `E`-injective. -/
structure InjectivePresentation (E : ExactStructure C) (X : C) where
  /-- The relatively injective middle term. -/
  I : C
  /-- The cokernel term of the presentation. -/
  K : C
  /-- The inflation from the presented object. -/
  i : X ⟶ I
  /-- The deflation from the injective term. -/
  p : I ⟶ K
  /-- The two presentation maps form a short complex. -/
  zero : i ≫ p = 0
  /-- The presentation is a conflation of `E`. -/
  conflation : E.Conflation (ShortComplex.mk i p zero)
  /-- The middle term is injective relative to `E`. -/
  isInjective : E.isInjective I

/-- An exact structure has enough injectives if every object admits a relative injective
presentation. -/
structure EnoughInjectives (E : ExactStructure C) : Prop where
  presentation : ∀ X : C, Nonempty (E.InjectivePresentation X)

namespace InjectivePresentation

/-- The tautological injective presentation in the split exact structure. -/
noncomputable def split (X : C) : (ExactStructure.split C).InjectivePresentation X where
  I := X
  K := 0
  i := 𝟙 X
  p := 0
  zero := by simp
  conflation := (ExactStructure.split C).conflation_id_zero X
  isInjective := split_isInjective X

@[simp] theorem split_I (X : C) : (split X).I = X := (rfl)

@[simp] theorem split_K (X : C) : (split X).K = 0 := (rfl)

@[simp] theorem split_i (X : C) : HEq (split X).i (𝟙 X) := (HEq.rfl)

@[simp] theorem split_p (X : C) : HEq (split X).p (0 : X ⟶ (0 : C)) := (HEq.rfl)

/-- Mathlib's injective presentation gives a relative injective presentation for the canonical
exact structure of an abelian category. -/
noncomputable def abelian {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    (ExactStructure.abelian A).InjectivePresentation X where
  I := Injective.under X
  K := cokernel (Injective.ι X)
  i := Injective.ι X
  p := cokernel.π (Injective.ι X)
  zero := cokernel.condition _
  conflation := abelian_conflation_of_mono _
  isInjective := (abelian_isInjective_iff _).mpr inferInstance

@[simp] theorem abelian_I {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    (abelian X).I = Injective.under X := (rfl)

@[simp] theorem abelian_K {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    (abelian X).K = cokernel (Injective.ι X) := (rfl)

@[simp] theorem abelian_i {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    HEq (abelian X).i (Injective.ι X) := (HEq.rfl)

@[simp] theorem abelian_p {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    HEq (abelian X).p (cokernel.π (Injective.ι X)) := (HEq.rfl)

section Comparison

variable {X Y : C}

/-- The extension of `f : X ⟶ Y` to the injective middle terms of relative injective
presentations `P` of `X` and `Q` of `Y`, chosen by relative injectivity of `Q.I`. -/
noncomputable def middleMap (P : E.InjectivePresentation X) (Q : E.InjectivePresentation Y)
    (f : X ⟶ Y) : P.I ⟶ Q.I :=
  Q.isInjective.factorThru (E.isInflation_f P.conflation) (f ≫ Q.i)

/-- The chosen extension of `f` does extend `f` across the two inflations. -/
@[reassoc (attr := simp)]
theorem i_comp_middleMap (P : E.InjectivePresentation X) (Q : E.InjectivePresentation Y)
    (f : X ⟶ Y) : P.i ≫ P.middleMap Q f = f ≫ Q.i :=
  Q.isInjective.comp_factorThru (E.isInflation_f P.conflation) (f ≫ Q.i)

/-- The morphism induced by `f : X ⟶ Y` on the cokernel terms of relative injective
presentations, through the chosen extension `TauCeti.ExactStructure.InjectivePresentation.middleMap`
of the injective middle terms. -/
noncomputable def cokernelMap (P : E.InjectivePresentation X) (Q : E.InjectivePresentation Y)
    (f : X ⟶ Y) : P.K ⟶ Q.K :=
  (E.isKernelCokernelPair _ P.conflation).desc (P.middleMap Q f ≫ Q.p) (by
    rw [← Category.assoc, P.i_comp_middleMap, Category.assoc, Q.zero, comp_zero])

/-- The induced morphism on cokernel terms makes the square on the two deflations commute. -/
@[reassoc (attr := simp)]
theorem p_comp_cokernelMap (P : E.InjectivePresentation X) (Q : E.InjectivePresentation Y)
    (f : X ⟶ Y) : P.p ≫ P.cokernelMap Q f = P.middleMap Q f ≫ Q.p :=
  (E.isKernelCokernelPair _ P.conflation).g_desc _ _

end Comparison

end InjectivePresentation

/-- The split exact structure has enough relative injectives. -/
theorem split_enoughInjectives : (ExactStructure.split C).EnoughInjectives :=
  ⟨fun X ↦ ⟨InjectivePresentation.split X⟩⟩

/-- Enough ordinary injectives give enough relative injectives for the canonical exact structure
on an abelian category. -/
theorem abelian_enoughInjectives {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] : (ExactStructure.abelian A).EnoughInjectives :=
  ⟨fun X ↦ ⟨InjectivePresentation.abelian X⟩⟩

namespace EnoughInjectives

/-- Choose a relative injective presentation from enough relative injectives. -/
noncomputable def injectivePresentation (h : E.EnoughInjectives) (X : C) :
    E.InjectivePresentation X :=
  (h.presentation X).some

end EnoughInjectives

/-- Relative injectivity in `C` is relative projectivity in the opposite exact category. -/
theorem isInjective_iff_isProjective_op (I : C) :
    E.isInjective I ↔ E.op.isProjective (Opposite.op I) := by
  constructor
  · rw [isProjective_iff]
    intro hI X Y p hp f
    rw [isInjective_iff] at hI
    obtain ⟨g, hg⟩ := hI ((E.op_isDeflation_iff p).mp hp) f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩
  · rw [isInjective_iff]
    intro hI X Y i hi f
    rw [isProjective_iff] at hI
    obtain ⟨g, hg⟩ := hI ((E.op_isDeflation_iff i.op).mpr (by simpa)) f.op
    exact ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

/-- Relative projectivity in `C` is relative injectivity in the opposite exact category. -/
theorem isProjective_iff_isInjective_op (P : C) :
    E.isProjective P ↔ E.op.isInjective (Opposite.op P) := by
  constructor
  · rw [isInjective_iff]
    intro hP X Y i hi f
    rw [isProjective_iff] at hP
    obtain ⟨g, hg⟩ := hP ((E.op_isInflation_iff i).mp hi) f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩
  · rw [isProjective_iff]
    intro hP X Y p hp f
    rw [isInjective_iff] at hP
    obtain ⟨g, hg⟩ := hP ((E.op_isInflation_iff p.op).mpr (by simpa)) f.op
    exact ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

namespace InjectivePresentation

/-- An injective presentation in `C` is a projective presentation in `Cᵒᵖ`. -/
def op {X : C} (P : E.InjectivePresentation X) :
    E.op.ProjectivePresentation (Opposite.op X) where
  K := Opposite.op P.K
  P := Opposite.op P.I
  i := P.p.op
  p := P.i.op
  zero := by simpa using congrArg Quiver.Hom.op P.zero
  conflation := (E.op_conflation_op_iff _).mpr P.conflation
  isProjective := (E.isInjective_iff_isProjective_op P.I).mp P.isInjective

/-- Unopposing an injective presentation gives a projective presentation. -/
def unop {X : Cᵒᵖ} (P : E.op.InjectivePresentation X) :
    E.ProjectivePresentation X.unop where
  K := P.K.unop
  P := P.I.unop
  i := P.p.unop
  p := P.i.unop
  zero := by simpa using congrArg Quiver.Hom.unop P.zero
  conflation := (E.op_conflation _).mp P.conflation
  isProjective := (E.isProjective_iff_isInjective_op P.I.unop).mpr P.isInjective

end InjectivePresentation

namespace ProjectivePresentation

/-- A projective presentation in `C` is an injective presentation in `Cᵒᵖ`. -/
def op {X : C} (P : E.ProjectivePresentation X) :
    E.op.InjectivePresentation (Opposite.op X) where
  I := Opposite.op P.P
  K := Opposite.op P.K
  i := P.p.op
  p := P.i.op
  zero := by simpa using congrArg Quiver.Hom.op P.zero
  conflation := (E.op_conflation_op_iff _).mpr P.conflation
  isInjective := (E.isProjective_iff_isInjective_op P.P).mp P.isProjective

/-- Unopposing a projective presentation gives an injective presentation. -/
def unop {X : Cᵒᵖ} (P : E.op.ProjectivePresentation X) :
    E.InjectivePresentation X.unop where
  I := P.P.unop
  K := P.K.unop
  i := P.p.unop
  p := P.i.unop
  zero := by simpa using congrArg Quiver.Hom.unop P.zero
  conflation := (E.op_conflation _).mp P.conflation
  isInjective := (E.isInjective_iff_isProjective_op P.P.unop).mpr P.isProjective

end ProjectivePresentation

/-- Enough relative injectives in `C` are equivalent to enough relative projectives in `Cᵒᵖ`. -/
theorem enoughInjectives_iff_op_enoughProjectives :
    E.EnoughInjectives ↔ E.op.EnoughProjectives := by
  constructor
  · intro h
    exact ⟨fun X ↦ ⟨(h.injectivePresentation X.unop).op⟩⟩
  · intro h
    exact ⟨fun X ↦ ⟨(h.projectivePresentation (Opposite.op X)).unop⟩⟩

/-- Enough relative projectives in `C` are equivalent to enough relative injectives in `Cᵒᵖ`. -/
theorem enoughProjectives_iff_op_enoughInjectives :
    E.EnoughProjectives ↔ E.op.EnoughInjectives := by
  constructor
  · intro h
    exact ⟨fun X ↦ ⟨(h.projectivePresentation X.unop).op⟩⟩
  · intro h
    exact ⟨fun X ↦ ⟨(h.injectivePresentation (Opposite.op X)).unop⟩⟩

end ExactStructure

end TauCeti
