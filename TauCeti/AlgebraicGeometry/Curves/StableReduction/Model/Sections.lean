/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Extending markings to proper models

Every rational point of the prescribed generic fibre of a proper model over a discrete valuation
ring extends uniquely to a section. The extension uses the model's chosen generic-fibre
identification, and is compatible with morphisms of proper models. Equivalently, sections of the
model are in bijection with rational points of that generic fibre.

This extends each marking separately. Distinct generic markings can meet on the special fibre,
and their extensions need not pass through the relative smooth locus.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 10.
* R. Hartshorne, *Algebraic Geometry*, Theorem II.4.7 (the valuative criterion of properness).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

private def sectionSquare (M : Model R K C toK) (p : Spec (.of K) ⟶ C)
    (hp : p ≫ toK = 𝟙 _) : ValuativeCommSq M.toBase where
  R := R
  K := K
  i₁ := p ≫ M.genericι
  i₂ := 𝟙 _
  commSq := ⟨by simp [reassoc_of% hp]⟩

/-- A rational point of the prescribed generic fibre of a proper model extends uniquely to a
section. The equality on the generic fibre uses the model's prescribed identification. -/
theorem existsUnique_section (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) :
    ∃! s : Spec (.of R) ⟶ M.total,
      s ≫ M.toBase = 𝟙 _ ∧
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = p ≫ M.genericι := by
  have hv : ValuativeCriterion M.toBase := by
    have h : AlgebraicGeometry.IsProper M.toBase := inferInstance
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨h⟩ := hv (sectionSquare M p hp)
  refine ⟨h.default.l, ⟨h.default.fac_right, h.default.fac_left⟩, ?_⟩
  intro s hs
  exact congrArg CommSq.LiftStruct.l (h.uniq ⟨s, hs.2, hs.1⟩)

/-- The unique section extending a rational point of the prescribed generic fibre. -/
def extendSection (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) : Spec (.of R) ⟶ M.total :=
  (M.existsUnique_section p hp).choose

/-- The extension is a section of the model's structure morphism. -/
@[reassoc (attr := simp)]
theorem extendSection_toBase (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) :
    M.extendSection p hp ≫ M.toBase = 𝟙 _ :=
  (M.existsUnique_section p hp).choose_spec.1.1

/-- The extension restricts to the given rational point on the prescribed generic fibre. -/
@[reassoc (attr := simp)]
theorem specMap_extendSection (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ M.extendSection p hp = p ≫ M.genericι :=
  (M.existsUnique_section p hp).choose_spec.1.2

/-- Any section with the prescribed generic value is the extension. -/
theorem eq_extendSection (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _)
    (s : Spec (.of R) ⟶ M.total) (hs : s ≫ M.toBase = 𝟙 _)
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = p ≫ M.genericι) :
    s = M.extendSection p hp :=
  (M.existsUnique_section p hp).choose_spec.2 s ⟨hs, hgen⟩

/-- Restrict a section to the prescribed generic fibre. -/
def genericSection (M : Model R K C toK)
    (s : Spec (.of R) ⟶ M.total) (hs : s ≫ M.toBase = 𝟙 _) : Spec (.of K) ⟶ C :=
  M.isPullback_genericι.lift
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s) (𝟙 _) (by simp [hs])

/-- Restriction of a section is a rational point over the fraction field. -/
@[reassoc (attr := simp)]
theorem genericSection_toK (M : Model R K C toK)
    (s : Spec (.of R) ⟶ M.total) (hs : s ≫ M.toBase = 𝟙 _) :
    M.genericSection s hs ≫ toK = 𝟙 _ :=
  M.isPullback_genericι.lift_snd _ _ _

/-- Restriction uses the prescribed generic-fibre inclusion. -/
@[reassoc (attr := simp)]
theorem genericSection_genericι (M : Model R K C toK)
    (s : Spec (.of R) ⟶ M.total) (hs : s ≫ M.toBase = 𝟙 _) :
    M.genericSection s hs ≫ M.genericι =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s :=
  M.isPullback_genericι.lift_fst _ _ _

/-- Restricting an extended section recovers the rational point. -/
@[simp]
theorem genericSection_extendSection (M : Model R K C toK) [M.IsProper]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) :
    M.genericSection (M.extendSection p hp) (M.extendSection_toBase p hp) = p := by
  apply M.isPullback_genericι.hom_ext <;> simp [hp]

/-- Extending the generic value of an existing section recovers that section. -/
@[simp]
theorem extendSection_genericSection (M : Model R K C toK) [M.IsProper]
    (s : Spec (.of R) ⟶ M.total) (hs : s ≫ M.toBase = 𝟙 _) :
    M.extendSection (M.genericSection s hs) (M.genericSection_toK s hs) = s := by
  exact (M.eq_extendSection _ _ s hs (M.genericSection_genericι s hs).symm).symm

/-- Sections of a proper model correspond to rational points of its prescribed generic fibre. -/
def sectionEquiv (M : Model R K C toK) [M.IsProper] :
    {s : Spec (.of R) ⟶ M.total // s ≫ M.toBase = 𝟙 _} ≃
      {p : Spec (.of K) ⟶ C // p ≫ toK = 𝟙 _} where
  toFun s := ⟨M.genericSection s.1 s.2, M.genericSection_toK s.1 s.2⟩
  invFun p := ⟨M.extendSection p.1 p.2, M.extendSection_toBase p.1 p.2⟩
  left_inv s := Subtype.ext (M.extendSection_genericSection s.1 s.2)
  right_inv p := Subtype.ext (M.genericSection_extendSection p.1 p.2)

@[simp]
theorem sectionEquiv_apply (M : Model R K C toK) [M.IsProper]
    (s : {s : Spec (.of R) ⟶ M.total // s ≫ M.toBase = 𝟙 _}) :
    (M.sectionEquiv s).1 = M.genericSection s.1 s.2 :=
  (rfl)

@[simp]
theorem sectionEquiv_symm_apply (M : Model R K C toK) [M.IsProper]
    (p : {p : Spec (.of K) ⟶ C // p ≫ toK = 𝟙 _}) :
    (M.sectionEquiv.symm p).1 = M.extendSection p.1 p.2 :=
  (rfl)

/-- A morphism between proper models carries an extended marking to the same extended marking. -/
@[reassoc (attr := simp)]
theorem extendSection_hom {M N : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : M ⟶ N) (p : Spec (.of K) ⟶ C) (hp : p ≫ toK = 𝟙 _) :
    M.extendSection p hp ≫ f.hom = N.extendSection p hp := by
  apply N.eq_extendSection p hp <;> simp

end TauCeti.Model
