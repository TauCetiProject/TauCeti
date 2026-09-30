/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Rational points of a scheme over a base

A `k`-rational point of a scheme `X` over a field `k` is a morphism `Spec k ⟶ X` over `Spec k`,
that is, a *section* of the structure morphism `f : X ⟶ Spec k`. This file records what such a
section gives at the level of points and residue fields. The residue-degree results hold for a
section `s` of an arbitrary morphism of schemes `f : X ⟶ S`, with hypothesis `s ≫ f = 𝟙 S`.
Stalk evaluation is surjective over any commutative local ring; the final results identify residue
fields and global functions over a field.

## Main results

* `residueDegree_eq_one_of_section`: the residue degree of `f` at a point in the image of a
  section is `1`. Over `S = Spec k` this is the statement `[κ(x₀) : k] = 1` at a `k`-rational
  point `x₀`, and it is the reason a rational point is the right normalization datum.
* `residueFieldIsoOfSection`: consequently the residue field of `X` at such a point *is* the
  residue field of the base, `κ(y) ≅ κ(s y)`, with inverse the residue-field map of `s`.
* `residueDegree_comp_of_section`: residue degrees over a further base are computed on the base,
  `[κ(s y) : κ(g y)] = [κ(y) : κ(g y)]` for `g : S ⟶ Z`.
* `residueFieldRingEquivOfSection`: over a base `Spec K` with `K` a field, the residue field at a
  `K`-rational point *is* `K`, through the evaluation map that Mathlib attaches to any `K`-point,
  `X.descResidueField (Scheme.stalkClosedPointTo s)`. The section hypothesis makes that map
  bijective (`descResidueField_bijective_of_section`), which is what lets a `K`-rational point
  transport `K`-structures to the fibre data at the point.
* `appTop_bijective_of_section`: if moreover `X` is integral and universally closed over `Spec K`,
  a `K`-rational point forces the global functions of `X` to be the constants, that is,
  `f.appTop : Γ(Spec K, ⊤) ⟶ Γ(X, ⊤)` is bijective. Mathlib's `isField_of_universallyClosed`
  makes `Γ(X, ⊤)` a field, and evaluation at the point is a retraction of `f.appTop`.

The divisor-level consequences live in `TauCeti.AlgebraicGeometry.RationalPoint.Degree`, which
keeps the results here independent of Weil divisor theory. They are the geometric source of the
weight-one base point hypothesis in divisor degree theory: the weight of a point of a curve over
`k` is its residue degree `[κ(x) : k]`, and both the class-group splitting
`OrderSystem.classGroupAddEquivPicZeroProdInt` and the Abel-Jacobi class
`OrderSystem.weightedAbelJacobiClass` require a base point of weight one.

No external mathematics is vendored; the proofs reuse Mathlib's `Scheme.Hom.residueFieldMap`,
`Scheme.residueFieldCongr` and `Scheme.Hom.residueDegree` API, `CategoryTheory.asIso` and
`CategoryTheory.Iso.inv_ext` for the isomorphism, Mathlib's `Scheme.descResidueField`,
`Scheme.stalkClosedPointTo` and `Scheme.residue_descResidueField` for the rational-point
evaluation map, and Tau Ceti's `residueDegree_comp` and `residueDegree_eq_one_iff`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-! ### Points in the image of a section -/

/-- On underlying points, a section of `f` is a right inverse of `f`. -/
lemma leftInverse_of_section (hs : s ≫ f = 𝟙 S) : Function.LeftInverse f s := fun y ↦ by
  have h : (s ≫ f).base y = (𝟙 S : S ⟶ S).base y := by rw [hs]
  simpa using h

/-- A section of `f` is a one-sided inverse of `f` at every point of the base. -/
@[simp]
lemma section_apply (hs : s ≫ f = 𝟙 S) (y : S) : f (s y) = y :=
  leftInverse_of_section hs y

/-! ### Residue degrees at a section -/

/-- The two residue degrees attached to a section multiply to one: the residue-field extensions
`κ(y) → κ(s y) → κ(y)` compose to the identity of `κ(y)`. -/
private lemma residueDegree_mul_residueDegree_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) * s.residueDegree y = 1 := by
  rw [← residueDegree_comp s f y, hs, Scheme.Hom.residueDegree_id]

/-- The residue degree of `f` at a point in the image of a section is one.

For `S = Spec k` this says that a `k`-rational point `x₀` of `X` has residue field `κ(x₀)` of
degree one over `k`. -/
@[simp]
theorem residueDegree_eq_one_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) = 1 :=
  Nat.dvd_one.mp ⟨_, (residueDegree_mul_residueDegree_of_section hs y).symm⟩

-- `section_apply` and `residueDegree_eq_one_of_section` above are the normal-form lemmas of this
-- file and carry `@[simp]`; their consequences are deliberately *not* annotated. `simpNF` rejects
-- `@[simp]` on `residueDegree_section_eq_one` outright, since its `f` cannot be inferred from the
-- left-hand side so the lemma would never apply, and reports the other consequences as already
-- provable by `simp` from the two lemmas above — `simp [hs]` reaches them with no annotation.

/-- A section has residue degree one at every point of the base. -/
theorem residueDegree_section_eq_one (hs : s ≫ f = 𝟙 S) (y : S) :
    s.residueDegree y = 1 := by
  have h := residueDegree_mul_residueDegree_of_section hs y
  rwa [residueDegree_eq_one_of_section hs y, Nat.one_mul] at h

/-- Residue degrees over a further base are computed on the base: at a point in the image of a
section of `f : X ⟶ S`, the residue degree of `f ≫ g` agrees with that of `g : S ⟶ Z`. -/
theorem residueDegree_comp_of_section (hs : s ≫ f = 𝟙 S) (g : S ⟶ Z) (y : S) :
    (f ≫ g).residueDegree (s y) = g.residueDegree y := by
  rw [residueDegree_comp, residueDegree_eq_one_of_section hs, Nat.mul_one, section_apply hs]

/-! ### Residue fields at a section -/

/-- The residue-field map of `f` at a point in the image of a section is bijective. -/
theorem residueFieldMap_bijective_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (f.residueFieldMap (s y)) :=
  (residueDegree_eq_one_iff f (s y)).mp (residueDegree_eq_one_of_section hs y)

/-- The residue-field map of a section is bijective at every point of the base. -/
theorem residueFieldMap_section_bijective (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (s.residueFieldMap y) :=
  (residueDegree_eq_one_iff s y).mp (residueDegree_section_eq_one hs y)

/-- The residue-field map of `f` at a point in the image of a section is an isomorphism. -/
lemma isIso_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (f.residueFieldMap (s y)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (residueFieldMap_bijective_of_section hs y)

/-- The residue-field map of a section is an isomorphism at every point of the base. -/
lemma isIso_residueFieldMap_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (s.residueFieldMap y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (residueFieldMap_section_bijective hs y)

/-- The residue-field map of `f` at a point in the image of a section, followed by the
residue-field map of the section, is the identity of `κ(y)`. -/
lemma residueFieldMap_comp_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    (S.residueFieldCongr (section_apply hs y).symm).hom ≫
        f.residueFieldMap (s y) ≫ s.residueFieldMap y = 𝟙 (S.residueField y) := by
  rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hs y]
  simp only [Scheme.residueFieldMap_id]
  exact (S.residueFieldCongr (section_apply hs y)).inv_hom_id

/-- The residue field of `X` at a point in the image of a section is the residue field of the
base at the corresponding point of the base. The inverse is the residue-field map of the
section. -/
noncomputable def residueFieldIsoOfSection (hs : s ≫ f = 𝟙 S) (y : S) :
    S.residueField y ≅ X.residueField (s y) :=
  haveI := isIso_residueFieldMap_of_section hs y
  asIso ((S.residueFieldCongr (section_apply hs y).symm).hom ≫ f.residueFieldMap (s y))

-- The isomorphism is intentionally not `@[expose]`, so downstream modules cannot unfold it; the
-- two lemmas below are its public characterization, which keeps consumers from having to rely on
-- the definitional unfolding.

/-- The forward map of `residueFieldIsoOfSection` is the residue-field map of `f`, transported
along `f (s y) = y`. -/
@[simp]
lemma residueFieldIsoOfSection_hom (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).hom =
      (S.residueFieldCongr (section_apply hs y).symm).hom ≫ f.residueFieldMap (s y) :=
  (rfl)

/-- The inverse of `residueFieldIsoOfSection` is the residue-field map of the section. -/
@[simp]
lemma residueFieldIsoOfSection_inv (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).inv = s.residueFieldMap y :=
  Iso.inv_ext <| by
    rw [residueFieldIsoOfSection_hom, Category.assoc,
      residueFieldMap_comp_residueFieldMap_of_section hs y]

/-! ### Stalk evaluation over a local ring -/

section OverLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of R)} {s : Spec (.of R) ⟶ X}

/-- A section over a commutative local ring `R` induces a surjection from the stalk at the
image of the closed point of `Spec R` onto `R`. -/
lemma stalkClosedPointTo_surjective_of_section (hs : s ≫ f = 𝟙 (Spec (.of R))) :
    Function.Surjective (Scheme.stalkClosedPointTo s) := by
  -- The hypothesis is used through a universally quantified morphism, since the *type* of
  -- `Scheme.stalkClosedPointTo t` depends on `t`; substituting `t := 𝟙 _` avoids a transport.
  have key : ∀ t : Spec (.of R) ⟶ Spec (.of R), t = 𝟙 (Spec (.of R)) →
      Function.Surjective (Scheme.stalkClosedPointTo t) := by
    rintro t rfl
    have H : ∀ x : (Spec (.of R) : Scheme.{u}),
        IsIso (Scheme.Hom.stalkMap (𝟙 (Spec (.of R))) x) := fun _ ↦ inferInstance
    have : IsIso (Scheme.stalkClosedPointTo (𝟙 (Spec (.of R)))) := by
      rw [Scheme.stalkClosedPointTo]
      have := H (IsLocalRing.closedPoint R)
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hcomp := key _ hs
  rw [Scheme.stalkClosedPointTo_comp] at hcomp
  exact Function.Surjective.of_comp hcomp

end OverLocalRing

/-! ### The residue field at a rational point

Over a field `K`, the residue field at a rational point is canonically isomorphic to `K`
through the evaluation map `X.descResidueField (Scheme.stalkClosedPointTo s)`. -/

section OverField

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {s : Spec (.of K) ⟶ X}

/-- The canonical evaluation map `κ(s 0) ⟶ K` at a `K`-rational point is bijective: it is
injective as a map of fields, and surjective because the stalk already surjects onto `K`. -/
lemma descResidueField_bijective_of_section (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    Function.Bijective (X.descResidueField (Scheme.stalkClosedPointTo s)) := by
  refine ⟨(X.descResidueField (Scheme.stalkClosedPointTo s)).hom.injective, fun k ↦ ?_⟩
  obtain ⟨a, ha⟩ := stalkClosedPointTo_surjective_of_section hs k
  refine ⟨X.residue _ a, ?_⟩
  rw [← ha, ← ConcreteCategory.comp_apply, Scheme.residue_descResidueField]

/-- The residue field of `X` at a `K`-rational point is canonically the ground field `K`, through
the evaluation map of the point. -/
noncomputable def residueFieldRingEquivOfSection (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    IsLocalRing.ResidueField (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) ≃+* K :=
  RingEquiv.ofBijective (X.descResidueField (Scheme.stalkClosedPointTo s)).hom
    (descResidueField_bijective_of_section hs)

/-- `residueFieldRingEquivOfSection` is the evaluation map of the rational point. -/
@[simp]
lemma residueFieldRingEquivOfSection_apply (hs : s ≫ f = 𝟙 (Spec (.of K)))
    (z : IsLocalRing.ResidueField (X.presheaf.stalk (s (IsLocalRing.closedPoint K)))) :
    residueFieldRingEquivOfSection hs z =
      X.descResidueField (Scheme.stalkClosedPointTo s) z :=
  (rfl)

/-- **Global functions on a proper integral scheme with a rational point are constant.** If `X`
is integral and universally closed over `Spec K` and has a `K`-rational point, then pulling back
along the structure morphism identifies the global functions on `Spec K` with those on `X`. -/
theorem appTop_bijective_of_section [IsIntegral X] [UniversallyClosed f]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) : Function.Bijective f.appTop := by
  -- Evaluation at the point is left inverse to `f.appTop`, and injective since `Γ(X, ⊤)` is a
  -- field.
  have hsf (a : Γ(Spec (.of K), ⊤)) : s.appTop (f.appTop a) = a := by
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.comp_apply,
      CommRingCat.id_apply] using
      ConcreteCategory.congr_hom (congrArg (fun g : Spec (.of K) ⟶ Spec (.of K) ↦
        g.appTop) hs) a
  let := (isField_of_universallyClosed K f).toField
  have hinj : Function.Injective s.appTop := s.appTop.hom.injective
  exact ⟨Function.LeftInverse.injective hsf, fun a ↦ ⟨s.appTop a, hinj (hsf _)⟩⟩

end OverField

end AlgebraicGeometry

end TauCeti
