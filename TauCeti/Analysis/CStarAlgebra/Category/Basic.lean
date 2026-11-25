/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# C*-categories

A C*-category is a complex linear dagger category whose Hom spaces are Banach spaces, with
contractive composition, the C*-identity `‖f†f‖ = ‖f‖²`, and `f†f` positive in `End X` for
every arrow `f` out of `X`. Here `f†f` denotes the operator-order composite, which is
`f ≫ dagger f` in categorical notation.

`TauCeti.CStarCategory` adds this analytic structure to Mathlib's native `Preadditive` and
`Linear ℂ` carriers and to a conjugate-linear `TauCeti.DaggerCategory`. Positivity of `f†f`
is stated as `f ≫ dagger f = g ≫ dagger g` for an endomorphism `g` of `X`; in the C*-algebra
`End X` this is equivalent to `0 ≤ f†f` (`CategoryTheory.End.nonneg_iff`).

## Main declarations

* `TauCeti.CStarCategory`: the C*-category axioms on given Hom norms.
* `TauCeti.CStarCategory.norm_dagger` and `TauCeti.CStarCategory.norm_self_comp_dagger`: the
  dagger is isometric and the C*-identity holds with equality.
* `TauCeti.CStarCategory.norm_id`: identities of nonzero objects have norm one.
* `CategoryTheory.End.instCStarAlgebra`: each endomorphism algebra `End X` is a unital
  C*-algebra, with Mathlib's operator-order multiplication and the dagger as star.
* `CategoryTheory.End.nonneg_iff`: the positive elements of `End X` are exactly the composites
  `f ≫ dagger f` for arrows `f` out of `X`.
* `CategoryTheory.End.comp_comp_dagger_mono`: conjugation `a ↦ g†ag` by an arrow `g` is
  monotone.
* `CategoryTheory.End.comp_comp_dagger_le_norm_smul`: `g†ag ≤ ‖a‖ g†g` for self-adjoint `a`.

## Implementation notes

As for Mathlib's `CStarModule`, the class takes the Hom norms as `Norm` parameters and asks for
a `NormedSpace.Core`, rather than registering `NormedAddCommGroup` instances on Hom types: a
concrete category such as Hilbert spaces already carries normed structures on its Hom types,
whose uniformities need not be definitionally those induced by the norm. The abbreviations
`TauCeti.CStarCategory.normedAddCommGroup` and `TauCeti.CStarCategory.normedSpace` provide
these structures when no others are present. The type `End X` has no prior norm, so its
normed and C*-algebra structures are global instances.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti

/-- A *C*-category* structure on given norms of the Hom spaces of a complex linear dagger
category: the Hom spaces are complex Banach spaces, composition is contractive, the
C*-inequality `‖f‖² ≤ ‖f†f‖` holds, and `f†f` has the form `g†g` for an endomorphism `g`
of the source of `f`. Here `f†f` is the operator-order composite `f ≫ dagger f`. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    [∀ X Y : C, Norm (X ⟶ Y)] : Prop where
  /-- Each Hom space is a complex normed space for the given norm. -/
  normedSpaceCore (X Y : C) : NormedSpace.Core ℂ (X ⟶ Y)
  /-- Each Hom space is complete for the metric of its norm. -/
  completeSpace (X Y : C) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore X Y)
    CompleteSpace (X ⟶ Y)
  /-- Composition is contractive. -/
  norm_comp_le {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖
  /-- The C*-inequality; equality follows (`TauCeti.CStarCategory.norm_self_comp_dagger`). -/
  norm_mul_self_le {X Y : C} (f : X ⟶ Y) : ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖
  /-- Positivity of `f†f` in `End X`: it is `g†g` for some endomorphism `g` of `X`. -/
  exists_self_comp_dagger_eq {X Y : C} (f : X ⟶ Y) :
    ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed group structure of a Hom space of a C*-category. This is not an instance:
a Hom type may already carry a normed structure with a better uniformity. -/
abbrev normedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) :=
  .ofCore (normedSpaceCore X Y)

/-- The complex normed space structure of a Hom space of a C*-category. This is not an
instance, for the same reason as `TauCeti.CStarCategory.normedAddCommGroup`. -/
abbrev normedSpace (X Y : C) :
    letI := normedAddCommGroup X Y
    NormedSpace ℂ (X ⟶ Y) :=
  letI := normedAddCommGroup X Y
  .ofCore (normedSpaceCore X Y)

variable {X Y Z : C}

/-- Hom norms are nonnegative. -/
theorem norm_nonneg (f : X ⟶ Y) : 0 ≤ ‖f‖ :=
  (normedSpaceCore X Y).norm_nonneg f

/-- An arrow has norm zero exactly when it is zero. -/
@[simp] theorem norm_eq_zero {f : X ⟶ Y} : ‖f‖ = 0 ↔ f = 0 :=
  (normedSpaceCore X Y).norm_eq_zero_iff f

/-- The zero arrow has norm zero. -/
@[simp] theorem norm_zero : ‖(0 : X ⟶ Y)‖ = 0 :=
  norm_eq_zero.2 rfl

/-- Hom norms are absolutely homogeneous for complex scalars. -/
theorem norm_smul (c : ℂ) (f : X ⟶ Y) : ‖c • f‖ = ‖c‖ * ‖f‖ :=
  (normedSpaceCore X Y).norm_smul c f

/-- Hom norms satisfy the triangle inequality. -/
theorem norm_add_le (f g : X ⟶ Y) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (normedSpaceCore X Y).norm_triangle f g

/-- Negating an arrow preserves its norm. -/
@[simp] theorem norm_neg (f : X ⟶ Y) : ‖-f‖ = ‖f‖ := by
  simpa using norm_smul (-1 : ℂ) f

/-- The dagger of a C*-category is isometric. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ := by
  -- `‖f‖² ≤ ‖f ≫ dagger f‖ ≤ ‖f‖ ‖dagger f‖` gives `‖f‖ ≤ ‖dagger f‖`, for `f` and `dagger f`.
  have key : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ ≤ ‖dagger f‖ := by
    intro X Y f
    have h := (norm_mul_self_le f).trans (norm_comp_le f (dagger f))
    rcases (norm_nonneg f).eq_or_lt with hf | hf
    · rw [← hf]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_left h hf
  exact le_antisymm (by simpa using key (dagger f)) (key f)

/-- The C*-identity: `‖f†f‖ = ‖f‖²`, where `f†f` is `f ≫ dagger f`. -/
theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [pow_two]
  refine le_antisymm ?_ (norm_mul_self_le f)
  simpa using norm_comp_le f (dagger f)

/-- The C*-identity for `f f†`, where `f f†` is `dagger f ≫ f`. -/
theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa using norm_self_comp_dagger (dagger f)

/-- An arrow `f` with `f†f = 0`, that is `f ≫ dagger f = 0`, is zero. -/
@[simp] theorem self_comp_dagger_eq_zero {f : X ⟶ Y} : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, pow_eq_zero_iff two_ne_zero, norm_eq_zero]

/-- An arrow `f` with `f f† = 0`, that is `dagger f ≫ f = 0`, is zero. -/
@[simp] theorem dagger_comp_self_eq_zero {f : X ⟶ Y} : dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, pow_eq_zero_iff two_ne_zero, norm_eq_zero]

/-- The norm of an identity arrow is idempotent under squaring. -/
private theorem sq_norm_id (X : C) : ‖𝟙 X‖ ^ 2 = ‖𝟙 X‖ := by
  simpa using (norm_self_comp_dagger (𝟙 X)).symm

/-- The identity of an object has norm at most one. -/
theorem norm_id_le_one (X : C) : ‖𝟙 X‖ ≤ 1 := by
  nlinarith [norm_nonneg (𝟙 X), sq_norm_id X]

/-- The identity of an object that is not a zero object has norm one. -/
theorem norm_id {X : C} (hX : ¬ Limits.IsZero X) : ‖𝟙 X‖ = 1 := by
  have hne : ‖𝟙 X‖ ≠ 0 := by
    rwa [Ne, norm_eq_zero, ← Limits.IsZero.iff_id_eq_zero]
  exact (mul_eq_left₀ hne).1 (by rw [← pow_two, sq_norm_id])

end CStarCategory

end TauCeti

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C]

section Norm

variable [∀ X Y : C, Norm (X ⟶ Y)] {X : C}

/-- An endomorphism has the norm of its underlying arrow. -/
instance instNorm : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The norm of an endomorphism is the norm of its underlying arrow. -/
theorem norm_def (a : End X) : ‖a‖ = ‖a.asHom‖ := (rfl)

/-- Regarding an arrow as an endomorphism preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

end Norm

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X : C}

/-- The normed space axioms for `End X`, transported from the Hom space of `X`. -/
theorem normedSpaceCore (X : C) : NormedSpace.Core ℂ (End X) where
  norm_nonneg a := CStarCategory.norm_nonneg a.asHom
  norm_smul c a := by
    simpa only [norm_def, smul_asHom] using
      (CStarCategory.normedSpaceCore X X).norm_smul c a.asHom
  norm_triangle a b := by
    simpa only [norm_def, add_asHom] using
      (CStarCategory.normedSpaceCore X X).norm_triangle a.asHom b.asHom
  norm_eq_zero_iff a := by
    rw [norm_def, CStarCategory.norm_eq_zero, End.ext_iff, zero_asHom]

/-- `End X` is a normed group for the norm of its underlying arrows. -/
instance instNormedAddCommGroup : NormedAddCommGroup (End X) :=
  .ofCore (normedSpaceCore X)

/-- `End X` is a normed ring: its operator-order multiplication is submultiplicative. -/
instance instNormedRing : NormedRing (End X) where
  __ := (inferInstance : NormedAddCommGroup (End X))
  __ := (inferInstance : Ring (End X))
  norm_mul_le a b := by
    simpa only [norm_def, mul_asHom, mul_comm ‖a.asHom‖] using
      CStarCategory.norm_comp_le b.asHom a.asHom

/-- `End X` is a normed complex algebra. -/
instance instNormedAlgebra : NormedAlgebra ℂ (End X) where
  norm_smul_le c a := ((normedSpaceCore X).norm_smul c a).le

/-- `End X` is complete, since the Hom space of `X` is. -/
instance instCompleteSpace : CompleteSpace (End X) := by
  let := CStarCategory.normedAddCommGroup X X
  have : CompleteSpace (X ⟶ X) := CStarCategory.completeSpace X X
  let e : End X ≃ᵢ (X ⟶ X) :=
    { toEquiv := End.addEquiv.toEquiv
      isometry_toFun := AddMonoidHomClass.isometry_of_norm End.addEquiv fun a => by
        rw [End.addEquiv_apply, End.norm_def] }
  exact e.completeSpace

/-- The C*-identity in `End X`, from the C*-inequality of the category. -/
instance instCStarRing : CStarRing (End X) where
  norm_mul_self_le a := by
    simpa only [norm_def, mul_asHom, star_asHom] using CStarCategory.norm_mul_self_le a.asHom

/-- Each endomorphism algebra of a C*-category is a unital C*-algebra, with the dagger as
star and Mathlib's operator-order multiplication. -/
instance instCStarAlgebra : CStarAlgebra (End X) where

/-- The positive cone of the C*-algebra `End X`: self-adjoint elements with nonnegative
spectrum. -/
instance instPartialOrder : PartialOrder (End X) := CStarAlgebra.spectralOrder (End X)

/-- The order of `End X` is the C*-algebra order. -/
instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- For an arrow `f` out of `X`, the endomorphism `f†f`, that is `f ≫ dagger f`, is
positive in the C*-algebra `End X`. -/
theorem self_comp_dagger_nonneg {Y : C} (f : X ⟶ Y) : 0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger_eq f
  rw [hg]
  exact star_mul_self_nonneg (End.of g)

/-- The positive elements of `End X` are exactly the endomorphisms `f ≫ dagger f`, for arrows
`f` out of `X`. -/
theorem nonneg_iff {a : End X} : 0 ≤ a ↔ ∃ (Y : C) (f : X ⟶ Y), a = End.of (f ≫ dagger f) := by
  refine ⟨fun ha => ?_, ?_⟩
  · obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 ha
    exact ⟨X, b.asHom, End.ext (by simp)⟩
  · rintro ⟨Y, f, rfl⟩
    exact self_comp_dagger_nonneg f

/-- Conjugation by an arrow `g : X ⟶ Y` is monotone from `End Y` to `End X`: `a ≤ b` implies
`g†ag ≤ g†bg`, that is `g ≫ a ≫ dagger g ≤ g ≫ b ≫ dagger g`. -/
theorem comp_comp_dagger_mono {Y : C} (g : X ⟶ Y) {a b : End Y} (hab : a ≤ b) :
    End.of (g ≫ a.asHom ≫ dagger g) ≤ End.of (g ≫ b.asHom ≫ dagger g) := by
  obtain ⟨h, hh⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (sub_nonneg.2 hab)
  have key : End.of (g ≫ b.asHom ≫ dagger g) - End.of (g ≫ a.asHom ≫ dagger g) =
      End.of ((g ≫ h.asHom) ≫ dagger (g ≫ h.asHom)) := by
    have := congrArg End.asHom hh
    simp only [End.sub_asHom, End.mul_asHom, star_asHom] at this
    ext
    simp [← Preadditive.comp_sub, ← Preadditive.sub_comp, this]
  rw [← sub_nonneg, key]
  exact self_comp_dagger_nonneg _

/-- For a self-adjoint `a : End Y` and an arrow `g : X ⟶ Y`, the conjugate `g†ag`, that is
`g ≫ a ≫ dagger g`, is at most `‖a‖ g†g` in `End X`. -/
theorem comp_comp_dagger_le_norm_smul {Y : C} (g : X ⟶ Y) (a : End Y)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    End.of (g ≫ a.asHom ≫ dagger g) ≤ ‖a‖ • End.of (g ≫ dagger g) := by
  refine (comp_comp_dagger_mono g ha.le_algebraMap_norm_self).trans_eq ?_
  ext
  simp [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]

end CategoryTheory.End
