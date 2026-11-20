/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The relative Picard fppf sheaf

For a morphism of schemes `f : X ⟶ S`, the relative Picard presheaf sends an `S`-scheme `T`
to `Pic(X_T) / Pic(T)`. The relative Picard functor is its associated sheaf for the fppf topology
on schemes over `S`.

This file constructs that sheaf and records its universal property. It makes no representability
claim: constructing a scheme that represents the sheaf, and identifying its degree-zero
component, require additional geometric input.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardAddPresheaf`: the relative Picard presheaf written as
  an additive commutative group;
* `TauCeti.AlgebraicGeometry.relativePicardAddPresheafMk`: the canonical section represented by
  a line-bundle class;
* `TauCeti.AlgebraicGeometry.relativePicardFppfSheaf`: its fppf sheafification;
* `TauCeti.AlgebraicGeometry.relativePicardToFppfSheaf`: the canonical map from
  `T ↦ Pic(X_T) / Pic(T)` to the relative Picard fppf sheaf;
* `TauCeti.AlgebraicGeometry.relativePicardFppfSheafHomEquiv`: the universal property of the
  sheafification.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The relative Picard presheaf, transported from multiplicative to additive notation. This
changes only the presentation of the abelian group law: addition is tensor product of
line-bundle classes. -/
def relativePicardAddPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  relativePicardPresheaf f ⋙ CommGrpCat.toAddCommGrp

/-- The additive relative Picard presheaf is obtained from the multiplicative one by the
equivalence between commutative groups and additive commutative groups. -/
theorem relativePicardAddPresheaf_eq :
    relativePicardAddPresheaf f = relativePicardPresheaf f ⋙ CommGrpCat.toAddCommGrp := by
  rw [relativePicardAddPresheaf]

/-- The section of the additive relative Picard presheaf represented by a line-bundle class. -/
def relativePicardAddPresheafMk (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom f)) : (relativePicardAddPresheaf f).obj T :=
  by
    unfold relativePicardAddPresheaf
    exact Additive.ofMul (QuotientGroup.mk a)

/-- Every section of the additive relative Picard presheaf is represented by a line-bundle
class. -/
theorem relativePicardAddPresheafMk_surjective (T : (Over S)ᵒᵖ) :
    Function.Surjective (relativePicardAddPresheafMk f T) := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  intro a
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a.toMul
  exact ⟨a, rfl⟩

/-- Pulling back a represented section of the additive relative Picard presheaf pulls back its
line-bundle class. -/
@[simp]
lemma relativePicardAddPresheaf_map_mk {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : LineBundleClass (pullback T.unop.hom f)) :
    (relativePicardAddPresheaf f).map φ (relativePicardAddPresheafMk f T a) =
      relativePicardAddPresheafMk f T'
        (LineBundleClass.pullback ((Over.pullback f).map φ.unop).left a) :=
  by
    unfold relativePicardAddPresheafMk relativePicardAddPresheaf
    exact congrArg Additive.ofMul (relativePicardPresheaf_map_mk f φ a)

/-- The trivial line-bundle class represents the zero section of the additive relative Picard
presheaf. -/
@[simp]
lemma relativePicardAddPresheafMk_one (T : (Over S)ᵒᵖ) :
    relativePicardAddPresheafMk f T 1 = 0 := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact congrArg Additive.ofMul (map_one (QuotientGroup.mk' _))

/-- The tensor product of line-bundle classes represents the sum of the represented sections of
the additive relative Picard presheaf. -/
@[simp]
lemma relativePicardAddPresheafMk_mul (T : (Over S)ᵒᵖ)
    (a b : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardAddPresheafMk f T (a * b) =
      relativePicardAddPresheafMk f T a + relativePicardAddPresheafMk f T b := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact congrArg Additive.ofMul (map_mul (QuotientGroup.mk' _) a b)

/-- Dualizing a line-bundle class negates its represented section. -/
@[simp]
lemma relativePicardAddPresheafMk_inv (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardAddPresheafMk f T a⁻¹ = -relativePicardAddPresheafMk f T a := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact congrArg Additive.ofMul (map_inv (QuotientGroup.mk' _) a)

/-- A quotient of line-bundle classes represents the difference of their sections. -/
@[simp]
lemma relativePicardAddPresheafMk_div (T : (Over S)ᵒᵖ)
    (a b : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardAddPresheafMk f T (a / b) =
      relativePicardAddPresheafMk f T a - relativePicardAddPresheafMk f T b := by
  simp only [div_eq_mul_inv, relativePicardAddPresheafMk_mul,
    relativePicardAddPresheafMk_inv, sub_eq_add_neg]

/-- A natural tensor power represents a natural multiple of the represented section. -/
@[simp]
lemma relativePicardAddPresheafMk_pow (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom f)) (n : ℕ) :
    relativePicardAddPresheafMk f T (a ^ n) = n • relativePicardAddPresheafMk f T a := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact congrArg Additive.ofMul (map_pow (QuotientGroup.mk' _) a n)

/-- An integer tensor power represents an integer multiple of the represented section. -/
@[simp]
lemma relativePicardAddPresheafMk_zpow (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom f)) (n : ℤ) :
    relativePicardAddPresheafMk f T (a ^ n) = n • relativePicardAddPresheafMk f T a := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact congrArg Additive.ofMul (map_zpow (QuotientGroup.mk' _) a n)

/-- A line-bundle class on `X_T` represents the zero section of the additive relative Picard
presheaf exactly when it is pulled back from `T`. -/
lemma relativePicardAddPresheafMk_eq_zero_iff (T : (Over S)ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardAddPresheafMk f T a = 0 ↔
      a ∈ (LineBundleClass.pullbackHom (pullback.fst T.unop.hom f)).range := by
  unfold relativePicardAddPresheafMk relativePicardAddPresheaf
  exact (ofMul_eq_zero (A := _ ⧸ _)).trans (QuotientGroup.eq_one_iff a)

/-- A line-bundle class pulled back from the base represents zero in the relative Picard
presheaf. -/
@[simp]
lemma relativePicardAddPresheafMk_pullback_fst (T : (Over S)ᵒᵖ)
    (b : LineBundleClass T.unop.left) :
    relativePicardAddPresheafMk f T
      (LineBundleClass.pullback (pullback.fst T.unop.hom f) b) = 0 :=
  (relativePicardAddPresheafMk_eq_zero_iff f T _).mpr ⟨b, LineBundleClass.pullbackHom_apply _ _⟩

/-- The **relative Picard fppf sheaf** of `f : X ⟶ S`, obtained by sheafifying the presheaf
`T ↦ Pic(X_T) / Pic(T)` on the fppf site of schemes over `S`.

This definition does not assert that the resulting sheaf is representable. -/
def relativePicardFppfSheaf : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (relativePicardAddPresheaf f)

/-- The relative Picard fppf sheaf is obtained by applying the fppf sheafification functor to
the additive relative Picard presheaf. -/
theorem relativePicardFppfSheaf_eq :
    relativePicardFppfSheaf f =
      (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
        (relativePicardAddPresheaf f) :=
  by rw [relativePicardFppfSheaf]

/-- The underlying presheaf of the relative Picard fppf sheaf is the sheafification of
`relativePicardPresheaf f`. -/
@[simp]
theorem relativePicardFppfSheaf_obj :
    (relativePicardFppfSheaf f).obj =
      sheafify (Scheme.fppfTopology.over S) (relativePicardAddPresheaf f) :=
  by rw [relativePicardFppfSheaf]

/-- The canonical map from the relative Picard presheaf to its fppf sheafification. -/
def relativePicardToFppfSheaf :
    relativePicardAddPresheaf f ⟶ (relativePicardFppfSheaf f).obj :=
  (toSheafify (Scheme.fppfTopology.over S) (relativePicardAddPresheaf f) :
      relativePicardAddPresheaf f ⟶
        sheafify (Scheme.fppfTopology.over S) (relativePicardAddPresheaf f)) ≫
    eqToHom (relativePicardFppfSheaf_obj f).symm

/-- The canonical map to the relative Picard fppf sheaf is the unit of fppf sheafification. -/
theorem relativePicardToFppfSheaf_eq :
    relativePicardToFppfSheaf f =
      toSheafify (Scheme.fppfTopology.over S) (relativePicardAddPresheaf f) ≫
        eqToHom (relativePicardFppfSheaf_obj f).symm :=
  (rfl)

/-- Two sections of `T ↦ Pic(X_T) / Pic(T)` with the same image in the relative Picard fppf sheaf
agree fppf-locally. -/
instance isLocallyInjective_relativePicardToFppfSheaf :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (relativePicardToFppfSheaf f) := by
  rw [relativePicardToFppfSheaf_eq]
  infer_instance

/-- Every section of the relative Picard fppf sheaf is fppf-locally represented by a section
of the relative Picard presheaf. -/
instance isLocallySurjective_relativePicardToFppfSheaf :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (relativePicardToFppfSheaf f) := by
  rw [relativePicardToFppfSheaf_eq]
  infer_instance

/-- **Universal property of the relative Picard fppf sheaf.** Maps from the sheafification to an
fppf sheaf `F` are naturally equivalent to maps from the relative Picard presheaf to the
underlying presheaf of `F`. -/
def relativePicardFppfSheafHomEquiv
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (relativePicardFppfSheaf f ⟶ F) ≃ (relativePicardAddPresheaf f ⟶ F.obj) :=
  (Iso.homCongr (eqToIso (relativePicardFppfSheaf_eq f)) (Iso.refl F)).trans <|
    (sheafificationAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv
      (relativePicardAddPresheaf f) F

/-- The universal-property equivalence restricts a sheaf morphism along the canonical map from
the relative Picard presheaf. -/
@[simp]
theorem relativePicardFppfSheafHomEquiv_apply
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (g : relativePicardFppfSheaf f ⟶ F) :
    relativePicardFppfSheafHomEquiv f F g = relativePicardToFppfSheaf f ≫ g.hom :=
  by
    rw [relativePicardFppfSheafHomEquiv]
    dsimp only [Equiv.trans_apply, Iso.homCongr_apply]
    rw [Adjunction.homEquiv_unit]
    simp [relativePicardToFppfSheaf, Category.assoc]

end

end TauCeti.AlgebraicGeometry
