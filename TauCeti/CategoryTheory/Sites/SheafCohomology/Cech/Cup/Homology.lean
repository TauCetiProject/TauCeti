/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Bilinear
public import TauCeti.Algebra.Homology.ModuleCat.Single
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Reverse

/-!
# The cup product on fixed-family Čech cohomology

Passing the cochain cup product `TauCeti.CategoryTheory.cechCupCochain` of
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic` to cocycles and cohomology via
`TauCeti.CochainComplex.moduleCatHomologyMap₂` yields an `R`-bilinear pairing
`TauCeti.CategoryTheory.cechComplexCup` on the cohomology of the fixed-family Čech complex
`Č(U, -)`.

Because `d_cechCupCochain` gives the graded Leibniz rule, the cup product of cocycles is a cocycle
and the cup product of a cocycle with a coboundary is a coboundary. The induced cohomology pairing
inherits associativity, left and right unit laws, naturality in both the family and the presheaves,
compatibility with the degree-`0` augmentation, and graded commutativity
(`TauCeti.CategoryTheory.cechComplexCup_comm`) via
`TauCeti.CategoryTheory.homologyMap_cechReverse_app`.

Specializing to a presheaf of `R`-algebras `F : Cᵒᵖ ⥤ AlgCat R` yields the cohomology cup product
`TauCeti.CategoryTheory.cechCupHomology` and unit class `TauCeti.CategoryTheory.cechOneHomology`,
for which:
* the cup product is **associative** (`TauCeti.CategoryTheory.cechCupHomology_assoc`);
* the class of the unit cochain `1` (`TauCeti.CategoryTheory.cechOneHomology`) is a two-sided
  **unit** (`TauCeti.CategoryTheory.cechCupHomology_cechOneHomology`,
  `TauCeti.CategoryTheory.cechOneHomology_cechCupHomology`);
* the maps on cohomology induced by morphisms of families, such as refinements of open covers,
  and by morphisms of presheaves of algebras preserve the cup product and the unit
  (`TauCeti.CategoryTheory.homologyMap_cechComplexMap_cechCupHomology`,
  `TauCeti.CategoryTheory.homologyMap_cechComplexFunctor_map_cechCupHomology` and the
  corresponding statements for `cechOneHomology`);
* in degree `0`, for a terminal object `T`, the classes of the augmentations of sections over `T`
  multiply as the sections do, and the section `1` gives the unit class
  (`TauCeti.CategoryTheory.homologyMap_cechAugmentation_mul`,
  `TauCeti.CategoryTheory.homologyMap_cechAugmentation_one`).

So `⊕ₚ Hᵖ(U, F)` is an associative unital graded `R`-algebra, functorial in the family and in the
presheaf. Since any two morphisms between two families induce the same map on cohomology, these
are the compatibilities through which the product passes to Čech cohomology defined as a colimit
over a directed system of covers (`TauCeti.CategoryTheory.cechCohomologyCup`).

## Main definitions

* `TauCeti.CategoryTheory.cechCupCycles`: the `R`-bilinear cup product on Čech cocycles.
* `TauCeti.CategoryTheory.cechComplexCup`: the `R`-bilinear cup product on fixed-family Čech
  cohomology `Hᵖ(Č(U, P)) × H^q(Č(U, Q)) → Hⁿ(Č(U, S))` for `p + q = n`.
* `TauCeti.CategoryTheory.cechUnitClass`: the degree-`0` Čech cohomology class of a compatible
  family of sections.
* `TauCeti.CategoryTheory.cechCupHomology` and `TauCeti.CategoryTheory.cechOneHomology`: the
  specialization to a presheaf of `R`-algebras `F`.

## Main results

* `TauCeti.CategoryTheory.cechComplexCup_homologyπ`: evaluation on cohomology classes of cocycles.
* `TauCeti.CategoryTheory.cechComplexCup_assoc`: associativity on fixed-family cohomology.
* `TauCeti.CategoryTheory.cechComplexCup_comm`: graded commutativity on fixed-family cohomology.
* `TauCeti.CategoryTheory.cechComplexCup_cechComplexMap`: compatibility with maps induced by
  morphisms of families.
* `TauCeti.CategoryTheory.cechComplexCup_naturality`: naturality in morphisms of presheaves.
* `TauCeti.CategoryTheory.cechComplexCup_unit_left`,
  `TauCeti.CategoryTheory.cechComplexCup_unit_right`: left and right unit laws on cohomology.
* `TauCeti.CategoryTheory.cechComplexCup_homologyMap_cechAugmentation`: compatibility with the
  degree-`0` augmentation from global sections.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP), for the cup product on Čech
  cohomology, associativity, and graded commutativity.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe uR w v v' u u'

namespace TauCeti.CategoryTheory

section Homology

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type w} (U : ι → C) {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}

section Descent

variable (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
  (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
  (p q n : ℕ) (h : p + q = n)

/-- The `R`-bilinear cup product on Čech cocycles. -/
def cechCupCycles :
    ((cechComplexFunctor U).obj P).cycles p →ₗ[R]
      ((cechComplexFunctor U).obj Q).cycles q →ₗ[R]
        ((cechComplexFunctor U).obj S).cycles n :=
  TauCeti.CochainComplex.moduleCatCyclesMap₂ (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b) p q n h

/-- On underlying cochains, `cechCupCycles` is `cechCupCochain`. -/
@[simp]
theorem iCycles_cechCupCycles (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).iCycles n (cechCupCycles U μ hμ p q n h a b) =
      cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b) :=
  TauCeti.CochainComplex.iCycles_moduleCatCyclesMap₂
    (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b) p q n h a b

/-- **The cup product on fixed-family Čech cohomology.** For a natural `R`-bilinear pairing `μ`
and `p + q = n`, this is the `R`-bilinear pairing
`Hᵖ(Č(U, P)) →ₗ[R] H^q(Č(U, Q)) →ₗ[R] Hⁿ(Č(U, S))` induced by `cechCupCochain`. -/
def cechComplexCup :
    ((cechComplexFunctor U).obj P).homology p →ₗ[R]
      ((cechComplexFunctor U).obj Q).homology q →ₗ[R]
        ((cechComplexFunctor U).obj S).homology n :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂ (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b) p q n h

/-- On cohomology classes of cocycles, `cechComplexCup` is the class of `cechCupCycles`. -/
@[simp]
theorem cechComplexCup_homologyπ (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    cechComplexCup U μ hμ p q n h
        (((cechComplexFunctor U).obj P).homologyπ p a)
        (((cechComplexFunctor U).obj Q).homologyπ q b) =
      ((cechComplexFunctor U).obj S).homologyπ n (cechCupCycles U μ hμ p q n h a b) :=
  TauCeti.CochainComplex.moduleCatHomologyMap₂_homologyπ
    (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b) p q n h a b

end Descent

/-- **Associativity of the cup product on fixed-family Čech cohomology.** -/
theorem cechComplexCup_assoc {P₁ P₂ P₃ P₁₂ P₂₃ P₁₂₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ₁₂ : ∀ X, P₁.obj X →ₗ[R] P₂.obj X →ₗ[R] P₁₂.obj X)
    (μ₁₂₃ : ∀ X, P₁₂.obj X →ₗ[R] P₃.obj X →ₗ[R] P₁₂₃.obj X)
    (μ₂₃ : ∀ X, P₂.obj X →ₗ[R] P₃.obj X →ₗ[R] P₂₃.obj X)
    (μ₁₂₃' : ∀ X, P₁.obj X →ₗ[R] P₂₃.obj X →ₗ[R] P₁₂₃.obj X)
    (hμ₁₂ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ₁₂ Y (P₁.map f x) (P₂.map f y) = P₁₂.map f (μ₁₂ X x y))
    (hμ₁₂₃ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y,
      μ₁₂₃ Y (P₁₂.map f x) (P₃.map f y) = P₁₂₃.map f (μ₁₂₃ X x y))
    (hμ₂₃ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y z, μ₂₃ Y (P₂.map f y) (P₃.map f z) = P₂₃.map f (μ₂₃ X y z))
    (hμ₁₂₃' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y,
      μ₁₂₃' Y (P₁.map f x) (P₂₃.map f y) = P₁₂₃.map f (μ₁₂₃' X x y))
    (hassoc : ∀ X x y z, μ₁₂₃ X (μ₁₂ X x y) z = μ₁₂₃' X x (μ₂₃ X y z))
    (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n)
    (x : ((cechComplexFunctor U).obj P₁).homology p)
    (y : ((cechComplexFunctor U).obj P₂).homology q)
    (z : ((cechComplexFunctor U).obj P₃).homology r) :
    cechComplexCup U μ₁₂₃ hμ₁₂₃ pq r n hn (cechComplexCup U μ₁₂ hμ₁₂ p q pq hpq x y) z =
      cechComplexCup U μ₁₂₃' hμ₁₂₃' p qr n (by omega) x
        (cechComplexCup U μ₂₃ hμ₂₃ q r qr hqr y z) := by
  obtain ⟨a, rfl⟩ := moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := moduleCat_homologyπ_surjective _ q y
  obtain ⟨c, rfl⟩ := moduleCat_homologyπ_surjective _ r z
  simp only [cechComplexCup_homologyπ]; congr 1; apply moduleCat_iCycles_injective
  simpa only [iCycles_cechCupCycles] using
    cechCupCochain_assoc U μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' hμ₁₂ hμ₂₃ hassoc p q r pq qr n hpq hqr hn _ _ _

/-- **Graded commutativity of the cup product on fixed-family Čech cohomology.** -/
theorem cechComplexCup_comm [Quiver.IsThin C]
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, Q.obj X →ₗ[R] P.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y x, μ' Y (Q.map f y) (P.map f x) = S.map f (μ' X y x))
    (hcomm : ∀ X x y, μ' X y x = μ X x y)
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    cechComplexCup U μ' hμ' q p n (by omega) y x =
      (-1 : ℤ) ^ (p * q) • cechComplexCup U μ hμ p q n h x y := by
  obtain ⟨a, rfl⟩ := moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := moduleCat_homologyπ_surjective _ q y
  trans homologyMap ((cechReverse (ModuleCat.{w} R) U).app S) n
    (cechComplexCup U μ' hμ' q p n (by omega)
      (homologyMap ((cechReverse (ModuleCat.{w} R) U).app Q) q
        (((cechComplexFunctor U).obj Q).homologyπ q b))
      (homologyMap ((cechReverse (ModuleCat.{w} R) U).app P) p
        (((cechComplexFunctor U).obj P).homologyπ p a)))
  · simp [homologyMap_cechReverse_app]
  simp only [moduleCat_homologyMap_homologyπ, cechComplexCup_homologyπ, ← map_zsmul]
  congr 1; apply moduleCat_iCycles_injective
  simpa using cechReverse_cechCupCochain U μ μ' hμ' hcomm p q n h _ _

/-- Compatibility of the cup product on fixed-family Čech cohomology with morphisms of families. -/
theorem cechComplexCup_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor V).obj P).homology p)
    (y : ((cechComplexFunctor V).obj Q).homology q) :
    homologyMap (cechComplexMap S φ) n (cechComplexCup V μ hμ p q n h x y) =
      cechComplexCup U μ hμ p q n h
        (homologyMap (cechComplexMap P φ) p x) (homologyMap (cechComplexMap Q φ) q y) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂
    (fun p q n h ↦ cechCupCochain V μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain V μ hμ p q n h a b)
    (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b)
    (cechComplexMap P φ) (cechComplexMap Q φ) (cechComplexMap S φ)
    (fun p q n h a b ↦ cechComplexMap_cechCupCochain U φ μ hμ p q n h a b) p q n h x y

/-- Naturality of the cup product on fixed-family Čech cohomology with respect to morphisms of
presheaves. -/
theorem cechComplexCup_naturality {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, P'.obj X →ₗ[R] Q'.obj X →ₗ[R] S'.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ' Y (P'.map f x) (Q'.map f y) = S'.map f (μ' X x y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ X x y, γ.app X (μ X x y) = μ' X (α.app X x) (β.app X y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    homologyMap ((cechComplexFunctor U).map γ) n (cechComplexCup U μ hμ p q n h x y) =
      cechComplexCup U μ' hμ' p q n h
        (homologyMap ((cechComplexFunctor U).map α) p x)
        (homologyMap ((cechComplexFunctor U).map β) q y) :=
  TauCeti.CochainComplex.homologyMap_moduleCatHomologyMap₂
    (fun p q n h ↦ cechCupCochain U μ p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ hμ p q n h a b)
    (fun p q n h ↦ cechCupCochain U μ' p q n h)
    (fun p q n h a b ↦ d_cechCupCochain U μ' hμ' p q n h a b)
    ((cechComplexFunctor U).map α) ((cechComplexFunctor U).map β) ((cechComplexFunctor U).map γ)
    (fun p q n h a b ↦ cechComplexFunctor_map_cechCupCochain U μ μ' α β γ hγ p q n h a b)
    p q n h x y

/-- The degree-`0` Čech cohomology class of a compatible family of sections `e`. -/
def cechUnitClass (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    ((cechComplexFunctor U).obj P).homology 0 :=
  ((cechComplexFunctor U).obj P).homologyπ 0 <|
    moduleCatCyclesMk ((cechComplexFunctor U).obj P) (n := 0)
      (cechUnitCochain U P e) 1 (by simp) (d_cechUnitCochain U P e he)

/-- Left unit law for `cechComplexCup`. -/
theorem cechComplexCup_unit_left (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] Q.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = Q.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (hl : ∀ X y, μ X (e X) y = y) (q : ℕ) (y : ((cechComplexFunctor U).obj Q).homology q) :
    cechComplexCup U μ hμ 0 q q (zero_add q) (cechUnitClass U P e he) y = y := by
  obtain ⟨b, rfl⟩ := moduleCat_homologyπ_surjective _ q y
  rw [cechUnitClass, cechComplexCup_homologyπ]; congr 1; apply moduleCat_iCycles_injective
  simpa using cechCupCochain_unit_left U μ e he hl q _

/-- Right unit law for `cechComplexCup`. -/
theorem cechComplexCup_unit_right (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = P.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ) (x : ((cechComplexFunctor U).obj P).homology p) :
    cechComplexCup U μ hμ p 0 p (add_zero p) x (cechUnitClass U Q e he) = x := by
  obtain ⟨a, rfl⟩ := moduleCat_homologyπ_surjective _ p x
  rw [cechUnitClass, cechComplexCup_homologyπ]; congr 1; apply moduleCat_iCycles_injective
  simpa using cechCupCochain_unit_right U μ e he hr p _

/-- Any cochain map sending `cechUnitCochain` to `cechUnitCochain` sends `cechUnitClass` to
`cechUnitClass`. -/
theorem homologyMap_cechUnitClass_of_f_zero {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
    {κ : Type w} {V : κ → D} {Q' : Dᵒᵖ ⥤ ModuleCat.{w} R}
    (φ : (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj Q')
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Dᵒᵖ, Q'.obj X) (heQ : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y), Q'.map f (eQ X) = eQ Y)
    (hφ : φ.f 0 (cechUnitCochain U P eP) = cechUnitCochain V Q' eQ) :
    homologyMap φ 0 (cechUnitClass U P eP heP) = cechUnitClass V Q' eQ heQ := by
  rw [cechUnitClass, cechUnitClass, moduleCat_homologyMap_homologyπ]
  congr 1; apply moduleCat_iCycles_injective; simpa using hφ

/-- Morphisms of families preserve `cechUnitClass`. -/
theorem homologyMap_cechComplexMap_cechUnitClass {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    homologyMap (cechComplexMap P φ) 0 (cechUnitClass V P e he) = cechUnitClass U P e he :=
  homologyMap_cechUnitClass_of_f_zero V (cechComplexMap P φ) e he e he
    (cechComplexMap_cechUnitCochain U φ P e he)

/-- Morphisms of presheaves preserving compatible unit sections preserve `cechUnitClass`. -/
theorem homologyMap_cechComplexFunctor_map_cechUnitClass (α : P ⟶ Q)
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Cᵒᵖ, Q.obj X) (heQ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (eQ X) = eQ Y)
    (hα : ∀ X, α.app X (eP X) = eQ X) :
    homologyMap ((cechComplexFunctor U).map α) 0 (cechUnitClass U P eP heP) =
      cechUnitClass U Q eQ heQ :=
  homologyMap_cechUnitClass_of_f_zero U ((cechComplexFunctor U).map α) eP heP eQ heQ
    (cechComplexFunctor_map_cechUnitCochain U α eP eQ hα)

/-- The degree-`0` augmentation sends a global section `e₀ ∈ P(T)` to the `cechUnitClass` of its
restrictions. -/
theorem cechUnitClass_eq_homologyMap_cechAugmentation {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e₀ : P.obj (op T)) :
    homologyMap (cechAugmentation U hT P) 0
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) =
      cechUnitClass U P (fun X ↦ P.map (hT.from X.unop).op e₀)
        (fun {X Y} f ↦ by
          rw [← ModuleCat.comp_apply, ← P.map_comp,
            show (hT.from X.unop).op ≫ f = (hT.from Y.unop).op from
              Quiver.Hom.unop_inj (hT.hom_ext _ _)]) := by
  rw [← singleObjCyclesSelfIso_inv_homologyπ, ModuleCat.comp_apply,
    moduleCat_homologyMap_homologyπ, cechUnitClass]
  congr 1; apply moduleCat_iCycles_injective
  have hsc : ((CochainComplex.single₀ (ModuleCat.{w} R)).obj (P.obj (op T))).iCycles 0
        ((singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) =
      (singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀ :=
    (ModuleCat.comp_apply _ (((single (ModuleCat.{w} R) _ 0).obj _).iCycles 0) e₀).symm.trans
      (ConcreteCategory.congr_hom (singleObjCyclesSelfIso_inv_iCycles (ComplexShape.up ℕ) 0 _) e₀)
  rw [moduleCat_iCycles_cyclesMap_apply, hsc, iCycles_moduleCatCyclesMk]
  exact cechAugmentation_f_zero_eq_cechUnitCochain U hT P e₀

/-- The degree-`0` augmentation intertwines `μ (op T)` with `cechComplexCup` in degree `0`. -/
theorem cechComplexCup_homologyMap_cechAugmentation {T : C} (hT : IsTerminal T)
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (x : P.obj (op T)) (y : Q.obj (op T)) :
    cechComplexCup U μ hμ 0 0 0 rfl
        (homologyMap (cechAugmentation U hT P) 0
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv x))
        (homologyMap (cechAugmentation U hT Q) 0
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (Q.obj (op T))).inv y)) =
      homologyMap (cechAugmentation U hT S) 0
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (S.obj (op T))).inv (μ (op T) x y)) := by
  simp only [cechUnitClass_eq_homologyMap_cechAugmentation, cechUnitClass, cechComplexCup_homologyπ]
  congr 1; apply moduleCat_iCycles_injective
  simp only [iCycles_cechCupCycles, iCycles_moduleCatCyclesMk]
  refine cechComplex_ext fun c ↦ ?_
  simp only [cechCupCochain_π, cechUnitCochain_π, ← ModuleCat.comp_apply, ← P.map_comp,
    ← Q.map_comp, ← op_comp, hT.hom_ext (_ ≫ hT.from _) (hT.from _), hμ]

end Homology

/-! ### Specialization to presheaves of algebras -/

section Algebra

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {R : Type u'} [CommRing R] (F : Cᵒᵖ ⥤ AlgCat.{w} R)

/-- **The cup product on Čech cohomology of a family** for a presheaf of `R`-algebras `F`:
`Hᵖ(U, F) →ₗ[R] H^q(U, F) →ₗ[R] Hⁿ(U, F)` for `p + q = n`. On classes of cocycles it is the
class of the cup product of cocycles (`TauCeti.CategoryTheory.cechCupHomology_homologyπ`). -/
def cechCupHomology (p q n : ℕ) (h : p + q = n) :
    (cechAlgebraComplex U F).homology p →ₗ[R] (cechAlgebraComplex U F).homology q →ₗ[R]
      (cechAlgebraComplex U F).homology n :=
  cechComplexCup U (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (cechAlgebraMul_naturality F) p q n h

/-- **The cup product on classes**: the cup product of the classes of two cocycles is the class of
the cup product of the cocycles. -/
@[simp]
theorem cechCupHomology_homologyπ {p q n : ℕ} (h : p + q = n)
    (a : (cechAlgebraComplex U F).cycles p) (b : (cechAlgebraComplex U F).cycles q) :
    cechCupHomology U F p q n h (((cechAlgebraComplex U F).homologyπ p).hom a)
        (((cechAlgebraComplex U F).homologyπ q).hom b) =
      ((cechAlgebraComplex U F).homologyπ n).hom ((cechAlgebraComplex U F).moduleCatCyclesMk
        (cechCup p q n h (((cechAlgebraComplex U F).iCycles p).hom a)
          (((cechAlgebraComplex U F).iCycles q).hom b)) (n + 1) (by simp)
        (d_cechCup_eq_zero h (moduleCat_d_iCycles_apply _ _ _ a)
          (moduleCat_d_iCycles_apply _ _ _ b))) := by
  refine (cechComplexCup_homologyπ U (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
      (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
      (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
      (fun X ↦ LinearMap.mul R (F.obj X)) (cechAlgebraMul_naturality F) p q n h a b).trans ?_
  congr 1
  apply moduleCat_iCycles_injective
  exact (iCycles_cechCupCycles U (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) _ p q n h a b).trans
    (by simp only [iCycles_moduleCatCyclesMk, cechCup_eq_cechCupCochain])

/-- **The cup product on classes of cochains**: the cup product of the classes of two cocycles
given as cochains is the class of their cup product. -/
theorem cechCupHomology_homologyπ_moduleCatCyclesMk {p q n : ℕ} (h : p + q = n)
    (x : (cechAlgebraComplex U F).X p) (m₁ : ℕ) (hm₁ : (ComplexShape.up ℕ).next p = m₁)
    (hx : ((cechAlgebraComplex U F).d p m₁).hom x = 0) (y : (cechAlgebraComplex U F).X q)
    (m₂ : ℕ) (hm₂ : (ComplexShape.up ℕ).next q = m₂)
    (hy : ((cechAlgebraComplex U F).d q m₂).hom y = 0) :
    cechCupHomology U F p q n h
        (((cechAlgebraComplex U F).homologyπ p).hom
          ((cechAlgebraComplex U F).moduleCatCyclesMk x m₁ hm₁ hx))
        (((cechAlgebraComplex U F).homologyπ q).hom
          ((cechAlgebraComplex U F).moduleCatCyclesMk y m₂ hm₂ hy)) =
      ((cechAlgebraComplex U F).homologyπ n).hom ((cechAlgebraComplex U F).moduleCatCyclesMk
        (cechCup p q n h x y) (n + 1) (by simp)
        (d_cechCup_eq_zero h (by subst hm₁; rwa [CochainComplex.next] at hx)
          (by subst hm₂; rwa [CochainComplex.next] at hy))) := by
  simp only [cechCupHomology_homologyπ, iCycles_moduleCatCyclesMk]

/-- **Associativity** of the cup product on Čech cohomology. -/
theorem cechCupHomology_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (α : (cechAlgebraComplex U F).homology p)
    (β : (cechAlgebraComplex U F).homology q) (γ : (cechAlgebraComplex U F).homology r) :
    cechCupHomology U F m r n h₂ (cechCupHomology U F p q m h₁ α β) γ =
      cechCupHomology U F p l n h₄ α (cechCupHomology U F q r l h₃ β γ) := by
  simp only [cechCupHomology]
  exact cechComplexCup_assoc U _ _ _ _
    (cechAlgebraMul_naturality F) (cechAlgebraMul_naturality F)
    (cechAlgebraMul_naturality F) (cechAlgebraMul_naturality F)
    (fun _ (x y z : F.obj _) ↦ mul_assoc x y z)
    p q r m l n h₁ h₃ h₂ α β γ

/-- The **unit class** of Čech cohomology: the class in `H⁰(U, F)` of the unit cocycle, all of
whose factors are `1`. -/
def cechOneHomology : (cechAlgebraComplex U F).homology 0 :=
  cechUnitClass U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) (fun X ↦ (1 : F.obj X))
    (cechAlgebraOne_naturality F)

/-- The unit class is the class of the unit cocycle. -/
theorem cechOneHomology_def :
    cechOneHomology U F = ((cechAlgebraComplex U F).homologyπ 0).hom
      ((cechAlgebraComplex U F).moduleCatCyclesMk (cechOne U F) 1 (by simp) d_cechOne) := by
  rw [cechOneHomology, cechUnitClass]
  congr 1; apply moduleCat_iCycles_injective
  simp only [iCycles_moduleCatCyclesMk, cechOne_eq_cechUnitCochain]

/-- The unit class is a left unit for the cup product on Čech cohomology. -/
@[simp]
theorem cechOneHomology_cechCupHomology {q : ℕ} (β : (cechAlgebraComplex U F).homology q) :
    cechCupHomology U F 0 q q (zero_add q) (cechOneHomology U F) β = β := by
  simp only [cechCupHomology, cechOneHomology]
  exact cechComplexCup_unit_left U _ (cechAlgebraMul_naturality F) _
    (cechAlgebraOne_naturality F) (fun _ (y : F.obj _) ↦ one_mul y) q β

/-- The unit class is a right unit for the cup product on Čech cohomology. -/
@[simp]
theorem cechCupHomology_cechOneHomology {p : ℕ} (α : (cechAlgebraComplex U F).homology p) :
    cechCupHomology U F p 0 p (add_zero p) α (cechOneHomology U F) = α := by
  simp only [cechCupHomology, cechOneHomology]
  exact cechComplexCup_unit_right U _ (cechAlgebraMul_naturality F) _
    (cechAlgebraOne_naturality F) (fun _ (x : F.obj _) ↦ mul_one x) p α

section Naturality

variable {U F}

/-- **Naturality under refinement.** The map on Čech cohomology `Hⁿ(V, F) ⟶ Hⁿ(U, F)` induced by a
morphism of families `φ : U ⟶ V`, such as a refinement of open covers, preserves cup products. -/
@[simp]
theorem homologyMap_cechComplexMap_cechCupHomology {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {p q n : ℕ} (h : p + q = n)
    (α : (cechAlgebraComplex V F).homology p) (β : (cechAlgebraComplex V F).homology q) :
    (homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) n).hom
        (cechCupHomology V F p q n h α β) =
      cechCupHomology U F p q n h
        ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) p).hom α)
        ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) q).hom
          β) := by
  simp only [cechCupHomology]
  exact cechComplexCup_cechComplexMap U φ _ (cechAlgebraMul_naturality F) p q n h α β

/-- The map on Čech cohomology induced by a morphism of families, such as a refinement of open
covers, preserves the unit class. -/
@[simp]
theorem homologyMap_cechComplexMap_cechOneHomology {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) 0).hom
        (cechOneHomology V F) =
      cechOneHomology U F := by
  simp only [cechOneHomology]
  exact homologyMap_cechComplexMap_cechUnitClass U φ
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) (fun X ↦ (1 : F.obj X))
    (cechAlgebraOne_naturality F)

/-- **Naturality in the coefficients.** The map on Čech cohomology induced by a morphism of
presheaves of algebras `α : F ⟶ G` preserves cup products. -/
@[simp]
theorem homologyMap_cechComplexFunctor_map_cechCupHomology {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)
    {p q n : ℕ} (h : p + q = n) (x : (cechAlgebraComplex U F).homology p)
    (y : (cechAlgebraComplex U F).homology q) :
    (homologyMap ((cechComplexFunctor U).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) n).hom
        (cechCupHomology U F p q n h x y) =
      cechCupHomology U G p q n h
        ((homologyMap ((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) p).hom x)
        ((homologyMap ((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) q).hom y) := by
  simp only [cechCupHomology]
  exact cechComplexCup_naturality U _ _
    (cechAlgebraMul_naturality F) (cechAlgebraMul_naturality G)
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun X (x y : F.obj X) ↦ map_mul (α.app X).hom x y) p q n h x y

/-- The map on Čech cohomology induced by a morphism of presheaves of algebras preserves the unit
class. -/
@[simp]
theorem homologyMap_cechComplexFunctor_map_cechOneHomology {G : Cᵒᵖ ⥤ AlgCat.{w} R}
    (α : F ⟶ G) :
    (homologyMap ((cechComplexFunctor U).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))) 0).hom
        (cechOneHomology U F) =
      cechOneHomology U G := by
  simp only [cechOneHomology]
  exact homologyMap_cechComplexFunctor_map_cechUnitClass U _ _
    (cechAlgebraOne_naturality F) _ (cechAlgebraOne_naturality G) fun X ↦ map_one (α.app X).hom

end Naturality

section Augmentation

variable {T : C} (hT : IsTerminal T)

/-- The class in `H⁰(U, F)` of the augmentation of a section over the terminal object is the class
of the cycle that the augmentation maps it to. -/
private lemma homologyMap_cechAugmentation_apply (s : F.obj (op T)) :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s) =
      ((cechAlgebraComplex U F).homologyπ 0).hom
        (cyclesMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0
          ((singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s)) := by
  rw [← singleObjCyclesSelfIso_inv_homologyπ, ModuleCat.comp_apply,
    moduleCat_homologyMap_homologyπ]

/-- **The cup product in degree zero is the product of sections.** For a terminal object `T`, the
class in `H⁰(U, F)` of the augmentation of a product `s * t` of sections of `F` over `T` is the cup
product of the classes of the augmentations of `s` and `t`. -/
theorem homologyMap_cechAugmentation_mul (s t : F.obj (op T)) :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom (s * t)) =
      cechCupHomology U F 0 0 0 rfl
        ((homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom s))
        ((homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom t)) := by
  simp only [homologyMap_cechAugmentation_apply, cechCupHomology_homologyπ]
  congr 1
  apply moduleCat_iCycles_injective
  refine cechCochain_ext fun a ↦ ?_
  simp only [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk, cechComponent_cechCup,
    CochainComplex.iCycles_singleObjCyclesSelfIso_inv, cechFace_cechAugmentation_f_zero,
    cechComponent_cechAugmentation_f_zero, map_mul]

/-- **The unit class in degree zero is the class of the unit section.** For a terminal object `T`,
the class in `H⁰(U, F)` of the augmentation of the section `1` of `F` over `T` is the unit class. -/
theorem homologyMap_cechAugmentation_one :
    (homologyMap (cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0).hom
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op T))).inv.hom
          (1 : F.obj (op T))) =
      cechOneHomology U F := by
  rw [homologyMap_cechAugmentation_apply, cechOneHomology_def]
  congr 1
  apply moduleCat_iCycles_injective
  refine cechCochain_ext fun a ↦ ?_
  simp only [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk,
    CochainComplex.iCycles_singleObjCyclesSelfIso_inv, cechComponent_cechAugmentation_f_zero,
    map_one, cechComponent_cechOne]

end Augmentation

end Algebra

end TauCeti.CategoryTheory
