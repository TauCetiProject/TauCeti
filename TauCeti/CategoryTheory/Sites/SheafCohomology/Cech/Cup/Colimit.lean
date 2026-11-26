/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.Order.Directed
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cofinal
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology

/-!
# The cup product on colimit Čech cohomology

Let `C` be a category with finite products, `R` a commutative ring, and `E : J → FormalCoproduct C`
a directed system of families of objects of `C` with refinement morphisms `E j ⟶ E i` whenever
`i ≤ j`. For presheaves `P, Q, S : Cᵒᵖ ⥤ ModuleCat R` equipped with a natural `R`-bilinear pairing
`μ : ∀ X, P(X) →ₗ[R] Q(X) →ₗ[R] S(X)`, the fixed-family cup products
`TauCeti.CategoryTheory.cechComplexCup` commute with refinement maps
(`TauCeti.CategoryTheory.cechComplexCup_cechComplexMap`), and hence pass to a canonical `R`-bilinear
cup product `TauCeti.CategoryTheory.cechCohomologyComplexCup` on the colimit Čech cohomology
`TauCeti.CategoryTheory.cechCohomology`.

The colimit cup product is uniquely determined by its restriction along the colimit insertions
(`TauCeti.CategoryTheory.cechCohomologyComplexCup_ι`,
`TauCeti.CategoryTheory.cechCohomology_bilinear_ext`), and more generally along
`TauCeti.CategoryTheory.toCechCohomology` for any family refined by the system
(`TauCeti.CategoryTheory.cechCohomologyComplexCup_toCechCohomology`). It inherits associativity,
graded commutativity, naturality in the presheaves, compatibility with comparison maps between
directed systems (`TauCeti.CategoryTheory.cechCohomologyComparison_cechCohomologyComplexCup`), left
and right unit laws for compatible families of sections, and compatibility with the degree-`0`
identification `TauCeti.CategoryTheory.cechCohomologyZeroIso`.

Specializing to a presheaf of `R`-algebras `F : Cᵒᵖ ⥤ AlgCat R` gives the algebra cup product
`TauCeti.CategoryTheory.cechCohomologyCup` and unit class
`TauCeti.CategoryTheory.cechCohomologyOne`, making `⊕ₚ Hᵖ(E, F)` an associative unital graded
`R`-algebra. When `F` satisfies the sheaf condition for every family of the system,
`cechCohomologyZeroIso` is multiplicative and unital
(`TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_mul`,
`TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_one`).

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyComplexCup`: the `R`-bilinear cup product on colimit Čech
  cohomology `Hᵖ(E, P) × H^q(E, Q) → Hⁿ(E, S)` for `p + q = n`.
* `TauCeti.CategoryTheory.cechCohomologyUnitClass`: the degree-`0` colimit Čech cohomology class
  of a compatible family of sections.
* `TauCeti.CategoryTheory.cechCohomologyCup`: the cup product on Čech cohomology for a presheaf
  of `R`-algebras `F`.
* `TauCeti.CategoryTheory.cechCohomologyOne`: the unit class for a presheaf of `R`-algebras `F`.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyComplexCup_ι`,
  `TauCeti.CategoryTheory.cechCohomologyComplexCup_toCechCohomology`: compatibility of the colimit
  cup product with fixed-family insertions and structure maps of arbitrary refined families.
* `TauCeti.CategoryTheory.cechCohomologyComplexCup_assoc`: associativity of the colimit cup
  product.
* `TauCeti.CategoryTheory.cechCohomologyComplexCup_comm`: graded commutativity of the colimit cup
  product.
* `TauCeti.CategoryTheory.cechCohomologyComplexCup_naturality`: naturality in morphisms of
  presheaves.
* `TauCeti.CategoryTheory.cechCohomologyComplexCup_unit_left`,
  `TauCeti.CategoryTheory.cechCohomologyComplexCup_unit_right`: left and right unit laws.
* `TauCeti.CategoryTheory.cechCohomologyComparison_cechCohomologyComplexCup`: compatibility with
  comparison maps between directed systems of families.
* `TauCeti.CategoryTheory.cechCohomologyComplexCup_cechCohomologyZeroIso_hom`: compatibility with
  the degree-`0` identification with global sections.
* `TauCeti.CategoryTheory.cechCohomologyCup_ι`, `TauCeti.CategoryTheory.cechCohomologyCup_ι_ι`,
  `TauCeti.CategoryTheory.cechCohomologyCup_assoc`,
  `TauCeti.CategoryTheory.cechCohomologyOne_cechCohomologyCup`,
  `TauCeti.CategoryTheory.cechCohomologyCup_cechCohomologyOne`,
  `TauCeti.CategoryTheory.cechCohomology_map_cechCohomologyCup`,
  `TauCeti.CategoryTheory.cechCohomology_map_cechCohomologyOne`,
  `TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_mul`,
  `TauCeti.CategoryTheory.cechCohomologyZeroIso_hom_one`: the specialization to presheaves of
  `R`-algebras.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY) and §20.25 (tag 01FP).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe uR w t t' v u u'

namespace TauCeti.CategoryTheory

/-! ### The cup product on colimit Čech cohomology -/

section Cup

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {J : Type t} [Preorder J] [IsDirectedOrder J]
  (E : J → FormalCoproduct.{w} C) (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i))
  [HasColimitsOfShape J (ModuleCat.{w} R)] {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}

/-- **The cup product on colimit Čech cohomology.** Given a natural `R`-bilinear pairing `μ` of
presheaves of `R`-modules and `p + q = n`, this is the unique `R`-bilinear map
`Hᵖ(E, P) →ₗ[R] H^q(E, Q) →ₗ[R] Hⁿ(E, S)` whose restriction along the colimit insertions at every
`j : J` is `TauCeti.CategoryTheory.cechComplexCup` (`cechCohomologyComplexCup_ι`). -/
def cechCohomologyComplexCup (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    (cechCohomology (ModuleCat.{w} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{w} R) E hE n).obj S :=
  TauCeti.ModuleCat.colimitMap₂
    (M := (cechCohomologyDiagram (ModuleCat.{w} R) E hE p).flip.obj P)
    (N := (cechCohomologyDiagram (ModuleCat.{w} R) E hE q).flip.obj Q)
    (P := (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj S)
    (fun j ↦ cechComplexCup (E j).obj μ hμ p q n h)
    fun _ j f x y ↦ by
      simp only [cechCohomologyDiagram_flip_obj_map E hE _ P f (hE (leOfHom f)).some,
        cechCohomologyDiagram_flip_obj_map E hE _ Q f (hE (leOfHom f)).some,
        cechCohomologyDiagram_flip_obj_map E hE _ S f (hE (leOfHom f)).some]
      exact (cechComplexCup_cechComplexMap (E j).obj (hE (leOfHom f)).some μ hμ p q n h x y).symm

/-- On classes inserted from the Čech cohomology of a family `E j`, the colimit cup product agrees
with `cechComplexCup` followed by insertion. -/
@[simp]
theorem cechCohomologyComplexCup_ι (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (j : J)
    (x : ((cechComplexFunctor (E j).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cechCohomologyComplexCup E hE μ hμ p q n h
        ((cechCohomologyι E hE p j).app P x) ((cechCohomologyι E hE q j).app Q y) =
      (cechCohomologyι E hE n j).app S (cechComplexCup (E j).obj μ hμ p q n h x y) := by
  simp only [cechCohomologyComplexCup, cechCohomologyι_app]
  exact TauCeti.ModuleCat.colimitMap₂_ι.{t, w} _ _ j _ _

omit [IsDirectedOrder J] in
/-- Two `R`-linear maps out of colimit Čech cohomology agree if they agree on all classes coming
from the individual families `E j`. -/
theorem cechCohomology_linear_ext {M : ModuleCat.{w} R} {p : ℕ}
    {f g : (cechCohomology (ModuleCat.{w} R) E hE p).obj P →ₗ[R] M}
    (h : ∀ j (x : ((cechComplexFunctor (E j).obj).obj P).homology p),
      f ((cechCohomologyι E hE p j).app P x) = g ((cechCohomologyι E hE p j).app P x)) :
    f = g :=
  TauCeti.ModuleCat.colimit_linearMap_ext fun j x ↦ by rw [← cechCohomologyι_app]; exact h j x

/-- Two `R`-bilinear maps out of colimit Čech cohomology agree if they agree on all pairs of
classes coming from the same family `E j`. -/
theorem cechCohomology_bilinear_ext {M : ModuleCat.{w} R} {p q : ℕ}
    {Φ Ψ : (cechCohomology (ModuleCat.{w} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj Q →ₗ[R] M}
    (h : ∀ j (x : ((cechComplexFunctor (E j).obj).obj P).homology p)
      (y : ((cechComplexFunctor (E j).obj).obj Q).homology q),
      Φ ((cechCohomologyι E hE p j).app P x) ((cechCohomologyι E hE q j).app Q y) =
        Ψ ((cechCohomologyι E hE p j).app P x) ((cechCohomologyι E hE q j).app Q y)) :
    Φ = Ψ :=
  TauCeti.ModuleCat.colimit_bilinear_ext fun j x y ↦ by
    rw [← cechCohomologyι_app, ← cechCohomologyι_app]; exact h j x y

/-- Two `R`-trilinear maps out of colimit Čech cohomology agree if they agree on all triples of
classes coming from the same family `E j`. -/
theorem cechCohomology_trilinear_ext {P₁ P₂ P₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
    {M : ModuleCat.{w} R} {p q r : ℕ}
    {Φ Ψ : (cechCohomology (ModuleCat.{w} R) E hE p).obj P₁ →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj P₂ →ₗ[R]
        (cechCohomology (ModuleCat.{w} R) E hE r).obj P₃ →ₗ[R] M}
    (h : ∀ j (a : ((cechComplexFunctor (E j).obj).obj P₁).homology p)
      (b : ((cechComplexFunctor (E j).obj).obj P₂).homology q)
      (c : ((cechComplexFunctor (E j).obj).obj P₃).homology r),
      Φ ((cechCohomologyι E hE p j).app P₁ a) ((cechCohomologyι E hE q j).app P₂ b)
          ((cechCohomologyι E hE r j).app P₃ c) =
        Ψ ((cechCohomologyι E hE p j).app P₁ a) ((cechCohomologyι E hE q j).app P₂ b)
          ((cechCohomologyι E hE r j).app P₃ c)) :
    Φ = Ψ :=
  TauCeti.ModuleCat.colimit_trilinear_ext fun j a b c ↦ by
    rw [← cechCohomologyι_app, ← cechCohomologyι_app, ← cechCohomologyι_app]; exact h j a b c

/-- On classes coming from any family `U` refined by the system `E`, the colimit cup product agrees
with `cechComplexCup` for `U`. -/
theorem cechCohomologyComplexCup_toCechCohomology
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U))
    (x : ((cechComplexFunctor U.obj).obj P).homology p)
    (y : ((cechComplexFunctor U.obj).obj Q).homology q) :
    cechCohomologyComplexCup E hE μ hμ p q n h
        ((toCechCohomology (ModuleCat.{w} R) E hE p U hU).app P x)
        ((toCechCohomology (ModuleCat.{w} R) E hE q U hU).app Q y) =
      (toCechCohomology (ModuleCat.{w} R) E hE n U hU).app S
        (cechComplexCup U.obj μ hμ p q n h x y) := by
  obtain ⟨j, ⟨φ⟩⟩ := hU
  rw [toCechCohomology_app_eq (ModuleCat.{w} R) E hE p U j φ P x,
    toCechCohomology_app_eq (ModuleCat.{w} R) E hE q U j φ Q y,
    toCechCohomology_app_eq (ModuleCat.{w} R) E hE n U j φ S _,
    cechCohomologyComplexCup_ι, cechComplexCup_cechComplexMap]

/-- **Associativity of the cup product on colimit Čech cohomology.** -/
theorem cechCohomologyComplexCup_assoc {P₁ P₂ P₃ P₁₂ P₂₃ P₁₂₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
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
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P₁)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj P₂)
    (z : (cechCohomology (ModuleCat.{w} R) E hE r).obj P₃) :
    cechCohomologyComplexCup E hE μ₁₂₃ hμ₁₂₃ pq r n hn
        (cechCohomologyComplexCup E hE μ₁₂ hμ₁₂ p q pq hpq x y) z =
      cechCohomologyComplexCup E hE μ₁₂₃' hμ₁₂₃' p qr n (by omega) x
        (cechCohomologyComplexCup E hE μ₂₃ hμ₂₃ q r qr hqr y z) :=
  congrArg (fun f ↦ f x y z) <| cechCohomology_trilinear_ext E hE
    (Φ := (cechCohomologyComplexCup E hE μ₁₂ hμ₁₂ p q pq hpq).compr₂
      (cechCohomologyComplexCup E hE μ₁₂₃ hμ₁₂₃ pq r n hn))
    (Ψ := { toFun a := (cechCohomologyComplexCup E hE μ₂₃ hμ₂₃ q r qr hqr).compr₂
              (cechCohomologyComplexCup E hE μ₁₂₃' hμ₁₂₃' p qr n (by omega) a)
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp })
    fun j a b c ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.coe_mk, AddHom.coe_mk,
        cechCohomologyComplexCup_ι]
      rw [cechComplexCup_assoc (E j).obj μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' hμ₁₂ hμ₁₂₃ hμ₂₃ hμ₁₂₃' hassoc
        p q r pq qr n hpq hqr hn]

/-- **Graded commutativity of the cup product on colimit Čech cohomology.** -/
theorem cechCohomologyComplexCup_comm [Quiver.IsThin C]
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, Q.obj X →ₗ[R] P.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y x, μ' Y (Q.map f y) (P.map f x) = S.map f (μ' X y x))
    (hcomm : ∀ X x y, μ' X y x = μ X x y)
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    cechCohomologyComplexCup E hE μ' hμ' q p n (by omega) y x =
      (-1 : ℤ) ^ (p * q) • cechCohomologyComplexCup E hE μ hμ p q n h x y :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyComplexCup E hE μ' hμ' q p n (by omega)).flip)
    (Ψ := (-1 : ℤ) ^ (p * q) • cechCohomologyComplexCup E hE μ hμ p q n h) fun j a b ↦ by
      simp only [LinearMap.flip_apply, LinearMap.smul_apply, cechCohomologyComplexCup_ι]
      rw [cechComplexCup_comm (E j).obj μ μ' hμ hμ' hcomm p q n h]
      exact map_zsmul (((cechCohomologyι E hE n j).app S :
        ((cechComplexFunctor (E j).obj).obj S).homology n ⟶ _).hom) _ _

/-- Naturality of the cup product on colimit Čech cohomology with respect to presheaf morphisms. -/
theorem cechCohomologyComplexCup_naturality {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, P'.obj X →ₗ[R] Q'.obj X →ₗ[R] S'.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ' Y (P'.map f x) (Q'.map f y) = S'.map f (μ' X x y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ X x y, γ.app X (μ X x y) = μ' X (α.app X x) (β.app X y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    (cechCohomology (ModuleCat.{w} R) E hE n).map γ
        (cechCohomologyComplexCup E hE μ hμ p q n h x y) =
      cechCohomologyComplexCup E hE μ' hμ' p q n h
        ((cechCohomology (ModuleCat.{w} R) E hE p).map α x)
        ((cechCohomology (ModuleCat.{w} R) E hE q).map β y) :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyComplexCup E hE μ hμ p q n h).compr₂
      ((cechCohomology (ModuleCat.{w} R) E hE n).map γ).hom)
    (Ψ := (cechCohomologyComplexCup E hE μ' hμ' p q n h).compl₁₂
      ((cechCohomology (ModuleCat.{w} R) E hE p).map α).hom
      ((cechCohomology (ModuleCat.{w} R) E hE q).map β).hom) fun j a b ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, cechCohomologyComplexCup_ι,
        cechCohomology_map_cechCohomologyι_app,
        cechComplexCup_naturality (E j).obj μ μ' hμ hμ' α β γ hγ p q n h]

/-- Compatibility of the colimit cup product with comparison maps between directed systems of
families. -/
theorem cechCohomologyComparison_cechCohomologyComplexCup {K : Type t'} [Preorder K]
    [IsDirectedOrder K] (F : K → FormalCoproduct.{w} C)
    (hF : ∀ ⦃i j : K⦄, i ≤ j → Nonempty (F j ⟶ F i)) [HasColimitsOfShape K (ModuleCat.{w} R)]
    (hEF : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    (cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app S
        (cechCohomologyComplexCup E hE μ hμ p q n h x y) =
      cechCohomologyComplexCup F hF μ hμ p q n h
        ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF p hEF).app P x)
        ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF q hEF).app Q y) :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyComplexCup E hE μ hμ p q n h).compr₂
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app S).hom)
    (Ψ := (cechCohomologyComplexCup F hF μ hμ p q n h).compl₁₂
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF p hEF).app P).hom
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF q hEF).app Q).hom) fun j a b ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, cechCohomologyComplexCup_ι,
        cechCohomologyComparison_app_ι, cechCohomologyComplexCup_toCechCohomology]

/-! ### Unit classes and degree zero -/

section Unit

variable [Nonempty J]

/-- The degree-`0` colimit Čech cohomology class of a compatible family of sections `e`. It is
independent of the chosen family `E j` (`cechCohomologyUnitClass_eq_ι`). -/
def cechCohomologyUnitClass (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    (cechCohomology (ModuleCat.{w} R) E hE 0).obj P :=
  (cechCohomologyι E hE 0 (Classical.arbitrary J)).app P
    (cechUnitClass (E (Classical.arbitrary J)).obj P e he)

/-- `cechCohomologyUnitClass` is the image of `cechUnitClass` from any family `E j`. -/
theorem cechCohomologyUnitClass_eq_ι (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) (j : J) :
    cechCohomologyUnitClass E hE P e he =
      (cechCohomologyι E hE 0 j).app P (cechUnitClass (E j).obj P e he) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge (Classical.arbitrary J) j
  rw [cechCohomologyUnitClass,
    ← cechCohomologyι_app_homologyMap E hE P hik (hE hik).some,
    ← cechCohomologyι_app_homologyMap E hE P hjk (hE hjk).some,
    homologyMap_cechComplexMap_cechUnitClass, homologyMap_cechComplexMap_cechUnitClass]

/-- `cechCohomologyUnitClass` is the image of `cechUnitClass` from any family `U` refined by `E`. -/
theorem cechCohomologyUnitClass_eq_toCechCohomology (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U)) :
    cechCohomologyUnitClass E hE P e he =
      (toCechCohomology (ModuleCat.{w} R) E hE 0 U hU).app P (cechUnitClass U.obj P e he) := by
  obtain ⟨j, ⟨φ⟩⟩ := hU
  rw [toCechCohomology_app_eq (ModuleCat.{w} R) E hE 0 U j φ P,
    homologyMap_cechComplexMap_cechUnitClass, cechCohomologyUnitClass_eq_ι E hE P e he j]

/-- Left unit law for `cechCohomologyComplexCup`. -/
theorem cechCohomologyComplexCup_unit_left
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] Q.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = Q.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (hl : ∀ X y, μ X (e X) y = y) (q : ℕ)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    cechCohomologyComplexCup E hE μ hμ 0 q q (zero_add q)
        (cechCohomologyUnitClass E hE P e he) y = y :=
  LinearMap.congr_fun (cechCohomology_linear_ext E hE (g := LinearMap.id) fun j b ↦ by
    rw [LinearMap.id_apply, cechCohomologyUnitClass_eq_ι E hE P e he j,
      cechCohomologyComplexCup_ι, cechComplexCup_unit_left (E j).obj μ hμ e he hl q b]) y

/-- Right unit law for `cechCohomologyComplexCup`. -/
theorem cechCohomologyComplexCup_unit_right
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = P.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P) :
    cechCohomologyComplexCup E hE μ hμ p 0 p (add_zero p) x
        (cechCohomologyUnitClass E hE Q e he) = x :=
  LinearMap.congr_fun (cechCohomology_linear_ext E hE
    (f := (cechCohomologyComplexCup E hE μ hμ p 0 p (add_zero p)).flip
      (cechCohomologyUnitClass E hE Q e he)) (g := LinearMap.id) fun j a ↦ by
    rw [LinearMap.flip_apply, LinearMap.id_apply, cechCohomologyUnitClass_eq_ι E hE Q e he j,
      cechCohomologyComplexCup_ι, cechComplexCup_unit_right (E j).obj μ hμ e he hr p a]) x

/-- Morphisms of presheaves preserving compatible sections preserve `cechCohomologyUnitClass`. -/
theorem cechCohomology_map_cechCohomologyUnitClass (α : P ⟶ Q)
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Cᵒᵖ, Q.obj X) (heQ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (eQ X) = eQ Y)
    (hα : ∀ X, α.app X (eP X) = eQ X) :
    (cechCohomology (ModuleCat.{w} R) E hE 0).map α (cechCohomologyUnitClass E hE P eP heP) =
      cechCohomologyUnitClass E hE Q eQ heQ := by
  rw [cechCohomologyUnitClass_eq_ι E hE P eP heP (Classical.arbitrary J),
    cechCohomologyUnitClass_eq_ι E hE Q eQ heQ (Classical.arbitrary J),
    cechCohomology_map_cechCohomologyι_app,
    homologyMap_cechComplexFunctor_map_cechUnitClass _ α eP heP eQ heQ hα]

/-- Comparison maps between directed systems preserve `cechCohomologyUnitClass`. -/
theorem cechCohomologyComparison_cechCohomologyUnitClass {K : Type t'} [Preorder K]
    [IsDirectedOrder K] [Nonempty K] (F : K → FormalCoproduct.{w} C)
    (hF : ∀ ⦃i j : K⦄, i ≤ j → Nonempty (F j ⟶ F i)) [HasColimitsOfShape K (ModuleCat.{w} R)]
    (hEF : ∀ j, ∃ k, Nonempty (F k ⟶ E j)) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    (cechCohomologyComparison (ModuleCat.{w} R) E hE F hF 0 hEF).app P
        (cechCohomologyUnitClass E hE P e he) =
      cechCohomologyUnitClass F hF P e he := by
  rw [cechCohomologyUnitClass_eq_ι E hE P e he (Classical.arbitrary J),
    cechCohomologyComparison_app_ι, cechCohomologyUnitClass_eq_toCechCohomology]

end Unit

section Zero

variable {T : C} (hT : IsTerminal T) [IsConnected J]

/-- The degree-`0` identification `cechCohomologyZeroIso` sends a global section `e₀ ∈ P(T)` to
`cechCohomologyUnitClass` of its restrictions. -/
theorem cechCohomologyZeroIso_hom_eq_cechCohomologyUnitClass (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0) (e₀ : P.obj (op T)) :
    (cechCohomologyZeroIso E hE hT P hP).hom e₀ =
      cechCohomologyUnitClass E hE P (fun X ↦ P.map (hT.from X.unop).op e₀)
        (fun {X Y} f ↦ by
          rw [← ModuleCat.comp_apply, ← P.map_comp,
            show (hT.from X.unop).op ≫ f = (hT.from Y.unop).op from
              Quiver.Hom.unop_inj (hT.hom_ext _ _)]) := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT P hP (Classical.arbitrary J),
    cechCohomologyUnitClass_eq_ι E hE P _ _ (Classical.arbitrary J),
    cechUnitClass_eq_homologyMap_cechAugmentation]

/-- The degree-`0` identification `cechCohomologyZeroIso` intertwines `μ (op T)` with
`cechCohomologyComplexCup` in degree `0`. -/
theorem cechCohomologyComplexCup_cechCohomologyZeroIso_hom
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (hQ : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT Q) 0)
    (hS : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT S) 0)
    (x : P.obj (op T)) (y : Q.obj (op T)) :
    cechCohomologyComplexCup E hE μ hμ 0 0 0 rfl
        ((cechCohomologyZeroIso E hE hT P hP).hom x)
        ((cechCohomologyZeroIso E hE hT Q hQ).hom y) =
      (cechCohomologyZeroIso E hE hT S hS).hom (μ (op T) x y) := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT P hP (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT Q hQ (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT S hS (Classical.arbitrary J),
    cechCohomologyComplexCup_ι, cechComplexCup_homologyMap_cechAugmentation]

end Zero

end Cup

/-! ### Specialization to presheaves of algebras -/

section Algebra

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {R : Type u'} [CommRing R]
  {J : Type t} [Preorder J] [IsDirectedOrder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) [HasColimitsOfShape J (ModuleCat.{w} R)]
  (F : Cᵒᵖ ⥤ AlgCat.{w} R)

/-- **The cup product on Čech cohomology** `Hᵖ(E, F) × H^q(E, F) → Hⁿ(E, F)`, for `p + q = n`,
of a presheaf of algebras `F` for a directed system of families `E`: the colimit of the cup
products on the Čech cohomologies of the families of the system. It is computed on the images of
classes of the families by `TauCeti.CategoryTheory.cechCohomologyCup_ι` and
`TauCeti.CategoryTheory.cechCohomologyCup_ι_ι`. -/
def cechCohomologyCup (p q n : ℕ) (h : p + q = n) :
    (cechCohomology (ModuleCat.{w} R) E hE p).obj
        (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj
          (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) →ₗ[R]
        (cechCohomology (ModuleCat.{w} R) E hE n).obj
          (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) :=
  TauCeti.ModuleCat.colimitMap₂
    (M := (cechCohomologyDiagram (ModuleCat.{w} R) E hE p).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (N := (cechCohomologyDiagram (ModuleCat.{w} R) E hE q).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (P := (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun j ↦ cechCupHomology (E j).obj F p q n h)
    fun _ _ f x y ↦ by
      simp only [cechCohomologyDiagram_flip_obj_map E hE _
        (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) f (hE (leOfHom f)).some]
      exact (homologyMap_cechComplexMap_cechCupHomology _ h x y).symm

/-- **The cup product on images of classes of one family.** The cup product of the images of two
classes of the family `E j` is the image of their cup product. -/
@[simp]
theorem cechCohomologyCup_ι {p q n : ℕ} (h : p + q = n) (j : J)
    (a : (cechAlgebraComplex (E j).obj F).homology p)
    (b : (cechAlgebraComplex (E j).obj F).homology q) :
    cechCohomologyCup E hE F p q n h
        (((cechCohomologyι E hE p j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom a)
        (((cechCohomologyι E hE q j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom b) =
      ((cechCohomologyι E hE n j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechCupHomology (E j).obj F p q n h a b) := by
  simp only [cechCohomologyCup, cechCohomologyι_app]
  -- the diagrams are only determined by the goal, so the universe levels are given explicitly
  exact TauCeti.ModuleCat.colimitMap₂_ι.{t, w} _ _ j _ _

/-- **The cup product on images of classes of two families.** The cup product of the images of a
class `a` of `E i` and a class `b` of `E j` is the image of the cup product of their restrictions
to any common refinement `E k`, along any morphisms of families `E k ⟶ E i` and `E k ⟶ E j`. -/
theorem cechCohomologyCup_ι_ι {p q n : ℕ} (h : p + q = n) {i j k : J} (hik : i ≤ k)
    (hjk : j ≤ k) (φ : E k ⟶ E i) (ψ : E k ⟶ E j)
    (a : (cechAlgebraComplex (E i).obj F).homology p)
    (b : (cechAlgebraComplex (E j).obj F).homology q) :
    cechCohomologyCup E hE F p q n h
        (((cechCohomologyι E hE p i).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom a)
        (((cechCohomologyι E hE q j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom b) =
      ((cechCohomologyι E hE n k).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechCupHomology (E k).obj F p q n h
          ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ) p).hom
            a)
          ((homologyMap (cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) ψ) q).hom
            b)) := by
  rw [← cechCohomologyι_app_homologyMap E hE _ hik φ a,
    ← cechCohomologyι_app_homologyMap E hE _ hjk ψ b, cechCohomologyCup_ι]

section Nonempty

variable [Nonempty J]

/-- The **unit class** of Čech cohomology for the system: the image of the unit class of any
family of the system (`TauCeti.CategoryTheory.cechCohomologyι_app_cechOneHomology`). -/
def cechCohomologyOne :
    (cechCohomology (ModuleCat.{w} R) E hE 0).obj (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) :=
  ((cechCohomologyι E hE 0 (Classical.arbitrary J)).app
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom (cechOneHomology (E _).obj F)

/-- The unit class is the image of the unit class of every family of the system. -/
@[simp]
theorem cechCohomologyι_app_cechOneHomology (j : J) :
    ((cechCohomologyι E hE 0 j).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).hom
        (cechOneHomology (E j).obj F) =
      cechCohomologyOne E hE F := by
  obtain ⟨k, hjk, hk⟩ := exists_ge_ge j (Classical.arbitrary J)
  rw [cechCohomologyOne, ← cechCohomologyι_app_homologyMap E hE _ hjk (hE hjk).some,
    ← cechCohomologyι_app_homologyMap E hE _ hk (hE hk).some,
    homologyMap_cechComplexMap_cechOneHomology, homologyMap_cechComplexMap_cechOneHomology]

/-- The unit class is a left unit for the cup product on Čech cohomology for the system. -/
@[simp]
theorem cechCohomologyOne_cechCohomologyCup {q : ℕ}
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F 0 q q (zero_add q) (cechCohomologyOne E hE F) y = y := by
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  rw [← cechCohomologyι_app_cechOneHomology E hE F j, cechCohomologyCup_ι,
    cechOneHomology_cechCupHomology]

/-- The unit class is a right unit for the cup product on Čech cohomology for the system. -/
@[simp]
theorem cechCohomologyCup_cechCohomologyOne {p : ℕ}
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F p 0 p (add_zero p) x (cechCohomologyOne E hE F) = x := by
  obtain ⟨j, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  rw [← cechCohomologyι_app_cechOneHomology E hE F j, cechCohomologyCup_ι,
    cechCupHomology_cechOneHomology]

/-- **Associativity** of the cup product on Čech cohomology for the system. -/
theorem cechCohomologyCup_assoc {p q r m l n : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (z : (cechCohomology (ModuleCat.{w} R) E hE r).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    cechCohomologyCup E hE F m r n h₂ (cechCohomologyCup E hE F p q m h₁ x y) z =
      cechCohomologyCup E hE F p l n h₄ x (cechCohomologyCup E hE F q r l h₃ y z) := by
  obtain ⟨i, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  obtain ⟨k, c, rfl⟩ := exists_cechCohomologyι_app_eq E hE z
  -- move the three classes to a common refinement
  obtain ⟨s, his, hjs⟩ := exists_ge_ge i j
  obtain ⟨t, hst, hkt⟩ := exists_ge_ge s k
  rw [← cechCohomologyι_app_homologyMap E hE _ (his.trans hst) (hE (his.trans hst)).some a,
    ← cechCohomologyι_app_homologyMap E hE _ (hjs.trans hst) (hE (hjs.trans hst)).some b,
    ← cechCohomologyι_app_homologyMap E hE _ hkt (hE hkt).some c]
  simp only [cechCohomologyCup_ι]
  rw [cechCupHomology_assoc (E t).obj F h₁ h₂ h₃ h₄]

section Naturality

variable {F} {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)

/-- **Naturality in the coefficients.** The map on Čech cohomology for the system induced by a
morphism of presheaves of algebras `α : F ⟶ G` preserves cup products. -/
@[simp]
theorem cechCohomology_map_cechCohomologyCup {p q n : ℕ} (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) :
    ((cechCohomology (ModuleCat.{w} R) E hE n).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom
        (cechCohomologyCup E hE F p q n h x y) =
      cechCohomologyCup E hE G p q n h
        (((cechCohomology (ModuleCat.{w} R) E hE p).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom x)
        (((cechCohomology (ModuleCat.{w} R) E hE q).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom y) := by
  obtain ⟨i, a, rfl⟩ := exists_cechCohomologyι_app_eq E hE x
  obtain ⟨j, b, rfl⟩ := exists_cechCohomologyι_app_eq E hE y
  -- move the two classes to a common refinement
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [← cechCohomologyι_app_homologyMap E hE _ hik (hE hik).some a,
    ← cechCohomologyι_app_homologyMap E hE _ hjk (hE hjk).some b]
  simp only [cechCohomologyCup_ι, cechCohomology_map_cechCohomologyι_app,
    homologyMap_cechComplexFunctor_map_cechCupHomology]

/-- The map on Čech cohomology for the system induced by a morphism of presheaves of algebras
preserves the unit class. -/
@[simp]
theorem cechCohomology_map_cechCohomologyOne :
    ((cechCohomology (ModuleCat.{w} R) E hE 0).map
        (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).hom
        (cechCohomologyOne E hE F) =
      cechCohomologyOne E hE G := by
  rw [cechCohomologyOne, cechCohomology_map_cechCohomologyι_app,
    homologyMap_cechComplexFunctor_map_cechOneHomology, cechCohomologyι_app_cechOneHomology]

end Naturality

section Zero

attribute [local instance] _root_.CategoryTheory.IsFiltered.isConnected

variable {T : C} (hT : IsTerminal T)
  (h : ∀ j, QuasiIsoAt
    (cechAugmentation (E j).obj hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) 0)

/-- **In degree zero the cup product is the product of sections.** If `F` satisfies the sheaf
condition for every family of the system, the identification of the degree `0` Čech cohomology
with the sections of `F` over the terminal object `T` (`cechCohomologyZeroIso`) carries the product
of sections to the cup product. -/
theorem cechCohomologyZeroIso_hom_mul (s t : F.obj (op T)) :
    (cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
        (s * t) =
      cechCohomologyCup E hE F 0 0 0 rfl
        ((cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom s)
        ((cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
          t) := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    homologyMap_cechAugmentation_mul, cechCohomologyCup_ι]

/-- **In degree zero the unit class is the unit section.** If `F` satisfies the sheaf condition for
every family of the system, the identification of the degree `0` Čech cohomology with the sections
of `F` over the terminal object `T` (`cechCohomologyZeroIso`) carries the section `1` to the unit
class. -/
theorem cechCohomologyZeroIso_hom_one :
    (cechCohomologyZeroIso E hE hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) h).hom.hom
        (1 : F.obj (op T)) =
      cechCohomologyOne E hE F := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT _ h (Classical.arbitrary J),
    homologyMap_cechAugmentation_one, cechCohomologyι_app_cechOneHomology]

end Zero

end Nonempty

end Algebra

end TauCeti.CategoryTheory
