/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
cup product `TauCeti.CategoryTheory.cechCohomologyCup` on the colimit Čech cohomology
`TauCeti.CategoryTheory.cechCohomology`.

The colimit cup product is uniquely determined by its restriction along the colimit insertions
(`TauCeti.CategoryTheory.cechCohomologyCup_ι`,
`TauCeti.CategoryTheory.cechCohomology_bilinear_ext`), and more generally along
`TauCeti.CategoryTheory.toCechCohomology` for any family refined by the system
(`TauCeti.CategoryTheory.cechCohomologyCup_toCechCohomology`). It inherits associativity, graded
commutativity, naturality in the presheaves, compatibility with comparison maps between directed
systems (`TauCeti.CategoryTheory.cechCohomologyComparison_cechCohomologyCup`), left and right unit
laws for compatible families of sections, and compatibility with the degree-`0` identification
`TauCeti.CategoryTheory.cechCohomologyZeroIso`.

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyCup`: the `R`-bilinear cup product on colimit Čech
  cohomology `Hᵖ(E, P) × H^q(E, Q) → Hⁿ(E, S)` for `p + q = n`.
* `TauCeti.CategoryTheory.cechCohomologyUnitClass`: the degree-`0` colimit Čech cohomology class
  of a compatible family of sections.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyCup_ι`,
  `TauCeti.CategoryTheory.cechCohomologyCup_toCechCohomology`: compatibility of the colimit cup
  product with fixed-family insertions and structure maps of arbitrary refined families.
* `TauCeti.CategoryTheory.cechCohomologyCup_assoc`: associativity of the colimit cup product.
* `TauCeti.CategoryTheory.cechCohomologyCup_comm`: graded commutativity of the colimit cup product.
* `TauCeti.CategoryTheory.cechCohomologyCup_naturality`: naturality in morphisms of presheaves.
* `TauCeti.CategoryTheory.cechCohomologyCup_unit_left`,
  `TauCeti.CategoryTheory.cechCohomologyCup_unit_right`: left and right unit laws.
* `TauCeti.CategoryTheory.cechCohomologyComparison_cechCohomologyCup`: compatibility with comparison
  maps between directed systems of families.
* `TauCeti.CategoryTheory.cechCohomologyCup_cechCohomologyZeroIso_hom`: compatibility with the
  degree-`0` identification with global sections.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY) and §20.25 (tag 01FP).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe uR w t t' v u

namespace TauCeti.CategoryTheory

/-! ### The cup product on colimit Čech cohomology -/

section Cup

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {J : Type t} [Preorder J] [IsDirectedOrder J]
  (E : J → FormalCoproduct.{w} C) (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i))
  [HasColimitsOfShape J (ModuleCat.{w} R)] {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}

omit [IsDirectedOrder J] in
private lemma cechCohomologyι_app_cechComplexHomologyMap {i j : J} (hij : i ≤ j)
    (φ : E j ⟶ E i) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology n) :
    (cechCohomologyι E hE n j).app P (homologyMap (cechComplexMap P φ) n x) =
      (cechCohomologyι E hE n i).app P x := by
  have hm : (cechComplexHomologyMap (ModuleCat.{w} R) n φ).app P ≫ (cechCohomologyι E hE n j).app P
      = (cechCohomologyι E hE n i).app P :=
    NatTrans.congr_app
      (cechComplexHomologyMap_comp_cechCohomologyι (ModuleCat.{w} R) E hE n hij φ) P
  rw [cechComplexHomologyMap_app] at hm
  exact (ModuleCat.comp_apply _ _ x).symm.trans (ConcreteCategory.congr_hom hm x)

private lemma toCechCohomology_app_eq (U : FormalCoproduct.{w} C) (j : J) (φ : E j ⟶ U)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ) (x : ((cechComplexFunctor U.obj).obj P).homology n) :
    (toCechCohomology (ModuleCat.{w} R) E hE n U ⟨j, ⟨φ⟩⟩).app P x =
      (cechCohomologyι E hE n j).app P (homologyMap (cechComplexMap P φ) n x) := by
  have hm : (toCechCohomology (ModuleCat.{w} R) E hE n U ⟨j, ⟨φ⟩⟩).app P =
      (cechComplexHomologyMap (ModuleCat.{w} R) n φ).app P ≫ (cechCohomologyι E hE n j).app P :=
    NatTrans.congr_app (toCechCohomology_eq (ModuleCat.{w} R) E hE n U j φ) P
  rw [cechComplexHomologyMap_app] at hm
  exact (ConcreteCategory.congr_hom hm x).trans (ModuleCat.comp_apply _ _ x)

omit [IsDirectedOrder J] in
private lemma cechCohomology_map_ι {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (α : P ⟶ Q) (n : ℕ) (j : J)
    (x : ((cechComplexFunctor (E j).obj).obj P).homology n) :
    (cechCohomology (ModuleCat.{w} R) E hE n).map α ((cechCohomologyι E hE n j).app P x) =
      (cechCohomologyι E hE n j).app Q
        (homologyMap ((cechComplexFunctor (E j).obj).map α) n x) := by
  have h : (((cechCohomologyι E hE n j).app P ≫ (cechCohomology (ModuleCat.{w} R) E hE n).map α :
        ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ _)) x =
      ((homologyMap ((cechComplexFunctor (E j).obj).map α) n ≫ (cechCohomologyι E hE n j).app Q :
        ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ _)) x :=
    ConcreteCategory.congr_hom ((cechCohomologyι E hE n j).naturality α).symm x
  exact (ModuleCat.comp_apply _ _ x).symm.trans (h.trans (ModuleCat.comp_apply _ _ x))

omit [IsDirectedOrder J] in
private lemma cechCohomologyComparison_app_ι {K : Type t'} [Preorder K] [IsDirectedOrder K]
    (F : K → FormalCoproduct.{w} C) (hF : ∀ ⦃i j : K⦄, i ≤ j → Nonempty (F j ⟶ F i))
    [HasColimitsOfShape K (ModuleCat.{w} R)] (hEF : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ) (j : J)
    (x : ((cechComplexFunctor (E j).obj).obj P).homology n) :
    (cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app P
        ((cechCohomologyι E hE n j).app P x) =
      (toCechCohomology (ModuleCat.{w} R) F hF n (E j) (hEF j)).app P x := by
  have h : (((cechCohomologyι E hE n j).app P ≫
        (cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app P :
        ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ _)) x =
      ((toCechCohomology (ModuleCat.{w} R) F hF n (E j) (hEF j)).app P :
        ((cechComplexFunctor (E j).obj).obj P).homology n ⟶ _) x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (cechCohomologyι_comp_cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF j) P) x
  exact (ModuleCat.comp_apply _ _ x).symm.trans h

omit [IsDirectedOrder J] in
private lemma cechCohomologyZeroIso_hom_apply {T : C} (hT : IsTerminal T) [IsConnected J]
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (j : J) (x : P.obj (op T)) :
    (cechCohomologyZeroIso E hE hT P hP).hom x =
      (cechCohomologyι E hE 0 j).app P (homologyMap (cechAugmentation (E j).obj hT P) 0
        ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv x)) := by
  have h : (cechCohomologyZeroIso E hE hT P hP).hom x =
      (((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv ≫
        homologyMap (cechAugmentation (E j).obj hT P) 0 ≫ (cechCohomologyι E hE 0 j).app P :
        P.obj (op T) ⟶ _)) x :=
    ConcreteCategory.congr_hom (cechCohomologyZeroIso_hom E hE hT P hP j) x
  exact h.trans <| (ModuleCat.comp_apply _ _ x).trans (ModuleCat.comp_apply _ _ _)

/-- **The cup product on colimit Čech cohomology.** Given a natural `R`-bilinear pairing `μ` of
presheaves of `R`-modules and `p + q = n`, this is the unique `R`-bilinear map
`Hᵖ(E, P) →ₗ[R] H^q(E, Q) →ₗ[R] Hⁿ(E, S)` whose restriction along the colimit insertions at every
`j : J` is `TauCeti.CategoryTheory.cechComplexCup` (`cechCohomologyCup_ι`). -/
def cechCohomologyCup (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    (cechCohomology (ModuleCat.{w} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{w} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{w} R) E hE n).obj S :=
  TauCeti.ModuleCat.colimitBilinear
    (F := (cechCohomologyDiagram (ModuleCat.{w} R) E hE p).flip.obj P)
    (G := (cechCohomologyDiagram (ModuleCat.{w} R) E hE q).flip.obj Q)
    (H := (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj S)
    (fun j ↦ cechComplexCup (E j).obj μ hμ p q n h)
    fun {i j} f x y ↦ by
      simp only [Functor.flip_obj_map, cechCohomologyDiagram_map _ E hE _ f (hE (leOfHom f)).some,
        cechComplexHomologyMap_app]
      exact (cechComplexCup_cechComplexMap (E j).obj (hE (leOfHom f)).some μ hμ p q n h x y).symm

/-- On classes inserted from the Čech cohomology of a family `E j`, the colimit cup product agrees
with `cechComplexCup` followed by insertion. -/
@[simp]
theorem cechCohomologyCup_ι (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (j : J)
    (x : ((cechComplexFunctor (E j).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cechCohomologyCup E hE μ hμ p q n h
        ((cechCohomologyι E hE p j).app P x) ((cechCohomologyι E hE q j).app Q y) =
      (cechCohomologyι E hE n j).app S (cechComplexCup (E j).obj μ hμ p q n h x y) := by
  rw [cechCohomologyι_app, cechCohomologyι_app, cechCohomologyι_app]
  exact TauCeti.ModuleCat.colimitBilinear_ι
    (F := (cechCohomologyDiagram (ModuleCat.{w} R) E hE p).flip.obj P)
    (G := (cechCohomologyDiagram (ModuleCat.{w} R) E hE q).flip.obj Q)
    (H := (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj S) _ _ j x y

omit [IsDirectedOrder J] in
private lemma cechCohomology_linear_ext {M : ModuleCat.{w} R} {p : ℕ}
    {f g : (cechCohomology (ModuleCat.{w} R) E hE p).obj P →ₗ[R] M}
    (h : ∀ j (x : ((cechComplexFunctor (E j).obj).obj P).homology p),
      f ((cechCohomologyι E hE p j).app P x) = g ((cechCohomologyι E hE p j).app P x)) :
    f = g :=
  TauCeti.ModuleCat.linearMap_colimit_ext fun j x ↦ by rw [← cechCohomologyι_app]; exact h j x

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

private lemma cechCohomology_trilinear_ext {P₁ P₂ P₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
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
theorem cechCohomologyCup_toCechCohomology (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U))
    (x : ((cechComplexFunctor U.obj).obj P).homology p)
    (y : ((cechComplexFunctor U.obj).obj Q).homology q) :
    cechCohomologyCup E hE μ hμ p q n h
        ((toCechCohomology (ModuleCat.{w} R) E hE p U hU).app P x)
        ((toCechCohomology (ModuleCat.{w} R) E hE q U hU).app Q y) =
      (toCechCohomology (ModuleCat.{w} R) E hE n U hU).app S
        (cechComplexCup U.obj μ hμ p q n h x y) := by
  obtain ⟨j, ⟨φ⟩⟩ := hU
  rw [toCechCohomology_app_eq E hE U j φ P p x, toCechCohomology_app_eq E hE U j φ Q q y,
    toCechCohomology_app_eq E hE U j φ S n _, cechCohomologyCup_ι, cechComplexCup_cechComplexMap]

/-- **Associativity of the cup product on colimit Čech cohomology.** -/
theorem cechCohomologyCup_assoc {P₁ P₂ P₃ P₁₂ P₂₃ P₁₂₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
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
    cechCohomologyCup E hE μ₁₂₃ hμ₁₂₃ pq r n hn
        (cechCohomologyCup E hE μ₁₂ hμ₁₂ p q pq hpq x y) z =
      cechCohomologyCup E hE μ₁₂₃' hμ₁₂₃' p qr n (by omega) x
        (cechCohomologyCup E hE μ₂₃ hμ₂₃ q r qr hqr y z) :=
  congrArg (fun f ↦ f x y z) <| cechCohomology_trilinear_ext E hE
    (Φ := (cechCohomologyCup E hE μ₁₂ hμ₁₂ p q pq hpq).compr₂
      (cechCohomologyCup E hE μ₁₂₃ hμ₁₂₃ pq r n hn))
    (Ψ := { toFun a := (cechCohomologyCup E hE μ₂₃ hμ₂₃ q r qr hqr).compr₂
              (cechCohomologyCup E hE μ₁₂₃' hμ₁₂₃' p qr n (by omega) a)
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp })
    fun j a b c ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.coe_mk, AddHom.coe_mk, cechCohomologyCup_ι]
      rw [cechComplexCup_assoc (E j).obj μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' hμ₁₂ hμ₁₂₃ hμ₂₃ hμ₁₂₃' hassoc
        p q r pq qr n hpq hqr hn]

/-- **Graded commutativity of the cup product on colimit Čech cohomology.** -/
theorem cechCohomologyCup_comm [Quiver.IsThin C]
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, Q.obj X →ₗ[R] P.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y x, μ' Y (Q.map f y) (P.map f x) = S.map f (μ' X y x))
    (hcomm : ∀ X x y, μ' X y x = μ X x y)
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    cechCohomologyCup E hE μ' hμ' q p n (by omega) y x =
      (-1 : ℤ) ^ (p * q) • cechCohomologyCup E hE μ hμ p q n h x y :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyCup E hE μ' hμ' q p n (by omega)).flip)
    (Ψ := (-1 : ℤ) ^ (p * q) • cechCohomologyCup E hE μ hμ p q n h) fun j a b ↦ by
      simp only [LinearMap.flip_apply, LinearMap.smul_apply, cechCohomologyCup_ι]
      rw [cechComplexCup_comm (E j).obj μ μ' hμ hμ' hcomm p q n h]
      exact map_zsmul (((cechCohomologyι E hE n j).app S :
        ((cechComplexFunctor (E j).obj).obj S).homology n ⟶ _).hom) _ _

/-- Naturality of the cup product on colimit Čech cohomology with respect to presheaf morphisms. -/
theorem cechCohomologyCup_naturality {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, P'.obj X →ₗ[R] Q'.obj X →ₗ[R] S'.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ' Y (P'.map f x) (Q'.map f y) = S'.map f (μ' X x y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ X x y, γ.app X (μ X x y) = μ' X (α.app X x) (β.app X y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    (cechCohomology (ModuleCat.{w} R) E hE n).map γ (cechCohomologyCup E hE μ hμ p q n h x y) =
      cechCohomologyCup E hE μ' hμ' p q n h
        ((cechCohomology (ModuleCat.{w} R) E hE p).map α x)
        ((cechCohomology (ModuleCat.{w} R) E hE q).map β y) :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyCup E hE μ hμ p q n h).compr₂
      ((cechCohomology (ModuleCat.{w} R) E hE n).map γ).hom)
    (Ψ := (cechCohomologyCup E hE μ' hμ' p q n h).compl₁₂
      ((cechCohomology (ModuleCat.{w} R) E hE p).map α).hom
      ((cechCohomology (ModuleCat.{w} R) E hE q).map β).hom) fun j a b ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, cechCohomologyCup_ι,
        cechCohomology_map_ι, cechComplexCup_naturality (E j).obj μ μ' hμ hμ' α β γ hγ p q n h]

/-- Compatibility of the colimit cup product with comparison maps between directed systems of
families. -/
theorem cechCohomologyComparison_cechCohomologyCup {K : Type t'} [Preorder K] [IsDirectedOrder K]
    (F : K → FormalCoproduct.{w} C) (hF : ∀ ⦃i j : K⦄, i ≤ j → Nonempty (F j ⟶ F i))
    [HasColimitsOfShape K (ModuleCat.{w} R)] (hEF : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    (cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app S
        (cechCohomologyCup E hE μ hμ p q n h x y) =
      cechCohomologyCup F hF μ hμ p q n h
        ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF p hEF).app P x)
        ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF q hEF).app Q y) :=
  congrArg (fun f ↦ f x y) <| cechCohomology_bilinear_ext E hE
    (Φ := (cechCohomologyCup E hE μ hμ p q n h).compr₂
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF n hEF).app S).hom)
    (Ψ := (cechCohomologyCup F hF μ hμ p q n h).compl₁₂
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF p hEF).app P).hom
      ((cechCohomologyComparison (ModuleCat.{w} R) E hE F hF q hEF).app Q).hom) fun j a b ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, cechCohomologyCup_ι,
        cechCohomologyComparison_app_ι, cechCohomologyCup_toCechCohomology]

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
    ← cechCohomologyι_app_cechComplexHomologyMap E hE hik (hE hik).some P 0,
    ← cechCohomologyι_app_cechComplexHomologyMap E hE hjk (hE hjk).some P 0,
    homologyMap_cechComplexMap_cechUnitClass, homologyMap_cechComplexMap_cechUnitClass]

/-- `cechCohomologyUnitClass` is the image of `cechUnitClass` from any family `U` refined by `E`. -/
theorem cechCohomologyUnitClass_eq_toCechCohomology (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U)) :
    cechCohomologyUnitClass E hE P e he =
      (toCechCohomology (ModuleCat.{w} R) E hE 0 U hU).app P (cechUnitClass U.obj P e he) := by
  obtain ⟨j, ⟨φ⟩⟩ := hU
  rw [toCechCohomology_app_eq E hE U j φ P 0, homologyMap_cechComplexMap_cechUnitClass,
    cechCohomologyUnitClass_eq_ι E hE P e he j]

/-- Left unit law for `cechCohomologyCup`. -/
theorem cechCohomologyCup_unit_left (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] Q.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = Q.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (hl : ∀ X y, μ X (e X) y = y) (q : ℕ)
    (y : (cechCohomology (ModuleCat.{w} R) E hE q).obj Q) :
    cechCohomologyCup E hE μ hμ 0 q q (zero_add q) (cechCohomologyUnitClass E hE P e he) y = y :=
  LinearMap.congr_fun (cechCohomology_linear_ext E hE (g := LinearMap.id) fun j b ↦ by
    rw [LinearMap.id_apply, cechCohomologyUnitClass_eq_ι E hE P e he j, cechCohomologyCup_ι,
      cechComplexCup_unit_left (E j).obj μ hμ e he hl q b]) y

/-- Right unit law for `cechCohomologyCup`. -/
theorem cechCohomologyCup_unit_right (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = P.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ)
    (x : (cechCohomology (ModuleCat.{w} R) E hE p).obj P) :
    cechCohomologyCup E hE μ hμ p 0 p (add_zero p) x (cechCohomologyUnitClass E hE Q e he) = x :=
  LinearMap.congr_fun (cechCohomology_linear_ext E hE
    (f := (cechCohomologyCup E hE μ hμ p 0 p (add_zero p)).flip
      (cechCohomologyUnitClass E hE Q e he)) (g := LinearMap.id) fun j a ↦ by
    rw [LinearMap.flip_apply, LinearMap.id_apply, cechCohomologyUnitClass_eq_ι E hE Q e he j,
      cechCohomologyCup_ι, cechComplexCup_unit_right (E j).obj μ hμ e he hr p a]) x

/-- Morphisms of presheaves preserving compatible sections preserve `cechCohomologyUnitClass`. -/
theorem cechCohomology_map_cechCohomologyUnitClass (α : P ⟶ Q)
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Cᵒᵖ, Q.obj X) (heQ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (eQ X) = eQ Y)
    (hα : ∀ X, α.app X (eP X) = eQ X) :
    (cechCohomology (ModuleCat.{w} R) E hE 0).map α (cechCohomologyUnitClass E hE P eP heP) =
      cechCohomologyUnitClass E hE Q eQ heQ := by
  rw [cechCohomologyUnitClass_eq_ι E hE P eP heP (Classical.arbitrary J),
    cechCohomologyUnitClass_eq_ι E hE Q eQ heQ (Classical.arbitrary J),
    cechCohomology_map_ι, homologyMap_cechComplexFunctor_map_cechUnitClass _ α eP heP eQ heQ hα]

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
`cechCohomologyCup` in degree `0`. -/
theorem cechCohomologyCup_cechCohomologyZeroIso_hom
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (hQ : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT Q) 0)
    (hS : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT S) 0)
    (x : P.obj (op T)) (y : Q.obj (op T)) :
    cechCohomologyCup E hE μ hμ 0 0 0 rfl
        ((cechCohomologyZeroIso E hE hT P hP).hom x)
        ((cechCohomologyZeroIso E hE hT Q hQ).hom y) =
      (cechCohomologyZeroIso E hE hT S hS).hom (μ (op T) x y) := by
  rw [cechCohomologyZeroIso_hom_apply E hE hT P hP (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT Q hQ (Classical.arbitrary J),
    cechCohomologyZeroIso_hom_apply E hE hT S hS (Classical.arbitrary J), cechCohomologyCup_ι,
    cechComplexCup_homologyMap_cechAugmentation]

end Zero

end Cup

end TauCeti.CategoryTheory
