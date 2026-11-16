/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic

/-!
# The cup product on fixed-family Čech cohomology

Passing the cochain cup product `TauCeti.CategoryTheory.cechCupCochain` of
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic` to cocycles and cohomology yields an
`R`-bilinear pairing `TauCeti.CategoryTheory.cechComplexCup` on the cohomology of the fixed-family
Čech complex `Č(U, -)`.

Because `d_cechCupCochain` gives the graded Leibniz rule, the cup product of cocycles is a cocycle
and the cup product of a cocycle with a coboundary is a coboundary. The induced cohomology pairing
inherits associativity, left and right unit laws, naturality in both the family and the presheaves,
compatibility with the degree-`0` augmentation, and graded commutativity
(`TauCeti.CategoryTheory.cechComplexCup_comm`) via
`TauCeti.CategoryTheory.homologyMap_cechReverse_app`.

## Main definitions

* `TauCeti.CategoryTheory.cechCupCycles`: the `R`-bilinear cup product on Čech cocycles.
* `TauCeti.CategoryTheory.cechComplexCup`: the `R`-bilinear cup product on fixed-family Čech
  cohomology `Hᵖ(Č(U, P)) × H^q(Č(U, Q)) → Hⁿ(Č(U, S))` for `p + q = n`.
* `TauCeti.CategoryTheory.cechUnitClass`: the degree-`0` Čech cohomology class of a compatible
  family of sections.

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

open CategoryTheory Limits Opposite

universe uR w v v' u u'

namespace TauCeti.CategoryTheory

section Homology

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type w} (U : ι → C) {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}

/-- Cupping on the left with a fixed cocycle, as a morphism of cocycle modules. -/
private def cechCupCyclesLeft
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p) :
    ((cechComplexFunctor U).obj Q).cycles q ⟶ ((cechComplexFunctor U).obj S).cycles n :=
  ((cechComplexFunctor U).obj S).liftCycles
    (ModuleCat.ofHom
      ((cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)) ∘ₗ
        (((cechComplexFunctor U).obj Q).iCycles q).hom)) (n + 1) (by simp) (by
      ext b
      have hd := d_cechCupCochain U μ hμ p q n h
        (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b)
      rw [HomologicalComplex.iCycles_d_apply, HomologicalComplex.iCycles_d_apply,
        LinearMap.map_zero₂, map_zero, smul_zero, add_zero] at hd
      exact hd)

private lemma iCycles_cechCupCyclesLeft
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).iCycles n (cechCupCyclesLeft U μ hμ p q n h a b) =
      cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b) :=
  ConcreteCategory.congr_hom (((cechComplexFunctor U).obj S).liftCycles_i _ _ _ _) b

/-- The `R`-bilinear cup product on Čech cocycles. -/
def cechCupCycles (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).cycles p →ₗ[R]
      ((cechComplexFunctor U).obj Q).cycles q →ₗ[R]
        ((cechComplexFunctor U).obj S).cycles n where
  toFun a := (cechCupCyclesLeft U μ hμ p q n h a).hom
  map_add' a a' := LinearMap.ext fun b ↦ HomologicalComplex.moduleCat_iCycles_injective _ _ <| by
    simp [iCycles_cechCupCyclesLeft]
  map_smul' r a := LinearMap.ext fun b ↦ HomologicalComplex.moduleCat_iCycles_injective _ _ <| by
    simp [iCycles_cechCupCyclesLeft]

/-- On underlying cochains, `cechCupCycles` is `cechCupCochain`. -/
@[simp]
theorem iCycles_cechCupCycles (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).iCycles n (cechCupCycles U μ hμ p q n h a b) =
      cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b) :=
  iCycles_cechCupCyclesLeft U μ hμ p q n h a b

private lemma homologyπ_cechCupCycles_toCycles_right
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p)
    (i : ℕ) (x : ((cechComplexFunctor U).obj Q).X i) :
    ((cechComplexFunctor U).obj S).homologyπ n
      (cechCupCycles U μ hμ p q n h a (((cechComplexFunctor U).obj Q).toCycles i q x)) = 0 := by
  by_cases hiq : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := hiq
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + i, by omega⟩
    have key : cechCupCycles U μ hμ p (i + 1) (m + 1) h a
        (((cechComplexFunctor U).obj Q).toCycles i (i + 1) x) =
        (-1 : ℤ) ^ p • ((cechComplexFunctor U).obj S).toCycles m (m + 1)
          (cechCupCochain U μ p i m (by omega)
            (((cechComplexFunctor U).obj P).iCycles p a) x) := by
      have hd := d_cechCupCochain U μ hμ p i m (by omega)
        (((cechComplexFunctor U).obj P).iCycles p a) x
      rw [HomologicalComplex.iCycles_d_apply, LinearMap.map_zero₂, zero_add] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cechCupCycles, map_zsmul, ← ConcreteCategory.comp_apply,
        HomologicalComplex.toCycles_i, ← ConcreteCategory.comp_apply,
        HomologicalComplex.toCycles_i, hd, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
        one_smul]
    rw [key, map_zsmul, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  · rw [((cechComplexFunctor U).obj Q).toCycles_eq_zero hiq]
    simp

private lemma homologyπ_cechCupCycles_toCycles_left
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (i : ℕ) (x : ((cechComplexFunctor U).obj P).X i)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).homologyπ n
      (cechCupCycles U μ hμ p q n h (((cechComplexFunctor U).obj P).toCycles i p x) b) = 0 := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := hip
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨i + q, by omega⟩
    have key : cechCupCycles U μ hμ (i + 1) q (m + 1) h
        (((cechComplexFunctor U).obj P).toCycles i (i + 1) x) b =
        ((cechComplexFunctor U).obj S).toCycles m (m + 1)
          (cechCupCochain U μ i q m (by omega) x
            (((cechComplexFunctor U).obj Q).iCycles q b)) := by
      have hd := d_cechCupCochain U μ hμ i q m (by omega) x
        (((cechComplexFunctor U).obj Q).iCycles q b)
      rw [HomologicalComplex.iCycles_d_apply, map_zero, smul_zero, add_zero] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cechCupCycles, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i,
        ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, hd]
    rw [key, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    rfl
  · rw [((cechComplexFunctor U).obj P).toCycles_eq_zero hip]
    simp

private def cechComplexCupLeft
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p) :
    ((cechComplexFunctor U).obj Q).homology q ⟶ ((cechComplexFunctor U).obj S).homology n :=
  (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj Q).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cechCupCycles U μ hμ p q n h a) ≫
      ((cechComplexFunctor U).obj S).homologyπ n)
    (by
      ext x
      exact homologyπ_cechCupCycles_toCycles_right U μ hμ p q n h a _ x)).1

private lemma cechComplexCupLeft_homologyπ
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    (cechComplexCupLeft U μ hμ p q n h a) (((cechComplexFunctor U).obj Q).homologyπ q b) =
      ((cechComplexFunctor U).obj S).homologyπ n (cechCupCycles U μ hμ p q n h a b) := by
  unfold cechComplexCupLeft
  exact ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj Q).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cechCupCycles U μ hμ p q n h a) ≫
      ((cechComplexFunctor U).obj S).homologyπ n) _).2 b

private def cechCupCyclesHomology
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).cycles p ⟶
      ModuleCat.of R (((cechComplexFunctor U).obj Q).homology q →ₗ[R]
        ((cechComplexFunctor U).obj S).homology n) :=
  ModuleCat.ofHom (X := ((cechComplexFunctor U).obj P).cycles p)
    { toFun a := (cechComplexCupLeft U μ hμ p q n h a).hom
      map_add' a a' := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [LinearMap.add_apply]
        exact (cechComplexCupLeft_homologyπ U μ hμ p q n h (a + a') b).trans <| by
          rw [map_add, LinearMap.add_apply, map_add, cechComplexCupLeft_homologyπ,
            cechComplexCupLeft_homologyπ]
      map_smul' r a := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [LinearMap.smul_apply, RingHom.id_apply]
        exact (cechComplexCupLeft_homologyπ U μ hμ p q n h (r • a) b).trans <| by
          rw [map_smul, LinearMap.smul_apply, map_smul, cechComplexCupLeft_homologyπ] }

private lemma toCycles_comp_cechCupCyclesHomology
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).toCycles ((ComplexShape.up ℕ).prev p) p ≫
      cechCupCyclesHomology U μ hμ p q n h = 0 := by
  ext x : 2
  refine LinearMap.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  exact (cechComplexCupLeft_homologyπ U μ hμ p q n h _ b).trans
    (homologyπ_cechCupCycles_toCycles_left U μ hμ p q n h _ x b)

/-- **The cup product on fixed-family Čech cohomology.** For a natural `R`-bilinear pairing `μ`
and `p + q = n`, this is the `R`-bilinear pairing
`Hᵖ(Č(U, P)) →ₗ[R] H^q(Č(U, Q)) →ₗ[R] Hⁿ(Č(U, S))` induced by `cechCupCochain`. -/
def cechComplexCup (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).homology p →ₗ[R]
      ((cechComplexFunctor U).obj Q).homology q →ₗ[R]
        ((cechComplexFunctor U).obj S).homology n :=
  (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj P).homologyIsCokernel _ p rfl)
    (cechCupCyclesHomology U μ hμ p q n h)
    (toCycles_comp_cechCupCyclesHomology U μ hμ p q n h)).1.hom

/-- On cohomology classes of cocycles, `cechComplexCup` is the class of `cechCupCycles`. -/
@[simp]
theorem cechComplexCup_homologyπ (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).cycles p)
    (b : ((cechComplexFunctor U).obj Q).cycles q) :
    cechComplexCup U μ hμ p q n h
        (((cechComplexFunctor U).obj P).homologyπ p a)
        (((cechComplexFunctor U).obj Q).homologyπ q b) =
      ((cechComplexFunctor U).obj S).homologyπ n (cechCupCycles U μ hμ p q n h a b) := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj P).homologyIsCokernel _ p rfl)
    (cechCupCyclesHomology U μ hμ p q n h)
    (toCycles_comp_cechCupCyclesHomology U μ hμ p q n h)).2 a
  rw [cechComplexCup, ← cechComplexCupLeft_homologyπ]
  exact LinearMap.congr_fun hfac _

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
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r z
  simp only [cechComplexCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [iCycles_cechCupCycles]
  exact cechCupCochain_assoc U μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' hμ₁₂ hμ₂₃ hassoc p q r pq qr n hpq hqr hn _ _ _

/-- **Graded commutativity of the cup product on fixed-family Čech cohomology.** -/
theorem cechComplexCup_comm
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
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  -- Transport `x`, `y`, and their cup product along `homologyMap ((cechReverse U).app _) = 𝟙 _`.
  have hS : HomologicalComplex.homologyMap ((cechReverse U).app S) n
      (cechComplexCup U μ' hμ' q p n (by omega)
        (HomologicalComplex.homologyMap ((cechReverse U).app Q) q
          (((cechComplexFunctor U).obj Q).homologyπ q b))
        (HomologicalComplex.homologyMap ((cechReverse U).app P) p
          (((cechComplexFunctor U).obj P).homologyπ p a))) =
      cechComplexCup U μ' hμ' q p n (by omega)
        (((cechComplexFunctor U).obj Q).homologyπ q b)
        (((cechComplexFunctor U).obj P).homologyπ p a) := by
    simp [homologyMap_cechReverse_app]
  rw [← hS, HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechComplexCup_homologyπ,
    cechComplexCup_homologyπ, HomologicalComplex.moduleCat_homologyMap_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles, map_zsmul,
    iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  exact cechReverse_cechCupCochain U μ μ' hμ' hcomm p q n h _ _

/-- Any triple of cochain maps between Čech complexes that commutes with `cechCupCochain` in
degrees `p`, `q`, `n` commutes with `cechComplexCup` on cohomology. -/
theorem homologyMap_cechComplexCup_of_f {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
    {κ : Type w} {V : κ → D} {P' Q' S' : Dᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Dᵒᵖ, P'.obj X →ₗ[R] Q'.obj X →ₗ[R] S'.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (hμ' : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y) x y, μ' Y (P'.map f x) (Q'.map f y) = S'.map f (μ' X x y))
    (φP : (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj P')
    (φQ : (cechComplexFunctor U).obj Q ⟶ (cechComplexFunctor V).obj Q')
    (φS : (cechComplexFunctor U).obj S ⟶ (cechComplexFunctor V).obj S')
    (p q n : ℕ) (h : p + q = n)
    (hφ : ∀ a b, φS.f n (cechCupCochain U μ p q n h a b) =
      cechCupCochain V μ' p q n h (φP.f p a) (φQ.f q b))
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    HomologicalComplex.homologyMap φS n (cechComplexCup U μ hμ p q n h x y) =
      cechComplexCup V μ' hμ' p q n h
        (HomologicalComplex.homologyMap φP p x) (HomologicalComplex.homologyMap φQ q y) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  rw [cechComplexCup_homologyπ, HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechComplexCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles,
    iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  exact hφ _ _

/-- Compatibility of the cup product on fixed-family Čech cohomology with morphisms of families. -/
theorem cechComplexCup_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor V).obj P).homology p)
    (y : ((cechComplexFunctor V).obj Q).homology q) :
    HomologicalComplex.homologyMap (cechComplexMap S φ) n (cechComplexCup V μ hμ p q n h x y) =
      cechComplexCup U μ hμ p q n h
        (HomologicalComplex.homologyMap (cechComplexMap P φ) p x)
        (HomologicalComplex.homologyMap (cechComplexMap Q φ) q y) :=
  homologyMap_cechComplexCup_of_f V μ μ hμ hμ
    (cechComplexMap P φ) (cechComplexMap Q φ) (cechComplexMap S φ) p q n h
    (cechComplexMap_cechCupCochain U φ μ hμ p q n h) x y

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
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map γ) n
        (cechComplexCup U μ hμ p q n h x y) =
      cechComplexCup U μ' hμ' p q n h
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) p x)
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map β) q y) :=
  homologyMap_cechComplexCup_of_f U μ μ' hμ hμ'
    ((cechComplexFunctor U).map α) ((cechComplexFunctor U).map β) ((cechComplexFunctor U).map γ)
    p q n h (cechComplexFunctor_map_cechCupCochain U μ μ' α β γ hγ p q n h) x y

/-- The degree-`0` Čech cohomology class of a compatible family of sections `e`. -/
def cechUnitClass (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    ((cechComplexFunctor U).obj P).homology 0 :=
  ((cechComplexFunctor U).obj P).homologyπ 0 <|
    HomologicalComplex.moduleCatCyclesMk ((cechComplexFunctor U).obj P) (n := 0)
      (cechUnitCochain U P e) 1 (by simp) (d_cechUnitCochain U P e he)

/-- Left unit law for `cechComplexCup`. -/
theorem cechComplexCup_unit_left (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] Q.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = Q.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (hl : ∀ X y, μ X (e X) y = y) (q : ℕ) (y : ((cechComplexFunctor U).obj Q).homology q) :
    cechComplexCup U μ hμ 0 q q (zero_add q) (cechUnitClass U P e he) y = y := by
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  rw [cechUnitClass, cechComplexCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.iCycles_moduleCatCyclesMk]
  exact cechCupCochain_unit_left U μ e he hl q _

/-- Right unit law for `cechComplexCup`. -/
theorem cechComplexCup_unit_right (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = P.map f (μ X x y))
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ) (x : ((cechComplexFunctor U).obj P).homology p) :
    cechComplexCup U μ hμ p 0 p (add_zero p) x (cechUnitClass U Q e he) = x := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  rw [cechUnitClass, cechComplexCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.iCycles_moduleCatCyclesMk]
  exact cechCupCochain_unit_right U μ e he hr p _

/-- Any cochain map sending `cechUnitCochain` to `cechUnitCochain` sends `cechUnitClass` to
`cechUnitClass`. -/
theorem homologyMap_cechUnitClass_of_f_zero {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
    {κ : Type w} {V : κ → D} {Q' : Dᵒᵖ ⥤ ModuleCat.{w} R}
    (φ : (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj Q')
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Dᵒᵖ, Q'.obj X) (heQ : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y), Q'.map f (eQ X) = eQ Y)
    (hφ : φ.f 0 (cechUnitCochain U P eP) = cechUnitCochain V Q' eQ) :
    HomologicalComplex.homologyMap φ 0 (cechUnitClass U P eP heP) =
      cechUnitClass V Q' eQ heQ := by
  rw [cechUnitClass, cechUnitClass, HomologicalComplex.moduleCat_homologyMap_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk]
  exact hφ

/-- Morphisms of families preserve `cechUnitClass`. -/
theorem homologyMap_cechComplexMap_cechUnitClass {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) 0 (cechUnitClass V P e he) =
      cechUnitClass U P e he :=
  homologyMap_cechUnitClass_of_f_zero V (cechComplexMap P φ) e he e he
    (cechComplexMap_cechUnitCochain U φ P e he)

/-- Morphisms of presheaves preserving compatible unit sections preserve `cechUnitClass`. -/
theorem homologyMap_cechComplexFunctor_map_cechUnitClass (α : P ⟶ Q)
    (eP : ∀ X : Cᵒᵖ, P.obj X) (heP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (eP X) = eP Y)
    (eQ : ∀ X : Cᵒᵖ, Q.obj X) (heQ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (eQ X) = eQ Y)
    (hα : ∀ X, α.app X (eP X) = eQ X) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) 0 (cechUnitClass U P eP heP) =
      cechUnitClass U Q eQ heQ :=
  homologyMap_cechUnitClass_of_f_zero U ((cechComplexFunctor U).map α) eP heP eQ heQ
    (cechComplexFunctor_map_cechUnitCochain U α eP eQ hα)

/-- The degree-`0` augmentation sends a global section `e₀ ∈ P(T)` to the `cechUnitClass` of its
restrictions. -/
theorem cechUnitClass_eq_homologyMap_cechAugmentation {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e₀ : P.obj (op T)) :
    HomologicalComplex.homologyMap (cechAugmentation U hT P) 0
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          (P.obj (op T))).inv e₀) =
      cechUnitClass U P (fun X ↦ P.map (hT.from X.unop).op e₀)
        (fun {X Y} f ↦ by
          rw [← ModuleCat.comp_apply, ← P.map_comp]
          have hcomp : (hT.from X.unop).op ≫ f = (hT.from Y.unop).op :=
            Quiver.Hom.unop_inj (hT.hom_ext (f.unop ≫ hT.from X.unop) (hT.from Y.unop))
          rw [hcomp]) := by
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, ModuleCat.comp_apply,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechUnitClass]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  have hsc : ((CochainComplex.single₀ (ModuleCat.{w} R)).obj (P.obj (op T))).iCycles 0
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀ :=
    (ConcreteCategory.comp_apply _ _ e₀).symm.trans <|
      ConcreteCategory.congr_hom
        (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (ComplexShape.up ℕ) 0
          (P.obj (op T))) e₀
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hsc,
    HomologicalComplex.iCycles_moduleCatCyclesMk]
  exact cechAugmentation_f_zero_eq_cechUnitCochain U hT P e₀

/-- The degree-`0` augmentation intertwines `μ (op T)` with `cechComplexCup` in degree `0`. -/
theorem cechComplexCup_homologyMap_cechAugmentation {T : C} (hT : IsTerminal T)
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (x : P.obj (op T)) (y : Q.obj (op T)) :
    cechComplexCup U μ hμ 0 0 0 rfl
        (HomologicalComplex.homologyMap (cechAugmentation U hT P) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (P.obj (op T))).inv x))
        (HomologicalComplex.homologyMap (cechAugmentation U hT Q) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (Q.obj (op T))).inv y)) =
      HomologicalComplex.homologyMap (cechAugmentation U hT S) 0
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (S.obj (op T))).inv
          (μ (op T) x y)) := by
  rw [cechUnitClass_eq_homologyMap_cechAugmentation, cechUnitClass_eq_homologyMap_cechAugmentation,
    cechUnitClass_eq_homologyMap_cechAugmentation, cechUnitClass, cechUnitClass, cechUnitClass,
    cechComplexCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.iCycles_moduleCatCyclesMk,
    HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk]
  refine cechComplex_ext fun c ↦ ?_
  rw [cechCupCochain_π, cechUnitCochain_π, cechUnitCochain_π, cechUnitCochain_π,
    ← ModuleCat.comp_apply, ← P.map_comp, ← op_comp, ← ModuleCat.comp_apply, ← Q.map_comp,
    ← op_comp, hT.hom_ext (_ ≫ hT.from _) (hT.from _), hT.hom_ext (_ ≫ hT.from _) (hT.from _), hμ]

end Homology

end TauCeti.CategoryTheory
