/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.ModuleCat
import TauCeti.Data.Fin.Basic

/-!
# The cup product on Čech complexes

Let `C` be a category with finite products, `U : ι → C` a family of objects, for instance an open
cover of a topological space, and `R` a commutative ring.

For presheaves of `R`-modules `P, Q, S : Cᵒᵖ ⥤ ModuleCat R` equipped with a natural `R`-bilinear
pairing `μ : ∀ X, P(X) →ₗ[R] Q(X) →ₗ[R] S(X)`, the Alexander–Whitney front/back face formula
restricts a `p`-cochain `a ∈ Čᵖ(U, P)` along the front projection from
`U(c 0) × ⋯ × U(c (p + q))` to `U(c 0) × ⋯ × U(c p)` and a `q`-cochain `b ∈ Č^q(U, Q)` along the
back projection to `U(c p) × ⋯ × U(c (p + q))`, and pairs them via `μ`. This defines an
`R`-bilinear cup product `TauCeti.CategoryTheory.cechCupCochain` on Čech cochains satisfying:

* the **graded Leibniz rule** `d (a ⌣ b) = d a ⌣ b + (-1)^p • (a ⌣ d b)`
  (`TauCeti.CategoryTheory.d_cechCupCochain`);
* **associativity** for associative pairings (`TauCeti.CategoryTheory.cechCupCochain_assoc`);
* **left and right unit laws** for compatible families of unit sections
  (`TauCeti.CategoryTheory.cechCupCochain_unit_left`,
  `TauCeti.CategoryTheory.cechCupCochain_unit_right`);
* **naturality** with respect to morphisms of families
  (`TauCeti.CategoryTheory.cechComplexMap_cechCupCochain`) and morphisms of presheaves
  (`TauCeti.CategoryTheory.cechComplexFunctor_map_cechCupCochain`).

Specializing to a presheaf of `R`-algebras `F : Cᵒᵖ ⥤ AlgCat R` (`cechAlgebraComplex U F`) with
multiplication `LinearMap.mul R (F.obj X)` yields the cup product `TauCeti.CategoryTheory.cechCup`
and unit cochain `TauCeti.CategoryTheory.cechOne`, satisfying:

* the **Leibniz rule** `d (a ⌣ b) = d a ⌣ b + (-1) ^ p a ⌣ d b`
  (`TauCeti.CategoryTheory.d_cechCup`), so the product of two cocycles is a cocycle and the
  product of a coboundary and a cocycle is a coboundary
  (`TauCeti.CategoryTheory.d_cechCup_eq_zero`, `TauCeti.CategoryTheory.cechCup_d_left`,
  `TauCeti.CategoryTheory.cechCup_d_right`);
* **associativity** (`TauCeti.CategoryTheory.cechCup_assoc`);
* **two-sided unit** (`TauCeti.CategoryTheory.d_cechOne`, `TauCeti.CategoryTheory.cechOne_cechCup`,
  `TauCeti.CategoryTheory.cechCup_cechOne`);
* **naturality** for morphisms of families (`TauCeti.CategoryTheory.cechComplexMap_cechCup`,
  `TauCeti.CategoryTheory.cechComplexMap_cechOne`), morphisms of presheaves of algebras
  (`TauCeti.CategoryTheory.cechComplexFunctor_map_cechCup`,
  `TauCeti.CategoryTheory.cechComplexFunctor_map_cechOne`), and the comparison
  `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` along a functor `G` preserving the products of members
  (`TauCeti.CategoryTheory.cechComplexCompIso_hom_cechCup`,
  `TauCeti.CategoryTheory.cechComplexCompIso_inv_cechCup`).

Algebra cochains are handled through their factors (`TauCeti.CategoryTheory.cechComponent`) and
vertex restrictions (`TauCeti.CategoryTheory.cechFace`). No thinness hypothesis on `C` and no
ordering on `ι` are needed. The reversal identity is in
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Reverse`, and the passage to fixed-family Čech
cohomology is in `TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology`.

## Main definitions

* `TauCeti.CategoryTheory.cechCupCochain`: the `R`-bilinear cup product on Čech cochains for a
  natural bilinear pairing of presheaves of modules.
* `TauCeti.CategoryTheory.cechUnitCochain`: the `0`-cochain determined by a compatible family of
  sections.
* `TauCeti.CategoryTheory.cechAlgebraComplex`: the Čech complex of a presheaf of `R`-algebras.
* `TauCeti.CategoryTheory.cechComponent` and `TauCeti.CategoryTheory.cechFace`: factors and
  vertex restrictions of algebra Čech cochains.
* `TauCeti.CategoryTheory.cechCup` and `TauCeti.CategoryTheory.cechOne`: the cup product and unit
  cochain for a presheaf of `R`-algebras.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP), for the cup product on Čech
  cochains, the Leibniz rule, associativity, and graded commutativity.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe uR w v v' u u'

namespace TauCeti.CategoryTheory

/-! ### The cup product on Čech cochains for general bilinear pairings -/

section Cochain

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type w} (U : ι → C) {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}

/-- **The cup product on Čech cochains.** Given a family of `R`-bilinear pairings
`μ : ∀ X, P(X) →ₗ[R] Q(X) →ₗ[R] S(X)` and `p + q = n`, on a tuple `c : Fin (n + 1) → ι` the cup
product of `a ∈ Čᵖ(U, P)` and `b ∈ Č^q(U, Q)` restricts `a` along the front projection to
`c 0, …, c p`, restricts `b` along the back projection to `c p, …, c n`, and applies `μ`. -/
def cechCupCochain (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).X p →ₗ[R] ((cechComplexFunctor U).obj Q).X q →ₗ[R]
      ((cechComplexFunctor U).obj S).X n :=
  LinearMap.mk₂ R
    (fun a b ↦ cechCochainMk U S n fun c ↦
      μ (op (∏ᶜ fun j ↦ U (c j)))
        (P.map (Pi.map' (Fin.castLE (by omega : p + 1 ≤ n + 1)) (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U P p (c ∘ Fin.castLE (by omega)) a))
        (Q.map (Pi.map' (fun i : Fin (q + 1) ↦ Fin.cast (by omega) (Fin.natAdd p i))
            (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U Q q (c ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b)))
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)

/-- The coordinate formula for `cechCupCochain` at a tuple `c : Fin (n + 1) → ι`. -/
@[simp]
theorem cechCupCochain_π (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 1) → ι) :
    cechComplexπ U S n c (cechCupCochain U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (c j)))
        (P.map (Pi.map' (Fin.castLE (by omega : p + 1 ≤ n + 1)) (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U P p (c ∘ Fin.castLE (by omega)) a))
        (Q.map (Pi.map' (fun i : Fin (q + 1) ↦ Fin.cast (by omega) (Fin.natAdd p i))
            (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U Q q (c ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b)) :=
  cechComplexπ_cechCochainMk U S n _ c

private def cupCochainTerm (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    {p q n : ℕ} (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) (f : Fin (p + 1) → Fin (n + 2)) (g : Fin (q + 1) → Fin (n + 2)) :
    S.obj (op (∏ᶜ fun j : Fin (n + 2) ↦ U (c j))) :=
  μ (op (∏ᶜ fun j ↦ U (c j)))
    (P.map (Pi.map' f (fun _ ↦ 𝟙 _)).op (cechComplexπ U P p (c ∘ f) a))
    (Q.map (Pi.map' g (fun _ ↦ 𝟙 _)).op (cechComplexπ U Q q (c ∘ g) b))

private lemma d_cechCupCochain_lhs (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : P.obj X) (y : Q.obj X),
      μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) :
    cechComplexπ U S (n + 1) c
        (((cechComplexFunctor U).obj S).d n (n + 1) (cechCupCochain U μ p q n h a b)) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        cupCochainTerm U μ a b c (k.succAbove ∘ Fin.castLE (by omega))
          (k.succAbove ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) := by
  rw [cechComplexπ_d]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg _ ?_
  rw [cechCupCochain_π]
  dsimp only [Function.comp_def]
  rw [← hμ, cechComplexπ_map_piMap'_comp, cechComplexπ_map_piMap'_comp]
  rfl

private lemma d_cechCupCochain_rhs₁ (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) :
    cechComplexπ U S (n + 1) c (cechCupCochain U μ (p + 1) q (n + 1) (by omega)
        (((cechComplexFunctor U).obj P).d p (p + 1) a) b) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        cupCochainTerm U μ a b c (Fin.castLE (by omega) ∘ i.succAbove)
          (fun i ↦ Fin.cast (by omega) (Fin.natAdd (p + 1) i)) := by
  rw [cechCupCochain_π, cechComplexπ_d, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply]
  dsimp only [Function.comp_def]
  rw [cechComplexπ_map_piMap'_comp]
  rfl

private lemma d_cechCupCochain_rhs₂ (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) :
    cechComplexπ U S (n + 1) c ((-1 : ℤ) ^ p •
        cechCupCochain U μ p (q + 1) (n + 1) (by omega) a
          (((cechComplexFunctor U).obj Q).d q (q + 1) b)) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (p + (j : ℕ)) •
        cupCochainTerm U μ a b c (Fin.castLE (by omega))
          ((fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) ∘ j.succAbove) := by
  rw [map_zsmul, cechCupCochain_π, cechComplexπ_d, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_zsmul, smul_smul, ← pow_add]
  dsimp only [Function.comp_def]
  rw [cechComplexπ_map_piMap'_comp]
  rfl

private lemma d_cechCupCochain_castAdd (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    {p q n : ℕ} (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) (i : Fin (p + 1)) :
    (-1 : ℤ) ^ ((finCongr (by omega : (p + 1) + (q + 1) = n + 2) (i.castAdd (q + 1)) :
          Fin (n + 2)) : ℕ) •
        cupCochainTerm U μ a b c
          ((finCongr (by omega : (p + 1) + (q + 1) = n + 2) (i.castAdd (q + 1))).succAbove ∘
            Fin.castLE (by omega))
          ((finCongr (by omega : (p + 1) + (q + 1) = n + 2) (i.castAdd (q + 1))).succAbove ∘
            fun x ↦ Fin.cast (by omega) (Fin.natAdd p x)) =
      (-1 : ℤ) ^ (i.castSucc : ℕ) •
        cupCochainTerm U μ a b c (Fin.castLE (by omega) ∘ i.castSucc.succAbove)
          (fun x ↦ Fin.cast (by omega) (Fin.natAdd (p + 1) x)) := by
  refine congrArg₂ (· • ·) (by simp) (congrArg₂ (cupCochainTerm U μ a b c) ?_ ?_)
  · funext x; ext
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, finCongr_apply,
      Fin.val_cast, Fin.val_castAdd, Fin.val_castLE]
    split_ifs <;> simp
  · funext y; ext
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, finCongr_apply,
      Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    split_ifs <;> simp <;> omega

private lemma d_cechCupCochain_natAdd (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    {p q n : ℕ} (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 2) → ι) (j : Fin (q + 1)) :
    (-1 : ℤ) ^ ((finCongr (by omega : (p + 1) + (q + 1) = n + 2)
          (Fin.natAdd (p + 1) j) : Fin (n + 2)) : ℕ) •
        cupCochainTerm U μ a b c
          ((finCongr (by omega : (p + 1) + (q + 1) = n + 2)
            (Fin.natAdd (p + 1) j)).succAbove ∘ Fin.castLE (by omega))
          ((finCongr (by omega : (p + 1) + (q + 1) = n + 2)
            (Fin.natAdd (p + 1) j)).succAbove ∘ fun x ↦ Fin.cast (by omega) (Fin.natAdd p x)) =
      (-1 : ℤ) ^ (p + (j.succ : ℕ)) •
        cupCochainTerm U μ a b c (Fin.castLE (by omega))
          ((fun x ↦ Fin.cast (by omega) (Fin.natAdd p x)) ∘ j.succ.succAbove) := by
  refine congrArg₂ (· • ·) (by congr 1; simp; omega)
    (congrArg₂ (cupCochainTerm U μ a b c) ?_ ?_)
  · funext x; ext
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, finCongr_apply,
      Fin.val_cast, Fin.val_natAdd, Fin.val_castLE]
    split_ifs <;> simp
    omega
  · funext y; ext
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
      finCongr_apply, Fin.val_cast, Fin.val_natAdd]
    split_ifs <;> simp <;> omega

/-- **The graded Leibniz rule for the Čech cup product.** For a natural bilinear pairing `μ`,
`d (a ⌣ b) = d a ⌣ b + (-1)^p • (a ⌣ d b)`. -/
theorem d_cechCupCochain (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : P.obj X) (y : Q.obj X),
      μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechComplexFunctor U).obj S).d n (n + 1) (cechCupCochain U μ p q n h a b) =
      cechCupCochain U μ (p + 1) q (n + 1) (by omega)
          (((cechComplexFunctor U).obj P).d p (p + 1) a) b +
        (-1 : ℤ) ^ p • cechCupCochain U μ p (q + 1) (n + 1) (by omega) a
          (((cechComplexFunctor U).obj Q).d q (q + 1) b) := by
  refine cechComplex_ext fun c ↦ ?_
  -- the faces `j ≤ p` of `a ⌣ b` are the faces of `d a`, the faces `j ≥ p + 1` those of `d b`,
  -- and the last face of `d a` cancels the first face of `d b`
  have hfront : (Fin.castLE (by omega : p + 1 + 1 ≤ n + 2) ∘ (Fin.last (p + 1)).succAbove) =
      Fin.castLE (by omega) := by
    rw [Fin.succAbove_last, Fin.castLE_comp_castSucc]
  have hback : ((fun i : Fin (q + 2) ↦ Fin.cast (by omega : p + (q + 1) + 1 = n + 2)
        (Fin.natAdd p i)) ∘ (0 : Fin (q + 2)).succAbove) =
      fun i : Fin (q + 1) ↦ Fin.cast (by omega : p + 1 + q + 1 = n + 2) (Fin.natAdd (p + 1) i) := by
    funext y; ext; simp; omega
  -- the last face of `d a` (for `i = Fin.last (p + 1)`) cancels the first face of `(-1)^p • d b`
  -- (for `j = 0`), since both restrict `a` to `[0..p]` and `b` to `[p+1..p+q+1]` with opposite
  -- signs
  have hcancel :
      (-1 : ℤ) ^ (Fin.last (p + 1) : ℕ) •
          cupCochainTerm U μ a b c (Fin.castLE (by omega) ∘ (Fin.last (p + 1)).succAbove)
            (fun i ↦ Fin.cast (by omega) (Fin.natAdd (p + 1) i)) +
        (-1 : ℤ) ^ (p + ((0 : Fin (q + 2)) : ℕ)) •
          cupCochainTerm U μ a b c (Fin.castLE (by omega))
            ((fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) ∘ (0 : Fin (q + 2)).succAbove) =
        0 := by
    rw [hfront, hback]
    simp [pow_succ]
  rw [map_add, d_cechCupCochain_lhs U μ hμ p q n h a b c, d_cechCupCochain_rhs₁ U μ p q n h a b c,
    d_cechCupCochain_rhs₂ U μ p q n h a b c, Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1)]
  let e := finCongr (by omega : (p + 1) + (q + 1) = n + 2)
  rw [← Fintype.sum_equiv e (fun k ↦ (-1 : ℤ) ^ ((e k : Fin (n + 2)) : ℕ) •
      cupCochainTerm U μ a b c ((e k).succAbove ∘ Fin.castLE (by omega))
        ((e k).succAbove ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)))
    _ (fun _ ↦ rfl), Fin.sum_univ_add,
    Finset.sum_congr rfl fun i _ ↦ d_cechCupCochain_castAdd U μ h a b c i,
    Finset.sum_congr rfl fun j _ ↦ d_cechCupCochain_natAdd U μ h a b c j]
  refine Eq.trans (add_zero _).symm ?_
  rw [← hcancel]
  abel

/-- **Associativity of the Čech cup product on cochains.** -/
theorem cechCupCochain_assoc {P₁ P₂ P₃ P₁₂ P₂₃ P₁₂₃ : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ₁₂ : ∀ X, P₁.obj X →ₗ[R] P₂.obj X →ₗ[R] P₁₂.obj X)
    (μ₁₂₃ : ∀ X, P₁₂.obj X →ₗ[R] P₃.obj X →ₗ[R] P₁₂₃.obj X)
    (μ₂₃ : ∀ X, P₂.obj X →ₗ[R] P₃.obj X →ₗ[R] P₂₃.obj X)
    (μ₁₂₃' : ∀ X, P₁.obj X →ₗ[R] P₂₃.obj X →ₗ[R] P₁₂₃.obj X)
    (hμ₁₂ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ₁₂ Y (P₁.map f x) (P₂.map f y) = P₁₂.map f (μ₁₂ X x y))
    (hμ₂₃ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y z, μ₂₃ Y (P₂.map f y) (P₃.map f z) = P₂₃.map f (μ₂₃ X y z))
    (hassoc : ∀ X x y z, μ₁₂₃ X (μ₁₂ X x y) z = μ₁₂₃' X x (μ₂₃ X y z))
    (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n)
    (a : ((cechComplexFunctor U).obj P₁).X p) (b : ((cechComplexFunctor U).obj P₂).X q)
    (c : ((cechComplexFunctor U).obj P₃).X r) :
    cechCupCochain U μ₁₂₃ pq r n hn (cechCupCochain U μ₁₂ p q pq hpq a b) c =
      cechCupCochain U μ₁₂₃' p qr n (by omega) a (cechCupCochain U μ₂₃ q r qr hqr b c) := by
  refine cechComplex_ext fun d ↦ ?_
  simp only [cechCupCochain_π]
  dsimp only [Function.comp_def]
  rw [← hμ₁₂, ← hμ₂₃, cechComplexπ_map_piMap'_comp, cechComplexπ_map_piMap'_comp,
    cechComplexπ_map_piMap'_comp, cechComplexπ_map_piMap'_comp, hassoc]
  refine congrArg₂ (fun x y ↦ μ₁₂₃' _ x y)
    (cechComplexπ_map_piMap'_eq_of_val U P₁ d (fun j ↦ rfl) a)
    (congrArg₂ (fun y z ↦ μ₂₃ _ y z)
      (cechComplexπ_map_piMap'_eq_of_val U P₂ d (fun j ↦ rfl) b)
      (cechComplexπ_map_piMap'_eq_of_val U P₃ d (fun j ↦ by simp; omega) c))

/-- Compatibility of the Čech cup product on cochains with a morphism of families. -/
theorem cechComplexMap_cechCupCochain {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (hμ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) x y, μ Y (P.map f x) (Q.map f y) = S.map f (μ X x y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor V).obj P).X p) (b : ((cechComplexFunctor V).obj Q).X q) :
    (cechComplexMap S φ).f n (cechCupCochain V μ p q n h a b) =
      cechCupCochain U μ p q n h ((cechComplexMap P φ).f p a) ((cechComplexMap Q φ).f q b) := by
  refine cechComplex_ext fun c ↦ ?_
  simp only [cechComplexπ_cechComplexMap, cechCupCochain_π, ← hμ, ← Functor.map_comp_apply,
    ← op_comp, Pi.map'_comp_map, Pi.map_comp_map', Category.id_comp, Category.comp_id]
  -- `φ.f ∘ c ∘ _` and `(φ.f ∘ c) ∘ _` are definitionally equal tuple reindexings
  rfl

/-- Naturality of the Čech cup product on cochains with respect to morphisms of presheaves. -/
theorem cechComplexFunctor_map_cechCupCochain {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, P'.obj X →ₗ[R] Q'.obj X →ₗ[R] S'.obj X)
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ X x y, γ.app X (μ X x y) = μ' X (α.app X x) (β.app X y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechComplexFunctor U).map γ).f n (cechCupCochain U μ p q n h a b) =
      cechCupCochain U μ' p q n h (((cechComplexFunctor U).map α).f p a)
        (((cechComplexFunctor U).map β).f q b) := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechComplexπ_cechComplexFunctor_map, cechCupCochain_π, cechCupCochain_π, hγ,
    cechComplexπ_cechComplexFunctor_map, cechComplexπ_cechComplexFunctor_map,
    NatTrans.naturality_apply, NatTrans.naturality_apply]
  -- `NatTrans.naturality_apply` produces `(α.app (op _)) (P.map ...)` where the products
  -- `∏ᶜ fun j ↦ U ((c ∘ f) j)` and `∏ᶜ fun x ↦ U (c (f x))` are definitionally equal
  rfl

/-! ### Unit cochains and degree-zero augmentation -/

/-- The `0`-cochain determined by a family of sections `e : ∀ X, P.obj X`. -/
def cechUnitCochain (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X) :
    ((cechComplexFunctor U).obj P).X 0 :=
  cechCochainMk U P 0 fun a ↦ e (op (∏ᶜ fun j ↦ U (a j)))

/-- The tuple projection of `cechUnitCochain` evaluates `e` on the singleton product. -/
@[simp]
theorem cechUnitCochain_π (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X) (a : Fin 1 → ι) :
    cechComplexπ U P 0 a (cechUnitCochain U P e) = e (op (∏ᶜ fun j ↦ U (a j))) :=
  cechComplexπ_cechCochainMk U P 0 _ a

/-- A compatible family of sections defines a `0`-cocycle in `Č(U, P)`. -/
theorem d_cechUnitCochain (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e : ∀ X : Cᵒᵖ, P.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    ((cechComplexFunctor U).obj P).d 0 1 (cechUnitCochain U P e) = 0 := by
  refine cechComplex_ext fun k ↦ ?_
  rw [cechComplexπ_d, map_zero]
  simp [cechUnitCochain_π, he]

/-- Left unit law for `cechCupCochain`. -/
theorem cechCupCochain_unit_left (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] Q.obj X)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y)
    (hl : ∀ X y, μ X (e X) y = y) (q : ℕ) (b : ((cechComplexFunctor U).obj Q).X q) :
    cechCupCochain U μ 0 q q (zero_add q) (cechUnitCochain U P e) b = b := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechCupCochain_π, cechUnitCochain_π]
  dsimp only [Function.comp_def]
  rw [he, hl]
  exact cechComplexπ_map_piMap'_id U Q c (fun j ↦ by simp) b

/-- Right unit law for `cechCupCochain`. -/
theorem cechCupCochain_unit_right (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ) (a : ((cechComplexFunctor U).obj P).X p) :
    cechCupCochain U μ p 0 p (add_zero p) a (cechUnitCochain U Q e) = a := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechCupCochain_π, cechUnitCochain_π]
  dsimp only [Function.comp_def]
  rw [he, hr]
  exact cechComplexπ_map_piMap'_id U P c (fun j ↦ by simp) a

/-- Morphisms of families send `cechUnitCochain` to `cechUnitCochain`. -/
theorem cechComplexMap_cechUnitCochain {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (e : ∀ X : Cᵒᵖ, P.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), P.map f (e X) = e Y) :
    (cechComplexMap P φ).f 0 (cechUnitCochain V P e) = cechUnitCochain U P e := by
  refine cechComplex_ext fun a ↦ ?_
  rw [cechComplexπ_cechComplexMap, cechUnitCochain_π, cechUnitCochain_π, he]

/-- Morphisms of presheaves preserving compatible sections send `cechUnitCochain` to
`cechUnitCochain`. -/
theorem cechComplexFunctor_map_cechUnitCochain (α : P ⟶ Q)
    (eP : ∀ X : Cᵒᵖ, P.obj X) (eQ : ∀ X : Cᵒᵖ, Q.obj X)
    (hα : ∀ X, α.app X (eP X) = eQ X) :
    ((cechComplexFunctor U).map α).f 0 (cechUnitCochain U P eP) = cechUnitCochain U Q eQ := by
  refine cechComplex_ext fun a ↦ ?_
  rw [cechComplexπ_cechComplexFunctor_map, cechUnitCochain_π, cechUnitCochain_π, hα]

/-- The degree-`0` augmentation of a global section `e₀ ∈ P(T)` is `cechUnitCochain` for its
restrictions to all objects. -/
theorem cechAugmentation_f_zero_eq_cechUnitCochain {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e₀ : P.obj (op T)) :
    (cechAugmentation U hT P).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) =
      cechUnitCochain U P (fun X ↦ P.map (hT.from X.unop).op e₀) := by
  refine cechComplex_ext fun a ↦ ?_
  rw [cechComplexπ_cechAugmentation, cechUnitCochain_π]

end Cochain

/-! ### Specialization to presheaves of algebras -/

section Algebra

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} {U : ι → C}
  {R : Type u'} [CommRing R] {F : Cᵒᵖ ⥤ AlgCat.{w} R}

section Components

variable (U F) in
/-- The Čech complex, for the family `U`, of the presheaf of `R`-modules underlying a presheaf of
`R`-algebras `F`. Its degree `m` term is the product over `a : Fin (m + 1) → ι` of the algebras
`F(U (a 0) × ⋯ × U (a m))`. -/
abbrev cechAlgebraComplex : CochainComplex (ModuleCat.{w} R) ℕ :=
  (cechComplexFunctor U).obj (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))

/-- The factor indexed by `a` of a Čech `m`-cochain, an element of `F(U (a 0) × ⋯ × U (a m))`. -/
def cechComponent {m : ℕ} (a : Fin (m + 1) → ι) :
    (cechAlgebraComplex U F).X m →ₗ[R] F.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  (cechComplexπ U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) m a).hom

/-- A Čech cochain is determined by its factors. -/
theorem cechCochain_ext {m : ℕ} {c c' : (cechAlgebraComplex U F).X m}
    (h : ∀ a, cechComponent a c = cechComponent a c') : c = c' :=
  cechComplex_ext h

/-- The Čech cochain with prescribed factors. -/
def cechOfComponents {m : ℕ}
    (f : ∀ a : Fin (m + 1) → ι, F.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    (cechAlgebraComplex U F).X m :=
  cechCochainMk U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) m f

/-- The factors of the cochain with prescribed factors are the prescribed ones. -/
@[simp]
theorem cechComponent_cechOfComponents {m : ℕ}
    (f : ∀ a : Fin (m + 1) → ι, F.obj (op (∏ᶜ fun j ↦ U (a j)))) (a : Fin (m + 1) → ι) :
    cechComponent a (cechOfComponents f) = f a :=
  cechComplexπ_cechCochainMk U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) m f a

/-- The restriction of a Čech `m`-cochain `c` along a map `σ : Fin (m + 1) → Fin (n + 1)` of
vertices, at `k : Fin (n + 1) → ι`: the factor of `c` indexed by `k ∘ σ`, restricted along the
projection `U (k 0) × ⋯ × U (k n) ⟶ U (k (σ 0)) × ⋯ × U (k (σ m))`. For the coface maps
`σ = j.succAbove` these are the terms of the Čech differential (`cechFace_d`), and the cup product
multiplies the restrictions along the front and back faces (`cechComponent_cechCup`). -/
def cechFace {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1)) :
    (cechAlgebraComplex U F).X m →ₗ[R] F.obj (op (∏ᶜ fun j ↦ U (k j))) :=
  (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)).op).hom.toLinearMap ∘ₗ
    cechComponent (k ∘ σ)

/-- The restriction along `σ` is the restriction of the factor indexed by `k ∘ σ`. -/
theorem cechFace_apply {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1))
    (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ c =
      (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)).op).hom (cechComponent (k ∘ σ) c) :=
  (rfl)

/-- Restricting along the identity of the vertices is taking the factor. -/
@[simp]
theorem cechFace_id {m : ℕ} (k : Fin (m + 1) → ι) (c : (cechAlgebraComplex U F).X m) :
    cechFace k id c = cechComponent k c := by
  simp [cechFace_apply]

/-- Restrictions along composable maps of vertices compose. -/
theorem map_cechFace {l m n : ℕ} (k : Fin (n + 1) → ι) (τ : Fin (m + 1) → Fin (n + 1))
    (σ : Fin (l + 1) → Fin (m + 1)) (c : (cechAlgebraComplex U F).X l) :
    (F.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (τ x)).op).hom (cechFace (k ∘ τ) σ c) =
      cechFace k (τ ∘ σ) c := by
  have : (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (τ x)) ≫
      (Pi.lift fun x ↦ Pi.π (fun j ↦ U ((k ∘ τ) j)) (σ x)) =
      Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) ((τ ∘ σ) x) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechFace_apply, ← AlgCat.comp_apply, ← F.map_comp, ← op_comp]
  exact congrArg (fun g ↦ (F.map g.op).hom (cechComponent (k ∘ τ ∘ σ) c)) this

/-- Reading a factor formula of a map of Čech complexes on cochains: if the factor indexed by `k` of
a map `f` is the combination `∑ i ∈ s, z i • (π_(k ∘ σ i) ≫ F(σ i))` of projections followed by
restrictions along maps `σ i` of vertices, then the factor indexed by `k` of `f c` is the same
combination `∑ i ∈ s, z i • cechFace k (σ i) c` of restrictions of `c`. This turns the factor
formulas of maps of Čech complexes, proved in a general preadditive category, into formulas for
algebra-valued cochains. -/
theorem cechComponent_eq_sum_of_comp_π_eq {κ : Type*} {m n : ℕ}
    {f : (cechAlgebraComplex U F).X m ⟶ (cechAlgebraComplex U F).X n} {k : Fin (n + 1) → ι}
    {s : Finset κ} {z : κ → ℤ} {σ : κ → Fin (m + 1) → Fin (n + 1)}
    (h : f ≫ Pi.π _ k = ∑ i ∈ s, z i • (Pi.π _ (k ∘ σ i) ≫
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map
        (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ i x)).op))
    (c : (cechAlgebraComplex U F).X m) :
    cechComponent k (f.hom c) = ∑ i ∈ s, z i • cechFace k (σ i) c := by
  have h := congrArg (fun g ↦ g.hom c) h
  erw [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.sum_apply] at h
  simp only [cechComponent, cechFace_apply, cechComplexπ_eq]
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp]
  simp only [Functor.comp_map, AlgCat.forget₂_module_map]
  rfl

/-- The factors of the Čech differential: the factor of `d c` indexed by `k : Fin (n + 2) → ι` is
the alternating sum of the restrictions of `c` along the coface maps `m.succAbove`. -/
theorem cechComponent_d {n : ℕ} (k : Fin (n + 2) → ι) (c : (cechAlgebraComplex U F).X n) :
    cechComponent k (((cechAlgebraComplex U F).d n (n + 1)).hom c) =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • cechFace k m.succAbove c :=
  cechComponent_eq_sum_of_comp_π_eq
    (cechComplexFunctor_obj_d_comp_π U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) n k) c

/-- The restrictions of the Čech differential of a cochain are alternating sums of restrictions of
the cochain. -/
theorem cechFace_d {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 2) → Fin (n + 1))
    (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ (((cechAlgebraComplex U F).d m (m + 1)).hom c) =
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • cechFace k (σ ∘ j.succAbove) c := by
  rw [cechFace_apply, cechComponent_d, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_cechFace]

end Components

section Maps

/-- The factors of the map of Čech complexes `Č(V, F) ⟶ Č(U, F)` induced by a morphism of families
`φ : U ⟶ V`: the factor indexed by `k` is the factor indexed by `φ.f ∘ k`, restricted along the
product of the morphisms `φ.φ (k j)`. -/
@[simp]
theorem cechComponent_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {m : ℕ} (k : Fin (m + 1) → ι)
    (c : (cechAlgebraComplex V F).X m) :
    cechComponent k
        (((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f m).hom c) =
      (F.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op).hom (cechComponent (φ.f ∘ k) c) := by
  simpa only [cechComponent, Functor.comp_map, AlgCat.forget₂_module_map, ModuleCat.hom_ofHom,
      AlgHom.toLinearMap_apply] using
    cechComplexπ_cechComplexMap φ (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) m c k

/-- The restrictions of the map of Čech complexes induced by a morphism of families `φ : U ⟶ V`
are the restrictions along the product of the morphisms `φ.φ (k j)`. -/
@[simp]
theorem cechFace_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {m l : ℕ} (k : Fin (l + 1) → ι)
    (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex V F).X m) :
    cechFace k σ
        (((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f m).hom c) =
      (F.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op).hom (cechFace (φ.f ∘ k) σ c) := by
  have : (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)) ≫
      Limits.Pi.map (fun j ↦ φ.φ ((k ∘ σ) j)) =
      Limits.Pi.map (fun j ↦ φ.φ (k j)) ≫
        Pi.lift fun x ↦ Pi.π (fun j ↦ V ((φ.f ∘ k) j)) (σ x) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechComponent_cechComplexMap, cechFace_apply, ← AlgCat.comp_apply,
    ← AlgCat.comp_apply, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, this]
  -- the products `∏ᶜ fun j ↦ U ((k ∘ σ) j)` and `∏ᶜ fun x ↦ U (k (σ x))` are the same object
  rfl

/-- The factors of the map of Čech complexes induced by a morphism of presheaves of algebras
`α : F ⟶ G` are the images of the factors under the components of `α`. -/
@[simp]
theorem cechComponent_cechComplexFunctor_map {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) {m : ℕ}
    (k : Fin (m + 1) → ι) (c : (cechAlgebraComplex U F).X m) :
    cechComponent k ((((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f m).hom c) =
      (α.app (op (∏ᶜ fun j ↦ U (k j)))).hom (cechComponent k c) := by
  simpa only [cechComponent, Functor.whiskerRight_app, AlgCat.forget₂_module_map,
      ModuleCat.hom_ofHom, AlgHom.toLinearMap_apply] using
    cechComplexπ_cechComplexFunctor_map U
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) m c k

/-- The restrictions of the map of Čech complexes induced by a morphism of presheaves of algebras
`α : F ⟶ G` are the images of the restrictions under the components of `α`. -/
@[simp]
theorem cechFace_cechComplexFunctor_map {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) {m l : ℕ}
    (k : Fin (l + 1) → ι) (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ ((((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f m).hom c) =
      (α.app (op (∏ᶜ fun j ↦ U (k j)))).hom (cechFace k σ c) := by
  rw [cechFace_apply, cechComponent_cechComplexFunctor_map, cechFace_apply, ← AlgCat.comp_apply,
    ← AlgCat.comp_apply, α.naturality]
  -- the products `∏ᶜ fun j ↦ U ((k ∘ σ) j)` and `∏ᶜ fun x ↦ U (k (σ x))` are the same object
  rfl

/-- The factors of the augmentation `F(T) → Č⁰(U, F)` for a terminal object `T`: the factor indexed
by `a` of the augmentation of a section `s` over `T` is the restriction of `s`. -/
theorem cechComponent_cechAugmentation_f_zero {T : C} (hT : IsTerminal T) (a : Fin 1 → ι)
    (s : F.obj (op T)) :
    cechComponent a
        (((cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f 0).hom s) =
      (F.map (hT.from (∏ᶜ fun j ↦ U (a j))).op).hom s := by
  have h : ((cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f 0 ≫
      Pi.π (fun d : Fin 1 → ι ↦
        (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op (∏ᶜ fun j ↦ U (d j)))) a).hom s =
      ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map
        (hT.from (∏ᶜ fun j ↦ U (a j))).op).hom s :=
    ConcreteCategory.congr_hom
      (cechAugmentation_f_zero_comp_π U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) a) s
  rw [cechComponent, cechComplexπ_eq]
  exact (ModuleCat.comp_apply
    ((cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f 0)
    (Pi.π (fun d : Fin 1 → ι ↦
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).obj (op (∏ᶜ fun j ↦ U (d j)))) a)
    s).symm.trans <| by
      simpa only [Functor.comp_map, AlgCat.forget₂_module_map, ModuleCat.hom_ofHom,
        AlgHom.toLinearMap_apply] using h

/-- The restrictions of the augmentation `F(T) → Č⁰(U, F)` for a terminal object `T`: every
restriction of the augmentation of a section `s` over `T` is the restriction of `s`. -/
theorem cechFace_cechAugmentation_f_zero {T : C} (hT : IsTerminal T) {n : ℕ}
    (k : Fin (n + 1) → ι) (σ : Fin 1 → Fin (n + 1)) (s : F.obj (op T)) :
    cechFace k σ
        (((cechAugmentation U hT (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f 0).hom s) =
      (F.map (hT.from (∏ᶜ fun j ↦ U (k j))).op).hom s := by
  rw [cechFace_apply, cechComponent_cechAugmentation_f_zero, ← AlgCat.comp_apply, ← F.map_comp,
    ← op_comp, hT.hom_ext (_ ≫ _) (hT.from _)]

end Maps

/-- Restrictions along maps of vertices with the same values agree. -/
lemma cechFace_eq_of_val {m n : ℕ} {k : Fin (n + 1) → ι} {σ σ' : Fin (m + 1) → Fin (n + 1)}
    (c : (cechAlgebraComplex U F).X m) (h : ∀ i, (σ i : ℕ) = σ' i) :
    cechFace k σ c = cechFace k σ' c := by
  rw [show σ = σ' from funext fun i ↦ Fin.ext (h i)]

section Cup

omit [HasFiniteProducts C] in
/-- Multiplication in a presheaf of `R`-algebras `F` commutes with restriction maps. -/
theorem cechAlgebraMul_naturality (F : Cᵒᵖ ⥤ AlgCat.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x y : F.obj X) :
    LinearMap.mul R (F.obj Y) ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map f x)
        ((F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map f y) =
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map f (LinearMap.mul R (F.obj X) x y) :=
  (map_mul (F.map f).hom x y).symm

omit [HasFiniteProducts C] in
/-- The multiplicative identity in a presheaf of `R`-algebras `F` is preserved by restriction
maps. -/
theorem cechAlgebraOne_naturality (F : Cᵒᵖ ⥤ AlgCat.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)).map f (1 : F.obj X) = (1 : F.obj Y) :=
  map_one (F.map f).hom

variable (p q n : ℕ) (h : p + q = n)

/-- The **cup product** of Čech cochains of a presheaf of algebras: for `a` of degree `p` and `b` of
degree `q`, the factor of `a ⌣ b` indexed by `k : Fin (p + q + 1) → ι` is
`a(k 0, …, k p) · b(k p, …, k (p + q))`, the factor of `a` on the front `p`-face and the factor of
`b` on the back `q`-face, both restricted to `U (k 0) × ⋯ × U (k (p + q))`
(`cechComponent_cechCup`). -/
def cechCup : (cechAlgebraComplex U F).X p →ₗ[R] (cechAlgebraComplex U F).X q →ₗ[R]
    (cechAlgebraComplex U F).X n :=
  cechCupCochain U (fun X ↦ LinearMap.mul R (F.obj X)) p q n h

/-- `cechCup` is `cechCupCochain` applied to algebra multiplication. -/
theorem cechCup_eq_cechCupCochain :
    cechCup (U := U) (F := F) p q n h =
      cechCupCochain U (fun X ↦ LinearMap.mul R (F.obj X)) p q n h :=
  (rfl)

variable {p q n}

/-- The factors of a cup product: the factor of `a` on the front face times the factor of `b` on the
back face. -/
@[simp]
theorem cechComponent_cechCup (k : Fin (n + 1) → ι) (a : (cechAlgebraComplex U F).X p)
    (b : (cechAlgebraComplex U F).X q) :
    cechComponent k (cechCup p q n h a b) =
      cechFace k (Fin.castLE (by omega)) a *
        cechFace k (fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b := by
  rw [cechCup_eq_cechCupCochain, cechComponent, cechCupCochain_π]
  simp only [cechComponent, cechFace_apply, Pi.map', Category.comp_id, Functor.comp_map,
    AlgCat.forget₂_module_map, ModuleCat.hom_ofHom, AlgHom.toLinearMap_apply]
  rfl

/-- The restrictions of a cup product are the products of the restrictions along the front and back
faces. -/
@[simp]
theorem cechFace_cechCup {m : ℕ} (k : Fin (m + 1) → ι) (σ : Fin (n + 1) → Fin (m + 1))
    (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    cechFace k σ (cechCup p q n h a b) =
      cechFace k (σ ∘ Fin.castLE (by omega)) a *
        cechFace k (σ ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b := by
  rw [cechFace_apply, cechComponent_cechCup, map_mul, map_cechFace, map_cechFace]

/-- The **Leibniz rule** for the Čech cup product:
`d (a ⌣ b) = d a ⌣ b + (-1) ^ p a ⌣ d b` for a cochain `a` of degree `p`. -/
theorem d_cechCup (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a b) =
      cechCup (p + 1) q (n + 1) (by omega) (((cechAlgebraComplex U F).d p (p + 1)).hom a) b +
        (-1 : ℤ) ^ p • cechCup p (q + 1) (n + 1) (by omega) a
          (((cechAlgebraComplex U F).d q (q + 1)).hom b) := by
  simp only [cechCup_eq_cechCupCochain]
  exact d_cechCupCochain U (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (cechAlgebraMul_naturality F) p q n h a b

/-- The cup product of two cocycles is a cocycle. -/
theorem d_cechCup_eq_zero {a : (cechAlgebraComplex U F).X p} {b : (cechAlgebraComplex U F).X q}
    (ha : ((cechAlgebraComplex U F).d p (p + 1)).hom a = 0)
    (hb : ((cechAlgebraComplex U F).d q (q + 1)).hom b = 0) :
    ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a b) = 0 := by
  rw [d_cechCup, ha, hb, map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- A coboundary times a cocycle is a coboundary: `d x ⌣ b = d (x ⌣ b)` when `d b = 0`. -/
theorem cechCup_d_left (x : (cechAlgebraComplex U F).X p) {b : (cechAlgebraComplex U F).X q}
    (hb : ((cechAlgebraComplex U F).d q (q + 1)).hom b = 0) :
    cechCup (p + 1) q (n + 1) (by omega) (((cechAlgebraComplex U F).d p (p + 1)).hom x) b =
      ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h x b) := by
  rw [d_cechCup, hb, map_zero, smul_zero, add_zero]

/-- A cocycle times a coboundary is a coboundary: `a ⌣ d y = (-1) ^ p d (a ⌣ y)` when `d a = 0`
and `a` has degree `p`. -/
theorem cechCup_d_right {a : (cechAlgebraComplex U F).X p} (y : (cechAlgebraComplex U F).X q)
    (ha : ((cechAlgebraComplex U F).d p (p + 1)).hom a = 0) :
    cechCup p (q + 1) (n + 1) (by omega) a (((cechAlgebraComplex U F).d q (q + 1)).hom y) =
      (-1 : ℤ) ^ p • ((cechAlgebraComplex U F).d n (n + 1)).hom (cechCup p q n h a y) := by
  rw [d_cechCup, ha, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

/-- **Associativity** of the Čech cup product, at the level of cochains. -/
theorem cechCup_assoc {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n) (h₃ : q + r = l)
    (h₄ : p + l = n) (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q)
    (c : (cechAlgebraComplex U F).X r) :
    cechCup m r n h₂ (cechCup p q m h₁ a b) c = cechCup p l n h₄ a (cechCup q r l h₃ b c) := by
  simp only [cechCup_eq_cechCupCochain]
  exact cechCupCochain_assoc U
    (P₁ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P₂ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P₃ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P₁₂ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P₂₃ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P₁₂₃ := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ LinearMap.mul R (F.obj X))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ LinearMap.mul R (F.obj X))
    (cechAlgebraMul_naturality F) (cechAlgebraMul_naturality F)
    (fun _ (x y z : F.obj _) ↦ mul_assoc x y z) p q r m l n h₁ h₃ h₂ a b c

variable (U F) in
/-- The **unit cochain**: the Čech `0`-cochain all of whose factors are `1`. -/
def cechOne : (cechAlgebraComplex U F).X 0 :=
  cechUnitCochain U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) fun X ↦ (1 : F.obj X)

/-- `cechOne` is `cechUnitCochain` for the unit sections `1 : F.obj X`. -/
theorem cechOne_eq_cechUnitCochain :
    cechOne U F =
      cechUnitCochain U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) fun X ↦ (1 : F.obj X) :=
  (rfl)

/-- Every factor of the unit cochain is `1`. -/
@[simp]
theorem cechComponent_cechOne (a : Fin 1 → ι) : cechComponent a (cechOne U F) = 1 := by
  rw [cechOne_eq_cechUnitCochain]
  exact cechUnitCochain_π U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ (1 : F.obj X)) a

/-- Every restriction of the unit cochain is `1`. -/
@[simp]
theorem cechFace_cechOne {m : ℕ} (k : Fin (m + 1) → ι) (σ : Fin 1 → Fin (m + 1)) :
    cechFace k σ (cechOne U F) = 1 := by
  rw [cechFace_apply, cechComponent_cechOne, map_one]

/-- The unit cochain is a cocycle. -/
@[simp]
theorem d_cechOne : ((cechAlgebraComplex U F).d 0 1).hom (cechOne U F) = 0 := by
  rw [cechOne_eq_cechUnitCochain]
  exact d_cechUnitCochain U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ (1 : F.obj X)) (cechAlgebraOne_naturality F)

/-- The unit cochain is a left unit for the cup product. -/
@[simp]
theorem cechOne_cechCup (b : (cechAlgebraComplex U F).X q) :
    cechCup 0 q q (zero_add q) (cechOne U F) b = b := by
  rw [cechCup_eq_cechCupCochain, cechOne_eq_cechUnitCochain]
  exact cechCupCochain_unit_left U
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ (1 : F.obj X))
    (cechAlgebraOne_naturality F) (fun _ (y : F.obj _) ↦ one_mul y) q b

/-- The unit cochain is a right unit for the cup product. -/
@[simp]
theorem cechCup_cechOne (a : (cechAlgebraComplex U F).X p) :
    cechCup p 0 p (add_zero p) a (cechOne U F) = a := by
  rw [cechCup_eq_cechCupCochain, cechOne_eq_cechUnitCochain]
  exact cechCupCochain_unit_right U
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ (1 : F.obj X))
    (cechAlgebraOne_naturality F) (fun _ (x : F.obj _) ↦ mul_one x) p a

section Naturality

/-- **Naturality under refinement.** The map of Čech complexes `Č(V, F) ⟶ Č(U, F)` induced by a
morphism of families `φ : U ⟶ V`, such as a refinement of open covers, preserves cup products. -/
theorem cechComplexMap_cechCup {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (a : (cechAlgebraComplex V F).X p)
    (b : (cechAlgebraComplex V F).X q) :
    ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f p a)
        ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f q b) := by
  simp only [cechCup_eq_cechCupCochain]
  exact cechComplexMap_cechCupCochain U φ
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (cechAlgebraMul_naturality F) p q n h a b

/-- **Naturality in the coefficients.** A morphism of presheaves of algebras `α : F ⟶ G` induces a
map of Čech complexes preserving cup products. -/
theorem cechComplexFunctor_map_cechCup {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G)
    (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    (((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h (((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f p a)
        (((cechComplexFunctor U).map
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f q b) := by
  simp only [cechCup_eq_cechCupCochain]
  exact cechComplexFunctor_map_cechCupCochain U
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (P' := G ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q' := G ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S' := G ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ LinearMap.mul R (G.obj X))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun X (x y : F.obj X) ↦ map_mul (α.app X).hom x y) p q n h a b

/-- The map of Čech complexes induced by a morphism of families, such as a refinement of open
covers, preserves the unit cochain. -/
@[simp]
theorem cechComplexMap_cechOne {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f 0).hom (cechOne V F) =
      cechOne U F := by
  simp only [cechOne_eq_cechUnitCochain]
  exact cechComplexMap_cechUnitCochain U φ (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ (1 : F.obj X)) (cechAlgebraOne_naturality F)

/-- The map of Čech complexes induced by a morphism of presheaves of algebras preserves the unit
cochain. -/
@[simp]
theorem cechComplexFunctor_map_cechOne {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) :
    (((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f 0).hom (cechOne U F) =
      cechOne U G := by
  simp only [cechOne_eq_cechUnitCochain]
  exact cechComplexFunctor_map_cechUnitCochain U
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun X ↦ (1 : F.obj X)) (fun X ↦ (1 : G.obj X)) fun X ↦ map_one (α.app X).hom

end Naturality

section Comparison

variable {D : Type*} [Category D] [HasFiniteProducts D] (G : C ⥤ D) {Q : Dᵒᵖ ⥤ AlgCat.{w} R}
  (hG : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (piComparison G fun j ↦ U (a j)))

/-- The factors of the comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes along a functor
`G` preserving the products of members: the factor indexed by `k` is the image of the factor of
the same index under `Q` applied to the comparison map
`G(U (k 0) × ⋯ × U (k m)) ⟶ G (U (k 0)) × ⋯ × G (U (k m))`. -/
theorem cechComponent_cechComplexCompIso_hom {m : ℕ} (k : Fin (m + 1) → ι)
    (c : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X m) :
    cechComponent (F := G.op ⋙ Q) k
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f m).hom
          c) =
      (Q.map (piComparison G fun j ↦ U (k j)).op).hom (cechComponent k c) := by
  simp only [cechComponent, cechComplexπ_eq]
  exact congrArg (fun f ↦ f.hom c)
    (cechComplexCompIso_hom_f_π G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG m k)

/-- The restrictions of the comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` are the images of the
restrictions under `Q` applied to the comparison maps of products. -/
theorem cechFace_cechComplexCompIso_hom {m l : ℕ} (k : Fin (l + 1) → ι)
    (σ : Fin (m + 1) → Fin (l + 1)) (c : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X m) :
    cechFace (F := G.op ⋙ Q) k σ
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f m).hom
          c) =
      (Q.map (piComparison G fun j ↦ U (k j)).op).hom (cechFace k σ c) := by
  have : piComparison G (fun j ↦ U (k j)) ≫
      (Pi.lift fun x ↦ Pi.π (fun j ↦ G.obj (U (k j))) (σ x)) =
      G.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (σ x)) ≫
        piComparison G fun j ↦ U ((k ∘ σ) j) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [cechFace_apply, cechComponent_cechComplexCompIso_hom, cechFace_apply, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, ← AlgCat.comp_apply, ← AlgCat.comp_apply, ← Q.map_comp,
    ← Q.map_comp, ← op_comp, ← op_comp, this]

/-- The comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes along a functor `G` preserving
the products of members preserves cup products. -/
theorem cechComplexCompIso_hom_cechCup
    (a : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X p)
    (b : (cechAlgebraComplex (fun i ↦ G.obj (U i)) Q).X q) :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f n).hom
        (cechCup p q n h a b) =
      cechCup (U := U) (F := G.op ⋙ Q) p q n h
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f p).hom
          a)
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f q).hom
          b) := by
  refine cechCochain_ext (U := U) (F := G.op ⋙ Q) fun k ↦ ?_
  rw [cechComponent_cechComplexCompIso_hom, cechComponent_cechCup, cechComponent_cechCup, map_mul,
    cechFace_cechComplexCompIso_hom, cechFace_cechComplexCompIso_hom]

/-- The inverse comparison `Č(U, G.op ⋙ Q) ≅ Č(G ∘ U, Q)` preserves cup products. -/
theorem cechComplexCompIso_inv_cechCup (a : (cechAlgebraComplex U (G.op ⋙ Q)).X p)
    (b : (cechAlgebraComplex U (G.op ⋙ Q)).X q) :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f p).hom
          a)
        (((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f q).hom
          b) := by
  let e := cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG
  have he (m : ℕ) (x) : (e.hom.f m).hom ((e.inv.f m).hom x) = x :=
    (HomologicalComplex.Hom.isoApp e m).inv_hom_id_apply x
  have he' (x) : (e.inv.f n).hom ((e.hom.f n).hom x) = x :=
    (HomologicalComplex.Hom.isoApp e n).hom_inv_id_apply x
  refine (Function.LeftInverse.injective he') ?_
  rw [he, cechComplexCompIso_hom_cechCup, he, he]

/-- The comparison `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)` of Čech complexes preserves the unit cochain. -/
@[simp]
theorem cechComplexCompIso_hom_cechOne :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).hom.f 0).hom
        (cechOne (fun i ↦ G.obj (U i)) Q) =
      cechOne U (G.op ⋙ Q) :=
  cechCochain_ext (U := U) (F := G.op ⋙ Q) fun k ↦ by
    rw [cechComponent_cechComplexCompIso_hom, cechComponent_cechOne, cechComponent_cechOne,
      map_one]

/-- The inverse comparison `Č(U, G.op ⋙ Q) ≅ Č(G ∘ U, Q)` preserves the unit cochain. -/
@[simp]
theorem cechComplexCompIso_inv_cechOne :
    ((cechComplexCompIso G U (Q ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) hG).inv.f 0).hom
        (cechOne U (G.op ⋙ Q)) =
      cechOne (fun i ↦ G.obj (U i)) Q := by
  rw [← cechComplexCompIso_hom_cechOne G hG]
  exact (HomologicalComplex.Hom.isoApp _ 0).hom_inv_id_apply _

end Comparison

end Cup

end Algebra

end TauCeti.CategoryTheory
