/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Reverse
import Mathlib.Tactic.Ring

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
  (`TauCeti.CategoryTheory.cechComplexFunctor_map_cechCupCochain`);
* the **reversal identity** with signed tuple reversal `TauCeti.CategoryTheory.cechReverse`
  (`TauCeti.CategoryTheory.cechReverse_cechCupCochain`).

Specializing to a presheaf of `R`-algebras `F : Cᵒᵖ ⥤ AlgCat R` (`cechAlgebraComplex U F`) with
multiplication `LinearMap.mul R (F.obj X)` yields the cup product `TauCeti.CategoryTheory.cechCup`
and unit cochain `TauCeti.CategoryTheory.cechOne`, together with their factor/face API
(`TauCeti.CategoryTheory.cechComponent`, `TauCeti.CategoryTheory.cechFace`).

No thinness hypothesis on `C` and no ordering on `ι` are needed. The passage to fixed-family Čech
cohomology is in `TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Homology`.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexπ`: projection from `Čⁿ(U, P)` onto the factor indexed by a
  tuple `c : Fin (n + 1) → ι`.
* `TauCeti.CategoryTheory.cechCochainMk`: construct an `n`-cochain in `Č(U, P)` from its tuple
  coordinates.
* `TauCeti.CategoryTheory.cechCupCochain`: the `R`-bilinear cup product on Čech cochains.
* `TauCeti.CategoryTheory.cechUnitCochain`: the `0`-cochain determined by a compatible family of
  sections.
* `TauCeti.CategoryTheory.cechAlgebraComplex`: the Čech complex of a presheaf of `R`-algebras.
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

section Helpers

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- The canonical projection from degree `n` of the Čech complex `Č(U, P)` to the factor indexed
by a tuple `c : Fin (n + 1) → ι`. Using this wrapper keeps the domain syntactically equal to
`((cechComplexFunctor U).obj P).X n` during rewriting. -/
def cechComplexπ {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) (c : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).obj P).X n ⟶ P.obj (op (∏ᶜ fun j ↦ U (c j))) :=
  Pi.π (fun d : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (d j)))) c

/-- `cechComplexπ` is definitionally the product projection `Pi.π`. -/
theorem cechComplexπ_eq {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c =
      Pi.π (fun d : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (d j)))) c :=
  (rfl)

variable {ι : Type w}

/-- Two `n`-cochains in `Č(U, P)` are equal if all their tuple projections agree. -/
theorem cechComplex_ext {U : ι → C} {P : Cᵒᵖ ⥤ ModuleCat.{w} R} {n : ℕ}
    {x y : ((cechComplexFunctor U).obj P).X n}
    (h : ∀ c : Fin (n + 1) → ι, cechComplexπ U P n c x = cechComplexπ U P n c y) : x = y := by
  let Z : (Fin (n + 1) → ι) → ModuleCat.{w} R := fun d ↦ P.obj (op (∏ᶜ fun j ↦ U (d j)))
  apply (ModuleCat.piIsoPi Z).toLinearEquiv.injective
  funext c
  exact (ModuleCat.piIsoPi_hom_ker_subtype_apply Z c x).trans <|
    (h c).trans (ModuleCat.piIsoPi_hom_ker_subtype_apply Z c y).symm

/-- Construct a degree-`n` Čech cochain in `Č(U, P)` from its values on all `(n + 1)`-tuples. -/
def cechCochainMk (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (f : ∀ c : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (c j)))) :
    ((cechComplexFunctor U).obj P).X n :=
  (ModuleCat.piIsoPi (fun c : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j))))).inv f

/-- The tuple projection of `cechCochainMk` recovers the defining coordinate function. -/
@[simp]
theorem cechComplexπ_cechCochainMk (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (f : ∀ c : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (c j)))) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c (cechCochainMk U P n f) = f c :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply _ c f

/-- Index map embedding the front `(p + 1)` vertices into `Fin (n + 1)` when `p ≤ n`. -/
private def frontFace (p n : ℕ) (hp : p ≤ n) : Fin (p + 1) → Fin (n + 1) :=
  fun j ↦ ⟨j.val, by omega⟩

/-- Index map embedding the back `(q + 1)` vertices into `Fin (n + 1)` when `p + q = n`. -/
private def backFace (p q n : ℕ) (h : p + q = n) : Fin (q + 1) → Fin (n + 1) :=
  fun j ↦ ⟨p + j.val, by omega⟩

private lemma frontFace_comp_succAbove_last (p n : ℕ) (hp : p + 1 ≤ n + 1) :
    frontFace (p + 1) (n + 1) hp ∘ (Fin.last (p + 1)).succAbove =
      frontFace p (n + 1) (by omega) := by
  funext x; ext; simp [frontFace, Fin.succAbove_last]

private lemma backFace_comp_succAbove_zero (p q n : ℕ) (h : p + (q + 1) = n + 1) :
    backFace p (q + 1) (n + 1) h ∘ (0 : Fin (q + 2)).succAbove =
      backFace (p + 1) q (n + 1) (by omega) := by
  funext y; ext; simp [backFace]; omega

/-- Projection between finite products of members of `U` induced by a map of finite index sets. -/
private def tupleProj (U : ι → C) {k m : ℕ} (c : Fin (m + 1) → ι) (f : Fin (k + 1) → Fin (m + 1)) :
    (∏ᶜ fun j : Fin (m + 1) ↦ U (c j)) ⟶ (∏ᶜ fun i : Fin (k + 1) ↦ U ((c ∘ f) i)) :=
  Pi.lift fun i ↦ Pi.π (fun j ↦ U (c j)) (f i)

private lemma tupleProj_comp_tupleProj (U : ι → C) {k l m : ℕ} (c : Fin (m + 1) → ι)
    (g : Fin (l + 1) → Fin (m + 1)) (f : Fin (k + 1) → Fin (l + 1)) :
    tupleProj U c g ≫ tupleProj U (c ∘ g) f = tupleProj U c (g ∘ f) :=
  Pi.hom_ext _ _ fun i ↦ by simp [tupleProj]

private lemma tupleProj_id (U : ι → C) {m : ℕ} (c : Fin (m + 1) → ι) :
    tupleProj U c id = 𝟙 (∏ᶜ fun j : Fin (m + 1) ↦ U (c j)) :=
  Pi.hom_ext _ _ fun i ↦ by simp [tupleProj]

omit [HasFiniteProducts C] in
private lemma presheaf_map_map {P : Cᵒᵖ ⥤ ModuleCat.{w} R} {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : P.obj X) : P.map g (P.map f x) = P.map (f ≫ g) x := by
  rw [P.map_comp, ModuleCat.comp_apply]

omit [HasFiniteProducts C] in
private lemma natTrans_app_map {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (α : P ⟶ Q) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : P.obj X) : α.app Y (P.map f x) = Q.map f (α.app X x) := by
  rw [← ModuleCat.comp_apply, α.naturality, ModuleCat.comp_apply]

/-- Elementwise differential formula for a Čech complex of modules. -/
private lemma cechComplexπ_d (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 2) → ι) :
    cechComplexπ U P (n + 1) c (((cechComplexFunctor U).obj P).d n (n + 1) a) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        P.map (tupleProj U c k.succAbove).op (cechComplexπ U P n (c ∘ k.succAbove) a) := by
  have h : (((cechComplexFunctor U).obj P).d n (n + 1) ≫ cechComplexπ U P (n + 1) c) a =
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (cechComplexπ U P n (c ∘ k.succAbove) ≫ P.map (tupleProj U c k.succAbove).op)) a :=
    ConcreteCategory.congr_hom (cechComplexFunctor_obj_d_comp_π U P n c) a
  exact (ModuleCat.comp_apply _ _ a).symm.trans <| h.trans <| by simp [ModuleCat.hom_sum]

private lemma cechComplexπ_cechReverse (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c (((cechReverse U).app P).f n a) =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        P.map (tupleProj U c Fin.rev).op (cechComplexπ U P n (c ∘ Fin.rev) a) := by
  have h : (((cechReverse U).app P).f n ≫ cechComplexπ U P n c) a =
      ((-1 : ℤ) ^ (n * (n + 1) / 2) •
        (cechComplexπ U P n (c ∘ Fin.rev) ≫ P.map (tupleProj U c Fin.rev).op)) a :=
    ConcreteCategory.congr_hom (cechReverse_app_f_π U P n c) a
  exact (ModuleCat.comp_apply _ _ a).symm.trans <| h.trans <| by simp

private lemma cechComplexπ_cechComplexMap {κ : Type w} {U : ι → C} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor V).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c ((cechComplexMap P φ).f n a) =
      P.map ((Limits.Pi.map fun j : Fin (n + 1) ↦ φ.φ (c j) :
          (∏ᶜ fun j : Fin (n + 1) ↦ U (c j)) ⟶ ∏ᶜ fun j : Fin (n + 1) ↦ V ((φ.f ∘ c) j))).op
        (cechComplexπ V P n (φ.f ∘ c) a) := by
  have h := ConcreteCategory.congr_hom (cechComplexMap_f_π P φ n c) a
  exact (ModuleCat.comp_apply _ _ a).symm.trans <| h.trans (ModuleCat.comp_apply _ _ a)

private lemma cechComplexπ_cechComplexFunctor_map (U : ι → C) {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (α : P ⟶ Q) (n : ℕ) (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U Q n c (((cechComplexFunctor U).map α).f n a) =
      α.app (op (∏ᶜ fun j ↦ U (c j))) (cechComplexπ U P n c a) := by
  have h := ConcreteCategory.congr_hom (cechComplexFunctor_map_f_π U P α n c) a
  exact (ModuleCat.comp_apply _ _ a).symm.trans <| h.trans (ModuleCat.comp_apply _ _ a)

private lemma cechComplexπ_cechAugmentation (U : ι → C) {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e₀ : P.obj (op T)) (a : Fin 1 → ι) :
    cechComplexπ U P 0 a
        ((cechAugmentation U hT P).f 0
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀)) =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op e₀ := by
  have h : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv ≫
        (cechAugmentation U hT P).f 0 ≫ cechComplexπ U P 0 a) e₀ =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op e₀ :=
    ConcreteCategory.congr_hom (cechAugmentation_f_zero_comp_π U hT P a) e₀
  simpa only [ModuleCat.comp_apply] using h

end Helpers

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
        (P.map (tupleProj U c (frontFace p n (by omega))).op
          (cechComplexπ U P p (c ∘ frontFace p n (by omega)) a))
        (Q.map (tupleProj U c (backFace p q n h)).op
          (cechComplexπ U Q q (c ∘ backFace p q n h) b)))
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)
    (fun _ _ _ ↦ cechComplex_ext fun c ↦ by simp)

private lemma cechCupCochain_π_faces (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 1) → ι) :
    cechComplexπ U S n c (cechCupCochain U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (c j)))
        (P.map (tupleProj U c (frontFace p n (by omega))).op
          (cechComplexπ U P p (c ∘ frontFace p n (by omega)) a))
        (Q.map (tupleProj U c (backFace p q n h)).op
          (cechComplexπ U Q q (c ∘ backFace p q n h) b)) :=
  cechComplexπ_cechCochainMk U S n _ c

/-- The coordinate formula for `cechCupCochain` at a tuple `c : Fin (n + 1) → ι`. -/
@[simp]
theorem cechCupCochain_π (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : Fin (n + 1) → ι) :
    cechComplexπ U S n c (cechCupCochain U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (c j)))
        (P.map (Pi.lift fun j : Fin (p + 1) ↦
            Pi.π (fun i ↦ U (c i)) ⟨j.val, by omega⟩).op
          (cechComplexπ U P p (fun j ↦ c ⟨j.val, by omega⟩) a))
        (Q.map (Pi.lift fun j : Fin (q + 1) ↦
            Pi.π (fun i ↦ U (c i)) ⟨p + j.val, by omega⟩).op
          (cechComplexπ U Q q (fun j ↦ c ⟨p + j.val, by omega⟩) b)) :=
  cechCupCochain_π_faces U μ p q n h a b c

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
  let term (f : Fin (p + 1) → Fin (n + 2)) (g : Fin (q + 1) → Fin (n + 2)) :
      S.obj (op (∏ᶜ fun j : Fin (n + 2) ↦ U (c j))) :=
    μ (op (∏ᶜ fun j ↦ U (c j)))
      (P.map (tupleProj U c f).op (cechComplexπ U P p (c ∘ f) a))
      (Q.map (tupleProj U c g).op (cechComplexπ U Q q (c ∘ g) b))
  have hLHS : cechComplexπ U S (n + 1) c
        (((cechComplexFunctor U).obj S).d n (n + 1) (cechCupCochain U μ p q n h a b)) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        term (k.succAbove ∘ frontFace p n (by omega)) (k.succAbove ∘ backFace p q n h) := by
    rw [cechComplexπ_d]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg _ ?_
    rw [cechCupCochain_π_faces, ← hμ, presheaf_map_map, ← op_comp, presheaf_map_map, ← op_comp,
      tupleProj_comp_tupleProj, tupleProj_comp_tupleProj]; rfl
  have hRHS₁ : cechComplexπ U S (n + 1) c (cechCupCochain U μ (p + 1) q (n + 1) (by omega)
        (((cechComplexFunctor U).obj P).d p (p + 1) a) b) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        term (frontFace (p + 1) (n + 1) (by omega) ∘ i.succAbove)
          (backFace (p + 1) q (n + 1) (by omega)) := by
    rw [cechCupCochain_π_faces, cechComplexπ_d, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, map_zsmul, LinearMap.smul_apply, presheaf_map_map, ← op_comp,
      tupleProj_comp_tupleProj]; rfl
  have hRHS₂ : cechComplexπ U S (n + 1) c ((-1 : ℤ) ^ p •
        cechCupCochain U μ p (q + 1) (n + 1) (by omega) a
          (((cechComplexFunctor U).obj Q).d q (q + 1) b)) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (p + (j : ℕ)) •
        term (frontFace p (n + 1) (by omega))
          (backFace p (q + 1) (n + 1) (by omega) ∘ j.succAbove) := by
    rw [map_zsmul, cechCupCochain_π_faces, cechComplexπ_d, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, map_zsmul, smul_smul, ← pow_add, presheaf_map_map, ← op_comp,
      tupleProj_comp_tupleProj]; rfl
  rw [map_add, hLHS, hRHS₁, hRHS₂, Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1), add_assoc (∑ i : Fin (p + 1), _),
    ← add_assoc ((-1 : ℤ) ^ (Fin.last (p + 1) : ℕ) • _)]
  rw [frontFace_comp_succAbove_last, backFace_comp_succAbove_zero, Fin.val_last, Fin.val_zero,
    add_zero, pow_succ, mul_neg_one, neg_smul, neg_add_cancel, zero_add]
  let e := finCongr (by omega : (p + 1) + (q + 1) = n + 2)
  rw [← Fintype.sum_equiv e (fun k ↦ (-1 : ℤ) ^ ((e k : Fin (n + 2)) : ℕ) •
      term ((e k).succAbove ∘ frontFace p n (by omega)) ((e k).succAbove ∘ backFace p q n h))
    _ (fun _ ↦ rfl), Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun j _ ↦ ?_)
  · refine congrArg₂ (· • ·) (by simp [e]) (congrArg₂ term ?_ ?_)
    · funext x; ext
      simp only [e, Function.comp_apply, frontFace, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
        finCongr_apply, Fin.val_cast, Fin.val_castAdd]; split_ifs <;> simp
    · funext y; ext
      simp only [e, Function.comp_apply, backFace, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
        finCongr_apply, Fin.val_cast, Fin.val_castAdd]; split_ifs <;> simp <;> omega
  · refine congrArg₂ (· • ·) (by congr 1; simp [e]; omega) (congrArg₂ term ?_ ?_)
    · funext x; ext
      simp only [e, Function.comp_apply, frontFace, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
        finCongr_apply, Fin.val_cast, Fin.val_natAdd]; split_ifs <;> simp; omega
    · funext y; ext
      simp only [e, Function.comp_apply, backFace, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
        Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]; split_ifs <;> simp <;> omega

private lemma map_tupleProj_comp_congr (P : Cᵒᵖ ⥤ ModuleCat.{w} R) {k l m : ℕ}
    (c : Fin (m + 1) → ι) (g : Fin (l + 1) → Fin (m + 1)) (f : Fin (k + 1) → Fin (l + 1))
    {h : Fin (k + 1) → Fin (m + 1)} (hfg : g ∘ f = h) (a : ((cechComplexFunctor U).obj P).X k) :
    P.map (tupleProj U c (g ∘ f)).op (cechComplexπ U P k ((c ∘ g) ∘ f) a) =
      P.map (tupleProj U c h).op (cechComplexπ U P k (c ∘ h) a) := by
  subst hfg; rfl

private lemma map_tupleProj_comp3_congr (P : Cᵒᵖ ⥤ ModuleCat.{w} R) {k l m n : ℕ}
    (c : Fin (n + 1) → ι) (f₁ : Fin (m + 1) → Fin (n + 1)) (f₂ : Fin (l + 1) → Fin (m + 1))
    (f₃ : Fin (k + 1) → Fin (l + 1)) {h : Fin (k + 1) → Fin (n + 1)}
    (hcomp : (f₁ ∘ f₂) ∘ f₃ = h) (a : ((cechComplexFunctor U).obj P).X k) :
    P.map (tupleProj U c (f₁ ∘ f₂) ≫ tupleProj U ((c ∘ f₁) ∘ f₂) f₃).op
        (cechComplexπ U P k (((c ∘ f₁) ∘ f₂) ∘ f₃) a) =
      P.map (tupleProj U c h).op (cechComplexπ U P k (c ∘ h) a) := by
  rw [show tupleProj U c (f₁ ∘ f₂) ≫ tupleProj U ((c ∘ f₁) ∘ f₂) f₃ =
      tupleProj U c ((f₁ ∘ f₂) ∘ f₃) from tupleProj_comp_tupleProj U c (f₁ ∘ f₂) f₃]
  subst hcomp; rfl

private lemma map_tupleProj_id (P : Cᵒᵖ ⥤ ModuleCat.{w} R) {m : ℕ} (c : Fin (m + 1) → ι)
    {f : Fin (m + 1) → Fin (m + 1)} (hf : f = id) (a : ((cechComplexFunctor U).obj P).X m) :
    P.map (tupleProj U c f).op (cechComplexπ U P m (c ∘ f) a) = cechComplexπ U P m c a := by
  subst hf; simp [tupleProj_id]

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
  rw [cechCupCochain_π_faces, cechCupCochain_π_faces, cechCupCochain_π_faces,
    cechCupCochain_π_faces, ← hμ₁₂, ← hμ₂₃, presheaf_map_map, presheaf_map_map, presheaf_map_map,
    presheaf_map_map, ← op_comp, ← op_comp, ← op_comp, ← op_comp, tupleProj_comp_tupleProj,
    tupleProj_comp_tupleProj, tupleProj_comp_tupleProj, tupleProj_comp_tupleProj, hassoc,
    map_tupleProj_comp_congr U P₁ d _ _ (show frontFace pq n (by omega) ∘ frontFace p pq (by omega)
      = frontFace p n (by omega) by funext j; ext; rfl),
    map_tupleProj_comp_congr U P₂ d _ _ rfl,
    map_tupleProj_comp_congr U P₂ d _ _ (show backFace p qr n (by omega) ∘ frontFace q qr (by omega)
      = frontFace pq n (by omega) ∘ backFace p q pq hpq by
        funext j; ext; simp [frontFace, backFace]),
    map_tupleProj_comp_congr U P₃ d _ _ (show backFace p qr n (by omega) ∘ backFace q r qr hqr =
      backFace pq r n hn by funext j; ext; simp [backFace]; omega)]

/-- **Reversal identity for the Čech cup product.** Reversing a cup product of reversed cochains
recovers the cup product in the opposite order with the Koszul sign `(-1) ^ (p * q)`. -/
theorem cechReverse_cechCupCochain
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, Q.obj X →ₗ[R] P.obj X →ₗ[R] S.obj X)
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y x, μ' Y (Q.map f y) (P.map f x) = S.map f (μ' X y x))
    (hcomm : ∀ X x y, μ' X y x = μ X x y)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechReverse U).app S).f n
        (cechCupCochain U μ' q p n (by omega)
          (((cechReverse U).app Q).f q b) (((cechReverse U).app P).f p a)) =
      (-1 : ℤ) ^ (p * q) • cechCupCochain U μ p q n h a b := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechComplexπ_cechReverse, map_zsmul, cechCupCochain_π_faces, cechCupCochain_π_faces, ← hμ',
    cechComplexπ_cechReverse, cechComplexπ_cechReverse, map_zsmul, map_zsmul, map_zsmul,
    LinearMap.smul_apply, map_zsmul, map_zsmul, map_zsmul, smul_smul, smul_smul, ← pow_add,
    ← pow_add, presheaf_map_map, presheaf_map_map, presheaf_map_map, presheaf_map_map, ← op_comp,
    ← op_comp, ← op_comp, ← op_comp, tupleProj_comp_tupleProj, tupleProj_comp_tupleProj, hcomm]
  have hsign : (-1 : ℤ) ^ (n * (n + 1) / 2 + q * (q + 1) / 2 + p * (p + 1) / 2) =
      (-1 : ℤ) ^ (p * q) := by
    have hp2 : 2 ∣ p * (p + 1) := (Nat.even_mul_succ_self p).two_dvd
    have hq2 : 2 ∣ q * (q + 1) := (Nat.even_mul_succ_self q).two_dvd
    have hmul : n * (n + 1) = p * (p + 1) + q * (q + 1) + 2 * (p * q) := by rw [← h]; ring
    rw [show n * (n + 1) / 2 + q * (q + 1) / 2 + p * (p + 1) / 2 =
        p * q + 2 * (p * (p + 1) / 2 + q * (q + 1) / 2) by omega,
      pow_add, pow_mul (-1 : ℤ) 2 _, neg_one_sq, one_pow, mul_one]
  rw [hsign,
    map_tupleProj_comp3_congr U P c _ _ _ (show ((Fin.rev : Fin (n + 1) → Fin (n + 1)) ∘
      backFace q p n (by omega)) ∘ Fin.rev = frontFace p n (by omega) by
        funext i; ext; simp only [Function.comp_apply, Fin.val_rev, backFace, frontFace]; omega),
    map_tupleProj_comp3_congr U Q c _ _ _ (show ((Fin.rev : Fin (n + 1) → Fin (n + 1)) ∘
      frontFace q n (by omega)) ∘ Fin.rev = backFace p q n h by
        funext j; ext; simp only [Function.comp_apply, Fin.val_rev, frontFace, backFace]; omega)]

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
  rw [cechComplexπ_cechComplexMap, cechCupCochain_π_faces, cechCupCochain_π_faces, ← hμ,
    cechComplexπ_cechComplexMap, cechComplexπ_cechComplexMap, presheaf_map_map, presheaf_map_map,
    presheaf_map_map, presheaf_map_map, ← op_comp, ← op_comp, ← op_comp, ← op_comp]
  have hcomm (k : ℕ) (f : Fin (k + 1) → Fin (n + 1)) :
      tupleProj U c f ≫ (Limits.Pi.map (fun j : Fin (k + 1) ↦ φ.φ ((c ∘ f) j)) :
          (∏ᶜ fun j ↦ U ((c ∘ f) j)) ⟶ ∏ᶜ fun j ↦ V ((φ.f ∘ c ∘ f) j)) =
        (Limits.Pi.map (fun i : Fin (n + 1) ↦ φ.φ (c i)) :
          (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun i ↦ V ((φ.f ∘ c) i)) ≫ tupleProj V (φ.f ∘ c) f :=
    Pi.hom_ext _ _ fun i ↦ by simp [tupleProj]
  rw [hcomm p (frontFace p n (by omega)), hcomm q (backFace p q n h)]; rfl

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
  rw [cechComplexπ_cechComplexFunctor_map, cechCupCochain_π_faces, cechCupCochain_π_faces, hγ,
    cechComplexπ_cechComplexFunctor_map, cechComplexπ_cechComplexFunctor_map, natTrans_app_map,
    natTrans_app_map]

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
  rw [cechCupCochain_π_faces, cechUnitCochain_π, he, hl]
  exact map_tupleProj_id U Q c (by funext j; ext; simp [backFace]) b

/-- Right unit law for `cechCupCochain`. -/
theorem cechCupCochain_unit_right (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] P.obj X)
    (e : ∀ X : Cᵒᵖ, Q.obj X) (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), Q.map f (e X) = e Y)
    (hr : ∀ X x, μ X x (e X) = x) (p : ℕ) (a : ((cechComplexFunctor U).obj P).X p) :
    cechCupCochain U μ p 0 p (add_zero p) a (cechUnitCochain U Q e) = a := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechCupCochain_π_faces, cechUnitCochain_π, he, hr]
  exact map_tupleProj_id U P c (by funext j; ext; simp [frontFace]) a

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

/-- The factors of the Čech differential: the factor of `d c` indexed by `k : Fin (n + 2) → ι` is
the alternating sum of the restrictions of `c` along the coface maps `m.succAbove`. -/
theorem cechComponent_d {n : ℕ} (k : Fin (n + 2) → ι) (c : (cechAlgebraComplex U F).X n) :
    cechComponent k (((cechAlgebraComplex U F).d n (n + 1)).hom c) =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • cechFace k m.succAbove c :=
  cechComplexπ_d U (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) n c k

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
      (F.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op).hom (cechComponent (φ.f ∘ k) c) :=
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
  rfl

/-- The factors of the map of Čech complexes induced by a morphism of presheaves of algebras
`α : F ⟶ G` are the images of the factors under the components of `α`. -/
@[simp]
theorem cechComponent_cechComplexFunctor_map {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) {m : ℕ}
    (k : Fin (m + 1) → ι) (c : (cechAlgebraComplex U F).X m) :
    cechComponent k ((((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f m).hom c) =
      (α.app (op (∏ᶜ fun j ↦ U (k j)))).hom (cechComponent k c) :=
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
  rfl

end Maps

section Cup

private abbrev algMod (F : Cᵒᵖ ⥤ AlgCat.{w} R) : Cᵒᵖ ⥤ ModuleCat.{w} R :=
  F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)

private def algMul (F : Cᵒᵖ ⥤ AlgCat.{w} R) (X : Cᵒᵖ) :
    (algMod F).obj X →ₗ[R] (algMod F).obj X →ₗ[R] (algMod F).obj X :=
  LinearMap.mul R (F.obj X)

omit [HasFiniteProducts C] in
private lemma algCat_mul_naturality (F : Cᵒᵖ ⥤ AlgCat.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x y : (algMod F).obj X) :
    algMul F Y ((algMod F).map f x) ((algMod F).map f y) =
      (algMod F).map f (algMul F X x y) := by
  let x' : F.obj X := x
  let y' : F.obj X := y
  exact (map_mul (F.map f).hom x' y').symm

variable (p q n : ℕ) (h : p + q = n)

/-- The **cup product** of Čech cochains of a presheaf of algebras: for `a` of degree `p` and `b` of
degree `q`, the factor of `a ⌣ b` indexed by `k : Fin (p + q + 1) → ι` is
`a(k 0, …, k p) · b(k p, …, k (p + q))`, the factor of `a` on the front `p`-face and the factor of
`b` on the back `q`-face, both restricted to `U (k 0) × ⋯ × U (k (p + q))`
(`cechComponent_cechCup`). -/
def cechCup : (cechAlgebraComplex U F).X p →ₗ[R] (cechAlgebraComplex U F).X q →ₗ[R]
    (cechAlgebraComplex U F).X n :=
  cechCupCochain U (algMul F) p q n h

variable {p q n}

/-- The factors of a cup product: the factor of `a` on the front face times the factor of `b` on the
back face. -/
@[simp]
theorem cechComponent_cechCup (k : Fin (n + 1) → ι) (a : (cechAlgebraComplex U F).X p)
    (b : (cechAlgebraComplex U F).X q) :
    cechComponent k (cechCup p q n h a b) =
      cechFace k (Fin.castLE (by omega)) a *
        cechFace k (fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) b := by
  exact cechCupCochain_π U (algMul F) p q n h a b k

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
          (((cechAlgebraComplex U F).d q (q + 1)).hom b) :=
  d_cechCupCochain U (algMul F) (algCat_mul_naturality F) p q n h a b

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
    cechCup m r n h₂ (cechCup p q m h₁ a b) c = cechCup p l n h₄ a (cechCup q r l h₃ b c) :=
  cechCupCochain_assoc U (algMul F) (algMul F) (algMul F) (algMul F)
    (algCat_mul_naturality F) (algCat_mul_naturality F)
    (fun _ (x y z : F.obj _) ↦ mul_assoc x y z) p q r m l n h₁ h₃ h₂ a b c

/-- **Reversal identity** for `cechCup` when multiplication in `F` is commutative. -/
theorem cechReverse_cechCup (hcomm : ∀ X (x y : F.obj X), x * y = y * x)
    (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    ((cechReverse U).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f n
        (cechCup q p n (by omega)
          (((cechReverse U).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f q b)
          (((cechReverse U).app (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f p a)) =
      (-1 : ℤ) ^ (p * q) • cechCup p q n h a b :=
  cechReverse_cechCupCochain U (algMul F) (algMul F) (algCat_mul_naturality F)
    (fun X (x y : F.obj X) ↦ hcomm X y x) p q n h a b

variable (U F) in
/-- The **unit cochain**: the Čech `0`-cochain all of whose factors are `1`. -/
def cechOne : (cechAlgebraComplex U F).X 0 :=
  cechUnitCochain U (algMod F) fun X ↦ (1 : F.obj X)

/-- Every factor of the unit cochain is `1`. -/
@[simp]
theorem cechComponent_cechOne (a : Fin 1 → ι) : cechComponent a (cechOne U F) = 1 :=
  cechUnitCochain_π U (algMod F) (fun X ↦ (1 : F.obj X)) a

/-- Every restriction of the unit cochain is `1`. -/
@[simp]
theorem cechFace_cechOne {m : ℕ} (k : Fin (m + 1) → ι) (σ : Fin 1 → Fin (m + 1)) :
    cechFace k σ (cechOne U F) = 1 := by
  rw [cechFace_apply, cechComponent_cechOne, map_one]

/-- The unit cochain is a cocycle. -/
@[simp]
theorem d_cechOne : ((cechAlgebraComplex U F).d 0 1).hom (cechOne U F) = 0 :=
  d_cechUnitCochain U (algMod F) (fun X ↦ (1 : F.obj X))
    fun f ↦ map_one (F.map f).hom

/-- The unit cochain is a left unit for the cup product. -/
@[simp]
theorem cechOne_cechCup (b : (cechAlgebraComplex U F).X q) :
    cechCup 0 q q (zero_add q) (cechOne U F) b = b :=
  cechCupCochain_unit_left U (algMul F) (fun X ↦ (1 : F.obj X))
    (fun f ↦ map_one (F.map f).hom) (fun _ (y : F.obj _) ↦ one_mul y) q b

/-- The unit cochain is a right unit for the cup product. -/
@[simp]
theorem cechCup_cechOne (a : (cechAlgebraComplex U F).X p) :
    cechCup p 0 p (add_zero p) a (cechOne U F) = a :=
  cechCupCochain_unit_right U (algMul F) (fun X ↦ (1 : F.obj X))
    (fun f ↦ map_one (F.map f).hom) (fun _ (x : F.obj _) ↦ mul_one x) p a

section Naturality

/-- **Naturality under refinement.** The map of Čech complexes `Č(V, F) ⟶ Č(U, F)` induced by a
morphism of families `φ : U ⟶ V`, such as a refinement of open covers, preserves cup products. -/
theorem cechComplexMap_cechCup {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (a : (cechAlgebraComplex V F).X p)
    (b : (cechAlgebraComplex V F).X q) :
    ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f p a)
        ((cechComplexMap (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) φ).f q b) :=
  cechComplexMap_cechCupCochain U φ (algMul F) (algCat_mul_naturality F) p q n h a b

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
          (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f q b) :=
  cechComplexFunctor_map_cechCupCochain U (algMul F) (algMul G)
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
      cechOne U F :=
  cechComplexMap_cechUnitCochain U φ (algMod F) (fun X ↦ (1 : F.obj X))
    fun f ↦ map_one (F.map f).hom

/-- The map of Čech complexes induced by a morphism of presheaves of algebras preserves the unit
cochain. -/
@[simp]
theorem cechComplexFunctor_map_cechOne {G : Cᵒᵖ ⥤ AlgCat.{w} R} (α : F ⟶ G) :
    (((cechComplexFunctor U).map
      (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))).f 0).hom (cechOne U F) =
      cechOne U G :=
  cechComplexFunctor_map_cechUnitCochain U
    (Functor.whiskerRight α (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)))
    (fun X ↦ (1 : F.obj X)) (fun X ↦ (1 : G.obj X)) fun X ↦ map_one (α.app X).hom

end Naturality

end Cup

end Algebra

end TauCeti.CategoryTheory
