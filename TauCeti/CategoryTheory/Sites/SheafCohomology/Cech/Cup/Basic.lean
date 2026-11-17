/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.OrderReversal

import Mathlib.Tactic.Ring

/-!
# The Čech cup product on cochains and fixed-family cohomology

Let `C` be a category with finite products, let `R` be a commutative ring, and let
`P, Q, S : Cᵒᵖ ⥤ ModuleCat R` be presheaves of `R`-modules equipped with a natural `R`-bilinear
pairing `μ : ∀ V, P(V) →ₗ[R] Q(V) →ₗ[R] S(V)`. For a family `U : ι → C` and degrees `p + q = n`,
the **Čech cup product** of cochains `a ∈ Čᵖ(U, P)` and `b ∈ Č^q(U, Q)` is the `n`-cochain
`cechCupCochain U μ p q n h a b ∈ Čⁿ(U, S)` whose component at a tuple `k : Fin (n + 1) → ι` is
given by restricting `a` to the front `p`-face `(k 0, …, k p)` and `b` to the back `q`-face
`(k p, …, k n)` and pairing them via `μ` (`π_cechCupCochain`).

This file proves the graded Leibniz rule (`d_cechCupCochain`), strict associativity
(`cechCupCochain_assoc`), unitality, compatibility with refinement maps, presheaf morphisms, and
product-preserving functors (`cechComplexCompIso`), and the reversal identity
`τ (τ b ⌣ τ a) = (-1)^(p * q) • (a ⌣ b)` (`cechOrderReversal_cechCupCochain`).

Descending to fixed-cover Čech cohomology yields the bilinear pairing `cechCup`, which is
associative, unital on augmentations, functorial in covers and coefficients, compatible with
`cechAugmentation` in degree `0`, and graded-commutative (`cechCup_gradedComm`) because order
reversal is chain homotopic to the identity (`homologyMap_cechOrderReversal`). Passing to the
colimit over a directed system of families is carried out in
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Colimit`.

## Main definitions

* `TauCeti.CategoryTheory.cechCupCochain`: the front-face / back-face cup product on Čech cochains.
* `TauCeti.CategoryTheory.cechCupCycles`: the cup product of Čech cocycles.
* `TauCeti.CategoryTheory.cechCup`: the cup product on fixed-family Čech cohomology.

## Main results

* `TauCeti.CategoryTheory.π_cechCupCochain`: componentwise front-face / back-face formula.
* `TauCeti.CategoryTheory.d_cechCupCochain`: the graded Leibniz rule for Čech cochains.
* `TauCeti.CategoryTheory.cechCup_assoc`, `TauCeti.CategoryTheory.cechCup_gradedComm`:
  associativity and graded commutativity on fixed-family Čech cohomology.
* `TauCeti.CategoryTheory.cechCup_cechComplexHomologyMap`: compatibility with refinement maps.
* `TauCeti.CategoryTheory.cechCup_zero_zero_augmentation`: degree-`0` compatibility with
  `cechAugmentation`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w uR v v'' u u' u''

namespace TauCeti.CategoryTheory

namespace CechCup

/-! ### Front-face and back-face index maps -/

/-- The front `p`-face inclusion `i ↦ i` from `Fin (p + 1)` to `Fin (n + 1)` for `p + q = n`. -/
private def frontFin {p q n : ℕ} (h : p + q = n) : Fin (p + 1) → Fin (n + 1) :=
  fun i ↦ ⟨i.1, by omega⟩

/-- The back `q`-face inclusion `j ↦ p + j` from `Fin (q + 1)` to `Fin (n + 1)` for `p + q = n`. -/
private def backFin {p q n : ℕ} (h : p + q = n) : Fin (q + 1) → Fin (n + 1) :=
  fun j ↦ ⟨p + j.1, by omega⟩

private lemma frontFin_zero_right {p : ℕ} (h : p + 0 = p) : frontFin h = id :=
  funext fun _ ↦ Fin.ext rfl

private lemma backFin_zero_left {q : ℕ} (h : 0 + q = q) : backFin h = id :=
  funext fun j ↦ Fin.ext (Nat.zero_add j.1)

private lemma frontFin_comp_frontFin {p q r pq n : ℕ} (h₁ : p + q = pq) (h₂ : pq + r = n)
    {qr : ℕ} (h₄ : p + qr = n) :
    frontFin h₂ ∘ frontFin h₁ = frontFin h₄ :=
  funext fun _ ↦ Fin.ext rfl

private lemma frontFin_comp_backFin {p q r pq qr n : ℕ} (h₁ : p + q = pq) (h₂ : pq + r = n)
    (h₃ : q + r = qr) (h₄ : p + qr = n) :
    frontFin h₂ ∘ backFin h₁ = backFin h₄ ∘ frontFin h₃ :=
  funext fun _ ↦ Fin.ext rfl

private lemma backFin_comp_backFin {p q r pq qr n : ℕ} (h₁ : p + q = pq) (h₂ : pq + r = n)
    (h₃ : q + r = qr) (h₄ : p + qr = n) :
    backFin h₄ ∘ backFin h₃ = backFin h₂ :=
  funext fun _ ↦ Fin.ext (by simp [backFin]; omega)

private lemma rev_comp_frontFin_comp_rev {p q n : ℕ} (h : p + q = n) (h' : q + p = n) :
    Fin.rev ∘ frontFin h' ∘ Fin.rev = backFin h :=
  funext fun i ↦ Fin.ext (by simp [frontFin, backFin, Fin.val_rev]; omega)

private lemma rev_comp_backFin_comp_rev {p q n : ℕ} (h : p + q = n) (h' : q + p = n) :
    Fin.rev ∘ backFin h' ∘ Fin.rev = frontFin h :=
  funext fun i ↦ Fin.ext (by simp [frontFin, backFin, Fin.val_rev]; omega)

private lemma succAbove_left_comp_frontFin {p q n : ℕ} (h : p + q = n) (h₁ : (p + 1) + q = n + 1)
    (i : Fin (p + 1)) :
    (⟨i.1, by omega⟩ : Fin (n + 2)).succAbove ∘ frontFin h =
      frontFin h₁ ∘ i.castSucc.succAbove := by
  ext x
  simp only [Function.comp_apply, Fin.succAbove, frontFin, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

private lemma succAbove_left_comp_backFin {p q n : ℕ} (h : p + q = n) (h₁ : (p + 1) + q = n + 1)
    (i : Fin (p + 1)) :
    (⟨i.1, by omega⟩ : Fin (n + 2)).succAbove ∘ backFin h = backFin h₁ := by
  ext y
  simp only [Function.comp_apply, Fin.succAbove, backFin, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp <;> omega

private lemma succAbove_right_comp_frontFin {p q n : ℕ} (h : p + q = n) (h₂ : p + (q + 1) = n + 1)
    (j : Fin (q + 1)) :
    (⟨p + 1 + j.1, by omega⟩ : Fin (n + 2)).succAbove ∘ frontFin h = frontFin h₂ := by
  ext x
  simp only [Function.comp_apply, Fin.succAbove, frontFin, Fin.lt_def, Fin.val_castSucc]
  split_ifs
  · rfl
  · omega

private lemma succAbove_right_comp_backFin {p q n : ℕ} (h : p + q = n) (h₂ : p + (q + 1) = n + 1)
    (j : Fin (q + 1)) :
    (⟨p + 1 + j.1, by omega⟩ : Fin (n + 2)).succAbove ∘ backFin h =
      backFin h₂ ∘ j.succ.succAbove := by
  ext y
  simp only [Function.comp_apply, Fin.succAbove, backFin, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

private lemma frontFin_comp_last_succAbove {p q n : ℕ} (h₁ : (p + 1) + q = n + 1)
    (h₂ : p + (q + 1) = n + 1) :
    frontFin h₁ ∘ (Fin.last (p + 1)).succAbove = frontFin h₂ := by
  ext x
  simp [frontFin, Fin.succAbove_last]

private lemma backFin_comp_zero_succAbove {p q n : ℕ} (h₁ : (p + 1) + q = n + 1)
    (h₂ : p + (q + 1) = n + 1) :
    backFin h₂ ∘ (0 : Fin (q + 2)).succAbove = backFin h₁ := by
  ext y
  simp only [Function.comp_apply, backFin, Fin.succAbove_zero, Fin.val_succ]
  omega

private lemma neg_one_pow_triangle_add (p q n : ℕ) (h : p + q = n) :
    (-1 : ℤ) ^ (n * (n + 1) / 2) * (-1 : ℤ) ^ (p * (p + 1) / 2) *
      (-1 : ℤ) ^ (q * (q + 1) / 2) = (-1 : ℤ) ^ (p * q) := by
  have htri : n * (n + 1) / 2 = p * (p + 1) / 2 + q * (q + 1) / 2 + p * q := by
    subst h
    have hp := Nat.even_mul_succ_self p
    have hq := Nat.even_mul_succ_self q
    have hmul : (p + q) * (p + q + 1) = p * (p + 1) + q * (q + 1) + 2 * (p * q) := by ring
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    omega
  have hsq (m : ℕ) : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [htri, pow_add, pow_add]
  calc ((-1 : ℤ) ^ (p * (p + 1) / 2) * (-1 : ℤ) ^ (q * (q + 1) / 2) * (-1 : ℤ) ^ (p * q)) *
        (-1 : ℤ) ^ (p * (p + 1) / 2) * (-1 : ℤ) ^ (q * (q + 1) / 2)
      = ((-1 : ℤ) ^ (p * (p + 1) / 2) * (-1 : ℤ) ^ (p * (p + 1) / 2)) *
        ((-1 : ℤ) ^ (q * (q + 1) / 2) * (-1 : ℤ) ^ (q * (q + 1) / 2)) * (-1 : ℤ) ^ (p * q) := by
        ring
    _ = (-1 : ℤ) ^ (p * q) := by rw [hsq, hsq, one_mul, one_mul]

/-! ### Elementwise extensionality for products in `ModuleCat` -/

/-- Two elements of a categorical product in `ModuleCat` agree if all their projections agree,
without any universe restriction between the ring, the index type, and the modules. -/
private lemma moduleCat_pi_ext {R : Type uR} [Ring R] {α : Type w}
    {f : α → ModuleCat.{u'} R} [HasProduct f] {x y : (∏ᶜ f : ModuleCat.{u'} R)}
    (h : ∀ k, Pi.π f k x = Pi.π f k y) : x = y := by
  let M : Submodule R (∏ᶜ f : ModuleCat.{u'} R) := Submodule.span R {x - y}
  have hι : ModuleCat.ofHom M.subtype = (0 : ModuleCat.of R M ⟶ ∏ᶜ f) := by
    refine Pi.hom_ext _ _ fun k ↦ ?_
    ext ⟨m, hm⟩
    have hmem : x - y ∈ LinearMap.ker (Pi.π f k).hom := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 (h k)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, Limits.zero_comp, ModuleCat.hom_zero,
      LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.zero_apply] using
      LinearMap.mem_ker.1 (((Submodule.span_singleton_le_iff_mem (x - y) _).2 hmem) hm)
  exact sub_eq_zero.1 <|
    ConcreteCategory.congr_hom hι ⟨x - y, Submodule.mem_span_singleton_self (x - y)⟩

/-! ### Projections of Čech complexes in `ModuleCat` -/

section Helpers

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [Ring R] [HasProducts.{w} (ModuleCat.{u'} R)]

/-- Projection from the degree-`n` Čech cochain object to the factor indexed by `k`, typed with
domain `((cechComplexFunctor U).obj P).X n` so rewrites stay well-typed at implicit transparency. -/
private def cechPi {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (n : ℕ)
    (k : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).obj P).X n ⟶ P.obj (op (∏ᶜ fun j ↦ U (k j))) :=
  Pi.π (fun c : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j)))) k

private lemma cechX_ext {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (n : ℕ)
    {x y : ((cechComplexFunctor U).obj P).X n}
    (h : ∀ k, cechPi U P n k x = cechPi U P n k y) : x = y :=
  moduleCat_pi_ext (f := fun c : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j)))) h

/-- The canonical projection `∏ⱼ U (b j) ⟶ ∏ⱼ U ((b ∘ α) j)` induced by a reindexing `α`. -/
private def reproj {ι : Type w} (U : ι → C) {m k : ℕ} (b : Fin (m + 1) → ι)
    (α : Fin (k + 1) → Fin (m + 1)) :
    (∏ᶜ fun j : Fin (m + 1) ↦ U (b j)) ⟶ (∏ᶜ fun j : Fin (k + 1) ↦ U ((b ∘ α) j)) :=
  Pi.lift fun j ↦ Pi.π (fun l ↦ U (b l)) (α j)

private lemma reproj_id_apply {ι : Type w} (U : ι → C) {m : ℕ} (b : Fin (m + 1) → ι)
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (x : ((cechComplexFunctor U).obj P).X m) :
    P.map (reproj U b id).op (cechPi U P m (b ∘ id) x) = cechPi U P m b x := by
  have h : reproj U b id = 𝟙 (∏ᶜ fun j ↦ U (b j)) :=
    Pi.hom_ext _ _ fun j ↦ by simp [reproj]
  exact (congrArg (fun f ↦ P.map f.op (cechPi U P m b x)) h).trans (by rw [op_id, P.map_id])

private lemma reproj_comp_apply {ι : Type w} (U : ι → C) {m k l : ℕ} (b : Fin (m + 1) → ι)
    (α : Fin (k + 1) → Fin (m + 1)) (β : Fin (l + 1) → Fin (k + 1))
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (x : ((cechComplexFunctor U).obj P).X l) :
    P.map (reproj U b α).op (P.map (reproj U (b ∘ α) β).op (cechPi U P l ((b ∘ α) ∘ β) x)) =
      P.map (reproj U b (α ∘ β)).op (cechPi U P l (b ∘ (α ∘ β)) x) := by
  have h : reproj U b α ≫ reproj U (b ∘ α) β = reproj U b (α ∘ β) :=
    Pi.hom_ext _ _ fun j ↦ by simp [reproj]
  exact ConcreteCategory.congr_hom
    ((P.map_comp (reproj U (b ∘ α) β).op (reproj U b α).op).symm.trans
      (congrArg (fun f ↦ P.map f.op) h))
    (cechPi U P l (b ∘ (α ∘ β)) x)

private lemma reproj_congr {ι : Type w} (U : ι → C) {m k : ℕ} (b : Fin (m + 1) → ι)
    {α β : Fin (k + 1) → Fin (m + 1)} (h : α = β) (P : Cᵒᵖ ⥤ ModuleCat.{u'} R)
    (x : ((cechComplexFunctor U).obj P).X k) :
    P.map (reproj U b α).op (cechPi U P k (b ∘ α) x) =
      P.map (reproj U b β).op (cechPi U P k (b ∘ β) x) := by
  subst h; rfl

private lemma π_cechD_apply {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (k : Fin (n + 2) → ι) :
    cechPi U P (n + 1) k (((cechComplexFunctor U).obj P).d n (n + 1) a) =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        P.map (reproj U k m.succAbove).op (cechPi U P n (k ∘ m.succAbove) a) := by
  have h : ((cechComplexFunctor U).obj P).d n (n + 1) ≫ cechPi U P (n + 1) k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        (cechPi U P n (k ∘ m.succAbove) ≫ P.map (reproj U k m.succAbove).op) :=
    cechComplexFunctor_obj_d_comp_π U P n k
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] using h'

private lemma π_cechOrderReversal_apply {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{u'} R)
    (n : ℕ) (a : ((cechComplexFunctor U).obj P).X n) (k : Fin (n + 1) → ι) :
    cechPi U P n k (((cechOrderReversal U).app P).f n a) =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        P.map (reproj U k Fin.rev).op (cechPi U P n (k ∘ Fin.rev) a) := by
  have h : ((cechOrderReversal U).app P).f n ≫ cechPi U P n k =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        (cechPi U P n (k ∘ Fin.rev) ≫ P.map (reproj U k Fin.rev).op) :=
    cechOrderReversal_app_f_π U P n k
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.smul_apply] using h'

private lemma π_cechComplexMap_apply {ι κ : Type w} {U : ι → C} {V : κ → C}
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : ((cechComplexFunctor V).obj P).X n) (k : Fin (n + 1) → ι) :
    cechPi U P n k ((cechComplexMap P φ).f n a) =
      P.map (Limits.Pi.map (f := fun j ↦ U (k j)) (g := fun j ↦ V ((φ.f ∘ k) j))
        fun j ↦ φ.φ (k j)).op (cechPi V P n (φ.f ∘ k) a) :=
  ConcreteCategory.congr_hom (cechComplexMap_f_π P φ n k) a

private lemma π_cechComplexFunctor_map_apply {ι : Type w} (U : ι → C)
    {P Q : Cᵒᵖ ⥤ ModuleCat.{u'} R} (α : P ⟶ Q) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (k : Fin (n + 1) → ι) :
    cechPi U Q n k (((cechComplexFunctor U).map α).f n a) =
      α.app (op (∏ᶜ fun j ↦ U (k j))) (cechPi U P n k a) :=
  ConcreteCategory.congr_hom (cechComplexFunctor_map_f_π U P α n k) a

private lemma π_cechComplexCompIso_hom_apply {D : Type u''} [Category.{v''} D] [HasFiniteProducts D]
    {ι : Type w} (G : C ⥤ D) (U : ι → C) (Q : Dᵒᵖ ⥤ ModuleCat.{u'} R)
    (hG : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (piComparison G fun j ↦ U (a j)))
    (n : ℕ) (a : ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).X n) (k : Fin (n + 1) → ι) :
    cechPi U (G.op ⋙ Q) n k ((cechComplexCompIso G U Q hG).hom.f n a) =
      Q.map (Pi.lift fun j ↦ G.map (Pi.π (fun j ↦ U (k j)) j)).op
        (cechPi (fun i ↦ G.obj (U i)) Q n k a) :=
  ConcreteCategory.congr_hom (cechComplexCompIso_hom_f_π G U Q hG n k) a

private lemma π_cechAugmentation_apply {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (s : P.obj (op T)) (a : Fin 1 → ι) :
    cechPi U P 0 a
        (((cechAugmentation U hT P).f 0)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv s)) =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op s := by
  have h : (cechAugmentation U hT P).f 0 ≫ cechPi U P 0 a =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).hom ≫
        P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op :=
    cechAugmentation_f_zero_comp_π U hT P a
  have h' : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv ≫
      (cechAugmentation U hT P).f 0 ≫ cechPi U P 0 a =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op := by
    rw [h, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom h' s

private lemma iCycles_augmentation_apply {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (s : P.obj (op T)) :
    ((cechComplexFunctor U).obj P).iCycles 0
        (HomologicalComplex.cyclesMap (cechAugmentation U hT P) 0
          ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
            (P.obj (op T))).inv s)) =
      ((cechAugmentation U hT P).f 0)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv s) := by
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  congr 1
  have h : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv ≫
      ((CochainComplex.single₀ _).obj (P.obj (op T))).iCycles 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv := by
    rw [← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso _ 0 _).hom,
      Iso.hom_inv_id_assoc, HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h s

private lemma homologyπ_augmentation_apply {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{u'} R) (s : P.obj (op T)) :
    ((cechComplexFunctor U).obj P).homologyπ 0
        (HomologicalComplex.cyclesMap (cechAugmentation U hT P) 0
          ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
            (P.obj (op T))).inv s)) =
      HomologicalComplex.homologyMap (cechAugmentation U hT P) 0
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          (P.obj (op T))).inv s) := by
  rw [← HomologicalComplex.moduleCat_homologyMap_homologyπ]
  exact congrArg (HomologicalComplex.homologyMap (cechAugmentation U hT P) 0)
    (ConcreteCategory.congr_hom (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ _ _ _) s)

end Helpers

end CechCup

open CechCup

/-! ### The cochain-level Čech cup product -/

section Cochain

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [CommRing R] [HasProducts.{w} (ModuleCat.{u'} R)]
  {ι : Type w} (U : ι → C)
  {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}

/-- Cupping on the left with a fixed Čech `p`-cochain, as a morphism `Č^q(U, Q) ⟶ Čⁿ(U, S)`. -/
private def cechCupCochainLeft (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).X p) :
    ((cechComplexFunctor U).obj Q).X q ⟶ ((cechComplexFunctor U).obj S).X n :=
  Pi.lift fun k : Fin (n + 1) → ι ↦
    cechPi U Q q (k ∘ backFin h) ≫ Q.map (reproj U k (backFin h)).op ≫
      ModuleCat.ofHom (μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h)).op (cechPi U P p (k ∘ frontFin h) a)))

private lemma π_cechCupCochainLeft (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).X p)
    (b : ((cechComplexFunctor U).obj Q).X q) (k : Fin (n + 1) → ι) :
    cechPi U S n k (cechCupCochainLeft U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h)).op (cechPi U P p (k ∘ frontFin h) a))
        (Q.map (reproj U k (backFin h)).op (cechPi U Q q (k ∘ backFin h) b)) :=
  ConcreteCategory.congr_hom (Pi.lift_comp_π _ k) b

/-- **The Čech cup product of cochains.** For a pairing
`μ : ∀ V, P(V) →ₗ[R] Q(V) →ₗ[R] S(V)` and degrees `p + q = n`, this is the `R`-bilinear map
`Čᵖ(U, P) × Č^q(U, Q) ⟶ Čⁿ(U, S)` whose component at a tuple `k : Fin (n + 1) → ι` pairs the
front `p`-face of the first argument with the back `q`-face of the second (`π_cechCupCochain`). -/
def cechCupCochain (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).X p →ₗ[R]
      ((cechComplexFunctor U).obj Q).X q →ₗ[R]
        ((cechComplexFunctor U).obj S).X n where
  toFun a := (cechCupCochainLeft U μ p q n h a).hom
  map_add' a a' := LinearMap.ext fun b ↦ cechX_ext U S n fun k ↦ by
    simp only [LinearMap.add_apply, map_add]
    exact (π_cechCupCochainLeft U μ p q n h (a + a') b k).trans <| by
      rw [π_cechCupCochainLeft, π_cechCupCochainLeft]
      simp [map_add]
  map_smul' r a := LinearMap.ext fun b ↦ cechX_ext U S n fun k ↦ by
    simp only [RingHom.id_apply, LinearMap.smul_apply, map_smul]
    exact (π_cechCupCochainLeft U μ p q n h (r • a) b k).trans <| by
      rw [π_cechCupCochainLeft]
      simp [map_smul]

/-- The component of `cechCupCochain U μ p q n h a b` at a tuple `k : Fin (n + 1) → ι` is `μ`
applied to the restriction of `a` from the front `p`-face and of `b` from the back `q`-face. -/
theorem π_cechCupCochain (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).X p)
    (b : ((cechComplexFunctor U).obj Q).X q) (k : Fin (n + 1) → ι) :
    Pi.π (fun c : Fin (n + 1) → ι ↦ S.obj (op (∏ᶜ fun j ↦ U (c j)))) k
        (cechCupCochain U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (Pi.lift fun i : Fin (p + 1) ↦ Pi.π (fun j ↦ U (k j)) ⟨i.1, by omega⟩).op
          (Pi.π (fun c : Fin (p + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j))))
            (fun i ↦ k ⟨i.1, by omega⟩) a))
        (Q.map (Pi.lift fun i : Fin (q + 1) ↦ Pi.π (fun j ↦ U (k j)) ⟨p + i.1, by omega⟩).op
          (Pi.π (fun c : Fin (q + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ U (c j))))
            (fun i ↦ k ⟨p + i.1, by omega⟩) b)) :=
  π_cechCupCochainLeft U μ p q n h a b k

private lemma π_cechCupCochain_reproj (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (p q n : ℕ) (h : p + q = n) (a : ((cechComplexFunctor U).obj P).X p)
    (b : ((cechComplexFunctor U).obj Q).X q) (k : Fin (n + 1) → ι) :
    cechPi U S n k (cechCupCochain U μ p q n h a b) =
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h)).op (cechPi U P p (k ∘ frontFin h) a))
        (Q.map (reproj U k (backFin h)).op (cechPi U Q q (k ∘ backFin h) b)) :=
  π_cechCupCochainLeft U μ p q n h a b k

private lemma d_cechCupCochain_lhs_term (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    {p q n : ℕ} (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (k : Fin (n + 2) → ι) (m : Fin (n + 2)) :
    S.map (reproj U k m.succAbove).op
        (cechPi U S n (k ∘ m.succAbove) (cechCupCochain U μ p q n h a b)) =
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (m.succAbove ∘ frontFin h)).op
          (cechPi U P p (k ∘ (m.succAbove ∘ frontFin h)) a))
        (Q.map (reproj U k (m.succAbove ∘ backFin h)).op
          (cechPi U Q q (k ∘ (m.succAbove ∘ backFin h)) b)) := by
  rw [π_cechCupCochain_reproj, hμ, reproj_comp_apply, reproj_comp_apply]

private lemma d_cechCupCochain_left_term (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    {p q n : ℕ} (h : p + q = n) (h₁ : (p + 1) + q = n + 1)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (k : Fin (n + 2) → ι) (i : Fin (p + 1)) {m : Fin (n + 2)}
    (hm : m = ⟨i.1, by omega⟩) :
    (-1 : ℤ) ^ (m : ℕ) •
        μ (op (∏ᶜ fun j ↦ U (k j)))
          (P.map (reproj U k (m.succAbove ∘ frontFin h)).op
            (cechPi U P p (k ∘ (m.succAbove ∘ frontFin h)) a))
          (Q.map (reproj U k (m.succAbove ∘ backFin h)).op
            (cechPi U Q q (k ∘ (m.succAbove ∘ backFin h)) b)) =
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h₁)).op
          ((-1 : ℤ) ^ (i.castSucc : ℕ) • P.map (reproj U (k ∘ frontFin h₁) i.castSucc.succAbove).op
            (cechPi U P p ((k ∘ frontFin h₁) ∘ i.castSucc.succAbove) a)))
        (Q.map (reproj U k (backFin h₁)).op (cechPi U Q q (k ∘ backFin h₁) b)) := by
  subst hm
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply, reproj_comp_apply,
    reproj_congr U k (succAbove_left_comp_frontFin h h₁ i),
    reproj_congr U k (succAbove_left_comp_backFin h h₁ i)]
  rfl

private lemma d_cechCupCochain_right_term (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    {p q n : ℕ} (h : p + q = n) (h₂ : p + (q + 1) = n + 1)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (k : Fin (n + 2) → ι) (j : Fin (q + 1)) {m : Fin (n + 2)}
    (hm : m = ⟨p + 1 + j.1, by omega⟩) :
    (-1 : ℤ) ^ (m : ℕ) •
        μ (op (∏ᶜ fun j ↦ U (k j)))
          (P.map (reproj U k (m.succAbove ∘ frontFin h)).op
            (cechPi U P p (k ∘ (m.succAbove ∘ frontFin h)) a))
          (Q.map (reproj U k (m.succAbove ∘ backFin h)).op
            (cechPi U Q q (k ∘ (m.succAbove ∘ backFin h)) b)) =
      (-1 : ℤ) ^ p • μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h₂)).op (cechPi U P p (k ∘ frontFin h₂) a))
        (Q.map (reproj U k (backFin h₂)).op
          ((-1 : ℤ) ^ (j.succ : ℕ) • Q.map (reproj U (k ∘ backFin h₂) j.succ.succAbove).op
            (cechPi U Q q ((k ∘ backFin h₂) ∘ j.succ.succAbove) b))) := by
  subst hm
  have hpow : (-1 : ℤ) ^ (p + 1 + j.1) = (-1 : ℤ) ^ p * (-1 : ℤ) ^ (j.succ : ℕ) := by
    rw [← pow_add]; congr 1; simp [Fin.val_succ]; omega
  rw [map_zsmul, map_zsmul, smul_smul, reproj_comp_apply,
    reproj_congr U k (succAbove_right_comp_frontFin h h₂ j),
    reproj_congr U k (succAbove_right_comp_backFin h h₂ j)]
  exact congrArg (· • _) hpow

private lemma d_cechCupCochain_cancel (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    {p q n : ℕ} (h₁ : (p + 1) + q = n + 1) (h₂ : p + (q + 1) = n + 1)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (k : Fin (n + 2) → ι) :
    μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h₁)).op
          ((-1 : ℤ) ^ (Fin.last (p + 1) : ℕ) •
            P.map (reproj U (k ∘ frontFin h₁) (Fin.last (p + 1)).succAbove).op
              (cechPi U P p ((k ∘ frontFin h₁) ∘ (Fin.last (p + 1)).succAbove) a)))
        (Q.map (reproj U k (backFin h₁)).op (cechPi U Q q (k ∘ backFin h₁) b)) +
      (-1 : ℤ) ^ p • μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (reproj U k (frontFin h₂)).op (cechPi U P p (k ∘ frontFin h₂) a))
        (Q.map (reproj U k (backFin h₂)).op
          ((-1 : ℤ) ^ ((0 : Fin (q + 2)) : ℕ) •
            Q.map (reproj U (k ∘ backFin h₂) (0 : Fin (q + 2)).succAbove).op
              (cechPi U Q q ((k ∘ backFin h₂) ∘ (0 : Fin (q + 2)).succAbove) b))) = 0 := by
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply, map_zsmul, map_zsmul, smul_smul,
    reproj_comp_apply, reproj_comp_apply,
    reproj_congr U k (frontFin_comp_last_succAbove h₁ h₂),
    reproj_congr U k (backFin_comp_zero_succAbove h₁ h₂)]
  simp only [Fin.val_last, Fin.val_zero, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul,
    neg_add_cancel]

/-- **The graded Leibniz rule for the Čech cup product**:
`d (a ⌣ b) = (d a) ⌣ b + (-1)^p • (a ⌣ d b)`. -/
theorem d_cechCupCochain (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechComplexFunctor U).obj S).d n (n + 1) (cechCupCochain U μ p q n h a b) =
      cechCupCochain U μ (p + 1) q (n + 1) (by omega)
        (((cechComplexFunctor U).obj P).d p (p + 1) a) b +
      (-1 : ℤ) ^ p • cechCupCochain U μ p (q + 1) (n + 1) (by omega) a
        (((cechComplexFunctor U).obj Q).d q (q + 1) b) := by
  refine cechX_ext U S (n + 1) fun k ↦ ?_
  have h₁ : (p + 1) + q = n + 1 := by omega
  have h₂ : p + (q + 1) = n + 1 := by omega
  rw [map_add, map_zsmul, π_cechD_apply, π_cechCupCochain_reproj, π_cechCupCochain_reproj,
    π_cechD_apply, π_cechD_apply, map_sum, map_sum, LinearMap.sum_apply, map_sum, map_sum,
    Finset.smul_sum]
  simp_rw [d_cechCupCochain_lhs_term U μ hμ h a b k]
  let e : Fin ((p + 1) + (q + 1)) ≃ Fin (n + 2) := finCongr (by omega)
  rw [← Fintype.sum_equiv e _ (fun m ↦ (-1 : ℤ) ^ (m : ℕ) • _) (fun _ ↦ rfl), Fin.sum_univ_add]
  conv_rhs => arg 1; rw [Fin.sum_univ_castSucc]
  conv_rhs => arg 2; rw [Fin.sum_univ_succ]
  rw [Finset.sum_congr rfl fun i _ ↦
        d_cechCupCochain_left_term U μ h h₁ a b k i (Fin.ext (by simp [e])),
      Finset.sum_congr rfl fun j _ ↦
        d_cechCupCochain_right_term U μ h h₂ a b k j (Fin.ext (by simp [e])),
      add_assoc (∑ i : Fin (p + 1), _), ← add_assoc (μ _ _ _),
      d_cechCupCochain_cancel U μ h₁ h₂ a b k, zero_add]

/-- **Strict associativity of the Čech cup product on cochains.** -/
theorem cechCupCochain_assoc {T₁₂ T₂₃ T : Cᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ₁₂ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] T₁₂.obj V)
    (hμ₁₂ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, T₁₂.map f (μ₁₂ V x y) = μ₁₂ W (P.map f x) (Q.map f y))
    (μ₁₂₃ : ∀ V : Cᵒᵖ, T₁₂.obj V →ₗ[R] S.obj V →ₗ[R] T.obj V)
    (μ₂₃ : ∀ V : Cᵒᵖ, Q.obj V →ₗ[R] S.obj V →ₗ[R] T₂₃.obj V)
    (hμ₂₃ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) y z, T₂₃.map f (μ₂₃ V y z) = μ₂₃ W (Q.map f y) (S.map f z))
    (μ₁_₂₃ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] T₂₃.obj V →ₗ[R] T.obj V)
    (hassoc : ∀ V x y z, μ₁₂₃ V (μ₁₂ V x y) z = μ₁_₂₃ V x (μ₂₃ V y z))
    {p q r pq qr n : ℕ} (h₁ : p + q = pq) (h₂ : pq + r = n) (h₃ : q + r = qr) (h₄ : p + qr = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q)
    (c : ((cechComplexFunctor U).obj S).X r) :
    cechCupCochain U μ₁₂₃ pq r n h₂ (cechCupCochain U μ₁₂ p q pq h₁ a b) c =
      cechCupCochain U μ₁_₂₃ p qr n h₄ a (cechCupCochain U μ₂₃ q r qr h₃ b c) := by
  refine cechX_ext U T n fun k ↦ ?_
  rw [π_cechCupCochain_reproj, π_cechCupCochain_reproj, π_cechCupCochain_reproj,
    π_cechCupCochain_reproj, hμ₁₂, hμ₂₃, hassoc, reproj_comp_apply, reproj_comp_apply,
    reproj_comp_apply, reproj_comp_apply,
    reproj_congr U k (frontFin_comp_frontFin h₁ h₂ h₄),
    reproj_congr U k (frontFin_comp_backFin h₁ h₂ h₃ h₄),
    reproj_congr U k (backFin_comp_backFin h₁ h₂ h₃ h₄)]

/-- Left unitality of the Čech cup product on cochains for a `0`-cochain acting as the left unit. -/
theorem cechCupCochain_left_unit (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] Q.obj V)
    (q : ℕ) (e : ((cechComplexFunctor U).obj P).X 0)
    (he : ∀ (k : Fin (q + 1) → ι) (y : Q.obj (op (∏ᶜ fun j ↦ U (k j)))),
      μ (op (∏ᶜ fun j ↦ U (k j)))
        (P.map (Pi.lift fun _ : Fin 1 ↦ Pi.π (fun j ↦ U (k j)) 0).op
          (Pi.π (fun c : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j)))) (fun _ ↦ k 0) e)) y = y)
    (b : ((cechComplexFunctor U).obj Q).X q) :
    cechCupCochain U μ 0 q q (Nat.zero_add q) e b = b := by
  refine cechX_ext U Q q fun k ↦ ?_
  have hfront : frontFin (Nat.zero_add q) = fun _ ↦ 0 :=
    funext fun i ↦ Fin.ext (by simp [frontFin])
  have he' : ∀ y, μ (op (∏ᶜ fun j ↦ U (k j)))
      (P.map (reproj U k (fun _ : Fin 1 ↦ (0 : Fin (q + 1)))).op
        (cechPi U P 0 (k ∘ fun _ ↦ 0) e)) y = y := he k
  rw [π_cechCupCochain_reproj, reproj_congr U k hfront, he',
    reproj_congr U k (backFin_zero_left (Nat.zero_add q)), reproj_id_apply]

/-- Right unitality of the Čech cup product on cochains for a `0`-cochain acting as the right
unit. -/
theorem cechCupCochain_right_unit (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] P.obj V)
    (p : ℕ) (e : ((cechComplexFunctor U).obj Q).X 0)
    (he : ∀ (k : Fin (p + 1) → ι) (x : P.obj (op (∏ᶜ fun j ↦ U (k j)))),
      μ (op (∏ᶜ fun j ↦ U (k j))) x
        (Q.map (Pi.lift fun _ : Fin 1 ↦ Pi.π (fun j ↦ U (k j)) (Fin.last p)).op
          (Pi.π (fun c : Fin 1 → ι ↦ Q.obj (op (∏ᶜ fun j ↦ U (c j))))
            (fun _ ↦ k (Fin.last p)) e)) = x)
    (a : ((cechComplexFunctor U).obj P).X p) :
    cechCupCochain U μ p 0 p (Nat.add_zero p) a e = a := by
  refine cechX_ext U P p fun k ↦ ?_
  have hback : backFin (Nat.add_zero p) = fun _ ↦ Fin.last p :=
    funext fun i ↦ Fin.ext (by simp [backFin])
  have he' : ∀ x, μ (op (∏ᶜ fun j ↦ U (k j))) x
      (Q.map (reproj U k (fun _ : Fin 1 ↦ Fin.last p)).op
        (cechPi U Q 0 (k ∘ fun _ ↦ Fin.last p) e)) = x := he k
  rw [π_cechCupCochain_reproj, reproj_congr U k hback, he',
    reproj_congr U k (frontFin_zero_right (Nat.add_zero p)), reproj_id_apply]

/-- **Order reversal relates `a ⌣ b` and `b ⌣ a` on cochains**:
`τ (τ b ⌣_{μ'} τ a) = (-1)^(p * q) • (a ⌣_μ b)` whenever `μ' V y x = μ V x y`. -/
theorem cechOrderReversal_cechCupCochain
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (μ' : ∀ V : Cᵒᵖ, Q.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V)
    (hμ' : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) y x, S.map f (μ' V y x) = μ' W (Q.map f y) (P.map f x))
    (hswap : ∀ V x y, μ' V y x = μ V x y)
    {p q n : ℕ} (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechOrderReversal U).app S).f n
        (cechCupCochain U μ' q p n (by omega)
          (((cechOrderReversal U).app Q).f q b) (((cechOrderReversal U).app P).f p a)) =
      (-1 : ℤ) ^ (p * q) • cechCupCochain U μ p q n h a b := by
  refine cechX_ext U S n fun k ↦ ?_
  have h' : q + p = n := by omega
  rw [map_zsmul, π_cechOrderReversal_apply, π_cechCupCochain_reproj, π_cechCupCochain_reproj,
    hμ', π_cechOrderReversal_apply, π_cechOrderReversal_apply, map_zsmul, map_zsmul, map_zsmul,
    map_zsmul, LinearMap.smul_apply, map_zsmul, map_zsmul, smul_smul, smul_smul,
    reproj_comp_apply, reproj_comp_apply, reproj_comp_apply, reproj_comp_apply,
    reproj_congr U k (rev_comp_frontFin_comp_rev h h'),
    reproj_congr U k (rev_comp_backFin_comp_rev h h'), hswap]
  congr 1
  calc (-1 : ℤ) ^ (n * (n + 1) / 2) * (-1 : ℤ) ^ (q * (q + 1) / 2) * (-1 : ℤ) ^ (p * (p + 1) / 2)
      = (-1 : ℤ) ^ (n * (n + 1) / 2) * (-1 : ℤ) ^ (p * (p + 1) / 2) *
          (-1 : ℤ) ^ (q * (q + 1) / 2) := by ring
    _ = (-1 : ℤ) ^ (p * q) := neg_one_pow_triangle_add p q n h

/-- Morphisms of presheaves compatible with bilinear pairings preserve the cochain-level Čech cup
product. -/
theorem cechComplexFunctor_map_cechCupCochain {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (μ' : ∀ V : Cᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' V (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    cechCupCochain U μ' p q n h (((cechComplexFunctor U).map α).f p a)
        (((cechComplexFunctor U).map β).f q b) =
      ((cechComplexFunctor U).map γ).f n (cechCupCochain U μ p q n h a b) := by
  refine cechX_ext U S' n fun k ↦ ?_
  rw [π_cechCupCochain_reproj, π_cechComplexFunctor_map_apply, π_cechComplexFunctor_map_apply,
    π_cechComplexFunctor_map_apply, π_cechCupCochain_reproj, hγ, ← ModuleCat.comp_apply,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← α.naturality,
    ← β.naturality]
  simp only [ModuleCat.comp_apply]

/-- Product-preserving functors preserve the cochain-level Čech cup product through
`cechComplexCompIso`. -/
theorem cechComplexCompIso_hom_cechCupCochain {D : Type u''} [Category.{v''} D]
    [HasFiniteProducts D] (G : C ⥤ D)
    (hG : ∀ (m : ℕ) (a : Fin (m + 1) → ι), IsIso (piComparison G fun j ↦ U (a j)))
    {P' Q' S' : Dᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ : ∀ V : Dᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ : ∀ ⦃V W : Dᵒᵖ⦄ (f : V ⟶ W) x y, S'.map f (μ V x y) = μ W (P'.map f x) (Q'.map f y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj P').X p)
    (b : ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q').X q) :
    cechCupCochain U (fun V ↦ μ (op (G.obj (unop V)))) p q n h
        ((cechComplexCompIso G U P' hG).hom.f p a)
        ((cechComplexCompIso G U Q' hG).hom.f q b) =
      (cechComplexCompIso G U S' hG).hom.f n
        (cechCupCochain (fun i ↦ G.obj (U i)) μ p q n h a b) := by
  refine cechX_ext U (G.op ⋙ S') n fun k ↦ ?_
  rw [π_cechCupCochain_reproj, π_cechComplexCompIso_hom_apply, π_cechComplexCompIso_hom_apply,
    π_cechComplexCompIso_hom_apply, π_cechCupCochain_reproj, hμ]
  have hcomm {m : ℕ} (α : Fin (m + 1) → Fin (n + 1)) :
      G.map (reproj U k α) ≫ Pi.lift (fun j ↦ G.map (Pi.π (fun l ↦ U ((k ∘ α) l)) j)) =
        Pi.lift (fun j ↦ G.map (Pi.π (fun l ↦ U (k l)) j)) ≫
          reproj (fun i ↦ G.obj (U i)) k α :=
    Pi.hom_ext _ _ fun j ↦ by simp [reproj, ← G.map_comp]
  simp only [Functor.comp_map, Functor.op_map, ← ModuleCat.comp_apply, Category.assoc,
    ← P'.map_comp, ← Q'.map_comp, ← op_comp, Quiver.Hom.unop_op]
  rw [hcomm (frontFin h), hcomm (backFin h)]

end Cochain

section CochainRefinement

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [CommRing R] [HasProducts.{w} (ModuleCat.{u'} R)]
  {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}

/-- Refinement maps preserve the cochain-level Čech cup product. -/
theorem cechComplexMap_cechCupCochain {ι κ : Type w} {U : ι → C} {V : κ → C}
    (μ : ∀ W : Cᵒᵖ, P.obj W →ₗ[R] Q.obj W →ₗ[R] S.obj W)
    (hμ : ∀ ⦃W W' : Cᵒᵖ⦄ (f : W ⟶ W') x y, S.map f (μ W x y) = μ W' (P.map f x) (Q.map f y))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor V).obj P).X p) (b : ((cechComplexFunctor V).obj Q).X q) :
    cechCupCochain U μ p q n h ((cechComplexMap P φ).f p a) ((cechComplexMap Q φ).f q b) =
      (cechComplexMap S φ).f n (cechCupCochain V μ p q n h a b) := by
  refine cechX_ext U S n fun k ↦ ?_
  rw [π_cechCupCochain_reproj, π_cechComplexMap_apply, π_cechComplexMap_apply,
    π_cechComplexMap_apply, π_cechCupCochain_reproj, hμ]
  have hcomm {m : ℕ} (α : Fin (m + 1) → Fin (n + 1)) :
      reproj U k α ≫
        Limits.Pi.map (f := fun j ↦ U ((k ∘ α) j)) (g := fun j ↦ V ((φ.f ∘ (k ∘ α)) j))
          (fun j ↦ φ.φ ((k ∘ α) j)) =
        Limits.Pi.map (f := fun j ↦ U (k j)) (g := fun j ↦ V ((φ.f ∘ k) j)) (fun j ↦ φ.φ (k j)) ≫
          reproj V (φ.f ∘ k) α :=
    Pi.hom_ext _ _ fun j ↦ by simp [reproj]
  have hside (K : Cᵒᵖ ⥤ ModuleCat.{u'} R) {m : ℕ} (α : Fin (m + 1) → Fin (n + 1))
      (x : ((cechComplexFunctor V).obj K).X m) :
      K.map (reproj U k α).op
          (K.map (Limits.Pi.map (f := fun j ↦ U ((k ∘ α) j)) (g := fun j ↦ V ((φ.f ∘ (k ∘ α)) j))
            (fun j ↦ φ.φ ((k ∘ α) j))).op (cechPi V K m (φ.f ∘ (k ∘ α)) x)) =
        K.map (Limits.Pi.map (f := fun j ↦ U (k j)) (g := fun j ↦ V ((φ.f ∘ k) j))
          (fun j ↦ φ.φ (k j))).op
          (K.map (reproj V (φ.f ∘ k) α).op (cechPi V K m ((φ.f ∘ k) ∘ α) x)) := by
    have hm : K.map (Limits.Pi.map (f := fun j ↦ U ((k ∘ α) j))
          (g := fun j ↦ V ((φ.f ∘ (k ∘ α)) j)) (fun j ↦ φ.φ ((k ∘ α) j))).op ≫
          K.map (reproj U k α).op =
        K.map (reproj V (φ.f ∘ k) α).op ≫
          K.map (Limits.Pi.map (f := fun j ↦ U (k j))
            (g := fun j ↦ V ((φ.f ∘ k) j)) (fun j ↦ φ.φ (k j))).op := by
      rw [← K.map_comp, ← K.map_comp, ← op_comp, ← op_comp, hcomm α]
    exact ConcreteCategory.congr_hom hm (cechPi V K m ((φ.f ∘ k) ∘ α) x)
  rw [hside P (frontFin h) a, hside Q (backFin h) b]

end CochainRefinement

/-! ### The fixed-cover cohomology cup product -/

section FixedCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [CommRing R] [HasProducts.{w} (ModuleCat.{u'} R)]
  {ι : Type w} (U : ι → C)
  {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}
  (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
  (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))

/-- Cupping on the left with a fixed Čech cocycle, as a morphism of cocycles. -/
private def cechCupCyclesLeft (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) :
    ((cechComplexFunctor U).obj Q).cycles q ⟶ ((cechComplexFunctor U).obj S).cycles n :=
  ((cechComplexFunctor U).obj S).liftCycles
    (ModuleCat.ofHom
      ((cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)) ∘ₗ
        (((cechComplexFunctor U).obj Q).iCycles q).hom)) (n + 1) (by simp) (by
      ext b
      have hd := d_cechCupCochain U μ hμ p q n h
        (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b)
      rw [HomologicalComplex.moduleCat_d_iCycles_apply,
        HomologicalComplex.moduleCat_d_iCycles_apply, LinearMap.map_zero₂, map_zero, smul_zero,
        add_zero] at hd
      exact hd)

private lemma iCycles_cechCupCyclesLeft (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).iCycles n (cechCupCyclesLeft U μ hμ p q n h a b) =
      cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b) :=
  ConcreteCategory.congr_hom (((cechComplexFunctor U).obj S).liftCycles_i _ _ _ _) b

/-- **The cup product of Čech cocycles**, induced by `cechCupCochain` via the Leibniz rule. -/
def cechCupCycles (p q n : ℕ) (h : p + q = n) :
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
theorem iCycles_cechCupCycles (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).iCycles n (cechCupCycles U μ hμ p q n h a b) =
      cechCupCochain U μ p q n h (((cechComplexFunctor U).obj P).iCycles p a)
        (((cechComplexFunctor U).obj Q).iCycles q b) :=
  iCycles_cechCupCyclesLeft U μ hμ p q n h a b

private lemma homologyπ_cechCupCycles_toCycles_right (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) (i : ℕ)
    (x : ((cechComplexFunctor U).obj Q).X i) :
    ((cechComplexFunctor U).obj S).homologyπ n
      (cechCupCycles U μ hμ p q n h a (((cechComplexFunctor U).obj Q).toCycles i q x)) = 0 := by
  by_cases hiq : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := hiq
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + i, by omega⟩
    have key : cechCupCycles U μ hμ p (i + 1) (m + 1) h a
        (((cechComplexFunctor U).obj Q).toCycles i (i + 1) x) =
        (-1 : ℤ) ^ p • ((cechComplexFunctor U).obj S).toCycles m (m + 1)
          (cechCupCochain U μ p i m (by omega) (((cechComplexFunctor U).obj P).iCycles p a) x) := by
      have hd := d_cechCupCochain U μ hμ p i m (by omega)
        (((cechComplexFunctor U).obj P).iCycles p a) x
      rw [HomologicalComplex.moduleCat_d_iCycles_apply, LinearMap.map_zero₂, zero_add] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cechCupCycles, map_zsmul, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        HomologicalComplex.moduleCat_iCycles_toCycles_apply, hd, smul_smul, ← mul_pow,
        neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, map_zsmul, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  · rw [((cechComplexFunctor U).obj Q).toCycles_eq_zero hiq]
    simp

private lemma homologyπ_cechCupCycles_toCycles_left (p q n : ℕ) (h : p + q = n) (i : ℕ)
    (x : ((cechComplexFunctor U).obj P).X i) (b : ((cechComplexFunctor U).obj Q).cycles q) :
    ((cechComplexFunctor U).obj S).homologyπ n
      (cechCupCycles U μ hμ p q n h (((cechComplexFunctor U).obj P).toCycles i p x) b) = 0 := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := hip
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨i + q, by omega⟩
    have key : cechCupCycles U μ hμ (i + 1) q (m + 1) h
        (((cechComplexFunctor U).obj P).toCycles i (i + 1) x) b =
        ((cechComplexFunctor U).obj S).toCycles m (m + 1)
          (cechCupCochain U μ i q m (by omega) x (((cechComplexFunctor U).obj Q).iCycles q b)) := by
      have hd := d_cechCupCochain U μ hμ i q m (by omega) x
        (((cechComplexFunctor U).obj Q).iCycles q b)
      rw [HomologicalComplex.moduleCat_d_iCycles_apply, map_zero, smul_zero, add_zero] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        HomologicalComplex.moduleCat_iCycles_toCycles_apply, hd]
    rw [key, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  · rw [((cechComplexFunctor U).obj P).toCycles_eq_zero hip]
    simp

private def cechCupHomologyLeft (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) :
    ((cechComplexFunctor U).obj Q).homology q ⟶ ((cechComplexFunctor U).obj S).homology n :=
  (CokernelCofork.IsColimit.desc' (((cechComplexFunctor U).obj Q).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cechCupCycles U μ hμ p q n h a) ≫
      ((cechComplexFunctor U).obj S).homologyπ n)
    (by ext x; exact homologyπ_cechCupCycles_toCycles_right U μ hμ p q n h a _ x)).1

private lemma cechCupHomologyLeft_homologyπ (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) (b : ((cechComplexFunctor U).obj Q).cycles q) :
    (cechCupHomologyLeft U μ hμ p q n h a).hom (((cechComplexFunctor U).obj Q).homologyπ q b) =
      ((cechComplexFunctor U).obj S).homologyπ n (cechCupCycles U μ hμ p q n h a b) := by
  unfold cechCupHomologyLeft
  exact ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj Q).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cechCupCycles U μ hμ p q n h a) ≫
      ((cechComplexFunctor U).obj S).homologyπ n) _).2 b

private def cechCupCyclesHomology (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).cycles p ⟶
      ModuleCat.of R
        (((cechComplexFunctor U).obj Q).homology q →ₗ[R]
          ((cechComplexFunctor U).obj S).homology n) :=
  ModuleCat.ofHom
    { toFun a := (cechCupHomologyLeft U μ hμ p q n h a).hom
      map_add' a a' := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [cechCupHomologyLeft_homologyπ, map_add, LinearMap.add_apply]
      map_smul' r a := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [cechCupHomologyLeft_homologyπ, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smul, LinearMap.smul_apply, map_smul] }

private lemma toCycles_comp_cechCupCyclesHomology (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).toCycles ((ComplexShape.up ℕ).prev p) p ≫
      cechCupCyclesHomology U μ hμ p q n h = 0 := by
  ext x : 2
  refine LinearMap.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  exact (cechCupHomologyLeft_homologyπ U μ hμ p q n h _ b).trans
    (homologyπ_cechCupCycles_toCycles_left U μ hμ p q n h _ x b)

/-- **The Čech cup product on fixed-family cohomology.** For a natural `R`-bilinear pairing
`μ : ∀ V, P(V) →ₗ[R] Q(V) →ₗ[R] S(V)` and degrees `p + q = n`, this is the `R`-bilinear map
`Hᵖ(Č(U, P)) × H^q(Č(U, Q)) ⟶ Hⁿ(Č(U, S))` sending the classes of cocycles `a` and `b` to the
class of `a ⌣ b` (`cechCup_homologyπ`). -/
def cechCup (p q n : ℕ) (h : p + q = n) :
    ((cechComplexFunctor U).obj P).homology p →ₗ[R]
      ((cechComplexFunctor U).obj Q).homology q →ₗ[R]
        ((cechComplexFunctor U).obj S).homology n :=
  (CokernelCofork.IsColimit.desc' (((cechComplexFunctor U).obj P).homologyIsCokernel _ p rfl)
    (cechCupCyclesHomology U μ hμ p q n h)
    (toCycles_comp_cechCupCyclesHomology U μ hμ p q n h)).1.hom

/-- On classes of cocycles, `cechCup` is the class of `cechCupCycles`. -/
@[simp]
theorem cechCup_homologyπ (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).cycles p) (b : ((cechComplexFunctor U).obj Q).cycles q) :
    cechCup U μ hμ p q n h (((cechComplexFunctor U).obj P).homologyπ p a)
        (((cechComplexFunctor U).obj Q).homologyπ q b) =
      ((cechComplexFunctor U).obj S).homologyπ n (cechCupCycles U μ hμ p q n h a b) := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (((cechComplexFunctor U).obj P).homologyIsCokernel _ p rfl)
    (cechCupCyclesHomology U μ hμ p q n h)
    (toCycles_comp_cechCupCyclesHomology U μ hμ p q n h)).2 a
  rw [cechCup, ← cechCupHomologyLeft_homologyπ]
  exact LinearMap.congr_fun hfac _

/-- **Associativity of the fixed-family Čech cup product.** -/
theorem cechCup_assoc {T₁₂ T₂₃ T : Cᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ₁₂ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] T₁₂.obj V)
    (hμ₁₂ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, T₁₂.map f (μ₁₂ V x y) = μ₁₂ W (P.map f x) (Q.map f y))
    (μ₁₂₃ : ∀ V : Cᵒᵖ, T₁₂.obj V →ₗ[R] S.obj V →ₗ[R] T.obj V)
    (hμ₁₂₃ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x z, T.map f (μ₁₂₃ V x z) = μ₁₂₃ W (T₁₂.map f x) (S.map f z))
    (μ₂₃ : ∀ V : Cᵒᵖ, Q.obj V →ₗ[R] S.obj V →ₗ[R] T₂₃.obj V)
    (hμ₂₃ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) y z, T₂₃.map f (μ₂₃ V y z) = μ₂₃ W (Q.map f y) (S.map f z))
    (μ₁_₂₃ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] T₂₃.obj V →ₗ[R] T.obj V)
    (hμ₁_₂₃ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y,
      T.map f (μ₁_₂₃ V x y) = μ₁_₂₃ W (P.map f x) (T₂₃.map f y))
    (hassoc : ∀ V x y z, μ₁₂₃ V (μ₁₂ V x y) z = μ₁_₂₃ V x (μ₂₃ V y z))
    {p q r pq qr n : ℕ} (h₁ : p + q = pq) (h₂ : pq + r = n) (h₃ : q + r = qr) (h₄ : p + qr = n)
    (α : ((cechComplexFunctor U).obj P).homology p)
    (β : ((cechComplexFunctor U).obj Q).homology q)
    (γ : ((cechComplexFunctor U).obj S).homology r) :
    cechCup U μ₁₂₃ hμ₁₂₃ pq r n h₂ (cechCup U μ₁₂ hμ₁₂ p q pq h₁ α β) γ =
      cechCup U μ₁_₂₃ hμ₁_₂₃ p qr n h₄ α (cechCup U μ₂₃ hμ₂₃ q r qr h₃ β γ) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r γ
  simp only [cechCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simpa only [iCycles_cechCupCycles] using
    cechCupCochain_assoc U μ₁₂ hμ₁₂ μ₁₂₃ μ₂₃ hμ₂₃ μ₁_₂₃ hassoc h₁ h₂ h₃ h₄ _ _ _

/-- **Graded commutativity of the fixed-family Čech cup product**:
`β ⌣_{μ'} α = (-1)^(p * q) • (α ⌣_μ β)` whenever `μ' V y x = μ V x y`. -/
theorem cechCup_gradedComm
    (μ' : ∀ V : Cᵒᵖ, Q.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V)
    (hμ' : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) y x, S.map f (μ' V y x) = μ' W (Q.map f y) (P.map f x))
    (hswap : ∀ V x y, μ' V y x = μ V x y) {p q n : ℕ} (h : p + q = n)
    (α : ((cechComplexFunctor U).obj P).homology p)
    (β : ((cechComplexFunctor U).obj Q).homology q) :
    cechCup U μ' hμ' q p n (by omega) β α =
      (-1 : ℤ) ^ (p * q) • cechCup U μ hμ p q n h α β := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  have hrev (K : Cᵒᵖ ⥤ ModuleCat.{u'} R) (m : ℕ) (z : ((cechComplexFunctor U).obj K).cycles m) :
      ((cechComplexFunctor U).obj K).homologyπ m
          (HomologicalComplex.cyclesMap ((cechOrderReversal U).app K) m z) =
        ((cechComplexFunctor U).obj K).homologyπ m z := by
    rw [← HomologicalComplex.moduleCat_homologyMap_homologyπ, homologyMap_cechOrderReversal]
    rfl
  conv_lhs => rw [← hrev Q q b, ← hrev P p a, cechCup_homologyπ, ← hrev S n]
  rw [cechCup_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, map_zsmul, iCycles_cechCupCycles]
  exact cechOrderReversal_cechCupCochain U μ μ' hμ' hswap h _ _

/-- **Twice an odd cup square vanishes** on fixed-family Čech cohomology for a symmetric pairing. -/
theorem two_smul_cechCup_self_eq_zero_of_odd
    {μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V}
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (P.map f y))
    (hsym : ∀ V x y, μ V y x = μ V x y) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (α : ((cechComplexFunctor U).obj P).homology p) :
    (2 : R) • cechCup U μ hμ p p n h α α = 0 := by
  have hcomm := cechCup_gradedComm U μ hμ μ hμ hsym h α α
  rw [(hp.mul hp).neg_one_pow, neg_one_smul] at hcomm
  rw [two_smul]
  nth_rw 1 [hcomm]
  exact neg_add_cancel _

/-- **Cup squares of odd classes vanish** on fixed-family Čech cohomology when `2` is invertible. -/
theorem cechCup_self_eq_zero_of_odd [Invertible (2 : R)]
    {μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V}
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (P.map f y))
    (hsym : ∀ V x y, μ V y x = μ V x y) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (α : ((cechComplexFunctor U).obj P).homology p) :
    cechCup U μ hμ p p n h α α = 0 := by
  rw [← one_smul R (cechCup U μ hμ p p n h α α), ← invOf_mul_self (2 : R), mul_smul,
    two_smul_cechCup_self_eq_zero_of_odd U hμ hsym hp h α, smul_zero]

/-- Morphisms of presheaves compatible with bilinear pairings preserve the fixed-family Čech cup
product on cohomology. -/
theorem cechCup_homologyMap_cechComplexFunctor_map {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ' : ∀ V : Cᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ' : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S'.map f (μ' V x y) = μ' W (P'.map f x) (Q'.map f y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' V (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    cechCup U μ' hμ' p q n h
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) p x)
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map β) q y) =
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map γ) n
        (cechCup U μ hμ p q n h x y) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechCup_homologyπ, cechCup_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles]
  exact cechComplexFunctor_map_cechCupCochain U μ μ' α β γ hγ p q n h _ _

/-- Product-preserving functors preserve the fixed-family Čech cup product on cohomology through
`cechComplexCompIso`. -/
theorem cechCup_homologyMap_cechComplexCompIso_hom {D : Type u''} [Category.{v''} D]
    [HasFiniteProducts D] (G : C ⥤ D)
    (hG : ∀ (m : ℕ) (a : Fin (m + 1) → ι), IsIso (piComparison G fun j ↦ U (a j)))
    {P' Q' S' : Dᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ' : ∀ V : Dᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ' : ∀ ⦃V W : Dᵒᵖ⦄ (f : V ⟶ W) x y, S'.map f (μ' V x y) = μ' W (P'.map f x) (Q'.map f y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj P').homology p)
    (y : ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q').homology q) :
    cechCup U (fun V ↦ μ' (op (G.obj (unop V))))
        (fun _ _ f x y ↦ hμ' (G.map f.unop).op x y) p q n h
        (HomologicalComplex.homologyMap (cechComplexCompIso G U P' hG).hom p x)
        (HomologicalComplex.homologyMap (cechComplexCompIso G U Q' hG).hom q y) =
      HomologicalComplex.homologyMap (cechComplexCompIso G U S' hG).hom n
        (cechCup (fun i ↦ G.obj (U i)) μ' hμ' p q n h x y) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechCup_homologyπ, cechCup_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles]
  exact cechComplexCompIso_hom_cechCupCochain U G hG μ' hμ' p q n h _ _

/-- Left unitality of the fixed-family Čech cup product for a global section acting as left unit. -/
theorem cechCup_left_unit_augmentation {T : C} (hT : IsTerminal T)
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] Q.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, Q.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (e : P.obj (op T)) (he : ∀ (V : Cᵒᵖ) (y : Q.obj V), μ V (P.map (hT.from (unop V)).op e) y = y)
    (q : ℕ) (β : ((cechComplexFunctor U).obj Q).homology q) :
    cechCup U μ hμ 0 q q (Nat.zero_add q)
        (HomologicalComplex.homologyMap (cechAugmentation U hT P) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (P.obj (op T))).inv e))
        β = β := by
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [← homologyπ_augmentation_apply, cechCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, iCycles_augmentation_apply]
  refine cechCupCochain_left_unit U μ q _ (fun k y ↦ ?_) _
  refine (congrArg (fun z ↦ μ (op (∏ᶜ fun j ↦ U (k j)))
    (P.map (Pi.lift fun _ : Fin 1 ↦ Pi.π (fun j ↦ U (k j)) 0).op z) y)
    (π_cechAugmentation_apply U hT P e (fun _ ↦ k 0))).trans ?_
  rw [← ModuleCat.comp_apply, ← P.map_comp, ← op_comp, hT.hom_ext (_ ≫ hT.from _) (hT.from _)]
  exact he (op (∏ᶜ fun j ↦ U (k j))) y

/-- Right unitality of the fixed-family Čech cup product for a global section acting as right
unit. -/
theorem cechCup_right_unit_augmentation {T : C} (hT : IsTerminal T)
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] P.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, P.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (e : Q.obj (op T)) (he : ∀ (V : Cᵒᵖ) (x : P.obj V), μ V x (Q.map (hT.from (unop V)).op e) = x)
    (p : ℕ) (α : ((cechComplexFunctor U).obj P).homology p) :
    cechCup U μ hμ p 0 p (Nat.add_zero p) α
        (HomologicalComplex.homologyMap (cechAugmentation U hT Q) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (Q.obj (op T))).inv e)) = α := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  rw [← homologyπ_augmentation_apply, cechCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, iCycles_augmentation_apply]
  refine cechCupCochain_right_unit U μ p _ (fun k x ↦ ?_) _
  refine (congrArg (fun z ↦ μ (op (∏ᶜ fun j ↦ U (k j))) x
    (Q.map (Pi.lift fun _ : Fin 1 ↦ Pi.π (fun j ↦ U (k j)) (Fin.last p)).op z))
    (π_cechAugmentation_apply U hT Q e (fun _ ↦ k (Fin.last p)))).trans ?_
  rw [← ModuleCat.comp_apply, ← Q.map_comp, ← op_comp, hT.hom_ext (_ ≫ hT.from _) (hT.from _)]
  exact he (op (∏ᶜ fun j ↦ U (k j))) x

/-- In degree `0`, `cechCup` agrees with `μ (op T)` under the augmentations. -/
theorem cechCup_zero_zero_augmentation {T : C} (hT : IsTerminal T)
    (s : P.obj (op T)) (t : Q.obj (op T)) :
    cechCup U μ hμ 0 0 0 rfl
        (HomologicalComplex.homologyMap (cechAugmentation U hT P) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (P.obj (op T))).inv s))
        (HomologicalComplex.homologyMap (cechAugmentation U hT Q) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (Q.obj (op T))).inv t)) =
      HomologicalComplex.homologyMap (cechAugmentation U hT S) 0
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (S.obj (op T))).inv
          (μ (op T) s t)) := by
  rw [← homologyπ_augmentation_apply, ← homologyπ_augmentation_apply,
    ← homologyπ_augmentation_apply, cechCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, iCycles_augmentation_apply, iCycles_augmentation_apply,
    iCycles_augmentation_apply]
  refine cechX_ext U S 0 fun k ↦ ?_
  rw [π_cechCupCochain_reproj, π_cechAugmentation_apply, π_cechAugmentation_apply,
    π_cechAugmentation_apply, hμ, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← P.map_comp,
    ← Q.map_comp, ← op_comp, ← op_comp, hT.hom_ext (_ ≫ hT.from _) (hT.from _),
    hT.hom_ext (_ ≫ hT.from _) (hT.from _)]

end FixedCohomology

section FixedCohomologyRefinement

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [CommRing R] [HasProducts.{w} (ModuleCat.{u'} R)]
  {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}

/-- Refinement maps preserve the fixed-family Čech cup product on cohomology. -/
theorem cechCup_cechComplexHomologyMap {ι κ : Type w} {U : ι → C} {V : κ → C}
    (μ : ∀ W : Cᵒᵖ, P.obj W →ₗ[R] Q.obj W →ₗ[R] S.obj W)
    (hμ : ∀ ⦃W W' : Cᵒᵖ⦄ (f : W ⟶ W') x y, S.map f (μ W x y) = μ W' (P.map f x) (Q.map f y))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (p q n : ℕ) (h : p + q = n)
    (α : ((cechComplexFunctor V).obj P).homology p)
    (β : ((cechComplexFunctor V).obj Q).homology q) :
    cechCup U μ hμ p q n h
        (HomologicalComplex.homologyMap (cechComplexMap P φ) p α)
        (HomologicalComplex.homologyMap (cechComplexMap Q φ) q β) =
      HomologicalComplex.homologyMap (cechComplexMap S φ) n (cechCup V μ hμ p q n h α β) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, cechCup_homologyπ, cechCup_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cechCupCycles, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cechCupCycles]
  exact cechComplexMap_cechCupCochain μ hμ φ p q n h _ _

end FixedCohomologyRefinement

end TauCeti.CategoryTheory
