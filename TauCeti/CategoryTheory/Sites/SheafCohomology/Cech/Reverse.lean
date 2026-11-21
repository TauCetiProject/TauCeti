/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Order reversal on the Čech complex

For a family `U : ι → C` of objects in a category with finite products and a presheaf `P : Cᵒᵖ ⥤ A`
with values in a preadditive category with products, reversing the indices of every `(n + 1)`-tuple
with the Koszul sign `(-1) ^ (n * (n + 1) / 2)` defines an involutive automorphism
`TauCeti.CategoryTheory.cechReverse` of the Čech complex `Č(U, P)`. No thinness hypothesis on `C`
and no ordering on `ι` are needed.

This involution is chain homotopic to the identity (`TauCeti.CategoryTheory.cechReverseHomotopy`),
so it induces the identity on Čech cohomology
(`TauCeti.CategoryTheory.homologyMap_cechReverse_app`).
The homotopy is constructed universally in the free abelian groups on functions
`Fin (n + 1) → Fin (m + 1)` by an inductive cone formula, and then evaluated on `Č(U, P)`.
Together with the reversal identity for the Čech cup product, this yields graded commutativity of
the cup product on Čech cohomology.

## Main definitions

* `TauCeti.CategoryTheory.cechReverse U`: the signed tuple-reversal automorphism of
  `CategoryTheory.cechComplexFunctor U`, natural in the coefficient presheaf.
* `TauCeti.CategoryTheory.cechReverseHomotopy U P`: a chain homotopy from the identity of `Č(U, P)`
  to `(cechReverse U).app P`.

## Main results

* `TauCeti.CategoryTheory.cechReverse_app_f_π`: on the factor indexed by `a : Fin (n + 1) → ι`,
  reversal acts by `(-1) ^ (n * (n + 1) / 2)` times restriction from `a ∘ Fin.rev`.
* `TauCeti.CategoryTheory.cechReverse_comp_cechReverse`: reversal is an involution.
* `TauCeti.CategoryTheory.cechReverse_app_comp_cechComplexMap`: reversal commutes with maps induced
  by morphisms of families.
* `TauCeti.CategoryTheory.homologyMap_cechReverse_app`: reversal induces the identity on Čech
  cohomology in every degree.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP), for the cup product on Čech
  cochains and its graded commutativity via tuple reversal.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

namespace CechReverse

/-! ### Universal chains of index maps

Every natural operation on Čech cochains built from index reindexing and projections is obtained by
evaluating a `ℤ`-linear combination of maps `f : Fin (n + 1) → Fin (m + 1)`. The chain homotopy
between the identity and signed tuple reversal is built once in these universal free abelian groups
and then transferred to any Čech complex. -/

/-- The free abelian group on maps `Fin (n + 1) → Fin (m + 1)`. -/
private abbrev UChain (n m : ℕ) := (Fin (n + 1) → Fin (m + 1)) →₀ ℤ

/-- Precomposition with the alternating sum of coface maps `Fin.succAbove`: corresponds to
precomposition with the Čech differential `d n (n + 1)`. -/
private def bdry (n m : ℕ) : UChain (n + 1) m →ₗ[ℤ] UChain n m :=
  Finsupp.linearCombination ℤ fun f ↦
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (f ∘ j.succAbove) 1

/-- Postcomposition with the alternating sum of coface maps `Fin.succAbove`: corresponds to
postcomposition with the Čech differential `d m (m + 1)`. -/
private def codiff (n m : ℕ) : UChain n m →ₗ[ℤ] UChain n (m + 1) :=
  Finsupp.linearCombination ℤ fun f ↦
    ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single (k.succAbove ∘ f) 1

private lemma bdry_codiff (n m : ℕ) (x : UChain (n + 1) m) :
    bdry n (m + 1) (codiff (n + 1) m x) = codiff n m (bdry n m x) := by
  change ((bdry n (m + 1)).comp (codiff (n + 1) m)) x = ((codiff n m).comp (bdry n m)) x
  refine LinearMap.congr_fun (Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring ?_) x
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, bdry, codiff,
    Finsupp.linearCombination_single, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm, Function.comp_assoc]

private lemma succAbove_comp_succAbove {m : ℕ} {k : Fin (m + 3)} {j : Fin (m + 2)}
    (h : (k : ℕ) ≤ j) :
    k.succAbove ∘ j.succAbove = j.succ.succAbove ∘ (k.castLT (by omega)).succAbove :=
  (congrArg (fun φ ↦ ⇑(SimplexCategory.Hom.toOrderHom φ))
    (SimplexCategory.δ_comp_δ'' (i := k) (j := j) (Fin.le_def.2 h))).symm

private lemma codiff_codiff (n m : ℕ) (x : UChain n m) :
    codiff n (m + 1) (codiff n m x) = 0 := by
  change ((codiff n (m + 1)).comp (codiff n m)) x = (0 : UChain n m →ₗ[ℤ] UChain n (m + 2)) x
  refine LinearMap.congr_fun (Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring ?_) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.lsingle_apply, codiff,
    Finsupp.linearCombination_single, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    ← Finset.sum_product']
  let S : Finset (Fin (m + 2) × Fin (m + 3)) := {jk | (jk.2 : ℕ) ≤ jk.1}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, add_eq_zero_iff_eq_neg,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij'
    (fun jk h ↦ (jk.2.castLT (by have : (jk.2 : ℕ) ≤ jk.1 := (Finset.mem_filter.1 h).2; omega),
      jk.1.succ))
    (fun jk h ↦ (jk.2.pred fun h0 ↦ by simp [S, h0] at h, jk.1.castSucc))
    (fun jk h ↦ by simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, Fin.val_castLT, not_le] at h ⊢; omega)
    (fun jk h ↦ by simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, Fin.val_pred, not_le] at h ⊢; omega)
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp) fun ⟨j, k⟩ h ↦ ?_
  have h' : (k : ℕ) ≤ j := (Finset.mem_filter.1 h).2
  rw [← Function.comp_assoc, succAbove_comp_succAbove h', Function.comp_assoc, ← neg_smul,
    Fin.val_succ, Fin.val_castLT, pow_succ]
  congr 1; ring

/-- The universal reversal chain `(-1) ^ (m * (m + 1) / 2) • [Fin.rev]` in degree `m`. -/
private def revChain (m : ℕ) : UChain m m :=
  (-1 : ℤ) ^ (m * (m + 1) / 2) • Finsupp.single Fin.rev 1

private lemma bdry_id_eq_codiff_id (m : ℕ) :
    bdry m (m + 1) (Finsupp.single (id : Fin (m + 2) → Fin (m + 2)) 1) =
      codiff m m (Finsupp.single (id : Fin (m + 1) → Fin (m + 1)) 1) := by
  simp [bdry, codiff]

private lemma bdry_revChain (m : ℕ) :
    bdry m (m + 1) (revChain (m + 1)) = codiff m m (revChain m) := by
  simp only [revChain, map_zsmul, bdry, codiff, Finsupp.linearCombination_single,
    Finset.smul_sum, smul_smul, one_mul]
  refine Fintype.sum_equiv ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ _ _ fun j ↦ ?_
  have hcomp : Fin.rev ∘ j.succAbove = j.rev.succAbove ∘ Fin.rev := funext (Fin.rev_succAbove j)
  have hsign : (m + 1) * (m + 2) / 2 = m * (m + 1) / 2 + (m + 1) := by
    rw [show (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) by ring,
      Nat.add_mul_div_left _ _ (by omega)]
  dsimp only [Equiv.coe_fn_mk]
  rw [hcomp, hsign, ← pow_add, ← pow_add]
  congr 1
  have hrev : (j.rev : ℕ) = m + 1 - j := by simp [Fin.val_rev]
  have hle : (j : ℕ) ≤ m + 1 := Nat.le_of_lt_succ j.isLt
  rw [show m * (m + 1) / 2 + (m + 1) + (j : ℕ) =
      m * (m + 1) / 2 + (j.rev : ℕ) + 2 * (j : ℕ) by omega,
    pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- Prepending vertex `0 : Fin (m + 1)` to a map `Fin (n + 1) → Fin (m + 1)`. -/
private def cone₀ (n m : ℕ) : UChain n m →ₗ[ℤ] UChain (n + 1) m :=
  Finsupp.linearCombination ℤ fun f ↦ Finsupp.single (Fin.cons 0 f) 1

private lemma cons_comp_succAbove_succ {n m : ℕ} (f : Fin (n + 2) → Fin (m + 1))
    (j : Fin (n + 2)) :
    Fin.cons (0 : Fin (m + 1)) f ∘ j.succ.succAbove = Fin.cons 0 (f ∘ j.succAbove) := by
  funext x
  cases x using Fin.cases with
  | zero => simp [Fin.succAbove]
  | succ y =>
    simp only [Function.comp_apply, Fin.cons_succ, Fin.succAbove]
    by_cases h : y.castSucc < j <;> simp [h]

private lemma bdry_cone₀ (n m : ℕ) (x : UChain (n + 1) m) :
    bdry (n + 1) m (cone₀ (n + 1) m x) = x - cone₀ n m (bdry n m x) := by
  change ((bdry (n + 1) m).comp (cone₀ (n + 1) m)) x =
    (LinearMap.id (R := ℤ) (M := UChain (n + 1) m) - (cone₀ n m).comp (bdry n m)) x
  refine LinearMap.congr_fun (Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring ?_) x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, Finsupp.lsingle_apply,
    cone₀, bdry, Finsupp.linearCombination_single, one_smul, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [cons_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]

/-- The universal chain homotopy between the identity and `revChain`, defined inductively by coning
at vertex `0`. -/
private def homotopyChain : ∀ m : ℕ, UChain (m + 1) m
  | 0 => 0
  | m + 1 => cone₀ (m + 1) (m + 1)
      (Finsupp.single id 1 - revChain (m + 1) - codiff (m + 1) m (homotopyChain m))

private lemma homotopyChain_zero_spec :
    bdry 0 0 (homotopyChain 0) = Finsupp.single (id : Fin 1 → Fin 1) 1 - revChain 0 := by
  have hrev : (Fin.rev : Fin 1 → Fin 1) = id := funext fun _ ↦ Subsingleton.elim _ _
  simp [homotopyChain, revChain, hrev]

private lemma homotopyChain_spec (m : ℕ) :
    bdry (m + 1) (m + 1) (homotopyChain (m + 1)) + codiff (m + 1) m (homotopyChain m) =
      Finsupp.single (id : Fin (m + 2) → Fin (m + 2)) 1 - revChain (m + 1) := by
  induction m with
  | zero =>
    rw [homotopyChain.eq_2, bdry_cone₀, map_sub (bdry _ _), map_sub (bdry _ _),
      bdry_id_eq_codiff_id, bdry_revChain, bdry_codiff, homotopyChain_zero_spec,
      map_sub (codiff _ _), sub_self, map_zero, sub_zero, sub_add_cancel]
  | succ m ih =>
    rw [homotopyChain.eq_2, bdry_cone₀, map_sub (bdry _ _), map_sub (bdry _ _),
      bdry_id_eq_codiff_id, bdry_revChain, bdry_codiff, ← map_sub, ← map_sub, ← ih,
      add_sub_cancel_left, codiff_codiff, map_zero, sub_zero, sub_add_cancel]

/-! ### Evaluation on a Čech complex -/

section Eval

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The morphism `Čⁿ(U, P) ⟶ Čᵐ(U, P)` induced by an index map `f : Fin (n + 1) → Fin (m + 1)`. -/
private def elemMap {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) :
    ((cechComplexFunctor U).obj P).X n ⟶ ((cechComplexFunctor U).obj P).X m :=
  Pi.lift fun b : Fin (m + 1) → ι ↦
    Pi.π _ (b ∘ f) ≫ P.map (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (b j)) (f i)).op

@[reassoc]
private lemma elemMap_comp_π {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (b : Fin (m + 1) → ι) :
    elemMap U P f ≫ Pi.π _ b =
      Pi.π _ (b ∘ f) ≫ P.map (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (b j)) (f i)).op :=
  Pi.lift_comp_π _ _

private lemma elemMap_id (n : ℕ) :
    elemMap U P (id : Fin (n + 1) → Fin (n + 1)) = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun (b : Fin (n + 1) → ι) ↦ ?_
  have h : (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (b j)) i) = 𝟙 _ :=
    Pi.hom_ext _ _ fun i ↦ by simp
  exact (elemMap_comp_π U P id b).trans <|
    (_ ≫= (congrArg (fun f ↦ P.map f.op) h).trans (P.map_id _)).trans <|
    (Category.comp_id _).trans (Category.id_comp _).symm

private lemma elemMap_comp {n m k : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Fin (k + 1)) :
    elemMap U P f ≫ elemMap U P g = elemMap U P (g ∘ f) := by
  refine Pi.hom_ext _ _ fun (c : Fin (k + 1) → ι) ↦ ?_
  have h : (Pi.lift fun j : Fin (m + 1) ↦ Pi.π (fun l ↦ U (c l)) (g j)) ≫
      (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (c (g j))) (f i)) =
      Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun l ↦ U (c l)) (g (f i)) :=
    Pi.hom_ext _ _ fun i ↦ by simp
  exact (Category.assoc _ _ _).trans <| (_ ≫= elemMap_comp_π U P g c).trans <|
    (Category.assoc _ _ _).symm.trans <| (elemMap_comp_π U P f (c ∘ g) =≫ _).trans <|
    (Category.assoc _ _ _).trans <|
    (_ ≫= (P.map_comp _ _).symm.trans (congrArg (fun x ↦ P.map x.op) h)).trans
    (elemMap_comp_π U P (g ∘ f) c).symm

private lemma d_eq_sum_elemMap (n : ℕ) :
    ((cechComplexFunctor U).obj P).d n (n + 1) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • elemMap U P j.succAbove := by
  refine Pi.hom_ext _ _ fun b ↦ ?_
  refine (cechComplexFunctor_obj_d_comp_π U P n b).trans <|
    (Finset.sum_congr rfl fun j _ ↦ ?_).trans (Preadditive.sum_comp _ _ _).symm
  exact (congrArg _ (elemMap_comp_π U P j.succAbove b).symm).trans
    (Preadditive.zsmul_comp _ _ _).symm

/-- Evaluate a universal chain `x : UChain n m` as a morphism `Čⁿ(U, P) ⟶ Čᵐ(U, P)`. -/
private def evalUChain {n m : ℕ} :
    UChain n m →ₗ[ℤ] (((cechComplexFunctor U).obj P).X n ⟶ ((cechComplexFunctor U).obj P).X m) :=
  Finsupp.linearCombination ℤ (elemMap U P)

private lemma d_comp_evalUChain {n m : ℕ} (x : UChain (n + 1) m) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ evalUChain U P x =
      evalUChain U P (bdry n m x) := by
  change ((Preadditive.leftComp _ (((cechComplexFunctor U).obj P).d n (n + 1))).toIntLinearMap.comp
      (evalUChain U P)) x = ((evalUChain U P).comp (bdry n m)) x
  refine LinearMap.congr_fun (Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring ?_) x
  simp [evalUChain, bdry, d_eq_sum_elemMap, Preadditive.leftComp, Preadditive.sum_comp,
    elemMap_comp]

private lemma evalUChain_comp_d {n m : ℕ} (x : UChain n m) :
    evalUChain U P x ≫ ((cechComplexFunctor U).obj P).d m (m + 1) =
      evalUChain U P (codiff n m x) := by
  change ((Preadditive.rightComp _ (((cechComplexFunctor U).obj P).d m (m + 1))).toIntLinearMap.comp
      (evalUChain U P)) x = ((evalUChain U P).comp (codiff n m)) x
  refine LinearMap.congr_fun (Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring ?_) x
  simp [evalUChain, codiff, d_eq_sum_elemMap, Preadditive.rightComp, Preadditive.comp_sum,
    elemMap_comp]

private lemma elemMap_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) {n m : ℕ}
    (f : Fin (n + 1) → Fin (m + 1)) :
    ((cechComplexFunctor U).map α).f n ≫ elemMap U Q f =
      elemMap U P f ≫ ((cechComplexFunctor U).map α).f m :=
  Pi.hom_ext _ _ fun b ↦
    (Category.assoc _ _ _).trans <| (_ ≫= elemMap_comp_π U Q f b).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechComplexFunctor_map_f_π U P α n (b ∘ f) =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= (α.naturality _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| ((elemMap_comp_π U P f b).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= (cechComplexFunctor_map_f_π U P α m b).symm).trans
    (Category.assoc _ _ _).symm

private lemma elemMap_comp_cechComplexMap {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {n m : ℕ}
    (f : Fin (n + 1) → Fin (m + 1)) :
    elemMap V P f ≫ (cechComplexMap P φ).f m =
      (cechComplexMap P φ).f n ≫ elemMap U P f := by
  refine Pi.hom_ext _ _ fun (b : Fin (m + 1) → ι) ↦ ?_
  have h : (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (b j)) (f i)) ≫
      Limits.Pi.map (fun i : Fin (n + 1) ↦ φ.φ (b (f i))) =
      Limits.Pi.map (fun j : Fin (m + 1) ↦ φ.φ (b j)) ≫
        Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ V (φ.f (b j))) (f i) :=
    Pi.hom_ext _ _ fun i ↦ by simp
  have hmap : P.map (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ V (φ.f (b j))) (f i)).op ≫
      P.map (Limits.Pi.map fun j : Fin (m + 1) ↦ φ.φ (b j)).op =
      P.map (Limits.Pi.map fun i : Fin (n + 1) ↦ φ.φ (b (f i))).op ≫
        P.map (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (b j)) (f i)).op := by
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, h]
  exact (Category.assoc _ _ _).trans <| (_ ≫= cechComplexMap_f_π P φ m b).trans <|
    (Category.assoc _ _ _).symm.trans <| (elemMap_comp_π V P f (φ.f ∘ b) =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= hmap).trans <|
    (Category.assoc _ _ _).symm.trans <| ((cechComplexMap_f_π P φ n (b ∘ f)).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= (elemMap_comp_π U P f b).symm).trans
    (Category.assoc _ _ _).symm

end Eval

end CechReverse

/-! ### The reversal automorphism of the Čech complex -/

open CechReverse

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- The signed tuple-reversal endomorphism of the Čech complex `Č(U, P)`. -/
private def cechReverseApp (P : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor U).obj P where
  f n := evalUChain U P (revChain n)
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    rw [evalUChain_comp_d, d_comp_evalUChain, bdry_revChain]

/-- **Signed tuple reversal on the Čech complex.** In degree `n`, it reverses the tuple of indices
with the Koszul sign `(-1) ^ (n * (n + 1) / 2)`, naturally in the coefficient presheaf. -/
def cechReverse : cechComplexFunctor (A := A) U ⟶ cechComplexFunctor U where
  app := cechReverseApp U
  naturality P Q α := by
    ext n : 1
    simp [cechReverseApp, revChain, evalUChain, elemMap_naturality]

private lemma cechReverse_app_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechReverse U).app P).f n = (-1 : ℤ) ^ (n * (n + 1) / 2) • elemMap U P Fin.rev := by
  change evalUChain U P (revChain n) = _
  simp [evalUChain, revChain]

/-- On the factor indexed by `a : Fin (n + 1) → ι`, signed tuple reversal applies the sign
`(-1) ^ (n * (n + 1) / 2)` to the factor indexed by `a ∘ Fin.rev`, restricted along the coordinate
reversal isomorphism of products. -/
@[reassoc]
theorem cechReverse_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechReverse U).app P).f n ≫ Pi.π _ a =
      (-1 : ℤ) ^ (n * (n + 1) / 2) • (Pi.π _ (a ∘ Fin.rev) ≫
        P.map (Pi.lift fun i : Fin (n + 1) ↦ Pi.π (fun j ↦ U (a j)) i.rev).op) :=
  (cechReverse_app_f U P n =≫ _).trans <|
    (Preadditive.zsmul_comp _ _ _).trans (congrArg _ (elemMap_comp_π U P Fin.rev a))

/-- Signed tuple reversal on `Č(U, P)` is an involution. -/
@[reassoc (attr := simp)]
theorem cechReverse_app_comp_cechReverse_app (P : Cᵒᵖ ⥤ A) :
    (cechReverse U).app P ≫ (cechReverse U).app P = 𝟙 _ := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, cechReverse_app_f,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_smul, elemMap_comp]
  rw [show (Fin.rev : Fin (n + 1) → Fin (n + 1)) ∘ Fin.rev = id from funext Fin.rev_rev, elemMap_id]

/-- Signed tuple reversal is an involution on the Čech complex functor. -/
@[simp]
theorem cechReverse_comp_cechReverse :
    cechReverse (A := A) U ≫ cechReverse U = 𝟙 _ := by
  ext P : 2
  exact cechReverse_app_comp_cechReverse_app U P

/-- Signed tuple reversal commutes with the map of Čech complexes induced by any morphism of
families. -/
@[reassoc]
theorem cechReverse_app_comp_cechComplexMap {κ : Type w} {V : κ → C} (P : Cᵒᵖ ⥤ A)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechReverse V).app P ≫ cechComplexMap P φ =
      cechComplexMap P φ ≫ (cechReverse U).app P := by
  ext n : 1
  simp [cechReverse_app_f, elemMap_comp_cechComplexMap]

private def cechReverseHomotopyHom (P : Cᵒᵖ ⥤ A) (i j : ℕ) :
    ((cechComplexFunctor U).obj P).X i ⟶ ((cechComplexFunctor U).obj P).X j :=
  if h : j + 1 = i then
    eqToHom (congrArg ((cechComplexFunctor U).obj P).X h.symm) ≫
      evalUChain U P (homotopyChain j)
  else 0

/-- **Signed tuple reversal is chain homotopic to the identity.** The homotopy evaluates the
universal cone homotopy on `Č(U, P)`. -/
def cechReverseHomotopy (P : Cᵒᵖ ⥤ A) :
    Homotopy (𝟙 ((cechComplexFunctor U).obj P)) ((cechReverse U).app P) where
  hom := cechReverseHomotopyHom U P
  zero _ _ hji := dite_eq_right_iff.2 fun h ↦ absurd h hji
  comm i := by
    rw [dNext_eq _ (rfl : (ComplexShape.up ℕ).Rel i (i + 1))]
    simp only [cechReverseHomotopyHom, ↓reduceDIte, eqToHom_refl, Category.id_comp]
    cases i with
    | zero =>
      rw [prevD_nat, ((cechComplexFunctor U).obj P).shape 0 0 (by simp), comp_zero, add_zero,
        d_comp_evalUChain, homotopyChain_zero_spec, map_sub, evalUChain,
        Finsupp.linearCombination_single, one_smul, elemMap_id]
      exact (sub_add_cancel _ _).symm
    | succ m =>
      rw [prevD_nat, Nat.add_sub_cancel]
      simp only [cechReverseHomotopyHom, ↓reduceDIte, eqToHom_refl, Category.id_comp]
      rw [d_comp_evalUChain, evalUChain_comp_d, ← map_add, homotopyChain_spec, map_sub,
        evalUChain, Finsupp.linearCombination_single, one_smul, elemMap_id]
      exact (sub_add_cancel _ _).symm

/-- **Signed tuple reversal induces the identity on Čech cohomology.** -/
@[simp]
theorem homologyMap_cechReverse_app [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechReverse U).app P) n = 𝟙 _ :=
  ((cechReverseHomotopy U P).homologyMap_eq n).symm.trans (HomologicalComplex.homologyMap_id _ n)

end TauCeti.CategoryTheory
