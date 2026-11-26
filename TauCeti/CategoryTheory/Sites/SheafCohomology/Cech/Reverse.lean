/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.ModuleCat
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv
import TauCeti.Data.Fin.Rev
import TauCeti.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# The order-reversing operator on Čech cochains

Let `C` be a category with finite products, `U : ι → C` a family of objects and `P : Cᵒᵖ ⥤ A` a
presheaf with values in a preadditive category with products. The **order-reversing operator**
`τ = cechReverse A U` acts on Mathlib's Čech complex `Č(U, P)` by reading each cochain backwards:
for a cochain `c` of degree `n`,

`(τ c)(k 0, …, k n) = (-1) ^ (n (n + 1) / 2) c(k n, …, k 0)`,

restricted along the isomorphism `U (k 0) × ⋯ × U (k n) ⟶ U (k n) × ⋯ × U (k 0)`
(`cechReverse_app_f_π`). The sign is that of the permutation reversing `n + 1` vertices, written
`(-1) ^ (n + 1).choose 2`; with it `τ` commutes with the Čech differential, so it is a map of
complexes, natural in the presheaf. It is an involution (`cechReverse_comp_cechReverse`) and
commutes with the maps induced by morphisms of families, such as refinements of open covers
(`cechComplexMap_comp_cechReverse_app`).

For a family in a thin category, for instance a family of open subsets of a topological space,
`τ` is homotopic to the identity (`cechReverseHomotopy`), so it induces the identity on Čech
cohomology (`homologyMap_cechReverse_app`) and fixes the class of every cocycle of a presheaf of
modules (`homologyπ_moduleCatCyclesMk_cechReverse`). The homotopy comes from the ordered Čech
complex: after choosing a well-ordering of `ι`, every cochain is homotopic to its alternation
(`strictMonoCechComplexHomotopyEquiv`), and alternating cochains are fixed by `τ`, because the
inversion signs of a tuple and of its reversal differ by the sign of the reversal
(`fromStrictMonoCechComplex_comp_cechReverse`).

The operator is the tool by which the cup product of Čech cochains becomes graded commutative on
cohomology. The cup product `cechCup` multiplies the front face of one cochain with the back face
of the other, so it is not graded commutative on cochains, but reversing the vertices exchanges
front and back faces: for a presheaf of commutative algebras,
`τ (τ b ⌣ τ a) = (-1) ^ (p q) a ⌣ b` for cochains `a` of degree `p` and `b` of degree `q`
(`cechReverse_cechCup_cechReverse`). For cocycles `a` and `b` in a thin category, this identity
and the homotopy `τ ≃ 1` are the two ingredients showing that `b ⌣ a` and `(-1) ^ (p q) a ⌣ b`
are cohomologous.

## Main definitions

* `TauCeti.CategoryTheory.cechReverse A U`: the order-reversing operator, a natural endomorphism
  of the Čech complex functor `cechComplexFunctor U`.
* `TauCeti.CategoryTheory.cechReverseHomotopy U P`: for a family in a thin category, a homotopy
  from the order-reversing operator to the identity.

## Main results

* `TauCeti.CategoryTheory.cechReverse_app_f_π`: the factors of `τ c`.
* `TauCeti.CategoryTheory.cechReverse_comp_cechReverse`: `τ` is an involution.
* `TauCeti.CategoryTheory.cechComplexMap_comp_cechReverse_app`: compatibility with refinements.
* `TauCeti.CategoryTheory.homologyMap_cechReverse_app`: in a thin category, `τ` is the identity on
  cohomology.
* `TauCeti.CategoryTheory.homologyπ_moduleCatCyclesMk_cechReverse`: in a thin category, a cocycle
  of a presheaf of modules and its reversal have the same class.
* `TauCeti.CategoryTheory.cechComplexπ_cechReverse`: the factors of `τ c` for a presheaf of
  modules.
* `TauCeti.CategoryTheory.cechComponent_cechReverse`, `TauCeti.CategoryTheory.cechFace_cechReverse`:
  the factors and restrictions of `τ c` for a presheaf of algebras.
* `TauCeti.CategoryTheory.cechReverse_cechCupCochain` and
  `TauCeti.CategoryTheory.cechReverse_cechCup_cechReverse`: `τ (τ b ⌣ τ a) = (-1) ^ (p q) a ⌣ b`
  for general pairings and presheaves of commutative algebras.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the cup product on
  Čech complexes, the order-reversing operator and the graded commutativity of the cup product on
  cohomology. The homotopy to the identity is obtained here from the alternating Čech complex.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v v' u u' u''

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)

/-! ### The operator -/

section Reverse

variable (P : Cᵒᵖ ⥤ A)

/-- The factor of a Čech `m`-cochain indexed by `k ∘ σ`, restricted along the projection
`U (k 0) × ⋯ × U (k n) ⟶ U (k (σ 0)) × ⋯ × U (k (σ m))`. -/
private def restrict {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1)) :
    ((cechComplexFunctor U).obj P).X m ⟶ P.obj (op (∏ᶜ fun j ↦ U (k j))) :=
  cechComplexπ U P m (k ∘ σ) ≫ P.map (Pi.map' σ (fun _ ↦ 𝟙 _)).op

/-- Restricting a restriction is restricting along the composite map of vertices. -/
private lemma restrict_comp_map {l m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1))
    (τ : Fin (l + 1) → Fin (m + 1)) :
    restrict U P (k ∘ σ) τ ≫ P.map (Pi.map' σ (fun _ ↦ 𝟙 _)).op =
      restrict U P k (σ ∘ τ) := by
  rw [restrict, restrict, Category.assoc, ← P.map_comp, ← op_comp, Pi.map'_comp_map']
  simp only [Function.comp_def, Category.id_comp]

private lemma d_comp_restrict {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 2) → Fin (n + 1)) :
    ((cechComplexFunctor U).obj P).d m (m + 1) ≫ restrict U P k σ =
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • restrict U P k (σ ∘ j.succAbove) := by
  rw [restrict, reassoc_of% cechComplexFunctor_obj_d_comp_cechComplexπ, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Preadditive.zsmul_comp]
  congr 1
  simpa only [restrict, Pi.map', Category.comp_id] using restrict_comp_map U P k σ j.succAbove

/-- The degree `n` component of the order-reversing operator. -/
private def reverseX (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶ ((cechComplexFunctor U).obj P).X n :=
  Pi.lift fun k ↦ (-1 : ℤ) ^ (n + 1).choose 2 • restrict U P k Fin.rev

private lemma reverseX_comp_cechComplexπ (n : ℕ) (k : Fin (n + 1) → ι) :
    reverseX U P n ≫ cechComplexπ U P n k =
      (-1 : ℤ) ^ (n + 1).choose 2 • restrict U P k Fin.rev := by
  rw [cechComplexπ_eq]
  exact Pi.lift_comp_π _ k

private lemma reverseX_comp_restrict {m n : ℕ} (k : Fin (n + 1) → ι)
    (σ : Fin (m + 1) → Fin (n + 1)) :
    reverseX U P m ≫ restrict U P k σ =
      (-1 : ℤ) ^ (m + 1).choose 2 • restrict U P k (σ ∘ Fin.rev) := by
  rw [restrict, reassoc_of% reverseX_comp_cechComplexπ, Preadditive.zsmul_comp, restrict_comp_map]

private lemma reverseX_comm (n : ℕ) :
    reverseX U P n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor U).obj P).d n (n + 1) ≫ reverseX U P (n + 1) := by
  refine cechComplex_hom_ext U P fun k ↦ ?_
  rw [Category.assoc, Category.assoc, reverseX_comp_cechComplexπ,
    cechComplexFunctor_obj_d_comp_cechComplexπ, Preadditive.comp_sum, Preadditive.comp_zsmul,
    d_comp_restrict, Finset.smul_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hσ : j.rev.succAbove ∘ Fin.rev = Fin.rev ∘ j.succAbove :=
    funext fun x ↦ (Fin.rev_succAbove j x).symm
  have hrestr :
      cechComplexπ U P n (k ∘ (Fin.revPerm j).succAbove) ≫
          P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) ((Fin.revPerm j).succAbove x)).op =
        restrict U P k (Fin.revPerm j).succAbove := by
    simp only [restrict, Pi.map', Category.comp_id]
  rw [Preadditive.comp_zsmul, hrestr, reverseX_comp_restrict, Fin.revPerm_apply, hσ, smul_smul,
    smul_smul, Fin.neg_one_pow_val_rev_mul]

private lemma restrict_id {n : ℕ} (k : Fin (n + 1) → ι) :
    restrict U P k id = cechComplexπ U P n k := by
  simp [restrict]

private lemma map_f_comp_restrict {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) {m n : ℕ} (k : Fin (n + 1) → ι)
    (σ : Fin (m + 1) → Fin (n + 1)) :
    ((cechComplexFunctor U).map α).f m ≫ restrict U Q k σ =
      restrict U P k σ ≫ α.app (op (∏ᶜ fun j ↦ U (k j))) := by
  rw [restrict, restrict, reassoc_of% cechComplexFunctor_map_f_comp_cechComplexπ, ← α.naturality,
    Category.assoc]

private lemma reverseX_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((cechComplexFunctor U).map α).f n ≫ reverseX U Q n =
      reverseX U P n ≫ ((cechComplexFunctor U).map α).f n := by
  refine cechComplex_hom_ext U Q fun k ↦ ?_
  rw [Category.assoc, Category.assoc, reverseX_comp_cechComplexπ, Preadditive.comp_zsmul,
    map_f_comp_restrict, cechComplexFunctor_map_f_comp_cechComplexπ,
    reassoc_of% reverseX_comp_cechComplexπ, Preadditive.zsmul_comp]

private lemma cechComplexMap_f_comp_restrict {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) {m n : ℕ} (k : Fin (n + 1) → ι)
    (σ : Fin (m + 1) → Fin (n + 1)) :
    (cechComplexMap P φ).f m ≫ restrict U P k σ =
      restrict V P (φ.f ∘ k) σ ≫ P.map (Limits.Pi.map fun j ↦ φ.φ (k j)).op := by
  have h : Pi.map' σ (fun _ ↦ 𝟙 _) ≫ Limits.Pi.map (fun j ↦ φ.φ ((k ∘ σ) j)) =
      Limits.Pi.map (fun j ↦ φ.φ (k j)) ≫ Pi.map' σ (fun _ ↦ 𝟙 _) :=
    Pi.hom_ext _ _ fun _ ↦ by simp
  rw [restrict, restrict, reassoc_of% cechComplexMap_f_comp_cechComplexπ, ← P.map_comp,
    Category.assoc, ← P.map_comp, ← op_comp, ← op_comp, h]
  -- the tuples `φ.f ∘ k ∘ σ` and `(φ.f ∘ k) ∘ σ` are the same function
  rfl

end Reverse

variable (A) in
/-- The **order-reversing operator** `τ` on Čech cochains: its factor at a tuple
`k = (k 0, …, k n)` of a cochain `c` of degree `n` is `(-1) ^ (n (n + 1) / 2)` times the factor of
`c` at the reversed tuple `(k n, …, k 0)`, restricted along the isomorphism
`U (k 0) × ⋯ × U (k n) ⟶ U (k n) × ⋯ × U (k 0)` (`cechReverse_app_f_π`). The sign
`(-1) ^ (n (n + 1) / 2)` is written `(-1) ^ (n + 1).choose 2`; it is the sign of the reversal of
`n + 1` vertices, and it makes `τ` commute with the Čech differential, so `τ` is a map of
complexes, natural in the presheaf. It is an involution (`cechReverse_comp_cechReverse`) and
commutes with the maps induced by morphisms of families (`cechComplexMap_comp_cechReverse_app`).
For a family in a thin category, such as a family of open subsets of a topological space, it is
homotopic to the identity (`cechReverseHomotopy`). -/
def cechReverse : cechComplexFunctor (A := A) U ⟶ cechComplexFunctor U where
  app P :=
    { f := reverseX U P
      comm' := by
        rintro i _ rfl
        exact reverseX_comm U P i }
  naturality P Q α := by
    ext n : 1
    exact reverseX_naturality U P α n

private lemma cechReverse_app_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechReverse A U).app P).f n = reverseX U P n :=
  rfl

/-- The factor of `τ c` at `k = (k 0, …, k n)` is `(-1) ^ (n (n + 1) / 2)` times the factor of `c`
at `(k n, …, k 0)`, restricted along `U (k 0) × ⋯ × U (k n) ⟶ U (k n) × ⋯ × U (k 0)`. -/
@[reassoc]
theorem cechReverse_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (k : Fin (n + 1) → ι) :
    ((cechReverse A U).app P).f n ≫ Pi.π _ k =
      (-1 : ℤ) ^ (n + 1).choose 2 • (Pi.π _ (k ∘ Fin.rev) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (Fin.rev x)).op) := by
  have h : ((cechReverse A U).app P).f n ≫ cechComplexπ U P n k =
      (-1 : ℤ) ^ (n + 1).choose 2 • (cechComplexπ U P n (k ∘ Fin.rev) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (Fin.rev x)).op) := by
    simpa only [cechReverse_app_f, restrict, Pi.map', Category.comp_id] using
      reverseX_comp_cechComplexπ U P n k
  simp only [cechComplexπ_eq] at h
  exact h

/-- The order-reversing operator is an involution. -/
@[reassoc (attr := simp)]
theorem cechReverse_comp_cechReverse : cechReverse A U ≫ cechReverse A U = 𝟙 _ := by
  ext P n : 3
  refine cechComplex_hom_ext U P fun k ↦ ?_
  simp only [NatTrans.comp_app, NatTrans.id_app, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, Category.assoc, cechReverse_app_f, reverseX_comp_cechComplexπ,
    Preadditive.comp_zsmul, reverseX_comp_restrict, Fin.rev_involutive.comp_self, restrict_id,
    Category.id_comp]
  simp [smul_smul, ← mul_pow]

/-- The order-reversing operator on the Čech complex of a presheaf is an involution. -/
@[reassoc (attr := simp)]
theorem cechReverse_app_comp_cechReverse_app (P : Cᵒᵖ ⥤ A) :
    (cechReverse A U).app P ≫ (cechReverse A U).app P = 𝟙 _ := by
  rw [← NatTrans.comp_app, cechReverse_comp_cechReverse, NatTrans.id_app]

/-- **Compatibility with refinements.** The order-reversing operator commutes with the map of Čech
complexes `Č(V, P) ⟶ Č(U, P)` induced by a morphism of families `φ : U ⟶ V`, such as a refinement
of open covers. -/
@[reassoc]
theorem cechComplexMap_comp_cechReverse_app {κ : Type w} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ A) :
    cechComplexMap P φ ≫ (cechReverse A U).app P =
      (cechReverse A V).app P ≫ cechComplexMap P φ := by
  ext n : 1
  refine cechComplex_hom_ext U P fun k ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    cechReverse_app_f, cechReverse_app_f, reverseX_comp_cechComplexπ, Preadditive.comp_zsmul,
    cechComplexMap_f_comp_restrict, cechComplexMap_f_comp_cechComplexπ,
    reassoc_of% reverseX_comp_cechComplexπ, Preadditive.zsmul_comp]

/-! ### Homotopy to the identity -/

section Thin

variable [Quiver.IsThin C]

section LinearOrder

variable [LinearOrder ι]

private lemma fromStrictMono_f_comp_cechComplexπ (P : Cᵒᵖ ⥤ A) {n : ℕ} {k : Fin (n + 1) → ι}
    (hk : Function.Injective k) :
    ((fromStrictMonoCechComplex U).app P).f n ≫ cechComplexπ U P n k =
      (-1 : ℤ) ^ #(univ.inversions k) •
        (strictMonoCechComplexπ U P ⟨k ∘ Tuple.sort k, Tuple.strictMono_comp_sort hk⟩ ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ U (k j)) (Tuple.sort k j)).op) := by
  simp only [cechComplexπ_eq]
  exact fromStrictMonoCechComplex_app_f_π U P n hk

private lemma fromStrictMono_f_comp_cechComplexπ_of_not_injective (P : Cᵒᵖ ⥤ A) {n : ℕ}
    {k : Fin (n + 1) → ι} (hk : ¬Function.Injective k) :
    ((fromStrictMonoCechComplex U).app P).f n ≫ cechComplexπ U P n k = 0 := by
  simp only [cechComplexπ_eq]
  exact fromStrictMonoCechComplex_app_f_π_of_not_injective U P n hk

/-- The alternating extension of an ordered cochain is fixed by the order-reversing operator. -/
@[reassoc (attr := simp)]
theorem fromStrictMonoCechComplex_comp_cechReverse :
    fromStrictMonoCechComplex (A := A) U ≫ cechReverse A U = fromStrictMonoCechComplex U := by
  ext P n : 3
  refine cechComplex_hom_ext U P fun k ↦ ?_
  rw [NatTrans.comp_app, HomologicalComplex.comp_f, Category.assoc, cechReverse_app_f,
    reverseX_comp_cechComplexπ, Preadditive.comp_zsmul, restrict]
  by_cases hk : Function.Injective k
  · have hk' : Function.Injective (k ∘ Fin.rev) := hk.comp Fin.rev_injective
    rw [reassoc_of% fromStrictMono_f_comp_cechComplexπ U P hk',
      fromStrictMono_f_comp_cechComplexπ U P hk, Preadditive.zsmul_comp, smul_smul,
      neg_one_pow_card_univ_inversions_comp_rev hk, Category.assoc, ← P.map_comp, ← op_comp]
    congr 1
    simp only [Pi.map', Category.comp_id]
    exact strictMonoCechComplexπ_comp_map_eq U P
      (Subtype.ext (Tuple.comp_sort_eq_comp_sort_of_range_eq hk' (Fin.rev_surjective.range_comp k)))
      _ _
  · have hk' : ¬Function.Injective (k ∘ Fin.rev) := fun h ↦
      hk (by simpa [Function.comp_assoc] using h.comp Fin.rev_injective)
    rw [reassoc_of% fromStrictMono_f_comp_cechComplexπ_of_not_injective U P hk',
      fromStrictMono_f_comp_cechComplexπ_of_not_injective U P hk, zero_comp, smul_zero]

end LinearOrder

/-- **The order-reversing operator is homotopic to the identity**, for a family in a thin
category, such as a family of open subsets of a topological space. The homotopy is obtained by
choosing a well-ordering of the index type: the alternating cochains for this order are fixed by
the operator (`fromStrictMonoCechComplex_comp_cechReverse`), and every cochain is homotopic to its
alternation (`strictMonoCechComplexHomotopyEquiv`). -/
def cechReverseHomotopy (P : Cᵒᵖ ⥤ A) : Homotopy ((cechReverse A U).app P) (𝟙 _) :=
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  let e := strictMonoCechComplexHomotopyEquiv U P
  (Homotopy.ofEq (Category.id_comp _).symm).trans <|
    (e.homotopyHomInvId.symm.compRight _).trans <|
      (Homotopy.ofEq (by
        rw [Category.assoc, strictMonoCechComplexHomotopyEquiv_hom,
          strictMonoCechComplexHomotopyEquiv_inv, ← NatTrans.comp_app,
          fromStrictMonoCechComplex_comp_cechReverse])).trans e.homotopyHomInvId

/-- For a family in a thin category the order-reversing operator induces the identity on Čech
cohomology. -/
@[simp]
theorem homologyMap_cechReverse_app [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechReverse A U).app P) n = 𝟙 _ := by
  rw [(cechReverseHomotopy U P).homologyMap_eq, HomologicalComplex.homologyMap_id]

/-- **The order-reversing operator fixes classes.** For a family in a thin category and a presheaf
of `R`-modules, the reversal `τ c` of a Čech cocycle `c` has the same class as `c`. -/
@[simp]
theorem homologyπ_moduleCatCyclesMk_cechReverse {R : Type u''} [Ring R]
    {P : Cᵒᵖ ⥤ ModuleCat.{w} R} {p : ℕ} (c : ((cechComplexFunctor U).obj P).X p) (m : ℕ)
    (hm : (ComplexShape.up ℕ).next p = m) (hc : (((cechComplexFunctor U).obj P).d p m).hom c = 0) :
    (((cechComplexFunctor U).obj P).homologyπ p).hom
        (((cechComplexFunctor U).obj P).moduleCatCyclesMk
          ((((cechReverse (ModuleCat.{w} R) U).app P).f p).hom c) m hm
          (by rw [HomologicalComplex.Hom.comm_apply, hc, map_zero])) =
      (((cechComplexFunctor U).obj P).homologyπ p).hom
        (((cechComplexFunctor U).obj P).moduleCatCyclesMk c m hm hc) := by
  rw [← HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk, homologyMap_cechReverse_app,
    ModuleCat.id_apply]

end Thin

/-! ### The cup product -/

section Cup

variable {R : Type u''} [CommRing R] {F : Cᵒᵖ ⥤ AlgCat.{w} R}

/-- The factor of `τ a` at `c = (c 0, …, c n)` for a presheaf of `R`-modules is
`(-1) ^ (n (n + 1) / 2)` times the factor of `a` at `c ∘ Fin.rev`, restricted along the reversal
of coordinates. -/
@[simp]
theorem cechComplexπ_cechReverse (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c (((cechReverse (ModuleCat.{w} R) U).app P).f n a) =
      (-1 : ℤ) ^ (n + 1).choose 2 •
        P.map (Pi.map' (Fin.rev : Fin (n + 1) → Fin (n + 1)) (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U P n (c ∘ Fin.rev) a) := by
  have hm : ((cechReverse (ModuleCat.{w} R) U).app P).f n ≫ cechComplexπ U P n c =
      (-1 : ℤ) ^ (n + 1).choose 2 • (cechComplexπ U P n (c ∘ Fin.rev) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (c j)) (Fin.rev x)).op) := by
    simp only [cechComplexπ_eq]
    exact cechReverse_app_f_π U P n c
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply, Pi.map',
    Category.comp_id] using ConcreteCategory.congr_hom hm a

/-- **Reversal identity for the Čech cup product on cochains.** Reversing a cup product of
reversed cochains recovers the cup product in the opposite order with the Koszul sign
`(-1) ^ (p * q)`. -/
theorem cechReverse_cechCupCochain
    {P Q S : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (μ : ∀ X : Cᵒᵖ, P.obj X →ₗ[R] Q.obj X →ₗ[R] S.obj X)
    (μ' : ∀ X : Cᵒᵖ, Q.obj X →ₗ[R] P.obj X →ₗ[R] S.obj X)
    (hμ' : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) y x, μ' Y (Q.map f y) (P.map f x) = S.map f (μ' X y x))
    (hcomm : ∀ X x y, μ' X y x = μ X x y)
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    ((cechReverse (ModuleCat.{w} R) U).app S).f n
        (cechCupCochain U μ' q p n (by omega)
          (((cechReverse (ModuleCat.{w} R) U).app Q).f q b)
          (((cechReverse (ModuleCat.{w} R) U).app P).f p a)) =
      (-1 : ℤ) ^ (p * q) • cechCupCochain U μ p q n h a b := by
  subst h
  refine cechComplex_ext fun c ↦ ?_
  rw [cechComplexπ_cechReverse, map_zsmul, cechCupCochain_π, cechCupCochain_π]
  dsimp only [Function.comp_def]
  rw [← hμ', cechComplexπ_cechReverse, cechComplexπ_cechReverse]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm ((-1 : ℤ) ^ (p + 1).choose 2), Nat.neg_one_pow_add_add_one_choose_two_mul, hcomm]
  refine congrArg ((-1 : ℤ) ^ (p * q) • ·) (congrArg₂ (fun x y ↦ μ _ x y) ?_ ?_)
  · dsimp only [Function.comp_def]
    rw [cechComplexπ_map_piMap'_comp U P (fun i ↦ c i.rev)]
    dsimp only [Function.comp_def]
    rw [cechComplexπ_map_piMap'_comp U P c]
    exact cechComplexπ_map_piMap'_eq_of_val U P c (fun i ↦ by simp [Fin.val_rev]; omega) a
  · dsimp only [Function.comp_def]
    rw [cechComplexπ_map_piMap'_comp U Q (fun i ↦ c i.rev)]
    dsimp only [Function.comp_def]
    rw [cechComplexπ_map_piMap'_comp U Q c]
    exact cechComplexπ_map_piMap'_eq_of_val U Q c (fun i ↦ by simp [Fin.val_rev]; omega) b

/-- The factors of `τ c` for a cochain `c` of a presheaf of algebras: the factor at
`k = (k 0, …, k n)` is `(-1) ^ (n (n + 1) / 2)` times the restriction of `c` along the reversal of
the vertices. -/
@[simp]
theorem cechComponent_cechReverse {n : ℕ} (k : Fin (n + 1) → ι)
    (c : (cechAlgebraComplex U F).X n) :
    cechComponent k ((((cechReverse (ModuleCat.{w} R) U).app
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f n).hom c) =
      (-1 : ℤ) ^ (n + 1).choose 2 • cechFace k Fin.rev c := by
  rw [cechComponent_eq_sum_of_comp_π_eq (s := {()}) (z := fun _ ↦ (-1) ^ (n + 1).choose 2)
    (σ := fun _ ↦ Fin.rev) (by rw [Finset.sum_singleton]; exact cechReverse_app_f_π U _ n k),
    Finset.sum_singleton]

/-- The restrictions of `τ c` along a map `σ` of vertices are the restrictions of `c` along
`σ ∘ Fin.rev`, times the sign `(-1) ^ (m (m + 1) / 2)` of the reversal of `m + 1` vertices. -/
@[simp]
theorem cechFace_cechReverse {m n : ℕ} (k : Fin (n + 1) → ι) (σ : Fin (m + 1) → Fin (n + 1))
    (c : (cechAlgebraComplex U F).X m) :
    cechFace k σ ((((cechReverse (ModuleCat.{w} R) U).app
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f m).hom c) =
      (-1 : ℤ) ^ (m + 1).choose 2 • cechFace k (σ ∘ Fin.rev) c := by
  rw [cechFace_apply, cechComponent_cechReverse, map_zsmul, map_cechFace]

/-- **The order-reversing operator reverses cup products.** For a presheaf of commutative
algebras, `τ (τ b ⌣ τ a) = (-1) ^ (p q) a ⌣ b` for Čech cochains `a` of degree `p` and `b` of
degree `q`. The cup product itself is not graded commutative on cochains; this identity, together
with the homotopy `τ ≃ 1` of `cechReverseHomotopy` for a family in a thin category, is what makes
it graded commutative on Čech cohomology. -/
theorem cechReverse_cechCup_cechReverse (hF : ∀ X (x y : F.obj X), x * y = y * x) {p q n : ℕ}
    (h : p + q = n) (a : (cechAlgebraComplex U F).X p) (b : (cechAlgebraComplex U F).X q) :
    (((cechReverse (ModuleCat.{w} R) U).app
      (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f n).hom
        (cechCup q p n (by omega)
          ((((cechReverse (ModuleCat.{w} R) U).app
            (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f q).hom b)
          ((((cechReverse (ModuleCat.{w} R) U).app
            (F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))).f p).hom a)) =
    (-1 : ℤ) ^ (p * q) • cechCup p q n h a b := by
  rw [cechCup_eq_cechCupCochain, cechCup_eq_cechCupCochain]
  exact cechReverse_cechCupCochain U
    (P := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (Q := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (S := F ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))
    (fun X ↦ LinearMap.mul R (F.obj X)) (fun X ↦ LinearMap.mul R (F.obj X))
    (cechAlgebraMul_naturality F)
    (fun X (x y : F.obj X) ↦ hF X y x) p q n h a b

end Cup

end TauCeti.CategoryTheory
