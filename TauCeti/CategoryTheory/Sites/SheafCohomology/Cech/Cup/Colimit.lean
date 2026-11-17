/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic

/-!
# The Čech cup product on directed-colimit cohomology

Given a directed system of families `E : J → FormalCoproduct C` and a natural `R`-bilinear pairing
`μ : ∀ V, P(V) →ₗ[R] Q(V) →ₗ[R] S(V)` of presheaves of `R`-modules, the fixed-family cup products
`cechCup` are compatible with refinement maps (`cechCup_cechComplexHomologyMap`). Passing to the
colimit over `J` yields a unique `R`-bilinear pairing
`cechCohomologyCup : Hᵖ(E, P) →ₗ[R] H^q(E, Q) →ₗ[R] Hⁿ(E, S)` for `p + q = n` satisfying
`cechCohomologyCup_cechCohomologyι`.

This file establishes associativity, graded commutativity, odd-degree square vanishing, naturality
in presheaf morphisms, left and right unitality on global sections, and degree-`0` compatibility
with `cechCohomologyZeroIso`.

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyCup`: the cup product on directed-colimit Čech cohomology.

## Main results

* `TauCeti.CategoryTheory.cechCohomologyCup_cechCohomologyι`: compatibility with structure maps.
* `TauCeti.CategoryTheory.cechCohomologyCup_assoc`: associativity.
* `TauCeti.CategoryTheory.cechCohomologyCup_gradedComm`: graded commutativity.
* `TauCeti.CategoryTheory.two_smul_cechCohomologyCup_self_eq_zero_of_odd`,
  `TauCeti.CategoryTheory.cechCohomologyCup_self_eq_zero_of_odd`: odd-degree square vanishing.
* `TauCeti.CategoryTheory.cechCohomologyCup_map`: naturality in morphisms of presheaves.
* `TauCeti.CategoryTheory.cechCohomologyCup_left_unit`,
  `TauCeti.CategoryTheory.cechCohomologyCup_right_unit`: left and right unitality.
* `TauCeti.CategoryTheory.cechCohomologyCup_zero_zero_cechCohomologyZeroIso`: in degree `0`, the
  cup product agrees with `μ(T)` under `cechCohomologyZeroIso`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w t uR v u u'

namespace TauCeti.CategoryTheory

section ColimitCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {R : Type uR} [CommRing R] [HasProducts.{w} (ModuleCat.{u'} R)]
  {J : Type t} [Preorder J] [IsDirectedOrder J]
  (E : J → FormalCoproduct.{w} C) (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i))
  [HasColimitsOfShape J (ModuleCat.{u'} R)]

omit [IsDirectedOrder J] in
private lemma cechCohomologyι_eq_of_le {P : Cᵒᵖ ⥤ ModuleCat.{u'} R} (p : ℕ) {i k : J} (hik : i ≤ k)
    (φ : E k ⟶ E i) (x : ((cechComplexFunctor (E i).obj).obj P).homology p) :
    (cechCohomologyι E hE p i).app P x =
      (cechCohomologyι E hE p k).app P (homologyMap (cechComplexMap P φ) p x) := by
  have h : (cechComplexHomologyMap (ModuleCat.{u'} R) p φ).app P ≫
      (cechCohomologyι E hE p k).app P = (cechCohomologyι E hE p i).app P :=
    NatTrans.congr_app
      (cechComplexHomologyMap_comp_cechCohomologyι (ModuleCat.{u'} R) E hE p hik φ) P
  rw [cechComplexHomologyMap_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

omit [IsDirectedOrder J] in
private lemma cechCohomology_linear_ext {P : Cᵒᵖ ⥤ ModuleCat.{u'} R} {p : ℕ}
    {Z : ModuleCat.{u'} R} {L₁ L₂ : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P →ₗ[R] Z}
    (h : ∀ (j : J) (x : ((cechComplexFunctor (E j).obj).obj P).homology p),
      L₁ ((cechCohomologyι E hE p j).app P x) = L₂ ((cechCohomologyι E hE p j).app P x))
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P) : L₁ α = L₂ α :=
  ConcreteCategory.congr_hom (cechCohomology_obj_hom_ext fun j ↦ by ext x; exact h j x) α

/-- Two `R`-bilinear maps on directed-colimit Čech cohomology agree once they agree on all pairs
coming from the same family `E k`. -/
theorem cechCohomology_bilinear_ext {P Q : Cᵒᵖ ⥤ ModuleCat.{u'} R} {p q : ℕ}
    {Z : ModuleCat.{u'} R}
    {B₁ B₂ : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R] Z}
    (h : ∀ (k : J) (x : ((cechComplexFunctor (E k).obj).obj P).homology p)
      (y : ((cechComplexFunctor (E k).obj).obj Q).homology q),
      B₁ ((cechCohomologyι E hE p k).app P x) ((cechCohomologyι E hE q k).app Q y) =
      B₂ ((cechCohomologyι E hE p k).app P x) ((cechCohomologyι E hE q k).app Q y))
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P)
    (β : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q) : B₁ α β = B₂ α β := by
  have h1 : ∀ (i : J) (x : ((cechComplexFunctor (E i).obj).obj P).homology p),
      B₁ ((cechCohomologyι E hE p i).app P x) = B₂ ((cechCohomologyι E hE p i).app P x) :=
    fun i x ↦ LinearMap.ext <| cechCohomology_linear_ext E hE fun j y ↦ by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [cechCohomologyι_eq_of_le E hE p hik (hE hik).some x,
        cechCohomologyι_eq_of_le E hE q hjk (hE hjk).some y]
      exact h k _ _
  exact LinearMap.congr_fun
    (cechCohomology_linear_ext E hE
      (Z := ModuleCat.of R ((cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R] Z)) h1 α) β

private lemma cechCohomology_trilinear_ext {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R} {p q r : ℕ}
    {Z : ModuleCat.{u'} R}
    {T₁ T₂ : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R]
      (cechCohomology (ModuleCat.{u'} R) E hE r).obj S →ₗ[R] Z}
    (h : ∀ (k : J) (x : ((cechComplexFunctor (E k).obj).obj P).homology p)
      (y : ((cechComplexFunctor (E k).obj).obj Q).homology q)
      (z : ((cechComplexFunctor (E k).obj).obj S).homology r),
      T₁ ((cechCohomologyι E hE p k).app P x) ((cechCohomologyι E hE q k).app Q y)
        ((cechCohomologyι E hE r k).app S z) =
      T₂ ((cechCohomologyι E hE p k).app P x) ((cechCohomologyι E hE q k).app Q y)
        ((cechCohomologyι E hE r k).app S z))
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P)
    (β : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q)
    (γ : (cechCohomology (ModuleCat.{u'} R) E hE r).obj S) : T₁ α β γ = T₂ α β γ := by
  have h1 : ∀ (i : J) (x : ((cechComplexFunctor (E i).obj).obj P).homology p),
      T₁ ((cechCohomologyι E hE p i).app P x) = T₂ ((cechCohomologyι E hE p i).app P x) :=
    fun i x ↦ LinearMap.ext fun β' ↦ LinearMap.ext <|
      cechCohomology_bilinear_ext E hE
        (B₁ := T₁ ((cechCohomologyι E hE p i).app P x))
        (B₂ := T₂ ((cechCohomologyι E hE p i).app P x)) (fun j y z ↦ by
          obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
          rw [cechCohomologyι_eq_of_le E hE p hik (hE hik).some x,
            cechCohomologyι_eq_of_le E hE q hjk (hE hjk).some y,
            cechCohomologyι_eq_of_le E hE r hjk (hE hjk).some z]
          exact h k _ _ _) β'
  exact LinearMap.congr_fun (LinearMap.congr_fun
    (cechCohomology_linear_ext E hE
      (Z := ModuleCat.of R ((cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE r).obj S →ₗ[R] Z)) h1 α) β) γ

omit [IsDirectedOrder J] in
private lemma cechCohomologyι_augmentation_eq {T : C} (hT : IsTerminal T)
    (K : Cᵒᵖ ⥤ ModuleCat.{u'} R) {j₀ k : J} (hj₀k : j₀ ≤ k) (e : K.obj (op T)) :
    (cechCohomologyι E hE 0 j₀).app K
        (homologyMap (cechAugmentation (E j₀).obj hT K) 0
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (K.obj (op T))).inv e)) =
      (cechCohomologyι E hE 0 k).app K
        (homologyMap (cechAugmentation (E k).obj hT K) 0
          ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (K.obj (op T))).inv e)) := by
  rw [cechCohomologyι_eq_of_le E hE 0 hj₀k (hE hj₀k).some, ← ConcreteCategory.comp_apply,
    ← homologyMap_comp, cechAugmentation_comp_cechComplexMap]

section Construction

variable {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}
  (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
  (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
  (p q n : ℕ) (h : p + q = n)

/-- Fixed-index bilinear pairing into the target colimit. -/
private def cupColimitDiag (k : J) :
    ((cechComplexFunctor (E k).obj).obj P).homology p →ₗ[R]
      ((cechComplexFunctor (E k).obj).obj Q).homology q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE n).obj S :=
  let ι : ((cechComplexFunctor (E k).obj).obj S).homology n →ₗ[R]
      (cechCohomology (ModuleCat.{u'} R) E hE n).obj S := ((cechCohomologyι E hE n k).app S).hom
  (cechCup (E k).obj μ hμ p q n h).compr₂ ι

omit [IsDirectedOrder J] in
private lemma cupColimitDiag_map {i k : J} (hik : i ≤ k) (φ : E k ⟶ E i)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E i).obj).obj Q).homology q) :
    cupColimitDiag E hE μ hμ p q n h k
        (homologyMap (cechComplexMap P φ) p x) (homologyMap (cechComplexMap Q φ) q y) =
      cupColimitDiag E hE μ hμ p q n h i x y :=
  (congrArg ((cechCohomologyι E hE n k).app S)
      (cechCup_cechComplexHomologyMap μ hμ φ p q n h x y)).trans
    (cechCohomologyι_eq_of_le E hE n hik φ _).symm

/-- Two-index pairing obtained by pushing both arguments to a common upper bound in `J`. -/
private def cupColimitPair (i j : J) :
    ((cechComplexFunctor (E i).obj).obj P).homology p →ₗ[R]
      ((cechComplexFunctor (E j).obj).obj Q).homology q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE n).obj S :=
  let k := (exists_ge_ge i j).choose
  let φ₁ : E k ⟶ E i := (hE (exists_ge_ge i j).choose_spec.1).some
  let φ₂ : E k ⟶ E j := (hE (exists_ge_ge i j).choose_spec.2).some
  ((cupColimitDiag E hE μ hμ p q n h k).compl₂ (homologyMap (cechComplexMap Q φ₂) q).hom).comp
    (homologyMap (cechComplexMap P φ₁) p).hom

private lemma cupColimitPair_eq {i j k : J} (φ₁ : E k ⟶ E i) (φ₂ : E k ⟶ E j)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cupColimitPair E hE μ hμ p q n h i j x y =
      cupColimitDiag E hE μ hμ p q n h k
        (homologyMap (cechComplexMap P φ₁) p x) (homologyMap (cechComplexMap Q φ₂) q y) := by
  let k₀ := (exists_ge_ge i j).choose
  let ψ₁ : E k₀ ⟶ E i := (hE (exists_ge_ge i j).choose_spec.1).some
  let ψ₂ : E k₀ ⟶ E j := (hE (exists_ge_ge i j).choose_spec.2).some
  obtain ⟨m, hk₀m, hkm⟩ := exists_ge_ge k₀ k
  have h1 := cupColimitDiag_map E hE μ hμ p q n h hk₀m (hE hk₀m).some
    (homologyMap (cechComplexMap P ψ₁) p x) (homologyMap (cechComplexMap Q ψ₂) q y)
  have h2 := cupColimitDiag_map E hE μ hμ p q n h hkm (hE hkm).some
    (homologyMap (cechComplexMap P φ₁) p x) (homologyMap (cechComplexMap Q φ₂) q y)
  have hcomp {K : Cᵒᵖ ⥤ ModuleCat.{u'} R} {r : ℕ} {i' : J}
      (f₁ : E k₀ ⟶ E i') (f₂ : E k ⟶ E i')
      (z : ((cechComplexFunctor (E i').obj).obj K).homology r) :
      homologyMap (cechComplexMap K (hE hk₀m).some) r (homologyMap (cechComplexMap K f₁) r z) =
        homologyMap (cechComplexMap K (hE hkm).some) r (homologyMap (cechComplexMap K f₂) r z) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← homologyMap_comp,
      ← homologyMap_comp, ← cechComplexMap_comp, ← cechComplexMap_comp]
    have hEq := NatTrans.congr_app
      (cechComplexHomologyMap_eq (ModuleCat.{u'} R) r ((hE hk₀m).some ≫ f₁) ((hE hkm).some ≫ f₂)) K
    rw [cechComplexHomologyMap_app, cechComplexHomologyMap_app] at hEq
    exact ConcreteCategory.congr_hom hEq z
  rw [hcomp ψ₁ φ₁ x, hcomp ψ₂ φ₂ y] at h1
  exact h1.symm.trans h2

private lemma cupColimitPair_self (i : J)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E i).obj).obj Q).homology q) :
    cupColimitPair E hE μ hμ p q n h i i x y = cupColimitDiag E hE μ hμ p q n h i x y := by
  rw [cupColimitPair_eq E hE μ hμ p q n h (𝟙 _) (𝟙 _), cechComplexMap_id (U := (E i).obj) P,
    cechComplexMap_id (U := (E i).obj) Q, homologyMap_id, homologyMap_id]; rfl

private lemma cupColimitPair_map_right {i j j' : J} (φ : E j' ⟶ E j)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cupColimitPair E hE μ hμ p q n h i j' x (homologyMap (cechComplexMap Q φ) q y) =
      cupColimitPair E hE μ hμ p q n h i j x y := by
  obtain ⟨k, hik, hj'k⟩ := exists_ge_ge i j'
  rw [cupColimitPair_eq E hE μ hμ p q n h (hE hik).some (hE hj'k).some,
    cupColimitPair_eq E hE μ hμ p q n h (hE hik).some ((hE hj'k).some ≫ φ),
    ← ConcreteCategory.comp_apply, ← homologyMap_comp, ← cechComplexMap_comp]

private lemma cupColimitPair_map_left {i i' j : J} (φ : E i' ⟶ E i)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cupColimitPair E hE μ hμ p q n h i' j (homologyMap (cechComplexMap P φ) p x) y =
      cupColimitPair E hE μ hμ p q n h i j x y := by
  obtain ⟨k, hi'k, hjk⟩ := exists_ge_ge i' j
  rw [cupColimitPair_eq E hE μ hμ p q n h (hE hi'k).some (hE hjk).some,
    cupColimitPair_eq E hE μ hμ p q n h ((hE hi'k).some ≫ φ) (hE hjk).some,
    ← ConcreteCategory.comp_apply, ← homologyMap_comp, ← cechComplexMap_comp]

/-- Descent in the second variable via `cechCohomologyDesc`. -/
private def cupColimitStep1 (i : J) (x : ((cechComplexFunctor (E i).obj).obj P).homology p) :
    (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q ⟶
      (cechCohomology (ModuleCat.{u'} R) E hE n).obj S :=
  cechCohomologyDesc E hE q (fun j ↦ ModuleCat.ofHom (cupColimitPair E hE μ hμ p q n h i j x))
    fun _ _ _ φ ↦ by ext y; exact cupColimitPair_map_right E hE μ hμ p q n h φ x y

private lemma cupColimitStep1_ι (i j : J)
    (x : ((cechComplexFunctor (E i).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    (cupColimitStep1 E hE μ hμ p q n h i x).hom ((cechCohomologyι E hE q j).app Q y) =
      cupColimitPair E hE μ hμ p q n h i j x y :=
  ConcreteCategory.congr_hom (cechCohomologyι_app_cechCohomologyDesc E hE q _ _ j) y

private def cupColimitStep1Linear (i : J) :
    ((cechComplexFunctor (E i).obj).obj P).homology p ⟶
      ModuleCat.of R ((cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE n).obj S) :=
  let f : ((cechComplexFunctor (E i).obj).obj P).homology p →ₗ[R]
      ((cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE n).obj S) :=
    { toFun x := (cupColimitStep1 E hE μ hμ p q n h i x).hom
      map_add' x x' :=
        LinearMap.ext <| cechCohomology_linear_ext E hE fun j y ↦ by simp [cupColimitStep1_ι]
      map_smul' r x :=
        LinearMap.ext <| cechCohomology_linear_ext E hE fun j y ↦ by simp [cupColimitStep1_ι] }
  ModuleCat.ofHom f

private lemma cupColimitStep1Linear_compat ⦃i i' : J⦄ (φ : E i' ⟶ E i) :
    homologyMap (cechComplexMap P φ) p ≫ cupColimitStep1Linear E hE μ hμ p q n h i' =
      cupColimitStep1Linear E hE μ hμ p q n h i := by
  ext x : 2
  exact LinearMap.ext <| cechCohomology_linear_ext E hE fun j y ↦
    (cupColimitStep1_ι E hE μ hμ p q n h _ j _ y).trans <|
      (cupColimitPair_map_left E hE μ hμ p q n h φ x y).trans
        (cupColimitStep1_ι E hE μ hμ p q n h _ j x y).symm

/-- **The Čech cup product on directed-colimit Čech cohomology.** For a directed system of
families `E : J → FormalCoproduct C`, a natural `R`-bilinear pairing
`μ : ∀ V, P(V) →ₗ[R] Q(V) →ₗ[R] S(V)`, and degrees `p + q = n`, this is the unique `R`-bilinear map
`Hᵖ(E, P) × H^q(E, Q) ⟶ Hⁿ(E, S)` compatible with the fixed-family cup products `cechCup` along
the colimit structure maps (`cechCohomologyCup_cechCohomologyι`). -/
def cechCohomologyCup :
    (cechCohomology (ModuleCat.{u'} R) E hE p).obj P →ₗ[R]
      (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q →ₗ[R]
        (cechCohomology (ModuleCat.{u'} R) E hE n).obj S :=
  (cechCohomologyDesc E hE p (cupColimitStep1Linear E hE μ hμ p q n h)
    (fun _ _ _ φ ↦ cupColimitStep1Linear_compat E hE μ hμ p q n h φ)).hom

/-- On classes coming from the same family `E j`, `cechCohomologyCup` is the fixed-family cup
product `cechCup` followed by the structure map. -/
@[simp]
theorem cechCohomologyCup_cechCohomologyι (j : J)
    (x : ((cechComplexFunctor (E j).obj).obj P).homology p)
    (y : ((cechComplexFunctor (E j).obj).obj Q).homology q) :
    cechCohomologyCup E hE μ hμ p q n h
        ((cechCohomologyι E hE p j).app P x) ((cechCohomologyι E hE q j).app Q y) =
      (cechCohomologyι E hE n j).app S (cechCup (E j).obj μ hμ p q n h x y) :=
  (LinearMap.congr_fun
    (ConcreteCategory.congr_hom (cechCohomologyι_app_cechCohomologyDesc E hE p _ _ j) x) _).trans <|
    (cupColimitStep1_ι E hE μ hμ p q n h j j x y).trans <|
      cupColimitPair_self E hE μ hμ p q n h j x y

end Construction

/-! ### Algebraic properties of `cechCohomologyCup` -/

variable {P Q S : Cᵒᵖ ⥤ ModuleCat.{u'} R}

/-- **Associativity of the directed-colimit Čech cup product.** -/
theorem cechCohomologyCup_assoc {T₁₂ T₂₃ T : Cᵒᵖ ⥤ ModuleCat.{u'} R}
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
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P)
    (β : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q)
    (γ : (cechCohomology (ModuleCat.{u'} R) E hE r).obj S) :
    cechCohomologyCup E hE μ₁₂₃ hμ₁₂₃ pq r n h₂
        (cechCohomologyCup E hE μ₁₂ hμ₁₂ p q pq h₁ α β) γ =
      cechCohomologyCup E hE μ₁_₂₃ hμ₁_₂₃ p qr n h₄ α
        (cechCohomologyCup E hE μ₂₃ hμ₂₃ q r qr h₃ β γ) :=
  cechCohomology_trilinear_ext E hE
    (T₁ := (cechCohomologyCup E hE μ₁₂ hμ₁₂ p q pq h₁).compr₂
      (cechCohomologyCup E hE μ₁₂₃ hμ₁₂₃ pq r n h₂))
    (T₂ := ((LinearMap.llcomp R _ _ _).comp
      (cechCohomologyCup E hE μ₁_₂₃ hμ₁_₂₃ p qr n h₄)).compl₂
      (cechCohomologyCup E hE μ₂₃ hμ₂₃ q r qr h₃))
    (fun k x y z ↦ by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.llcomp_apply, cechCohomologyCup_cechCohomologyι]
      rw [cechCup_assoc (E k).obj μ₁₂ hμ₁₂ μ₁₂₃ hμ₁₂₃ μ₂₃ hμ₂₃ μ₁_₂₃ hμ₁_₂₃ hassoc h₁ h₂ h₃ h₄])
    α β γ

/-- **Graded commutativity of the directed-colimit Čech cup product**:
`β ⌣_{μ'} α = (-1)^(p * q) • (α ⌣_μ β)` whenever `μ' V y x = μ V x y`. -/
theorem cechCohomologyCup_gradedComm
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (μ' : ∀ V : Cᵒᵖ, Q.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V)
    (hμ' : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) y x, S.map f (μ' V y x) = μ' W (Q.map f y) (P.map f x))
    (hswap : ∀ V x y, μ' V y x = μ V x y) {p q n : ℕ} (h : p + q = n)
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P)
    (β : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q) :
    cechCohomologyCup E hE μ' hμ' q p n (by omega) β α =
      (-1 : ℤ) ^ (p * q) • cechCohomologyCup E hE μ hμ p q n h α β :=
  cechCohomology_bilinear_ext E hE
    (B₁ := (cechCohomologyCup E hE μ' hμ' q p n (by omega)).flip)
    (B₂ := (-1 : ℤ) ^ (p * q) • cechCohomologyCup E hE μ hμ p q n h)
    (fun k x y ↦ by
      simp only [LinearMap.flip_apply, LinearMap.smul_apply, cechCohomologyCup_cechCohomologyι]
      exact (congrArg ((cechCohomologyι E hE n k).app S)
          (cechCup_gradedComm (E k).obj μ hμ μ' hμ' hswap h x y)).trans
        (map_zsmul ((cechCohomologyι E hE n k).app S).hom _ _)) α β

/-- **Twice an odd cup square vanishes** on directed-colimit Čech cohomology. -/
theorem two_smul_cechCohomologyCup_self_eq_zero_of_odd
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (P.map f y))
    (hsym : ∀ V x y, μ V y x = μ V x y) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P) :
    (2 : R) • cechCohomologyCup E hE μ hμ p p n h α α = 0 := by
  have hcomm := cechCohomologyCup_gradedComm E hE μ hμ μ hμ hsym h α α
  rw [(hp.mul hp).neg_one_pow, neg_one_smul] at hcomm
  rw [two_smul]; nth_rw 1 [hcomm]; exact neg_add_cancel _

/-- **Cup squares of odd classes vanish** on directed-colimit Čech cohomology when `2` is
invertible. -/
theorem cechCohomologyCup_self_eq_zero_of_odd [Invertible (2 : R)]
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] P.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (P.map f y))
    (hsym : ∀ V x y, μ V y x = μ V x y) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P) :
    cechCohomologyCup E hE μ hμ p p n h α α = 0 := by
  rw [← one_smul R (cechCohomologyCup E hE μ hμ p p n h α α), ← invOf_mul_self (2 : R),
    mul_smul, two_smul_cechCohomologyCup_self_eq_zero_of_odd E hE μ hμ hsym hp h α, smul_zero]

/-- Morphisms of presheaves compatible with bilinear pairings preserve `cechCohomologyCup`. -/
theorem cechCohomologyCup_map {P' Q' S' : Cᵒᵖ ⥤ ModuleCat.{u'} R}
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (μ' : ∀ V : Cᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ' : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S'.map f (μ' V x y) = μ' W (P'.map f x) (Q'.map f y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' V (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P)
    (y : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q) :
    cechCohomologyCup E hE μ' hμ' p q n h
        ((cechCohomology (ModuleCat.{u'} R) E hE p).map α x)
        ((cechCohomology (ModuleCat.{u'} R) E hE q).map β y) =
      (cechCohomology (ModuleCat.{u'} R) E hE n).map γ
        (cechCohomologyCup E hE μ hμ p q n h x y) :=
  cechCohomology_bilinear_ext E hE
    (B₁ := ((cechCohomologyCup E hE μ' hμ' p q n h).compl₂
      ((cechCohomology (ModuleCat.{u'} R) E hE q).map β).hom).comp
      ((cechCohomology (ModuleCat.{u'} R) E hE p).map α).hom)
    (B₂ := (cechCohomologyCup E hE μ hμ p q n h).compr₂
      ((cechCohomology (ModuleCat.{u'} R) E hE n).map γ).hom)
    (fun k a b ↦ by
      have hnat (K L : Cᵒᵖ ⥤ ModuleCat.{u'} R) (η : K ⟶ L) (m : ℕ)
          (z : ((cechComplexFunctor (E k).obj).obj K).homology m) :
          (cechCohomology (ModuleCat.{u'} R) E hE m).map η ((cechCohomologyι E hE m k).app K z) =
            (cechCohomologyι E hE m k).app L
              (homologyMap ((cechComplexFunctor (E k).obj).map η) m z) :=
        (ConcreteCategory.congr_hom ((cechCohomologyι E hE m k).naturality η) z).symm
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.compr₂_apply,
        cechCohomologyCup_cechCohomologyι]
      rw [hnat P P' α p a, hnat Q Q' β q b, hnat S S' γ n, cechCohomologyCup_cechCohomologyι,
        cechCup_homologyMap_cechComplexFunctor_map (E k).obj μ hμ μ' hμ' α β γ hγ]) x y

/-- Left unitality of `cechCohomologyCup` for a global section acting as left unit. -/
theorem cechCohomologyCup_left_unit {T : C} (hT : IsTerminal T)
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] Q.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, Q.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (e : P.obj (op T)) (he : ∀ (V : Cᵒᵖ) (y : Q.obj V), μ V (P.map (hT.from (unop V)).op e) y = y)
    (j₀ : J) (q : ℕ) (β : (cechCohomology (ModuleCat.{u'} R) E hE q).obj Q) :
    cechCohomologyCup E hE μ hμ 0 q q (Nat.zero_add q)
        ((cechCohomologyι E hE 0 j₀).app P
          (homologyMap (cechAugmentation (E j₀).obj hT P) 0
            ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e))) β = β := by
  refine cechCohomology_linear_ext E hE
    (L₁ := cechCohomologyCup E hE μ hμ 0 q q (Nat.zero_add q) _)
    (L₂ := LinearMap.id) (fun j y ↦ ?_) β
  obtain ⟨k, hj₀k, hjk⟩ := exists_ge_ge j₀ j
  rw [LinearMap.id_apply, cechCohomologyι_augmentation_eq E hE hT P hj₀k e,
    cechCohomologyι_eq_of_le E hE q hjk (hE hjk).some y,
    cechCohomologyCup_cechCohomologyι, cechCup_left_unit_augmentation (E k).obj hT μ hμ e he q]

/-- Right unitality of `cechCohomologyCup` for a global section acting as right unit. -/
theorem cechCohomologyCup_right_unit {T : C} (hT : IsTerminal T)
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] P.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, P.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (e : Q.obj (op T)) (he : ∀ (V : Cᵒᵖ) (x : P.obj V), μ V x (Q.map (hT.from (unop V)).op e) = x)
    (j₀ : J) (p : ℕ) (α : (cechCohomology (ModuleCat.{u'} R) E hE p).obj P) :
    cechCohomologyCup E hE μ hμ p 0 p (Nat.add_zero p) α
        ((cechCohomologyι E hE 0 j₀).app Q
          (homologyMap (cechAugmentation (E j₀).obj hT Q) 0
            ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (Q.obj (op T))).inv e))) = α := by
  refine cechCohomology_linear_ext E hE
    (L₁ := (cechCohomologyCup E hE μ hμ p 0 p (Nat.add_zero p)).flip _)
    (L₂ := LinearMap.id) (fun j x ↦ ?_) α
  obtain ⟨k, hj₀k, hjk⟩ := exists_ge_ge j₀ j
  rw [LinearMap.flip_apply, LinearMap.id_apply, cechCohomologyι_augmentation_eq E hE hT Q hj₀k e,
    cechCohomologyι_eq_of_le E hE p hjk (hE hjk).some x,
    cechCohomologyCup_cechCohomologyι, cechCup_right_unit_augmentation (E k).obj hT μ hμ e he p]

/-- **Degree-`0` compatibility with `cechCohomologyZeroIso`**: when `P`, `Q`, and `S` satisfy the
sheaf condition for every family in the connected directed system `E`, the degree-`0` cup product
agrees with `μ (op T)` under `cechCohomologyZeroIso`. -/
theorem cechCohomologyCup_zero_zero_cechCohomologyZeroIso {T : C} (hT : IsTerminal T)
    [IsConnected J]
    (μ : ∀ V : Cᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (hμ : ∀ ⦃V W : Cᵒᵖ⦄ (f : V ⟶ W) x y, S.map f (μ V x y) = μ W (P.map f x) (Q.map f y))
    (hP : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT P) 0)
    (hQ : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT Q) 0)
    (hS : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT S) 0)
    (s : P.obj (op T)) (t : Q.obj (op T)) :
    cechCohomologyCup E hE μ hμ 0 0 0 rfl
        ((cechCohomologyZeroIso E hE hT P hP).hom s)
        ((cechCohomologyZeroIso E hE hT Q hQ).hom t) =
      (cechCohomologyZeroIso E hE hT S hS).hom (μ (op T) s t) := by
  obtain ⟨j⟩ : Nonempty J := inferInstance
  have hcomp {F : Cᵒᵖ ⥤ ModuleCat.{u'} R}
      (hF : ∀ j, QuasiIsoAt (cechAugmentation (E j).obj hT F) 0) (z : F.obj (op T)) :
      (cechCohomologyZeroIso E hE hT F hF).hom z =
        (cechCohomologyι E hE 0 j).app F (homologyMap (cechAugmentation (E j).obj hT F) 0
          ((singleObjHomologySelfIso _ 0 (F.obj (op T))).inv z)) :=
    by rw [cechCohomologyZeroIso_hom E hE hT F hF j]; rfl
  rw [hcomp hP s, hcomp hQ t, hcomp hS (μ (op T) s t), cechCohomologyCup_cechCohomologyι,
    cechCup_zero_zero_augmentation]

end ColimitCohomology

end TauCeti.CategoryTheory
