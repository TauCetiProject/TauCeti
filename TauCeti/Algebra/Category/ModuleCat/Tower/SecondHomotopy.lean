/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Homotopy

/-!
# Second homotopies of maps of countable towers

Specified homotopies of transition squares induce maps of homotopy limits. Changing those
square homotopies need not preserve the induced map, but a compatible family of second
homotopies does give a homotopy of the induced maps.

We assemble degree-shifting maps from level `n + 1` to level `n` on the product complexes.
This assembly commutes with the Hom-complex differential. In degree `-2` it turns second
homotopies of the adjacent squares into a second homotopy of the product-difference square.
The native mapping-cocone construction then supplies the homotopy of homotopy-limit maps,
with its specified correction term and the resulting equality on homology.

The construction uses `ModuleTower.productComplexSquareHomotopy` and the native shifted-cone
second-homotopy API `CochainComplex.mappingCocone.mapOfHomotopyHomotopy`; no independence
from arbitrary choices of square homotopies is asserted.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
* The Stacks Project, More on Algebra, Tags 07KX and 0CQD.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite CochainComplex HomologicalComplex HomComplex

universe v u

variable {R : Type u} [Ring R]
  {K L : CochainComplex (ModuleTower.{v} R) ℤ}

local notation "ev" => fun n : ℕ ↦
  Functor.mapHomologicalComplex (Functor.obj (evaluation ℕᵒᵖ (ModuleCat R)) (op n))
    (ComplexShape.up ℤ)

local notation "tr" => fun n : ℕ ↦ NatTrans.mapHomologicalComplex
  (CategoryTheory.Functor.map (evaluation ℕᵒᵖ (ModuleCat R))
    (Quiver.Hom.op (homOfLE (Nat.le_succ n))))
  (ComplexShape.up ℤ)

/-- Assemble cochains from level `n + 1` to level `n` into a cochain on product complexes.
The output at level `n` uses only the input at level `n + 1`. -/
def productComplexTransitionCochain {a : ℤ}
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) a) :
    Cochain ((productComplexFunctor R).obj K) ((productComplexFunctor R).obj L) a :=
  Cochain.mk fun p q hpq ↦ ConcreteCategory.ofHom (C := ModuleCat R)
    (LinearMap.pi fun n ↦ ((s n).v p q hpq).hom.comp (LinearMap.proj (n + 1)))

@[simp↓]
lemma productComplexTransitionCochain_v_apply {a : ℤ}
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) a)
    (p q : ℤ) (hpq : p + a = q) (x : ((productComplexFunctor R).obj K).X p) (n : ℕ) :
    (productComplexTransitionCochain s).v p q hpq x n = (s n).v p q hpq (x (n + 1)) :=
  (rfl)

/-- Assembly of adjacent-level cochains commutes with the Hom-complex differential. -/
lemma δ_productComplexTransitionCochain {a b : ℤ} (hab : a + 1 = b)
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) a) :
    δ a b (productComplexTransitionCochain s) =
      productComplexTransitionCochain (fun n ↦ δ a b (s n)) := by
  apply Cochain.ext
  intro p q hpq
  rw [δ_v a b hab _ p q hpq (q - 1) (p + 1) rfl rfl]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  -- Fix the native product type so differential evaluation rewrites under linear maps.
  change (K.X p).Product at x
  have e := congrArg (fun g ↦ g.hom (x (n + 1)))
    (δ_v a b hab (s n) p q hpq (q - 1) (p + 1) rfl rfl)
  -- Name the evaluated linear maps on the native product carriers before adding coordinates.
  let S (i j : ℤ) (hij : i + a = j) (n : ℕ) :
      (K.X i).obj (op (n + 1)) →ₗ[R] (L.X j).obj (op n) := ((s n).v i j hij).hom
  change productMap (L.d (q - 1) q)
      (fun n ↦ S p (q - 1) (by omega) n (x (n + 1))) n +
      b.negOnePow • S (p + 1) q (by omega) n
        (productMap (K.d p (p + 1)) x (n + 1)) =
    (δ a b (s n)).v p q hpq (x (n + 1))
  rw [productMap_apply, productMap_apply]
  exact e.symm

/-- Assembling the cochains of the adjacent-square homotopies recovers the cochain of the
product-square homotopy. -/
lemma productComplexTransitionCochain_ofHomotopy
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L)) :
    productComplexTransitionCochain (fun n ↦ Cochain.ofHomotopy (h n)) =
      Cochain.ofHomotopy (productComplexSquareHomotopy f h) := by
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  simpa only [Cochain.ofHomotopy, Cochain.mk_v, productComplexTransitionCochain_v_apply]
    using (productComplexSquareHomotopy_hom_apply f h p q x n).symm

/-- The negative assembled second homotopy compares the reversed product-square homotopies
used by the native mapping fibre. -/
private lemma δ_neg_productComplexTransitionCochain
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h h' : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) (-2))
    (hs : ∀ n, δ (-2) (-1) (s n) = Cochain.ofHomotopy (h n) - Cochain.ofHomotopy (h' n)) :
    δ (-2) (-1) (-productComplexTransitionCochain s) =
      Cochain.ofHomotopy (productComplexSquareHomotopy (K := K) (L := L) f h).symm -
        Cochain.ofHomotopy (productComplexSquareHomotopy (K := K) (L := L) f h').symm := by
  rw [δ_neg, δ_productComplexTransitionCochain (by omega)]
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  simp only [Cochain.neg_v, hs, Cochain.sub_v, Cochain.ofHomotopy, Cochain.mk_v,
    Homotopy.symm_hom, ModuleCat.hom_sub, ModuleCat.hom_neg, LinearMap.sub_apply,
    LinearMap.neg_apply]
  -- Evaluate negation on the native dependent product before applying the component API.
  change -((productComplexTransitionCochain fun n ↦
      Cochain.ofHomotopy (h n) - Cochain.ofHomotopy (h' n)).v p q hpq x n) =
    -((productComplexSquareHomotopy f h).hom p q x n) -
      -((productComplexSquareHomotopy f h').hom p q x n)
  rw [productComplexTransitionCochain_v_apply]
  simp only [productComplexSquareHomotopy_hom_apply, Cochain.sub_v, Cochain.ofHomotopy,
    Cochain.mk_v, ModuleCat.hom_sub, LinearMap.sub_apply]
  abel

/-- A compatible family of second homotopies of the adjacent transition squares gives a
homotopy between the induced maps of homotopy limits. -/
def homotopyLimitMapOfHomotopiesHomotopy
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h h' : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) (-2))
    (hs : ∀ n, δ (-2) (-1) (s n) = Cochain.ofHomotopy (h n) - Cochain.ofHomotopy (h' n)) :
    Homotopy (homotopyLimitMapOfHomotopies (K := K) (L := L) f h)
      (homotopyLimitMapOfHomotopies (K := K) (L := L) f h') := by
  let H := mappingCocone.mapOfHomotopyHomotopy
    (productComplexSquareHomotopy (K := K) (L := L) f h).symm
    (productComplexSquareHomotopy (K := K) (L := L) f h').symm
    (-productComplexTransitionCochain s) (δ_neg_productComplexTransitionCochain f h h' s hs)
  exact
    { hom := H.hom
      zero := H.zero
      comm := fun i ↦ by
        rw [homotopyLimitMapOfHomotopies_def, homotopyLimitMapOfHomotopies_def]
        exact H.comm i }

/-- The homotopy of homotopy-limit maps factors through the product projection and the
assembled second homotopy. The two negative signs from reversal and shifting cancel. -/
@[simp]
lemma homotopyLimitMapOfHomotopiesHomotopy_hom
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h h' : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) (-2))
    (hs : ∀ n, δ (-2) (-1) (s n) = Cochain.ofHomotopy (h n) - Cochain.ofHomotopy (h' n))
    (p q : ℤ) (hpq : p + -1 = q) :
    (homotopyLimitMapOfHomotopiesHomotopy f h h' s hs).hom p q =
      (homotopyLimitFst K).f p ≫
        (productComplexTransitionCochain s).v p (q + -1) (by omega) ≫
          (mappingCocone.inr ((complexShift R).app L)).1.v (q + -1) q (by omega) := by
  rw [homotopyLimitMapOfHomotopiesHomotopy, mappingCocone.mapOfHomotopyHomotopy_hom
    _ _ _ _ p q hpq]
  simp only [Cochain.neg_v, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg,
    homotopyLimitFst_def]
  -- The remaining source and target presentations are the native shifted mapping cones.
  rfl

/-- Specified second homotopies make the induced homotopy-limit maps equal on homology,
without identifying maps coming from unrelated choices of square homotopies. -/
lemma homotopyLimitMapOfHomotopies_homologyMap_eq
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h h' : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (s : ∀ n, Cochain ((ev (n + 1)).obj K) ((ev n).obj L) (-2))
    (hs : ∀ n, δ (-2) (-1) (s n) = Cochain.ofHomotopy (h n) - Cochain.ofHomotopy (h' n))
    (i : ℤ) :
    homologyMap (homotopyLimitMapOfHomotopies f h) i =
      homologyMap (homotopyLimitMapOfHomotopies (K := K) (L := L) f h') i :=
  (homotopyLimitMapOfHomotopiesHomotopy f h h' s hs).homologyMap_eq i

end TauCeti.ModuleTower
