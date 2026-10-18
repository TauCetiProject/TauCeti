/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup

/-!
# Root subgroups at every root of the short-root F₄ carrier

The short-root type-`F₄` carrier has pinned root-subgroup homomorphisms at the positive and
negative simple roots and integral representatives of the simple reflections. Multiplying those
representatives along a word `l` gives a point `n_l`. Conjugating the positive simple-root
subgroup at node `i` by `n_l` gives

```text
x_{l,i}(u) = n_l xᵢ(u) n_l⁻¹
```

at the root `w αᵢ`, where `w` is the Weyl-group element spelled by `l`. Every root of the
simply connected type-`F₄` root datum has such a presentation. The resulting homomorphisms are
natural in the commutative value ring. The Weyl-word representatives also act on the short-root
carrier's represented weight torus through the corresponding abstract Weyl-word action.

The root-indexed family below fixes one Weyl-word presentation of each root, choosing the empty
word at positive simple roots. It does not compare two presentations of the same root; such a
comparison may change the sign of the parameter. The all-root pinning equation and the
representation of these pointwise homomorphisms by closed subgroup-scheme morphisms are left to
subsequent constructions.

## Main definitions

* `TauCeti.F4ShortRoot.weylWordPoint`: the carrier point represented by a word in the simple
  reflections.
* `TauCeti.F4ShortRoot.weylRootSubgroupPoints`: the root-subgroup homomorphism attached to a word
  and a simple node.
* `TauCeti.F4ShortRoot.rootSubgroupPointsAt`: a selected root-subgroup homomorphism for every root
  of the simply connected type-`F₄` root datum.

## Main results

* `TauCeti.F4ShortRoot.weylWordPoint_conj_weightTorusPoints`: Weyl-word representatives act on the
  represented torus through the abstract Weyl-word action.
* `TauCeti.F4ShortRoot.map_weylRootSubgroupPoints`: naturality under change of value ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.3.
-/

-- This is the short-root-carrier specialization of the formal Geck-carrier construction in
-- `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup`.

public section

namespace TauCeti.F4ShortRoot

open DynkinType

universe v w

noncomputable section

/-! ## Weyl-word representatives -/

/-- **The point of the short-root carrier represented by a word in the simple reflections.** -/
def weylWordPoint (l : List (Fin 4)) (A : Type v) [CommRing A] : points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty word represents the identity point. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] : weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its simple Weyl representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 4) (l : List (Fin 4)) (A : Type v) [CommRing A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation of words corresponds to multiplication of their representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin 4)) (A : Type v) [CommRing A] :
    weylWordPoint (l ++ l') A = weylWordPoint l A * weylWordPoint l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- Weyl-word representatives commute with change of value ring. -/
@[simp]
theorem map_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin 4)) :
    (pointsPresentation A).map (pointsPresentation B) f (weylWordPoint l A) =
      weylWordPoint l B := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [weylWordPoint_cons, map_mul, map_simpleWeylPoint, ih, weylWordPoint_cons]

/-- **Conjugation by a Weyl-word representative realizes the corresponding abstract Weyl-word
action on the represented weight torus.** -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A (F4.geckWeylWordTorusAction valid_F4 l A s) := by
  induction l with
  | nil =>
      rw [weylWordPoint_nil]
      simp only [one_mul, inv_one, mul_one]
      congr 1
      have h := DFunLike.congr_fun
        (F4.geckWeylWordTorusAction_nil valid_F4 A) s
      change F4.geckWeylWordTorusAction valid_F4 [] A s = s at h
      exact h.symm
  | cons i l ih =>
      rw [weylWordPoint_cons]
      calc
        (simpleWeylPoint i A * weylWordPoint l A) * weightTorusPoints A s *
              (simpleWeylPoint i A * weylWordPoint l A)⁻¹ =
            simpleWeylPoint i A *
              (weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹) *
              (simpleWeylPoint i A)⁻¹ := by group
        _ = simpleWeylPoint i A *
              weightTorusPoints A (F4.geckWeylWordTorusAction valid_F4 l A s) *
              (simpleWeylPoint i A)⁻¹ := by rw [ih]
        _ = weightTorusPoints A
              (F4.geckSimpleReflectionTorusPoint valid_F4 i A
                (F4.geckWeylWordTorusAction valid_F4 l A s)) :=
          simpleWeylPoint_conj_weightTorusPoints i A _
        _ = weightTorusPoints A (F4.geckWeylWordTorusAction valid_F4 (i :: l) A s) := by
          congr 1
          have h := DFunLike.congr_fun
            (F4.geckWeylWordTorusAction_cons valid_F4 i l A) s
          change F4.geckWeylWordTorusAction valid_F4 (i :: l) A s =
            F4.geckSimpleReflectionTorusPoint valid_F4 i A
              (F4.geckWeylWordTorusAction valid_F4 l A s) at h
          exact h.symm

/-- Every Weyl-word representative normalizes the represented weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons i l ih =>
      rw [weylWordPoint_cons]
      exact Subgroup.mul_mem _ (simpleWeylPoint_mem_normalizer_weightTorusPoints i A) ih

/-! ## Root subgroups transported along Weyl words -/

/-- **The short-root carrier's root subgroup attached to a Weyl word and a simple node**:
`x_{l,i}(u) = n_l xᵢ(u) n_l⁻¹`. Its root is `F4.geckWeylRootIndex valid_F4 l i`. -/
def weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  (MulAut.conj (weylWordPoint l A)).toMonoidHom.comp (rootSubgroupPoints (.inl i) A)

/-- A Weyl-transported root subgroup is conjugation of the numbered raising subgroup. -/
@[simp]
theorem weylRootSubgroupPoints_apply (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    weylRootSubgroupPoints l i A u =
      weylWordPoint l A * rootSubgroupPoints (.inl i) A u * (weylWordPoint l A)⁻¹ :=
  (rfl)

/-- The empty word gives the numbered positive simple-root subgroup. -/
@[simp]
theorem weylRootSubgroupPoints_nil (i : Fin 4) (A : Type v) [CommRing A] :
    weylRootSubgroupPoints [] i A = rootSubgroupPoints (.inl i) A := by
  ext u
  simp

/-- Prepending a node conjugates by the corresponding simple Weyl representative. -/
theorem weylRootSubgroupPoints_cons (j : Fin 4) (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    weylRootSubgroupPoints (j :: l) i A u =
      simpleWeylPoint j A * weylRootSubgroupPoints l i A u * (simpleWeylPoint j A)⁻¹ := by
  simp only [weylRootSubgroupPoints_apply, weylWordPoint_cons]
  group

/-- The word `[i]` gives the numbered negative simple-root subgroup with negated parameter. -/
theorem weylRootSubgroupPoints_singleton_self (i : Fin 4) (A : Type v) [CommRing A] (u : A) :
    weylRootSubgroupPoints [i] i A (Multiplicative.ofAdd u) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  rw [weylRootSubgroupPoints_cons, weylRootSubgroupPoints_nil,
    simpleWeylPoint_conj_rootSubgroupPoints]

/-- **Weyl-transported root subgroups commute with change of value ring.** -/
theorem map_weylRootSubgroupPoints {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin 4)) (i : Fin 4) (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (weylRootSubgroupPoints l i A u) =
      weylRootSubgroupPoints l i B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  rw [weylRootSubgroupPoints_apply, weylRootSubgroupPoints_apply, map_mul, map_mul, map_inv,
    map_weylWordPoint, map_rootSubgroupPoints]

/-! ## A selected family indexed by every root -/

/-- A selected Weyl-word presentation of every type-`F₄` root, specialized to the concrete
rank-four node type. Positive simple roots use the empty word. -/
def rootSubgroupPresentation (k : Fin F4.numRoots) : List (Fin 4) × Fin 4 := by
  simpa only [rank_F4] using F4.geckRootSubgroupPresentation valid_F4 k

/-- The selected presentation at a positive simple root is the empty word at that node. -/
@[simp]
theorem rootSubgroupPresentation_simpleIndex (i : Fin 4) :
    rootSubgroupPresentation (Fin.castAdd 44 i) = ([], i) := by
  simpa only [rootSubgroupPresentation, rank_F4, simpleIndex_F4] using
    F4.geckRootSubgroupPresentation_simpleIndex valid_F4 i

/-- The selected Weyl-word presentation represents its root index. -/
@[simp]
theorem weylRootIndex_rootSubgroupPresentation (k : Fin F4.numRoots) :
    F4.geckWeylRootIndex valid_F4 (rootSubgroupPresentation k).1
      (rootSubgroupPresentation k).2 = k := by
  simpa only [rootSubgroupPresentation, rank_F4] using
    F4.geckWeylRootIndex_geckRootSubgroupPresentation valid_F4 k

/-- **A selected root subgroup of the short-root carrier at every root index.** The selected
Weyl-word presentation is `rootSubgroupPresentation`; no independence of the presentation is
asserted. -/
def rootSubgroupPointsAt (k : Fin F4.numRoots) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  weylRootSubgroupPoints (rootSubgroupPresentation k).1 (rootSubgroupPresentation k).2 A

/-- At a positive simple root, the selected family recovers the pinned raising subgroup. -/
@[simp]
theorem rootSubgroupPointsAt_simpleIndex (i : Fin 4) (A : Type v) [CommRing A] :
    rootSubgroupPointsAt (Fin.castAdd 44 i) A = rootSubgroupPoints (.inl i) A := by
  change weylRootSubgroupPoints (rootSubgroupPresentation (Fin.castAdd 44 i)).1
      (rootSubgroupPresentation (Fin.castAdd 44 i)).2 A = rootSubgroupPoints (.inl i) A
  rw [rootSubgroupPresentation_simpleIndex, weylRootSubgroupPoints_nil]

/-- The selected root-indexed family commutes with change of value ring. -/
theorem map_rootSubgroupPointsAt {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (k : Fin F4.numRoots) (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPointsAt k A u) =
      rootSubgroupPointsAt k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  exact map_weylRootSubgroupPoints f _ _ u

end

end TauCeti.F4ShortRoot
