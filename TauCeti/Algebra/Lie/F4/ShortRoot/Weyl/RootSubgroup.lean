/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.RootDatum
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
natural in the commutative value ring, and the represented weight torus rescales the parameter
of `x_{l,i}` through the character of the root `w αᵢ`:

```text
s x_{l,i}(u) s⁻¹ = x_{l,i}((w αᵢ)(s) u).
```

The root-indexed family below fixes one Weyl-word presentation of each root, choosing the empty
word at positive simple roots, so it satisfies the pinning equation at every root. It does not
compare two presentations of the same root; such a comparison may change the sign of the
parameter. The representation of these pointwise homomorphisms by closed subgroup-scheme
morphisms is left to subsequent constructions.

## Main definitions

* `TauCeti.F4ShortRoot.weylRootSubgroupPoints`: the root-subgroup homomorphism attached to a word
  and a simple node.
* `TauCeti.F4ShortRoot.rootSubgroupPointsAt`: a selected root-subgroup homomorphism for every root
  of the simply connected type-`F₄` root datum.

## Main results

* `TauCeti.F4ShortRoot.weightTorusPoints_conj_weylRootSubgroupPoints` and
  `TauCeti.F4ShortRoot.weightTorusPoints_conj_rootSubgroupPointsAt`: the pinning equations at the
  root attached to a word and node, and at every root index.
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

/-! ## Root subgroups transported along Weyl words -/

/-- **The short-root carrier's root subgroup attached to a Weyl word and a simple node**:
`x_{l,i}(u) = n_l xᵢ(u) n_l⁻¹`. Its root is `F4.geckWeylRootIndex valid_F4 l i`, by
`weightTorusPoints_conj_weylRootSubgroupPoints`. -/
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

/-! ## The pinning equation at every root -/

/-- **The pinning equation of a Weyl-transported root subgroup.** Conjugation by a weight-torus
point `s` rescales the parameter of `x_{l,i}` by the character of the root at
`F4.geckWeylRootIndex valid_F4 l i`, that is `w αᵢ` with `w` the Weyl-group element spelled
by `l`. -/
theorem weightTorusPoints_conj_weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * weylRootSubgroupPoints l i A u * (weightTorusPoints A s)⁻¹ =
      weylRootSubgroupPoints l i A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((F4.simplyConnectedRootDatum valid_F4).root
                (F4.geckWeylRootIndex valid_F4 l i)) : A) *
            Multiplicative.toAdd u)) :=
  F4.conj_conj_eq_torusCharacter_root_geckWeylRootIndex valid_F4 _ _ _ l i
    (weylWordPoint_conj_weightTorusPoints l A)
    (weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex valid_F4 i A) s u

/-! ## A selected family indexed by every root -/

/-- A selected Weyl-word presentation of every type-`F₄` root, specialized to the concrete
rank-four node type. Positive simple roots use the empty word. -/
def rootSubgroupPresentation (k : Fin F4.numRoots) : List (Fin 4) × Fin 4 :=
  F4.geckRootSubgroupPresentation valid_F4 k

/-- The selected presentation at a positive simple root is the empty word at that node. -/
@[simp]
theorem rootSubgroupPresentation_simpleIndex (i : Fin 4) :
    rootSubgroupPresentation (Fin.castAdd 44 i) = ([], i) := by
  unfold rootSubgroupPresentation
  rw [← simpleIndex_F4 valid_F4 i]
  -- `F4.rank` reduces to `4`, so the generic lemma at `i : Fin F4.rank` applies to `i : Fin 4`;
  -- `rw` cannot perform this cast because the generic pattern is ill-typed at `Fin 4`.
  exact F4.geckRootSubgroupPresentation_simpleIndex valid_F4 i

/-- The selected Weyl-word presentation represents its root index. -/
@[simp]
theorem weylRootIndex_rootSubgroupPresentation (k : Fin F4.numRoots) :
    F4.geckWeylRootIndex valid_F4 (rootSubgroupPresentation k).1
      (rootSubgroupPresentation k).2 = k :=
  F4.geckWeylRootIndex_geckRootSubgroupPresentation valid_F4 k

/-- **A selected root subgroup of the short-root carrier at every root index.** The selected
Weyl-word presentation is `rootSubgroupPresentation`; no independence of the presentation is
asserted. -/
def rootSubgroupPointsAt (k : Fin F4.numRoots) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  weylRootSubgroupPoints (rootSubgroupPresentation k).1 (rootSubgroupPresentation k).2 A

/-- The selected root subgroup at `k` is the Weyl-transported root subgroup of the selected
presentation of `k`. -/
theorem rootSubgroupPointsAt_def (k : Fin F4.numRoots) (A : Type v) [CommRing A] :
    rootSubgroupPointsAt k A =
      weylRootSubgroupPoints (rootSubgroupPresentation k).1 (rootSubgroupPresentation k).2 A :=
  (rfl)

/-- At a positive simple root, the selected family recovers the pinned raising subgroup. -/
@[simp]
theorem rootSubgroupPointsAt_simpleIndex (i : Fin 4) (A : Type v) [CommRing A] :
    rootSubgroupPointsAt (Fin.castAdd 44 i) A = rootSubgroupPoints (.inl i) A := by
  rw [rootSubgroupPointsAt_def (Fin.castAdd 44 i), rootSubgroupPresentation_simpleIndex,
    weylRootSubgroupPoints_nil]

/-- The selected root-indexed family commutes with change of value ring. -/
theorem map_rootSubgroupPointsAt {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (k : Fin F4.numRoots) (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPointsAt k A u) =
      rootSubgroupPointsAt k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  rw [rootSubgroupPointsAt_def, rootSubgroupPointsAt_def]
  exact map_weylRootSubgroupPoints f _ _ u

/-- **The pinning equation of the selected root subgroup at every root.** Conjugation by a
weight-torus point `s` rescales the parameter of the selected root subgroup at `k` by the
character of the root at `k`. -/
theorem weightTorusPoints_conj_rootSubgroupPointsAt (k : Fin F4.numRoots)
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPointsAt k A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPointsAt k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s ((F4.simplyConnectedRootDatum valid_F4).root k) : A) *
            Multiplicative.toAdd u)) := by
  have h := weightTorusPoints_conj_weylRootSubgroupPoints (rootSubgroupPresentation k).1
    (rootSubgroupPresentation k).2 A s u
  rw [rootSubgroupPointsAt_def]
  rwa [weylRootIndex_rootSubgroupPresentation] at h

end

end TauCeti.F4ShortRoot
