/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.Alternating.LinearDependent

/-!
# Bilinear maps read off multilinear maps in two variables

A multilinear map on the constant family `fun _ : Fin 2 => V` and a bilinear map on `V` carry the
same data.  This file records the direction that is used downstream:
`MultilinearMap.toBilinMap` reads a multilinear map `m` as the bilinear map
`(x, y) ↦ m ![x, y]`, and two recognition lemmas say when that map is symmetric or alternating.

The point of the construction is that the maps out of a second symmetric or exterior power are
multilinear in exactly this sense, so a functional on `Sym²V` or on `⋀²V` becomes a bilinear form
on `V` by composing with the universal multilinear map.  That is what
`TauCeti/LinearAlgebra/BilinearForm/Squares.lean` builds on this file.  An alternating bilinear
map can likewise be read as an `AlternatingMap` on `Fin 2`, and these two readings are inverse.

## Main definitions

* `MultilinearMap.toBilinMap`: the bilinear map `(x, y) ↦ m ![x, y]` of a multilinear map `m` in
  two variables.
* `LinearMap.IsAlt.toAlternatingMap`: an alternating bilinear map read as an alternating map on
  two arguments.

## Main results

* `MultilinearMap.map_vecCons_add_left`, `map_vecCons_add_right`, `map_vecCons_smul_left` and
  `map_vecCons_smul_right`: a (semilinear) multilinear map in two variables is additive and
  semilinear in each argument of a pair `![x, y]`.
* `MultilinearMap.isSymm_toBilinMap`: the scalar-valued form is symmetric when `m` is unchanged by
  swapping its two arguments.
* `MultilinearMap.isAlt_toBilinMap`: the map is alternating when `m` vanishes on a repeated
  argument; `AlternatingMap.isAlt_toBilinMap` specializes this to alternating maps.
* `MultilinearMap.toBilinMap_injective`: the other half of "the same data" -- the bilinear map
  determines the multilinear map.
* `LinearMap.IsAlt.eq_zero_of_not_linearIndependent`: an alternating bilinear map vanishes on a
  linearly dependent pair when unequal scalars act differently on every nonzero value, the case of
  two arguments of `AlternatingMap.map_linearDependent_of_smul_left_injective`.
* `AlternatingMap.toAlternatingMap_isAlt_toBilinMap` and
  `LinearMap.IsAlt.toBilinMap_toAlternatingMap`: the two round trips between alternating maps on
  `Fin 2` and alternating bilinear maps.

## Implementation notes

Bilinearity is Mathlib's `MultilinearMap.cons_add` and `cons_smul` at the first argument and
`MultilinearMap.snoc_add` and `snoc_smul` at the second, since `![x, y]` is both `Fin.cons x ![y]`
and `Fin.snoc ![x] y`; the `map_vecCons_*` lemmas state them for pairs.  Feeding those four facts
to `LinearMap.mk₂` keeps the four linearity goals stated in the `![·, ·]` notation, so none of
them has to be massaged into the nested form a bare `LinearMap` constructor would present.
-/

public section

variable {R V N : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid N] [Module R N]

namespace LinearMap

namespace IsAlt

/-- An alternating bilinear map read as an alternating map in two arguments. -/
def toAlternatingMap {ω : V →ₗ[R] V →ₗ[R] N} (hω : LinearMap.IsAlt ω) :
    V [⋀^Fin 2]→ₗ[R] N where
  toFun v := ω (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i c x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all [hω.self_eq_zero]

/-- Evaluating the alternating map recovers the original bilinear map on the two arguments. -/
@[simp]
theorem toAlternatingMap_apply {ω : V →ₗ[R] V →ₗ[R] N} (hω : LinearMap.IsAlt ω)
    (v : Fin 2 → V) : hω.toAlternatingMap v = ω (v 0) (v 1) :=
  (rfl)

/-- An alternating bilinear map vanishes on a linearly dependent pair, provided unequal scalars
act differently on every nonzero value. Over an integral domain acting on torsion-free values in an
additive group, the latter hypothesis is `fun _ ↦ smul_left_injective R`. This is the case of two
arguments of `AlternatingMap.map_linearDependent_of_smul_left_injective`. -/
theorem eq_zero_of_not_linearIndependent {ω : V →ₗ[R] V →ₗ[R] N} (halt : ω.IsAlt)
    (hN : ∀ n : N, n ≠ 0 → Function.Injective fun r : R ↦ r • n) {v w : V}
    (hvw : ¬LinearIndependent R ![v, w]) : ω v w = 0 := by
  simpa using halt.toAlternatingMap.map_linearDependent_of_smul_left_injective hN hvw

end IsAlt

end LinearMap

namespace MultilinearMap

section VecCons

variable {S S' M P : Type*} [Semiring S] [Semiring S'] {σ : S →+* S'} [AddCommMonoid M]
  [Module S M] [AddCommMonoid P] [Module S' P] (m : (Fin 2 → M) →ₘₛₗ[σ] P)

/-- A multilinear map in two variables is additive in its first argument. -/
theorem map_vecCons_add_left (x x' y : M) : m ![x + x', y] = m ![x, y] + m ![x', y] :=
  m.cons_add ![y] x x'

/-- A multilinear map in two variables is additive in its second argument. -/
theorem map_vecCons_add_right (x y y' : M) : m ![x, y + y'] = m ![x, y] + m ![x, y'] := by
  simpa using m.snoc_add ![x] y y'

/-- A multilinear map in two variables is `σ`-semilinear in its first argument. -/
theorem map_vecCons_smul_left (c : S) (x y : M) : m ![c • x, y] = σ c • m ![x, y] :=
  m.cons_smul ![y] c x

/-- A multilinear map in two variables is `σ`-semilinear in its second argument. -/
theorem map_vecCons_smul_right (c : S) (x y : M) : m ![x, c • y] = σ c • m ![x, y] := by
  simpa using m.snoc_smul ![x] c y

end VecCons

/-- The bilinear map `(x, y) ↦ m ![x, y]` of a multilinear map `m` in two variables. -/
def toBilinMap (m : MultilinearMap (RingHom.id R) (fun _ : Fin 2 => V)
    N) : LinearMap.BilinMap R V N :=
  LinearMap.mk₂ R (fun x y => m ![x, y]) m.map_vecCons_add_left m.map_vecCons_smul_left
    m.map_vecCons_add_right m.map_vecCons_smul_right

@[simp]
theorem toBilinMap_apply (m : MultilinearMap (RingHom.id R) (fun _ : Fin 2 => V) N) (x y : V) :
    m.toBilinMap x y = m ![x, y] :=
  (rfl)

/-- The form of a scalar-valued multilinear map that is unchanged by swapping its two arguments
is symmetric. -/
theorem isSymm_toBilinMap {m : MultilinearMap (RingHom.id R) (fun _ : Fin 2 => V) R}
    (h : ∀ x y : V, m ![y, x] = m ![x, y]) : LinearMap.BilinForm.IsSymm m.toBilinMap :=
  ⟨fun x y => (h x y).symm⟩

/-- The bilinear map of a multilinear map that vanishes on a repeated argument is alternating. -/
theorem isAlt_toBilinMap {m : MultilinearMap (RingHom.id R) (fun _ : Fin 2 => V) N}
    (h : ∀ x : V, m ![x, x] = 0) : m.toBilinMap.IsAlt :=
  fun x => (toBilinMap_apply m x x).trans (h x)

/-- **A multilinear map in two variables is determined by its bilinear map.**  Every argument of
`m` is a `![x, y]`, and the bilinear map records the value of `m` there. -/
theorem toBilinMap_injective :
    Function.Injective (toBilinMap : MultilinearMap (RingHom.id R) (fun _ : Fin 2 => V) N → _) := by
  intro m n h
  ext f
  rw [← FinVec.etaExpand_eq f]
  exact congr($h (f 0) (f 1))

end MultilinearMap

namespace AlternatingMap

/-- The bilinear map of an alternating map in two arguments is alternating. -/
theorem isAlt_toBilinMap (A : V [⋀^Fin 2]→ₗ[R] N) : A.toMultilinearMap.toBilinMap.IsAlt :=
  MultilinearMap.isAlt_toBilinMap fun x =>
    A.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

/-- Reading an alternating map in two arguments as a bilinear map and back recovers the map. -/
@[simp]
theorem toAlternatingMap_isAlt_toBilinMap (A : V [⋀^Fin 2]→ₗ[R] N) :
    A.isAlt_toBilinMap.toAlternatingMap = A := by
  ext v
  rw [← FinVec.etaExpand_eq v]
  rfl

end AlternatingMap

namespace LinearMap.IsAlt

/-- Reading an alternating bilinear map as an alternating map and back recovers the map. -/
@[simp]
theorem toBilinMap_toAlternatingMap {B : V →ₗ[R] V →ₗ[R] N} (hB : B.IsAlt) :
    hB.toAlternatingMap.toMultilinearMap.toBilinMap = B :=
  (rfl)

end LinearMap.IsAlt
