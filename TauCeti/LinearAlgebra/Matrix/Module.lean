/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Matrix modules

A family `y : n → P` in a module over a ring `A` satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` is exactly a
fixed point of Mathlib's `Matrix n n A`-action on `n → P` (`Matrix.Module.matrixModule`), so it
is killed by `1 - B`. If `1 - B` is a unit, `y` vanishes.

This is pure algebra: `P` carries no topology and `A` need not be commutative. Criteria producing
`IsUnit (1 - B)`, such as topological nilpotence of the entries of `B`, live elsewhere, so this
statement applies to abstract subquotients without importing them.

The scoped column action on `ι → R` agrees with the matrix-to-endomorphism algebra
equivalence; in particular its action map is bijective. This identifies the matrix module
used by matrix Morita equivalence with the usual full endomorphism representation.

The graph `Matrix.piGraph u P = {(x, u • x) : x ∈ P^ι}` of the action of a square matrix `u` on
`V^ι`, over the coordinatewise power of a submodule `P`, is isomorphic to `P^ι`. When `2` and `u`
are invertible, the graphs of `u` and `-u` meet only in zero: a vector `x` with `u • x = -u • x`
satisfies `2 • u • x = 0`.

Changing a family `v` by the rows of a matrix, `vⱼ ↦ ∑ i, A j i • vᵢ`, is compatible with matrix
multiplication: changing by `A` and then by `B` is changing by `B * A`.

## Main results

* `TauCeti.eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul`: a family fixed by `B` vanishes as
  soon as `1 - B` is a unit.
* `Matrix.sum_mul_apply_smul`: two successive changes of a family by matrices `A` and then `B`
  are the change by `B * A`.
* `Matrix.piGraph`, `Matrix.mem_piGraph_iff`: the graph of a matrix action over `P^ι`.
* `Matrix.disjoint_piGraph_neg`: the graphs of an invertible matrix and of its negative meet only
  in zero when `2` is invertible.
* `Matrix.finrank_piGraph`: the graph over `P^ι` has dimension `card ι * dim P`.

## References

* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.7.2/1, where this is the algebraic engine behind closedness of finitely generated
  submodules.
-/

public section

open scoped Matrix.Module

namespace TauCeti

/-- **A family fixed by a matrix vanishes when `1 - B` is a unit.** If `y : n → P` satisfies
`yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` for every `i` and `1 - B` is invertible in `Matrix n n A`, then `y = 0`. The
ring `A` need not be commutative. -/
theorem eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul {A : Type*} [Ring A] {n : Type*}
    [Fintype n] [DecidableEq n] {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hU : IsUnit (1 - B))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) : y = 0 := by
  refine hU.smul_eq_zero.mp ?_
  rw [sub_smul, one_smul, sub_eq_zero]
  ext i
  rw [Matrix.Module.smul_apply, ← hy i]

end TauCeti

/-- Two successive changes of frame, by `A` and then by `B`, are the change of frame by `B * A`. -/
theorem Matrix.sum_mul_apply_smul {R M ι κ μ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [Fintype κ] (B : Matrix μ κ R) (A : Matrix κ ι R) (v : ι → M)
    (j : μ) : ∑ l, (B * A) j l • v l = ∑ i, B j i • ∑ l, A i l • v l := by
  simp_rw [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

namespace Matrix.Module

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The scoped column action agrees with the usual matrix-to-endomorphism equivalence. -/
theorem lsmul_eq_toLinAlgEquiv' :
    (Algebra.lsmul R R (ι → R) : Matrix ι ι R →ₐ[R] _) =
      Matrix.toLinAlgEquiv'.toAlgHom := by
  ext a v i
  simp [Matrix.Module.smul_apply, Matrix.mulVec, dotProduct]

/-- The native column action is the full endomorphism algebra of the column space. -/
theorem lsmul_bijective :
    Function.Bijective (Algebra.lsmul R R (ι → R) : Matrix ι ι R →ₐ[R] _) := by
  rw [lsmul_eq_toLinAlgEquiv']
  exact Matrix.toLinAlgEquiv'.bijective

end Matrix.Module

namespace Matrix

section CommRing

variable {ι k V : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [AddCommGroup V] [Module k V]

/-- The graph `{(x, u • x) : x ∈ P^ι}` of the action of a square matrix `u` on `V^ι`, restricted
to the coordinatewise power `P^ι` of a submodule `P`. -/
def piGraph (u : Matrix ι ι k) (P : Submodule k V) : Submodule k ((ι → V) × (ι → V)) :=
  (Submodule.pi Set.univ fun _ ↦ P).map (LinearMap.id.prod (Algebra.lsmul k k (ι → V) u))

/-- A pair lies in the graph of `u` over `P^ι` when its first component lies in `P^ι` and its
second is the image of the first under `u`. -/
@[simp]
theorem mem_piGraph_iff {u : Matrix ι ι k} {P : Submodule k V} {p : (ι → V) × (ι → V)} :
    p ∈ u.piGraph P ↔ (∀ i, p.1 i ∈ P) ∧ p.2 = u • p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i ↦ hx i trivial, rfl⟩
  · rintro ⟨hp, h⟩
    exact ⟨p.1, fun i _ ↦ hp i, Prod.ext rfl h.symm⟩

/-- When `2` is invertible, the graphs of an invertible matrix and of its negative meet only in
zero. -/
theorem disjoint_piGraph_neg [Invertible (2 : k)] {u : Matrix ι ι k} (hu : IsUnit u)
    (P Q : Submodule k V) : Disjoint (u.piGraph P) ((-u).piGraph Q) := by
  rw [Submodule.disjoint_def]
  rintro p hp hq
  rw [mem_piGraph_iff] at hp hq
  have h : u • p.1 = -(u • p.1) := hp.2.symm.trans (hq.2.trans (neg_smul u p.1))
  have h2 : (2 : k) • u • p.1 = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  have hu' : u • p.1 = 0 := by
    simpa using congr(⅟(2 : k) • $h2)
  have h1 : p.1 = 0 := (hu.smul_left_cancel).mp (hu'.trans (smul_zero u).symm)
  exact Prod.ext h1 (hp.2.trans hu')

end CommRing

section Field

variable {ι k V : Type*} [Fintype ι] [DecidableEq ι] [Field k] [AddCommGroup V] [Module k V]

/-- The graph of a matrix action over `P^ι` has dimension `card ι * dim P`. -/
theorem finrank_piGraph (u : Matrix ι ι k) (P : Submodule k V) :
    Module.finrank k (u.piGraph P) = Fintype.card ι * Module.finrank k P := by
  have hinj : Function.Injective (LinearMap.id.prod (Algebra.lsmul k k (ι → V) u)) :=
    fun x y h ↦ congr_arg Prod.fst h
  have hsub : Function.Injective (P.subtype.compLeft ι) :=
    fun x y h ↦ funext fun i ↦ P.subtype_injective (congr_fun h i)
  have hpi : Submodule.pi Set.univ (fun _ : ι ↦ P) = LinearMap.range (P.subtype.compLeft ι) := by
    rw [LinearMap.range_compLeft, P.range_subtype]
  rw [piGraph, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, hpi,
    LinearMap.finrank_range_of_inj hsub]
  by_cases hP : Module.Finite k P
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · -- `P` is infinite-dimensional, and so is `P^ι` when `ι` is nonempty: both sides are `0`.
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Module.finrank_zero_of_subsingleton]
    · obtain ⟨i⟩ := hι
      have hfin : ¬Module.Finite k (ι → P) := fun h ↦
        hP (.of_surjective _ (LinearMap.proj_surjective (R := k) (φ := fun _ ↦ P) i))
      rw [Module.finrank_of_not_finite hP, mul_zero, Module.finrank_of_not_finite hfin]

end Field

end Matrix
