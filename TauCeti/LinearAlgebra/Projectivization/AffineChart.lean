/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import TauCeti.Algebra.Field.Fin.Tuple
public import TauCeti.Data.Fin.Tuple.Basic

/-!
# Standard affine charts of projective space

For a division ring `K` and an index type `ι`, the projective space `ℙ K (ι → K)` is covered by
the standard affine opens `U_i = {[v] | v i ≠ 0}`, one for each `i : ι`. For a field `K` and
`ι = Fin (n + 1)`, the homogeneous ratios `[v] ↦ (v (i.succAbove j) / v i)_(j : Fin n)`
identify `U_i` with the affine space `Fin n → K`; the inverse inserts the coordinate `1` in
position `i`, sending `z` to `[Fin.insertNth i 1 z]`. The remaining coordinates are enumerated by
`Fin.succAbove i`.

This file records these charts as partial equivalences `Projectivization.affineChart i`, together
with their transition maps: on the overlap of `U_i` and `U_j`, the transition from the chart of `i`
to the chart of `j` divides the homogeneous coordinates `Fin.insertNth i 1 z` by their `j`-th
entry. These are the algebraic data of the standard atlas of projective space, over an arbitrary
field: once projective space carries its quotient topology, they are the charts and rational
transition maps from which the smooth structure of real projective space and the complex structure
of complex projective space are built.

## Main declarations

* `Projectivization.affineOpen i`: the points whose `i`-th homogeneous coordinate is nonzero;
  `Projectivization.iUnion_affineOpen` says that these sets cover projective space.
* `Projectivization.affineChart i`: the affine chart `U_i ≃ Fin n → K` by homogeneous ratios.
* `Projectivization.affineChart_mk` and `Projectivization.affineChart_symm_apply`: the chart and
  its inverse in homogeneous coordinates.
* `Projectivization.affineChart_symm_trans_source` and
  `Projectivization.affineChart_symm_trans_apply`: the domain and formula of the transition maps.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set

open scoped LinearAlgebra.Projectivization

namespace Projectivization

section AffineOpen

variable {K : Type*} [DivisionRing K] {ι : Type*}

/-- The standard affine open of projective space where the `i`-th homogeneous coordinate is
nonzero. -/
def affineOpen (i : ι) : Set (ℙ K (ι → K)) :=
  {x | x.rep i ≠ 0}

/-- A point lies in the standard affine open of `i` when the `i`-th entry of its chosen
representative is nonzero; see `Projectivization.mk_mem_affineOpen_iff` for arbitrary homogeneous
coordinates. -/
theorem mem_affineOpen_iff (i : ι) (x : ℙ K (ι → K)) : x ∈ affineOpen i ↔ x.rep i ≠ 0 :=
  Iff.rfl

/-- Membership in a standard affine open does not depend on the chosen homogeneous coordinates. -/
@[simp]
theorem mk_mem_affineOpen_iff (i : ι) (v : ι → K) (hv : v ≠ 0) :
    mk K v hv ∈ affineOpen i ↔ v i ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  simp [mem_affineOpen_iff, ← ha, Units.smul_def]

/-- Every point of projective space lies in some standard affine open. -/
theorem exists_mem_affineOpen (x : ℙ K (ι → K)) : ∃ i, x ∈ affineOpen i :=
  Function.ne_iff.1 x.rep_nonzero

/-- The standard affine opens cover projective space. -/
theorem iUnion_affineOpen : ⋃ i, affineOpen (K := K) (ι := ι) i = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.2 (exists_mem_affineOpen x)

/-- With a single homogeneous coordinate, as for the projective space of dimension zero, the
standard affine open is the whole space. -/
@[simp]
theorem affineOpen_eq_univ [Subsingleton ι] (i : ι) : affineOpen (K := K) i = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨j, hj⟩ := exists_mem_affineOpen x
  rwa [Subsingleton.elim j i] at hj

end AffineOpen

variable {K : Type*} [Field K] {n : ℕ}

/-- The standard affine chart of projective space at the coordinate `i`: on the affine open where
the `i`-th homogeneous coordinate is nonzero, it is given by the ratios of the other coordinates to
that one, enumerated by `Fin.succAbove i`. Its inverse sends `z` to `[Fin.insertNth i 1 z]`. -/
noncomputable def affineChart (i : Fin (n + 1)) : PartialEquiv (ℙ K (Fin (n + 1) → K)) (Fin n → K)
    where
  toFun := Projectivization.lift (fun v j ↦ v.1 (i.succAbove j) / v.1 i) fun a b t h ↦ by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using h)
    ext j
    simp [h, mul_div_mul_left _ _ ht]
  invFun z := mk K (Fin.insertNth (α := fun _ ↦ K) i 1 z)
    (Fin.insertNth_one_ne_zero i z)
  source := affineOpen i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := by simp
  left_inv' x hx := by
    induction x using ind with | h v hv =>
    rw [mk_mem_affineOpen_iff] at hx
    exact (mk_eq_mk_iff' K _ _ _ hv).2 ⟨(v i)⁻¹, (Fin.insertNth_one_div_eq_inv_smul i v hx).symm⟩
  right_inv' z _ := by
    ext j
    simp

@[simp]
theorem affineChart_source (i : Fin (n + 1)) : (affineChart (K := K) i).source = affineOpen i :=
  (rfl)

@[simp]
theorem affineChart_target (i : Fin (n + 1)) : (affineChart (K := K) i).target = univ :=
  (rfl)

/-- The standard affine chart in homogeneous coordinates: the ratios of the other coordinates to
the `i`-th one. Outside the chart domain both sides are `0`. -/
@[simp]
theorem affineChart_mk (i : Fin (n + 1)) (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    affineChart i (mk K v hv) = fun j ↦ v (i.succAbove j) / v i :=
  (rfl)

/-- The inverse of the standard affine chart sends `z` to `[Fin.insertNth i 1 z]`. -/
@[simp]
theorem affineChart_symm_apply (i : Fin (n + 1)) (z : Fin n → K) :
    (affineChart i).symm z = mk K (Fin.insertNth (α := fun _ ↦ K) i 1 z)
      (Fin.insertNth_one_ne_zero i z) :=
  (rfl)

/-- The domain of the transition map from the standard affine chart of `i` to that of `j`
consists of the points whose homogeneous coordinates `Fin.insertNth i 1 z` have nonzero `j`-th
entry. -/
theorem affineChart_symm_trans_source (i j : Fin (n + 1)) :
    ((affineChart (K := K) i).symm.trans (affineChart j)).source =
      {z | Fin.insertNth (α := fun _ ↦ K) i 1 z j ≠ 0} := by
  ext z
  simp

/-- The transition map from the standard affine chart of `i` to that of `j` divides the
homogeneous coordinates `Fin.insertNth i 1 z` by their `j`-th entry. -/
theorem affineChart_symm_trans_apply (i j : Fin (n + 1)) (z : Fin n → K) :
    (affineChart i).symm.trans (affineChart j) z =
      fun k ↦ Fin.insertNth (α := fun _ ↦ K) i 1 z (j.succAbove k) /
        Fin.insertNth (α := fun _ ↦ K) i 1 z j :=
  (rfl)

end Projectivization
