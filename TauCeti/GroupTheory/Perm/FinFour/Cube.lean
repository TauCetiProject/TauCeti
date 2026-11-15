/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Monomial
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.InformationTheory.Coding.Equivalence

/-!
# The symmetric group on four letters as the rotation group of the cube

The rotations of the cube `[-1, 1]³` are the determinant-one signed permutation matrices: the
matrices in `SL(3, ℤ)` whose `j`-th column is `±e_{σ j}` for a permutation `σ` of the coordinates.
Their entries are integers, and they act on `ℝ³` through `ℤ ⊆ ℝ`. This file constructs that group,
its actions on the eight vertices `X = {-1, 1}³` and on the twelve edges of the cube, and the
classical isomorphism with `S₄ = Equiv.Perm (Fin 4)` given by the permutation of the four body
diagonals.

A vertex is a function `Fin 3 → ℤˣ`, a rotation `A` sends it to `A v`, and an edge is an unordered
pair of vertices differing in exactly one coordinate. The four body diagonals are the lines through
`±(1, 1, 1)`, `±(1, -1, -1)`, `±(-1, 1, -1)` and `±(-1, -1, 1)`, labelled `0, 1, 2, 3` in that
order. A rotation commutes with `v ↦ -v`, so it permutes the diagonals; a rotation fixing every
diagonal is the identity (this uses the determinant: `-1` fixes every diagonal), and the
permutations induced by a face quarter-turn and an edge half-turn generate `S₄`.

The four named rotations below represent the four nontrivial conjugacy classes of `S₄`: a half-turn
about the axis through two opposite edge midpoints induces a transposition, a half-turn about the
axis through two opposite face centres a double transposition, a third-turn about a body diagonal a
`3`-cycle, and a quarter-turn about a face axis a `4`-cycle.

## Main definitions

* `TauCeti.cubeRotationGroup`: the determinant-one signed permutation matrices, a subgroup of
  `SL(3, ℤ)`, acting on the vertices `Fin 3 → ℤˣ`.
* `TauCeti.cubeEdgeSet`: the twelve edges, as unordered pairs of vertices at Hamming distance one,
  with the induced action of `TauCeti.cubeRotationGroup`.
* `TauCeti.cubeBodyDiagonal`, `TauCeti.cubeBodyDiagonalIndex`: the labelled diagonals and the label
  of the diagonal through a vertex.
* `TauCeti.cubeBodyDiagonalHom`: the permutation of the body diagonals induced by a rotation.
* `TauCeti.cubeRotationEquiv`: the isomorphism of the rotation group with `S₄`.
* `TauCeti.cubeEdgeHalfTurn`, `TauCeti.cubeFaceHalfTurn`, `TauCeti.cubeDiagonalThirdTurn`,
  `TauCeti.cubeFaceQuarterTurn`: the four rotations above.

## Main results

* `TauCeti.cubeBodyDiagonalHom_injective`, `TauCeti.cubeBodyDiagonalHom_surjective`: the induced
  permutation of the diagonals is an isomorphism.
* `TauCeti.cubeBodyDiagonalHom_cubeEdgeHalfTurn` and its three companions: the permutations of the
  diagonals induced by the four named rotations.
* `TauCeti.natCard_fixed_cubeVertex_cubeEdgeHalfTurn`,
  `TauCeti.natCard_fixed_cubeEdgeSet_cubeEdgeHalfTurn` and their companions: the numbers of
  vertices and edges fixed by the four named rotations, `0, 0, 2, 0` and `2, 0, 0, 0`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv Matrix

/-! ### The rotation group -/

/-- **The rotation group of the cube** `[-1, 1]³`: the matrices of `SL(3, ℤ)` acting on `ℤ³` as
monomial transformations, that is, the determinant-one signed permutation matrices, whose `j`-th
column is `ε j • e_{σ j}` for a permutation `σ` of the coordinates and signs `ε : Fin 3 → ℤˣ`. -/
def cubeRotationGroup : Subgroup (SpecialLinearGroup (Fin 3) ℤ) :=
  (monomialGroup ℤ (Fin 3)).comap SpecialLinearGroup.toLin'

/-- A matrix of `SL(3, ℤ)` is a rotation of the cube exactly when it is a signed permutation
matrix. -/
theorem mem_cubeRotationGroup_iff {A : SpecialLinearGroup (Fin 3) ℤ} :
    A ∈ cubeRotationGroup ↔ ∃ σ : Perm (Fin 3), ∃ ε : Fin 3 → ℤˣ,
      ∀ i j, A i j = if σ j = i then (ε j : ℤ) else 0 := by
  -- `A` acts as `monomialEquiv ε σ` exactly when it is the matrix of `monomialEquiv ε σ`.
  have key (ε : Fin 3 → ℤˣ) (σ : Perm (Fin 3)) : monomialEquiv ε σ = SpecialLinearGroup.toLin' A ↔
      ∀ i j, A i j = if σ j = i then (ε j : ℤ) else 0 := by
    rw [eq_comm, ← LinearEquiv.toLinearMap_inj, SpecialLinearGroup.toLin'_to_linearMap,
      ← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_toLin', ← Matrix.ext_iff]
    simp only [toMatrix'_monomialEquiv]
  simp only [cubeRotationGroup, Subgroup.mem_comap, mem_monomialGroup, key]
  exact exists_comm

/-- A rotation of the cube acts on `ℤ³` as a monomial transformation. -/
theorem exists_monomialEquiv_eq_of_mem_cubeRotationGroup {A : SpecialLinearGroup (Fin 3) ℤ}
    (hA : A ∈ cubeRotationGroup) :
    ∃ (ε : Fin 3 → ℤˣ) (σ : Perm (Fin 3)), monomialEquiv ε σ = SpecialLinearGroup.toLin' A :=
  mem_monomialGroup.mp (Subgroup.mem_comap.mp hA)

/-- A rotation of the cube sends a vertex to a vertex: the coordinates of `A v` are signs. -/
theorem mulVec_mul_self_of_mem_cubeRotationGroup {A : SpecialLinearGroup (Fin 3) ℤ}
    (hA : A ∈ cubeRotationGroup) (v : Fin 3 → ℤˣ) (i : Fin 3) :
    (A *ᵥ fun j ↦ (v j : ℤ)) i * (A *ᵥ fun j ↦ (v j : ℤ)) i = 1 := by
  obtain ⟨ε, σ, h⟩ := exists_monomialEquiv_eq_of_mem_cubeRotationGroup hA
  rw [← Matrix.toLin'_apply, ← SpecialLinearGroup.toLin'_apply, ← h, monomialEquiv_apply,
    ← Units.val_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- The rotation group of the cube acts on the vertices `{-1, 1}³ = Fin 3 → ℤˣ` by matrix
multiplication. -/
instance : SMul cubeRotationGroup (Fin 3 → ℤˣ) where
  smul A v i :=
    ⟨((A.1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ fun j ↦ (v j : ℤ)) i,
      ((A.1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ fun j ↦ (v j : ℤ)) i,
      mulVec_mul_self_of_mem_cubeRotationGroup A.2 v i,
      mulVec_mul_self_of_mem_cubeRotationGroup A.2 v i⟩

/-- The coordinates of `A • v` are those of the matrix product `A v`. -/
@[simp]
theorem coe_cubeRotationGroup_smul_apply (A : cubeRotationGroup) (v : Fin 3 → ℤˣ) (i : Fin 3) :
    ((A • v) i : ℤ) = ((A.1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ fun j ↦ (v j : ℤ)) i :=
  (rfl)

/-- A rotation acting on `ℤ³` as the monomial transformation with signs `ε` and coordinate
permutation `σ` moves coordinate `σ⁻¹ i` of a vertex to coordinate `i`, with sign `ε (σ⁻¹ i)`. -/
theorem cubeRotationGroup_smul_apply_of_monomialEquiv {A : cubeRotationGroup}
    {ε : Fin 3 → ℤˣ} {σ : Perm (Fin 3)} (h : monomialEquiv ε σ = SpecialLinearGroup.toLin' A.1)
    (v : Fin 3 → ℤˣ) (i : Fin 3) : (A • v) i = ε (σ.symm i) * v (σ.symm i) :=
  Units.ext <| by
    rw [coe_cubeRotationGroup_smul_apply, ← Matrix.toLin'_apply, ← SpecialLinearGroup.toLin'_apply,
      ← h, monomialEquiv_apply, Units.val_mul]

instance : MulAction cubeRotationGroup (Fin 3 → ℤˣ) where
  one_smul v := funext fun i ↦ Units.ext <| by simp
  mul_smul A B v := funext fun i ↦ Units.ext <| by simp [Matrix.mulVec_mulVec]

/-- A rotation is linear, so it commutes with the antipodal map. -/
@[simp]
theorem cubeRotationGroup_smul_neg (A : cubeRotationGroup) (v : Fin 3 → ℤˣ) :
    A • -v = -(A • v) := by
  funext i
  refine Units.ext ?_
  have hv : (fun j ↦ ((-v) j : ℤ)) = -fun j ↦ (v j : ℤ) := funext fun j ↦ by simp
  rw [coe_cubeRotationGroup_smul_apply, hv, Matrix.mulVec_neg, Pi.neg_apply, Pi.neg_apply,
    Units.val_neg, coe_cubeRotationGroup_smul_apply]

/-- A rotation preserves the Hamming distance between vertices: it permutes the coordinates and
changes their signs. -/
@[simp]
theorem hammingDist_cubeRotationGroup_smul (A : cubeRotationGroup) (v w : Fin 3 → ℤˣ) :
    hammingDist (A • v) (A • w) = hammingDist v w := by
  obtain ⟨ε, σ, h⟩ := exists_monomialEquiv_eq_of_mem_cubeRotationGroup A.2
  have hval (u : Fin 3 → ℤˣ) :
      (fun i ↦ ((A • u) i : ℤ)) = monomialEquiv ε σ (fun i ↦ (u i : ℤ)) := by
    funext i
    rw [cubeRotationGroup_smul_apply_of_monomialEquiv h, Units.val_mul, monomialEquiv_apply]
  rw [← hammingDist_comp (fun _ ↦ Units.val) (fun _ ↦ Units.val_injective) (x := A • v),
    ← hammingDist_comp (fun _ ↦ Units.val) (fun _ ↦ Units.val_injective) (x := v), hval, hval,
    hammingDist_monomialEquiv]

/-! ### The edges -/

/-- **The twelve edges of the cube**: the unordered pairs of vertices differing in exactly one
coordinate. -/
def cubeEdgeSet : Set (Sym2 (Fin 3 → ℤˣ)) :=
  Sym2.fromRel (r := fun v w : Fin 3 → ℤˣ ↦ hammingDist v w = 1)
    ⟨fun v w h ↦ (hammingDist_comm w v).trans h⟩

/-- `s(v, w)` is an edge exactly when `v` and `w` differ in exactly one coordinate. -/
@[simp]
theorem mk_mem_cubeEdgeSet {v w : Fin 3 → ℤˣ} : s(v, w) ∈ cubeEdgeSet ↔ hammingDist v w = 1 :=
  Sym2.fromRel_prop

/-- Membership in `TauCeti.cubeEdgeSet` is decidable, which lets the edge counts below be
computed. -/
private instance : DecidablePred (· ∈ cubeEdgeSet) := by
  unfold cubeEdgeSet
  infer_instance

/-- A rotation sends an edge to an edge. -/
theorem map_smul_mem_cubeEdgeSet (A : cubeRotationGroup) {e : Sym2 (Fin 3 → ℤˣ)}
    (he : e ∈ cubeEdgeSet) : e.map (A • ·) ∈ cubeEdgeSet := by
  induction e using Sym2.ind with
  | _ v w =>
    rw [Sym2.map_mk, mk_mem_cubeEdgeSet, hammingDist_cubeRotationGroup_smul]
    exact mk_mem_cubeEdgeSet.mp he

/-- The rotation group of the cube acts on its edges. -/
instance : SMul cubeRotationGroup cubeEdgeSet where
  smul A e := ⟨e.1.map (A • ·), map_smul_mem_cubeEdgeSet A e.2⟩

/-- A rotation moves an edge by moving its two endpoints. -/
@[simp]
theorem coe_cubeRotationGroup_smul_cubeEdgeSet (A : cubeRotationGroup) (e : cubeEdgeSet) :
    ((A • e : cubeEdgeSet) : Sym2 (Fin 3 → ℤˣ)) = (e : Sym2 (Fin 3 → ℤˣ)).map (A • ·) :=
  (rfl)

instance : MulAction cubeRotationGroup cubeEdgeSet where
  one_smul e := Subtype.ext <| by
    rw [coe_cubeRotationGroup_smul_cubeEdgeSet]
    simp only [one_smul]
    exact congrFun Sym2.map_id' e.1
  mul_smul A B e := Subtype.ext <| by
    simp only [coe_cubeRotationGroup_smul_cubeEdgeSet, Sym2.map_map]
    congr 1
    funext v
    exact mul_smul A B v

/-! ### The body diagonals -/

/-- **The four body diagonals of the cube**, each recorded by its endpoint whose coordinates have
product `1`: `(1, 1, 1)`, `(1, -1, -1)`, `(-1, 1, -1)` and `(-1, -1, 1)`. -/
def cubeBodyDiagonal : Fin 4 → Fin 3 → ℤˣ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- The label of the body diagonal through a vertex, read off from which coordinates agree. -/
def cubeBodyDiagonalIndex (v : Fin 3 → ℤˣ) : Fin 4 :=
  if v 1 = v 2 then (if v 0 = v 2 then 0 else 1) else (if v 0 = v 2 then 2 else 3)

/-- The vertex `v` lies on the body diagonal `k` exactly when `v = ±cubeBodyDiagonal k`. -/
theorem cubeBodyDiagonalIndex_eq_iff {v : Fin 3 → ℤˣ} {k : Fin 4} :
    cubeBodyDiagonalIndex v = k ↔ v = cubeBodyDiagonal k ∨ v = -cubeBodyDiagonal k := by
  revert v k
  decide

/-- Antipodal vertices lie on the same body diagonal. -/
@[simp]
theorem cubeBodyDiagonalIndex_neg (v : Fin 3 → ℤˣ) :
    cubeBodyDiagonalIndex (-v) = cubeBodyDiagonalIndex v := by
  revert v
  decide

/-- The endpoint `cubeBodyDiagonal k` lies on the body diagonal `k`. -/
@[simp]
theorem cubeBodyDiagonalIndex_cubeBodyDiagonal (k : Fin 4) :
    cubeBodyDiagonalIndex (cubeBodyDiagonal k) = k :=
  cubeBodyDiagonalIndex_eq_iff.mpr (Or.inl rfl)

/-- The diagonal through `A • v` depends only on the diagonal through `v`. -/
theorem cubeBodyDiagonalIndex_smul (A : cubeRotationGroup) (v : Fin 3 → ℤˣ) :
    cubeBodyDiagonalIndex (A • v) =
      cubeBodyDiagonalIndex (A • cubeBodyDiagonal (cubeBodyDiagonalIndex v)) := by
  rcases cubeBodyDiagonalIndex_eq_iff.mp (rfl : cubeBodyDiagonalIndex v = _) with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h, cubeRotationGroup_smul_neg, cubeBodyDiagonalIndex_neg]

/-- **The permutation of the body diagonals induced by a rotation of the cube.** -/
def cubeBodyDiagonalHom : cubeRotationGroup →* Perm (Fin 4) where
  toFun A :=
    { toFun k := cubeBodyDiagonalIndex (A • cubeBodyDiagonal k)
      invFun k := cubeBodyDiagonalIndex (A⁻¹ • cubeBodyDiagonal k)
      left_inv k := by
        dsimp only
        rw [← cubeBodyDiagonalIndex_smul, inv_smul_smul, cubeBodyDiagonalIndex_cubeBodyDiagonal]
      right_inv k := by
        dsimp only
        rw [← cubeBodyDiagonalIndex_smul, smul_inv_smul, cubeBodyDiagonalIndex_cubeBodyDiagonal] }
  map_one' := Equiv.ext fun k ↦ by simp
  map_mul' A B := Equiv.ext fun k ↦ by
    simp only [Equiv.coe_fn_mk, Perm.coe_mul, Function.comp_apply, mul_smul]
    exact cubeBodyDiagonalIndex_smul A _

/-- A rotation sends the body diagonal `k` to the diagonal `cubeBodyDiagonalHom A k`. -/
theorem cubeBodyDiagonalHom_apply (A : cubeRotationGroup) (k : Fin 4) :
    cubeBodyDiagonalHom A k = cubeBodyDiagonalIndex (A • cubeBodyDiagonal k) :=
  (rfl)

/-- A rotation sends the body diagonal through `v` to the body diagonal through `A • v`. -/
@[simp]
theorem cubeBodyDiagonalHom_apply_cubeBodyDiagonalIndex (A : cubeRotationGroup)
    (v : Fin 3 → ℤˣ) :
    cubeBodyDiagonalHom A (cubeBodyDiagonalIndex v) = cubeBodyDiagonalIndex (A • v) :=
  (cubeBodyDiagonalIndex_smul A v).symm

/-- **A rotation fixing every body diagonal is the identity.** The determinant condition is
needed: the antipodal map `-1` fixes every diagonal. -/
theorem cubeBodyDiagonalHom_injective : Function.Injective cubeBodyDiagonalHom := by
  refine (injective_iff_map_eq_one _).mpr fun A hA ↦ ?_
  obtain ⟨ε, σ, h⟩ := exists_monomialEquiv_eq_of_mem_cubeRotationGroup A.2
  have hfix : ∀ k, cubeBodyDiagonalIndex (fun i ↦ ε (σ.symm i) * cubeBodyDiagonal k (σ.symm i)) =
      k := fun k ↦ by
    rw [← funext (cubeRotationGroup_smul_apply_of_monomialEquiv h (cubeBodyDiagonal k))]
    exact DFunLike.congr_fun hA k
  -- A finite check: only the signed permutations `1` and `-1` fix the four body diagonals.
  obtain ⟨rfl, rfl | rfl⟩ := (by decide : ∀ (σ : Perm (Fin 3)) (ε : Fin 3 → ℤˣ),
    (∀ k, cubeBodyDiagonalIndex (fun i ↦ ε (σ.symm i) * cubeBodyDiagonal k (σ.symm i)) = k) →
      σ = 1 ∧ (ε = 1 ∨ ε = -1)) σ ε hfix
  · refine Subtype.ext (SpecialLinearGroup.toLin'_injective ?_)
    rw [← h, OneMemClass.coe_one, map_one]
    exact LinearEquiv.ext fun x ↦ funext fun i ↦ by simp [← Perm.inv_def]
  · -- The antipodal map `-1` has determinant `-1`, so it is not in `SL(3, ℤ)`.
    have hA1 : (A.1 : Matrix (Fin 3) (Fin 3) ℤ) = -1 := by
      rw [← LinearMap.toMatrix'_toLin' (A.1 : Matrix (Fin 3) (Fin 3) ℤ),
        ← SpecialLinearGroup.toLin'_to_linearMap, ← h]
      ext i j
      rw [toMatrix'_monomialEquiv]
      simp [Matrix.one_apply, eq_comm, apply_ite Neg.neg]
    have hdet := A.1.2
    rw [hA1, Matrix.det_neg, Matrix.det_one] at hdet
    simp at hdet

/-! ### Four rotations -/

/-- **The half-turn about the axis through the midpoints of two opposite edges**, the edges with
midpoints `±(0, 1, 1)`: `(x, y, z) ↦ (-x, z, y)`. -/
def cubeEdgeHalfTurn : cubeRotationGroup :=
  ⟨⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩,
    mem_cubeRotationGroup_iff.mpr
      ⟨swap 1 2, ![-1, 1, 1], fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl⟩⟩

/-- **The half-turn about the axis through two opposite face centres**, the first coordinate axis:
`(x, y, z) ↦ (x, -y, -z)`. -/
def cubeFaceHalfTurn : cubeRotationGroup :=
  ⟨⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩,
    mem_cubeRotationGroup_iff.mpr
      ⟨1, ![1, -1, -1], fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl⟩⟩

/-- **The third-turn about a body diagonal**, the diagonal through `(-1, -1, 1)`:
`(x, y, z) ↦ (y, -z, -x)`. -/
def cubeDiagonalThirdTurn : cubeRotationGroup :=
  ⟨⟨!![0, 1, 0; 0, 0, -1; -1, 0, 0], by simp [Matrix.det_fin_three]⟩,
    mem_cubeRotationGroup_iff.mpr
      ⟨[0, 2, 1].formPerm, ![-1, 1, -1], fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl⟩⟩

/-- **The quarter-turn about the axis through two opposite face centres**, the second coordinate
axis: `(x, y, z) ↦ (-z, y, x)`. -/
def cubeFaceQuarterTurn : cubeRotationGroup :=
  ⟨⟨!![0, 0, -1; 0, 1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩,
    mem_cubeRotationGroup_iff.mpr
      ⟨swap 0 2, ![1, 1, -1], fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl⟩⟩

/-- The edge half-turn exchanges the diagonals `0` and `1` and fixes the other two. -/
@[simp]
theorem cubeBodyDiagonalHom_cubeEdgeHalfTurn : cubeBodyDiagonalHom cubeEdgeHalfTurn = swap 0 1 := by
  decide

/-- The face half-turn exchanges the diagonals `0 ↔ 1` and `2 ↔ 3`. -/
@[simp]
theorem cubeBodyDiagonalHom_cubeFaceHalfTurn :
    cubeBodyDiagonalHom cubeFaceHalfTurn = swap 0 1 * swap 2 3 := by
  decide

/-- The diagonal third-turn cycles the diagonals `0 → 1 → 2 → 0` and fixes its axis `3`. -/
@[simp]
theorem cubeBodyDiagonalHom_cubeDiagonalThirdTurn :
    cubeBodyDiagonalHom cubeDiagonalThirdTurn = [0, 1, 2].formPerm := by
  decide

/-- The face quarter-turn cycles the diagonals `0 → 1 → 2 → 3 → 0`. -/
@[simp]
theorem cubeBodyDiagonalHom_cubeFaceQuarterTurn :
    cubeBodyDiagonalHom cubeFaceQuarterTurn = [0, 1, 2, 3].formPerm := by
  decide

/-- **Every permutation of the body diagonals comes from a rotation**: the `4`-cycle of the face
quarter-turn and the transposition of the edge half-turn generate `S₄`. -/
theorem cubeBodyDiagonalHom_surjective : Function.Surjective cubeBodyDiagonalHom := by
  have hnodup : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
  have hcycle : ([0, 1, 2, 3] : List (Fin 4)).formPerm.IsCycle :=
    List.isCycle_formPerm hnodup (by decide)
  have hsupp : ([0, 1, 2, 3] : List (Fin 4)).formPerm.support = Finset.univ := by
    rw [List.support_formPerm_of_nodup _ hnodup (by simp)]
    decide
  have htop := Perm.closure_cycle_adjacent_swap hcycle hsupp 0
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop, Subgroup.closure_le]
  rintro τ (rfl | rfl)
  · exact ⟨cubeFaceQuarterTurn, cubeBodyDiagonalHom_cubeFaceQuarterTurn⟩
  · exact ⟨cubeEdgeHalfTurn, by rw [cubeBodyDiagonalHom_cubeEdgeHalfTurn]; decide⟩

/-- **The rotation group of the cube is `S₄`**, through its permutation of the four body
diagonals. -/
noncomputable def cubeRotationEquiv : cubeRotationGroup ≃* Perm (Fin 4) :=
  MulEquiv.ofBijective cubeBodyDiagonalHom
    ⟨cubeBodyDiagonalHom_injective, cubeBodyDiagonalHom_surjective⟩

/-- The isomorphism with `S₄` is the permutation of the body diagonals. -/
@[simp]
theorem cubeRotationEquiv_apply (A : cubeRotationGroup) :
    cubeRotationEquiv A = cubeBodyDiagonalHom A :=
  (rfl)

/-- The rotation inducing the transposition `(01)` of the diagonals is the edge half-turn. -/
@[simp]
theorem cubeRotationEquiv_symm_swap_zero_one :
    cubeRotationEquiv.symm (swap 0 1) = cubeEdgeHalfTurn :=
  cubeRotationEquiv.symm_apply_eq.mpr cubeBodyDiagonalHom_cubeEdgeHalfTurn.symm

/-- The rotation inducing `(01)(23)` is the face half-turn. -/
@[simp]
theorem cubeRotationEquiv_symm_swap_zero_one_mul_swap_two_three :
    cubeRotationEquiv.symm (swap 0 1 * swap 2 3) = cubeFaceHalfTurn :=
  cubeRotationEquiv.symm_apply_eq.mpr cubeBodyDiagonalHom_cubeFaceHalfTurn.symm

/-- The rotation inducing `(012)` is the diagonal third-turn. -/
theorem cubeRotationEquiv_symm_formPerm_zero_one_two :
    cubeRotationEquiv.symm [0, 1, 2].formPerm = cubeDiagonalThirdTurn :=
  cubeRotationEquiv.symm_apply_eq.mpr cubeBodyDiagonalHom_cubeDiagonalThirdTurn.symm

/-- The rotation inducing `(0123)` is the face quarter-turn. -/
theorem cubeRotationEquiv_symm_formPerm_zero_one_two_three :
    cubeRotationEquiv.symm [0, 1, 2, 3].formPerm = cubeFaceQuarterTurn :=
  cubeRotationEquiv.symm_apply_eq.mpr cubeBodyDiagonalHom_cubeFaceQuarterTurn.symm

/-! ### Fixed vertices and edges -/

/-- The cube has `12` edges. -/
theorem natCard_cubeEdgeSet : Nat.card cubeEdgeSet = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The edge half-turn fixes no vertex. -/
theorem natCard_fixed_cubeVertex_cubeEdgeHalfTurn :
    Nat.card {v : Fin 3 → ℤˣ // cubeEdgeHalfTurn • v = v} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The edge half-turn fixes the two edges its axis passes through. -/
theorem natCard_fixed_cubeEdgeSet_cubeEdgeHalfTurn :
    Nat.card {e : cubeEdgeSet // cubeEdgeHalfTurn • e = e} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The face half-turn fixes no vertex. -/
theorem natCard_fixed_cubeVertex_cubeFaceHalfTurn :
    Nat.card {v : Fin 3 → ℤˣ // cubeFaceHalfTurn • v = v} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The face half-turn fixes no edge. -/
theorem natCard_fixed_cubeEdgeSet_cubeFaceHalfTurn :
    Nat.card {e : cubeEdgeSet // cubeFaceHalfTurn • e = e} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The diagonal third-turn fixes the two endpoints of its axis. -/
theorem natCard_fixed_cubeVertex_cubeDiagonalThirdTurn :
    Nat.card {v : Fin 3 → ℤˣ // cubeDiagonalThirdTurn • v = v} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The diagonal third-turn fixes no edge. -/
theorem natCard_fixed_cubeEdgeSet_cubeDiagonalThirdTurn :
    Nat.card {e : cubeEdgeSet // cubeDiagonalThirdTurn • e = e} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The face quarter-turn fixes no vertex. -/
theorem natCard_fixed_cubeVertex_cubeFaceQuarterTurn :
    Nat.card {v : Fin 3 → ℤˣ // cubeFaceQuarterTurn • v = v} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The face quarter-turn fixes no edge. -/
theorem natCard_fixed_cubeEdgeSet_cubeFaceQuarterTurn :
    Nat.card {e : cubeEdgeSet // cubeFaceQuarterTurn • e = e} = 0 := by
  rw [Nat.card_eq_fintype_card]
  decide

end TauCeti
