/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import Mathlib.Data.Fintype.Sum
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The group of a standard quadratic equation with coefficients as a surface amalgam

Let `S` be the standard quadratic equation
`[x₁, y₁] ⋯ [xₙ, yₙ] z₁⁻¹ c₁ z₁ ⋯ z_m⁻¹ c_m z_m d = 1` of type (2) over a group `G`, all of whose
variables occur. Its group `G_S = G[X] ⧸ ncl(S)` is obtained from the free product of `G` with the
orientable surface group `S⁺(n, m + 1)` by adding stable letters `z₁, …, z_m` conjugating `cⱼ` to
the peripheral element `pⱼ`, and identifying the last peripheral element `p_{m+1}` with `d`. The
same holds for the equation `x₁² ⋯ xₙ² z₁⁻¹ c₁ z₁ ⋯ z_m⁻¹ c_m z_m d = 1` of type (4) with the
nonorientable surface group `S⁻(n, m + 1)`. When `c₁, …, c_m, d` have infinite order (for instance
when `G` is torsion-free), this is the presentation, relative to the maximal tree consisting of the
edge of `d`, of the fundamental group of the graph of groups with vertex groups `G` and the surface
group and `m + 1` infinite cyclic edge groups, one for each of `c₁, …, c_m, d`; this
identification is not made here.

The presentation is written as the group of a system of equations over `G ∗ L`, for a group `L`
with distinguished elements `p₁, …, p_{m+1}`: the boundary system `zⱼ⁻¹ cⱼ zⱼ = pⱼ` (`j ≤ m`),
`d = p_{m+1}` in the variables `z₁, …, z_m`. The isomorphisms are Tietze transformations: the
relator of `S` is the surface relator in which the peripheral elements are replaced by
`zⱼ⁻¹ cⱼ zⱼ` and `d`. They hold over every group `G`; no consistency or regularity of `S` is
needed.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.boundarySystem c d p`: the boundary system over `G ∗ L`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableCoeffSystemGroupEquiv`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.nonorientableCoeffSystemGroupEquiv`: the isomorphisms of
  the groups of the standard equations of types (2) and (4), all of whose variables occur, with the
  groups of the boundary systems over `G ∗ S⁺(n, m + 1)` and `G ∗ S⁻(n, m + 1)`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.mem_V_boundarySystem_iff`: the solutions of the boundary system;
  `TauCeti.GroupAlgGeom.Quadratic.boundarySystem_conj` and
  `TauCeti.GroupAlgGeom.Quadratic.boundarySystem_constant`: its relations in the group of the
  system.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableCoeffSystemGroupEquiv_mk_inr_of_x` and the
  other `_mk_…` and `_symm_mk_…` lemmas: the values of the isomorphisms on generators; in
  particular the peripheral element `pⱼ` corresponds to `zⱼ⁻¹ cⱼ zⱼ` and `p_{m+1}` to `d`.
* `TauCeti.GroupAlgGeom.Quadratic.exists_mulEquiv_amalgam_commutator`: over `F(a, b)`, the group of
  `[x, y][a, b]⁻¹ = 1` is the amalgamated product `F(a, b) ∗_{[a, b]⁻¹ = p} S⁺(1, 1)`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 3 (the standard quadratic equations).
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Proposition 1 and its proof (groups of standard quadratic equations identified through their
  presentations).
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

open SurfaceGroup

variable {G X : Type*} [Group G]

/-! ### The boundary system -/

section BoundarySystem

variable {L : Type*} [Group L] {m : ℕ}

/-- The boundary system: the equations `zⱼ⁻¹ cⱼ zⱼ = pⱼ` (`j ≤ m`) and `d = p_{m+1}` over the
free product `G ∗ L`, in the variables `z₁, …, z_m`, attaching a group `L` with distinguished
elements `p₁, …, p_{m+1}` to `G` along the elements `c₁, …, c_m, d`. -/
def boundarySystem (c : Fin m → G) (d : G) (p : Fin (m + 1) → L) :
    Set (GX (Monoid.Coprod G L) (Fin m)) :=
  (Set.range fun j : Fin m ↦
      (inr (FreeGroup.of j) : GX (Monoid.Coprod G L) (Fin m))⁻¹ * inl (inl (c j)) *
        inr (FreeGroup.of j) * (inl (inr (p j.castSucc)) : GX (Monoid.Coprod G L) (Fin m))⁻¹) ∪
    {(inl (inl d) : GX (Monoid.Coprod G L) (Fin m)) *
      (inl (inr (p (Fin.last m))) : GX (Monoid.Coprod G L) (Fin m))⁻¹}

/-- A point `t` solves the boundary system when `tⱼ` conjugates `cⱼ` to `pⱼ` for every `j ≤ m`
and `d = p_{m+1}`. -/
theorem mem_V_boundarySystem_iff {H : Type*} [Group H] {c : Fin m → G} {d : G}
    {p : Fin (m + 1) → L} {ι : Monoid.Coprod G L →* H} {t : Fin m → H} :
    t ∈ V ι (boundarySystem c d p) ↔
      (∀ j, (t j)⁻¹ * ι (inl (c j)) * t j = ι (inr (p j.castSucc))) ∧
        ι (inl d) = ι (inr (p (Fin.last m))) := by
  -- Squeezed for speed: the bare `simp` needs `and_comm` to reorder the conjuncts and takes
  -- several seconds.
  simp only [boundarySystem, mem_V, Set.forall_mem_union, Set.forall_mem_range,
    Set.forall_mem_singleton, map_mul, map_inv, eval_inl, eval_inr_of, mul_inv_eq_one]

variable (c : Fin m → G) (d : G) (p : Fin (m + 1) → L)

/-- In the group of the boundary system, the variable `zⱼ` conjugates `cⱼ` to `pⱼ`. -/
theorem boundarySystem_conj (j : Fin m) :
    ((inr (FreeGroup.of j) : GX (Monoid.Coprod G L) (Fin m)) :
        SystemGroup _ (boundarySystem c d p))⁻¹ *
      ((inl (inl (c j)) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) *
        ((inr (FreeGroup.of j) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) =
      ((inl (inr (p j.castSucc)) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) := by
  simpa using (mem_V_boundarySystem_iff.1 (SystemGroup.homEquiv _ _ (GHom.id _)).2).1 j

/-- In the group of the boundary system, the constant `d` is the last distinguished element. -/
theorem boundarySystem_constant :
    ((inl (inl d) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ (boundarySystem c d p)) =
      ((inl (inr (p (Fin.last m))) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) := by
  simpa using (mem_V_boundarySystem_iff.1 (SystemGroup.homEquiv _ _ (GHom.id _)).2).2

-- In the group of the boundary system, the conjugates `zⱼ⁻¹ cⱼ zⱼ` followed by `d` are the
-- distinguished elements `p`.
private theorem snoc_eq_boundarySystem :
    Fin.snoc (α := fun _ ↦ SystemGroup _ (boundarySystem c d p))
        (fun j ↦ ((inr (FreeGroup.of j) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _)⁻¹ *
          ((inl (inl (c j)) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) *
            ((inr (FreeGroup.of j) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _))
        ((inl (inl d) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) =
      fun j ↦ ((inl (inr (p j)) : GX (Monoid.Coprod G L) (Fin m)) : SystemGroup _ _) := by
  ext j
  induction j using Fin.lastCases with
  | last => simpa using boundarySystem_constant c d p
  | cast j => simpa using boundarySystem_conj c d p j

end BoundarySystem

namespace Standard

variable {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

/-! ### Type (2): `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` -/

section OrientableCoeff

variable (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
  (surj : (Sum.elim (Sum.elim x y) z).Surjective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1)

-- The point of the boundary group at which `xᵢ`, `yᵢ`, `zⱼ` take the values `aᵢ`, `bᵢ`, `zⱼ`.
private noncomputable def orientableCoeffPoint (x y : Fin n → X) (z : Fin m → X) (c : Fin m → G)
    (d : G) : X → SystemGroup (Monoid.Coprod G (Orientable n (m + 1)))
      (boundarySystem c d (Orientable.peripheral n (m + 1))) :=
  Function.extend (Sum.elim (Sum.elim x y) z) (Sum.elim (Sum.elim
    (fun i ↦ ((inl (inr (Orientable.a n (m + 1) i)) :
      GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _))
    (fun i ↦ ((inl (inr (Orientable.b n (m + 1) i)) :
      GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _)))
    (fun j ↦ ((inr (FreeGroup.of j) :
      GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _))) 1

include inj in
private theorem orientableCoeffPoint_x (i : Fin n) :
    orientableCoeffPoint x y z c d (x i) =
      ((inl (inr (Orientable.a n (m + 1) i)) :
        GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) :=
  inj.extend_apply _ _ (Sum.inl (Sum.inl i))

include inj in
private theorem orientableCoeffPoint_y (i : Fin n) :
    orientableCoeffPoint x y z c d (y i) =
      ((inl (inr (Orientable.b n (m + 1) i)) :
        GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) :=
  inj.extend_apply _ _ (Sum.inl (Sum.inr i))

include inj in
private theorem orientableCoeffPoint_z (j : Fin m) :
    orientableCoeffPoint x y z c d (z j) =
      ((inr (FreeGroup.of j) :
        GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) :=
  inj.extend_apply _ _ (Sum.inr j)

private theorem orientableCoeffPoint_mem_V :
    orientableCoeffPoint x y z c d ∈ V ((SystemGroup.coeff _).comp inl)
      {(orientableCoeff n m hnm x y z inj c hc d hd).toWord} := by
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_orientableCoeff]
  simp only [orientableCoeffPoint_x inj, orientableCoeffPoint_y inj, orientableCoeffPoint_z inj,
    MonoidHom.comp_apply, SystemGroup.coeff_apply, snoc_eq_boundarySystem]
  simpa using (map_orientableWord ((SystemGroup.coeff
    (boundarySystem c d (Orientable.peripheral n (m + 1)))).comp inr)
    (Orientable.a n (m + 1)) (Orientable.b n (m + 1)) (Orientable.peripheral n (m + 1))).symm

-- Evaluation of the group of the equation at the point `orientableCoeffPoint`.
private noncomputable def orientableCoeffToBoundary :
    SystemGroup G {(orientableCoeff n m hnm x y z inj c hc d hd).toWord} →*
      SystemGroup (Monoid.Coprod G (Orientable n (m + 1)))
        (boundarySystem c d (Orientable.peripheral n (m + 1))) :=
  (SystemGroup.evalGHom _ (orientableCoeffPoint_mem_V hnm inj hc hd) : _ →* _)

private theorem orientableCoeffOfBoundary_mem_V :
    (fun j ↦ ((inr (FreeGroup.of (z j)) : GX G X) :
        SystemGroup G {(orientableCoeff n m hnm x y z inj c hc d hd).toWord})) ∈
      V (Monoid.Coprod.lift (SystemGroup.coeff _)
        (surfaceHomOrientableCoeff (SystemGroup.homEquiv _ _ (GHom.id (SystemGroup.coeff _))).2))
        (boundarySystem c d (Orientable.peripheral n (m + 1))) :=
  mem_V_boundarySystem_iff.2 <| by simp

-- The inverse of `orientableCoeffToBoundary`: the surface group goes to the group of the
-- equation by the homomorphism of the generic solution, and the variables `zⱼ` to `zⱼ`.
private noncomputable def orientableCoeffOfBoundary :
    SystemGroup (Monoid.Coprod G (Orientable n (m + 1)))
        (boundarySystem c d (Orientable.peripheral n (m + 1))) →*
      SystemGroup G {(orientableCoeff n m hnm x y z inj c hc d hd).toWord} :=
  (SystemGroup.evalGHom _ (orientableCoeffOfBoundary_mem_V hnm inj hc hd) : _ →* _)

include surj in
private theorem orientableCoeffOfBoundary_comp_toBoundary :
    (orientableCoeffOfBoundary hnm inj hc hd).comp (orientableCoeffToBoundary hnm inj hc hd) =
      MonoidHom.id _ := by
  ext w
  · simp [orientableCoeffOfBoundary, orientableCoeffToBoundary]
  · obtain ⟨(i | i) | j, rfl⟩ := surj w <;>
      simp [orientableCoeffOfBoundary, orientableCoeffToBoundary, orientableCoeffPoint_x inj,
        orientableCoeffPoint_y inj, orientableCoeffPoint_z inj]

private theorem orientableCoeffToBoundary_comp_ofBoundary :
    (orientableCoeffToBoundary hnm inj hc hd).comp (orientableCoeffOfBoundary hnm inj hc hd) =
      MonoidHom.id _ := by
  ext w
  · simp [orientableCoeffOfBoundary, orientableCoeffToBoundary]
  · simp [orientableCoeffOfBoundary, orientableCoeffToBoundary, orientableCoeffPoint_x inj]
  · simp [orientableCoeffOfBoundary, orientableCoeffToBoundary, orientableCoeffPoint_y inj]
  · induction w using Fin.lastCases with
    | last =>
      simpa [orientableCoeffOfBoundary, orientableCoeffToBoundary] using
        boundarySystem_constant c d (Orientable.peripheral n (m + 1))
    | cast j =>
      simpa [orientableCoeffOfBoundary, orientableCoeffToBoundary, orientableCoeffPoint_z inj] using
        boundarySystem_conj c d (Orientable.peripheral n (m + 1)) j
  · simp [orientableCoeffOfBoundary, orientableCoeffToBoundary, orientableCoeffPoint_z inj]

/-- The group of the standard quadratic equation `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (2), all
of whose variables occur, is the group of the boundary system over `G ∗ S⁺(n, m + 1)`: the
isomorphism is the identity on `G` and sends `xᵢ`, `yᵢ` to the generators `aᵢ`, `bᵢ` of the
surface group and `zⱼ` to the variable `zⱼ` of the boundary system. Its inverse sends the
peripheral elements `pⱼ` to `zⱼ⁻¹ cⱼ zⱼ` and the last one to `d`. -/
noncomputable def orientableCoeffSystemGroupEquiv :
    SystemGroup G {(orientableCoeff n m hnm x y z inj c hc d hd).toWord} ≃*
      SystemGroup (Monoid.Coprod G (Orientable n (m + 1)))
        (boundarySystem c d (Orientable.peripheral n (m + 1))) :=
  (orientableCoeffToBoundary hnm inj hc hd).toMulEquiv (orientableCoeffOfBoundary hnm inj hc hd)
    (orientableCoeffOfBoundary_comp_toBoundary hnm inj surj hc hd)
    (orientableCoeffToBoundary_comp_ofBoundary hnm inj hc hd)

@[simp]
theorem orientableCoeffSystemGroupEquiv_mk_inl (g : G) :
    orientableCoeffSystemGroupEquiv hnm inj surj hc hd ((inl g : GX G X) : SystemGroup G _) =
      ((inl (inl g) : GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffToBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_mk_inr_of_x (i : Fin n) :
    orientableCoeffSystemGroupEquiv hnm inj surj hc hd
        ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      ((inl (inr (Orientable.a n (m + 1) i)) :
        GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffToBoundary, orientableCoeffPoint_x inj]

@[simp]
theorem orientableCoeffSystemGroupEquiv_mk_inr_of_y (i : Fin n) :
    orientableCoeffSystemGroupEquiv hnm inj surj hc hd
        ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) =
      ((inl (inr (Orientable.b n (m + 1) i)) :
        GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffToBoundary, orientableCoeffPoint_y inj]

@[simp]
theorem orientableCoeffSystemGroupEquiv_mk_inr_of_z (j : Fin m) :
    orientableCoeffSystemGroupEquiv hnm inj surj hc hd
        ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) =
      ((inr (FreeGroup.of j) : GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) :
        SystemGroup _ _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffToBoundary, orientableCoeffPoint_z inj]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inl_inl (g : G) :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inl (inl g) : GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inl_inr_a (i : Fin n) :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inl (inr (Orientable.a n (m + 1) i)) :
          GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inl_inr_b (i : Fin n) :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inl (inr (Orientable.b n (m + 1) i)) :
          GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inl_inr_peripheral_castSucc (j : Fin m) :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inl (inr (Orientable.peripheral n (m + 1) j.castSucc)) :
          GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _)⁻¹ *
        ((inl (c j) : GX G X) : SystemGroup G _) *
          ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inl_inr_peripheral_last :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inl (inr (Orientable.peripheral n (m + 1) (Fin.last m))) :
          GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inl d : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

@[simp]
theorem orientableCoeffSystemGroupEquiv_symm_mk_inr_of (j : Fin m) :
    (orientableCoeffSystemGroupEquiv hnm inj surj hc hd).symm
        ((inr (FreeGroup.of j) : GX (Monoid.Coprod G (Orientable n (m + 1))) (Fin m)) :
          SystemGroup _ _) =
      ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) := by
  simp [orientableCoeffSystemGroupEquiv, orientableCoeffOfBoundary]

end OrientableCoeff

/-! ### Type (4): `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` -/

section NonorientableCoeff

variable {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
  (surj : (Sum.elim x z).Surjective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1)

-- The point of the boundary group at which `xᵢ`, `zⱼ` take the values `cᵢ`, `zⱼ`.
private noncomputable def nonorientableCoeffPoint (x : Fin n → X) (z : Fin m → X) (c : Fin m → G)
    (d : G) : X → SystemGroup (Monoid.Coprod G (Nonorientable n (m + 1)))
      (boundarySystem c d (Nonorientable.peripheral n (m + 1))) :=
  Function.extend (Sum.elim x z) (Sum.elim
    (fun i ↦ ((inl (inr (Nonorientable.c n (m + 1) i)) :
      GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _))
    (fun j ↦ ((inr (FreeGroup.of j) :
      GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _))) 1

include inj in
private theorem nonorientableCoeffPoint_x (i : Fin n) :
    nonorientableCoeffPoint x z c d (x i) =
      ((inl (inr (Nonorientable.c n (m + 1) i)) :
        GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) :=
  inj.extend_apply _ _ (Sum.inl i)

include inj in
private theorem nonorientableCoeffPoint_z (j : Fin m) :
    nonorientableCoeffPoint x z c d (z j) =
      ((inr (FreeGroup.of j) :
        GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) :=
  inj.extend_apply _ _ (Sum.inr j)

private theorem nonorientableCoeffPoint_mem_V :
    nonorientableCoeffPoint x z c d ∈ V ((SystemGroup.coeff _).comp inl)
      {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} := by
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_nonorientableCoeff]
  simp only [nonorientableCoeffPoint_x inj, nonorientableCoeffPoint_z inj, MonoidHom.comp_apply,
    SystemGroup.coeff_apply, snoc_eq_boundarySystem]
  simpa using (map_nonorientableWord ((SystemGroup.coeff
    (boundarySystem c d (Nonorientable.peripheral n (m + 1)))).comp inr)
    (Nonorientable.c n (m + 1)) (Nonorientable.peripheral n (m + 1))).symm

-- Evaluation of the group of the equation at the point `nonorientableCoeffPoint`.
private noncomputable def nonorientableCoeffToBoundary :
    SystemGroup G {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} →*
      SystemGroup (Monoid.Coprod G (Nonorientable n (m + 1)))
        (boundarySystem c d (Nonorientable.peripheral n (m + 1))) :=
  (SystemGroup.evalGHom _ (nonorientableCoeffPoint_mem_V hn inj hc hd) : _ →* _)

private theorem nonorientableCoeffOfBoundary_mem_V :
    (fun j ↦ ((inr (FreeGroup.of (z j)) : GX G X) :
        SystemGroup G {(nonorientableCoeff n m hn x z inj c hc d hd).toWord})) ∈
      V (Monoid.Coprod.lift (SystemGroup.coeff _)
        (surfaceHomNonorientableCoeff (SystemGroup.homEquiv _ _ (GHom.id (SystemGroup.coeff _))).2))
        (boundarySystem c d (Nonorientable.peripheral n (m + 1))) :=
  mem_V_boundarySystem_iff.2 <| by simp

-- The inverse of `nonorientableCoeffToBoundary`: the surface group goes to the group of the
-- equation by the homomorphism of the generic solution, and the variables `zⱼ` to `zⱼ`.
private noncomputable def nonorientableCoeffOfBoundary :
    SystemGroup (Monoid.Coprod G (Nonorientable n (m + 1)))
        (boundarySystem c d (Nonorientable.peripheral n (m + 1))) →*
      SystemGroup G {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} :=
  (SystemGroup.evalGHom _ (nonorientableCoeffOfBoundary_mem_V hn inj hc hd) : _ →* _)

include surj in
private theorem nonorientableCoeffOfBoundary_comp_toBoundary :
    (nonorientableCoeffOfBoundary hn inj hc hd).comp (nonorientableCoeffToBoundary hn inj hc hd) =
      MonoidHom.id _ := by
  ext w
  · simp [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary]
  · obtain ⟨i | j, rfl⟩ := surj w <;>
      simp [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary,
        nonorientableCoeffPoint_x inj, nonorientableCoeffPoint_z inj]

private theorem nonorientableCoeffToBoundary_comp_ofBoundary :
    (nonorientableCoeffToBoundary hn inj hc hd).comp (nonorientableCoeffOfBoundary hn inj hc hd) =
      MonoidHom.id _ := by
  ext w
  · simp [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary]
  · simp [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary, nonorientableCoeffPoint_x inj]
  · induction w using Fin.lastCases with
    | last =>
      simpa [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary] using
        boundarySystem_constant c d (Nonorientable.peripheral n (m + 1))
    | cast j =>
      simpa [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary,
        nonorientableCoeffPoint_z inj] using
        boundarySystem_conj c d (Nonorientable.peripheral n (m + 1)) j
  · simp [nonorientableCoeffOfBoundary, nonorientableCoeffToBoundary, nonorientableCoeffPoint_z inj]

/-- The group of the standard quadratic equation `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (4), all of
whose variables occur, is the group of the boundary system over `G ∗ S⁻(n, m + 1)`: the isomorphism
is the identity on `G` and sends `xᵢ` to the crosscap generator of index `i` of the surface group
and `zⱼ` to the variable `zⱼ` of the boundary system. Its inverse sends the peripheral elements
`pⱼ` to `zⱼ⁻¹ cⱼ zⱼ` and the last one to `d`. -/
noncomputable def nonorientableCoeffSystemGroupEquiv :
    SystemGroup G {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} ≃*
      SystemGroup (Monoid.Coprod G (Nonorientable n (m + 1)))
        (boundarySystem c d (Nonorientable.peripheral n (m + 1))) :=
  (nonorientableCoeffToBoundary hn inj hc hd).toMulEquiv (nonorientableCoeffOfBoundary hn inj hc hd)
    (nonorientableCoeffOfBoundary_comp_toBoundary hn inj surj hc hd)
    (nonorientableCoeffToBoundary_comp_ofBoundary hn inj hc hd)

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_mk_inl (g : G) :
    nonorientableCoeffSystemGroupEquiv hn inj surj hc hd ((inl g : GX G X) : SystemGroup G _) =
      ((inl (inl g) : GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) :
        SystemGroup _ _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffToBoundary]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_mk_inr_of_x (i : Fin n) :
    nonorientableCoeffSystemGroupEquiv hn inj surj hc hd
        ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      ((inl (inr (Nonorientable.c n (m + 1) i)) :
        GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffToBoundary,
    nonorientableCoeffPoint_x inj]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_mk_inr_of_z (j : Fin m) :
    nonorientableCoeffSystemGroupEquiv hn inj surj hc hd
        ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) =
      ((inr (FreeGroup.of j) : GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) :
        SystemGroup _ _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffToBoundary,
    nonorientableCoeffPoint_z inj]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_symm_mk_inl_inl (g : G) :
    (nonorientableCoeffSystemGroupEquiv hn inj surj hc hd).symm
        ((inl (inl g) : GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) :
          SystemGroup _ _) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffOfBoundary]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_symm_mk_inl_inr_c (i : Fin n) :
    (nonorientableCoeffSystemGroupEquiv hn inj surj hc hd).symm
        ((inl (inr (Nonorientable.c n (m + 1) i)) :
          GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffOfBoundary]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_symm_mk_inl_inr_peripheral_castSucc (j : Fin m) :
    (nonorientableCoeffSystemGroupEquiv hn inj surj hc hd).symm
        ((inl (inr (Nonorientable.peripheral n (m + 1) j.castSucc)) :
          GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _)⁻¹ *
        ((inl (c j) : GX G X) : SystemGroup G _) *
          ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffOfBoundary]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_symm_mk_inl_inr_peripheral_last :
    (nonorientableCoeffSystemGroupEquiv hn inj surj hc hd).symm
        ((inl (inr (Nonorientable.peripheral n (m + 1) (Fin.last m))) :
          GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) : SystemGroup _ _) =
      ((inl d : GX G X) : SystemGroup G _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffOfBoundary]

@[simp]
theorem nonorientableCoeffSystemGroupEquiv_symm_mk_inr_of (j : Fin m) :
    (nonorientableCoeffSystemGroupEquiv hn inj surj hc hd).symm
        ((inr (FreeGroup.of j) : GX (Monoid.Coprod G (Nonorientable n (m + 1))) (Fin m)) :
          SystemGroup _ _) =
      ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G _) := by
  simp [nonorientableCoeffSystemGroupEquiv, nonorientableCoeffOfBoundary]

end NonorientableCoeff

end Standard

/-! ### Example -/

section Example

open FreeGroup

/-- Over `F(a, b)`, the group of the equation `[x, y][a, b]⁻¹ = 1` is the amalgamated product
`F(a, b) ∗_{[a, b]⁻¹ = p} S⁺(1, 1)` of `F(a, b)` and the one-holed torus group, by an isomorphism
which is the identity on `F(a, b)` and sends `x`, `y` to the generators `a₁`, `b₁` of `S⁺(1, 1)`.
Here `[u, v] = u⁻¹ v⁻¹ u v`, Mathlib's `⁅u⁻¹, v⁻¹⁆`. -/
theorem exists_mulEquiv_amalgam_commutator :
    ∃ e : SystemGroup (FreeGroup (Fin 2))
        {⁅(inr (of 0) : GX (FreeGroup (Fin 2)) (Fin 2))⁻¹,
            (inr (of 1) : GX (FreeGroup (Fin 2)) (Fin 2))⁻¹⁆ *
          inl ⁅(of 0 : FreeGroup (Fin 2))⁻¹, (of 1 : FreeGroup (Fin 2))⁻¹⁆⁻¹} ≃*
        Monoid.Coprod (FreeGroup (Fin 2)) (Orientable 1 1) ⧸
          Subgroup.normalClosure
            {inl ⁅(of 0 : FreeGroup (Fin 2))⁻¹, (of 1 : FreeGroup (Fin 2))⁻¹⁆⁻¹ *
              (inr (Orientable.peripheral 1 1 0))⁻¹},
      (∀ g, e ((inl g : GX _ (Fin 2)) : SystemGroup _ _) =
          ↑(inl g : Monoid.Coprod (FreeGroup (Fin 2)) (Orientable 1 1))) ∧
        e ((inr (of 0) : GX (FreeGroup (Fin 2)) (Fin 2)) : SystemGroup _ _) =
          ↑(inr (Orientable.a 1 1 0) : Monoid.Coprod (FreeGroup (Fin 2)) (Orientable 1 1)) ∧
        e ((inr (of 1) : GX (FreeGroup (Fin 2)) (Fin 2)) : SystemGroup _ _) =
          ↑(inr (Orientable.b 1 1 0) : Monoid.Coprod (FreeGroup (Fin 2)) (Orientable 1 1)) := by
  have hd : ⁅(of 0 : FreeGroup (Fin 2))⁻¹, (of 1 : FreeGroup (Fin 2))⁻¹⁆⁻¹ ≠ 1 := by decide
  have inj : (Sum.elim (Sum.elim ![(0 : Fin 2)] ![1]) Fin.elim0).Injective := by decide
  have surj : (Sum.elim (Sum.elim ![(0 : Fin 2)] ![1]) Fin.elim0).Surjective := by decide
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (by simp [Standard.toWord_def])).trans
    ((Standard.orientableCoeffSystemGroupEquiv (n := 1) (m := 0) (c := Fin.elim0) one_pos inj surj
      Fin.rec0 hd).trans
      (QuotientGroup.congr _ _ GX.equivOfIsEmpty ?_)), fun g ↦ ?_, ?_, ?_⟩
  · rw [Subgroup.map_normalClosure _ _ (MulEquiv.surjective _)]
    simp [boundarySystem]
  · simp
  · have h := Standard.orientableCoeffSystemGroupEquiv_mk_inr_of_x (n := 1) (m := 0)
      (c := Fin.elim0) one_pos inj surj Fin.rec0 hd 0
    simp at h
    simp [h]
  · have h := Standard.orientableCoeffSystemGroupEquiv_mk_inr_of_y (n := 1) (m := 0)
      (c := Fin.elim0) one_pos inj surj Fin.rec0 hd 0
    simp at h
    simp [h]

end Example

end TauCeti.GroupAlgGeom.Quadratic
