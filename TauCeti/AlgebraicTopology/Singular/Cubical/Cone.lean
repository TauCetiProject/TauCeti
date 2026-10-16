/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.Singular.Cubical.Augment

/-!
# The cone on cubical chains of a contractible space

Let `H` be a homotopy from the constant map at a point `v` of a space `X` to the identity of `X`.
The **cone** on a singular `n`-cube `c` of `X` is the `(n+1)`-cube which follows `H` along a new
first coordinate,

`cone c (t, x) = H (t, c x)`.

Its face at `t = 1` is `c`, its face at `t = 0` is the constant cube at `v`, and its faces in the
other coordinates are the cones on the faces of `c`.  So, on chains,

`∂ (cone f) + cone (∂ f) = [v] - f`,

where `[v]` stands for the constant cube at `v` with the coefficients of `f`.  In positive degrees
the constant cube is degenerate, hence zero in the normalized chains: the negated cone is a
contracting homotopy of the normalized cubical chains of `X` in positive degrees, and in degree
zero it contracts onto the multiples of the point `v`.  Consequently the normalized cubical chains
of a contractible space are **acyclic**: every cycle of positive degree is a boundary
(`NormalizedCubicalChain.exists_boundary_eq_of_boundary_eq_zero`), and every `0`-chain of
augmentation zero is a boundary (`NormalizedCubicalChain.exists_boundary_eq_of_augment_eq_zero`).
Convex sets, in particular the cubes `Iⁿ` and the topological simplices, are contractible; they
are the models of the comparison between cubical and simplicial singular chains, and this is the
acyclicity of the cubical side on them.

The cone is degenerate on degenerate cubes (`SingularCube.IsDegenerateAt.cone`), so it descends to
the normalized chains.

## Main definitions

* `TauCeti.SingularCube.cone`: the cone on a singular cube along a contracting homotopy.
* `TauCeti.CubicalChain.cone`, `TauCeti.NormalizedCubicalChain.cone`: the cone on unnormalized and
  on normalized cubical chains.

## Main results

* `TauCeti.CubicalChain.boundary_cone_add_cone_boundary`: `∂ (cone f) + cone (∂ f) = [v] - f`.
* `TauCeti.NormalizedCubicalChain.boundary_cone_add_cone_boundary`: on normalized chains of
  positive degree, `∂ (cone f) + cone (∂ f) = -f`.
* `TauCeti.NormalizedCubicalChain.boundary_cone_zero`: in degree zero,
  `∂ (cone f) = ε(f) • [v] - f`.
* `TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_boundary_eq_zero` and
  `TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_augment_eq_zero`: the normalized cubical
  chains of a contractible space are acyclic.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {v : X}

namespace SingularCube

/-- The **cone** on a singular `n`-cube `c` along a homotopy `H` from the constant map at `v` to
the identity: the `(n+1)`-cube `(t, x) ↦ H (t, c x)`, along a new first coordinate `t`. -/
def cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) : SingularCube X (n + 1) where
  toFun x := H (x 0, c (Fin.tail x))
  continuous_toFun := by fun_prop

@[simp]
theorem cone_apply (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) (x : Fin (n + 1) → I) : cone H c x = H (x 0, c (Fin.tail x)) :=
  (rfl)

/-- The face of the cone at the new coordinate equal to `1` is the cube itself. -/
@[simp]
theorem face_zero_one_cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) : face 0 1 (cone H c) = c := by
  ext x
  simp [Fin.insertNth_zero']

/-- The face of the cone at the new coordinate equal to `0` is the constant cube at `v`. -/
theorem face_zero_zero_cone_apply (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    {n : ℕ} (c : SingularCube X n) (x : Fin n → I) : face 0 0 (cone H c) x = v := by
  simp [Fin.insertNth_zero']

/-- The faces of the cone in the other coordinates are the cones on the faces. -/
@[simp]
theorem face_succ_cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (j : Fin (n + 1)) (t : I) (c : SingularCube X (n + 1)) :
    face j.succ t (cone H c) = cone H (face j t c) := by
  ext x
  obtain ⟨a, y, rfl⟩ : ∃ a y, x = Fin.cons a y := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
  simp

/-- The face of the cone at the new coordinate equal to `0` is degenerate in positive dimensions:
it is constant. -/
theorem isDegenerate_face_zero_zero_cone
    (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X (n + 1)) : IsDegenerate (face 0 0 (cone H c)) :=
  isDegenerate_iff.2 ⟨0, isDegenerateAt_iff.2 fun x t ↦ by
    rw [face_zero_zero_cone_apply, face_zero_zero_cone_apply]⟩

/-- The cone on a cube independent of its `i`-th coordinate is independent of its
`(i+1)`-st. -/
theorem IsDegenerateAt.cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    {n : ℕ} {c : SingularCube X n} {i : Fin n} (h : IsDegenerateAt c i) :
    IsDegenerateAt (SingularCube.cone H c) i.succ :=
  isDegenerateAt_iff.2 fun x t ↦ by
    simp only [cone_apply, Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ,
      h.apply_update]

/-- The cone on a degenerate cube is degenerate. -/
theorem IsDegenerate.cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    {c : SingularCube X n} (h : IsDegenerate c) : IsDegenerate (SingularCube.cone H c) :=
  (isDegenerate_iff.1 h).elim fun _ hi ↦ (hi.cone H).isDegenerate

end SingularCube

namespace CubicalChain

open SingularCube

variable (R : Type*) [Ring R]

/-- The cone on cubical chains along a homotopy from a constant map to the identity, extending
`SingularCube.cone` linearly. -/
def cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) (n : ℕ) :
    CubicalChain X R n →ₗ[R] CubicalChain X R (n + 1) :=
  lmapDomain R R (SingularCube.cone H)

@[simp]
theorem cone_single (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) (a : R) :
    cone R H n (single c a) = single (SingularCube.cone H c) a := by
  rw [cone, lmapDomain_apply, mapDomain_single]

/-- The chain of the faces of the cones at the new coordinate equal to `0`: the constant cubes at
`v`, with the coefficients of the chain. -/
def coneBase (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) (n : ℕ) :
    CubicalChain X R n →ₗ[R] CubicalChain X R n :=
  lmapDomain R R fun c ↦ face 0 0 (SingularCube.cone H c)

@[simp]
theorem coneBase_single (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) (a : R) :
    coneBase R H n (single c a) = single (face 0 0 (SingularCube.cone H c)) a := by
  rw [coneBase, lmapDomain_apply, mapDomain_single]

/-- The cone of a degenerate chain is degenerate. -/
theorem cone_mem_degenerate (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    {n : ℕ} {f : CubicalChain X R n} (hf : f ∈ degenerate X R n) :
    cone R H n f ∈ degenerate X R (n + 1) := by
  refine degenerate_induction R (P := fun f ↦ cone R H n f ∈ degenerate X R (n + 1)) ?_ ?_ ?_ ?_ hf
  · simp
  · intro c hc
    rw [cone_single]
    exact single_mem_degenerate R (hc.cone H) 1
  · intro f g hf hg
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  · intro r f hf
    rw [map_smul]
    exact Submodule.smul_mem _ r hf

/-- In positive degrees the constant cubes at `v` are degenerate. -/
theorem coneBase_mem_degenerate (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    {n : ℕ} (f : CubicalChain X R (n + 1)) : coneBase R H (n + 1) f ∈ degenerate X R (n + 1) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single c a =>
    rw [coneBase_single]
    exact single_mem_degenerate R (isDegenerate_face_zero_zero_cone H c) a

/-- The cone in degree zero: the boundary of the cone on a point is the point `v` minus the
point. -/
theorem boundary_cone_zero (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    (f : CubicalChain X R 0) : boundary X R 0 (cone R H 0 f) = coneBase R H 0 f - f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; abel
  | single c a => simp

/-- **The cone formula**: `∂ (cone f) + cone (∂ f) = [v] - f`, where `[v]` is the chain of the
constant cubes at `v` with the coefficients of `f`. -/
theorem boundary_cone_add_cone_boundary
    (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (f : CubicalChain X R (n + 1)) :
    boundary X R (n + 1) (cone R H (n + 1) f) + cone R H n (boundary X R n f) =
      coneBase R H (n + 1) f - f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg]
    abel
  | single c a =>
    -- The face of the cone in coordinate `0` gives `[v] - c`; the faces in the other
    -- coordinates are the cones on the faces of `c`, with the opposite sign.
    rw [cone_single, boundary_single, Fin.sum_univ_succ, boundary_single, map_sum]
    simp [pow_succ]

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R]

/-- The cone on normalized cubical chains along a homotopy from a constant map to the
identity. -/
def cone (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) (n : ℕ) :
    NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain X R (n + 1) :=
  Submodule.mapQ _ _ (CubicalChain.cone R H n) fun _ hf ↦ cone_mem_degenerate R H hf

@[simp]
theorem cone_mk (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (f : CubicalChain X R n) :
    cone R H n (Submodule.Quotient.mk f) = Submodule.Quotient.mk (CubicalChain.cone R H n f) :=
  Submodule.mapQ_apply _ _ _ f

@[simp]
theorem cone_ofCube (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (c : SingularCube X n) : cone R H n (ofCube X R c) = ofCube X R (SingularCube.cone H c) := by
  rw [ofCube_def, ofCube_def, cone_mk, cone_single]

/-- **The contracting homotopy in positive degrees**: on normalized chains,
`∂ (cone f) + cone (∂ f) = -f`. -/
theorem boundary_cone_add_cone_boundary
    (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X)) {n : ℕ}
    (f : NormalizedCubicalChain X R (n + 1)) :
    boundary X R (n + 1) (cone R H (n + 1) f) + cone R H n (boundary X R n f) = -f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    -- In positive degrees the constant cubes at `v` are degenerate, hence zero.
    rw [cone_mk, boundary_mk, boundary_mk, cone_mk, ← Submodule.Quotient.mk_add,
      CubicalChain.boundary_cone_add_cone_boundary, ← Submodule.Quotient.mk_neg,
      Submodule.Quotient.eq]
    simpa using coneBase_mem_degenerate R H f

/-- The cone in degree zero: `∂ (cone f) = ε(f) • [v] - f`. -/
theorem boundary_cone_zero (H : (ContinuousMap.const X v).Homotopy (ContinuousMap.id X))
    (f : NormalizedCubicalChain X R 0) :
    boundary X R 0 (cone R H 0 f) = augment X R f • ofCube X R (SingularCube.point v) - f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [cone_mk, boundary_mk, CubicalChain.boundary_cone_zero, Submodule.Quotient.mk_sub,
      augment_mk]
    congr 1
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, Submodule.Quotient.mk_add, hf, hg, add_smul]
    | single c a =>
      rw [coneBase_single, augment_single, ofCube_def, ← Submodule.Quotient.mk_smul,
        smul_single_one]
      congr 2
      ext x
      simp

/-- **Acyclicity in positive degrees**: a cycle of positive degree in the normalized cubical
chains of a contractible space is a boundary. -/
theorem exists_boundary_eq_of_boundary_eq_zero [ContractibleSpace X] {n : ℕ}
    {f : NormalizedCubicalChain X R (n + 1)} (hf : boundary X R n f = 0) :
    ∃ g, boundary X R (n + 1) g = f := by
  obtain ⟨v, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic X).1 ‹_›
  refine ⟨-cone R H.symm (n + 1) f, ?_⟩
  have := boundary_cone_add_cone_boundary R H.symm f
  simp only [hf, map_zero, add_zero] at this
  simp [this]

/-- **Acyclicity in degree zero**: a `0`-chain of augmentation zero in the normalized cubical
chains of a contractible space is a boundary. -/
theorem exists_boundary_eq_of_augment_eq_zero [ContractibleSpace X]
    {f : NormalizedCubicalChain X R 0} (hf : augment X R f = 0) : ∃ g, boundary X R 0 g = f := by
  obtain ⟨v, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic X).1 ‹_›
  exact ⟨-cone R H.symm 0 f, by simp [boundary_cone_zero R H.symm, hf]⟩

end NormalizedCubicalChain

end TauCeti
