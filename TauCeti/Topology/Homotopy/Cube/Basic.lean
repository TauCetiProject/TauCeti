/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.PiCurry

/-!
# The cube and its boundary

Mathlib's higher homotopy groups `π_ n X x` are built from generalized loops `Ω^ N X x`,
continuous maps `I^N → X` sending the cube boundary `Cube.boundary N`
(`{y | ∃ i, y i = 0 ∨ y i = 1}`) to the base point. Reasoning about `π_ n` for `n ≥ 2`
needs to know how the cube and, crucially, its *boundary* are connected: the boundary of an
`n`-cube is the topological sphere `S^{n-1}`, which is connected precisely when `n ≥ 2`.
Mathlib records the cube boundary set but proves nothing about its connectivity.

This file supplies that missing input:

* the whole cube `I^N` is path connected (`TauCeti.isPathConnected_cube`);
* its boundary is path connected as soon as the index type has at least two elements
  (`TauCeti.isPathConnected_cubeBoundary`).

It also records how the boundary of a cube with one extra direction splits, mirroring Mathlib's
`Cube.boundary_sum_iff`: a point of `I^(Option N)` is on the boundary exactly when its `none`
coordinate is `0` or `1` or its remaining coordinates are on the boundary of `I^N`
(`Cube.boundary_option_iff`), and likewise for the first coordinate of `I^(Fin (n + 1))`
(`Cube.boundary_fin_succ_iff`). This is how a cube `I × I^N` with a distinguished first direction,
as used for relative homotopy groups, is compared with the absolute cube `I^(Option N)` along
`TauCeti.piOptionEquivProdHomeomorph` (`TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary`),
or with `I^(Fin (n + 1))` along `TauCeti.cubeSplitHomeomorph`
(`TauCeti.cubeSplitHomeomorph_symm_mem_boundary`).

The resulting path-connectedness declarations expose `JoinedIn` witnesses through their
`.joinedIn` methods, so callers can use the generic connectedness API directly.

The paths are elementary: a coordinate is dragged to `0` along the straight line
`pathTowardZero`, and any boundary point is joined to the corner `0` in two phases that each
keep one coordinate pinned at an endpoint, so the whole journey stays inside the boundary.
The two-element hypothesis is exactly what lets the second phase pin a *different* coordinate
at `0` while releasing the first.

## Main declarations

* `TauCeti.pathTowardZero`: the straight-line path in `I` from `a` to `0`.
* `TauCeti.cubeContraction`: the straight-line homotopy from the corner `0` to the identity; so
  the cube is contractible.
* `TauCeti.isPathConnected_cube`: `I^N` is path connected.
* `TauCeti.zero_mem_cubeBoundary`: the corner `0` lies on the boundary.
* `TauCeti.cubeBoundarySetoid`: the equivalence relation identifying all boundary points, whose
  quotient is the cube modulo its boundary.
* `TauCeti.isPathConnected_cubeBoundary`: for `[Nontrivial N]`, `Cube.boundary N` is path
  connected.
* `Cube.boundary_option_iff`, `Cube.boundary_fin_succ_iff`: the boundaries of `I^(Option N)`
  and `I^(Fin (n + 1))`.
* `Cube.boundary_eq_empty`: the boundary of the cube over an empty index type is empty.
* `TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary`: a point of `I × I^N` whose first
  coordinate is `0` or `1`, or whose second lies on the boundary of `I^N`, is sent to the boundary
  of `I^(Option N)`.
* `TauCeti.Cube.prodBoundary`: the boundary of the cube `I × I^N`, matching the boundary of
  `I^(Option N)` by `TauCeti.piOptionEquivProdHomeomorph_mem_prodBoundary_iff`.
* `TauCeti.cubeSplitHomeomorph`: the homeomorphism `I^(Fin (n + 1)) ≃ₜ I × I^(Fin n)` splitting
  off the first coordinate, matching the boundaries by
  `TauCeti.cubeSplitHomeomorph_mem_prodBoundary_iff`.
-/

public section

open scoped Topology unitInterval in
/-- A point of the cube `I^(Option N)` lies on its boundary exactly when its `none` coordinate is
`0` or `1`, or its remaining coordinates lie on the boundary of `I^N`. -/
theorem Cube.boundary_option_iff {N : Type*} {y : I^(Option N)} :
    y ∈ Cube.boundary (Option N) ↔
      (y none = 0 ∨ y none = 1) ∨ (fun k => y (some k)) ∈ Cube.boundary N := by
  constructor
  · rintro ⟨_ | k, hk⟩
    exacts [Or.inl hk, Or.inr ⟨k, hk⟩]
  · rintro (h | ⟨k, hk⟩)
    exacts [⟨none, h⟩, ⟨some k, hk⟩]

open scoped Topology unitInterval in
/-- The cube over an empty index type is a point, and its boundary is empty. -/
@[simp]
theorem Cube.boundary_eq_empty {N : Type*} [IsEmpty N] : Cube.boundary N = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨i, _⟩ ↦ isEmptyElim i

open scoped Topology unitInterval in
/-- A point of the cube `I^(Fin (n + 1))` lies on its boundary exactly when its first coordinate
is `0` or `1`, or its remaining coordinates `Fin.tail y` lie on the boundary of `I^(Fin n)`. -/
theorem Cube.boundary_fin_succ_iff {n : ℕ} {y : I^(Fin (n + 1))} :
    y ∈ Cube.boundary (Fin (n + 1)) ↔
      (y 0 = 0 ∨ y 0 = 1) ∨ Fin.tail y ∈ Cube.boundary (Fin n) := by
  constructor
  · rintro ⟨j, hj⟩
    cases j using Fin.cases with
    | zero => exact Or.inl hj
    | succ k => exact Or.inr ⟨k, hj⟩
  · rintro (h | ⟨k, hk⟩)
    exacts [⟨0, h⟩, ⟨k.succ, hk⟩]

open scoped Topology unitInterval in
/-- A point of the cube `I^(Fin 1)` lies on its boundary exactly when its coordinate is `0` or
`1`. -/
theorem Cube.boundary_fin_one_iff {y : I^(Fin 1)} :
    y ∈ Cube.boundary (Fin 1) ↔ y 0 = 0 ∨ y 0 = 1 := by
  rw [Cube.boundary_fin_succ_iff]
  simp

namespace TauCeti

open scoped Topology
open unitInterval

variable {N : Type*}

/-- The boundary of the cube `I × I^N`: the points whose first coordinate is `0` or `1`, or whose
second coordinate lies on the boundary of `I^N`. -/
def Cube.prodBoundary (N : Type*) : Set (I × I^N) :=
  {y | (y.1 = 0 ∨ y.1 = 1) ∨ y.2 ∈ Cube.boundary N}

@[simp]
theorem Cube.mem_prodBoundary_iff {y : I × I^N} :
    y ∈ Cube.prodBoundary N ↔ (y.1 = 0 ∨ y.1 = 1) ∨ y.2 ∈ Cube.boundary N :=
  Iff.rfl

theorem Cube.mk_zero_mem_prodBoundary (t : I^N) : ((0, t) : I × I^N) ∈ Cube.prodBoundary N :=
  .inl (.inl rfl)

theorem Cube.mk_mem_prodBoundary {s : I} {t : I^N} (h : s = 1 ∨ t ∈ Cube.boundary N) :
    ((s, t) : I × I^N) ∈ Cube.prodBoundary N :=
  h.elim (fun hs => .inl (.inr hs)) .inr

/-- `TauCeti.piOptionEquivProdHomeomorph` identifies the boundary of `I^(Option N)` with the
boundary of `I × I^N`. -/
theorem piOptionEquivProdHomeomorph_mem_prodBoundary_iff {y : I^(Option N)} :
    piOptionEquivProdHomeomorph (fun _ => I) y ∈ Cube.prodBoundary N ↔
      y ∈ Cube.boundary (Option N) := by
  simp [Cube.boundary_option_iff]

/-- A point on the boundary of `I × I^N` corresponds to a point on the boundary of
`I^(Option N)`. -/
theorem piOptionEquivProdHomeomorph_symm_mem_boundary {y : I × I^N}
    (h : y ∈ Cube.prodBoundary N) :
    (piOptionEquivProdHomeomorph fun _ : Option N => I).symm y ∈ Cube.boundary (Option N) :=
  piOptionEquivProdHomeomorph_mem_prodBoundary_iff.1 (by rwa [Homeomorph.apply_symm_apply])

/-- The homeomorphism `Iⁿ⁺¹ ≃ₜ I × Iⁿ` splitting a point into its first coordinate and the
remaining ones, `Fin.consEquiv` as a homeomorphism. -/
def cubeSplitHomeomorph (n : ℕ) : (I^(Fin (n + 1))) ≃ₜ I × (I^(Fin n)) where
  toEquiv := (Fin.consEquiv fun _ ↦ I).symm
  continuous_toFun := (continuous_apply 0).prodMk continuous_id.finTail
  continuous_invFun := continuous_fst.finCons (A := fun _ ↦ I) continuous_snd

@[simp]
theorem cubeSplitHomeomorph_apply {n : ℕ} (z : I^(Fin (n + 1))) :
    cubeSplitHomeomorph n z = (z 0, Fin.tail z) :=
  (rfl)

@[simp]
theorem cubeSplitHomeomorph_symm_apply {n : ℕ} (x : I × (I^(Fin n))) :
    (cubeSplitHomeomorph n).symm x = Fin.cons x.1 x.2 :=
  (rfl)

/-- `TauCeti.cubeSplitHomeomorph` identifies the boundary of `I^(Fin (n + 1))` with the boundary
of `I × I^(Fin n)`. -/
theorem cubeSplitHomeomorph_mem_prodBoundary_iff {n : ℕ} {y : I^(Fin (n + 1))} :
    cubeSplitHomeomorph n y ∈ Cube.prodBoundary (Fin n) ↔ y ∈ Cube.boundary (Fin (n + 1)) :=
  Cube.boundary_fin_succ_iff.symm

/-- A point on the boundary of `I × I^(Fin n)` corresponds to a point on the boundary of
`I^(Fin (n + 1))`. -/
theorem cubeSplitHomeomorph_symm_mem_boundary {n : ℕ} {y : I × I^(Fin n)}
    (h : y ∈ Cube.prodBoundary (Fin n)) :
    (cubeSplitHomeomorph n).symm y ∈ Cube.boundary (Fin (n + 1)) :=
  cubeSplitHomeomorph_mem_prodBoundary_iff.1 (by rwa [Homeomorph.apply_symm_apply])

/-- The straight-line path in the unit interval `I` from `a` to `0`, given by `t ↦ a * σ t`
where `σ` is the interval symmetry `t ↦ 1 - t`. -/
@[expose] def pathTowardZero (a : I) : Path a 0 where
  toFun t := a * σ t
  continuous_toFun := by
    rw [continuous_induced_rng]
    simp only [Function.comp_def, Set.Icc.coe_mul, coe_symm_eq]
    fun_prop
  source' := by simp [symm_zero]
  target' := by simp [symm_one]

@[simp]
theorem pathTowardZero_apply (a t : I) : pathTowardZero a t = a * σ t := rfl

/-- The straight-line homotopy from the zero vertex to the identity on a standard cube. -/
def cubeContraction (N : Type*) :
    ContinuousMap.Homotopy (ContinuousMap.const (N → I) (fun _ ↦ 0))
      (ContinuousMap.id (N → I)) where
  toFun p i := Set.Icc.convexComb 0 (p.2 i) p.1
  continuous_toFun := by
    apply continuous_pi
    intro i
    have hc : Continuous (fun p : I × (N → I) ↦ ((0 : I), p.2 i, p.1)) := by fun_prop
    exact Set.Icc.continuous_convexComb_prod.comp hc
  map_zero_left := by intro x; ext i; simp
  map_one_left := by intro x; ext i; simp

@[simp]
theorem cubeContraction_apply (N : Type*) (t : I) (x : N → I) (i : N) :
    cubeContraction N (t, x) i = Set.Icc.convexComb 0 (x i) t :=
  (rfl)

/-- The cube `I^N` is contractible, by the straight-line contraction onto its corner `0`. -/
instance (N : Type*) : ContractibleSpace (N → I) :=
  (contractible_iff_id_nullhomotopic _).2 ⟨fun _ ↦ 0, ⟨(cubeContraction N).symm⟩⟩

/-- The cube `I^N` is path connected: every point is joined to the corner `0` by the pointwise
product of the coordinate paths `pathTowardZero`. -/
theorem isPathConnected_cube : IsPathConnected (Set.univ : Set (I^N)) :=
  ⟨fun _ => 0, Set.mem_univ _, fun {y} _ =>
    ⟨(Path.pi fun j => pathTowardZero (y j)).symm, fun _ => Set.mem_univ _⟩⟩

/-- The corner `0` lies on the boundary of the cube (any coordinate is `0`). -/
theorem zero_mem_cubeBoundary [Nonempty N] : (0 : I^N) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

variable (N) in
/-- The equivalence relation on the cube `I^N` identifying all points of its boundary with each
other, and no other points.  The quotient is the cube modulo its boundary. -/
def cubeBoundarySetoid : Setoid (I^N) where
  r y z := y = z ∨ y ∈ Cube.boundary N ∧ z ∈ Cube.boundary N
  iseqv :=
    { refl := fun _ ↦ .inl rfl
      symm := fun h ↦ h.elim (fun h ↦ .inl h.symm) fun h ↦ .inr h.symm
      trans := by
        rintro _ _ _ (rfl | ⟨hy, hz⟩) (rfl | ⟨hz', hw⟩)
        exacts [.inl rfl, .inr ⟨hz', hw⟩, .inr ⟨hy, hz⟩, .inr ⟨hy, hw⟩] }

lemma cubeBoundarySetoid_iff {y z : I^N} :
    cubeBoundarySetoid N y z ↔ y = z ∨ y ∈ Cube.boundary N ∧ z ∈ Cube.boundary N :=
  Iff.rfl

section Paths

variable [DecidableEq N]

/-- The path in `I^N` dragging every coordinate other than `i₀` to `0`, while holding the
`i₀`-coordinate fixed at `y i₀`. Its endpoint is supported on `i₀`. -/
private def cubeCollapseComplement (i₀ : N) (y : I^N) :
    Path y (Function.update (0 : I^N) i₀ (y i₀)) where
  toFun t := Function.update (fun j => pathTowardZero (y j) t) i₀ (y i₀)
  continuous_toFun :=
    (continuous_pi fun j => (pathTowardZero (y j)).continuous).update i₀ continuous_const
  source' := by
    simp only [Path.source]
    exact Function.update_eq_self i₀ y
  target' := by
    simp only [Path.target]
    rfl

@[simp]
private theorem cubeCollapseComplement_apply (i₀ : N) (y : I^N) (t : I) :
    cubeCollapseComplement i₀ y t
      = Function.update (fun j => pathTowardZero (y j) t) i₀ (y i₀) := rfl

/-- The path in `I^N` dragging the `i₀`-coordinate from `a` to `0`, with every other
coordinate held at `0`. It runs from the point supported on `i₀` back to the corner `0`. -/
private def cubeCollapseCoord (i₀ : N) (a : I) : Path (Function.update (0 : I^N) i₀ a) 0 where
  toFun t := Function.update (0 : I^N) i₀ (pathTowardZero a t)
  continuous_toFun := continuous_const.update i₀ (pathTowardZero a).continuous
  source' := by simp only [Path.source]
  target' := by
    simp only [Path.target]
    exact Function.update_eq_self i₀ (0 : I^N)

@[simp]
private theorem cubeCollapseCoord_apply (i₀ : N) (a t : I) :
    cubeCollapseCoord i₀ a t = Function.update (0 : I^N) i₀ (pathTowardZero a t) := rfl

end Paths

/-- The boundary of the cube `I^N` is path connected once the index type has at least two
elements. Any boundary point `y`, extreme in some coordinate `i₀`, is joined to the corner `0`
in two phases: first collapse every other coordinate to `0` (keeping `i₀` extreme), then
collapse the `i₀`-coordinate (keeping a *different* coordinate `j₀` at `0`). The two-element
hypothesis provides the index `j₀ ≠ i₀`. -/
theorem isPathConnected_cubeBoundary [Nontrivial N] : IsPathConnected (Cube.boundary N) := by
  classical
  refine ⟨0, zero_mem_cubeBoundary, fun {y} hy => ?_⟩
  obtain ⟨i₀, hi₀⟩ := hy
  obtain ⟨j₀, hj₀⟩ := exists_ne i₀
  have h1 : JoinedIn (Cube.boundary N) y (Function.update (0 : I^N) i₀ (y i₀)) :=
    ⟨cubeCollapseComplement i₀ y, fun t =>
      ⟨i₀, by rw [cubeCollapseComplement_apply, Function.update_self]; exact hi₀⟩⟩
  have h2 : JoinedIn (Cube.boundary N) (Function.update (0 : I^N) i₀ (y i₀)) 0 :=
    ⟨cubeCollapseCoord i₀ (y i₀), fun t =>
      ⟨j₀, Or.inl <| by rw [cubeCollapseCoord_apply, Function.update_of_ne hj₀]; rfl⟩⟩
  exact (h1.trans h2).symm

end TauCeti
