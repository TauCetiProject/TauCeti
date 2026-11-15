/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.Isomorphism.Walk

/-!
# Path–cycle decompositions under network isomorphisms

A network isomorphism transports a weighted walk by relabelling its endpoints and arrows while
keeping its weight, and the assignment of the transported walk is the transported assignment.
Consequently the path–cycle decompositions of an assignment correspond bijectively to the
path–cycle decompositions of the transported assignment: components are transported one by one,
so the weights, the numbers of path and cycle components, and the path and cycle parts are
preserved.

The coefficient type of the decomposed assignment need not be the coefficient type of the
network's bounds. Arrow identities are retained, so parallel arrows, antiparallel arrows, and loop
cycles are transported unchanged.

## Main definitions

* `TauCeti.Network.Iso.weightedWalkEquiv` and `TauCeti.Network.Iso.weightedClosedWalkEquiv`:
  transport of weighted walks and weighted closed walks.
* `TauCeti.Network.Iso.pathCycleDecompositionEquiv`: the correspondence between path–cycle
  decompositions of an assignment and of its transport.

## Main results

* `TauCeti.Network.Iso.walkAssignment_mapPath`: transporting a walk transports its assignment.
-/

public section

namespace TauCeti.Network.Iso

universe u u' w w'

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network K V} {N' : Network K W} {R : Type w'}

/-- Weighting a transported walk gives the transported weighted walk assignment. -/
@[simp]
theorem walkAssignment_mapPath [AddMonoid R] (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y)
    (q : R) : walkAssignment (e.mapPath p) q = e.assignmentEquiv R (walkAssignment p q) := by
  classical
  rw [← Equiv.symm_apply_eq]
  ext a b f
  simp [walkAssignment_apply, arrows_mapPath, totalHomEquiv_apply,
    ← List.count_map_of_injective _ _ e.totalHomEquiv.injective]

/-! ### Weighted walks -/

private theorem weightedWalk_mk_eq {Q : V → V → Type*} {s t s' t' : V} (hs : s' = s)
    (ht : t' = t) {p' : ArrowWalk Q s' t'} {p : ArrowWalk Q s t}
    (h : @Quiver.Path.cast V ⟨Q⟩ _ _ _ _ hs ht p' = p) (q : R) :
    (⟨s', t', p', q⟩ : WeightedWalk Q R) = ⟨s, t, p, q⟩ := by
  subst hs ht h
  rfl

private theorem weightedClosedWalk_mk_eq {Q : V → V → Type*} {s s' : V} (hs : s' = s)
    {p' : ArrowWalk Q s' s'} {p : ArrowWalk Q s s}
    (h : @Quiver.Path.cast V ⟨Q⟩ _ _ _ _ hs hs p' = p) (q : R) :
    (⟨s', p', q⟩ : WeightedClosedWalk Q R) = ⟨s, p, q⟩ := by
  subst hs h
  rfl

variable (R) in
/-- Transport a weighted walk along a network isomorphism, keeping its weight. -/
def weightedWalkEquiv (e : N ≃ₙ N') : WeightedWalk N.Hom R ≃ WeightedWalk N'.Hom R where
  toFun p := ⟨_, _, e.mapPath p.walk, p.weight⟩
  invFun p := ⟨_, _, e.symm.mapPath p.walk, p.weight⟩
  left_inv := by
    rintro ⟨s, t, p, q⟩
    exact weightedWalk_mk_eq _ _ (e.mapPath_symm_mapPath p) q
  right_inv := by
    rintro ⟨s, t, p, q⟩
    exact weightedWalk_mk_eq _ _ (e.mapPath_mapPath_symm p) q

@[simp]
theorem weightedWalkEquiv_apply (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    e.weightedWalkEquiv R p = ⟨_, _, e.mapPath p.walk, p.weight⟩ :=
  (rfl)

/-- The inverse of weighted-walk transport is transport along the inverse isomorphism. -/
@[simp]
theorem weightedWalkEquiv_symm (e : N ≃ₙ N') :
    (e.weightedWalkEquiv R).symm = e.symm.weightedWalkEquiv R := by
  ext p
  simp only [weightedWalkEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]

/-- The assignment of a transported weighted walk is the transported assignment. -/
theorem assignment_weightedWalkEquiv [AddCommMonoid R] (e : N ≃ₙ N')
    (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).assignment = e.assignmentEquiv R p.assignment := by
  rw [weightedWalkEquiv_apply, WeightedWalk.assignment_def, WeightedWalk.assignment_def]
  exact e.walkAssignment_mapPath p.walk p.weight

variable (R) in
/-- Transport a weighted closed walk along a network isomorphism, keeping its weight. -/
def weightedClosedWalkEquiv (e : N ≃ₙ N') :
    WeightedClosedWalk N.Hom R ≃ WeightedClosedWalk N'.Hom R where
  toFun c := ⟨_, e.mapPath c.walk, c.weight⟩
  invFun c := ⟨_, e.symm.mapPath c.walk, c.weight⟩
  left_inv := by
    rintro ⟨s, c, q⟩
    exact weightedClosedWalk_mk_eq _ (e.mapPath_symm_mapPath c) q
  right_inv := by
    rintro ⟨s, c, q⟩
    exact weightedClosedWalk_mk_eq _ (e.mapPath_mapPath_symm c) q

@[simp]
theorem weightedClosedWalkEquiv_apply (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    e.weightedClosedWalkEquiv R c = ⟨_, e.mapPath c.walk, c.weight⟩ :=
  (rfl)

/-- The inverse of weighted closed-walk transport is transport along the inverse isomorphism. -/
@[simp]
theorem weightedClosedWalkEquiv_symm (e : N ≃ₙ N') :
    (e.weightedClosedWalkEquiv R).symm = e.symm.weightedClosedWalkEquiv R := by
  ext c
  simp only [weightedClosedWalkEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]

/-- The assignment of a transported weighted closed walk is the transported assignment. -/
theorem assignment_weightedClosedWalkEquiv [AddCommMonoid R] (e : N ≃ₙ N')
    (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).assignment = e.assignmentEquiv R c.assignment := by
  rw [weightedClosedWalkEquiv_apply, WeightedClosedWalk.assignment_def,
    WeightedClosedWalk.assignment_def]
  exact e.walkAssignment_mapPath c.walk c.weight

/-! ### Path–cycle decompositions -/

variable [Fintype V] [Fintype W] [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (N'.Hom x y)]
  [AddCommGroup R] [Preorder R]

/-- Transport a path–cycle decomposition of `f` to one of any assignment equal to the transport
of `f`; the equation lets the inverse transport land on `f` itself. -/
private def mapPathCycleDecomposition (e : N ≃ₙ N') {f : N.Assignment R} {g : N'.Assignment R}
    (hfg : e.assignmentEquiv R f = g) (D : PathCycleDecomposition f) :
    PathCycleDecomposition g where
  paths := D.paths.map (e.weightedWalkEquiv R)
  cycles := D.cycles.map (e.weightedClosedWalkEquiv R)
  isPath_walk := by simpa using D.isPath_walk
  isCycle_walk := by simpa using D.isCycle_walk
  weight_pos_of_mem_paths := by simpa using D.weight_pos_of_mem_paths
  weight_pos_of_mem_cycles := by simpa using D.weight_pos_of_mem_cycles
  excessAt_source_neg := by subst hfg; simpa using D.excessAt_source_neg
  excessAt_target_pos := by subst hfg; simpa using D.excessAt_target_pos
  sum_paths_add_sum_cycles := by
    subst hfg
    conv_rhs => rw [← D.sum_paths_add_sum_cycles]
    simp only [assignmentEquiv_add, assignmentEquiv_list_sum, List.map_map, Function.comp_def,
      assignment_weightedWalkEquiv, assignment_weightedClosedWalkEquiv]

@[simp]
private theorem mapPathCycleDecomposition_paths (e : N ≃ₙ N') {f : N.Assignment R}
    {g : N'.Assignment R} (hfg : e.assignmentEquiv R f = g) (D : PathCycleDecomposition f) :
    (mapPathCycleDecomposition e hfg D).paths = D.paths.map (e.weightedWalkEquiv R) :=
  rfl

@[simp]
private theorem mapPathCycleDecomposition_cycles (e : N ≃ₙ N') {f : N.Assignment R}
    {g : N'.Assignment R} (hfg : e.assignmentEquiv R f = g) (D : PathCycleDecomposition f) :
    (mapPathCycleDecomposition e hfg D).cycles = D.cycles.map (e.weightedClosedWalkEquiv R) :=
  rfl

/-- A network isomorphism identifies the path–cycle decompositions of an assignment with those of
its transport, transporting every path and cycle component. -/
def pathCycleDecompositionEquiv (e : N ≃ₙ N') (f : N.Assignment R) :
    PathCycleDecomposition f ≃ PathCycleDecomposition (e.assignmentEquiv R f) where
  toFun := mapPathCycleDecomposition e rfl
  invFun := mapPathCycleDecomposition e.symm <| by
    rw [← assignmentEquiv_symm, Equiv.symm_apply_apply]
  left_inv D := by
    ext1 <;> simp [← weightedWalkEquiv_symm, ← weightedClosedWalkEquiv_symm]
  right_inv D := by
    ext1 <;> simp [← weightedWalkEquiv_symm, ← weightedClosedWalkEquiv_symm]

@[simp]
theorem pathCycleDecompositionEquiv_apply_paths (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition f) :
    (e.pathCycleDecompositionEquiv f D).paths = D.paths.map (e.weightedWalkEquiv R) :=
  (rfl)

@[simp]
theorem pathCycleDecompositionEquiv_apply_cycles (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition f) :
    (e.pathCycleDecompositionEquiv f D).cycles = D.cycles.map (e.weightedClosedWalkEquiv R) :=
  (rfl)

@[simp]
theorem pathCycleDecompositionEquiv_symm_apply_paths (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition (e.assignmentEquiv R f)) :
    ((e.pathCycleDecompositionEquiv f).symm D).paths =
      D.paths.map (e.symm.weightedWalkEquiv R) := by
  simp only [pathCycleDecompositionEquiv, Equiv.coe_fn_symm_mk, mapPathCycleDecomposition_paths]

@[simp]
theorem pathCycleDecompositionEquiv_symm_apply_cycles (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition (e.assignmentEquiv R f)) :
    ((e.pathCycleDecompositionEquiv f).symm D).cycles =
      D.cycles.map (e.symm.weightedClosedWalkEquiv R) := by
  simp only [pathCycleDecompositionEquiv, Equiv.coe_fn_symm_mk, mapPathCycleDecomposition_cycles]

/-- The path part of a transported decomposition is the transported path part. -/
@[simp]
theorem pathAssignment_pathCycleDecompositionEquiv (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition f) :
    (e.pathCycleDecompositionEquiv f D).pathAssignment = e.assignmentEquiv R D.pathAssignment := by
  simp only [PathCycleDecomposition.pathAssignment_def, pathCycleDecompositionEquiv_apply_paths,
    assignmentEquiv_list_sum, List.map_map, Function.comp_def, assignment_weightedWalkEquiv]

/-- The cycle part of a transported decomposition is the transported cycle part. -/
@[simp]
theorem cycleAssignment_pathCycleDecompositionEquiv (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition f) :
    (e.pathCycleDecompositionEquiv f D).cycleAssignment =
      e.assignmentEquiv R D.cycleAssignment := by
  simp only [PathCycleDecomposition.cycleAssignment_def, pathCycleDecompositionEquiv_apply_cycles,
    assignmentEquiv_list_sum, List.map_map, Function.comp_def,
    assignment_weightedClosedWalkEquiv]

end TauCeti.Network.Iso
