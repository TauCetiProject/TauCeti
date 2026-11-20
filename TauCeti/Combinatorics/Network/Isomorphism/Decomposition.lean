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

universe u u' u'' w w'

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

variable (R) in
/-- Transport a weighted walk along a network isomorphism, keeping its weight. -/
def weightedWalkEquiv (e : N ≃ₙ N') : WeightedWalk N.Hom R ≃ WeightedWalk N'.Hom R where
  toFun p := ⟨_, _, e.mapPath p.walk, p.weight⟩
  invFun p := ⟨_, _, e.symm.mapPath p.walk, p.weight⟩
  left_inv := by
    rintro ⟨s, t, p, q⟩
    exact WeightedWalk.ext _ _ (e.mapPath_symm_mapPath p) rfl
  right_inv := by
    rintro ⟨s, t, p, q⟩
    exact WeightedWalk.ext _ _ (e.mapPath_mapPath_symm p) rfl

theorem weightedWalkEquiv_apply (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    e.weightedWalkEquiv R p = ⟨_, _, e.mapPath p.walk, p.weight⟩ :=
  (rfl)

/-- The source of a transported weighted walk is the transported source. -/
@[simp]
theorem source_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).source = e.vertexEquiv p.source := by
  rw [weightedWalkEquiv_apply]

/-- The target of a transported weighted walk is the transported target. -/
@[simp]
theorem target_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).target = e.vertexEquiv p.target := by
  rw [weightedWalkEquiv_apply]

/-- The walk of a transported weighted walk is the transported walk. -/
@[simp]
theorem walk_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    @Quiver.Path.cast W ⟨N'.Hom⟩ _ _ _ _ (source_weightedWalkEquiv e p)
      (target_weightedWalkEquiv e p) (e.weightedWalkEquiv R p).walk = e.mapPath p.walk := by
  rw [@Quiver.Path.cast_eq_iff_heq W ⟨N'.Hom⟩, weightedWalkEquiv_apply]

/-- The weight of a transported weighted walk is unchanged. -/
@[simp]
theorem weight_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).weight = p.weight := by
  rw [weightedWalkEquiv_apply]

/-- The arrows of a transported weighted walk are the transported arrows. -/
@[simp]
theorem arrows_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).walk.arrows = p.walk.arrows.map e.totalHomEquiv := by
  rw [weightedWalkEquiv_apply]
  exact e.arrows_mapPath p.walk

/-- The vertices of a transported weighted walk are the transported vertices. -/
@[simp]
theorem vertices_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).walk.vertices = p.walk.vertices.map e.vertexEquiv := by
  rw [weightedWalkEquiv_apply]
  exact e.vertices_mapPath p.walk

/-- Transport preserves the length of a weighted walk. -/
@[simp]
theorem length_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).walk.length = p.walk.length := by
  rw [weightedWalkEquiv_apply]
  exact e.length_mapPath p.walk

/-- Transport preserves and reflects whether a weighted walk is a path. -/
@[simp]
theorem isPath_weightedWalkEquiv (e : N ≃ₙ N') (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).walk.IsPath ↔ p.walk.IsPath := by
  rw [weightedWalkEquiv_apply]
  exact e.isPath_mapPath p.walk

/-- The inverse of weighted-walk transport is transport along the inverse isomorphism. -/
@[simp]
theorem weightedWalkEquiv_symm (e : N ≃ₙ N') :
    e.symm.weightedWalkEquiv R = (e.weightedWalkEquiv R).symm := by
  apply Equiv.ext
  intro p
  simp only [weightedWalkEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]

/-- Inverse weighted-walk transport applies inverse path transport and keeps the weight. -/
theorem weightedWalkEquiv_symm_apply (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    (e.weightedWalkEquiv R).symm p = ⟨_, _, e.symm.mapPath p.walk, p.weight⟩ := by
  rw [← weightedWalkEquiv_symm]
  exact weightedWalkEquiv_apply e.symm p

/-- The source of a pulled-back weighted walk is the pulled-back source. -/
@[simp]
theorem source_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).source = e.vertexEquiv.symm p.source := by
  simpa only [weightedWalkEquiv_symm_apply] using symm_vertexEquiv_apply e p.source

/-- The target of a pulled-back weighted walk is the pulled-back target. -/
@[simp]
theorem target_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).target = e.vertexEquiv.symm p.target := by
  simpa only [weightedWalkEquiv_symm_apply] using symm_vertexEquiv_apply e p.target

/-- The walk of a pulled-back weighted walk is the inverse-transported walk. -/
@[simp]
theorem walk_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    @Quiver.Path.cast V ⟨N.Hom⟩ _ _ _ _
      ((source_weightedWalkEquiv_symm e p).trans (symm_vertexEquiv_apply e p.source).symm)
      ((target_weightedWalkEquiv_symm e p).trans (symm_vertexEquiv_apply e p.target).symm)
      ((e.weightedWalkEquiv R).symm p).walk = e.symm.mapPath p.walk := by
  rw [@Quiver.Path.cast_eq_iff_heq V ⟨N.Hom⟩, weightedWalkEquiv_symm_apply]

/-- Pulling back a weighted walk leaves its weight unchanged. -/
@[simp]
theorem weight_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).weight = p.weight := by
  rw [weightedWalkEquiv_symm_apply]

/-- Pulling back a weighted walk inverse-transports its arrows. -/
@[simp]
theorem arrows_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).walk.arrows =
      p.walk.arrows.map e.totalHomEquiv.symm := by
  rw [weightedWalkEquiv_symm_apply, arrows_mapPath, totalHomEquiv_symm]

/-- Pulling back a weighted walk inverse-transports its vertices. -/
@[simp]
theorem vertices_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).walk.vertices =
      p.walk.vertices.map e.vertexEquiv.symm := by
  rw [weightedWalkEquiv_symm_apply, vertices_mapPath, symm_vertexEquiv]

/-- Pulling back preserves the length of a weighted walk. -/
@[simp]
theorem length_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).walk.length = p.walk.length := by
  rw [weightedWalkEquiv_symm_apply]
  exact e.symm.length_mapPath p.walk

/-- Pulling back preserves and reflects whether a weighted walk is a path. -/
@[simp]
theorem isPath_weightedWalkEquiv_symm (e : N ≃ₙ N') (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).walk.IsPath ↔ p.walk.IsPath := by
  rw [weightedWalkEquiv_symm_apply]
  exact e.symm.isPath_mapPath p.walk

/-- Transport along the identity network isomorphism fixes weighted walks. -/
@[simp]
theorem weightedWalkEquiv_refl (N : Network K V) :
    (refl N).weightedWalkEquiv R = Equiv.refl _ := by
  apply Equiv.ext
  rintro ⟨s, t, p, q⟩
  simp only [weightedWalkEquiv_apply, Equiv.refl_apply]
  exact WeightedWalk.ext (refl_vertexEquiv_apply N s) (refl_vertexEquiv_apply N t)
    (mapPath_refl N p) rfl

/-- Weighted-walk transport commutes with composition of network isomorphisms. -/
@[simp]
theorem weightedWalkEquiv_trans {X : Type u''} {N'' : Network K X}
    (e : N ≃ₙ N') (f : N' ≃ₙ N'') :
    (e.trans f).weightedWalkEquiv R =
      (e.weightedWalkEquiv R).trans (f.weightedWalkEquiv R) := by
  apply Equiv.ext
  rintro ⟨s, t, p, q⟩
  simp only [weightedWalkEquiv_apply, Equiv.trans_apply]
  exact WeightedWalk.ext (trans_vertexEquiv_apply e f s) (trans_vertexEquiv_apply e f t)
    (mapPath_trans e f p) rfl

/-- The assignment of a transported weighted walk is the transported assignment. -/
@[simp]
theorem assignment_weightedWalkEquiv [AddMonoid R] (e : N ≃ₙ N')
    (p : WeightedWalk N.Hom R) :
    (e.weightedWalkEquiv R p).assignment = e.assignmentEquiv R p.assignment := by
  rw [weightedWalkEquiv_apply, WeightedWalk.assignment_def, WeightedWalk.assignment_def]
  exact e.walkAssignment_mapPath p.walk p.weight

/-- The assignment of a pulled-back weighted walk is the pulled-back assignment. -/
@[simp]
theorem assignment_weightedWalkEquiv_symm [AddMonoid R] (e : N ≃ₙ N')
    (p : WeightedWalk N'.Hom R) :
    ((e.weightedWalkEquiv R).symm p).assignment =
      (e.assignmentEquiv R).symm p.assignment := by
  rw [weightedWalkEquiv_symm_apply, WeightedWalk.assignment_def, WeightedWalk.assignment_def,
    assignmentEquiv_symm]
  exact e.symm.walkAssignment_mapPath p.walk p.weight

variable (R) in
/-- Transport a weighted closed walk along a network isomorphism, keeping its weight. -/
def weightedClosedWalkEquiv (e : N ≃ₙ N') :
    WeightedClosedWalk N.Hom R ≃ WeightedClosedWalk N'.Hom R where
  toFun c := ⟨_, e.mapPath c.walk, c.weight⟩
  invFun c := ⟨_, e.symm.mapPath c.walk, c.weight⟩
  left_inv := by
    rintro ⟨s, c, q⟩
    exact WeightedClosedWalk.ext _ (e.mapPath_symm_mapPath c) rfl
  right_inv := by
    rintro ⟨s, c, q⟩
    exact WeightedClosedWalk.ext _ (e.mapPath_mapPath_symm c) rfl

theorem weightedClosedWalkEquiv_apply (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    e.weightedClosedWalkEquiv R c = ⟨_, e.mapPath c.walk, c.weight⟩ :=
  (rfl)

/-- The base of a transported weighted closed walk is the transported base. -/
@[simp]
theorem base_weightedClosedWalkEquiv (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).base = e.vertexEquiv c.base := by
  rw [weightedClosedWalkEquiv_apply]

/-- The walk of a transported weighted closed walk is the transported walk. -/
@[simp]
theorem walk_weightedClosedWalkEquiv (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    @Quiver.Path.cast W ⟨N'.Hom⟩ _ _ _ _ (base_weightedClosedWalkEquiv e c)
      (base_weightedClosedWalkEquiv e c) (e.weightedClosedWalkEquiv R c).walk =
        e.mapPath c.walk := by
  rw [@Quiver.Path.cast_eq_iff_heq W ⟨N'.Hom⟩, weightedClosedWalkEquiv_apply]

/-- The weight of a transported weighted closed walk is unchanged. -/
@[simp]
theorem weight_weightedClosedWalkEquiv (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).weight = c.weight := by
  rw [weightedClosedWalkEquiv_apply]

/-- The arrows of a transported weighted closed walk are the transported arrows. -/
@[simp]
theorem arrows_weightedClosedWalkEquiv (e : N ≃ₙ N') (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).walk.arrows = c.walk.arrows.map e.totalHomEquiv := by
  rw [weightedClosedWalkEquiv_apply]
  exact e.arrows_mapPath c.walk

/-- The vertices of a transported weighted closed walk are the transported vertices. -/
@[simp]
theorem vertices_weightedClosedWalkEquiv (e : N ≃ₙ N')
    (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).walk.vertices = c.walk.vertices.map e.vertexEquiv := by
  rw [weightedClosedWalkEquiv_apply]
  exact e.vertices_mapPath c.walk

/-- Transport preserves the length of a weighted closed walk. -/
@[simp]
theorem length_weightedClosedWalkEquiv (e : N ≃ₙ N')
    (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).walk.length = c.walk.length := by
  rw [weightedClosedWalkEquiv_apply]
  exact e.length_mapPath c.walk

/-- Transport preserves and reflects whether a weighted closed walk is a cycle. -/
@[simp]
theorem isCycle_weightedClosedWalkEquiv (e : N ≃ₙ N')
    (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).walk.IsCycle ↔ c.walk.IsCycle := by
  rw [weightedClosedWalkEquiv_apply]
  exact e.isCycle_mapPath c.walk

/-- The inverse of weighted closed-walk transport is transport along the inverse isomorphism. -/
@[simp]
theorem weightedClosedWalkEquiv_symm (e : N ≃ₙ N') :
    e.symm.weightedClosedWalkEquiv R = (e.weightedClosedWalkEquiv R).symm := by
  apply Equiv.ext
  intro c
  simp only [weightedClosedWalkEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]

/-- Inverse weighted closed-walk transport applies inverse path transport and keeps the weight. -/
theorem weightedClosedWalkEquiv_symm_apply (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    (e.weightedClosedWalkEquiv R).symm c = ⟨_, e.symm.mapPath c.walk, c.weight⟩ := by
  rw [← weightedClosedWalkEquiv_symm]
  exact weightedClosedWalkEquiv_apply e.symm c

/-- The base of a pulled-back weighted closed walk is the pulled-back base. -/
@[simp]
theorem base_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).base = e.vertexEquiv.symm c.base := by
  simpa only [weightedClosedWalkEquiv_symm_apply] using symm_vertexEquiv_apply e c.base

/-- The walk of a pulled-back weighted closed walk is the inverse-transported walk. -/
@[simp]
theorem walk_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    @Quiver.Path.cast V ⟨N.Hom⟩ _ _ _ _
      ((base_weightedClosedWalkEquiv_symm e c).trans (symm_vertexEquiv_apply e c.base).symm)
      ((base_weightedClosedWalkEquiv_symm e c).trans (symm_vertexEquiv_apply e c.base).symm)
      ((e.weightedClosedWalkEquiv R).symm c).walk = e.symm.mapPath c.walk := by
  rw [@Quiver.Path.cast_eq_iff_heq V ⟨N.Hom⟩, weightedClosedWalkEquiv_symm_apply]

/-- Pulling back a weighted closed walk leaves its weight unchanged. -/
@[simp]
theorem weight_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).weight = c.weight := by
  rw [weightedClosedWalkEquiv_symm_apply]

/-- Pulling back a weighted closed walk inverse-transports its arrows. -/
@[simp]
theorem arrows_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).walk.arrows =
      c.walk.arrows.map e.totalHomEquiv.symm := by
  rw [weightedClosedWalkEquiv_symm_apply, arrows_mapPath, totalHomEquiv_symm]

/-- Pulling back a weighted closed walk inverse-transports its vertices. -/
@[simp]
theorem vertices_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).walk.vertices =
      c.walk.vertices.map e.vertexEquiv.symm := by
  rw [weightedClosedWalkEquiv_symm_apply, vertices_mapPath, symm_vertexEquiv]

/-- Pulling back preserves the length of a weighted closed walk. -/
@[simp]
theorem length_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).walk.length = c.walk.length := by
  rw [weightedClosedWalkEquiv_symm_apply]
  exact e.symm.length_mapPath c.walk

/-- Pulling back preserves and reflects whether a weighted closed walk is a cycle. -/
@[simp]
theorem isCycle_weightedClosedWalkEquiv_symm (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).walk.IsCycle ↔ c.walk.IsCycle := by
  rw [weightedClosedWalkEquiv_symm_apply]
  exact e.symm.isCycle_mapPath c.walk

/-- Transport along the identity network isomorphism fixes weighted closed walks. -/
@[simp]
theorem weightedClosedWalkEquiv_refl (N : Network K V) :
    (refl N).weightedClosedWalkEquiv R = Equiv.refl _ := by
  apply Equiv.ext
  rintro ⟨s, c, q⟩
  simp only [weightedClosedWalkEquiv_apply, Equiv.refl_apply]
  exact WeightedClosedWalk.ext (refl_vertexEquiv_apply N s) (mapPath_refl N c) rfl

/-- Weighted closed-walk transport commutes with composition of network isomorphisms. -/
@[simp]
theorem weightedClosedWalkEquiv_trans {X : Type u''} {N'' : Network K X}
    (e : N ≃ₙ N') (f : N' ≃ₙ N'') :
    (e.trans f).weightedClosedWalkEquiv R =
      (e.weightedClosedWalkEquiv R).trans (f.weightedClosedWalkEquiv R) := by
  apply Equiv.ext
  rintro ⟨s, c, q⟩
  simp only [weightedClosedWalkEquiv_apply, Equiv.trans_apply]
  exact WeightedClosedWalk.ext (trans_vertexEquiv_apply e f s) (mapPath_trans e f c) rfl

/-- The assignment of a transported weighted closed walk is the transported assignment. -/
@[simp]
theorem assignment_weightedClosedWalkEquiv [AddMonoid R] (e : N ≃ₙ N')
    (c : WeightedClosedWalk N.Hom R) :
    (e.weightedClosedWalkEquiv R c).assignment = e.assignmentEquiv R c.assignment := by
  rw [weightedClosedWalkEquiv_apply, WeightedClosedWalk.assignment_def,
    WeightedClosedWalk.assignment_def]
  exact e.walkAssignment_mapPath c.walk c.weight

/-- The assignment of a pulled-back weighted closed walk is the pulled-back assignment. -/
@[simp]
theorem assignment_weightedClosedWalkEquiv_symm [AddMonoid R] (e : N ≃ₙ N')
    (c : WeightedClosedWalk N'.Hom R) :
    ((e.weightedClosedWalkEquiv R).symm c).assignment =
      (e.assignmentEquiv R).symm c.assignment := by
  rw [weightedClosedWalkEquiv_symm_apply, WeightedClosedWalk.assignment_def,
    WeightedClosedWalk.assignment_def, assignmentEquiv_symm]
  exact e.symm.walkAssignment_mapPath c.walk c.weight

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
    ext1 <;> simp
  right_inv D := by
    ext1 <;> simp

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
      D.paths.map (e.weightedWalkEquiv R).symm := by
  simp only [pathCycleDecompositionEquiv, Equiv.coe_fn_symm_mk, mapPathCycleDecomposition_paths]
  rw [weightedWalkEquiv_symm]

@[simp]
theorem pathCycleDecompositionEquiv_symm_apply_cycles (e : N ≃ₙ N') {f : N.Assignment R}
    (D : PathCycleDecomposition (e.assignmentEquiv R f)) :
    ((e.pathCycleDecompositionEquiv f).symm D).cycles =
      D.cycles.map (e.weightedClosedWalkEquiv R).symm := by
  simp only [pathCycleDecompositionEquiv, Equiv.coe_fn_symm_mk, mapPathCycleDecomposition_cycles]
  rw [weightedClosedWalkEquiv_symm]

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

/-- The path part of a decomposition pulled back along an isomorphism is pulled back. -/
@[simp]
theorem pathAssignment_pathCycleDecompositionEquiv_symm (e : N ≃ₙ N')
    {f : N.Assignment R} (D : PathCycleDecomposition (e.assignmentEquiv R f)) :
    ((e.pathCycleDecompositionEquiv f).symm D).pathAssignment =
      (e.assignmentEquiv R).symm D.pathAssignment := by
  rw [assignmentEquiv_symm]
  simp only [PathCycleDecomposition.pathAssignment_def,
    pathCycleDecompositionEquiv_symm_apply_paths, assignmentEquiv_list_sum, List.map_map,
    Function.comp_def, ← weightedWalkEquiv_symm, assignment_weightedWalkEquiv]

/-- The cycle part of a decomposition pulled back along an isomorphism is pulled back. -/
@[simp]
theorem cycleAssignment_pathCycleDecompositionEquiv_symm (e : N ≃ₙ N')
    {f : N.Assignment R} (D : PathCycleDecomposition (e.assignmentEquiv R f)) :
    ((e.pathCycleDecompositionEquiv f).symm D).cycleAssignment =
      (e.assignmentEquiv R).symm D.cycleAssignment := by
  rw [assignmentEquiv_symm]
  simp only [PathCycleDecomposition.cycleAssignment_def,
    pathCycleDecompositionEquiv_symm_apply_cycles, assignmentEquiv_list_sum, List.map_map,
    Function.comp_def, ← weightedClosedWalkEquiv_symm, assignment_weightedClosedWalkEquiv]

end TauCeti.Network.Iso
