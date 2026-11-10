/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import TauCeti.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.LinearAlgebra.AffineSpace.Generic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Generic points for affine arrangements

Adapted from `Mei/Geometry/Affine/Generic.lean` at commit `7f1e4c7`.

The common complement of countably many proper affine subspaces of a
real normed affine space with finite-dimensional direction is dense and is a Gδ set. For a finite
family the complement is open. These statements allow arbitrarily small
perturbations avoiding all the prescribed affine exceptions. Countably many affine
subspaces not containing `A` can also be avoided in any nonempty relatively open subset
of `A`, using `AffineIsometryEquiv.constVSub` to pass to its direction space.
Relatively, finitely many affine subspaces covering all points of an affine subspace `A`
near one of its points
include one whose direction contains that of `A`.

For affine obstacles of codimension at least two, a freely chosen intermediate
vertex can avoid all the affine spans with either endpoint. This constructs two
segments avoiding every obstacle while fixing both endpoints. Finite exceptional
arrangements support union and transport by affine equivalences.

For a set covered by such obstacles, the endpoints need only avoid the set
itself, and the vertex may simultaneously avoid additional proper affine
subspaces.
-/

public section

open Set

namespace AffineSubspace

section Topology

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- A proper real affine subspace has empty interior, even without a
finite-dimensionality assumption. -/
theorem interior_eq_empty_of_ne_top (S : AffineSubspace ℝ P) (hS : S ≠ ⊤) :
    interior (S : Set P) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hspan := isOpen_interior.affineSpan_eq_top ⟨x, hx⟩
  have hle : affineSpan ℝ (interior (S : Set P)) ≤ S :=
    affineSpan_le.mpr interior_subset
  exact hS (top_le_iff.mp (hspan ▸ hle))

/-- The complement of a proper affine subspace is dense. -/
theorem dense_compl_of_ne_top (S : AffineSubspace ℝ P) (hS : S ≠ ⊤) :
    Dense (S : Set P)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (S.interior_eq_empty_of_ne_top hS)

/-- If finitely many affine subspaces cover all points of `A` near a point of `A`, then
the direction of one of them contains the direction of `A`. In particular, finitely many
affine subspaces of smaller dimension never cover a relative neighbourhood in `A`. -/
theorem exists_direction_le_of_forall_mem {ι : Type*} [Finite ι]
    (A : AffineSubspace ℝ P) (E : ι → AffineSubspace ℝ P) {x : P} (hx : x ∈ A)
    {U : Set P} (hU : U ∈ nhds x) (hcover : ∀ y ∈ A, y ∈ U → ∃ j, y ∈ E j) :
    ∃ j, A.direction ≤ (E j).direction := by
  -- Every direction of `A` is the direction of two points of one `E j` on its line.
  have hcov (v : V) (hv : v ∈ A.direction) : ∃ j, v ∈ (E j).direction := by
    let S : Set ℝ := {t | t • v +ᵥ x ∈ U}
    have hS : S ∈ nhds (0 : ℝ) := by
      have hc : Continuous fun t : ℝ => t • v +ᵥ x := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa only [zero_smul, zero_vadd] using hU)
    have : Infinite S := (infinite_of_mem_nhds (0 : ℝ) hS).to_subtype
    choose f hf using fun t : S =>
      hcover _ (vadd_mem_of_mem_direction (A.direction.smul_mem (t : ℝ) hv) hx) t.property
    obtain ⟨s, t, hst, hj⟩ := Finite.exists_ne_map_eq_of_infinite f
    have hsub := vsub_mem_direction (hf s) (hj ▸ hf t)
    rw [vadd_vsub_vadd_cancel_right, ← sub_smul] at hsub
    have hne : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hst)
    exact ⟨f s, by simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using
      (E (f s)).direction.smul_mem ((s : ℝ) - t)⁻¹ hsub⟩
  let p : ι → Submodule ℝ A.direction := fun j => (E j).direction.comap A.direction.subtype
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := p)
    (Set.eq_univ_of_forall fun v => Set.mem_iUnion.mpr (hcov v v.property))
  exact ⟨j, fun v hv => (Submodule.eq_top_iff'.mp hj ⟨v, hv⟩ : _)⟩

variable [FiniteDimensional ℝ V]

/-- Countably many proper affine subspaces have dense common complement. -/
theorem dense_genericLocus {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ P)
    (hA : ∀ i, A i ≠ ⊤) : Dense (genericLocus A) := by
  let : CompleteSpace P :=
    (AffineIsometryEquiv.constVSub ℝ (Classical.arbitrary P)).toIsometryEquiv.completeSpace
  rw [genericLocus_eq_iInter]
  exact dense_iInter_of_isOpen
    (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)
    (fun i => (A i).dense_compl_of_ne_top (hA i))

/-- The common complement is a countable intersection of open sets. -/
theorem isGδ_genericLocus {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ P) :
    IsGδ (genericLocus A) := by
  rw [genericLocus_eq_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- For a finite family, the common complement is open. -/
theorem isOpen_genericLocus {ι : Sort*} [Finite ι] (A : ι → AffineSubspace ℝ P) :
    IsOpen (genericLocus A) := by
  rw [genericLocus_eq_iInter]
  exact isOpen_iInter_of_finite (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- A generic point can be chosen in any prescribed nonempty open set. -/
theorem exists_mem_open_genericLocus {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ P) (hA : ∀ i, A i ≠ ⊤)
    {U : Set P} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  obtain ⟨x, hxU, hxA⟩ := (dense_genericLocus A hA).inter_open_nonempty U hU hne
  exact ⟨x, hxU, mem_genericLocus.mp hxA⟩

/-- A nonempty relatively open set in an affine subspace contains a point
outside any countable family of affine subspaces none of which contains it. -/
theorem exists_mem_open_avoid_of_not_le {ι : Sort*} [Countable ι]
    (A : AffineSubspace ℝ P)
    (E : ι → AffineSubspace ℝ P)
    (hE : ∀ j, ¬ A ≤ E j)
    {U : Set A} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ j, (x : P) ∉ E j := by
  obtain ⟨p, hp⟩ := hne
  let : Nonempty A := ⟨p⟩
  let e := (AffineIsometryEquiv.constVSub ℝ p).symm
  let f := A.subtype.comp e.toAffineEquiv.toAffineMap
  have hproper (j : ι) : (E j).comap f ≠ ⊤ := by
    intro hj
    have hle : A ≤ E j := by
      intro y hy
      have hv : e.symm ⟨y, hy⟩ ∈ (E j).comap f := by rw [hj]; trivial
      simpa only [mem_comap, f, AffineMap.comp_apply, coe_subtype,
        AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
        e.apply_symm_apply] using hv
    exact hE j hle
  obtain ⟨v, hv, havoid⟩ := exists_mem_open_genericLocus
    (fun j => (E j).comap f) hproper
    (hU.preimage e.continuous) ⟨e.symm p, by simpa using hp⟩
  exact ⟨e v, hv, havoid⟩

/-- A nonempty relatively open set in an affine subspace contains a point
outside any countable family of affine subspaces of smaller dimension. -/
theorem exists_mem_open_avoid_of_finrank_lt {ι : Sort*} [Countable ι]
    (A : AffineSubspace ℝ P) (E : ι → AffineSubspace ℝ P)
    (hE : ∀ j, Module.finrank ℝ (E j).direction < Module.finrank ℝ A.direction)
    {U : Set A} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ j, (x : P) ∉ E j :=
  A.exists_mem_open_avoid_of_not_le E
    (fun j hle => (not_le_of_gt (hE j)) (Submodule.finrank_mono (direction_le hle))) hU hne

/-- Generic points can be chosen arbitrarily close to any point. -/
theorem exists_dist_lt_genericLocus {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ P) (hA : ∀ i, A i ≠ ⊤)
    (x : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, dist y x < ε ∧ ∀ i, y ∉ A i := by
  obtain ⟨y, hy, hA⟩ := exists_mem_open_genericLocus A hA
    Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
  exact ⟨y, hy, hA⟩

end Topology


section Topology

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]

/-- A set covered by countably many affine subspaces of codimension at least
two can be avoided by both full lines from two fixed allowed endpoints to a
vertex in any nonempty open set. The vertex may simultaneously avoid any
additional countable family of proper affine subspaces.

The endpoints are required to avoid the actual set only; they may lie in its
affine cover. The prescribed open set constrains the vertex, not the lines. -/
theorem exists_mem_open_two_lineMaps_avoid_set {ι κ : Type*} [Countable ι] [Countable κ]
    (S : κ → AffineSubspace ℝ P)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    (A : ι → AffineSubspace ℝ P) (hA : ∀ i, A i ≠ ⊤)
    {E : Set P} (hE : E ⊆ ⋃ k, (S k : Set P))
    {x y : P} (hx : x ∉ E) (hy : y ∉ E)
    {U : Set P} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, z ∉ A i) ∧ ∀ t : ℝ,
      AffineMap.lineMap x z t ∉ E ∧ AffineMap.lineMap y z t ∉ E := by
  let B : (κ ⊕ κ) ⊕ ι → AffineSubspace ℝ P := Sum.elim
    (Sum.elim (fun k => affineSpan ℝ (insert x (S k : Set P)))
      (fun k => affineSpan ℝ (insert y (S k : Set P)))) A
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i
    rcases i with k | i
    · rcases k with k | k
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) x
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) y
    · exact hA i
  obtain ⟨z, hzU, hz⟩ := exists_mem_open_genericLocus B hB hU hne
  have havoid (p : P) (hp : p ∉ E)
      (hzp : ∀ k, z ∉ affineSpan ℝ (insert p (S k : Set P))) (t : ℝ) :
      AffineMap.lineMap p z t ∉ E := by
    by_cases ht : t = 0
    · simpa [ht] using hp
    · intro htE
      obtain ⟨k, htk⟩ := Set.mem_iUnion.mp (hE htE)
      exact (S k).lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (hzp k) ht htk
  exact ⟨z, hzU, fun i => hz (.inr i), fun t =>
    ⟨havoid x hx (fun k => hz (.inl (.inl k))) t,
      havoid y hy (fun k => hz (.inl (.inr k))) t⟩⟩

/-- Between endpoints outside countably many affine obstacles of codimension at
least two, an intermediate vertex can be chosen in any nonempty open set so
that both full lines, and hence both segments, avoid every obstacle.

Only the vertex is varied: both endpoints remain fixed. -/
theorem exists_mem_open_two_lineMaps_avoid {ι : Type*} [Countable ι]
    (S : ι → AffineSubspace ℝ P)
    (hS : ∀ i, Module.finrank ℝ (S i).direction + 1 < Module.finrank ℝ V)
    {x y : P} (hx : ∀ i, x ∉ S i) (hy : ∀ i, y ∉ S i)
    {U : Set P} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, ∀ i (t : ℝ),
      AffineMap.lineMap x z t ∉ S i ∧ AffineMap.lineMap y z t ∉ S i := by
  obtain ⟨z, hzU, _, hz⟩ := exists_mem_open_two_lineMaps_avoid_set S hS
    (fun i : Empty => nomatch i) (fun i => nomatch i) (E := ⋃ i, (S i : Set P))
    Subset.rfl (by simpa using hx) (by simpa using hy) hU hne
  exact ⟨z, hzU, fun i t =>
    ⟨fun h => (hz t).1 (mem_iUnion.mpr ⟨i, h⟩),
      fun h => (hz t).2 (mem_iUnion.mpr ⟨i, h⟩)⟩⟩

end Topology

end AffineSubspace

namespace TauCeti

section Hyperplane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A set covered by countably many affine subspaces of ambient codimension at least two
has dense complement in a hyperplane: every point of the hyperplane is a limit of points
of the hyperplane outside the set. -/
theorem hyperplane_subset_closure_sdiff_of_finrank {ι : Sort*} [Countable ι]
    {ν : V →L[ℝ] ℝ} {b : ℝ} {Z : Set V} (hν : ν ≠ 0)
    (E : ι → AffineSubspace ℝ V) (hZE : Z ⊆ ⋃ i, (E i : Set V))
    (hE : ∀ i, Module.finrank ℝ (E i).direction + 1 < Module.finrank ℝ V) :
    {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z) := by
  intro x hx
  have hx' : ν x = b := hx
  -- The hyperplane is the affine subspace through `x` with direction `ker ν`.
  let A : AffineSubspace ℝ V := .mk' x (LinearMap.ker ν.toLinearMap)
  have hA : ∀ y ∈ A, ν y = b := fun y hy => by
    have := AffineSubspace.mem_mk'.mp hy
    simpa [sub_eq_zero, hx'] using this
  have hdir : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V := by
    rw [AffineSubspace.direction_mk']
    exact Module.Dual.finrank_ker_add_one_of_ne_zero (f := ν.toLinearMap)
      (fun h => hν (ContinuousLinearMap.coe_injective h))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hzE⟩ := A.exists_mem_open_avoid_of_finrank_lt E
    (fun i => by have := hE i; omega) (U := Subtype.val ⁻¹' Metric.ball x ε)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
    ⟨⟨x, AffineSubspace.self_mem_mk' x _⟩, Metric.mem_ball_self hε⟩
  exact ⟨z, ⟨hA z z.2, fun hzZ => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hZE hzZ)
    exact hzE i hi⟩, by simpa [dist_comm] using hz⟩

end Hyperplane

namespace ExceptionalArrangement

section Topology

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]

/-- Generic points of a finite exceptional arrangement form an open set. -/
theorem isOpen_isGeneric (E : ExceptionalArrangement ℝ P) : IsOpen {x | E.IsGeneric x} := by
  convert
    AffineSubspace.isOpen_genericLocus (fun S : E.exceptions => S.1) using 1
  ext x
  simp [isGeneric_iff]

/-- Generic points of a finite exceptional arrangement form a dense set. -/
theorem dense_isGeneric (E : ExceptionalArrangement ℝ P) : Dense {x | E.IsGeneric x} := by
  convert
    AffineSubspace.dense_genericLocus (fun S : E.exceptions => S.1)
      (fun S => E.proper S.1 S.2) using 1
  ext x
  simp [isGeneric_iff]

/-- A countable family of finite arrangements has dense common generic locus. -/
theorem dense_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement ℝ P) : Dense {x | ∀ i, (E i).IsGeneric x} := by
  convert
    AffineSubspace.dense_genericLocus
      (fun p : Σ i, (E i).exceptions => p.2.1)
      (fun p => (E p.1).proper p.2.1 p.2.2) using 1
  ext x
  simp [isGeneric_iff, Sigma.forall]

/-- The common generic locus of countably many finite arrangements is a Gδ set. -/
theorem isGδ_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement ℝ P) : IsGδ {x | ∀ i, (E i).IsGeneric x} := by
  convert
    AffineSubspace.isGδ_genericLocus (fun p : Σ i, (E i).exceptions => p.2.1) using 1
  ext x
  simp [isGeneric_iff, Sigma.forall]

end Topology

end ExceptionalArrangement

end TauCeti
