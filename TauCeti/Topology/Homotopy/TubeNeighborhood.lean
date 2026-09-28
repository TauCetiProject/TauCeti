/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.CompactOpen
public import TauCeti.Topology.Homotopy.Path

/-!
# Tube neighborhoods in path space

A *tube* in the space of paths in `X` is determined by a partition `0 = t₀ ≤ ⋯ ≤ tₙ = 1` of the
unit interval, open sets `Uᵢ` for the segments `[tᵢ, tᵢ₊₁]`, and open path-connected sets `Vⱼ` for
the vertices `tⱼ`, each contained in the adjacent segment sets. A path lies in the tube if it
maps each segment into `Uᵢ` and each vertex into `Vⱼ`. Tubes are open in the compact-open
topology. When each `Uᵢ` is path-homotopy-trivial (`IsPathHomotopyTrivial`), two paths with the
same endpoints in a common tube are homotopic: connect corresponding vertices by paths in `Vⱼ`, use
homotopy triviality of `Uᵢ` on each rectangle, and paste
(`Path.Homotopic.trans_of_subpath_trans`).

## Main definitions

* `Path.Tube X n`: the segment sets `Uᵢ` and vertex sets `Vⱼ` of a tube, with their properties.
* `Path.IsInTube f part T`: the predicate that `f : I → X` lies in the tube.

## Main statements

* `Path.exists_isInTube`: in a locally path-connected space, a path lies in a tube if each
  point on it has an open, path-homotopy-trivial neighborhood.
* `unitInterval.Partition.isOpen_setOf_mapsTo_Icc_and_mem`: the maps sending the segments and
  vertices of a partition into given open sets form an open set in the compact-open topology.
* `Path.Tube.isOpen_setOf_isInTube`: hence tubes are open.
* `Path.IsInTube.exists_trans_homotopic`: two paths with the same source in a common tube become
  homotopic after appending to the first a path in the last vertex set.
* `Path.IsInTube.homotopic`: two paths with the same endpoints in a common tube are homotopic.

The application to semilocally simply connected spaces (path-homotopy classes are open, so
`Path.Homotopic.Quotient` is discrete) is in
`TauCeti/AlgebraicTopology/SemilocallySimplyConnected/On.lean`.
-/

-- Ported from https://github.com/leanprover-community/mathlib4/pull/44183.

noncomputable section

open Set Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- The data of a tube with `n` segments: open path-homotopy-trivial sets `U i` for the segments,
and open path-connected sets `V j` for the vertices, with `V j` contained in the `U i` of the
adjacent segments. -/
public structure Path.Tube (X : Type*) [TopologicalSpace X] (n : ℕ) where
  /-- The segment sets. -/
  U : Fin n → Set X
  /-- The vertex sets. -/
  V : Fin (n + 1) → Set X
  /-- Each segment set is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- Each segment set is path-homotopy-trivial. -/
  isPathHomotopyTrivial_U : ∀ i, IsPathHomotopyTrivial (U i)
  /-- Each vertex set is open. -/
  isOpen_V : ∀ j, IsOpen (V j)
  /-- Each vertex set is path-connected. -/
  isPathConnected_V : ∀ j, IsPathConnected (V j)
  /-- The vertex set at the start of a segment lies in that segment's set. -/
  V_castSucc_subset : ∀ i : Fin n, V i.castSucc ⊆ U i
  /-- The vertex set at the end of a segment lies in that segment's set. -/
  V_succ_subset : ∀ i : Fin n, V i.succ ⊆ U i

/-- `f : I → X` lies in the tube determined by `part` and `T` if it maps each segment
`[tᵢ, tᵢ₊₁]` into `U i` and each vertex `tⱼ` into `V j`. -/
public structure Path.IsInTube {n : ℕ} (f : I → X) (part : unitInterval.Partition n)
    (T : Path.Tube X n) : Prop where
  /-- Each segment is mapped into its segment set. -/
  mapsTo : ∀ i : Fin n, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)
  /-- Each vertex is mapped into its vertex set. -/
  mem_V : ∀ j, f (part.t j) ∈ T.V j

variable {n : ℕ} {part : unitInterval.Partition n} {T : Path.Tube X n}

/-- Unbundled form of `Path.IsInTube`. -/
@[simp] public theorem Path.isInTube_iff {f : I → X} :
    Path.IsInTube f part T ↔
      (∀ i : Fin n, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)) ∧
        ∀ j, f (part.t j) ∈ T.V j :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A path in a tube has each of its segment subpaths inside the corresponding segment set. -/
public theorem Path.IsInTube.range_subpath_subset {x y : X} {γ : Path x y}
    (hγ : Path.IsInTube γ part T) (i : Fin n) :
    range (γ.subpath (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i := by
  rintro _ ⟨t, rfl⟩
  exact hγ.mapsTo i
    ⟨Icc.le_convexComb (part.t_castSucc_le_succ i) t,
      Icc.convexComb_le (part.t_castSucc_le_succ i) t⟩

/-! ### Openness of tubes -/

/-- The maps `f : C(I, X)` sending each segment `[tᵢ, tᵢ₊₁]` of a partition into an open set `U i`
and each vertex `tⱼ` into an open set `V j` form an open set in the compact-open topology. -/
public theorem unitInterval.Partition.isOpen_setOf_mapsTo_Icc_and_mem
    (part : unitInterval.Partition n) {U : Fin n → Set X} {V : Fin (n + 1) → Set X}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j)) :
    IsOpen {f : C(I, X) | (∀ i : Fin n, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (U i)) ∧
      ∀ j, f (part.t j) ∈ V j} := by
  simp only [ofPred_and, ofPred_forall]
  refine (isOpen_iInter_of_finite fun i ↦ ?_).inter (isOpen_iInter_of_finite fun j ↦ ?_)
  · exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (hU i)
  · exact (hV j).preimage (continuous_eval_const _)

/-- A tube is open in the compact-open topology on `C(I, X)`. -/
public theorem Path.Tube.isOpen_setOf_isInTube (part : unitInterval.Partition n)
    (T : Path.Tube X n) :
    IsOpen {f : C(I, X) | Path.IsInTube f part T} := by
  simpa only [Path.isInTube_iff] using part.isOpen_setOf_mapsTo_Icc_and_mem T.isOpen_U T.isOpen_V

/-- A tube is open in the path space `Path x y`. -/
public theorem Path.Tube.isOpen_setOf_isInTube_path (part : unitInterval.Partition n)
    (T : Path.Tube X n) (x y : X) : IsOpen {γ : Path x y | Path.IsInTube γ part T} := by
  -- The topology on `Path x y` is induced by `Path.toContinuousMap`; rewrite the preimage of the
  -- tube in `C(I, X)` along it using `Path.coe_toContinuousMap`.
  have h := (T.isOpen_setOf_isInTube part).preimage
    (continuous_induced_dom : Continuous (Path.toContinuousMap : Path x y → C(I, X)))
  simpa only [preimage_ofPred_eq, Path.coe_toContinuousMap] using h

/-! ### Existence of tubes -/

/-- If every point on a path has an open, path-homotopy-trivial neighborhood, then the path
lies in a tube. -/
public theorem Path.exists_isInTube [LocallyPathConnectedSpace X] {x y : X} (γ : Path x y)
    (h : ∀ z ∈ range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ IsPathHomotopyTrivial U) :
    ∃ (n : ℕ) (part : unitInterval.Partition n) (T : Path.Tube X n), Path.IsInTube γ part T := by
  obtain ⟨n, part, h_seg⟩ := γ.exists_partition_with_property IsPathHomotopyTrivial h
  choose U hU_open hU hU_mapsTo using h_seg
  obtain ⟨V, hV_open, hV_pathConn, hγV, hV_castSucc, hV_succ⟩ :=
    unitInterval.exists_vertex_family part.mono hU_open hU_mapsTo
  exact ⟨n, part, ⟨U, V, hU_open, hU, hV_open, hV_pathConn, hV_castSucc, hV_succ⟩,
    hU_mapsTo, hγV⟩

/-! ### Paths in a common tube are homotopic -/

/-- Rung paths at the vertices, connecting two functions in a common tube. -/
private theorem Path.IsInTube.exists_rungs {x y x' y' : X} {γ : Path x y} {γ' : Path x' y'}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) :
    ∃ α : (j : Fin (n + 1)) → Path (γ (part.t j)) (γ' (part.t j)), ∀ j, range (α j) ⊆ T.V j := by
  have h j := (T.isPathConnected_V j).joinedIn _ (hγ.mem_V j) _ (hγ'.mem_V j)
  exact ⟨fun j ↦ (h j).somePath, fun j ↦ range_subset_iff.mpr (h j).somePath_mem⟩

/-- Two paths with the same source in a common tube are homotopic after appending to the first
a path in the last vertex set of the tube. -/
public theorem Path.IsInTube.exists_trans_homotopic {x y y' : X} {γ : Path x y} {γ' : Path x y'}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) :
    ∃ ρ : Path y y', range ρ ⊆ T.V (Fin.last n) ∧ (γ.trans ρ).Homotopic γ' := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n =>
  obtain ⟨α, hα⟩ := hγ.exists_rungs hγ'
  have h_rect : ∀ i : Fin (n + 1),
      ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ)).Homotopic
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))) := fun i ↦
    isPathHomotopyTrivial_def.mp (T.isPathHomotopyTrivial_U i) _ _
      (by
        rw [Path.trans_range]
        exact union_subset (hγ.range_subpath_subset i) ((hα _).trans (T.V_succ_subset i)))
      (by
        rw [Path.trans_range]
        exact union_subset ((hα _).trans (T.V_castSucc_subset i)) (hγ'.range_subpath_subset i))
  have h_α₀ : ((α 0).cast (by simp) (by simp)).Homotopic (Path.refl x) :=
    (T.isPathHomotopyTrivial_U 0).nullhomotopic _
      (by simpa using (hα 0).trans (T.V_castSucc_subset 0))
  exact ⟨(α (Fin.last _)).cast (by simp) (by simp), by simpa using hα _,
    (Path.Homotopic.trans_of_subpath_trans γ γ' part α h_rect).trans
      (Path.Homotopic.trans_left_of_nullhomotopic h_α₀)⟩

/-- Two paths with the same endpoints in a common tube are homotopic. -/
public theorem Path.IsInTube.homotopic {x y : X} {γ γ' : Path x y}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) : γ.Homotopic γ' := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n =>
  obtain ⟨ρ, hρ, h⟩ := hγ.exists_trans_homotopic hγ'
  have hρ_null : ρ.Homotopic (Path.refl y) :=
    (T.isPathHomotopyTrivial_U (Fin.last n)).nullhomotopic ρ
      (hρ.trans (T.V_succ_subset (Fin.last n)))
  exact (Path.Homotopic.trans_right_of_nullhomotopic hρ_null).symm.trans h

end
