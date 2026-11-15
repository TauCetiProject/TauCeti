/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Coordinate graph charts on finite Grassmannians

A matrix `A : Matrix (Fin r) (Fin q) 𝕜` describes the graph of the map `x ↦ x ᵥ* A`
in `𝕜^(r+q)`. The graph map is an open embedding for a Hausdorff topological field, with the
existing frame-quotient topology on the finite Grassmannian. Its inverse is the coordinate graph
chart. A frame belongs to this chart exactly when its first square block is invertible;
its chart coordinate is the inverse of that block times the remaining block.

This gives the usual affine coordinate neighbourhood of the first coordinate plane,
including zero-dimensional blocks. The construction uses Mathlib's matrix inverse and
Tau Ceti's frame-span open quotient, without changing the Grassmannian carrier or topology.

The graph description of Grassmannian charts is classical; see Milnor–Stasheff,
*Characteristic Classes*, §5.
-/

public section

open Set Matrix Topology

namespace TauCeti
namespace finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] {r q : ℕ}

/-- The normalized frame of a graph: its first block is the identity and its second block is
`A`. Rows, like all finite Grassmannian frames, are indexed starting at zero. -/
def graphFrame (A : Matrix (Fin r) (Fin q) 𝕜) : finiteFullRankFrame 𝕜 r (r + q) :=
  ⟨fun i ↦ Fin.append (Pi.single i 1) (A i), by
    have h : LinearIndependent 𝕜 (fun i : Fin r ↦ Pi.single i (1 : 𝕜)) :=
      by
        convert (Pi.basisFun 𝕜 (Fin r)).linearIndependent using 1
        funext i
        exact (Pi.basisFun_apply 𝕜 (Fin r) i).symm
    apply LinearIndependent.of_comp (LinearMap.funLeft 𝕜 𝕜 (Fin.castAdd q))
    convert h using 1
    funext i j
    simp [LinearMap.funLeft, Function.comp_def]⟩

@[simp]
theorem graphFrame_castAdd (A : Matrix (Fin r) (Fin q) 𝕜) (i j : Fin r) :
    (graphFrame A).1 i (Fin.castAdd q j) = (Pi.single i 1 : Fin r → 𝕜) j := by
  simp [graphFrame]

@[simp]
theorem graphFrame_natAdd (A : Matrix (Fin r) (Fin q) 𝕜) (i : Fin r) (j : Fin q) :
    (graphFrame A).1 i (Fin.natAdd r j) = A i j := by
  simp [graphFrame]

/-- The graph of `x ↦ x ᵥ* A`, as an `r`-plane in the existing finite Grassmannian. -/
noncomputable def graph (A : Matrix (Fin r) (Fin q) 𝕜) : finiteGrassmannian 𝕜 r (r + q) :=
  frameSpan (graphFrame A)

/-- The normalized graph frame spans the graph plane. -/
@[simp]
theorem frameSpan_graphFrame (A : Matrix (Fin r) (Fin q) 𝕜) :
    frameSpan (graphFrame A) = graph A := by rw [graph]

/-- Membership in the graph is the equation relating its two coordinate blocks. -/
@[simp]
theorem mem_graph_iff (A : Matrix (Fin r) (Fin q) 𝕜) (v : Fin (r + q) → 𝕜) :
    v ∈ (graph A).1 ↔
      (fun j ↦ v (Fin.natAdd r j)) = (fun i ↦ v (Fin.castAdd q i)) ᵥ* A := by
  rw [graph, coe_frameSpan, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    ext j
    simp [vecMul, dotProduct, Pi.single_apply]
  · intro hv
    refine ⟨fun i ↦ v (Fin.castAdd q i), ?_⟩
    ext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simp [Pi.single_apply]
    · simpa [vecMul, dotProduct] using (congrFun hv j).symm

/-- Graph coordinates determine their plane uniquely. -/
theorem graph_injective : Function.Injective (graph : Matrix (Fin r) (Fin q) 𝕜 → _) := by
  intro A B h
  ext i j
  have hm : (graphFrame A).1 i ∈ (graph B).1 := by
    rw [← h, graph, coe_frameSpan]
    exact Submodule.subset_span (mem_range_self i)
  have he := congrFun ((mem_graph_iff B _).1 hm) j
  simpa [vecMul, dotProduct, Pi.single_apply] using he

private def firstBlock (f : finiteFullRankFrame 𝕜 r (r + q)) : Matrix (Fin r) (Fin r) 𝕜 :=
  fun i j ↦ f.1 i (Fin.castAdd q j)

private def lastBlock (f : finiteFullRankFrame 𝕜 r (r + q)) : Matrix (Fin r) (Fin q) 𝕜 :=
  fun i j ↦ f.1 i (Fin.natAdd r j)

private theorem firstBlock_graphFrame (A : Matrix (Fin r) (Fin q) 𝕜) :
    firstBlock (graphFrame A) = 1 := by
  ext i j
  simp [firstBlock, Matrix.one_apply, Pi.single_apply, eq_comm]

private theorem firstBlock_smul (M : GL (Fin r) 𝕜)
    (f : finiteFullRankFrame 𝕜 r (r + q)) :
    firstBlock (M • f) = (M : Matrix (Fin r) (Fin r) 𝕜) * firstBlock f := by
  ext i j
  simp [firstBlock, finiteFullRankFrame.coe_smul, Matrix.mul_apply]

private theorem lastBlock_smul (M : GL (Fin r) 𝕜)
    (f : finiteFullRankFrame 𝕜 r (r + q)) :
    lastBlock (M • f) = (M : Matrix (Fin r) (Fin r) 𝕜) * lastBlock f := by
  ext i j
  simp [lastBlock, finiteFullRankFrame.coe_smul, Matrix.mul_apply]

private theorem frameSpan_eq_graph (f : finiteFullRankFrame 𝕜 r (r + q))
    (hf : IsUnit (firstBlock f)) :
    frameSpan f = graph ((firstBlock f)⁻¹ * lastBlock f) := by
  let M : GL (Fin r) 𝕜 := hf.unit⁻¹
  have hfirst : firstBlock (M • f) = 1 := by
    rw [firstBlock_smul]
    exact hf.val_inv_mul
  have hlast : lastBlock (M • f) = (firstBlock f)⁻¹ * lastBlock f := by
    rw [lastBlock_smul]
    congr 1
    exact Matrix.coe_units_inv hf.unit
  have he : M • f = graphFrame ((firstBlock f)⁻¹ * lastBlock f) := by
    apply Subtype.ext
    funext i j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simpa [firstBlock, Matrix.one_apply, Pi.single_apply, eq_comm] using
        congrFun (congrFun hfirst i) j
    · simpa [lastBlock] using congrFun (congrFun hlast i) j
  rw [← frameSpan_smul M f, he]
  exact frameSpan_graphFrame _

/-- A frame represents a graph precisely when its initial square block is invertible. The
coordinate is obtained by normalizing that block to the identity. -/
theorem frameSpan_eq_graph_iff (f : finiteFullRankFrame 𝕜 r (r + q))
    (A : Matrix (Fin r) (Fin q) 𝕜) :
    frameSpan f = graph A ↔
      IsUnit (Matrix.submatrix f.1 id (Fin.castAdd q)) ∧
        (Matrix.submatrix f.1 id (Fin.castAdd q))⁻¹ *
          Matrix.submatrix f.1 id (Fin.natAdd r) = A := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := frameSpan_eq_frameSpan_iff.1
      ((frameSpan_graphFrame A).trans h.symm)
    subst f
    have hu : IsUnit (firstBlock (M • graphFrame A)) := by
      rw [firstBlock_smul, firstBlock_graphFrame, Matrix.mul_one]
      exact M.isUnit
    exact ⟨hu, graph_injective ((frameSpan_eq_graph _ hu).symm.trans h)⟩
  · rintro ⟨hf, rfl⟩
    exact frameSpan_eq_graph f hf

variable [TopologicalSpace 𝕜]

/-- Graph frames vary continuously with their matrix entries. -/
@[fun_prop]
theorem continuous_graphFrame :
    Continuous (graphFrame : Matrix (Fin r) (Fin q) 𝕜 → finiteFullRankFrame 𝕜 r (r + q)) := by
  unfold graphFrame
  refine (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_).subtype_mk _
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simpa only [Fin.append_left] using
      (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin q) 𝕜 ↦
        (Pi.single i 1 : Fin r → 𝕜) j)
  · simpa only [Fin.append_right, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i) :
        Continuous fun A : Matrix (Fin r) (Fin q) 𝕜 ↦ A i j)

/-- The graph map is continuous for the frame-quotient topology. -/
@[fun_prop]
theorem continuous_graph :
    Continuous (graph : Matrix (Fin r) (Fin q) 𝕜 → finiteGrassmannian 𝕜 r (r + q)) := by
  unfold graph
  exact continuous_frameSpan.comp continuous_graphFrame

private theorem continuous_firstBlock :
    Continuous (firstBlock : finiteFullRankFrame 𝕜 r (r + q) → _) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (Fin.castAdd q j)).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem continuous_lastBlock :
    Continuous (lastBlock : finiteFullRankFrame 𝕜 r (r + q) → _) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (Fin.natAdd r j)).comp ((continuous_apply i).comp continuous_subtype_val)

variable [IsTopologicalDivisionRing 𝕜] [T1Space 𝕜]

private theorem isOpen_firstBlock_isUnit :
    IsOpen {f : finiteFullRankFrame 𝕜 r (r + q) | IsUnit (firstBlock f)} := by
  simp_rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isOpen_ne.preimage continuous_firstBlock.matrix_det

omit [T1Space 𝕜] in
private theorem continuousOn_normalize :
    ContinuousOn (fun f : finiteFullRankFrame 𝕜 r (r + q) ↦
      (firstBlock f)⁻¹ * lastBlock f) {f | IsUnit (firstBlock f)} := by
  have hmul : Continuous fun p : Matrix (Fin r) (Fin r) 𝕜 × Matrix (Fin r) (Fin q) 𝕜 ↦
      p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  intro f hf
  have hinv : ContinuousAt Inv.inv (firstBlock f) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hf))
  exact hmul.continuousAt.comp_continuousWithinAt
    (((hinv.comp continuous_firstBlock.continuousAt).prodMk
      continuous_lastBlock.continuousAt).continuousWithinAt)

/-- The graphs form an open coordinate neighbourhood in the finite Grassmannian, and their
matrix coordinates give its topology. No positivity assumption on either block size is needed. -/
theorem isOpenEmbedding_graph :
    IsOpenEmbedding (graph : Matrix (Fin r) (Fin q) 𝕜 → finiteGrassmannian 𝕜 r (r + q)) := by
  refine .of_continuous_injective_isOpenMap continuous_graph graph_injective fun s hs ↦ ?_
  rw [← isQuotientMap_frameSpan.isOpen_preimage]
  have he : frameSpan ⁻¹' (graph '' s) =
      {f : finiteFullRankFrame 𝕜 r (r + q) | IsUnit (firstBlock f)} ∩
        (fun f ↦ (firstBlock f)⁻¹ * lastBlock f) ⁻¹' s := by
    ext f
    constructor
    · rintro ⟨A, hA, hf⟩
      obtain ⟨hu, he⟩ := (frameSpan_eq_graph_iff f A).1 hf.symm
      have hs' := he.symm ▸ hA
      exact ⟨hu, hs'⟩
    · rintro ⟨hu, hs⟩
      exact ⟨_, hs, (frameSpan_eq_graph f hu).symm⟩
  rw [he]
  exact continuousOn_normalize.isOpen_inter_preimage isOpen_firstBlock_isUnit hs

/-- The coordinate graph chart at the first coordinate plane. Its source consists of planes
transverse to the last coordinate block, and its target is the entire matrix space. -/
noncomputable def graphChart :
    OpenPartialHomeomorph (finiteGrassmannian 𝕜 r (r + q)) (Matrix (Fin r) (Fin q) 𝕜) :=
  (isOpenEmbedding_graph.toOpenPartialHomeomorph graph).symm

@[simp]
theorem graphChart_source :
    (graphChart (𝕜 := 𝕜) (r := r) (q := q)).source = range graph := by
  simp [graphChart]

@[simp]
theorem graphChart_target :
    (graphChart (𝕜 := 𝕜) (r := r) (q := q)).target = univ := by
  simp [graphChart]

@[simp]
theorem graphChart_symm_apply (A : Matrix (Fin r) (Fin q) 𝕜) :
    (graphChart (𝕜 := 𝕜)).symm A = graph A := by
  simp [graphChart]

@[simp]
theorem graphChart_graph (A : Matrix (Fin r) (Fin q) 𝕜) :
    graphChart (graph A) = A := by
  unfold graphChart
  exact isOpenEmbedding_graph.toOpenPartialHomeomorph_left_inv graph

/-- The graph chart domain is detected by the initial square block of any representing frame. -/
theorem frameSpan_mem_graphChart_source_iff (f : finiteFullRankFrame 𝕜 r (r + q)) :
    frameSpan f ∈ (graphChart (𝕜 := 𝕜)).source ↔
      IsUnit (Matrix.submatrix f.1 id (Fin.castAdd q)) := by
  rw [graphChart_source]
  exact ⟨fun ⟨A, hA⟩ ↦ ((frameSpan_eq_graph_iff f A).1 hA.symm).1,
    fun hf ↦ ⟨_, (frameSpan_eq_graph f hf).symm⟩⟩

/-- In graph coordinates a frame is normalized by left-multiplying its last block by the inverse
of its first block. -/
theorem graphChart_frameSpan (f : finiteFullRankFrame 𝕜 r (r + q))
    (hf : IsUnit (Matrix.submatrix f.1 id (Fin.castAdd q))) :
    graphChart (frameSpan f) = (Matrix.submatrix f.1 id (Fin.castAdd q))⁻¹ *
      Matrix.submatrix f.1 id (Fin.natAdd r) := by
  rw [frameSpan_eq_graph f hf, graphChart_graph]
  rfl

end finiteGrassmannian
end TauCeti
