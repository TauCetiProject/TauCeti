/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.FiniteDimensional
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Instances.Sign
public import TauCeti.LinearAlgebra.Prod

/-!
# Graph coordinates for negative subspaces

For the normalized quadratic form `Q(u,v) = -‖u‖² + ‖v‖²`, strict negativity at every
nonzero vector of a subspace is equivalent to `‖v‖ < ‖u‖`; such a subspace is called
*split-negative* (`Submodule.IsSplitNegative`). It projects
injectively to the first factor. When its dimension equals that of the first factor,
it is the graph of a unique continuous linear map `A` with `‖A‖ < 1`.

These are the graph coordinates used to compare negative spaces in Morse charts. Their
parameter domain is the open operator-norm unit ball, rather than the closed ball: a
map of norm one can have a null vector in its graph. The classification also applies
to a real normed first factor and a real seminormed second factor; only in inner product
spaces is `Q` a quadratic form. Only the first factor needs to be finite dimensional.

The main result is
`Submodule.existsUnique_eq_graph_iff_finrank_eq_and_isSplitNegative`. The preceding dimension
bound and the final maximality theorem explain why subspaces of this dimension are
maximal among negative subspaces. The statements include a zero-dimensional first factor.
In these graph coordinates the space of maximal negative subspaces is the open unit ball of
`E →L[ℝ] F`, which is contractible (`Metric.contractibleSpace_ball`) by the straight-line
contraction `A ↦ t • A`.

Graph coordinates also compare orientations of different negative subspaces. A frame of a
negative subspace is an operator `L : E →L[ℝ] E × F` whose nonzero values lie in the negative
cone; its negative block `fst ∘ L` is then invertible, and the sign of its determinant records
the orientation of the frame relative to `E`. Along a continuous family of such frames over a
preconnected parameter space this sign is constant
(`ContinuousLinearMap.det_fst_comp_pos_iff_of_norm_snd_lt`), so it is the orientation transported
through the space of negative subspaces. The straight-line contraction acts on frames as
`ContinuousLinearMap.negativeContraction`, `u ↦ ((L u).1, t • (L u).2)`: if the image of `L` is
the graph of `A`, the image of its contraction at time `t` is the graph of `t • A`
(`ContinuousLinearMap.range_negativeContraction`). It stays negative for `|t| ≤ 1`
(`ContinuousLinearMap.norm_snd_negativeContraction_lt`) and joins `L` to the frame
`inl ∘ fst ∘ L` of `E × 0`. Hence `det (fst ∘ L) > 0` exactly when `L` can be moved through
negative frames to a positively oriented frame of `E × 0`
(`ContinuousLinearMap.det_fst_comp_pos_iff_exists_path_of_norm_snd_lt`).

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, change of negative spaces
  in the comparison of Morse coordinates.

The graph construction uses Mathlib's `Submodule.exists_eq_graph` (the vertical line test).
-/

public section

open Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

namespace ContinuousLinearMap

/-- A frame whose nonzero values lie strictly inside the negative cone has injective negative
block. No finite-dimensionality is needed, and the frame may be defined on any space. -/
theorem injective_fst_comp_of_norm_snd_lt {V : Type*} [TopologicalSpace V] [AddCommGroup V]
    [Module ℝ V] (L : V →L[ℝ] E × F) (hL : ∀ u, u ≠ 0 → ‖(L u).2‖ < ‖(L u).1‖) :
    Injective ((fst ℝ E F).comp L) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  by_contra hne
  have h := hL u hne
  have h0 : (L u).1 = 0 := by simpa using hu
  rw [h0, norm_zero] at h
  exact (norm_nonneg _).not_gt h

/-- A frame whose nonzero values lie strictly inside the negative cone has invertible negative
block. -/
theorem det_fst_comp_ne_zero_of_norm_snd_lt [FiniteDimensional ℝ E] (L : E →L[ℝ] E × F)
    (hL : ∀ u, u ≠ 0 → ‖(L u).2‖ < ‖(L u).1‖) : ((fst ℝ E F).comp L).det ≠ 0 := by
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot]
  exact L.injective_fst_comp_of_norm_snd_lt hL

/-- **Orientation transport through negative subspaces.** Along a continuous family of frames
whose nonzero values lie strictly inside the negative cone, parametrized by a preconnected space,
the sign of the determinant of the negative block is constant. -/
theorem det_fst_comp_pos_iff_of_norm_snd_lt [FiniteDimensional ℝ E] {X : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] {L : X → E →L[ℝ] E × F} (hcont : Continuous L)
    (hL : ∀ x u, u ≠ 0 → ‖(L x u).2‖ < ‖(L x u).1‖) (x y : X) :
    0 < ((fst ℝ E F).comp (L x)).det ↔ 0 < ((fst ℝ E F).comp (L y)).det := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff (a := ((fst ℝ E F).comp (L y)).det),
    isPreconnected_univ.sign_eq_of_continuousOn (f := fun z ↦ ((fst ℝ E F).comp (L z)).det)
      (continuous_det.comp ((compL ℝ E (E × F) E (fst ℝ E F)).continuous.comp hcont)).continuousOn
      (fun z _ ↦ (L z).det_fst_comp_ne_zero_of_norm_snd_lt (hL z)) trivial trivial]

/-- The straight-line contraction of a frame `L` in graph coordinates: the frame
`u ↦ ((L u).1, t • (L u).2)`. It is `L` at `t = 1` and a frame of `E × 0` at `t = 0`. -/
noncomputable def negativeContraction (L : E →L[ℝ] E × F) (t : ℝ) : E →L[ℝ] E × F :=
  inl ℝ E F ∘L fst ℝ E F ∘L L + t • (inr ℝ E F ∘L snd ℝ E F ∘L L)

@[simp]
theorem negativeContraction_apply (L : E →L[ℝ] E × F) (t : ℝ) (u : E) :
    L.negativeContraction t u = ((L u).1, t • (L u).2) := by
  simp [negativeContraction]

@[simp]
theorem negativeContraction_one (L : E →L[ℝ] E × F) : L.negativeContraction 1 = L := by
  ext u <;> simp

@[simp]
theorem negativeContraction_zero (L : E →L[ℝ] E × F) :
    L.negativeContraction 0 = inl ℝ E F ∘L fst ℝ E F ∘L L := by
  ext u <;> simp

@[continuity, fun_prop]
theorem continuous_negativeContraction (L : E →L[ℝ] E × F) :
    Continuous L.negativeContraction :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- The straight-line contraction of a frame is the contraction of its graph coordinate: if
the image of `L` is the graph of `A`, the image of `L.negativeContraction t` is the graph of
`t • A`. -/
theorem range_negativeContraction {L : E →L[ℝ] E × F} {A : E →L[ℝ] F}
    (hA : LinearMap.range (L : E →ₗ[ℝ] E × F) = A.toLinearMap.graph) (t : ℝ) :
    LinearMap.range (L.negativeContraction t : E →ₗ[ℝ] E × F) = (t • A).toLinearMap.graph := by
  have hL (u : E) : (L u).2 = A (L u).1 := by
    have : L u ∈ A.toLinearMap.graph := hA ▸ LinearMap.mem_range_self (L : E →ₗ[ℝ] E × F) u
    simpa using this
  ext z
  simp only [LinearMap.mem_range, coe_coe, negativeContraction_apply, LinearMap.mem_graph_iff,
    smul_apply]
  constructor
  · rintro ⟨u, rfl⟩
    simp [hL]
  · intro hz
    obtain ⟨u, hu⟩ : (z.1, A z.1) ∈ LinearMap.range (L : E →ₗ[ℝ] E × F) := hA ▸ by simp
    rw [coe_coe] at hu
    exact ⟨u, Prod.ext (by simp [hu]) (by simp [hu, hz])⟩

/-- The straight-line contraction keeps a negative frame negative for `|t| ≤ 1`. -/
theorem norm_snd_negativeContraction_lt (L : E →L[ℝ] E × F)
    (hL : ∀ u, u ≠ 0 → ‖(L u).2‖ < ‖(L u).1‖) {t : ℝ} (ht : |t| ≤ 1) {u : E} (hu : u ≠ 0) :
    ‖(L.negativeContraction t u).2‖ < ‖(L.negativeContraction t u).1‖ := by
  rw [negativeContraction_apply, norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans_lt (hL u hu)

/-- **Orientation of a negative frame.** A frame `L₀` whose nonzero values lie strictly inside
the negative cone has negative block of positive determinant exactly when it can be moved,
through such frames, to a frame `inl ∘ B` of `E × 0` with `det B > 0`. The straight-line
contraction gives such a path, with `B = fst ∘ L₀`. -/
theorem det_fst_comp_pos_iff_exists_path_of_norm_snd_lt [FiniteDimensional ℝ E]
    (L₀ : E →L[ℝ] E × F) (hL₀ : ∀ u, u ≠ 0 → ‖(L₀ u).2‖ < ‖(L₀ u).1‖) :
    0 < ((fst ℝ E F).comp L₀).det ↔
      ∃ (L : C(unitInterval, E →L[ℝ] E × F)) (B : E →L[ℝ] E),
        L 0 = L₀ ∧ L 1 = (inl ℝ E F).comp B ∧
        (∀ t u, u ≠ 0 → ‖(L t u).2‖ < ‖(L t u).1‖) ∧ 0 < B.det := by
  constructor
  · intro hdet
    refine ⟨⟨fun t ↦ L₀.negativeContraction (1 - t), by fun_prop⟩, (fst ℝ E F).comp L₀,
      by simp, by simp, fun t u hu ↦ L₀.norm_snd_negativeContraction_lt hL₀ ?_ hu, hdet⟩
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2]
  · rintro ⟨L, B, h₀, h₁, hL, hB⟩
    rwa [← h₀, det_fst_comp_pos_iff_of_norm_snd_lt L.continuous hL 0 1, h₁, ← comp_assoc,
      fst_comp_inl, id_comp]

end ContinuousLinearMap

namespace Submodule

variable {W W' : Submodule ℝ (E × F)}

/-- A submodule `W` of `E × F` is *split-negative* if the split indefinite form
`Q(u, v) = -‖u‖² + ‖v‖²` is negative on every nonzero vector of `W`: `‖v‖ < ‖u‖` for every
nonzero `(u, v) ∈ W`. -/
def IsSplitNegative (W : Submodule ℝ (E × F)) : Prop :=
  ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖

theorem isSplitNegative_iff : W.IsSplitNegative ↔ ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖ :=
  Iff.rfl

@[simp]
theorem isSplitNegative_bot : (⊥ : Submodule ℝ (E × F)).IsSplitNegative := by
  intro w hw hw0
  exact absurd ((mem_bot ℝ).1 hw) hw0

/-- A submodule of a split-negative subspace is split-negative. -/
theorem IsSplitNegative.mono (hW : W.IsSplitNegative) (h : W' ≤ W) : W'.IsSplitNegative :=
  fun w hw ↦ hW w (h hw)

/-- A nonzero vector of a split-negative subspace has nonzero first component. -/
theorem IsSplitNegative.fst_ne_zero (hW : W.IsSplitNegative) {w : E × F} (hw : w ∈ W)
    (hw0 : w ≠ 0) : w.1 ≠ 0 := by
  intro h
  have := hW w hw hw0
  rw [h, norm_zero] at this
  exact (norm_nonneg _).not_gt this

/-- A split-negative subspace meets the positive factor `0 × F` only in `0`. -/
theorem IsSplitNegative.disjoint_ker_fst (hW : W.IsSplitNegative) :
    Disjoint W (LinearMap.ker (LinearMap.fst ℝ E F)) := by
  rw [disjoint_def]
  intro w hw hw'
  by_contra hw0
  exact hW.fst_ne_zero hw hw0 hw'

/-- The graph of a linear map `T : E → F` is split-negative exactly when `T` strictly decreases
the norm of every nonzero vector. -/
theorem isSplitNegative_graph_iff (T : E →ₗ[ℝ] F) :
    (LinearMap.graph T).IsSplitNegative ↔ ∀ u, u ≠ 0 → ‖T u‖ < ‖u‖ := by
  refine ⟨fun h u hu ↦ h (u, T u) rfl fun h0 ↦ hu congr(($h0).1), fun h w hw hw0 ↦ ?_⟩
  rw [LinearMap.mem_graph_iff] at hw
  rw [hw]
  refine h _ fun h1 ↦ hw0 (Prod.ext h1 ?_)
  rw [hw, h1, map_zero, Prod.snd_zero]

/-- A split-negative subspace projects injectively to the negative factor. No
finite-dimensionality is needed for this implication. -/
theorem IsSplitNegative.injective_fst (hW : W.IsSplitNegative) :
    Injective ((LinearMap.fst ℝ E F).comp W.subtype) :=
  W.subtypeL.injective_fst_comp_of_norm_snd_lt fun z hz ↦
    hW z z.property (by simpa using hz)

end Submodule

namespace ContinuousLinearMap

/-- A graph is strictly negative for `-‖u‖² + ‖v‖²` exactly when its operator has norm
strictly less than one. Finite-dimensionality is essential for the reverse implication. -/
theorem opNorm_lt_one_iff_isSplitNegative_graph [FiniteDimensional ℝ E] (A : E →L[ℝ] F) :
    ‖A‖ < 1 ↔ A.toLinearMap.graph.IsSplitNegative := by
  rw [A.opNorm_lt_iff zero_lt_one, Submodule.isSplitNegative_graph_iff]
  simp only [ContinuousLinearMap.coe_coe, one_mul]

/-- The range of a frame whose nonzero values lie strictly inside the negative cone is
split-negative. -/
theorem isSplitNegative_range_of_norm_snd_lt {V : Type*} [TopologicalSpace V] [AddCommGroup V]
    [Module ℝ V] (L : V →L[ℝ] E × F) (hL : ∀ u, u ≠ 0 → ‖(L u).2‖ < ‖(L u).1‖) :
    (LinearMap.range (L : V →ₗ[ℝ] E × F)).IsSplitNegative := by
  rintro _ ⟨u, rfl⟩ hu
  exact hL u fun h ↦ hu (by simp [h])

end ContinuousLinearMap

namespace Submodule

variable [FiniteDimensional ℝ E] {W V : Submodule ℝ (E × F)}

/-- Every split-negative subspace is finite dimensional, even if the positive factor is
infinite dimensional. -/
theorem IsSplitNegative.finiteDimensional (hW : W.IsSplitNegative) : FiniteDimensional ℝ W :=
  FiniteDimensional.of_injective _ hW.injective_fst

/-- The dimension of a split-negative subspace is at most that of the negative factor. -/
theorem IsSplitNegative.finrank_le (hW : W.IsSplitNegative) :
    Module.finrank ℝ W ≤ Module.finrank ℝ E :=
  LinearMap.finrank_le_finrank_of_injective hW.injective_fst

/-- A split-negative subspace of full negative dimension is the graph of a strict contraction. -/
theorem IsSplitNegative.exists_eq_graph_of_finrank_eq (hW : W.IsSplitNegative)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph := by
  have := hW.finiteDimensional
  have hinj := hW.injective_fst
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨A, hA⟩ := W.exists_eq_graph ⟨hinj, hsurj⟩
  refine ⟨A.toContinuousLinearMap, ?_, hA⟩
  exact A.toContinuousLinearMap.opNorm_lt_one_iff_isSplitNegative_graph.mpr (hA ▸ hW)

/-- The full-dimensional split-negative subspaces are exactly the graphs of unique operators in
the open operator-norm unit ball. This is the global graph-coordinate classification. -/
theorem existsUnique_eq_graph_iff_finrank_eq_and_isSplitNegative (W : Submodule ℝ (E × F)) :
    (∃! A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph) ↔
      Module.finrank ℝ W = Module.finrank ℝ E ∧ W.IsSplitNegative := by
  constructor
  · rintro ⟨A, ⟨hA, rfl⟩, -⟩
    exact ⟨LinearMap.finrank_graph _, A.opNorm_lt_one_iff_isSplitNegative_graph.mp hA⟩
  · rintro ⟨hdim, hW⟩
    obtain ⟨A, hA, hgraph⟩ := hW.exists_eq_graph_of_finrank_eq hdim
    refine ⟨A, ⟨hA, hgraph⟩, fun B hB ↦ ?_⟩
    ext u
    have hu : (u, B u) ∈ A.toLinearMap.graph := by
      rw [← hgraph, hB.2]
      simp
    exact (LinearMap.mem_graph_iff _ _).mp hu

/-- A full-dimensional subspace of a split-negative subspace is all of it: a full-dimensional
split-negative subspace cannot be enlarged while remaining split-negative. -/
theorem IsSplitNegative.eq_of_le_of_finrank_eq (hV : V.IsSplitNegative) (hWV : W ≤ V)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) : W = V := by
  have := hV.finiteDimensional
  apply Submodule.eq_of_le_of_finrank_le hWV
  rw [hdim]
  exact hV.finrank_le

end Submodule
