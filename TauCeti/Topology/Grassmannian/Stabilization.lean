/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Map
public import TauCeti.Topology.Grassmannian.Orthonormal
public import TauCeti.Topology.Grassmannian.Plucker
public import TauCeti.LinearAlgebra.Submodule.Fin
public import TauCeti.LinearAlgebra.ExtendByZero
public import TauCeti.Topology.Algebra.Module.ExtendByZero

/-!
# Coordinate stabilization of finite Grassmannians

Ambient stabilization appends a zero last coordinate. Rank stabilization puts a new
coordinate line first: it sends `V` to `𝕜 e₀ ⊕ shift(V)`, with shift sending coordinate
`i` to `i.succ`. The two stabilizations commute strictly, so they can be used as the
two structure maps of a Grassmannian tower without choosing coordinate permutations.

`ambientInclusion` includes `𝕜^N` into the first coordinates of `𝕜^M` for any `N ≤ M`.
These inclusions compose functorially and agree with `ambientStabilization` in one step.

The rank map is continuous for the frame-quotient topology and injective. Its image
consists exactly of the planes containing `e₀`. Each stabilized subspace is identified
linearly with `𝕜 × V`, in that order, by `Submodule.finConsEquiv`. Over the real or
complex numbers both stabilizations and all ambient inclusions are closed embeddings.
All constructions include rank zero and empty Grassmannians.

The continuity proof uses the frame-span quotient from
`TauCeti.Topology.Grassmannian.Basic`; the coordinate splitting is Mathlib's
`Fin.consLinearEquiv`.
-/

public section

open Set

namespace TauCeti

namespace finiteFullRankFrame

variable {𝕜 : Type*} [Field 𝕜] {r N : ℕ}

/-- Prepend `e₀` to a frame and shift each old vector into the remaining coordinates. -/
def rankStabilization (v : finiteFullRankFrame 𝕜 r N) :
    finiteFullRankFrame 𝕜 (r + 1) (N + 1) :=
  ⟨Fin.cons (Pi.single 0 1) (fun i ↦ Fin.cons 0 (v.1 i)), by
    have hli : LinearIndependent 𝕜 (fun i ↦ (Fin.cons 0 (v.1 i) : Fin (N + 1) → 𝕜)) := by
      apply LinearIndependent.of_comp (LinearMap.funLeft 𝕜 𝕜 Fin.succ)
      convert v.2 using 1
      ext i j
      simp
    apply hli.finCons
    have hs : Submodule.span 𝕜 (range fun i ↦ (Fin.cons 0 (v.1 i) : Fin (N + 1) → 𝕜)) ≤
        LinearMap.ker (LinearMap.proj (0 : Fin (N + 1))) := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      simp
    intro h
    have := hs h
    simp at this⟩

@[simp]
theorem coe_rankStabilization (v : finiteFullRankFrame 𝕜 r N) :
    (rankStabilization v).1 = Fin.cons (Pi.single 0 1) (fun i ↦ Fin.cons 0 (v.1 i)) := (rfl)

/-- Stabilizing a full-rank frame is continuous in all its coordinates. -/
@[fun_prop]
theorem continuous_rankStabilization [TopologicalSpace 𝕜] :
    Continuous (rankStabilization : finiteFullRankFrame 𝕜 r N → _) := by
  refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
  refine Fin.cases continuous_const (fun i ↦ continuous_pi fun j ↦ ?_) i
  exact Fin.cases continuous_const (fun j ↦
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)) j

end finiteFullRankFrame

namespace finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] {r N : ℕ}

/-- Prepend the first coordinate line to a plane, shifting all its old coordinates
by `Fin.succ`. The rank increases by one. -/
def rankStabilization (V : finiteGrassmannian 𝕜 r N) :
    finiteGrassmannian 𝕜 (r + 1) (N + 1) :=
  ⟨V.1.comap (LinearMap.funLeft 𝕜 𝕜 Fin.succ), by
    rw [← V.1.finConsEquiv.finrank_eq, Module.finrank_prod, Module.finrank_self, V.2]
    omega⟩

/-- Rank stabilization is inverse image under deletion of coordinate zero.
Use `mem_rankStabilization` for membership simplification. -/
theorem coe_rankStabilization (V : finiteGrassmannian 𝕜 r N) :
    (rankStabilization V).1 = V.1.comap (LinearMap.funLeft 𝕜 𝕜 Fin.succ) := (rfl)

/-- Membership in the stabilized plane is detected by deleting coordinate zero. -/
@[simp]
theorem mem_rankStabilization (V : finiteGrassmannian 𝕜 r N) (v : Fin (N + 1) → 𝕜) :
    v ∈ (rankStabilization V).1 ↔ Fin.tail v ∈ V.1 := Iff.rfl

/-- The new coordinate line belongs to every rank-stabilized plane. -/
theorem single_zero_mem_rankStabilization (V : finiteGrassmannian 𝕜 r N) :
    Pi.single (0 : Fin (N + 1)) 1 ∈ (rankStabilization V).1 := by
  rw [mem_rankStabilization]
  convert V.1.zero_mem using 1
  ext i
  simp [Fin.tail]

/-- Rank stabilization does not identify distinct planes. -/
theorem rankStabilization_injective :
    Function.Injective (rankStabilization : finiteGrassmannian 𝕜 r N → _) := by
  intro V W h
  apply Subtype.ext
  apply Submodule.comap_injective_of_surjective
    (LinearMap.funLeft_surjective_of_injective 𝕜 𝕜 Fin.succ (Fin.succ_injective N))
  exact congrArg Subtype.val h

/-- The inclusion `𝕜^N → 𝕜^M`, for `N ≤ M`, onto the first `N` coordinates, on planes. Its
one-step case is `ambientStabilization`. -/
noncomputable def ambientInclusion {M : ℕ} (h : N ≤ M) (V : finiteGrassmannian 𝕜 r N) :
    finiteGrassmannian 𝕜 r M :=
  map (Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE h))
    (Function.extend_injective (Fin.castLE_injective h) 0) V

theorem coe_ambientInclusion {M : ℕ} (h : N ≤ M) (V : finiteGrassmannian 𝕜 r N) :
    (ambientInclusion h V).1 = V.1.map (Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE h)) :=
  coe_map _ _ V

/-- Membership in an ambient inclusion is detected by restricting to the old coordinates and
checking that the remaining coordinates vanish. -/
@[simp]
theorem mem_ambientInclusion {M : ℕ} (h : N ≤ M) (V : finiteGrassmannian 𝕜 r N)
    (v : Fin M → 𝕜) :
    v ∈ (ambientInclusion h V).1 ↔ v ∘ Fin.castLE h ∈ V.1 ∧ ∀ i : Fin M, N ≤ i → v i = 0 := by
  rw [coe_ambientInclusion, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    constructor
    · simpa only [Function.comp_def,
        Function.ExtendByZero.linearMap_apply_of_injective 𝕜 (Fin.castLE_injective h)] using hw
    · intro i hi
      have hnot : i ∉ range (Fin.castLE h) := by simpa [Fin.range_castLE] using hi
      exact Function.ExtendByZero.linearMap_apply_of_notMem_range 𝕜 w hnot
  · rintro ⟨hv, hz⟩
    refine ⟨v ∘ Fin.castLE h, hv, funext fun i ↦ ?_⟩
    by_cases hi : (i : ℕ) < N
    · obtain ⟨j, rfl⟩ : i ∈ range (Fin.castLE h) := by simpa [Fin.range_castLE] using hi
      simp only [Function.ExtendByZero.linearMap_apply_of_injective 𝕜
        (Fin.castLE_injective h), Function.comp_apply]
    · have hnot : i ∉ range (Fin.castLE h) := by simpa [Fin.range_castLE] using hi
      rw [Function.ExtendByZero.linearMap_apply_of_notMem_range 𝕜 _ hnot,
        hz i (Nat.le_of_not_gt hi)]

theorem ambientInclusion_injective {M : ℕ} (h : N ≤ M) :
    Function.Injective (ambientInclusion (𝕜 := 𝕜) (r := r) h) :=
  map_injective _ _

@[simp]
theorem ambientInclusion_refl (V : finiteGrassmannian 𝕜 r N) :
    ambientInclusion le_rfl V = V := by
  apply Subtype.ext
  rw [coe_ambientInclusion, Fin.castLE_rfl, Function.ExtendByZero.linearMap_id, Submodule.map_id]

@[simp]
theorem ambientInclusion_ambientInclusion {M L : ℕ} (h : N ≤ M) (h' : M ≤ L)
    (V : finiteGrassmannian 𝕜 r N) :
    ambientInclusion h' (ambientInclusion h V) = ambientInclusion (h.trans h') V := by
  apply Subtype.ext
  rw [coe_ambientInclusion, coe_ambientInclusion, coe_ambientInclusion, ← Submodule.map_comp,
    ← Function.ExtendByZero.linearMap_comp _ (Fin.castLE_injective h'),
    Fin.castLE_comp_castLE]

/-- Append a zero last coordinate, leaving the rank unchanged: the one-step ambient inclusion. -/
noncomputable def ambientStabilization (V : finiteGrassmannian 𝕜 r N) :
    finiteGrassmannian 𝕜 r (N + 1) :=
  ambientInclusion (Nat.le_succ N) V

/-- The one-step ambient inclusion is ambient stabilization. -/
@[simp]
theorem ambientInclusion_succ (V : finiteGrassmannian 𝕜 r N) :
    ambientInclusion (Nat.le_succ N) V = ambientStabilization V :=
  (rfl)

/-- Ambient stabilization is exactly the image under extension along `Fin.castSucc`.
Use `mem_ambientStabilization` for membership simplification. -/
theorem coe_ambientStabilization (V : finiteGrassmannian 𝕜 r N) :
    (ambientStabilization V).1 =
      V.1.map (Function.ExtendByZero.linearMap 𝕜 𝕜 Fin.castSucc) := by
  have : Fin.castLE (Nat.le_succ N) = Fin.castSucc := funext fun i ↦ Fin.ext (by simp)
  rw [ambientStabilization, coe_ambientInclusion, this]

/-- Appending a zero coordinate does not identify distinct planes. -/
theorem ambientStabilization_injective :
    Function.Injective (ambientStabilization : finiteGrassmannian 𝕜 r N → _) :=
  ambientInclusion_injective _

/-- Membership in an ambient-stabilized plane: the old coordinates belong to the
original plane and the last coordinate vanishes. -/
@[simp]
theorem mem_ambientStabilization (V : finiteGrassmannian 𝕜 r N) (v : Fin (N + 1) → 𝕜) :
    v ∈ (ambientStabilization V).1 ↔ Fin.init v ∈ V.1 ∧ v (Fin.last N) = 0 := by
  rw [coe_ambientStabilization, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(Function.ExtendByZero.init_linearMap_castSucc 𝕜 w).symm ▸ hw,
      Function.ExtendByZero.linearMap_castSucc_last 𝕜 w⟩
  · rintro ⟨hv, hlast⟩
    refine ⟨Fin.init v, hv, funext fun i ↦ ?_⟩
    cases i using Fin.lastCases with
    | last => rw [Function.ExtendByZero.linearMap_castSucc_last 𝕜, hlast]
    | cast i =>
      rw [Function.ExtendByZero.linearMap_apply_of_injective 𝕜 (Fin.castSucc_injective N),
        Fin.init]

/-- Rank and ambient stabilization commute as actual maps, with no intervening
coordinate permutation or homotopy. -/
theorem ambientStabilization_rankStabilization (V : finiteGrassmannian 𝕜 r N) :
    ambientStabilization (rankStabilization V) = rankStabilization (ambientStabilization V) := by
  apply Subtype.ext
  ext v
  simp only [mem_ambientStabilization, mem_rankStabilization]
  rw [Fin.tail_init_eq_init_tail]
  rfl

/-- Taking spans commutes with adjoining the new first frame vector. -/
@[simp]
theorem frameSpan_rankStabilization (v : finiteFullRankFrame 𝕜 r N) :
    frameSpan v.rankStabilization = rankStabilization (frameSpan v) := by
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [coe_frameSpan]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    rw [finiteFullRankFrame.coe_rankStabilization]
    refine Fin.cases (single_zero_mem_rankStabilization _) (fun i ↦ ?_) i
    simp only [Fin.cons_succ]
    apply (mem_rankStabilization (frameSpan v) _).2
    rw [Fin.tail_cons, coe_frameSpan]
    exact Submodule.subset_span (mem_range_self i)
  · exact (frameSpan v.rankStabilization).2.trans (rankStabilization (frameSpan v)).2.symm

/-- Rank stabilization is continuous for the frame-quotient topologies. -/
@[fun_prop]
theorem continuous_rankStabilization [TopologicalSpace 𝕜] :
    Continuous (rankStabilization : finiteGrassmannian 𝕜 r N → _) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  exact (continuous_frameSpan.comp finiteFullRankFrame.continuous_rankStabilization).congr
    fun v ↦ frameSpan_rankStabilization v

/-- Including into a larger coordinate space is continuous for the frame-quotient topologies. -/
@[fun_prop]
theorem continuous_ambientInclusion [TopologicalSpace 𝕜] {M : ℕ} (h : N ≤ M) :
    Continuous (ambientInclusion (𝕜 := 𝕜) (r := r) h) :=
  continuous_map _ _ (Function.ExtendByZero.continuous_linearMap 𝕜 _)

/-- Appending the last coordinate is continuous for the frame-quotient topologies. -/
@[fun_prop]
theorem continuous_ambientStabilization [TopologicalSpace 𝕜] :
    Continuous (ambientStabilization : finiteGrassmannian 𝕜 r N → _) :=
  continuous_ambientInclusion _

/-- A plane is in the image of rank stabilization exactly when it contains the new
first coordinate vector. -/
theorem mem_range_rankStabilization (W : finiteGrassmannian 𝕜 (r + 1) (N + 1)) :
    W ∈ range (rankStabilization : finiteGrassmannian 𝕜 r N → _) ↔
      Pi.single (0 : Fin (N + 1)) 1 ∈ W.1 := by
  constructor
  · rintro ⟨V, rfl⟩
    exact single_zero_mem_rankStabilization V
  · intro hW
    let t := LinearMap.funLeft 𝕜 𝕜 (Fin.succ : Fin N → Fin (N + 1))
    have hker : LinearMap.ker t ≤ W.1 := by
      intro v hv
      have htail : Fin.tail v = 0 :=
        funext fun i ↦ by simpa [t, Fin.tail] using congrFun (LinearMap.mem_ker.1 hv) i
      rw [Function.ExtendByZero.eq_smul_single_zero_add_linearMap_succ_tail v, htail, map_zero,
        add_zero]
      exact W.1.smul_mem _ hW
    have hcomap : (W.1.map t).comap t = W.1 := Submodule.comap_map_eq_self hker
    have hdim := (W.1.map t).finConsEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at hdim
    rw [hcomap, W.2] at hdim
    refine ⟨⟨W.1.map t, by omega⟩, Subtype.ext hcomap⟩

end finiteGrassmannian

namespace finiteGrassmannian

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- Over the real or complex numbers, the rank map is a closed embedding. -/
theorem isClosedEmbedding_rankStabilization :
    Topology.IsClosedEmbedding (rankStabilization : finiteGrassmannian 𝕜 r N → _) :=
  continuous_rankStabilization.isClosedEmbedding rankStabilization_injective

/-- Over the real or complex numbers, the inclusion into a larger coordinate space is a closed
embedding. -/
theorem isClosedEmbedding_ambientInclusion {M : ℕ} (h : N ≤ M) :
    Topology.IsClosedEmbedding (ambientInclusion (𝕜 := 𝕜) (r := r) h) :=
  (continuous_ambientInclusion h).isClosedEmbedding (ambientInclusion_injective h)

/-- Over the real or complex numbers, appending a last coordinate is a closed embedding. -/
theorem isClosedEmbedding_ambientStabilization :
    Topology.IsClosedEmbedding (ambientStabilization : finiteGrassmannian 𝕜 r N → _) :=
  isClosedEmbedding_ambientInclusion _

/-- The locus of planes containing the first coordinate line is closed. -/
theorem isClosed_single_zero_mem :
    IsClosed {W : finiteGrassmannian 𝕜 (r + 1) (N + 1) | Pi.single 0 1 ∈ W.1} := by
  convert (isClosedEmbedding_rankStabilization (𝕜 := 𝕜) (r := r) (N := N)).isClosed_range using 1
  ext W
  exact (mem_range_rankStabilization W).symm

/-- Adjoining the first coordinate line is a homeomorphism onto the closed locus of
planes containing that line. -/
noncomputable def rankStabilizationHomeomorph :
    finiteGrassmannian 𝕜 r N ≃ₜ
      {W : finiteGrassmannian 𝕜 (r + 1) (N + 1) // Pi.single 0 1 ∈ W.1} :=
  (isClosedEmbedding_rankStabilization (𝕜 := 𝕜) (r := r) (N := N)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (s := range (rankStabilization : finiteGrassmannian 𝕜 r N → _))
      (t := {W : finiteGrassmannian 𝕜 (r + 1) (N + 1) | Pi.single 0 1 ∈ W.1})
      (Set.ext fun W ↦ mem_range_rankStabilization W))

@[simp]
theorem coe_rankStabilizationHomeomorph_apply (V : finiteGrassmannian 𝕜 r N) :
    (rankStabilizationHomeomorph V).1 = rankStabilization V := (rfl)

@[simp]
theorem rankStabilizationHomeomorph_symm_apply (V : finiteGrassmannian 𝕜 r N) :
    rankStabilizationHomeomorph.symm
      ⟨rankStabilization V, single_zero_mem_rankStabilization V⟩ = V :=
  rankStabilizationHomeomorph.injective (Subtype.ext (by simp))

end finiteGrassmannian
end TauCeti
