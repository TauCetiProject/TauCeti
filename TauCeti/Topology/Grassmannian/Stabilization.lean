/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Map
public import TauCeti.Topology.Grassmannian.Orthonormal
public import TauCeti.Topology.Grassmannian.Plucker
public import TauCeti.Topology.Algebra.Module.ExtendByZero
public import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Ambient and rank inclusions of finite Grassmannians

The finite Grassmannians `TauCeti.finiteGrassmannian 𝕜 r N` are connected by two coordinate maps,
which form the stabilization diagram whose colimits are the infinite Grassmannians.

* The ambient inclusion `TauCeti.finiteGrassmannian.castSucc : Gr(r, N) → Gr(r, N + 1)` views
  `𝕜^N` as the coordinate hyperplane of `𝕜^(N + 1)` with vanishing last coordinate: a vector `v`
  is sent to `Function.extend Fin.castSucc v 0`.
* The rank inclusion `TauCeti.finiteGrassmannian.rankSucc : Gr(r, N) → Gr(r + 1, N + 1)` is
  `s(V) = 𝕜 e₀ ⊕ shift V`, where `e₀ = Pi.single 0 1` is the new first basis vector and
  `shift : 𝕜^N → 𝕜^(N + 1)` sends `e_i` to `e_(i + 1)`, that is, `v ↦ Function.extend Fin.succ v 0`.
  The new line comes first. Equivalently, `s(V)` consists of the vectors whose tail
  `(w 1, …, w N)` lies in `V` (`TauCeti.finiteGrassmannian.mem_rankSucc_iff`).

Both maps are continuous and injective, and they commute strictly:
`s ∘ castSucc = castSucc ∘ s` as maps `Gr(r, N) → Gr(r + 1, N + 2)`
(`TauCeti.finiteGrassmannian.rankSucc_castSucc`). The image of the rank inclusion is exactly the
set of planes containing `e₀` (`TauCeti.finiteGrassmannian.range_rankSucc`), a closed Schubert
subvariety. Over `ℝ` or `ℂ` the finite Grassmannians are compact Hausdorff, so both maps are closed
embeddings; in particular the rank inclusion is a homeomorphism onto the planes containing `e₀`.

On frames the rank inclusion prepends `e₀` to the shifted frame
(`TauCeti.finiteFullRankFrame.rankSucc`); continuity is checked there, because the Grassmannian
carries the quotient topology of the span map.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, for the infinite Grassmannian as the
  union of the finite Grassmannians along the coordinate inclusions.
-/

public section

open Set Module Function.ExtendByZero

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] {r N : ℕ}

namespace finiteFullRankFrame

/-- The rank inclusion on frames: shift every vector of the frame by `e_i ↦ e_(i + 1)` and
prepend the new first basis vector `e₀`. -/
noncomputable def rankSucc (f : finiteFullRankFrame 𝕜 r N) :
    finiteFullRankFrame 𝕜 (r + 1) (N + 1) :=
  ⟨Fin.cons (Pi.single 0 1)
      (map (linearMap 𝕜 𝕜 Fin.succ) (linearMap_injective (Fin.succ_injective N)) f).1, by
    refine (map _ _ f).2.finCons fun h ↦
      single_zero_notMem_range_linearMap_succ (Submodule.span_le.2 ?_ h)
    rw [coe_map]
    rintro _ ⟨i, rfl⟩
    exact ⟨f.1 i, rfl⟩⟩

@[simp]
theorem coe_rankSucc (f : finiteFullRankFrame 𝕜 r N) :
    (rankSucc f).1 = Fin.cons (Pi.single 0 1)
      (map (linearMap 𝕜 𝕜 Fin.succ) (linearMap_injective (Fin.succ_injective N)) f).1 :=
  (rfl)

/-- The rank inclusion on frames is continuous. -/
@[fun_prop]
theorem continuous_rankSucc [TopologicalSpace 𝕜] :
    Continuous (rankSucc : finiteFullRankFrame 𝕜 r N → _) :=
  (continuous_const.finCons (continuous_subtype_val.comp
    (continuous_map _ _ (continuous_linearMap 𝕜 Fin.succ)))).subtype_mk _

end finiteFullRankFrame

namespace finiteGrassmannian

/-- The **ambient inclusion** `Gr(r, N) → Gr(r, N + 1)`: a plane in `𝕜^N` viewed as a plane in the
coordinate hyperplane of `𝕜^(N + 1)` with vanishing last coordinate, along `Fin.castSucc`. -/
noncomputable def castSucc (V : finiteGrassmannian 𝕜 r N) : finiteGrassmannian 𝕜 r (N + 1) :=
  map (linearMap 𝕜 𝕜 Fin.castSucc)
    (linearMap_injective (Fin.castSucc_injective N)) V

theorem coe_castSucc (V : finiteGrassmannian 𝕜 r N) :
    (castSucc V).1 = V.1.map (linearMap 𝕜 𝕜 Fin.castSucc) :=
  coe_map _ _ V

/-- A vector lies in the ambient inclusion of `V` exactly when its last coordinate vanishes and
its first `N` coordinates form a vector of `V`. -/
@[simp]
theorem mem_castSucc_iff {V : finiteGrassmannian 𝕜 r N} {w : Fin (N + 1) → 𝕜} :
    w ∈ (castSucc V).1 ↔ w (Fin.last N) = 0 ∧ Fin.init w ∈ V.1 := by
  rw [coe_castSucc, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨linearMap_castSucc_last v, (init_linearMap_castSucc v).symm ▸ hv⟩
  · rintro ⟨hw, hV⟩
    refine ⟨Fin.init w, hV, funext fun i ↦ ?_⟩
    cases i using Fin.lastCases with
    | last => rw [linearMap_castSucc_last, hw]
    | cast i => simp [Fin.init, (Fin.castSucc_injective N).extend_apply]

/-- The ambient inclusion is injective. -/
theorem castSucc_injective : Function.Injective (castSucc : finiteGrassmannian 𝕜 r N → _) :=
  map_injective _ _

/-- The ambient inclusion is continuous. -/
@[fun_prop]
theorem continuous_castSucc [TopologicalSpace 𝕜] :
    Continuous (castSucc : finiteGrassmannian 𝕜 r N → _) :=
  continuous_map _ _ (continuous_linearMap 𝕜 Fin.castSucc)

/-- The **rank inclusion** `s : Gr(r, N) → Gr(r + 1, N + 1)`, `s(V) = 𝕜 e₀ ⊕ shift V`, where
`e₀ = Pi.single 0 1` and `shift` sends `e_i` to `e_(i + 1)` along `Fin.succ`. The new line comes
first. -/
noncomputable def rankSucc (V : finiteGrassmannian 𝕜 r N) : finiteGrassmannian 𝕜 (r + 1) (N + 1) :=
  ⟨(𝕜 ∙ Pi.single 0 1) ⊔ V.1.map (linearMap 𝕜 𝕜 Fin.succ), by
    rw [finrank_span_single_zero_sup_map_linearMap_succ, V.2]⟩

theorem coe_rankSucc (V : finiteGrassmannian 𝕜 r N) :
    (rankSucc V).1 = (𝕜 ∙ Pi.single 0 1) ⊔ V.1.map (linearMap 𝕜 𝕜 Fin.succ) :=
  (rfl)

/-- A vector lies in the rank inclusion of `V` exactly when its tail `(w 1, …, w N)` lies in `V`;
its first coordinate is unconstrained. -/
@[simp]
theorem mem_rankSucc_iff {V : finiteGrassmannian 𝕜 r N} {w : Fin (N + 1) → 𝕜} :
    w ∈ (rankSucc V).1 ↔ Fin.tail w ∈ V.1 :=
  mem_span_single_zero_sup_map_linearMap_succ_iff V.1 w

/-- Taking spans commutes with the rank inclusion of frames. -/
@[simp]
theorem frameSpan_rankSucc (f : finiteFullRankFrame 𝕜 r N) :
    frameSpan f.rankSucc = rankSucc (frameSpan f) := by
  have h := congrArg Subtype.val
    (frameSpan_map (linearMap 𝕜 𝕜 Fin.succ) (linearMap_injective (Fin.succ_injective N)) f)
  simp only [coe_frameSpan, coe_map] at h
  apply Subtype.ext
  simp only [coe_frameSpan, finiteFullRankFrame.coe_rankSucc, coe_rankSucc, Fin.range_cons,
    Submodule.span_insert, h]

/-- The rank inclusion is injective. -/
theorem rankSucc_injective : Function.Injective (rankSucc : finiteGrassmannian 𝕜 r N → _) :=
  fun V W h ↦ Subtype.ext <| Submodule.ext fun v ↦ by
    simpa using SetLike.ext_iff.1 (congrArg Subtype.val h) (Fin.cons 0 v)

/-- The rank inclusion is continuous. -/
@[fun_prop]
theorem continuous_rankSucc [TopologicalSpace 𝕜] :
    Continuous (rankSucc : finiteGrassmannian 𝕜 r N → _) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  exact (continuous_frameSpan.comp finiteFullRankFrame.continuous_rankSucc).congr
    fun f ↦ frameSpan_rankSucc f

/-- **Strict commutation of the rank and ambient inclusions**: `s ∘ castSucc = castSucc ∘ s` as
maps `Gr(r, N) → Gr(r + 1, N + 2)`. -/
theorem rankSucc_castSucc (V : finiteGrassmannian 𝕜 r N) :
    rankSucc (castSucc V) = castSucc (rankSucc V) :=
  Subtype.ext <| Submodule.ext fun w ↦ by
    simp only [mem_rankSucc_iff, mem_castSucc_iff, Fin.tail_init_eq_init_tail]
    rw [Fin.tail, Fin.succ_last]

/-- The image of the rank inclusion consists exactly of the planes containing the first basis
vector `e₀`. -/
theorem range_rankSucc :
    range (rankSucc : finiteGrassmannian 𝕜 r N → _) = {W | Pi.single 0 1 ∈ W.1} := by
  ext W
  constructor
  · rintro ⟨V, rfl⟩
    refine mem_rankSucc_iff.2 ?_
    convert V.1.zero_mem
    funext i
    simp [Fin.tail, Fin.succ_ne_zero]
  · intro hW
    -- The candidate preimage is the image of `W` under taking tails.
    let X := W.1.map (LinearMap.funLeft 𝕜 𝕜 Fin.succ)
    have hmem (w : Fin (N + 1) → 𝕜) :
        w ∈ (𝕜 ∙ Pi.single 0 1) ⊔ X.map (linearMap 𝕜 𝕜 Fin.succ) ↔
          w ∈ W.1 := by
      rw [mem_span_single_zero_sup_map_linearMap_succ_iff]
      refine ⟨fun ⟨w', hw', h⟩ ↦ ?_, fun hw ↦ ⟨w, hw, rfl⟩⟩
      -- `w` and `w'` have the same tail, so they differ by a multiple of `e₀`.
      have h' : Fin.tail w' = Fin.tail w := h
      rw [eq_smul_single_zero_add_linearMap_succ_tail w, ← h',
        eq_sub_of_add_eq' (eq_smul_single_zero_add_linearMap_succ_tail w').symm]
      exact W.1.add_mem (W.1.smul_mem _ hW) (W.1.sub_mem hw' (W.1.smul_mem _ hW))
    have hX : finrank 𝕜 X = r := by
      have h := finrank_span_single_zero_sup_map_linearMap_succ X
      rw [SetLike.ext hmem, W.2] at h
      omega
    exact ⟨⟨X, hX⟩, Subtype.ext (SetLike.ext hmem)⟩

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Over `ℝ` or `ℂ` the ambient inclusion is a closed embedding, since finite Grassmannians are
compact Hausdorff. -/
theorem isClosedEmbedding_castSucc :
    Topology.IsClosedEmbedding (castSucc : finiteGrassmannian 𝕜 r N → _) :=
  continuous_castSucc.isClosedEmbedding castSucc_injective

/-- Over `ℝ` or `ℂ` the rank inclusion is a closed embedding, hence a homeomorphism onto the
planes containing `e₀` (`TauCeti.finiteGrassmannian.range_rankSucc`). -/
theorem isClosedEmbedding_rankSucc :
    Topology.IsClosedEmbedding (rankSucc : finiteGrassmannian 𝕜 r N → _) :=
  continuous_rankSucc.isClosedEmbedding rankSucc_injective

end RCLike

end finiteGrassmannian

end TauCeti
