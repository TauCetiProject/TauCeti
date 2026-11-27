/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height.Basic
public import TauCeti.Combinatorics.Tiling.Lozenge.Flip

/-!
# The lattice of height functions and flips of heights

The pointwise minimum and maximum of two height functions on a region `R` are height functions on
`R`: along an edge of `R` both functions rise by `0` or `1`, hence so do their minimum and maximum.

A flip at a vertex `v` changes the height function at `v` alone, by one. If the six faces round
`v` lie in `R`, the free tiling of a height function `H` on `R` contains the three edges
`(v,3)`, `(v−e₁,1)`, `(v−e₂,2)` (`highFlipEdges v`) exactly when
`H(v + e_k) = H(v) = H(v − e_k) + 1` for `k = 1, 2, 3`, and then lowering `H(v)` by one gives a
height function on `R` whose free tiling is obtained by exchanging those edges for `(v,1)`, `(v,2)`,
`(v−e₃,3)` (`lowFlipEdges v`). The reverse exchange raises `H(v)` by one. On a connected region
containing the six faces round `v`, the height functions of two tilings related by a flip at `v`,
normalised at a common vertex of `R` other than `v`, therefore differ on the vertices of `R` only at
`v`, by one.

## Main statements

* `TauCeti.IsHeightFunctionOn.inf`, `TauCeti.IsHeightFunctionOn.sup`: height functions on `R` are
  closed under pointwise minimum and maximum.
* `TauCeti.IsHeightFunctionOn.highFlipEdges_subset_tilingOfHeightOn_iff`,
  `TauCeti.IsHeightFunctionOn.lowFlipEdges_subset_tilingOfHeightOn_iff`: the values of `H` round a
  vertex at which its free tiling can be flipped.
* `TauCeti.IsHeightFunctionOn.update_sub_one`, `TauCeti.IsHeightFunctionOn.update_add_one`: a flip
  at `v` lowers, respectively raises, the height function at `v` by one and leaves it unchanged
  elsewhere.
* `TauCeti.IsFlipAt.exists_isHeightFunctionOn_update`: for a flip `M → M'` at `v` of the free
  tiling `M` of a height function `H` on `R`, changing `H(v)` by `±1` gives a height function on
  `R` with free tiling `M'`.
* `TauCeti.IsFlipAt.exists_eqOn_update_of_isConnectedRegion`: on a connected region `R` containing
  the six faces round `v`, height functions of `M` and `M'` that agree at a vertex of `R` other than
  `v` differ on the vertices of `R` only at `v`, by one.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 2 (flips, Theorem 2.1, and footnote 1 for the pointwise extremum of heights, stated
  there for `x + y − 3H`, whose maximum is the minimum here).
-/

public section

namespace TauCeti

variable {R : Set TriFace} {M M' : Set TriEdge} {H H' : ℤ × ℤ → ℤ} {v : ℤ × ℤ}

/-! ### Minimum and maximum -/

namespace IsHeightFunctionOn

/-- **Minimum of heights.** The pointwise minimum of two height functions on `R` is a height
function on `R`. -/
theorem inf (hH : IsHeightFunctionOn R H) (hH' : IsHeightFunctionOn R H') :
    IsHeightFunctionOn R (H ⊓ H') := isHeightFunctionOn_def.2 fun e he => by
  have h₁ := isHeightFunctionOn_def.1 hH e he
  have h₂ := isHeightFunctionOn_def.1 hH' e he
  simp only [Pi.inf_apply]
  omega

/-- **Maximum of heights.** The pointwise maximum of two height functions on `R` is a height
function on `R`. -/
theorem sup (hH : IsHeightFunctionOn R H) (hH' : IsHeightFunctionOn R H') :
    IsHeightFunctionOn R (H ⊔ H') := isHeightFunctionOn_def.2 fun e he => by
  have h₁ := isHeightFunctionOn_def.1 hH e he
  have h₂ := isHeightFunctionOn_def.1 hH' e he
  simp only [Pi.sup_apply]
  omega

end IsHeightFunctionOn

namespace IsHeightFunctionOn

/-- Changing a height function `H` on `R` at `v` alone: if `A` and `B` consist of edges at `v`, and
along each edge at `v` the new function has increment `0` or `1` and lies in its free tiling exactly
when the edge lies in `tilingOfHeightOn R H \ A ∪ B`, then the new function is a height function on
`R` with free tiling `tilingOfHeightOn R H \ A ∪ B`. -/
private theorem update_of_mem_endpoints (hH : IsHeightFunctionOn R H) {c : ℤ}
    {A B : Set TriEdge} (hA : ∀ e ∈ A, v ∈ e.endpoints) (hB : ∀ e ∈ B, v ∈ e.endpoints)
    (hv : ∀ e : TriEdge, v ∈ e.endpoints →
      (e ∈ regionEdges R → Function.update H v c e.target - Function.update H v c e.v = 0 ∨
          Function.update H v c e.target - Function.update H v c e.v = 1) ∧
        (e ∈ tilingOfHeightOn R (Function.update H v c) ↔ e ∈ tilingOfHeightOn R H \ A ∪ B)) :
    IsHeightFunctionOn R (Function.update H v c) ∧
      tilingOfHeightOn R (Function.update H v c) = tilingOfHeightOn R H \ A ∪ B := by
  have key : ∀ e : TriEdge, v ∉ e.endpoints →
      Function.update H v c e.target - Function.update H v c e.v = H e.target - H e.v ∧
        e ∉ A ∧ e ∉ B := fun e he => by
    rw [TriEdge.mem_endpoints, not_or] at he
    exact ⟨by rw [Function.update_of_ne (Ne.symm he.2), Function.update_of_ne (Ne.symm he.1)],
      fun h => he.elim (TriEdge.mem_endpoints.1 (hA e h)).elim,
      fun h => he.elim (TriEdge.mem_endpoints.1 (hB e h)).elim⟩
  refine ⟨isHeightFunctionOn_def.2 fun e he => ?_, Set.ext fun e => ?_⟩ <;>
    by_cases hve : v ∈ e.endpoints
  · exact (hv e hve).1 he
  · rw [(key e hve).1]
    exact isHeightFunctionOn_def.1 hH e he
  · exact (hv e hve).2
  · obtain ⟨h, hA', hB'⟩ := key e hve
    simp only [mem_tilingOfHeightOn, h, Set.mem_union, Set.mem_sdiff, hA', hB',
      not_false_eq_true, and_true, or_false]

variable (hH : IsHeightFunctionOn R H) (hR : (vertexFaces v : Set TriFace) ⊆ R)
include hH hR

/-- Increments of `H` along the edges of the faces round `v`. -/
private theorem incr (e : TriEdge) (f : TriFace) (hf : f ∈ vertexFaces v) (he : e ∈ f.edges) :
    H e.target - H e.v = 0 ∨ H e.target - H e.v = 1 :=
  isHeightFunctionOn_def.1 hH e (edges_subset_regionEdges (hR hf) he)

/-- **The values round a high flip vertex.** If the six faces round `v` lie in `R`, the free tiling
of a height function `H` on `R` contains `highFlipEdges v` exactly when
`H(v + e_k) = H(v) = H(v − e_k) + 1` for `k = 1, 2, 3`. -/
theorem highFlipEdges_subset_tilingOfHeightOn_iff :
    highFlipEdges v ⊆ tilingOfHeightOn R H ↔
      H (v + (1, 0)) = H v ∧ H (v + (0, 1)) = H v ∧ H (v + (1, 1)) = H v ∧
        H (v - (1, 0)) = H v - 1 ∧ H (v - (0, 1)) = H v - 1 ∧ H (v - (1, 1)) = H v - 1 := by
  refine ⟨fun hM => ?_, fun hvals e he => mem_tilingOfHeightOn.2 ⟨?_,
    mem_regionEdges_of_vertexFaces_subset hR (mem_endpoints_of_mem_highFlipEdges he)⟩⟩
  · obtain ⟨x, y⟩ := v
    have m₁ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y), 2⟩ : TriEdge) ∈ _ by simp))).1
    have m₂ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y) - (1, 0), 0⟩ : TriEdge) ∈ _ by simp))).1
    have m₃ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y) - (0, 1), 1⟩ : TriEdge) ∈ _ by simp))).1
    have i₁ := hH.incr hR ⟨(x, y) + (1, 0), 1⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₂ := hH.incr hR ⟨(x, y), 0⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₃ := hH.incr hR ⟨(x, y) + (0, 1), 0⟩ ⟨(x, y), false⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₄ := hH.incr hR ⟨(x, y), 1⟩ ⟨(x, y), false⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₅ := hH.incr hR ⟨(x, y) - (1, 1), 0⟩ ⟨(x, y) - (1, 1), true⟩
      (by simp [vertexFaces_def]) (by simp)
    have i₆ := hH.incr hR ⟨(x, y) - (1, 1), 2⟩ ⟨(x, y) - (1, 1), true⟩
      (by simp [vertexFaces_def]) (by simp)
    simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
      neutralIncrement_def, Prod.mk_add_mk, Prod.mk_sub_mk] at *
    norm_num at *
    omega
  · obtain ⟨x, y⟩ := v
    rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, neutralIncrement_def]

/-- **The values round a low flip vertex.** If the six faces round `v` lie in `R`, the free tiling
of a height function `H` on `R` contains `lowFlipEdges v` exactly when `H(v + e_k) = H(v) + 1` and
`H(v − e_k) = H(v)` for `k = 1, 2, 3`. -/
theorem lowFlipEdges_subset_tilingOfHeightOn_iff :
    lowFlipEdges v ⊆ tilingOfHeightOn R H ↔
      H (v + (1, 0)) = H v + 1 ∧ H (v + (0, 1)) = H v + 1 ∧ H (v + (1, 1)) = H v + 1 ∧
        H (v - (1, 0)) = H v ∧ H (v - (0, 1)) = H v ∧ H (v - (1, 1)) = H v := by
  refine ⟨fun hM => ?_, fun hvals e he => mem_tilingOfHeightOn.2 ⟨?_,
    mem_regionEdges_of_vertexFaces_subset hR (mem_endpoints_of_mem_lowFlipEdges he)⟩⟩
  · obtain ⟨x, y⟩ := v
    have m₁ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y), 0⟩ : TriEdge) ∈ _ by simp))).1
    have m₂ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y), 1⟩ : TriEdge) ∈ _ by simp))).1
    have m₃ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y) - (1, 1), 2⟩ : TriEdge) ∈ _ by simp))).1
    have i₁ := hH.incr hR ⟨(x, y) + (1, 0), 1⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₂ := hH.incr hR ⟨(x, y), 2⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
      (by simp)
    have i₃ := hH.incr hR ⟨(x, y) - (1, 1), 1⟩ ⟨(x, y) - (1, 1), false⟩
      (by simp [vertexFaces_def]) (by simp)
    have i₄ := hH.incr hR ⟨(x, y) - (1, 1) + (0, 1), 0⟩ ⟨(x, y) - (1, 1), false⟩
      (by simp [vertexFaces_def]) (by simp)
    have i₅ := hH.incr hR ⟨(x, y) - (1, 1), 0⟩ ⟨(x, y) - (1, 1), true⟩
      (by simp [vertexFaces_def]) (by simp)
    have i₆ := hH.incr hR ⟨(x, y) - (1, 1) + (1, 0), 1⟩ ⟨(x, y) - (1, 1), true⟩
      (by simp [vertexFaces_def]) (by simp)
    simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
      neutralIncrement_def, Prod.mk_add_mk, Prod.mk_sub_mk] at *
    norm_num at *
    omega
  · obtain ⟨x, y⟩ := v
    rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, neutralIncrement_def]

/-- **A flip lowers the height by one.** If the six faces round `v` lie in `R` and the free tiling
of a height function `H` on `R` contains `highFlipEdges v`, then lowering `H(v)` by one gives a
height function on `R` whose free tiling is obtained by exchanging `highFlipEdges v` for
`lowFlipEdges v`. -/
theorem update_sub_one (hM : highFlipEdges v ⊆ tilingOfHeightOn R H) :
    IsHeightFunctionOn R (Function.update H v (H v - 1)) ∧
      tilingOfHeightOn R (Function.update H v (H v - 1)) =
        tilingOfHeightOn R H \ highFlipEdges v ∪ lowFlipEdges v := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := (hH.highFlipEdges_subset_tilingOfHeightOn_iff hR).1 hM
  refine hH.update_of_mem_endpoints (fun _ => mem_endpoints_of_mem_highFlipEdges)
    (fun _ => mem_endpoints_of_mem_lowFlipEdges) fun e he => ?_
  have hR' := mem_regionEdges_of_vertexFaces_subset hR he
  obtain ⟨x, y⟩ := v
  rcases e with ⟨ev, k⟩
  rcases TriEdge.mem_endpoints.1 he with rfl | ht
  · clear he
    simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
    fin_cases k <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
        neutralIncrement_def]
    omega
  · obtain rfl : ev = (x, y) - latticeDir k := eq_sub_of_add_eq (TriEdge.target_mk ev k ▸ ht.symm)
    clear he ht
    simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
    fin_cases k <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
        neutralIncrement_def]

/-- **A flip raises the height by one.** If the six faces round `v` lie in `R` and the free tiling
of a height function `H` on `R` contains `lowFlipEdges v`, then raising `H(v)` by one gives a
height function on `R` whose free tiling is obtained by exchanging `lowFlipEdges v` for
`highFlipEdges v`. -/
theorem update_add_one (hM : lowFlipEdges v ⊆ tilingOfHeightOn R H) :
    IsHeightFunctionOn R (Function.update H v (H v + 1)) ∧
      tilingOfHeightOn R (Function.update H v (H v + 1)) =
        tilingOfHeightOn R H \ lowFlipEdges v ∪ highFlipEdges v := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := (hH.lowFlipEdges_subset_tilingOfHeightOn_iff hR).1 hM
  refine hH.update_of_mem_endpoints (fun _ => mem_endpoints_of_mem_lowFlipEdges)
    (fun _ => mem_endpoints_of_mem_highFlipEdges) fun e he => ?_
  have hR' := mem_regionEdges_of_vertexFaces_subset hR he
  obtain ⟨x, y⟩ := v
  rcases e with ⟨ev, k⟩
  rcases TriEdge.mem_endpoints.1 he with rfl | ht
  · clear he
    simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
    fin_cases k <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
        neutralIncrement_def]
    all_goals omega
  · obtain rfl : ev = (x, y) - latticeDir k := eq_sub_of_add_eq (TriEdge.target_mk ev k ▸ ht.symm)
    clear he ht
    simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
    fin_cases k <;>
      simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
        neutralIncrement_def]

end IsHeightFunctionOn

namespace IsFlipAt

variable (h : IsFlipAt v M M') (hR : (vertexFaces v : Set TriFace) ⊆ R)
include h hR

/-- **Heights of a flip.** If `M'` is obtained by a flip at `v` from the free tiling `M` of a
height function `H` on `R`, and the six faces round `v` lie in `R`, then changing `H(v)` by `−1`
(when `M` contains `highFlipEdges v`) or by `+1` (when `M` contains `lowFlipEdges v`) gives a
height function on `R` with free tiling `M'`. -/
theorem exists_isHeightFunctionOn_update (hH : IsHeightFunctionOn R H)
    (hM : tilingOfHeightOn R H = M) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsHeightFunctionOn R (Function.update H v (H v + ε)) ∧
      tilingOfHeightOn R (Function.update H v (H v + ε)) = M' := by
  subst hM
  rcases isFlipAt_def.1 h with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [← sub_eq_add_neg] using hH.update_sub_one hR hs
  · exact ⟨1, Or.inl rfl, hH.update_add_one hR hs⟩

/-- **Heights of a flip on a connected region.** If `M'` is obtained from `M` by a flip at `v`,
the six faces round `v` lie in the connected region `R`, and `H`, `H'` are height functions on `R`
with free tilings `M`, `M'` agreeing at a vertex `u₀ ≠ v` of `R`, then on the vertices of `R`,
`H'` differs from `H` only at `v`, by one. -/
theorem exists_eqOn_update_of_isConnectedRegion (hRc : IsConnectedRegion R)
    (hH : IsHeightFunctionOn R H) (hM : tilingOfHeightOn R H = M)
    (hH' : IsHeightFunctionOn R H') (hM' : tilingOfHeightOn R H' = M') {u₀ : ℤ × ℤ}
    (hu₀ : u₀ ∈ regionVertices R) (hne : u₀ ≠ v) (h₀ : H u₀ = H' u₀) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      Set.EqOn H' (Function.update H v (H v + ε)) (regionVertices R) := by
  obtain ⟨ε, hε, hH'', hM''⟩ := h.exists_isHeightFunctionOn_update hR hH hM
  exact ⟨ε, hε, hRc.eqOn_of_tilingOfHeightOn_eq hH' hH'' (hM'.trans hM''.symm) hu₀
    (by rw [Function.update_of_ne hne, h₀])⟩

end IsFlipAt

end TauCeti
