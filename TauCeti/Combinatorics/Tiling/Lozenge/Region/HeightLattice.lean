/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height
public import TauCeti.Combinatorics.Tiling.Lozenge.Flip

/-!
# The lattice of height functions and flips of heights

The pointwise minimum and maximum of two height functions on a region `R` are height functions on
`R`: along an edge of `R` both functions rise by `0` or `1`, hence so do their minimum and maximum.

A flip at a vertex `v` changes the height function at `v` alone, by one. If the six faces round
`v` lie in `R` and the free tiling of a height function `H` on `R` contains the three edges
`(v,3)`, `(v−e₁,1)`, `(v−e₂,2)` (`highFlipEdges v`), then `H(v + e_k) = H(v) = H(v − e_k) + 1` for
`k = 1, 2, 3`, and lowering `H(v)` by one gives a height function on `R` whose free tiling is
obtained by exchanging those edges for `(v,1)`, `(v,2)`, `(v−e₃,3)` (`lowFlipEdges v`). The
reverse exchange raises `H(v)` by one. On a connected region, the height functions of two tilings
related by a flip at `v`, normalised at a common vertex other than `v`, therefore differ only at
`v`, by one.

## Main statements

* `TauCeti.IsHeightFunctionOn.inf`, `TauCeti.IsHeightFunctionOn.sup`: height functions on `R` are
  closed under pointwise minimum and maximum.
* `TauCeti.IsHeightFunctionOn.flipDown`, `TauCeti.IsHeightFunctionOn.flipUp`: a flip at `v`
  lowers, respectively raises, the height function at `v` by one and leaves it unchanged elsewhere.
* `TauCeti.IsFlipAt.exists_isHeightFunctionOn_update`: for a flip `M → M'` at `v` of the free
  tiling `M` of a height function `H` on `R`, changing `H(v)` by `±1` gives a height function on
  `R` with free tiling `M'`.
* `TauCeti.IsFlipAt.eqOn_update_of_isConnectedRegion`: on a connected region, height functions of
  `M` and `M'` that agree at a vertex other than `v` differ only at `v`, by one.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
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

/-! ### The edges at a vertex -/

/-- Every edge with `e.v = v` is one of the three edges `(v, k)`. -/
private theorem eq_mk_of_v_eq {e : TriEdge} (h : e.v = v) : e = ⟨v, e.k⟩ := by
  cases e
  simp_all

/-- Every edge with target `v` is one of the three edges `(v − e_k, k)`. -/
private theorem eq_mk_of_target_eq {e : TriEdge} (h : e.target = v) :
    e = ⟨v - latticeDir e.k, e.k⟩ := by
  cases e
  simp only [TriEdge.target_mk] at h
  subst h
  simp

/-- The six edges at `v` are edges of `R` when the six faces round `v` lie in `R`. -/
private theorem mem_regionEdges_of_vertexFaces_subset (hR : (vertexFaces v : Set TriFace) ⊆ R)
    {e : TriEdge} (he : e.v = v ∨ e.target = v) : e ∈ regionEdges R := by
  rw [mem_regionEdges_iff]
  left
  apply hR
  obtain ⟨x, y⟩ := v
  rcases he with he | he
  · rw [eq_mk_of_v_eq he]
    rcases e with ⟨-, k⟩
    fin_cases k <;> simp [vertexFaces_def]
  · rw [eq_mk_of_target_eq he]
    rcases e with ⟨-, k⟩
    fin_cases k <;> simp [vertexFaces_def, latticeDir_zero, latticeDir_one, latticeDir_two]

namespace IsHeightFunctionOn

variable (hH : IsHeightFunctionOn R H) (hR : (vertexFaces v : Set TriFace) ⊆ R)
include hH hR

/-- Increments of `H` along the edges of the faces round `v`. -/
private theorem incr (e : TriEdge) (f : TriFace) (hf : f ∈ vertexFaces v) (he : e ∈ f.edges) :
    H e.target - H e.v = 0 ∨ H e.target - H e.v = 1 :=
  isHeightFunctionOn_def.1 hH e (edges_subset_regionEdges (hR hf) he)

/-- **The values round a high flip vertex.** If the free tiling of a height function on `R`
contains `highFlipEdges v` and the six faces round `v` lie in `R`, then
`H(v + e_k) = H(v) = H(v − e_k) + 1` for `k = 1, 2, 3`. -/
theorem eq_of_highFlipEdges_subset (hM : highFlipEdges v ⊆ tilingOfHeightOn R H) :
    H (v + (1, 0)) = H v ∧ H (v + (0, 1)) = H v ∧ H (v + (1, 1)) = H v ∧
      H (v - (1, 0)) = H v - 1 ∧ H (v - (0, 1)) = H v - 1 ∧ H (v - (1, 1)) = H v - 1 := by
  obtain ⟨x, y⟩ := v
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
  have i₅ := hH.incr hR ⟨(x, y) - (1, 1), 0⟩ ⟨(x, y) - (1, 1), true⟩ (by simp [vertexFaces_def])
    (by simp)
  have i₆ := hH.incr hR ⟨(x, y) - (1, 1), 2⟩ ⟨(x, y) - (1, 1), true⟩ (by simp [vertexFaces_def])
    (by simp)
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    neutralIncrement_def, Prod.mk_add_mk, Prod.mk_sub_mk] at *
  norm_num at *
  omega

/-- **The values round a low flip vertex.** If the free tiling of a height function on `R`
contains `lowFlipEdges v` and the six faces round `v` lie in `R`, then
`H(v + e_k) = H(v) + 1` and `H(v − e_k) = H(v)` for `k = 1, 2, 3`. -/
theorem eq_of_lowFlipEdges_subset (hM : lowFlipEdges v ⊆ tilingOfHeightOn R H) :
    H (v + (1, 0)) = H v + 1 ∧ H (v + (0, 1)) = H v + 1 ∧ H (v + (1, 1)) = H v + 1 ∧
      H (v - (1, 0)) = H v ∧ H (v - (0, 1)) = H v ∧ H (v - (1, 1)) = H v := by
  obtain ⟨x, y⟩ := v
  have m₁ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y), 0⟩ : TriEdge) ∈ _ by simp))).1
  have m₂ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y), 1⟩ : TriEdge) ∈ _ by simp))).1
  have m₃ := (mem_tilingOfHeightOn.1 (hM (show (⟨(x, y) - (1, 1), 2⟩ : TriEdge) ∈ _ by simp))).1
  have i₁ := hH.incr hR ⟨(x, y) + (1, 0), 1⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
    (by simp)
  have i₂ := hH.incr hR ⟨(x, y), 2⟩ ⟨(x, y), true⟩ (by simp [vertexFaces_def])
    (by simp)
  have i₃ := hH.incr hR ⟨(x, y) - (1, 1), 1⟩ ⟨(x, y) - (1, 1), false⟩ (by simp [vertexFaces_def])
    (by simp)
  have i₄ := hH.incr hR ⟨(x, y) - (1, 1) + (0, 1), 0⟩ ⟨(x, y) - (1, 1), false⟩
    (by simp [vertexFaces_def]) (by simp)
  have i₅ := hH.incr hR ⟨(x, y) - (1, 1), 0⟩ ⟨(x, y) - (1, 1), true⟩ (by simp [vertexFaces_def])
    (by simp)
  have i₆ := hH.incr hR ⟨(x, y) - (1, 1) + (1, 0), 1⟩ ⟨(x, y) - (1, 1), true⟩
    (by simp [vertexFaces_def]) (by simp)
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    neutralIncrement_def, Prod.mk_add_mk, Prod.mk_sub_mk] at *
  norm_num at *
  omega

/-- **A flip lowers the height by one.** If the six faces round `v` lie in `R` and the free tiling
of a height function `H` on `R` contains `highFlipEdges v`, then lowering `H(v)` by one gives a
height function on `R` whose free tiling is obtained by exchanging `highFlipEdges v` for
`lowFlipEdges v`. -/
theorem flipDown (hM : highFlipEdges v ⊆ tilingOfHeightOn R H) :
    IsHeightFunctionOn R (Function.update H v (H v - 1)) ∧
      tilingOfHeightOn R (Function.update H v (H v - 1)) =
        tilingOfHeightOn R H \ highFlipEdges v ∪ lowFlipEdges v := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hH.eq_of_highFlipEdges_subset hR hM
  have key : ∀ e : TriEdge,
      (e ∈ regionEdges R → (Function.update H v (H v - 1) e.target -
          Function.update H v (H v - 1) e.v = 0 ∨ Function.update H v (H v - 1) e.target -
          Function.update H v (H v - 1) e.v = 1)) ∧
        (e ∈ tilingOfHeightOn R (Function.update H v (H v - 1)) ↔
          e ∈ tilingOfHeightOn R H \ highFlipEdges v ∪ lowFlipEdges v) := by
    intro e
    by_cases hv : e.v = v
    · have hR' := mem_regionEdges_of_vertexFaces_subset hR (Or.inl hv)
      obtain ⟨x, y⟩ := v
      rcases e with ⟨ev, k⟩
      simp only at hv
      subst hv
      simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
      fin_cases k <;>
        simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
          neutralIncrement_def]
      omega
    by_cases ht : e.target = v
    · have hR' := mem_regionEdges_of_vertexFaces_subset hR (Or.inr ht)
      obtain ⟨x, y⟩ := v
      rcases e with ⟨ev, k⟩
      simp only [TriEdge.target_mk] at ht
      obtain rfl : ev = (x, y) - latticeDir k := eq_sub_of_add_eq ht
      simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
      fin_cases k <;>
        simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
          neutralIncrement_def]
    · have hhi : e ∉ highFlipEdges v := fun he => by
        rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
          simp_all [latticeDir_zero, latticeDir_one]
      have hlo : e ∉ lowFlipEdges v := fun he => by
        rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;>
          simp_all [latticeDir_two]
      simp only [mem_tilingOfHeightOn, Function.update_of_ne ht, Function.update_of_ne hv,
        Set.mem_union, Set.mem_sdiff, hhi, hlo, not_false_eq_true, and_true, or_false]
      exact isHeightFunctionOn_def.1 hH e
  exact ⟨isHeightFunctionOn_def.2 fun e he => (key e).1 he, Set.ext fun e => (key e).2⟩

/-- **A flip raises the height by one.** If the six faces round `v` lie in `R` and the free tiling
of a height function `H` on `R` contains `lowFlipEdges v`, then raising `H(v)` by one gives a
height function on `R` whose free tiling is obtained by exchanging `lowFlipEdges v` for
`highFlipEdges v`. -/
theorem flipUp (hM : lowFlipEdges v ⊆ tilingOfHeightOn R H) :
    IsHeightFunctionOn R (Function.update H v (H v + 1)) ∧
      tilingOfHeightOn R (Function.update H v (H v + 1)) =
        tilingOfHeightOn R H \ lowFlipEdges v ∪ highFlipEdges v := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hH.eq_of_lowFlipEdges_subset hR hM
  have key : ∀ e : TriEdge,
      (e ∈ regionEdges R → (Function.update H v (H v + 1) e.target -
          Function.update H v (H v + 1) e.v = 0 ∨ Function.update H v (H v + 1) e.target -
          Function.update H v (H v + 1) e.v = 1)) ∧
        (e ∈ tilingOfHeightOn R (Function.update H v (H v + 1)) ↔
          e ∈ tilingOfHeightOn R H \ lowFlipEdges v ∪ highFlipEdges v) := by
    intro e
    by_cases hv : e.v = v
    · have hR' := mem_regionEdges_of_vertexFaces_subset hR (Or.inl hv)
      obtain ⟨x, y⟩ := v
      rcases e with ⟨ev, k⟩
      simp only at hv
      subst hv
      simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
      fin_cases k <;>
        simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
          neutralIncrement_def]
      all_goals omega
    by_cases ht : e.target = v
    · have hR' := mem_regionEdges_of_vertexFaces_subset hR (Or.inr ht)
      obtain ⟨x, y⟩ := v
      rcases e with ⟨ev, k⟩
      simp only [TriEdge.target_mk] at ht
      obtain rfl : ev = (x, y) - latticeDir k := eq_sub_of_add_eq ht
      simp only [Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero] at h₁ h₂ h₃ h₄ h₅ h₆
      fin_cases k <;>
        simp_all [latticeDir_zero, latticeDir_one, latticeDir_two, Prod.ext_iff,
          neutralIncrement_def]
    · have hhi : e ∉ highFlipEdges v := fun he => by
        rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
          simp_all [latticeDir_zero, latticeDir_one]
      have hlo : e ∉ lowFlipEdges v := fun he => by
        rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;>
          simp_all [latticeDir_two]
      simp only [mem_tilingOfHeightOn, Function.update_of_ne ht, Function.update_of_ne hv,
        Set.mem_union, Set.mem_sdiff, hhi, hlo, not_false_eq_true, and_true, or_false]
      exact isHeightFunctionOn_def.1 hH e
  exact ⟨isHeightFunctionOn_def.2 fun e he => (key e).1 he, Set.ext fun e => (key e).2⟩

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
    simpa only [← sub_eq_add_neg] using hH.flipDown hR hs
  · exact ⟨1, Or.inl rfl, hH.flipUp hR hs⟩

/-- **Heights of a flip on a connected region.** If `M'` is obtained from `M` by a flip at `v`,
the six faces round `v` lie in the connected region `R`, and `H`, `H'` are height functions on `R`
with free tilings `M`, `M'` agreeing at a vertex `u₀ ≠ v` of `R`, then on the vertices of `R`,
`H'` differs from `H` only at `v`, by one. -/
theorem eqOn_update_of_isConnectedRegion (hRc : IsConnectedRegion R)
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
