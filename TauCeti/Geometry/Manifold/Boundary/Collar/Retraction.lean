/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global

/-!
# The image of a collar deformation retracts onto its zero slice

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`). Its image is an open
neighbourhood of the image of `f`, and it deformation retracts onto it: the homotopy
`c (x, t) ↦ c (x, s t)`, `s ∈ [0, 1]`, runs from the projection `c (x, t) ↦ f x` to the identity.
So `f`, read as a map into the image of the collar, is a homotopy equivalence
(`TauCeti.IsCollar.homotopyEquivRange`), with homotopy inverse `c (x, t) ↦ x`.

This is how an open collar neighbourhood replaces the boundary of a manifold in homology: for
`N ⊆ M`, the inclusion of pairs `(M, N) → (M, c (N × [0, 1)))` induces isomorphisms on relative
homology, by the five lemma.

## Main definitions

* `TauCeti.IsCollar.homotopyEquivRange`: the zero slice of a collar is a homotopy equivalence onto
  the image of the collar.
-/

public section

open Set Topology

namespace TauCeti

namespace IsCollar

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

/-- Scaling the depth of a point of `N × [0, 1)` by a time `s ∈ [0, 1]`:
`(s, (x, t)) ↦ (x, s t)`. -/
private def scaleDepth : C(unitInterval × (N × Ico (0 : ℝ) 1), N × Ico (0 : ℝ) 1) :=
  ⟨fun q ↦ (q.2.1, ⟨q.1 * q.2.2, mul_nonneg q.1.2.1 q.2.2.2.1,
    (mul_le_of_le_one_left q.2.2.2.1 q.1.2.2).trans_lt q.2.2.2.2⟩), by fun_prop⟩

variable (h : IsCollar f c)
include h

/-- A collar is a homeomorphism onto its image. -/
private noncomputable def rangeHomeomorph : N × Ico (0 : ℝ) 1 ≃ₜ range c :=
  h.isOpenEmbedding.isEmbedding.toHomeomorph

private theorem rangeHomeomorph_apply (p : N × Ico (0 : ℝ) 1) :
    h.rangeHomeomorph p = ⟨c p, p, rfl⟩ :=
  Subtype.ext (h.isOpenEmbedding.isEmbedding.toHomeomorph_apply_coe p)

/-- The zero slice of a collar, as a map into the image of the collar. -/
private def toRange : C(N, range c) :=
  ⟨fun x ↦ ⟨f x, h.range_subset_range ⟨x, rfl⟩⟩, h.continuous.subtype_mk _⟩

/-- The projection of the image of a collar onto the first coordinate, `c (x, t) ↦ x`. -/
private noncomputable def ofRange : C(range c, N) :=
  ⟨fun z ↦ (h.rangeHomeomorph.symm z).1, by fun_prop⟩

/-- The projection `c (x, t) ↦ x` undoes the zero slice. -/
private theorem ofRange_toRange (x : N) : h.ofRange (h.toRange x) = x := by
  have hx : h.toRange x = h.rangeHomeomorph (x, ⟨0, by norm_num⟩) := by
    rw [h.rangeHomeomorph_apply]
    exact Subtype.ext (h.apply_zero x).symm
  simp [ofRange, hx]

/-- The homotopy of the image of a collar that pushes `c (x, t)` to `c (x, s t)`, from the
projection onto the zero slice at `s = 0` to the identity at `s = 1`. -/
private noncomputable def rangeHomotopy :
    (h.toRange.comp h.ofRange).Homotopy (ContinuousMap.id (range c)) where
  toFun p := h.rangeHomeomorph (scaleDepth (p.1, h.rangeHomeomorph.symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left z := Subtype.ext <| by
    simp [rangeHomeomorph_apply, toRange, ofRange, scaleDepth, ← h.apply_zero]
  map_one_left z := by simp [scaleDepth]

/-- **The image of a collar deformation retracts onto its zero slice.** The zero slice `f`, read
as a map into the image of the collar, is a homotopy equivalence. Its homotopy inverse sends
`c (x, t)` to `x`, and the homotopy to the identity pushes `c (x, t)` to `c (x, s t)`. -/
noncomputable def homotopyEquivRange : ContinuousMap.HomotopyEquiv N (range c) where
  toFun := h.toRange
  invFun := h.ofRange
  left_inv := by
    have hid : h.ofRange.comp h.toRange = ContinuousMap.id N :=
      ContinuousMap.ext h.ofRange_toRange
    rw [hid]
  right_inv := ⟨h.rangeHomotopy⟩

/-- The homotopy equivalence of a collar is its zero slice. -/
@[simp]
theorem coe_homotopyEquivRange_apply (x : N) : (h.homotopyEquivRange x : M) = f x :=
  (rfl)

/-- The homotopy inverse of the homotopy equivalence of a collar sends `c (x, t)` to `x`. -/
@[simp]
theorem homotopyEquivRange_symm_apply (p : N × Ico (0 : ℝ) 1) :
    h.homotopyEquivRange.symm ⟨c p, p, rfl⟩ = p.1 := by
  rw [← h.rangeHomeomorph_apply]
  exact congrArg Prod.fst (h.rangeHomeomorph.symm_apply_apply p)

end IsCollar

end TauCeti
