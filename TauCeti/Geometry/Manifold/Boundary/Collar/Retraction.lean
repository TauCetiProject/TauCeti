/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global

/-!
# Homotopy equivalences of a collar

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`). Its image is an open
neighbourhood of the image of `f`, and it deformation retracts onto it: the homotopy
`c (x, t) ↦ c (x, s t)`, `s ∈ [0, 1]`, runs from the projection `c (x, t) ↦ f x` to the identity.
So `f`, read as a map into the image of the collar, is a homotopy equivalence
(`TauCeti.IsCollar.homotopyEquivRange`), with homotopy inverse `c (x, t) ↦ x`.

This is how an open collar neighbourhood replaces the boundary of a manifold in homology: for
`N ⊆ M`, the inclusion of pairs `(M, N) → (M, c (N × [0, 1)))` induces isomorphisms on relative
homology, by the five lemma.

If moreover `N` is compact and `M` is Hausdorff, then pushing every point of the collar inward
along its collar line, by an amount that vanishes from depth `1 / 2` on, moves the whole space off
`f(N)`. Concretely, the depth `t` of a point `c (x, t)` is pushed at time `s ∈ [0, 1]` to
`max t (s (1/2 - t))`. This is `t` at time `0` and for `t ≥ 1/2`, never smaller than `t`, and at
time `1` at least `1/4`, so the homotopy sending depth `t` at time `s` to `max t (s (1/2 - t))`
connects the push to the identity without ever moving a point onto `f(N)`. Hence the inclusion of
the complement `M \ f(N)` into `M` is a homotopy equivalence
(`TauCeti.IsCollar.complHomotopyEquiv`), whose homotopy inverse is the push at time `1` and fixes
every point of depth at least `1 / 2`. The push is extended by the identity outside the collar. It
is continuous there because the part `c(N × [0, 1/2])` of the collar that moves is compact, hence
closed in `M`. That is where compactness of `N` and the Hausdorff property of `M` are used.

## Main definitions

* `TauCeti.IsCollar.homotopyEquivRange`: the zero slice of a collar is a homotopy equivalence onto
  the image of the collar.
* `TauCeti.IsCollar.complHomotopyEquiv`: the inclusion `M \ f(N) → M` of the complement of a
  collared compact set, as a homotopy equivalence.

## Main results

* `TauCeti.IsCollar.coe_complHomotopyEquiv`: the homotopy equivalence `M \ f(N) ≃ₕ M` is the
  inclusion.
* `TauCeti.IsCollar.coe_complHomotopyEquiv_symm_apply`: its homotopy inverse sends `c (x, t)` to
  `c (x, max t (1/2 - t))`, so it fixes the points of the collar of depth at least `1 / 2`
  (`TauCeti.IsCollar.coe_complHomotopyEquiv_symm_apply_of_le`), and
  `TauCeti.IsCollar.coe_complHomotopyEquiv_symm_apply_of_notMem_range`: it fixes the points outside
  the collar.
-/

public section

open Set Topology unitInterval

namespace TauCeti

namespace IsCollar

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

/-- Scaling the depth of a point of `N × [0, 1)` by a time `s ∈ [0, 1]`:
`(s, (x, t)) ↦ (x, s t)`. -/
private def scaleDepth : C(unitInterval × (N × Ico (0 : ℝ) 1), N × Ico (0 : ℝ) 1) :=
  ⟨fun q ↦ (q.2.1, ⟨q.1 * q.2.2, mul_nonneg q.1.property.1 q.2.2.property.1,
    (mul_le_of_le_one_left q.2.2.property.1 q.1.property.2).trans_lt q.2.2.property.2⟩),
        by fun_prop⟩

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

namespace IsCollar

section PushCoord

variable {N : Type*}

/-- The inward push of collar coordinates at time `s`: the depth `t` becomes `max t (s (1/2 - t))`,
which is `t` at time `0` and from depth `1/2` on, and at least `1/4` at time `1`. -/
private noncomputable def pushCoord (s : I) (p : N × Ico (0 : ℝ) 1) : N × Ico (0 : ℝ) 1 :=
  (p.1, ⟨max p.2 (s * (1 / 2 - p.2)), le_max_of_le_left p.2.property.1, max_lt p.2.property.2 (by
    nlinarith [mul_nonneg s.property.1 p.2.property.1, s.property.2])⟩)

private theorem continuous_pushCoord [TopologicalSpace N] :
    Continuous fun q : I × (N × Ico (0 : ℝ) 1) ↦ pushCoord q.1 q.2 := by
  unfold pushCoord
  fun_prop

private theorem coe_pushCoord_snd (s : I) (p : N × Ico (0 : ℝ) 1) :
    ((pushCoord s p).2 : ℝ) = max (p.2 : ℝ) (s * (1 / 2 - (p.2 : ℝ))) :=
  rfl

private theorem pushCoord_zero (p : N × Ico (0 : ℝ) 1) : pushCoord 0 p = p :=
  Prod.ext rfl (Subtype.ext (by simp [coe_pushCoord_snd, p.2.property.1]))

private theorem pushCoord_of_le (s : I) {p : N × Ico (0 : ℝ) 1} (hp : 1 / 2 ≤ (p.2 : ℝ)) :
    pushCoord s p = p :=
  Prod.ext rfl (Subtype.ext (max_eq_left (by
    nlinarith [s.property.1, p.2.property.1])))

private theorem le_pushCoord (s : I) (p : N × Ico (0 : ℝ) 1) :
    (p.2 : ℝ) ≤ (pushCoord s p).2 :=
  le_max_left _ _

/-- At time `1` the push leaves depth `0`. -/
private theorem pos_pushCoord_one (p : N × Ico (0 : ℝ) 1) : 0 < ((pushCoord 1 p).2 : ℝ) := by
  have h₁ := le_max_left (p.2 : ℝ) (1 * (1 / 2 - p.2))
  have h₂ := le_max_right (p.2 : ℝ) (1 * (1 / 2 - p.2))
  rw [coe_pushCoord_snd]
  push_cast at h₁ h₂ ⊢
  linarith

end PushCoord

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

/-- The inward push of the whole space at time `s`: the push of collar coordinates on the image of
the collar, extended by the identity. -/
private noncomputable def push (c : N × Ico (0 : ℝ) 1 → M) (q : I × M) : M :=
  Function.extend c (fun p ↦ c (pushCoord q.1 p)) id q.2

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem push_of_notMem_range (s : I) {x : M} (hx : x ∉ range c) : push c (s, x) = x :=
  Function.extend_apply' _ _ _ fun ⟨p, hp⟩ ↦ hx ⟨p, hp⟩

variable (hc : IsCollar f c)
include hc

private theorem push_apply (s : I) (p : N × Ico (0 : ℝ) 1) :
    push c (s, c p) = c (pushCoord s p) :=
  hc.isOpenEmbedding.injective.extend_apply _ _ p

private theorem push_zero (x : M) : push c (0, x) = x := by
  by_cases hx : x ∈ range c
  · obtain ⟨p, rfl⟩ := hx
    rw [hc.push_apply, pushCoord_zero]
  · exact push_of_notMem_range 0 hx

/-- Outside the part `c(N × [0, 1/2])` of the collar, the push is the identity. -/
private theorem push_of_notMem_image (s : I) {x : M}
    (hx : x ∉ c '' {p | (p.2 : ℝ) ≤ 1 / 2}) : push c (s, x) = x := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.push_apply, pushCoord_of_le s (le_of_lt (not_le.1 fun h ↦ hx ⟨p, h, rfl⟩))]
  · exact push_of_notMem_range s hxc

/-- The part `c(N × [0, 1/2])` of a collar of a compact space in a Hausdorff space is closed. -/
private theorem isClosed_image_le [CompactSpace N] [T2Space M] :
    IsClosed (c '' {p | (p.2 : ℝ) ≤ 1 / 2}) := by
  have hS : IsCompact {t : Ico (0 : ℝ) 1 | (t : ℝ) ≤ 1 / 2} := by
    rw [Subtype.isCompact_iff]
    convert isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2) using 1
    ext t
    refine ⟨fun ⟨u, hu, hut⟩ ↦ hut ▸ ⟨u.property.1, hu⟩, fun ht ↦ ⟨⟨t, ht.1, ?_⟩, ht.2, rfl⟩⟩
    linarith [ht.2]
  have h : {p : N × Ico (0 : ℝ) 1 | (p.2 : ℝ) ≤ 1 / 2} =
      univ ×ˢ {t : Ico (0 : ℝ) 1 | (t : ℝ) ≤ 1 / 2} := by
    ext p
    simp
  rw [h]
  exact ((isCompact_univ.prod hS).image hc.isOpenEmbedding.continuous).isClosed

/-- The push is continuous: on the open image of the collar it is the push of collar coordinates,
and on the open complement of `c(N × [0, 1/2])` it is the identity. -/
private theorem continuous_push [CompactSpace N] [T2Space M] : Continuous (push c) := by
  have he : IsOpenEmbedding (Prod.map id c : I × (N × Ico (0 : ℝ) 1) → I × M) :=
    IsOpenEmbedding.id.prodMap hc.isOpenEmbedding
  refine continuous_iff_continuousAt.2 fun ⟨s, x⟩ ↦ ?_
  by_cases hx : x ∈ c '' {p | (p.2 : ℝ) ≤ 1 / 2}
  · obtain ⟨p, -, rfl⟩ := hx
    have h : push c ∘ Prod.map id c = fun q ↦ c (pushCoord q.1 q.2) :=
      funext fun q ↦ hc.push_apply q.1 q.2
    refine (he.continuousAt_iff (x := (s, p))).1 ?_
    rw [h]
    exact (hc.isOpenEmbedding.continuous.comp continuous_pushCoord).continuousAt
  · have hU : (univ ×ˢ (c '' {p | (p.2 : ℝ) ≤ 1 / 2})ᶜ : Set (I × M)) ∈ 𝓝 (s, x) :=
      prod_mem_nhds Filter.univ_mem (hc.isClosed_image_le.isOpen_compl.mem_nhds hx)
    refine continuousAt_snd.congr (Filter.mem_of_superset hU fun q hq ↦ ?_)
    exact (hc.push_of_notMem_image q.1 hq.2).symm

/-- A point of the collar on the boundary `f(N)` has depth `0`. -/
private theorem coe_snd_eq_zero_of_apply_mem_range {p : N × Ico (0 : ℝ) 1}
    (hp : c p ∈ range f) : (p.2 : ℝ) = 0 :=
  congrArg Subtype.val (hc.preimage_range.subset hp).2

/-- A point outside the collar is not on the boundary `f(N)`. -/
private theorem notMem_range_of_notMem_range_collar {x : M} (hx : x ∉ range c) : x ∉ range f :=
  fun h ↦ hx (hc.range_subset_range h)

/-- The push never moves a point onto the boundary `f(N)`. -/
private theorem push_notMem_range (s : I) {x : M} (hx : x ∉ range f) :
    push c (s, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.push_apply]
    intro hmem
    have hp : (p.2 : ℝ) = 0 := le_antisymm
      ((le_pushCoord s p).trans (hc.coe_snd_eq_zero_of_apply_mem_range hmem).le) p.2.property.1
    refine hx ⟨p.1, ?_⟩
    rw [← hc.apply_zero]
    exact congrArg c (Prod.ext rfl (Subtype.ext hp.symm))
  · rw [push_of_notMem_range s hxc]
    exact hc.notMem_range_of_notMem_range_collar hxc

/-- At time `1` the push moves every point off the boundary `f(N)`. -/
private theorem push_one_notMem_range (x : M) : push c (1, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.push_apply]
    exact fun hmem ↦ (pos_pushCoord_one p).ne' (hc.coe_snd_eq_zero_of_apply_mem_range hmem)
  · rw [push_of_notMem_range 1 hxc]
    exact hc.notMem_range_of_notMem_range_collar hxc

variable [CompactSpace N] [T2Space M]

/-- The push at time `1`, a map from the whole space to the complement of the boundary. -/
private noncomputable def pushOff : C(M, ((range f)ᶜ : Set M)) :=
  ⟨fun x ↦ ⟨push c (1, x), hc.push_one_notMem_range x⟩,
    (hc.continuous_push.comp (Continuous.prodMk_right 1)).subtype_mk _⟩

/-- **The complement of a collared compact set is homotopy equivalent to the whole space.** If `c`
is a collar of `f : N → M` with `N` compact and `M` Hausdorff, the inclusion `M \ f(N) → M` is a
homotopy equivalence. Its homotopy inverse pushes every point of the collar inward along its collar
line, by an amount vanishing from depth `1 / 2` on. -/
noncomputable def complHomotopyEquiv : ContinuousMap.HomotopyEquiv ((range f)ᶜ : Set M) M where
  toFun := ⟨Subtype.val, continuous_subtypeVal⟩
  invFun := hc.pushOff
  left_inv := ⟨{
    toFun := fun q ↦ ⟨push c (σ q.1, q.2), hc.push_notMem_range _ q.2.property⟩
    continuous_toFun := (hc.continuous_push.comp
      ((continuous_symm.comp continuous_fst).prodMk
        (continuous_subtypeVal.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x ↦ Subtype.ext (by simp [pushOff])
    map_one_left := fun x ↦ Subtype.ext (by simp [hc.push_zero]) }⟩
  right_inv := ⟨{
    toFun := fun q ↦ push c (σ q.1, q.2)
    continuous_toFun := hc.continuous_push.comp
      ((continuous_symm.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun x ↦ by simp [pushOff]
    map_one_left := fun x ↦ by simp [hc.push_zero] }⟩

/-- The homotopy equivalence `M \ f(N) ≃ₕ M` of a collar is the inclusion. -/
@[simp]
theorem coe_complHomotopyEquiv : ⇑hc.complHomotopyEquiv = Subtype.val :=
  (rfl)

/-- The homotopy inverse of the inclusion `M \ f(N) → M` is the push at time `1`. -/
private theorem coe_complHomotopyEquiv_symm_eq_push (x : M) :
    (hc.complHomotopyEquiv.symm x : M) = push c (1, x) :=
  rfl

/-- The homotopy inverse of the inclusion `M \ f(N) → M` sends the point `c (x, t)` of the collar
to `c (x, max t (1/2 - t))`. -/
@[simp]
theorem coe_complHomotopyEquiv_symm_apply (p : N × Ico (0 : ℝ) 1) :
    (hc.complHomotopyEquiv.symm (c p) : M) =
      c (p.1, ⟨max (p.2 : ℝ) (1 / 2 - p.2), le_max_of_le_left p.2.property.1,
        max_lt p.2.property.2 (by linarith [p.2.property.1])⟩) := by
  rw [hc.coe_complHomotopyEquiv_symm_eq_push, hc.push_apply]
  exact congrArg c (Prod.ext rfl (Subtype.ext (by simp [coe_pushCoord_snd])))

/-- The homotopy inverse of the inclusion `M \ f(N) → M` fixes the points of the collar of depth at
least `1 / 2`. -/
theorem coe_complHomotopyEquiv_symm_apply_of_le {p : N × Ico (0 : ℝ) 1}
    (hp : 1 / 2 ≤ (p.2 : ℝ)) : (hc.complHomotopyEquiv.symm (c p) : M) = c p := by
  rw [hc.coe_complHomotopyEquiv_symm_apply]
  exact congrArg c (Prod.ext rfl (Subtype.ext (max_eq_left (by linarith))))

/-- The homotopy inverse of the inclusion `M \ f(N) → M` fixes the points outside the collar. -/
@[simp]
theorem coe_complHomotopyEquiv_symm_apply_of_notMem_range {x : M} (hx : x ∉ range c) :
    (hc.complHomotopyEquiv.symm x : M) = x := by
  rw [hc.coe_complHomotopyEquiv_symm_eq_push, push_of_notMem_range 1 hx]


end IsCollar

end TauCeti
