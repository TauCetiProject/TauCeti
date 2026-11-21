/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.Boundary.Collar.Topological

/-!
# The complement of a collared boundary is homotopy equivalent to the whole space

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`), with `N` compact and
`M` Hausdorff. Pushing every point of the collar inward along its collar line, by an amount that
vanishes from depth `1 / 2` on, moves the whole space off the boundary `f(N)`, and the straight-line
homotopy in the depth coordinate connects this push to the identity without ever moving a point
onto `f(N)`. Hence the inclusion of the complement `M \ f(N)` into `M` is a homotopy equivalence
(`TauCeti.IsCollar.complHomotopyEquiv`), whose homotopy inverse is the push and fixes every point
of depth at least `1 / 2`.

Concretely, the depth `t` of a point `c (x, t)` is pushed at time `s ∈ [0, 1]` to
`max t (s (1/2 - t))`. This is `t` at time `0` and for `t ≥ 1/2`, never smaller than `t`, and at
time `1` at least `1/4`. The push is extended by the identity outside the collar. It is continuous
there because the part `c(N × [0, 1/2])` of the collar that moves is compact, hence closed in `M`.
That is where compactness of `N` and the Hausdorff property of `M` are used.

Applied to the topological collar of a compact boundary of a manifold
(`TauCeti.isCollared_subtypeVal_boundary`), this shows that the inclusion of the interior of a
Hausdorff charted space over the half-space `𝓡∂ (n + 1)` with compact boundary is a homotopy
equivalence (`TauCeti.interiorHomotopyEquiv`). This is the homotopy-theoretic half of
J. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.26, there proved with a smooth
collar; only a topological collar is needed.

## Main definitions

* `TauCeti.IsCollar.complHomotopyEquiv`: the inclusion `M \ f(N) → M` of the complement of a
  collared compact set, as a homotopy equivalence.
* `TauCeti.interiorHomotopyEquiv`: the inclusion of the interior of a Hausdorff charted space over
  the half-space with compact boundary, as a homotopy equivalence.

## Main results

* `TauCeti.IsCollar.coe_complHomotopyEquiv` and `TauCeti.coe_interiorHomotopyEquiv`: the homotopy
  equivalences are the inclusions.
* `TauCeti.IsCollar.coe_complHomotopyEquiv_symm_apply_of_le`: the homotopy inverse fixes the
  points of the collar of depth at least `1 / 2`, and
  `TauCeti.IsCollar.coe_complHomotopyEquiv_symm_apply_of_notMem_range` the points outside the
  collar.

## References

* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.26.
-/

public section

noncomputable section

open Set Topology unitInterval
open scoped Manifold

namespace TauCeti

namespace IsCollar

section PushCoord

variable {N : Type*}

/-- The inward push of collar coordinates at time `s`: the depth `t` becomes `max t (s (1/2 - t))`,
which is `t` at time `0` and from depth `1/2` on, and at least `1/4` at time `1`. -/
private def pushCoord (s : I) (p : N × Ico (0 : ℝ) 1) : N × Ico (0 : ℝ) 1 :=
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
private def push (c : N × Ico (0 : ℝ) 1 → M) (q : I × M) : M :=
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

/-- The push never moves a point onto the boundary `f(N)`. -/
private theorem push_notMem_range (s : I) {x : M} (hx : x ∉ range f) :
    push c (s, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.push_apply]
    intro hmem
    have h₀ : ((pushCoord s p).2 : ℝ) = 0 :=
      congrArg Subtype.val (hc.preimage_range.subset hmem).2
    have hp : (p.2 : ℝ) = 0 := le_antisymm ((le_pushCoord s p).trans h₀.le) p.2.property.1
    refine hx ⟨p.1, ?_⟩
    rw [← hc.apply_zero]
    exact congrArg c (Prod.ext rfl (Subtype.ext hp.symm))
  · rw [push_of_notMem_range s hxc]
    exact fun h ↦ hxc (hc.range_subset_range h)

/-- At time `1` the push moves every point off the boundary `f(N)`. -/
private theorem push_one_notMem_range (x : M) : push c (1, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.push_apply]
    intro hmem
    have h₀ : ((pushCoord 1 p).2 : ℝ) = 0 :=
      congrArg Subtype.val (hc.preimage_range.subset hmem).2
    exact (pos_pushCoord_one p).ne' h₀
  · rw [push_of_notMem_range 1 hxc]
    exact fun h ↦ hxc (hc.range_subset_range h)

variable [CompactSpace N] [T2Space M]

/-- The push at time `1`, a map from the whole space to the complement of the boundary. -/
private def pushOff : C(M, ((range f)ᶜ : Set M)) :=
  ⟨fun x ↦ ⟨push c (1, x), hc.push_one_notMem_range x⟩,
    (hc.continuous_push.comp (Continuous.prodMk_right 1)).subtype_mk _⟩

/-- **The complement of a collared compact set is homotopy equivalent to the whole space.** If `c`
is a collar of `f : N → M` with `N` compact and `M` Hausdorff, the inclusion `M \ f(N) → M` is a
homotopy equivalence. Its homotopy inverse pushes every point of the collar inward along its collar
line, by an amount vanishing from depth `1 / 2` on. -/
def complHomotopyEquiv : ContinuousMap.HomotopyEquiv ((range f)ᶜ : Set M) M where
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

/-- The homotopy inverse of the inclusion `M \ f(N) → M` fixes the points of the collar of depth at
least `1 / 2`. -/
theorem coe_complHomotopyEquiv_symm_apply_of_le {p : N × Ico (0 : ℝ) 1}
    (hp : 1 / 2 ≤ (p.2 : ℝ)) : (hc.complHomotopyEquiv.symm (c p) : M) = c p := by
  change push c (1, c p) = c p
  rw [hc.push_apply, pushCoord_of_le 1 hp]

/-- The homotopy inverse of the inclusion `M \ f(N) → M` fixes the points outside the collar. -/
theorem coe_complHomotopyEquiv_symm_apply_of_notMem_range {x : M} (hx : x ∉ range c) :
    (hc.complHomotopyEquiv.symm x : M) = x :=
  push_of_notMem_range 1 hx

end IsCollar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [T2Space M]

/-- **The interior of a manifold with compact boundary is homotopy equivalent to the manifold.**
For a Hausdorff charted space `M` over the half-space `𝓡∂ (n + 1)` whose boundary is compact, the
inclusion of the interior into `M` is a homotopy equivalence. The homotopy inverse pushes `M` off
its boundary along a topological collar (`TauCeti.isCollared_subtypeVal_boundary`). -/
def interiorHomotopyEquiv (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ContinuousMap.HomotopyEquiv ((𝓡∂ (n + 1)).interior M) M :=
  have := isCompact_iff_compactSpace.1 hK
  (Homeomorph.setCongr (by rw [Subtype.range_coe, ModelWithCorners.compl_boundary] :
      (𝓡∂ (n + 1)).interior M = (range ((↑) : (𝓡∂ (n + 1)).boundary M → M))ᶜ)).toHomotopyEquiv
    |>.trans (isCollared_iff.1 (isCollared_subtypeVal_boundary hK)).choose_spec.complHomotopyEquiv

/-- The homotopy equivalence between the interior of a manifold with compact boundary and the
manifold is the inclusion. -/
@[simp]
theorem coe_interiorHomotopyEquiv (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ⇑(interiorHomotopyEquiv hK) = Subtype.val :=
  (rfl)

end TauCeti
