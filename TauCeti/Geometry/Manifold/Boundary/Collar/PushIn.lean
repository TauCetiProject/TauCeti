/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Pushing a space off a collared boundary

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`) in a Hausdorff space `M`,
with compact boundary parameter space `N`, as for the boundary of a compact manifold with boundary
or with corners. The collar of depth at most `t < 1` is then compact, and a compact set missing the
boundary `f(N)` misses the collar of some positive depth
(`TauCeti.IsCollar.exists_disjoint_collarPart`).

Raising the depth coordinate of the collar to at least `τ / 2`, for `τ ∈ [0, 1]`, and leaving the
points outside the collar where they are, deforms the identity of `M` into a map with values off
the boundary, through maps which keep the complement of the boundary inside it. So the inclusion of
the complement of the boundary is a homotopy equivalence
(`TauCeti.IsCollar.complHomotopyEquiv`), and so is every embedding with image the complement of
the boundary (`TauCeti.IsCollar.homotopyEquivOfRangeEq`): the interior of a compact manifold
with boundary is homotopy equivalent to the manifold. This is how the homology of a compact
manifold with collared boundary is read in its interior, as in Lefschetz duality.

## Main definitions

* `TauCeti.IsCollar.complHomotopyEquiv`: the inclusion `M ∖ f(N) → M` as a homotopy equivalence.
* `TauCeti.IsCollar.homotopyEquivOfRangeEq`: an embedding onto `M ∖ f(N)` as a homotopy
  equivalence.

## Main results

* `TauCeti.IsCollar.isCompact_image_le`: the collar of depth at most `t < 1` is compact.
* `TauCeti.IsCollar.exists_disjoint_collarPart`: a compact set missing the boundary misses the
  collar of some positive depth.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43, where the collar identifies a compact manifold with boundary with its interior up
  to homotopy.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- The collar of depth less than `1` is the whole image of the collar. -/
lemma collarPart_one : collarPart c 1 = range c := by
  ext x
  rw [mem_collarPart_iff]
  constructor
  · rintro ⟨p, -, rfl⟩
    exact mem_range_self p
  · rintro ⟨p, rfl⟩
    exact ⟨p, p.2.property.2, rfl⟩

namespace IsCollar

/-- Raising the depth coordinate to at least `τ / 2`. -/
private def raise (τ : I) (p : N × Ico (0 : ℝ) 1) : N × Ico (0 : ℝ) 1 :=
  (p.1, ⟨max p.2 ((τ : ℝ) / 2), le_max_of_le_left p.2.property.1,
    max_lt p.2.property.2 (by linarith [τ.property.2])⟩)

private lemma continuous_raise : Continuous fun q : I × (N × Ico (0 : ℝ) 1) ↦ raise q.1 q.2 :=
  continuous_snd.fst.prodMk (((continuous_subtypeVal.comp continuous_snd.snd).max
    ((continuous_subtypeVal.comp continuous_fst).div_const 2)).subtype_mk _)

variable (hc : IsCollar f c)
include hc

/-- A point `c p` of the collar lies on the boundary exactly when its depth is `0`. -/
lemma apply_mem_range_iff {p : N × Ico (0 : ℝ) 1} : c p ∈ range f ↔ (p.2 : ℝ) = 0 := by
  -- `c p ∈ range f` is `p ∈ c ⁻¹' range f` by definition of the preimage.
  exact (Set.ext_iff.1 hc.preimage_range p).trans ⟨fun h ↦ congrArg Subtype.val h.2,
    fun h ↦ ⟨trivial, Subtype.ext h⟩⟩

/-- **The collar of depth at most `t < 1` is compact** when the boundary parameter space is. -/
lemma isCompact_image_le [CompactSpace N] {t : ℝ} (ht : t < 1) :
    IsCompact (c '' {p | (p.2 : ℝ) ≤ t}) := by
  have hI : IsCompact (((↑) : Ico (0 : ℝ) 1 → ℝ) ⁻¹' Icc 0 t) :=
    IsInducing.subtypeVal.isCompact_preimage' isCompact_Icc fun s hs ↦
      ⟨⟨s, hs.1, hs.2.trans_lt ht⟩, rfl⟩
  have : {p : N × Ico (0 : ℝ) 1 | (p.2 : ℝ) ≤ t} =
      univ ×ˢ (((↑) : Ico (0 : ℝ) 1 → ℝ) ⁻¹' Icc 0 t) :=
    ext fun p ↦ by simp [p.2.property.1]
  rw [this]
  exact (isCompact_univ.prod hI).image hc.isOpenEmbedding.continuous

/-- **A compact set missing the boundary misses the collar of some positive depth.** -/
lemma exists_disjoint_collarPart [CompactSpace N] [T2Space M] {S : Set M} (hS : IsCompact S)
    (hSf : Disjoint S (range f)) : ∃ t, 0 < t ∧ Disjoint S (collarPart c t) := by
  -- The complements of the collars of depth at most `s ∈ (0, 1)` form a directed open cover of
  -- the complement of the boundary.
  let U : Ioo (0 : ℝ) 1 → Set M := fun s ↦ (c '' {p | (p.2 : ℝ) ≤ s})ᶜ
  have hU (s : Ioo (0 : ℝ) 1) : IsOpen (U s) :=
    (hc.isCompact_image_le s.property.2).isClosed.isOpen_compl
  have hmono {s s' : Ioo (0 : ℝ) 1} (h : (s : ℝ) ≤ s') : U s' ⊆ U s :=
    compl_subset_compl.2 (image_mono fun _ hp ↦ le_trans hp h)
  have hdir : Directed (· ⊆ ·) U := fun s s' ↦
    ⟨⟨min s s', lt_min s.property.1 s'.property.1,
        (min_le_left _ _).trans_lt s.property.2⟩,
      hmono (min_le_left _ _), hmono (min_le_right _ _)⟩
  have hcover : S ⊆ ⋃ s, U s := by
    intro x hx
    rw [mem_iUnion]
    by_cases hxc : x ∈ range c
    · obtain ⟨q, rfl⟩ := hxc
      have hq : 0 < (q.2 : ℝ) := lt_of_le_of_ne q.2.property.1 fun h ↦
        hSf.notMem_of_mem_left hx ((hc.apply_mem_range_iff).2 h.symm)
      refine ⟨⟨q.2 / 2, half_pos hq, by linarith [q.2.property.2]⟩, ?_⟩
      rintro ⟨p, hp, hpq⟩
      rw [hc.isOpenEmbedding.injective hpq] at hp
      exact absurd hp (not_le.2 (half_lt_self hq))
    · exact ⟨⟨1 / 2, by norm_num, by norm_num⟩, fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩⟩
  have : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨s, hs⟩ := hS.elim_directed_cover U hU hcover hdir
  refine ⟨s, s.property.1, disjoint_left.2 fun x hx hxc ↦ ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_collarPart_iff.1 hxc
  exact hs hx ⟨p, hp.le, rfl⟩

open scoped Classical in
/-- The deformation raising the depth coordinate of the collar to at least `τ / 2`, and fixing
the points outside the collar. -/
private def pushInFun (q : I × M) : M :=
  if h : q.2 ∈ collarPart c 1 then c (raise q.1 (hc.collarCoord 1 ⟨q.2, h⟩)) else q.2

private lemma pushInFun_apply (τ : I) (p : N × Ico (0 : ℝ) 1) :
    hc.pushInFun (τ, c p) = c (raise τ p) := by
  have h : c p ∈ collarPart c 1 := collarPart_one ▸ mem_range_self p
  rw [pushInFun, dite_eq_left_of_eq_true (eq_true h), hc.collarCoord_apply ⟨c p, h⟩ p rfl]

private lemma pushInFun_of_notMem (τ : I) {x : M} (hx : x ∉ range c) : hc.pushInFun (τ, x) = x := by
  rw [pushInFun, dite_eq_right_of_eq_false (eq_false (collarPart_one ▸ hx))]

private lemma continuous_pushInFun [CompactSpace N] [T2Space M] : Continuous hc.pushInFun := by
  -- On the collar the deformation is read in collar coordinates; off the collar of depth at most
  -- `1 / 2` it is the identity.
  refine continuous_of_cover_nhds (s := fun b : Bool ↦ (if b then univ ×ˢ collarPart c 1 else
    univ ×ˢ (c '' {p | (p.2 : ℝ) ≤ 1 / 2})ᶜ : Set (I × M))) (fun q ↦ ?_) (fun b ↦ ?_)
  · by_cases hq : q.2 ∈ c '' {p | (p.2 : ℝ) ≤ 1 / 2}
    · refine ⟨true, (isOpen_univ.prod (hc.isOpen_collarPart 1)).mem_nhds ⟨trivial, ?_⟩⟩
      obtain ⟨p, hp, hpq⟩ := hq
      exact mem_collarPart_iff.2 ⟨p, lt_of_le_of_lt hp (by norm_num), hpq⟩
    · exact ⟨false, (isOpen_univ.prod (hc.isCompact_image_le (by norm_num)).isClosed.isOpen_compl
        ).mem_nhds ⟨trivial, hq⟩⟩
  · cases b
    · refine continuous_snd.continuousOn.congr ?_
      rintro ⟨τ, x⟩ hq
      by_cases hxc : x ∈ range c
      · obtain ⟨p, rfl⟩ := hxc
        have hp' : (1 / 2 : ℝ) < p.2 := not_le.1 fun h ↦ hq.2 ⟨p, h, rfl⟩
        rw [hc.pushInFun_apply]
        refine congrArg c (Prod.ext rfl (Subtype.ext (max_eq_left ?_)))
        linarith [τ.property.2]
      · exact hc.pushInFun_of_notMem τ hxc
    · rw [continuousOn_iff_continuous_domRestrict]
      have : Continuous fun q : (univ ×ˢ collarPart c 1 : Set (I × M)) ↦
          c (raise q.val.1 (hc.collarCoord 1 ⟨q.val.2, q.property.2⟩)) :=
        hc.isOpenEmbedding.continuous.comp (continuous_raise.comp
          ((continuous_fst.comp continuous_subtypeVal).prodMk
            ((map_continuous _).comp ((continuous_snd.comp continuous_subtypeVal).subtype_mk _))))
      refine this.congr fun q ↦ ?_
      rw [domRestrict_apply, pushInFun, dite_eq_left_of_eq_true (eq_true q.property.2)]

/-- At time `0` the deformation is the identity. -/
private lemma pushInFun_zero (x : M) : hc.pushInFun (0, x) = x := by
  by_cases hx : x ∈ range c
  · obtain ⟨p, rfl⟩ := hx
    rw [hc.pushInFun_apply]
    refine congrArg c (Prod.ext rfl (Subtype.ext (max_eq_left ?_)))
    simpa using p.2.property.1
  · exact hc.pushInFun_of_notMem 0 hx

/-- The deformation never moves a point onto the boundary. -/
private lemma pushInFun_notMem (τ : I) {x : M} (hx : x ∉ range f) :
    hc.pushInFun (τ, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.pushInFun_apply, hc.apply_mem_range_iff]
    have hp : (p.2 : ℝ) ≠ 0 := fun h ↦ hx ((hc.apply_mem_range_iff).2 h)
    exact (lt_of_lt_of_le (lt_of_le_of_ne p.2.property.1 hp.symm) (le_max_left _ _)).ne'
  · rwa [hc.pushInFun_of_notMem τ hxc]

/-- At time `1` the deformation has values off the boundary. -/
private lemma pushInFun_one_notMem (x : M) : hc.pushInFun (1, x) ∉ range f := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.pushInFun_apply, hc.apply_mem_range_iff]
    exact (lt_of_lt_of_le (by norm_num) (le_max_right _ _)).ne'
  · rw [hc.pushInFun_of_notMem 1 hxc]
    exact fun hx ↦ hxc (hc.range_subset_range hx)

variable [CompactSpace N] [T2Space M]

/-- The deformation as a homotopy from the identity of `M`. -/
private def pushIn : ContinuousMap.Homotopy (ContinuousMap.id M)
    ⟨fun x ↦ hc.pushInFun (1, x), hc.continuous_pushInFun.comp (Continuous.prodMk_right 1)⟩ where
  toFun := hc.pushInFun
  continuous_toFun := hc.continuous_pushInFun
  map_zero_left := hc.pushInFun_zero
  map_one_left _ := rfl

/-- **The inclusion of the complement of a collared boundary is a homotopy equivalence**, for a
compact boundary parameter space in a Hausdorff space: raising the depth of the collar pushes `M`
off the boundary. -/
def complHomotopyEquiv : ContinuousMap.HomotopyEquiv ((range f)ᶜ : Set M) M where
  toFun := ⟨Subtype.val, continuous_subtypeVal⟩
  invFun := ⟨fun x ↦ ⟨hc.pushInFun (1, x), hc.pushInFun_one_notMem x⟩,
    (hc.continuous_pushInFun.comp (Continuous.prodMk_right 1)).subtype_mk _⟩
  left_inv := ⟨(ContinuousMap.Homotopy.symm
    { toFun := fun q ↦ ⟨hc.pushInFun (q.1, q.2), hc.pushInFun_notMem q.1 q.2.property⟩
      continuous_toFun := (hc.continuous_pushInFun.comp
        (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext (hc.pushInFun_zero x)
      map_one_left := fun _ ↦ rfl })⟩
  right_inv := ⟨(hc.pushIn).symm⟩

/-- The homotopy equivalence `M ∖ f(N) ≃ₕ M` is the inclusion. -/
@[simp]
lemma coe_complHomotopyEquiv : ⇑hc.complHomotopyEquiv = Subtype.val := by
  rw [complHomotopyEquiv]
  rfl

/-- **An embedding onto the complement of a collared boundary is a homotopy equivalence**, for a
compact boundary parameter space in a Hausdorff space: the interior of a compact manifold with
collared boundary is homotopy equivalent to the manifold. -/
def homotopyEquivOfRangeEq {P : Type*} [TopologicalSpace P] {ι : P → M} (hι : IsEmbedding ι)
    (hιf : range ι = (range f)ᶜ) : ContinuousMap.HomotopyEquiv P M :=
  ((hι.toHomeomorph.trans (Homeomorph.setCongr hιf)).toHomotopyEquiv).trans hc.complHomotopyEquiv

/-- The homotopy equivalence of an embedding onto the complement of the boundary is the
embedding. -/
@[simp]
lemma coe_homotopyEquivOfRangeEq {P : Type*} [TopologicalSpace P] {ι : P → M}
    (hι : IsEmbedding ι) (hιf : range ι = (range f)ᶜ) :
    ⇑(hc.homotopyEquivOfRangeEq hι hιf) = ι := by
  rw [homotopyEquivOfRangeEq]
  exact funext fun x ↦ congrFun hc.coe_complHomotopyEquiv _

end IsCollar

end TauCeti
