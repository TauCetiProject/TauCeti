/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
import TauCeti.Topology.Homeomorph.Extend
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Brown's collaring theorem

A map `f : N → M` is *locally collared* (`TauCeti.IsLocallyCollared`, defined in
`TauCeti.Geometry.Manifold.Boundary.Collar.Global`) when every point of `N` has an open
neighbourhood `U` such that `f` restricted to `U` has a collar, an open embedding
`c : U × [0, 1) → M` with zero slice `f`, which meets the image of `f` only along that zero slice.
This is M. Brown's notion: `f(U)` is collared in `(M \ f(N)) ∪ f(U)`. The condition on the image
keeps the positive-depth part of a local collar away from the rest of `f(N)`.

**Brown's collaring theorem** says that local collars can be assembled into a global collar. This
file proves it for a compact domain and a Hausdorff ambient space
(`TauCeti.IsLocallyCollared.isCollared`): an injective, locally collared map from a compact space
into a Hausdorff space is collared. Together with the easy converse this characterizes collared
maps out of compact spaces (`TauCeti.isCollared_iff_injective_and_isLocallyCollared`).

The proof is R. Connelly's. Attach an external collar `f(N) × (-∞, 0]` to `M` along `f(N)`;
inside `M × ℝ` this is the set of points `(m, 0)` and `(f x, t)` with `t ≤ 0`. Choose
finitely many local collars covering `N` and a partition of unity `φᵢ` subordinate to them. In the
chart of the `i`-th local collar, which runs from the external collar into `M`, push everything
inward by `φᵢ / 4`, damping the push to zero at depth `1 / 2` of the local collar so that it extends
by the identity to a homeomorphism of the whole space. The composite of these pushes moves every
point `(f x, t)` with `t ≤ -1/4` to `(f x, t + 1/4)`. Being a homeomorphism, it carries the strip
`f(N) × [-1/4, 0)` of the external collar onto an open neighbourhood of `f(N)` in `M`, and that is
the global collar.

The compactness of the domain makes the cover finite, so that only finitely many pushes are
composed. This is the case of compact boundaries, and of the codimension-one spheres to which the
theorem is applied in Brown's study of locally flat embeddings. Over a paracompact domain the
cover is only locally finite, and the pushes must instead be composed locally.

## Main results

* `TauCeti.IsLocallyCollared.isCollared`: **Brown's collaring theorem**, for a compact domain.
* `TauCeti.isCollared_iff_injective_and_isLocallyCollared`: a map from a compact space to a
  Hausdorff space is collared exactly when it is injective and locally collared.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. Connelly, *A new proof of Brown's collaring theorem*, Proceedings of the American Mathematical
  Society 27 (1971), 180–182.
-/

public section

open Set Topology Function

namespace TauCeti

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}

/-! ### The proof of Brown's theorem -/

section Brown

/-! #### The depth pushes

`push a` is the piecewise-linear homeomorphism of `ℝ` that translates `(-∞, 0]` by `a`, is the
identity on `[1/2, ∞)`, and is linear in between; `unpush a` is its inverse. They are the
one-dimensional pushes, for `0 ≤ a ≤ 1/4`. -/

/-- Translate by `a` up to `0`, interpolate linearly on `[0, 1/2]`, and fix `[1/2, ∞)`. -/
private def push (a s : ℝ) : ℝ := max (min (s + a) (a + (1 - 2 * a) * s)) s

/-- The inverse of `push a`. -/
private noncomputable def unpush (a y : ℝ) : ℝ := min (max (y - a) ((y - a) / (1 - 2 * a))) y

variable {a s y : ℝ}

private theorem push_of_nonpos (ha : 0 ≤ a) (hs : s ≤ 0) : push a s = s + a := by
  rw [push, min_eq_left (by nlinarith), max_eq_left (by linarith)]

private theorem push_of_mem_Icc (ha : 0 ≤ a) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    push a s = a + (1 - 2 * a) * s := by
  rw [push, min_eq_right (by nlinarith), max_eq_left (by nlinarith)]

private theorem push_of_half_le (ha : 0 ≤ a) (hs : 1 / 2 ≤ s) : push a s = s := by
  rw [push, min_eq_right (by nlinarith), max_eq_right (by nlinarith)]

private theorem push_zero_left (s : ℝ) : push 0 s = s := by
  simp [push]

private theorem push_lt_one (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) (hs : s < 1) : push a s < 1 := by
  refine max_lt ?_ hs
  rcases le_total s (1 / 2) with h | h
  · exact (min_le_left _ _).trans_lt (by linarith)
  · exact (min_le_right _ _).trans_lt (by nlinarith)

private theorem unpush_le (a y : ℝ) : unpush a y ≤ y := min_le_right _ _

private theorem unpush_push (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) (s : ℝ) : unpush a (push a s) = s := by
  have hd : 0 < 1 - 2 * a := by linarith
  rcases le_total s 0 with hs | hs
  · rw [push_of_nonpos ha0 hs, unpush, add_sub_cancel_right,
      max_eq_left ((div_le_iff₀ hd).2 (by nlinarith)), min_eq_left (by linarith)]
  rcases le_total s (1 / 2) with hs' | hs'
  · have h : a + (1 - 2 * a) * s - a = (1 - 2 * a) * s := by ring
    rw [push_of_mem_Icc ha0 hs hs', unpush, h, mul_div_cancel_left₀ _ hd.ne',
      max_eq_right (by nlinarith), min_eq_left (by nlinarith)]
  · rw [push_of_half_le ha0 hs', unpush,
      min_eq_right (le_max_of_le_right ((le_div_iff₀ hd).2 (by nlinarith)))]

private theorem push_unpush (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) (y : ℝ) : push a (unpush a y) = y := by
  have hd : 0 < 1 - 2 * a := by linarith
  rcases le_total y a with hy | hy
  · rw [unpush, max_eq_left ((div_le_iff₀ hd).2 (by nlinarith)), min_eq_left (by linarith),
      push_of_nonpos ha0 (by linarith), sub_add_cancel]
  rcases le_total y (1 / 2) with hy' | hy'
  · have h0 : 0 ≤ (y - a) / (1 - 2 * a) := div_nonneg (by linarith) hd.le
    have h1 : (y - a) / (1 - 2 * a) ≤ 1 / 2 := (div_le_iff₀ hd).2 (by nlinarith)
    rw [unpush, max_eq_right ((le_div_iff₀ hd).2 (by nlinarith)),
      min_eq_left ((div_le_iff₀ hd).2 (by nlinarith)), push_of_mem_Icc ha0 h0 h1,
      mul_div_cancel₀ _ hd.ne', add_sub_cancel]
  · rw [unpush, min_eq_right (le_max_of_le_right ((le_div_iff₀ hd).2 (by nlinarith))),
      push_of_half_le ha0 hy']

private theorem continuous_push : Continuous fun p : ℝ × ℝ => push p.1 p.2 := by
  unfold push
  fun_prop

/-! #### The space with an external collar -/

variable (f) in
/-- The space `M` with the external collar `f(N) × (-∞, 0]` attached along `f(N)`, realised as the
points `(m, 0)` and `(f x, t)`, `t ≤ 0`, of `M × ℝ`. -/
private def extended : Set (M × ℝ) := {p | p.2 ≤ 0 ∧ (p.2 = 0 ∨ p.1 ∈ range f)}

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem mk_mem_extended {x : N} {t : ℝ} (ht : t ≤ 0) : (f x, t) ∈ extended f :=
  ⟨ht, Or.inr ⟨x, rfl⟩⟩

variable (f) in
/-- `G` pushes the external collar inward by the depth function `b`: it moves `(f x, t)` to
`(f x, t + b x)` as long as the latter stays in the external collar. -/
private def PushesBy (G : extended f ≃ₜ extended f) (b : N → ℝ) : Prop :=
  ∀ x t (h : (f x, t) ∈ extended f), t + b x ≤ 0 →
    ((G ⟨(f x, t), h⟩ : extended f) : M × ℝ) = (f x, t + b x)

omit [TopologicalSpace N] in
private theorem PushesBy.trans {G H : extended f ≃ₜ extended f} {b a : N → ℝ}
    (hG : PushesBy f G b) (hH : PushesBy f H a) (ha : ∀ x, 0 ≤ a x) :
    PushesBy f (G.trans H) (b + a) := by
  intro x t h hle
  have hle' : t + (b x + a x) ≤ 0 := hle
  have h1 : t + b x ≤ 0 := by linarith [ha x]
  have hG' : G ⟨(f x, t), h⟩ = ⟨(f x, t + b x), mk_mem_extended h1⟩ := Subtype.ext (hG x t h h1)
  rw [Homeomorph.trans_apply, hG', hH x _ _ (by simpa only [Pi.add_apply, add_assoc] using hle),
    Pi.add_apply, add_assoc]

/-! #### The chart of a local collar

A local collar `c` of `f` over `U` extends across the external collar to a chart
`U × (-∞, 1) → extended f`, equal to `(u, s) ↦ (f u, s)` for `s ≤ 0` and to `(u, s) ↦ (c (u, s), 0)`
for `s ≥ 0`. -/

variable {U : Set N} {c : U × Ico (0 : ℝ) 1 → M}

/-- The depth `max s 0 ∈ [0, 1)` read by the local collar at chart depth `s < 1`. -/
private def depth (s : Iio (1 : ℝ)) : Ico (0 : ℝ) 1 :=
  ⟨max (s : ℝ) 0, le_max_right _ _, max_lt s.2 one_pos⟩

private theorem depth_eq_zero {s : Iio (1 : ℝ)} (hs : (s : ℝ) ≤ 0) :
    depth s = ⟨0, by norm_num⟩ :=
  Subtype.ext (max_eq_right hs)

private theorem continuous_depth : Continuous depth :=
  (continuous_subtype_val.max continuous_const).subtype_mk _

/-- The chart of `extended f` built from the local collar `c`. -/
private def chart (hc : IsCollar (f ∘ ((↑) : U → N)) c) (z : U × Iio (1 : ℝ)) : extended f :=
  ⟨(c (z.1, depth z.2), min (z.2 : ℝ) 0), min_le_right _ _, by
    rcases le_total (z.2 : ℝ) 0 with h | h
    · refine Or.inr ⟨z.1, ?_⟩
      rw [depth_eq_zero h, hc.apply_zero]
      rfl
    · exact Or.inl (min_eq_right h)⟩

private theorem coe_chart (hc : IsCollar (f ∘ ((↑) : U → N)) c) (z : U × Iio (1 : ℝ)) :
    (chart hc z : M × ℝ) = (c (z.1, depth z.2), min (z.2 : ℝ) 0) :=
  rfl

private theorem coe_chart_of_nonpos (hc : IsCollar (f ∘ ((↑) : U → N)) c) (u : U)
    {s : Iio (1 : ℝ)} (hs : (s : ℝ) ≤ 0) : (chart hc (u, s) : M × ℝ) = (f u, (s : ℝ)) := by
  rw [coe_chart, depth_eq_zero hs, hc.apply_zero, min_eq_left hs]
  rfl

private theorem continuous_chart (hc : IsCollar (f ∘ ((↑) : U → N)) c) :
    Continuous (chart hc) :=
  ((hc.isOpenEmbedding.continuous.comp (continuous_fst.prodMk
    (continuous_depth.comp continuous_snd))).prodMk
    ((continuous_subtype_val.comp continuous_snd).min continuous_const)).subtype_mk _

/-- Read in the chart, a point of the local collar `c` at height `t ≤ 0` is the point `(c q, t)`,
provided it lies in the external collar (`q` at depth zero) or in `M` (`t = 0`). -/
private theorem coe_chart_add (hc : IsCollar (f ∘ ((↑) : U → N)) c) (q : U × Ico (0 : ℝ) 1)
    {t : ℝ} (ht : t ≤ 0) (hqt : t = 0 ∨ (q.2 : ℝ) = 0) (h : (q.2 : ℝ) + t ∈ Iio 1) :
    (chart hc (q.1, ⟨(q.2 : ℝ) + t, h⟩) : M × ℝ) = (c q, t) := by
  rcases hqt with rfl | hq0
  · refine Prod.ext (congrArg c (Prod.ext rfl (Subtype.ext ?_))) ?_
    · simp [depth, q.2.2.1]
    · simp [coe_chart, q.2.2.1]
  · have hcq : c q = f q.1 :=
      (congrArg c (Prod.ext rfl (Subtype.ext hq0) : q = (q.1, ⟨0, by norm_num⟩))).trans
        (hc.apply_zero q.1)
    rw [coe_chart_of_nonpos hc _ (by simpa [hq0] using ht), hcq]
    simp [hq0]

/-- The part of `extended f` lying over the image of the local collar. -/
private def chartRange (c : U × Ico (0 : ℝ) 1 → M) : Set (extended f) :=
  {y | (y : M × ℝ).1 ∈ range c}

/-- The inverse of `chart hc` on `chartRange c`: the point `(c q, t)` has chart coordinates
`(q.1, q.2 + t)`. -/
private noncomputable def chartInv (hc : IsCollar (f ∘ ((↑) : U → N)) c)
    (y : chartRange (f := f) c) : U × Iio (1 : ℝ) :=
  let q := hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm ⟨(y : M × ℝ).1, y.2⟩
  (q.1, ⟨(q.2 : ℝ) + (y : M × ℝ).2, by
    have hq := q.2.2.2
    have ht := (y : extended f).2.1
    simp only [mem_Iio]
    linarith⟩)

/-- The chart of a local collar is an open embedding. -/
private theorem isOpenEmbedding_chart (hc : IsCollar (f ∘ ((↑) : U → N)) c)
    (hcf : ∀ p, c p ∈ range f → (p.2 : ℝ) = 0) : IsOpenEmbedding (chart hc) := by
  set e := hc.isOpenEmbedding.isEmbedding.toHomeomorph
  have hopen : IsOpen (chartRange (f := f) c) :=
    hc.isOpenEmbedding.isOpen_range.preimage (continuous_fst.comp continuous_subtype_val)
  have he : ∀ y : chartRange (f := f) c, c (e.symm ⟨(y : M × ℝ).1, y.2⟩) = (y : M × ℝ).1 :=
    fun y => congrArg Subtype.val (e.apply_symm_apply ⟨(y : M × ℝ).1, y.2⟩)
  let E : U × Iio (1 : ℝ) ≃ₜ chartRange (f := f) c :=
    { toFun := fun z => ⟨chart hc z, (z.1, depth z.2), rfl⟩
      invFun := chartInv hc
      left_inv := fun z => by
        have hq : hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm
            ⟨c (z.1, depth z.2), mem_range_self _⟩ = (z.1, depth z.2) :=
          hc.isOpenEmbedding.isEmbedding.toHomeomorph_symm_apply _
        simp only [chartInv, coe_chart, hq]
        refine Prod.ext rfl (Subtype.ext ?_)
        rcases le_total (z.2 : ℝ) 0 with h | h <;> simp [depth, h]
      right_inv := fun y => by
        obtain ⟨hy0, hy⟩ := (y : extended f).2
        -- `chartInv hc y` is by definition `(q.1, q.2 + t)` for `y = (c q, t)`.
        have hqt : (y : M × ℝ).2 = 0 ∨ ((e.symm ⟨(y : M × ℝ).1, y.2⟩).2 : ℝ) = 0 :=
          hy.imp id fun hy => hcf _ (by rw [he y]; exact hy)
        exact Subtype.ext (Subtype.ext ((coe_chart_add hc _ hy0 hqt _).trans
          (Prod.ext (he y) rfl)))
      continuous_toFun := (continuous_chart hc).subtype_mk _
      continuous_invFun := by
        have hq : Continuous fun y : chartRange (f := f) c => e.symm ⟨(y : M × ℝ).1, y.2⟩ :=
          e.symm.continuous.comp ((continuous_fst.comp
            (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
        exact (continuous_fst.comp hq).prodMk
          (((continuous_subtype_val.comp (continuous_snd.comp hq)).add
            (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk
            _) }
  exact hopen.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding

/-! #### One push -/

/-- The push by the depth function `a`, as a homeomorphism of the chart domain. -/
private noncomputable def pushHomeomorph (a : N → ℝ) (ha : Continuous a) (ha0 : ∀ x, 0 ≤ a x)
    (ha1 : ∀ x, a x ≤ 1 / 4) : (U × Iio (1 : ℝ)) ≃ₜ (U × Iio (1 : ℝ)) where
  toFun z := (z.1, ⟨push (a z.1) z.2, push_lt_one (ha0 _) (ha1 _) z.2.2⟩)
  invFun z := (z.1, ⟨unpush (a z.1) z.2, (unpush_le _ _).trans_lt z.2.2⟩)
  left_inv z := Prod.ext rfl (Subtype.ext (unpush_push (ha0 _) (ha1 _) _))
  right_inv z := Prod.ext rfl (Subtype.ext (push_unpush (ha0 _) (ha1 _) _))
  continuous_toFun := continuous_fst.prodMk ((continuous_push.comp
    ((ha.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _)
  continuous_invFun := by
    have ha' : Continuous fun z : U × Iio (1 : ℝ) => a z.1 :=
      ha.comp (continuous_subtype_val.comp continuous_fst)
    have hs : Continuous fun z : U × Iio (1 : ℝ) => (z.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine continuous_fst.prodMk (Continuous.subtype_mk ?_ _)
    exact ((hs.sub ha').max ((hs.sub ha').div (continuous_const.sub (continuous_const.mul ha'))
      fun z => by dsimp only [Pi.sub_apply, Pi.mul_apply]; linarith [ha1 z.1])).min hs

/-- The slab `T × [0, 1/2]` of the chart domain over a compact `T ⊆ U` is compact. -/
private theorem isCompact_slab {T : Set N} (hT : IsCompact T) (hTU : T ⊆ U) :
    IsCompact {z : U × Iio (1 : ℝ) | (z.1 : N) ∈ T ∧ (z.2 : ℝ) ∈ Icc 0 (1 / 2)} := by
  refine IsCompact.prod (s := (Subtype.val ⁻¹' T : Set U))
    (t := (Subtype.val ⁻¹' Icc 0 (1 / 2) : Set (Iio (1 : ℝ)))) ?_ ?_
  · rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hTU]
    exact hT
  · rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun r hr => mem_Iio.2 (hr.2.trans_lt (by norm_num))]
    exact isCompact_Icc

/-- A point of the external collar or of `f(N)` seen by the chart of a local collar over `U` lies
over `U`. -/
private theorem mem_of_coe_chart_eq (hf : Injective f) (hc : IsCollar (f ∘ ((↑) : U → N)) c)
    (hcf : ∀ p, c p ∈ range f → (p.2 : ℝ) = 0) {z : U × Iio (1 : ℝ)} {x : N} {t : ℝ}
    (h : (chart hc z : M × ℝ) = (f x, t)) : x ∈ U := by
  have hcz : c (z.1, depth z.2) = f x := congrArg Prod.fst h
  have hd : depth z.2 = ⟨0, by norm_num⟩ := Subtype.ext (hcf _ ⟨x, hcz.symm⟩)
  rw [hd, hc.apply_zero] at hcz
  exact hf hcz ▸ z.1.2

/-- A local collar and a depth function `a ≤ 1/4` supported in its domain give a homeomorphism of
`extended f` pushing the external collar inward by `a`. -/
private theorem exists_pushesBy [T2Space M] [CompactSpace N] (hf : Injective f)
    (hfc : Continuous f) (hc : IsCollar (f ∘ ((↑) : U → N)) c)
    (hcf : ∀ p, c p ∈ range f → (p.2 : ℝ) = 0) {a : N → ℝ} (ha : Continuous a)
    (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1 / 4) (hsupp : tsupport a ⊆ U) :
    ∃ G : extended f ≃ₜ extended f, PushesBy f G a := by
  set T := tsupport a
  have hT : IsCompact T := (isClosed_tsupport a).isCompact
  -- The push moves only the external collar over `T` and the image of the slab `T × [0, 1/2]`.
  set C : Set (extended f) := {y | (y : M × ℝ) ∈ (f '' T) ×ˢ Iic 0} ∪
    chart hc '' {z | (z.1 : N) ∈ T ∧ (z.2 : ℝ) ∈ Icc 0 (1 / 2)}
  have hC : IsClosed C :=
    (((hT.image hfc).isClosed.prod isClosed_Iic).preimage continuous_subtype_val).union
      ((isCompact_slab hT hsupp).image (continuous_chart hc)).isClosed
  have hCχ : C ⊆ range (chart hc) := by
    rintro y (⟨⟨x, hxT, hx⟩, ht⟩ | ⟨z, -, rfl⟩)
    · have ht' : (y : M × ℝ).2 ≤ 0 := mem_Iic.1 ht
      refine ⟨(⟨x, hsupp hxT⟩, ⟨(y : M × ℝ).2, by simp only [mem_Iio]; linarith⟩), ?_⟩
      exact Subtype.ext ((coe_chart_of_nonpos hc _ ht').trans (Prod.ext hx rfl))
    · exact mem_range_self z
  set Λ := pushHomeomorph (U := U) a ha ha0 ha1
  have hΛ : ∀ z, chart hc z ∉ C → Λ z = z := by
    intro z hz
    by_contra hne
    have hpush : push (a z.1) z.2 ≠ z.2 := fun h => hne (Prod.ext rfl (Subtype.ext h))
    have hzT : (z.1 : N) ∈ T := subset_tsupport a fun h => hpush (by rw [h, push_zero_left])
    rcases le_total (z.2 : ℝ) 0 with h0 | h0
    · have hmem : (chart hc z : M × ℝ) ∈ (f '' T) ×ˢ Iic 0 := by
        rw [coe_chart_of_nonpos hc _ h0]
        exact ⟨mem_image_of_mem f hzT, h0⟩
      exact hz (Or.inl hmem)
    rcases le_total (z.2 : ℝ) (1 / 2) with h1 | h1
    · exact hz (Or.inr (mem_image_of_mem _ ⟨hzT, h0, h1⟩))
    · exact hpush (push_of_half_le (ha0 _) h1)
  obtain ⟨H, hHχ, hHC⟩ :=
    (isOpenEmbedding_chart hc hcf).exists_homeomorph_extend Λ hC hCχ hΛ
  refine ⟨H, fun x t h hle => ?_⟩
  by_cases hxU : x ∈ U
  · -- Inside the chart the homeomorphism is the push itself.
    have ht : t < 1 := by linarith [h.1]
    have hy : (⟨(f x, t), h⟩ : extended f) = chart hc (⟨x, hxU⟩, ⟨t, ht⟩) :=
      Subtype.ext (coe_chart_of_nonpos hc ⟨x, hxU⟩ (s := ⟨t, ht⟩) h.1).symm
    have hΛz : Λ (⟨x, hxU⟩, ⟨t, ht⟩) =
        (⟨x, hxU⟩, ⟨t + a x, by simp only [mem_Iio]; linarith⟩) :=
      Prod.ext rfl (Subtype.ext (push_of_nonpos (ha0 x) h.1))
    rw [hy, hHχ, hΛz, coe_chart_of_nonpos hc _ hle]
  · -- Outside the chart nothing moves, and the push vanishes.
    have hax : a x = 0 := image_eq_zero_of_notMem_tsupport fun hxT => hxU (hsupp hxT)
    rw [hax, add_zero, hHC]
    rintro (⟨⟨x', hx'T, hx'⟩, -⟩ | ⟨z, -, hz⟩)
    · exact hxU (hf hx' ▸ hsupp hx'T)
    · exact hxU (mem_of_coe_chart_eq hf hc hcf (congrArg Subtype.val hz))

/-! #### Assembling the collar -/

omit [TopologicalSpace N] in
/-- A push by `1/4` carries the strip `f(N) × [-1/4, 0]` of the external collar into `M`. -/
private theorem PushesBy.coe_snd_eq_zero {G : extended f ≃ₜ extended f}
    (hG : PushesBy f G fun _ => 1 / 4) {x : N} {t : ℝ} (h : (f x, t) ∈ extended f)
    (ht : -(1 / 4) ≤ t) : (G ⟨(f x, t), h⟩ : M × ℝ).2 = 0 := by
  obtain ⟨hy0, hy | ⟨x', hx'⟩⟩ := (G ⟨(f x, t), h⟩).2
  · exact hy
  -- Otherwise the image is in the external collar, where it is the push of a point below the strip.
  by_contra hne
  have hlt : (G ⟨(f x, t), h⟩ : M × ℝ).2 < 0 := lt_of_le_of_ne hy0 hne
  have hq : G ⟨(f x', (G ⟨(f x, t), h⟩ : M × ℝ).2 - 1 / 4), mk_mem_extended (by linarith)⟩ =
      G ⟨(f x, t), h⟩ :=
    Subtype.ext ((hG x' _ _ (by linarith)).trans (Prod.ext hx' (by ring)))
  have h2 := congrArg (fun y : extended f => (y : M × ℝ).2) (G.injective hq)
  dsimp only at h2
  linarith

omit [TopologicalSpace N] in
/-- A push by `1/4` moves every point of the external collar below the strip
`f(N) × [-1/4, 0]` off `M`. -/
private theorem PushesBy.le_coe_snd {G : extended f ≃ₜ extended f}
    (hG : PushesBy f G fun _ => 1 / 4) {y : extended f} (hy : (G y : M × ℝ).2 = 0) :
    -(1 / 4) ≤ (y : M × ℝ).2 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨x, hx⟩ : (y : M × ℝ).1 ∈ range f := y.2.2.resolve_left (by linarith)
  have hy' : y = ⟨(f x, (y : M × ℝ).2), mk_mem_extended (by linarith)⟩ :=
    Subtype.ext (Prod.ext hx.symm rfl)
  rw [hy', hG x _ _ (by linarith)] at hy
  dsimp only at hy
  linarith

/-- A homeomorphism of `extended f` pushing the external collar inward by `1/4` gives a collar of
`f`: the image of the strip `f(N) × [-1/4, 0)`. -/
private theorem isCollared_of_pushesBy (hfe : IsEmbedding f) {G : extended f ≃ₜ extended f}
    (hG : PushesBy f G fun _ => 1 / 4) : IsCollared f := by
  -- `M` sits in `extended f` as the slice at height `0`.
  let ι : M → extended f := fun m => ⟨(m, 0), le_rfl, Or.inl rfl⟩
  have hι : Continuous ι := (continuous_id.prodMk continuous_const).subtype_mk _
  -- The strip of the external collar, parametrized by `N × [0, 1)`.
  let e : N × Ico (0 : ℝ) 1 → extended f := fun p =>
    ⟨(f p.1, ((p.2 : ℝ) - 1) / 4), mk_mem_extended (by linarith [p.2.2.2])⟩
  let aff : ℝ ≃ₜ ℝ :=
    { toFun := fun t => (t - 1) / 4
      invFun := fun t => 4 * t + 1
      left_inv := fun t => by ring
      right_inv := fun t => by ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have he : IsEmbedding e :=
    (hfe.prodMap (aff.isEmbedding.comp IsEmbedding.subtypeVal)).codRestrict _ _
  -- The collar is the push of the strip, which lands in `M`.
  let col : N × Ico (0 : ℝ) 1 → M := fun p => (G (e p) : M × ℝ).1
  have hcomp : ι ∘ col = G ∘ e := funext fun p =>
    Subtype.ext (Prod.ext rfl (hG.coe_snd_eq_zero _ (by linarith [p.2.2.1])).symm)
  have hcol : Continuous col :=
    continuous_fst.comp (continuous_subtype_val.comp (G.continuous.comp he.continuous))
  -- Its image is the part of `M` covered by the push of the open lower half of `extended f`.
  have hrange : range col = ι ⁻¹' (G '' {y | (y : M × ℝ).2 < 0}) := by
    ext m
    constructor
    · rintro ⟨p, rfl⟩
      have hp : ((p.2 : ℝ) - 1) / 4 < 0 := by linarith [p.2.2.2]
      exact ⟨e p, hp, (congrFun hcomp p).symm⟩
    · rintro ⟨y, hy, hym⟩
      have hy' : (y : M × ℝ).2 < 0 := hy
      have hge := hG.le_coe_snd (y := y) (by rw [hym])
      obtain ⟨x, hx⟩ : (y : M × ℝ).1 ∈ range f := y.2.2.resolve_left hy'.ne
      let p : N × Ico (0 : ℝ) 1 := (x, ⟨4 * (y : M × ℝ).2 + 1, by linarith, by linarith⟩)
      have hey : e p = y := Subtype.ext (Prod.ext hx (by simp only [e, p]; ring))
      have hp : (ι ∘ col) p = ι m := (congrFun hcomp p).trans (by rw [comp_apply, hey, hym])
      exact ⟨p, congrArg (fun z : extended f => (z : M × ℝ).1) hp⟩
  refine isCollared_iff.2 ⟨col, ⟨.of_comp hcol hι (hcomp ▸ G.isEmbedding.comp he), hrange ▸ ?_⟩,
    fun x => ?_⟩
  · exact (G.isOpenMap _ (isOpen_Iio.preimage
      (continuous_snd.comp continuous_subtype_val))).preimage hι
  · -- At depth zero the collar is `f`.
    have he0 : e (x, ⟨0, by norm_num⟩) = ⟨(f x, -(1 / 4)), mk_mem_extended (by norm_num)⟩ :=
      Subtype.ext (Prod.ext rfl (by norm_num))
    simp only [col, he0, hG x (-(1 / 4)) _ (by norm_num)]

end Brown

/-- **Brown's collaring theorem**, for a compact domain: an injective, locally collared map from a
compact space into a Hausdorff space is collared. The local collars are assembled into one by
pushing an external collar inward along each of them in turn (Connelly's proof). -/
theorem IsLocallyCollared.isCollared [CompactSpace N] [T2Space M] (h : IsLocallyCollared f)
    (hf : Injective f) : IsCollared f := by
  have hfc := h.continuous
  have : T2Space N := .of_injective_continuous hf hfc
  choose U hUo hxU c hc hcf using isLocallyCollared_iff.1 h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    fun x _ => mem_iUnion.2 ⟨x, hxU x⟩
  let V : Fin t.card → Set N := fun i => U (t.equivFin.symm i)
  have hV : univ ⊆ ⋃ i, V i := by
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion.2 ⟨t.equivFin ⟨x, hxt⟩, by simpa [V] using hyx⟩
  obtain ⟨φ, hφU, hφ1, hφ01, -⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun i => hUo _) isCompact_univ hV
  -- Push along the local collars one at a time, by a quarter of the partition of unity.
  have key : ∀ s : Finset (Fin t.card), ∃ G : extended f ≃ₜ extended f,
      PushesBy f G fun x => ∑ i ∈ s, φ i x / 4 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Homeomorph.refl _, fun x t h _ => by simp⟩
    | insert i s hi ih =>
      obtain ⟨G, hG⟩ := ih
      obtain ⟨H, hH⟩ := exists_pushesBy hf hfc (hc _) (hcf _) ((φ i).continuous.div_const 4)
        (fun x => by linarith [(hφ01 i x).1]) (fun x => by linarith [(hφ01 i x).2])
        ((tsupport_comp_subset (g := fun r : ℝ => r / 4) (zero_div 4) (φ i)).trans (hφU i))
      refine ⟨G.trans H, ?_⟩
      convert hG.trans hH (fun x => by linarith [(hφ01 i x).1]) using 1
      ext x
      rw [Finset.sum_insert hi, Pi.add_apply, add_comm]
  obtain ⟨G, hG⟩ := key Finset.univ
  refine isCollared_of_pushesBy (hfc.isClosedEmbedding hf).isEmbedding (G := G) ?_
  convert hG using 1
  ext x
  rw [← Finset.sum_div, ← Finset.sum_apply, hφ1 (mem_univ x), Pi.one_apply]

/-- A map from a compact space to a Hausdorff space is collared exactly when it is injective and
locally collared. -/
theorem isCollared_iff_injective_and_isLocallyCollared [CompactSpace N] [T2Space M] :
    IsCollared f ↔ Injective f ∧ IsLocallyCollared f :=
  ⟨fun h => ⟨h.isEmbedding.injective, h.isLocallyCollared⟩, fun h => h.2.isCollared h.1⟩

end TauCeti
