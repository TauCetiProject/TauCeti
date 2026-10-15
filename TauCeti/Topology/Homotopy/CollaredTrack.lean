/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.LocalAtTarget

/-!
# Collared tracks

A *concordance* between two embeddings `f g : M → N` is an embedding of `M × [0, 1]` into
`N × [0, 1]` restricting to `f` and `g` on the two ends. To avoid manifolds with boundary, Tau Ceti
records a concordance in *collared form*: as a map `F : M × ℝ → N × ℝ` which is the product
`f × id` for all times `t ≤ ε` and the product `g × id` for all times `t ≥ 1 - ε`, for some positive
collar width `ε`, and which maps the open slab `M × (0, 1)` into the open slab `N × (0, 1)`. Two
such tracks with a common middle embedding can be run one after the other, and the uniform collars
are what make the seam invisible: on a whole open slab around it both tracks are the same product
`g × id`.

This file isolates these end conditions on the bare map, `TauCeti.IsCollaredTrack f g F`, and
develops everything about a concordance that does not depend on the regularity asked of its
track — smooth, locally flat or merely topological. That is: the end conditions imply that the
track is the appropriate product for all `t ≤ 0` and all `t ≥ 1` and that it moves no time level
across `0` or `1`; the product `f × id` is a track from `f` to `f`; a track can be pushed forward
along a map of the target or pulled back along a map of the source; time can be reflected
(`TauCeti.reverseTime`), giving a track from `g` to `f`; and two tracks can be stacked
(`TauCeti.stack`), the first run at triple speed on `[0, 1/3]` and the second at triple speed on
`[2/3, 1]`, giving a track from `f` to `h`. The stacked track is glued from two open slabs, and it
is an embedding as soon as the two tracks are, because the pieces are embeddings and the seam lies
in the product region.

## Main definitions

* `TauCeti.IsCollaredTrack f g F`: the end conditions of a collared track from `f` to `g`.
* `TauCeti.conjTime F a b`: the conjugate of `F` by the affine change of time `t ↦ a * t + b`.
* `TauCeti.reverseTime F`: the track run backwards, time being reflected in `1 / 2`.
* `TauCeti.stack F G`: the first track at triple speed until time `1 / 2`, then the second.

## Main results

* `TauCeti.IsCollaredTrack.snd_apply_lt_iff`, `TauCeti.IsCollaredTrack.lt_snd_apply_iff` and
  `TauCeti.IsCollaredTrack.snd_apply_mem_Ioo_iff`: a collared track preserves the comparison of
  the time coordinate with any level outside `(0, 1)`.
* `TauCeti.isCollaredTrack_prodMap_id`, `TauCeti.IsCollaredTrack.reverseTime` and
  `TauCeti.IsCollaredTrack.stack`: the constant, reversed and stacked tracks are collared tracks.
* `TauCeti.IsCollaredTrack.isEmbedding_stack`: the stack of two collared tracks which are
  topological embeddings is a topological embedding.

## References

* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Topology

variable {M M' N P : Type*}

/-- A map `F : M × ℝ → N × ℝ` is a **collared track** from `f` to `g` when it is the product
`f × id` for all times `t ≤ ε` and the product `g × id` for all times `t ≥ 1 - ε`, for some positive
collar width `ε`, and maps the open slab `M × (0, 1)` into the open slab `N × (0, 1)`. These are the
end conditions of a concordance in collared form, whatever regularity is asked of the track. -/
structure IsCollaredTrack (f g : M → N) (F : M × ℝ → N × ℝ) : Prop where
  /-- The track is the product of `f` with the identity on a collar of the initial end. -/
  exists_pos_apply_eq_left : ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), t ≤ ε → F (x, t) = (f x, t)
  /-- The track is the product of `g` with the identity on a collar of the final end. -/
  exists_pos_apply_eq_right : ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), 1 - ε ≤ t → F (x, t) = (g x, t)
  /-- The track maps the open slab `M × (0, 1)` into the open slab `N × (0, 1)`. -/
  snd_apply_mem_Ioo (x : M) (t : ℝ) (ht : t ∈ Ioo 0 1) : (F (x, t)).2 ∈ Ioo 0 1

namespace IsCollaredTrack

variable {f g h : M → N} {F G : M × ℝ → N × ℝ}

/-- A collared track is the product of its initial map with the identity for `t ≤ 0`. -/
theorem apply_of_nonpos (hF : IsCollaredTrack f g F) (x : M) {t : ℝ} (ht : t ≤ 0) :
    F (x, t) = (f x, t) := by
  obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_left
  exact hF x t (ht.trans hε.le)

/-- A collared track is the product of its final map with the identity for `1 ≤ t`. -/
theorem apply_of_one_le (hF : IsCollaredTrack f g F) (x : M) {t : ℝ} (ht : 1 ≤ t) :
    F (x, t) = (g x, t) := by
  obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_right
  exact hF x t (by linarith)

/-- At time `0` a collared track is its initial map. -/
theorem apply_zero (hF : IsCollaredTrack f g F) (x : M) : F (x, 0) = (f x, 0) :=
  hF.apply_of_nonpos x le_rfl

/-- At time `1` a collared track is its final map. -/
theorem apply_one (hF : IsCollaredTrack f g F) (x : M) : F (x, 1) = (g x, 1) :=
  hF.apply_of_one_le x le_rfl

/-- A collared track moves no time outside the open interval `(0, 1)` and keeps times inside it,
so it preserves the comparison of time with any level `c ∉ (0, 1)`. -/
theorem snd_apply_lt_iff (hF : IsCollaredTrack f g F) (x : M) {t c : ℝ} (hc : c ∉ Ioo 0 1) :
    (F (x, t)).2 < c ↔ t < c := by
  rcases le_or_gt t 0 with ht | ht
  · simp [hF.apply_of_nonpos x ht]
  rcases le_or_gt 1 t with ht' | ht'
  · simp [hF.apply_of_one_le x ht']
  have hmem : (F (x, t)).2 ∈ Ioo 0 1 := hF.snd_apply_mem_Ioo x t ⟨ht, ht'⟩
  simp only [mem_Ioo, not_and_or, not_lt] at hc hmem
  constructor <;> intro <;> rcases hc with hc | hc <;> linarith

/-- A collared track preserves the comparison of time with any level `c ∉ (0, 1)` from below. -/
theorem lt_snd_apply_iff (hF : IsCollaredTrack f g F) (x : M) {t c : ℝ} (hc : c ∉ Ioo 0 1) :
    c < (F (x, t)).2 ↔ c < t := by
  rcases le_or_gt t 0 with ht | ht
  · simp [hF.apply_of_nonpos x ht]
  rcases le_or_gt 1 t with ht' | ht'
  · simp [hF.apply_of_one_le x ht']
  have hmem : (F (x, t)).2 ∈ Ioo 0 1 := hF.snd_apply_mem_Ioo x t ⟨ht, ht'⟩
  simp only [mem_Ioo, not_and_or, not_lt] at hc hmem
  constructor <;> intro <;> rcases hc with hc | hc <;> linarith

/-- A collared track maps `M × (0, 1)` into `N × (0, 1)` and nothing else there. -/
theorem snd_apply_mem_Ioo_iff (hF : IsCollaredTrack f g F) (x : M) {t : ℝ} :
    (F (x, t)).2 ∈ Ioo 0 1 ↔ t ∈ Ioo 0 1 := by
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  simp only [mem_Ioo, hF.lt_snd_apply_iff x h0, hF.snd_apply_lt_iff x h1]

/-- Pushing a collared track from `f` to `g` forward along a map `e` of the target gives a
collared track from `e ∘ f` to `e ∘ g`. -/
theorem prodMap_id_comp (hF : IsCollaredTrack f g F) (e : N → P) :
    IsCollaredTrack (e ∘ f) (e ∘ g) (Prod.map e id ∘ F) where
  exists_pos_apply_eq_left := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_left
    exact ⟨ε, hε, fun x t ht => by simp [hF x t ht]⟩
  exists_pos_apply_eq_right := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_right
    exact ⟨ε, hε, fun x t ht => by simp [hF x t ht]⟩
  snd_apply_mem_Ioo x t ht := by simpa using hF.snd_apply_mem_Ioo x t ht

/-- Pulling a collared track from `f` to `g` back along a map `e` of the source gives a collared
track from `f ∘ e` to `g ∘ e`. -/
theorem comp_prodMap_id (hF : IsCollaredTrack f g F) (e : M' → M) :
    IsCollaredTrack (f ∘ e) (g ∘ e) (F ∘ Prod.map e id) where
  exists_pos_apply_eq_left := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_left
    exact ⟨ε, hε, fun x t ht => by simp [hF (e x) t ht]⟩
  exists_pos_apply_eq_right := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_right
    exact ⟨ε, hε, fun x t ht => by simp [hF (e x) t ht]⟩
  snd_apply_mem_Ioo x t ht := by simpa using hF.snd_apply_mem_Ioo (e x) t ht

end IsCollaredTrack

/-- The product `f × id` is a collared track from `f` to itself. -/
theorem isCollaredTrack_prodMap_id (f : M → N) : IsCollaredTrack f f (Prod.map f id) where
  exists_pos_apply_eq_left := ⟨1, one_pos, fun _ _ _ => by simp⟩
  exists_pos_apply_eq_right := ⟨1, one_pos, fun _ _ _ => by simp⟩
  snd_apply_mem_Ioo _ _ ht := by simpa using ht

/-! ### Affine changes of time -/

/-- The conjugate of a map `F : M × ℝ → N × ℝ` by the affine change of time `t ↦ a * t + b`: run
`F` at the time `a * t + b` and read the resulting time back through the inverse change. -/
def conjTime (F : M × ℝ → N × ℝ) (a b : ℝ) (p : M × ℝ) : N × ℝ :=
  ((F (p.1, a * p.2 + b)).1, ((F (p.1, a * p.2 + b)).2 - b) / a)

@[simp]
theorem conjTime_apply (F : M × ℝ → N × ℝ) (a b : ℝ) (x : M) (t : ℝ) :
    conjTime F a b (x, t) = ((F (x, a * t + b)).1, ((F (x, a * t + b)).2 - b) / a) :=
  (rfl)

/-- For `a ≠ 0` the affine change of time is a homeomorphism of the line, and the conjugate track
is the conjugate of `F` by the corresponding self-homeomorphisms of `M × ℝ` and `N × ℝ`. -/
theorem conjTime_eq_comp [TopologicalSpace M] [TopologicalSpace N] (F : M × ℝ → N × ℝ) {a : ℝ}
    (b : ℝ) (ha : a ≠ 0) :
    conjTime F a b = ((Homeomorph.refl N).prodCongr (affineHomeomorph a b ha).symm) ∘ F ∘
      ((Homeomorph.refl M).prodCongr (affineHomeomorph a b ha)) := by
  funext ⟨x, t⟩
  refine Prod.ext ?_ ?_ <;> simp [conjTime]

/-- Reversing a track: reflect time in `1 / 2`, so that the track is run backwards. -/
def reverseTime (F : M × ℝ → N × ℝ) : M × ℝ → N × ℝ :=
  conjTime F (-1) 1

/-- Reversing time is conjugation by the reflection `t ↦ -t + 1`. -/
theorem reverseTime_def (F : M × ℝ → N × ℝ) : reverseTime F = conjTime F (-1) 1 :=
  (rfl)

@[simp]
theorem reverseTime_apply (F : M × ℝ → N × ℝ) (x : M) (t : ℝ) :
    reverseTime F (x, t) = ((F (x, 1 - t)).1, 1 - (F (x, 1 - t)).2) := by
  have ht : -1 * t + 1 = 1 - t := by ring
  rw [reverseTime, conjTime_apply, ht, div_neg, div_one, neg_sub]

/-- Reversing a track twice gives it back. -/
@[simp]
theorem reverseTime_reverseTime (F : M × ℝ → N × ℝ) : reverseTime (reverseTime F) = F := by
  funext ⟨x, t⟩
  simp

/-- The reversed track of a collared track from `f` to `g` is a collared track from `g` to `f`. -/
theorem IsCollaredTrack.reverseTime {f g : M → N} {F : M × ℝ → N × ℝ}
    (hF : IsCollaredTrack f g F) : IsCollaredTrack g f (reverseTime F) where
  exists_pos_apply_eq_left := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_right
    refine ⟨ε, hε, fun x t ht => ?_⟩
    rw [reverseTime_apply, hF x (1 - t) (by linarith)]
    simp
  exists_pos_apply_eq_right := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_left
    refine ⟨ε, hε, fun x t ht => ?_⟩
    rw [reverseTime_apply, hF x (1 - t) (by linarith)]
    simp
  snd_apply_mem_Ioo x t ht := by
    rw [reverseTime_apply]
    have hrev : 1 - t ∈ Ioo 0 1 := by
      simp only [mem_Ioo] at ht ⊢
      constructor <;> linarith
    have hmem := (hF.snd_apply_mem_Ioo_iff x).2 hrev
    simp only [mem_Ioo] at hmem ⊢
    constructor <;> linarith

/-! ### Stacking tracks -/

/-- The stack of two tracks: the first track run at triple speed until time `1 / 2`, the second
track run at triple speed afterwards. For collared tracks with a common middle map `g` both are
the product `g × id` on the slab `[1/3, 2/3]`, so the seam at `1 / 2` is invisible. -/
def stack (F G : M × ℝ → N × ℝ) (p : M × ℝ) : N × ℝ :=
  if p.2 ≤ 1 / 2 then conjTime F 3 0 p else conjTime G 3 (-2) p

/-- Until time `1 / 2` the stacked track runs the first track at triple speed. -/
theorem stack_apply_of_le (F G : M × ℝ → N × ℝ) (x : M) {t : ℝ} (ht : t ≤ 1 / 2) :
    stack F G (x, t) = ((F (x, 3 * t)).1, (F (x, 3 * t)).2 / 3) := by
  simp only [stack, ht, ↓reduceIte, conjTime_apply, add_zero, sub_zero]

/-- After time `1 / 2` the stacked track runs the second track at triple speed. -/
theorem stack_apply_of_lt (F G : M × ℝ → N × ℝ) (x : M) {t : ℝ} (ht : 1 / 2 < t) :
    stack F G (x, t) = ((G (x, 3 * t - 2)).1, ((G (x, 3 * t - 2)).2 + 2) / 3) := by
  simp only [stack, not_le.2 ht, ↓reduceIte, conjTime_apply, sub_neg_eq_add, ← sub_eq_add_neg]

namespace IsCollaredTrack

variable {f g h : M → N} {F G : M × ℝ → N × ℝ}

/-- Before time `2 / 3` the stack of two collared tracks is the first track at triple speed. -/
theorem stack_eqOn_lower (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G) :
    EqOn (stack F G) (conjTime F 3 0) {p | p.2 < 2 / 3} := by
  rintro ⟨x, t⟩ (ht : t < 2 / 3)
  rw [conjTime_apply, add_zero, sub_zero]
  rcases le_or_gt t (1 / 2) with ht' | ht'
  · rw [stack_apply_of_le F G x ht']
  · rw [stack_apply_of_lt F G x ht', hF.apply_of_one_le x (by linarith),
      hG.apply_of_nonpos x (by linarith)]
    refine Prod.ext rfl ?_
    simp only
    ring

/-- After time `1 / 3` the stack of two collared tracks is the second track at triple speed. -/
theorem stack_eqOn_upper (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G) :
    EqOn (stack F G) (conjTime G 3 (-2)) {p | 1 / 3 < p.2} := by
  rintro ⟨x, t⟩ (ht : 1 / 3 < t)
  rw [conjTime_apply, sub_neg_eq_add, ← sub_eq_add_neg]
  rcases le_or_gt t (1 / 2) with ht' | ht'
  · rw [stack_apply_of_le F G x ht', hF.apply_of_one_le x (by linarith),
      hG.apply_of_nonpos x (by linarith)]
    refine Prod.ext rfl ?_
    simp only
    ring
  · rw [stack_apply_of_lt F G x ht']

/-- The stacked track preserves the comparison of time with the level `2 / 3`. -/
theorem snd_stack_lt_iff (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G) (p : M × ℝ) :
    (stack F G p).2 < 2 / 3 ↔ p.2 < 2 / 3 := by
  obtain ⟨x, t⟩ := p
  have h2 : (2 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.2]
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
  rcases le_or_gt t (1 / 2) with ht | ht
  · rw [stack_apply_of_le F G x ht]
    have key := hF.snd_apply_lt_iff x (t := 3 * t) h2
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]
  · rw [stack_apply_of_lt F G x ht]
    have key := hG.snd_apply_lt_iff x (t := 3 * t - 2) h0
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]

/-- The stacked track preserves the comparison of time with the level `1 / 3`. -/
theorem lt_snd_stack_iff (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G) (p : M × ℝ) :
    1 / 3 < (stack F G p).2 ↔ 1 / 3 < p.2 := by
  obtain ⟨x, t⟩ := p
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  have hm1 : (-1 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.1]
  rcases le_or_gt t (1 / 2) with ht | ht
  · rw [stack_apply_of_le F G x ht]
    have key := hF.lt_snd_apply_iff x (t := 3 * t) h1
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]
  · rw [stack_apply_of_lt F G x ht]
    have key := hG.lt_snd_apply_iff x (t := 3 * t - 2) hm1
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro _; linarith [key.2 (by linarith)]

/-- The stack of a collared track from `f` to `g` and one from `g` to `h` is a collared track from
`f` to `h`. -/
theorem stack (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G) :
    IsCollaredTrack f h (TauCeti.stack F G) where
  exists_pos_apply_eq_left := by
    obtain ⟨ε, hε, hF⟩ := hF.exists_pos_apply_eq_left
    refine ⟨min (ε / 3) (1 / 4), lt_min (by linarith) (by norm_num), fun x t ht => ?_⟩
    have hδε : min (ε / 3) (1 / 4) ≤ ε / 3 := min_le_left _ _
    have hδ : min (ε / 3) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    rw [stack_apply_of_le F G x (by linarith), hF x (3 * t) (by linarith)]
    refine Prod.ext rfl ?_
    simp only
    ring
  exists_pos_apply_eq_right := by
    obtain ⟨ε, hε, hG⟩ := hG.exists_pos_apply_eq_right
    refine ⟨min (ε / 3) (1 / 4), lt_min (by linarith) (by norm_num), fun x t ht => ?_⟩
    have hδε : min (ε / 3) (1 / 4) ≤ ε / 3 := min_le_left _ _
    have hδ : min (ε / 3) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    rw [stack_apply_of_lt F G x (by linarith), hG x (3 * t - 2) (by linarith)]
    refine Prod.ext rfl ?_
    simp only
    ring
  snd_apply_mem_Ioo x t ht := by
    have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
    have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
    have h3 : (3 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.2]
    have hm2 : (-2 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.1]
    simp only [mem_Ioo] at ht ⊢
    rcases le_or_gt t (1 / 2) with ht' | ht'
    · rw [stack_apply_of_le F G x ht']
      have hlo := hF.lt_snd_apply_iff x (t := 3 * t) h0
      have hhi := hF.snd_apply_lt_iff x (t := 3 * t) h3
      constructor <;> linarith [hlo.2 (by linarith), hhi.2 (by linarith)]
    · rw [stack_apply_of_lt F G x ht']
      have hlo := hG.lt_snd_apply_iff x (t := 3 * t - 2) hm2
      have hhi := hG.snd_apply_lt_iff x (t := 3 * t - 2) h1
      constructor <;> linarith [hlo.2 (by linarith), hhi.2 (by linarith)]

variable [TopologicalSpace M] [TopologicalSpace N]

/-- The stack of two collared tracks which are topological embeddings is a topological embedding:
the two open slabs `{t < 2/3}` and `{1/3 < t}` cover `N × ℝ`, over each the stacked track is one
of the two rescaled tracks, and both of those are embeddings. -/
theorem isEmbedding_stack (hF : IsCollaredTrack f g F) (hG : IsCollaredTrack g h G)
    (hF' : IsEmbedding F) (hG' : IsEmbedding G) : IsEmbedding (TauCeti.stack F G) := by
  have hlow : IsOpen {p : M × ℝ | p.2 < 2 / 3} := isOpen_lt continuous_snd continuous_const
  have hup : IsOpen {p : M × ℝ | 1 / 3 < p.2} := isOpen_lt continuous_const continuous_snd
  have hF3 : IsEmbedding (conjTime F 3 0) := by
    rw [conjTime_eq_comp F 0 (by norm_num)]
    exact (Homeomorph.isEmbedding _).comp (hF'.comp (Homeomorph.isEmbedding _))
  have hG3 : IsEmbedding (conjTime G 3 (-2)) := by
    rw [conjTime_eq_comp G (-2) (by norm_num)]
    exact (Homeomorph.isEmbedding _).comp (hG'.comp (Homeomorph.isEmbedding _))
  have hcont : Continuous (TauCeti.stack F G) := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rcases lt_or_ge p.2 (2 / 3) with hp | hp
    · exact hF3.continuous.continuousAt.congr
        (eventuallyEq_of_mem (hlow.mem_nhds hp) (hF.stack_eqOn_lower hG).symm)
    · exact hG3.continuous.continuousAt.congr
        (eventuallyEq_of_mem (hup.mem_nhds (lt_of_lt_of_le (by norm_num) hp))
          (hF.stack_eqOn_upper hG).symm)
  -- The two open slabs `{s < 2 / 3}` and `{1 / 3 < s}` cover `N × ℝ`; over each the stacked
  -- track is one of the two rescaled tracks, restricted to the matching slab of `M × ℝ`.
  let U : Bool → TopologicalSpace.Opens (N × ℝ) := fun b => bif b
    then ⟨{q | 1 / 3 < q.2}, isOpen_lt continuous_const continuous_snd⟩
    else ⟨{q | q.2 < 2 / 3}, isOpen_lt continuous_snd continuous_const⟩
  let W : Bool → Set (M × ℝ) := fun b => bif b then {p | 1 / 3 < p.2} else {p | p.2 < 2 / 3}
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range (TauCeti.stack F G) hcont
    U ?_ (fun b => W b) (fun b => Subtype.val) (fun b => continuous_subtype_val) ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    rcases lt_or_ge (TauCeti.stack F G p).2 (2 / 3) with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, (by linarith : 1 / 3 < (TauCeti.stack F G p).2)⟩
  · rintro (_ | _) p hp
    · exact ⟨⟨p, (hF.snd_stack_lt_iff hG p).1 hp⟩, rfl⟩
    · exact ⟨⟨p, (hF.lt_snd_stack_iff hG p).1 hp⟩, rfl⟩
  · rintro (_ | _)
    · have heq : TauCeti.stack F G ∘ (Subtype.val : W false → M × ℝ) =
          conjTime F 3 0 ∘ Subtype.val :=
        funext fun p => hF.stack_eqOn_lower hG p.2
      rw [heq]
      exact hF3.comp IsEmbedding.subtypeVal
    · have heq : TauCeti.stack F G ∘ (Subtype.val : W true → M × ℝ) =
          conjTime G 3 (-2) ∘ Subtype.val :=
        funext fun p => hF.stack_eqOn_upper hG p.2
      rw [heq]
      exact hG3.comp IsEmbedding.subtypeVal

end IsCollaredTrack

end TauCeti
