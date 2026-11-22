/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Functions on the additive circle lifted from a fundamental interval

Records range, injectivity, boundary agreement, and frontier bounds for `AddCircle.liftIco p a f`
and `AddCircle.equivIco T c` on half-open arcs `[a, b) ⊆ [c, c + T)`:

* `AddCircle.liftIco_coe_apply_of_mem_Icc`: if `f a = f (a + p)`, the lift agrees with `f` on
  `[a, a + p]`.
* `AddCircle.range_liftIco`: the range of the lift is `f '' Ico a (a + p)`.
* `AddCircle.injective_liftIco_iff`: the lift is injective iff `f` is injective on `[a, a + p)`.
* `AddCircle.frontier_preimage_equivIco_Ico_subset`: `frontier (equivIco ⁻¹' Ico a b) ⊆ {a, b}`.
-/

public section

open Function Set

namespace AddCircle

variable {𝕜 B : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  {p a : 𝕜} [hp : Fact (0 < p)] {f : 𝕜 → B}

/-- If `f a = f (a + p)`, the lift of `f` to `AddCircle p` agrees with `f` on the closed interval
`[a, a + p]`. -/
theorem liftIco_coe_apply_of_mem_Icc (hf : f a = f (a + p)) {x : 𝕜} (hx : x ∈ Icc a (a + p)) :
    liftIco p a f x = f x := by
  rcases hx.2.lt_or_eq with h | rfl
  · exact liftIco_coe_apply ⟨hx.1, h⟩
  · rw [← liftIoc_eq_liftIco hf]
    exact liftIoc_coe_apply ⟨lt_add_of_pos_right a hp.out, le_rfl⟩

/-- The range of the lift of `f` to `AddCircle p` is the image of `[a, a + p)` under `f`. -/
@[simp] theorem range_liftIco : range (liftIco p a f) = f '' Ico a (a + p) := by
  rw [← image_univ, ← coe_image_Ico_eq p a, image_image]
  exact image_congr fun _ hx ↦ liftIco_coe_apply hx

/-- The lift of `f` to `AddCircle p` is injective exactly when `f` is injective on the
fundamental interval `[a, a + p)`. -/
@[simp] theorem injective_liftIco_iff : Injective (liftIco p a f) ↔ InjOn f (Ico a (a + p)) := by
  exact ((equivIco p a).injective_comp _).trans Set.injOn_iff_injective.symm

/-- For `c ≤ a` and `b ≤ c + T`, the frontier of the preimage of `[a, b)` under `equivIco T c`
is contained in `{(a : AddCircle T), (b : AddCircle T)}`. -/
theorem frontier_preimage_equivIco_Ico_subset {T c a b : ℝ} [Fact (0 < T)] (hc : c ≤ a)
    (hb : b ≤ c + T) : frontier ((fun θ : AddCircle T ↦ (equivIco T c θ : ℝ)) ⁻¹' Ico a b) ⊆
      {(a : AddCircle T), (b : AddCircle T)} := by
  set E : Set (AddCircle T) := (fun θ : AddCircle T ↦ (equivIco T c θ : ℝ)) ⁻¹' Ico a b
  have hE : E = ((↑) : ℝ → AddCircle T) '' Ico a b := by
    ext x; refine ⟨fun hx ↦ ⟨equivIco T c x, hx, by simp⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩; simpa [E, equivIco_coe_of_mem ⟨hc.trans hy.1, hy.2.trans_le hb⟩] using hy
  have hcl : closure E ⊆ ((↑) : ℝ → AddCircle T) '' Icc a b := by
    have : T3Space (Quotient (QuotientAddGroup.leftRel (AddSubgroup.zmultiples T))) :=
      @QuotientAddGroup.instT3Space _ _ _ _ _ _
        (AddSubgroup.zmultiples T).isClosed_of_discreteTopology
    rw [hE]; exact closure_minimal (image_mono Ico_subset_Icc_self)
      (isCompact_Icc.image continuous_quotient_mk').isClosed
  have hint : ((↑) : ℝ → AddCircle T) '' Ioo a b ⊆ interior E := by
    rw [hE]; exact interior_maximal (image_mono Ioo_subset_Ico_self)
      (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
  intro x hx; obtain ⟨y, hy, rfl⟩ := hcl hx.1
  have hy_not : y ∉ Ioo a b := fun hyo ↦ hx.2 (hint ⟨y, hyo, rfl⟩)
  rcases eq_or_lt_of_le hy.1 with rfl | hlt
  · simp
  · simp [le_antisymm hy.2 (not_lt.mp fun h ↦ hy_not ⟨hlt, h⟩)]

end AddCircle
