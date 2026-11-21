/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs
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
  · rw [← liftIoc_eq_liftIco hf]; exact liftIoc_coe_apply ⟨lt_add_of_pos_right a hp.out, le_rfl⟩

/-- The range of the lift of `f` to `AddCircle p` is the image of `[a, a + p)` under `f`. -/
@[simp] theorem range_liftIco : range (liftIco p a f) = f '' Ico a (a + p) := by
  rw [← image_univ, ← coe_image_Ico_eq p a, image_image]
  exact image_congr fun _ hx ↦ liftIco_coe_apply hx

/-- The lift of `f` to `AddCircle p` is injective exactly when `f` is injective on the
fundamental interval `[a, a + p)`. -/
@[simp] theorem injective_liftIco_iff : Injective (liftIco p a f) ↔ InjOn f (Ico a (a + p)) :=
  ((equivIco p a).injective_comp _).trans Set.injOn_iff_injective.symm

/-- For `c ≤ a ≤ b ≤ c + T`, the frontier of the chart preimage of `[a, b)` in `AddCircle T` is
contained in `{(a : AddCircle T), (b : AddCircle T)}`. -/
theorem frontier_preimage_equivIco_Ico_subset {T c a b : ℝ} [Fact (0 < T)] (hc : c ≤ a)
    (hab : a ≤ b) (hb : b ≤ c + T) :
    frontier ((fun θ : AddCircle T ↦ (equivIco T c θ : ℝ)) ⁻¹' Ico a b) ⊆
      {(a : AddCircle T), (b : AddCircle T)} := by
  set E : Set (AddCircle T) := (fun θ : AddCircle T ↦ (equivIco T c θ : ℝ)) ⁻¹' Ico a b
  intro x hx; by_contra hnot
  obtain ⟨hxa, hxb⟩ := not_or.mp (by simpa [mem_insert_iff, mem_singleton_iff] using hnot)
  set t : ℝ := (equivIco T c x : ℝ); obtain ⟨ht0, ht1⟩ := (equivIco T c x).2
  have hxt : (t : AddCircle T) = x := by simp [t]
  have himg_open (u v : ℝ) : IsOpen (((↑) : ℝ → AddCircle T) '' Ioo u v) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hmem {y : ℝ} (hy0 : c ≤ y) (hy1 : y < c + T) : (y : AddCircle T) ∈ E ↔ y ∈ Ico a b := by
    simp only [E, Set.mem_preimage, equivIco_coe_of_mem ⟨hy0, hy1⟩]
  have hdisj (u v : ℝ) (hxU : x ∈ ((↑) : ℝ → AddCircle T) '' Ioo u v)
      (hd : ∀ y ∈ Ioo u v, (y : AddCircle T) ∉ E) : False :=
    let ⟨_, ⟨y, hy, rfl⟩, hyE⟩ := mem_closure_iff.mp hx.1 _ (himg_open u v) hxU; hd y hy hyE
  by_cases hmem_ab : a < t ∧ t < b
  · exact hx.2 (mem_interior.mpr ⟨((↑) : ℝ → AddCircle T) '' Ioo a b, fun _ ⟨y, hy, hy'⟩ ↦
      hy' ▸ (hmem (hc.trans hy.1.le) (hy.2.trans_le hb)).mpr ⟨hy.1.le, hy.2⟩,
      himg_open a b, ⟨t, hmem_ab, hxt⟩⟩)
  · by_cases htlta : t < a
    · by_cases htpos : c < t
      · exact hdisj c a ⟨t, ⟨htpos, htlta⟩, hxt⟩ fun y hy hyE ↦ by
          linarith [hy.2, ((hmem hy.1.le (by linarith [hy.2])).mp hyE).1]
      · have ht_eq : t = c := le_antisymm (not_lt.mp htpos) ht0
        have hb_lt : b < c + T := lt_of_le_of_ne hb fun hb1 ↦
          hxb (by rw [← hxt, ht_eq, hb1, coe_add, coe_period, add_zero])
        refine hdisj (b - T) a ⟨c, ⟨by linarith, htlta.trans_le' ht0⟩, by simpa [ht_eq] using hxt⟩
          fun y hy hyE ↦ ?_
        by_cases hyc : c ≤ y
        · linarith [hy.2, ((hmem hyc (by linarith [hy.2])).mp hyE).1]
        · rw [(by simp : (y : AddCircle T) = ((y + T : ℝ) : AddCircle T)),
            hmem (by linarith [hy.1]) (by linarith)] at hyE; linarith [hy.1, hyE.2]
    · have hbt : b < t := lt_of_le_of_ne (not_lt.mp fun hlt ↦
        hmem_ab ⟨lt_of_le_of_ne (not_lt.mp htlta) fun h ↦ hxa (by rw [← hxt, h.symm]), hlt⟩)
        fun h ↦ hxb (by rw [← hxt, h])
      exact hdisj b (c + T) ⟨t, ⟨hbt, ht1⟩, hxt⟩ fun y hy hyE ↦ by
        linarith [hy.1, ((hmem (by linarith [hy.1]) hy.2).mp hyE).2]

end AddCircle
