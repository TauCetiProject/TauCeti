/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sublevels of real functions

If a real function has a unique global minimum and one compact sublevel strictly above it,
then sufficiently small sublevels lie in any prescribed open neighbourhood of the minimum
(`TauCeti.exists_pos_sublevel_subset_of_unique_min`).
This allows local descriptions near the minimum to describe whole sublevels. Continuity is
needed only on the one compact sublevel, not on the entire space.

If a continuous motion of the space lowers `f` at unit speed through the band `a ≤ f ≤ b`, then
following it until the level `a` is reached retracts the sublevel `{f ≤ b}` onto `{f ≤ a}`, by a
homotopy fixing `{f ≤ a}` pointwise (`TauCeti.exists_sublevelDeformation_of_apply_eq_sub`); here
`TauCeti.sublevelInclusion` is the inclusion of `{f ≤ a}` into `{f ≤ b}`. This
is the topological half of the deformation of sublevels across a band without critical points,
where the motion is the flow of a vector field `X` with `df(X) = -1` on the band.

If the motion is a flow along whose lines `f` never increases, then its time-`(b - a)` map carries
`{f ≤ b}` exactly onto `{f ≤ a}` (`Flow.apply_le_iff_of_apply_eq_sub`), and, when `f`
strictly decreases along flow lines starting on the level `a`, the level `f⁻¹(b)` exactly onto
`f⁻¹(a)` (`Flow.apply_eq_iff_of_apply_eq_sub`). This is the topological half of the
homeomorphism between the sublevels on either side of a band without critical points.

Under the same hypotheses the band `f⁻¹[a, b]` is homeomorphic to `f⁻¹(a) × [a, b]` by a
homeomorphism preserving the value of `f` (`Flow.bandHomeomorph`): a point of the band is sent to
the point where its flow line meets the level `a`, together with its value.
-/

public section

open Set

namespace TauCeti

/-- Small sublevels of a function with a unique global minimum lie in any open neighbourhood
of that minimum, provided one sublevel strictly above the minimum is compact and `f` is
continuous on it. -/
theorem exists_pos_sublevel_subset_of_unique_min {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} {a : ℝ}
    (hcompact : IsCompact {y | f y ≤ a}) (hf : ContinuousOn f {y | f y ≤ a})
    (ha : f x < a) (hmin : ∀ y, f y ≤ f x → y = x)
    {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ ε > 0, {y | f y ≤ f x + ε} ⊆ U := by
  by_cases hne : ({y | f y ≤ a} \ U).Nonempty
  · obtain ⟨z, hz, hzm⟩ := (hcompact.diff hU).exists_isMinOn hne
      (hf.mono sdiff_subset)
    have hxz : f x < f z := by
      by_contra! hle
      exact hz.2 (hmin z hle ▸ hx)
    let ε := min (a - f x) (f z - f x) / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, hε, fun y hy ↦ ?_⟩
    have hεa : ε ≤ (a - f x) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hεz : ε ≤ (f z - f x) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    by_contra hyU
    have hyK : y ∈ {y | f y ≤ a} \ U := ⟨by dsimp at hy ⊢; linarith, hyU⟩
    have hzy : f z ≤ f y := hzm hyK
    dsimp at hy
    linarith
  · refine ⟨(a - f x) / 2, by positivity, fun y hy ↦ ?_⟩
    by_contra hyU
    exact hne ⟨y, ⟨by dsimp at hy ⊢; linarith, hyU⟩⟩

/-- The inclusion `{f ≤ a} → {f ≤ b}` of sublevels of `f`, for `a ≤ b`. -/
def sublevelInclusion {X β : Type*} [TopologicalSpace X] [Preorder β] (f : X → β) (a b : β)
    (hab : a ≤ b) : C({x | f x ≤ a}, {x | f x ≤ b}) :=
  ContinuousMap.inclusion (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans hab)

@[simp]
theorem coe_sublevelInclusion_apply {X β : Type*} [TopologicalSpace X] [Preorder β] (f : X → β)
    {a b : β} (hab : a ≤ b) (x : {x | f x ≤ a}) : (sublevelInclusion f a b hab x : X) = x :=
  (rfl)

/-- **Deformation of sublevels along a unit-speed descent.** Let `φ t` be a continuous motion of
`X`, with `φ 0` the identity, which lowers `f` at unit speed through the band `a ≤ f ≤ b`: if
`f x ≤ b` and `f x - t ≥ a` with `t ≥ 0`, then `f (φ t x) = f x - t`. Moving each point of
`{f ≤ b}` until it reaches the level `a` is a retraction `r` of `{f ≤ b}` onto `{f ≤ a}`, and moving
it only part of the way is a homotopy from the inclusion of `r` to the identity fixing `{f ≤ a}`
pointwise. -/
theorem exists_sublevelDeformation_of_apply_eq_sub {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (φ : ℝ → X → X)
    (hφ : Continuous (Function.uncurry φ)) (hφ0 : ∀ x, φ 0 x = x)
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t) :
    ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
      (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((sublevelInclusion f a b hab).comp r)
        (ContinuousMap.id _) {x | f x ≤ a}) := by
  -- Each point of `{f ≤ b}` needs the time `τ x = max (f x - a) 0` to reach `{f ≤ a}`.
  set τ : X → ℝ := fun x ↦ max (f x - a) 0
  have hτ : Continuous τ := (hf.sub continuous_const).max continuous_const
  have hτ0 : ∀ x, f x ≤ a → τ x = 0 := fun x hx ↦ max_eq_right (by linarith)
  have hfφ : ∀ x, f x ≤ b → ∀ s : ℝ, 0 ≤ s → s ≤ 1 → f (φ (s * τ x) x) = f x - s * τ x := by
    intro x hx s hs0 hs1
    by_cases hxa : f x ≤ a
    · simp [hτ0 x hxa, hφ0]
    · have hτx : τ x = f x - a := max_eq_left (by linarith)
      refine hφf x _ (by rw [hτx]; nlinarith) ?_ hx
      rw [hτx]
      nlinarith
  have hra : ∀ x : {x | f x ≤ b}, φ (τ x.1) x.1 ∈ {x | f x ≤ a} := fun x ↦ by
    have h := hfφ x.1 x.2 1 zero_le_one le_rfl
    rw [one_mul] at h
    rw [mem_ofPred_eq, h]
    linarith [le_max_left (f x.1 - a) 0]
  obtain ⟨r, hr⟩ : ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}), ∀ x, (r x : X) = φ (τ x.1) x.1 :=
    ⟨⟨fun x ↦ ⟨φ (τ x.1) x.1, hra x⟩,
      (hφ.comp ((hτ.comp continuous_subtype_val).prodMk continuous_subtype_val)).subtype_mk _⟩,
      fun _ ↦ rfl⟩
  refine ⟨r, fun x ↦ Subtype.ext ?_, ⟨?_⟩⟩
  · simp [hr, hτ0 x.1 x.2, hφ0]
  have hHb : ∀ p : unitInterval × {x | f x ≤ b},
      φ ((1 - (p.1 : ℝ)) * τ p.2.1) p.2.1 ∈ {x | f x ≤ b} := fun p ↦ by
    have h := hfφ p.2.1 p.2.2 (1 - p.1) (by linarith [p.1.2.2]) (by linarith [p.1.2.1])
    have hb : f p.2.1 ≤ b := p.2.2
    have : 0 ≤ (1 - (p.1 : ℝ)) * τ p.2.1 := mul_nonneg (by linarith [p.1.2.2]) (le_max_right _ _)
    rw [mem_ofPred_eq, h]
    linarith
  have hx : Continuous fun p : unitInterval × {x | f x ≤ b} ↦ (p.2 : X) :=
    continuous_subtype_val.comp continuous_snd
  exact
    { toFun := fun p ↦ ⟨φ ((1 - (p.1 : ℝ)) * τ p.2.1) p.2.1, hHb p⟩
      continuous_toFun := (hφ.comp (((continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).mul (hτ.comp hx)).prodMk hx)).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext <| by simp [hr]
      map_one_left := fun x ↦ Subtype.ext <| by simp [hφ0]
      prop' := fun t x hx ↦ Subtype.ext <| by simp [hr, hτ0 x.1 hx, hφ0] }

end TauCeti

namespace Flow

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {a b : ℝ} (φ : Flow ℝ X)

/-- **Sublevels along a unit-speed descent.** Let `φ` be a flow along whose lines `f` never
increases in positive time, and which lowers `f` at unit speed through the band `a ≤ f ≤ b`. Then
the time-`(b - a)` map of `φ` carries a point into `{f ≤ a}` exactly when the point lies in
`{f ≤ b}`. -/
theorem apply_le_iff_of_apply_eq_sub (hf : Continuous f) (hab : a ≤ b)
    (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t) (x : X) :
    f (φ (b - a) x) ≤ a ↔ f x ≤ b := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  constructor
  · intro h
    by_contra! hb
    -- The flow line of `x` crosses the level `b` at a positive time `t₀ ≤ b - a`, and from there
    -- descends at unit speed for the remaining time `b - a - t₀`, staying strictly above `a`.
    obtain ⟨t₀, ⟨ht₀, ht₀'⟩, hft₀⟩ : ∃ t₀ ∈ Icc 0 (b - a), f (φ t₀ x) = b :=
      intermediate_value_Icc' hba
      (hf.comp (φ.continuous continuous_id continuous_const)).continuousOn
      ⟨h.trans hab, by simpa using hb.le⟩
    have ht₀pos : 0 < t₀ := by
      refine ht₀.lt_of_ne fun h0 ↦ ?_
      rw [← h0, Flow.map_zero_apply] at hft₀
      linarith
    have hft : f (φ (b - a - t₀) (φ t₀ x)) = f (φ t₀ x) - (b - a - t₀) :=
      hφf _ _ (by linarith) (by rw [hft₀]; linarith) hft₀.le
    rw [← Flow.map_add, sub_add_cancel] at hft
    linarith
  · intro hb
    rcases le_or_gt (f x) a with hxa | hxa
    · calc f (φ (b - a) x) ≤ f (φ 0 x) := hanti x (mem_Ici.2 le_rfl) hba hba
        _ ≤ a := by rwa [Flow.map_zero_apply]
    · have h1 := hφf x (f x - a) (by linarith) (by linarith) hb
      calc f (φ (b - a) x) ≤ f (φ (f x - a) x) :=
            hanti x (mem_Ici.2 (by linarith)) (mem_Ici.2 hba) (by linarith)
        _ = a := by rw [h1]; ring

/-- **Levels along a unit-speed descent.** Under the hypotheses of
`Flow.apply_le_iff_of_apply_eq_sub`, suppose moreover that `f` drops strictly below `a`
along the flow line of every point of the level `f⁻¹(a)`. Then the time-`(b - a)` map of `φ`
carries a point into `f⁻¹(a)` exactly when the point lies in `f⁻¹(b)`. -/
theorem apply_eq_iff_of_apply_eq_sub (hf : Continuous f) (hab : a ≤ b)
    (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)
    (hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a) (x : X) :
    f (φ (b - a) x) = a ↔ f x = b := by
  constructor
  · intro h
    have hb := (φ.apply_le_iff_of_apply_eq_sub hf hab hanti hφf x).1 h.le
    refine hb.eq_of_not_lt fun hb' ↦ ?_
    rcases lt_or_ge (f x) a with hxa | hxa
    · -- Below the level `a`, the flow line never rises back to `a`.
      have := hanti x (mem_Ici.2 le_rfl) (mem_Ici.2 (sub_nonneg.2 hab)) (sub_nonneg.2 hab)
      simp only [Flow.map_zero_apply] at this
      linarith
    · -- The flow line reaches the level `a` at time `f x - a < b - a`, and then drops below it.
      have h1 := hφf x (f x - a) (by linarith) (by linarith) hb
      have h2 := hφa (φ (f x - a) x) (b - f x) (by rw [h1]; ring) (by linarith)
      rw [← Flow.map_add, show b - f x + (f x - a) = b - a by ring] at h2
      linarith
  · intro h
    rw [hφf x (b - a) (sub_nonneg.2 hab) (by rw [h]; linarith) h.le, h]
    ring

/-- **Ascent from the lower level.** Under the hypotheses of `Flow.apply_eq_iff_of_apply_eq_sub`,
running the flow backwards for a time `t` from a point of the level `f⁻¹(a)` raises `f` at unit
speed through the band: if `f y = a`, `0 ≤ t` and `a + t ≤ b`, then `f (φ (-t) y) = a + t`. -/
theorem apply_neg_eq_add_of_apply_eq_sub (hf : Continuous f)
    (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)
    (hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a) {y : X} (hy : f y = a) {t : ℝ}
    (ht : 0 ≤ t) (htb : a + t ≤ b) : f (φ (-t) y) = a + t := by
  have hxy : φ t (φ (-t) y) = y := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hxa : a ≤ f (φ (-t) y) := by
    have h := hanti (φ (-t) y) (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
    simp only [Flow.map_zero_apply, hxy, hy] at h
    exact h
  rcases lt_trichotomy (f (φ (-t) y)) (a + t) with hlt | heq | hgt
  · -- The flow line of `φ (-t) y` reaches the level `a` before time `t`, and then drops below it.
    exfalso
    set s := f (φ (-t) y) - a
    have h1 := hφf (φ (-t) y) s (by linarith) (by linarith) (by linarith)
    have h2 := hφa (φ s (φ (-t) y)) (t - s) (by rw [h1]; ring) (by linarith)
    rw [← Flow.map_add, sub_add_cancel, hxy, hy] at h2
    exact lt_irrefl a h2
  · exact heq
  · -- Some earlier point `φ (-u) y` of the backward flow line lies on the level `a + t`; flowing
    -- down from it for time `t` overshoots the point `y` of the level `a`.
    exfalso
    obtain ⟨u, ⟨hu0, hut⟩, hfu⟩ : ∃ u ∈ Icc 0 t, f (φ (-u) y) = a + t :=
      intermediate_value_Icc ht
        (hf.comp (φ.continuous continuous_neg continuous_const)).continuousOn
        ⟨by simp [hy, ht], hgt.le⟩
    have hut' : u < t := hut.lt_of_ne fun h ↦ hgt.ne' (h ▸ hfu)
    have h1 := hφf (φ (-u) y) t ht (by linarith) (by rwa [hfu])
    have h2 := hφa y (t - u) hy (by linarith)
    rw [← Flow.map_add, ← sub_eq_add_neg, hfu, add_sub_cancel_right] at h1
    exact lt_irrefl a (h1 ▸ h2)

/-- **A band traversed at unit speed is a product.** Under the hypotheses of
`Flow.apply_eq_iff_of_apply_eq_sub`, following the flow line of a point `x` of the band
`f⁻¹[a, b]` down to the level `a` is a homeomorphism `x ↦ (φ (f x - a) x, f x)` from the band onto
`f⁻¹(a) × [a, b]`, with inverse `(y, s) ↦ φ (a - s) y`. It preserves the value of `f`, and it is
the identity on the level `f⁻¹(a)`. -/
def bandHomeomorph (hf : Continuous f) (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)
    (hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a) :
    f ⁻¹' Icc a b ≃ₜ (f ⁻¹' {a}) × Icc a b :=
  have hdown (x : f ⁻¹' Icc a b) : φ (f x - a) x ∈ f ⁻¹' {a} := by
    rw [mem_preimage, mem_singleton_iff, hφf x _ (by linarith [x.2.1]) (by linarith) x.2.2]
    ring
  have hup (p : (f ⁻¹' {a}) × Icc a b) : f (φ (a - p.2) p.1) = p.2 := by
    rw [← neg_sub, φ.apply_neg_eq_add_of_apply_eq_sub hf hanti hφf hφa p.1.2
      (sub_nonneg.2 p.2.2.1) (by linarith [p.2.2.2]), add_sub_cancel]
  have hband (p : (f ⁻¹' {a}) × Icc a b) : φ (a - p.2) p.1 ∈ f ⁻¹' Icc a b := by
    rw [mem_preimage, hup p]
    exact p.2.2
  { toFun x := (⟨φ (f x - a) x, hdown x⟩, ⟨f x, x.2⟩)
    invFun p := ⟨φ (a - p.2) p.1, hband p⟩
    left_inv x := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply]
    right_inv p := Prod.ext (Subtype.ext <| by
        dsimp only
        rw [hup p, ← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply])
      (Subtype.ext (hup p))
    continuous_toFun := by
      have hx : Continuous fun x : f ⁻¹' Icc a b ↦ (x : X) := continuous_subtype_val
      exact ((φ.continuous ((hf.comp hx).sub continuous_const) hx).subtype_mk _).prodMk
        ((hf.comp hx).subtype_mk _)
    continuous_invFun :=
      (φ.continuous (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
        (continuous_subtype_val.comp continuous_fst)).subtype_mk hband }

variable (hf : Continuous f) (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
  (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)
  (hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a)

@[simp]
theorem coe_bandHomeomorph_apply_fst (x : f ⁻¹' Icc a b) :
    ((φ.bandHomeomorph hf hanti hφf hφa x).1 : X) = φ (f x - a) x :=
  (rfl)

@[simp]
theorem coe_bandHomeomorph_apply_snd (x : f ⁻¹' Icc a b) :
    ((φ.bandHomeomorph hf hanti hφf hφa x).2 : ℝ) = f x :=
  (rfl)

@[simp]
theorem coe_bandHomeomorph_symm_apply (p : (f ⁻¹' {a}) × Icc a b) :
    ((φ.bandHomeomorph hf hanti hφf hφa).symm p : X) = φ (a - p.2) p.1 :=
  (rfl)

/-- `Flow.bandHomeomorph` is the identity on the level `f⁻¹(a)`. -/
theorem coe_bandHomeomorph_apply_fst_of_apply_eq {x : f ⁻¹' Icc a b} (hx : f x = a) :
    ((φ.bandHomeomorph hf hanti hφf hφa x).1 : X) = x := by
  simp [hx]

end Flow
