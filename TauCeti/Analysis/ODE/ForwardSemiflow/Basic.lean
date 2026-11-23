/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.ODE.Gronwall
import TauCeti.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.Gluing

/-!
# Maximal forward semiflows of locally Lipschitz vector fields

Defines `TauCeti.forwardSemiflowInterval`, `TauCeti.forwardSemiflowDomain`, and
`TauCeti.forwardSemiflow` for an autonomous vector field `X` on an arbitrary state subset `S`, and
proves maximal interval characterization, forward uniqueness, trajectory derivatives, the semiflow
cocycle law, Grönwall spatial Lipschitz/continuity propagation, cocycle continuation of local
product-neighborhood properties, and non-accumulation under uniform local restart.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.16.
-/

public section

open Filter Function Metric Set
open scoped NNReal Topology

/-! ### The maximal forward semiflow -/

namespace TauCeti

section ForwardSemiflowDefs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The maximal forward interval of existence** of an integral curve of `X` in `S` starting at
`x`: the union of all intervals `[0, b)` (`0 < b`) carrying a curve `γ` with `γ 0 = x`,
`MapsTo γ (Ico 0 b) S`, and `HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s` for all `s ∈ [0, b)`. -/
def forwardSemiflowInterval (X : E → E) (S : Set E) (x : E) : Set ℝ :=
  {t | ∃ γ : ℝ → E, ∃ b > (0 : ℝ), t ∈ Ico 0 b ∧ γ 0 = x ∧ MapsTo γ (Ico 0 b) S ∧
    ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s}

/-- **The joint domain of the maximal forward semiflow** of `X` in `S`, consisting of pairs
`(t, x) : ℝ × E` with `x ∈ S` and `t ∈ forwardSemiflowInterval X S x`. -/
def forwardSemiflowDomain (X : E → E) (S : Set E) : Set (ℝ × E) :=
  {p | p.2 ∈ S ∧ p.1 ∈ forwardSemiflowInterval X S p.2}

open Classical in
/-- **The maximal forward semiflow** of `X` in `S`, evaluated at time `t` and initial point `x`.
Outside `forwardSemiflowInterval X S x` it takes the junk value `x`. -/
noncomputable def forwardSemiflow (X : E → E) (S : Set E) (t : ℝ) (x : E) : E :=
  if ht : t ∈ forwardSemiflowInterval X S x then ht.choose t else x

/-- Membership in `forwardSemiflowInterval` unfolded. -/
theorem mem_forwardSemiflowInterval_iff {X : E → E} {S : Set E} {x : E} {t : ℝ} :
    t ∈ forwardSemiflowInterval X S x ↔
      ∃ γ : ℝ → E, ∃ b > (0 : ℝ), t ∈ Ico 0 b ∧ γ 0 = x ∧ MapsTo γ (Ico 0 b) S ∧
        ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s :=
  Iff.rfl

/-- Membership in `forwardSemiflowDomain` unfolded. -/
@[simp]
theorem mem_forwardSemiflowDomain_iff {X : E → E} {S : Set E} {p : ℝ × E} :
    p ∈ forwardSemiflowDomain X S ↔ p.2 ∈ S ∧ p.1 ∈ forwardSemiflowInterval X S p.2 :=
  Iff.rfl

/-- Every time in `forwardSemiflowInterval` is nonnegative. -/
theorem nonneg_of_mem_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) : 0 ≤ t :=
  let ⟨_, _, _, htI, _⟩ := ht; htI.1

/-- Any integral curve of `X` in `S` on `[0, b)` (`0 < b`) starting at `x` has `[0, b)` contained in
`forwardSemiflowInterval X S x`. -/
theorem Ico_subset_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {γ : ℝ → E} {b : ℝ}
    (hb : 0 < b) (h0 : γ 0 = x) (hS : MapsTo γ (Ico 0 b) S)
    (hγ' : ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s) :
    Ico 0 b ⊆ forwardSemiflowInterval X S x :=
  fun _ ht ↦ ⟨γ, b, hb, ht, h0, hS, hγ'⟩

/-- Every time in `forwardSemiflowInterval` is strictly bounded above by some `b > 0` with
`[0, b) ⊆ forwardSemiflowInterval`. -/
theorem exists_Ico_subset_of_mem_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) : ∃ b > t, Ico 0 b ⊆ forwardSemiflowInterval X S x :=
  let ⟨_, b, hb, htI, h0, hS, hγ'⟩ := ht
  ⟨b, htI.2, Ico_subset_forwardSemiflowInterval hb h0 hS hγ'⟩

/-- `forwardSemiflowInterval` is downward-closed in `[0, ∞)`. -/
theorem Icc_subset_forwardSemiflowInterval_of_mem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) : Icc 0 t ⊆ forwardSemiflowInterval X S x :=
  let ⟨_, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  fun _ hs ↦ hsub ⟨hs.1, hs.2.trans_lt htb⟩

/-- `forwardSemiflowInterval` is order-connected. -/
theorem ordConnected_forwardSemiflowInterval (X : E → E) (S : Set E) (x : E) :
    (forwardSemiflowInterval X S x).OrdConnected :=
  ⟨fun _ hs _ ht _ hr ↦ Icc_subset_forwardSemiflowInterval_of_mem ht
    ⟨(nonneg_of_mem_forwardSemiflowInterval hs).trans hr.1, hr.2⟩⟩

/-- Any finite least upper bound of a `forwardSemiflowInterval` containing `0` is strictly
positive. -/
theorem pos_of_isLUB_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (h0 : (0 : ℝ) ∈ forwardSemiflowInterval X S x)
    (hb : IsLUB (forwardSemiflowInterval X S x) b) : 0 < b := by
  obtain ⟨c, hc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval h0
  exact (half_pos hc).trans_le (hb.1 (hsub ⟨by linarith, by linarith⟩))

/-- An unbounded-above `forwardSemiflowInterval` equals `Ici 0`. -/
theorem forwardSemiflowInterval_eq_Ici_of_not_bddAbove {X : E → E} {S : Set E} {x : E}
    (h : ¬ BddAbove (forwardSemiflowInterval X S x)) : forwardSemiflowInterval X S x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦
    let ⟨_, hs, hts⟩ := not_bddAbove_iff.mp h t
    Icc_subset_forwardSemiflowInterval_of_mem hs ⟨ht, hts.le⟩

/-- At time `0`, `forwardSemiflow` is always the identity. -/
@[simp]
theorem forwardSemiflow_zero (X : E → E) (S : Set E) (x : E) : forwardSemiflow X S 0 x = x := by
  classical simp only [forwardSemiflow]; split_ifs with h0
  exacts [h0.choose_spec.choose_spec.2.2.1, rfl]

/-- Outside `forwardSemiflowInterval X S x`, `forwardSemiflow` returns `x`. -/
theorem forwardSemiflow_of_notMem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∉ forwardSemiflowInterval X S x) : forwardSemiflow X S t x = x := by
  classical simp [forwardSemiflow, ht]

/-- When every trajectory starting in `S` is globally forward complete, `forwardSemiflowDomain X S`
is equal to `Ici 0 ×ˢ S`. -/
theorem forwardSemiflowDomain_eq_Ici_prod {X : E → E} {S : Set E}
    (hglob : ∀ x ∈ S, forwardSemiflowInterval X S x = Ici 0) :
    forwardSemiflowDomain X S = Ici 0 ×ˢ S := by
  ext ⟨t, x⟩; simp only [mem_forwardSemiflowDomain_iff, mem_prod, and_comm]
  exact and_congr_right fun hx ↦ by rw [hglob x hx]

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` stays in `S`. -/
theorem forwardSemiflow_mem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) : forwardSemiflow X S t x ∈ S := by
  classical
  dsimp only [forwardSemiflow]; rw [dite_eq_left ht]
  obtain ⟨_, _, htI, _, hS, _⟩ := ht.choose_spec; exact hS htI

/-- For any `t ∈ forwardSemiflowInterval X S x`, there exists an integral curve `γ` on `[0, b)`
passing through `forwardSemiflow X S t x` at time `t`. -/
theorem exists_integralCurve_apply_eq_forwardSemiflow {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) :
    ∃ γ : ℝ → E, ∃ b > (0 : ℝ), t ∈ Ico 0 b ∧ γ t = forwardSemiflow X S t x ∧
      γ 0 = x ∧ MapsTo γ (Ico 0 b) S ∧
      ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s := by
  classical
  obtain ⟨b, hb, htI, h0, hS, hγ'⟩ := ht.choose_spec
  exact ⟨ht.choose, b, hb, htI, by simp [forwardSemiflow, ht], h0, hS, hγ'⟩

end ForwardSemiflowDefs

end TauCeti

section

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `forwardSemiflowInterval X S x` has a finite least upper bound `b`, then it equals
`Ico 0 b`. -/
theorem IsLUB.forwardSemiflowInterval_eq_Ico {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (hb : IsLUB (forwardSemiflowInterval X S x) b) : forwardSemiflowInterval X S x = Ico 0 b := by
  refine Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨c, htc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
    have hmid : (t + c) / 2 ∈ forwardSemiflowInterval X S x :=
      hsub ⟨by linarith [nonneg_of_mem_forwardSemiflowInterval ht], by linarith⟩
    exact ⟨nonneg_of_mem_forwardSemiflowInterval ht, lt_of_lt_of_le (by linarith) (hb.1 hmid)⟩
  · obtain ⟨s, hs, hts, _⟩ := hb.exists_between ht.2
    exact Icc_subset_forwardSemiflowInterval_of_mem hs ⟨ht.1, hts.le⟩

/-- Every `forwardSemiflowInterval` is either `Ici 0` or `Ico 0 b` for some `b ≥ 0`. -/
theorem TauCeti.forwardSemiflowInterval_eq_Ici_or_exists_eq_Ico (X : E → E) (S : Set E) (x : E) :
    forwardSemiflowInterval X S x = Ici 0 ∨ ∃ b ≥ 0, forwardSemiflowInterval X S x = Ico 0 b := by
  by_cases hbdd : BddAbove (forwardSemiflowInterval X S x)
  · rcases (forwardSemiflowInterval X S x).eq_empty_or_nonempty with hemp | ⟨t, ht⟩
    · exact Or.inr ⟨0, le_rfl, by simp [hemp]⟩
    · have hlub := isLUB_csSup ⟨t, ht⟩ hbdd
      exact Or.inr ⟨_, (nonneg_of_mem_forwardSemiflowInterval ht).trans (hlub.1 ht),
        hlub.forwardSemiflowInterval_eq_Ico⟩
  · exact Or.inl (forwardSemiflowInterval_eq_Ici_of_not_bddAbove hbdd)

end

namespace LocallyLipschitzOn

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {X : E → E} {x : E}

/-- For a locally Lipschitz field `X` on `S`, every forward integral curve on `[0, b)` starting at
`x` agrees with `forwardSemiflow X S` on `[0, b)`. -/
theorem eqOn_forwardSemiflow (hX : LocallyLipschitzOn S X)
    {γ : ℝ → E} {b : ℝ} (hb : 0 < b) (h0 : γ 0 = x) (hS : MapsTo γ (Ico 0 b) S)
    (hγ' : ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (X (γ s)) (Ico 0 b) s) :
    EqOn γ (fun t ↦ forwardSemiflow X S t x) (Ico 0 b) := by
  classical
  intro t ht
  have ht_mem : t ∈ forwardSemiflowInterval X S x :=
    Ico_subset_forwardSemiflowInterval hb h0 hS hγ' ht
  dsimp only [forwardSemiflow]; rw [dite_eq_left ht_mem]
  obtain ⟨b₁, hb₁, ht₁, h0₁, hS₁, hγ₁'⟩ := ht_mem.choose_spec
  exact hX.eqOn_Ico_of_hasDerivAt_Ioo ⟨le_rfl, lt_min hb hb₁⟩
    (fun s hs ↦ ((hγ' s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).continuousWithinAt).mono
      (Ico_subset_Ico_right (min_le_left _ _)))
    (fun s hs ↦ (hγ' s ⟨hs.1.le, hs.2.trans_le (min_le_left _ _)⟩).hasDerivAt
      (Ico_mem_nhds hs.1 (hs.2.trans_le (min_le_left _ _))))
    (hS.mono_left (Ico_subset_Ico_right (min_le_left _ _)))
    (fun s hs ↦ ((hγ₁' s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩).continuousWithinAt).mono
      (Ico_subset_Ico_right (min_le_right _ _)))
    (fun s hs ↦ (hγ₁' s ⟨hs.1.le, hs.2.trans_le (min_le_right _ _)⟩).hasDerivAt
      (Ico_mem_nhds hs.1 (hs.2.trans_le (min_le_right _ _))))
    (hS₁.mono_left (Ico_subset_Ico_right (min_le_right _ _)))
    (h0.trans h0₁.symm) ⟨ht.1, lt_min ht.2 ht₁.2⟩

/-- On any `[0, b) ⊆ forwardSemiflowInterval X S x` (`0 < b`), `forwardSemiflow` solves
`γ' = X ∘ γ` within `[0, b)`. -/
theorem hasDerivWithinAt_forwardSemiflow_Ico (hX : LocallyLipschitzOn S X) {b t : ℝ}
    (hsub : Ico 0 b ⊆ forwardSemiflowInterval X S x) (ht : t ∈ Ico 0 b) :
    HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (Ico 0 b) t := by
  obtain ⟨γ, d, hd, htI, h0, hS, hγ'⟩ := hsub ht
  have heq := hX.eqOn_forwardSemiflow hd h0 hS hγ'
  have h1 := ((hγ' t htI).mono (Ico_subset_Ico_right (min_le_right b d))).congr
    (fun s hs ↦ (heq ⟨hs.1, hs.2.trans_le (min_le_right b d)⟩).symm) (heq htI).symm
  rw [heq htI] at h1
  exact h1.mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
    ⟨Iio (min b d), isOpen_Iio, lt_min ht.2 htI.2, fun _ hs ↦ ⟨hs.2.1, hs.1⟩⟩

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` solves `γ' = X ∘ γ` within its maximal
forward interval. -/
theorem hasDerivWithinAt_forwardSemiflow (hX : LocallyLipschitzOn S X) {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) :
    HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (forwardSemiflowInterval X S x) t := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact (hX.hasDerivWithinAt_forwardSemiflow_Ico hsub
    ⟨nonneg_of_mem_forwardSemiflowInterval ht, htb⟩).mono_of_mem_nhdsWithin <|
    mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, htb,
      fun _ hs ↦ ⟨nonneg_of_mem_forwardSemiflowInterval hs.2, hs.1⟩⟩

/-- At every strictly positive time in `forwardSemiflowInterval X S x`, `forwardSemiflow` has a
two-sided derivative equal to `X (forwardSemiflow X S t x)`. -/
theorem hasDerivAt_forwardSemiflow (hX : LocallyLipschitzOn S X) {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    HasDerivAt (fun s ↦ forwardSemiflow X S s x) (X (forwardSemiflow X S t x)) t := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact (hX.hasDerivWithinAt_forwardSemiflow_Ico hsub ⟨ht_pos.le, htb⟩).hasDerivAt
    (Ico_mem_nhds ht_pos htb)

/-- Time-shifted derivative of `forwardSemiflow` on `[0, b - s)`. -/
private theorem hasDerivWithinAt_forwardSemiflow_shift (hX : LocallyLipschitzOn S X)
    {s b u : ℝ} (hs0 : 0 ≤ s) (hsub : Ico 0 b ⊆ forwardSemiflowInterval X S x)
    (hu : u ∈ Ico 0 (b - s)) :
    HasDerivWithinAt (fun r ↦ forwardSemiflow X S (r + s) x)
      (X (forwardSemiflow X S (u + s) x)) (Ico 0 (b - s)) u := by
  simpa [Function.comp_def, one_smul] using HasDerivWithinAt.scomp (t' := Ico 0 b)
    (s := Ico 0 (b - s)) u (h := fun r ↦ r + s)
    (hX.hasDerivWithinAt_forwardSemiflow_Ico hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    ((hasDerivAt_id u).add_const s).hasDerivWithinAt
    fun _ hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- **Translation characterization of `forwardSemiflowInterval`.** For `s` in the forward interval
at `x` and `0 ≤ t`, `t + s` lies in the forward interval at `x` if and only if `t` lies in the
forward interval at `forwardSemiflow X S s x`. -/
theorem add_mem_forwardSemiflowInterval_iff (hX : LocallyLipschitzOn S X)
    {s t : ℝ} (hs : s ∈ forwardSemiflowInterval X S x) (ht : 0 ≤ t) :
    t + s ∈ forwardSemiflowInterval X S x ↔
      t ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x) := by
  have hs0 := nonneg_of_mem_forwardSemiflowInterval hs
  refine ⟨fun hts ↦ ?_, fun ht' ↦ ?_⟩
  · obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hts
    exact Ico_subset_forwardSemiflowInterval (γ := fun u ↦ forwardSemiflow X S (u + s) x)
      (by linarith : 0 < b - s) (by simp)
      (fun u hu ↦ forwardSemiflow_mem (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
      (fun _ hu ↦ hX.hasDerivWithinAt_forwardSemiflow_shift hs0 hsub hu) ⟨ht, by linarith⟩
  · obtain ⟨b₁, hsb₁, hsub₁⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hs
    obtain ⟨γ₂, b₂, hb₂, htI₂, h0₂, hS₂, hγ₂'⟩ := ht'
    refine Ico_subset_forwardSemiflowInterval
      (γ := fun u ↦ if u ≤ s then forwardSemiflow X S u x else γ₂ (u - s))
      (by positivity : 0 < s + b₂) (by simp [hs0])
      (fun u hu ↦ by
        dsimp only; split_ifs with hus
        exacts [forwardSemiflow_mem (hsub₁ ⟨hu.1, hus.trans_lt hsb₁⟩),
          hS₂ ⟨by linarith, by linarith [hu.2]⟩])
      (fun _ hu ↦ hasDerivWithinAt_ite_Ico X h0₂
        (fun _ hv ↦ (hX.hasDerivWithinAt_forwardSemiflow_Ico hsub₁
          ⟨hv.1, hv.2.trans_lt hsb₁⟩).mono fun _ hr ↦ ⟨hr.1, hr.2.trans_lt hsb₁⟩) hγ₂' hu)
      ⟨by positivity, by linarith [htI₂.2]⟩

/-- **The semiflow cocycle law.** When `s` lies in the forward interval at `x` and `t` lies in the
forward interval at `forwardSemiflow X S s x`, shifting time by `s` composes the semiflow. -/
theorem forwardSemiflow_add (hX : LocallyLipschitzOn S X)
    {s t : ℝ} (hs : s ∈ forwardSemiflowInterval X S x)
    (ht : t ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x)) :
    forwardSemiflow X S (t + s) x = forwardSemiflow X S t (forwardSemiflow X S s x) := by
  have hs0 := nonneg_of_mem_forwardSemiflowInterval hs
  have ht0 := nonneg_of_mem_forwardSemiflowInterval ht
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval
    ((hX.add_mem_forwardSemiflowInterval_iff hs ht0).mpr ht)
  exact hX.eqOn_forwardSemiflow (by linarith : 0 < b - s) (by simp)
    (fun u hu ↦ forwardSemiflow_mem (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
    (fun _ hu ↦ hX.hasDerivWithinAt_forwardSemiflow_shift hs0 hsub hu) ⟨ht0, by linarith⟩

/-- Spatial Grönwall Lipschitz bound and joint continuity of `forwardSemiflow` on `Icc 0 τ ×ˢ B`
from a Lipschitz bound on `X` over a trapping region `B'`. -/
theorem exists_lipschitzOnWith_and_continuousOn_forwardSemiflow_Icc_prod {B B' : Set E}
    (hX : LocallyLipschitzOn S X) {τ : ℝ} {K : ℝ≥0}
    (hKLip : LipschitzOnWith K X B')
    (hsub : ∀ y ∈ B, τ ∈ forwardSemiflowInterval X S y)
    (hmem : ∀ y ∈ B, ∀ t ∈ Ico 0 τ, forwardSemiflow X S t y ∈ B') :
    ∃ KΦ : ℝ≥0,
      (∀ t ∈ Icc 0 τ, LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X S t y) B) ∧
      ContinuousOn (uncurry (forwardSemiflow X S)) (Icc 0 τ ×ˢ B) := by
  let KΦ : ℝ≥0 := Real.toNNReal (Real.exp ((K : ℝ) * τ))
  have hcont {y : E} (hy : y ∈ B) : ContinuousOn (fun u ↦ forwardSemiflow X S u y) (Icc 0 τ) := by
    obtain ⟨b, hτb, hsub_y⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval (hsub y hy)
    exact fun s hs ↦ ((hX.hasDerivWithinAt_forwardSemiflow_Ico hsub_y
      ⟨hs.1, hs.2.trans_lt hτb⟩).continuousWithinAt).mono fun _ hu ↦ ⟨hu.1, hu.2.trans_lt hτb⟩
  have hLipΦ (t : ℝ) (ht : t ∈ Icc 0 τ) :
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X S t y) B := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun y₁ hy₁ y₂ hy₂ ↦ ?_
    have hIci {y : E} (hy : y ∈ B) (s : ℝ) (hs : s ∈ Ico 0 τ) : HasDerivWithinAt
        (fun u ↦ forwardSemiflow X S u y) (X (forwardSemiflow X S s y)) (Ici s) s := by
      obtain ⟨b, hτb, hsub_y⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval (hsub y hy)
      exact (hX.hasDerivWithinAt_forwardSemiflow_Ico hsub_y
        ⟨hs.1, hs.2.trans hτb⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
          ⟨Iio b, isOpen_Iio, hs.2.trans hτb, fun _ hu ↦ ⟨hs.1.trans hu.2, hu.1⟩⟩
    refine (dist_le_of_trajectories_ODE_of_mem (v := fun _ ↦ X) (s := fun _ ↦ B')
      (fun _ _ ↦ hKLip) (hcont hy₁) (hIci hy₁) (hmem y₁ hy₁)
      (hcont hy₂) (hIci hy₂) (hmem y₂ hy₂)
      (by simp only [forwardSemiflow_zero]; exact le_rfl) t ht).trans ?_
    rw [sub_zero, mul_comm (dist y₁ y₂), Real.coe_toNNReal _ (Real.exp_pos _).le]
    gcongr; exact ht.2
  exact ⟨KΦ, hLipΦ,
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ KΦ hLipΦ fun _ hy ↦ hcont hy⟩

/-- Restart, cocycle-shift, and gluing step for `exists_Icc_prod_of_mem_forwardSemiflowInterval`:
combines a property `Q` on `Icc 0 (s + δs) ×ˢ B₁` with a property `Q` on `Icc 0 τz ×ˢ B₂` when
`forwardSemiflow X S s` maps `B ⊆ B₁` into `B₂`. -/
private theorem cocycle_glue_Icc_prod (hX : LocallyLipschitzOn S X)
    {Q : Set (ℝ × E) → ℝ × E → Prop}
    (hQ_mono : ∀ ⦃S₁ S₂ p⦄, p ∈ S₁ → S₁ ⊆ S₂ → Q S₂ p → Q S₁ p)
    (hQ_nhds : ∀ ⦃S₁ S₂ p⦄, S₁ ⊆ S₂ → S₁ ∈ 𝓝[S₂] p → Q S₁ p → Q S₂ p)
    (hQ_shift : ∀ {s δ τ : ℝ} {B₁ B₂ : Set E},
      (∀ p ∈ Icc 0 (s + δ) ×ˢ B₁, Q (Icc 0 (s + δ) ×ˢ B₁) p) →
      (∀ p ∈ Icc 0 τ ×ˢ B₂, Q (Icc 0 τ ×ˢ B₂) p) → 0 ≤ s → 0 < δ →
      (∀ y ∈ B₁, forwardSemiflow X S s y ∈ B₂) →
      (∀ p ∈ Icc s (s + τ) ×ˢ B₁, uncurry (forwardSemiflow X S) p =
        uncurry (forwardSemiflow X S) (p.1 - s, forwardSemiflow X S s p.2)) →
      ∀ p ∈ Icc s (s + τ) ×ˢ B₁, Q (Icc s (s + τ) ×ˢ B₁) p)
    {s δs τz : ℝ} {B₁ B₂ B : Set E} (hs0 : 0 ≤ s) (hδs : 0 < δs) (hτz : 0 < τz)
    (hB_sub : B ⊆ B₁)
    (hsubs : ∀ y ∈ B₁, Ico 0 (s + 2 * δs) ⊆ forwardSemiflowInterval X S y)
    (hsubz : ∀ y ∈ B₂, Ico 0 (2 * τz) ⊆ forwardSemiflowInterval X S y)
    (hQs : ∀ p ∈ Icc 0 (s + δs) ×ˢ B₁, Q (Icc 0 (s + δs) ×ˢ B₁) p)
    (hQz : ∀ p ∈ Icc 0 τz ×ˢ B₂, Q (Icc 0 τz ×ˢ B₂) p)
    (hΦs_ball : ∀ y ∈ B, forwardSemiflow X S s y ∈ B₂) :
    (∀ y ∈ B, Ico 0 (s + 2 * τz) ⊆ forwardSemiflowInterval X S y) ∧
      ∀ p ∈ Icc 0 (s + τz) ×ˢ B, Q (Icc 0 (s + τz) ×ˢ B) p := by
  have hsub_all (y : E) (hy : y ∈ B) :
      Ico 0 (s + 2 * τz) ⊆ forwardSemiflowInterval X S y := fun t ht ↦ by
    have hsJ := hsubs y (hB_sub hy) ⟨hs0, by linarith⟩
    rcases le_or_gt t s with hts | hst
    · exact Icc_subset_forwardSemiflowInterval_of_mem hsJ ⟨ht.1, hts⟩
    · rw [← sub_add_cancel t s]
      exact (hX.add_mem_forwardSemiflowInterval_iff hsJ (by linarith)).mpr
        (hsubz (forwardSemiflow X S s y) (hΦs_ball y hy) ⟨by linarith, by linarith [ht.2]⟩)
  have hstep_Q : ∀ p ∈ Icc s (s + τz) ×ˢ B, Q (Icc s (s + τz) ×ˢ B) p :=
    hQ_shift (fun p hp ↦ hQ_mono hp (prod_mono Subset.rfl hB_sub) (hQs p ⟨hp.1, hB_sub hp.2⟩))
      hQz hs0 hδs hΦs_ball fun p hp ↦ by
        have htJ : p.1 - s ∈ forwardSemiflowInterval X S (forwardSemiflow X S s p.2) :=
          hsubz (forwardSemiflow X S s p.2) (hΦs_ball p.2 hp.2)
            ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
        simpa [uncurry, sub_add_cancel] using
          hX.forwardSemiflow_add (hsub_all p.2 hp.2 ⟨hs0, by linarith⟩) htJ
  refine ⟨hsub_all, fun p hp ↦ ?_⟩
  set T₁ := min (s + δs) (s + τz)
  rcases lt_or_ge p.1 T₁ with hlt | hge
  · exact hQ_nhds (prod_mono (Icc_subset_Icc_right (min_le_right _ _)) Subset.rfl)
      (mem_nhdsWithin.mpr ⟨Iio T₁ ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hlt, trivial⟩,
        fun q hq ↦ ⟨⟨hq.2.1.1, hq.1.1.le⟩, hq.2.2⟩⟩)
      (hQ_mono ⟨⟨hp.1.1, hlt.le⟩, hp.2⟩ (prod_mono (Icc_subset_Icc_right (min_le_left _ _)) hB_sub)
        (hQs p ⟨⟨hp.1.1, hlt.le.trans (min_le_left _ _)⟩, hB_sub hp.2⟩))
  · exact hQ_nhds (prod_mono (Icc_subset_Icc_left hs0) Subset.rfl)
      (mem_nhdsWithin.mpr ⟨Ioi s ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
        ⟨(lt_min (by linarith) (by linarith)).trans_le hge, trivial⟩,
        fun q hq ↦ ⟨⟨hq.1.1.le, hq.2.1.2⟩, hq.2.2⟩⟩)
      (hstep_Q p ⟨⟨(lt_min (by linarith) (by linarith)).trans_le hge |>.le, hp.1.2⟩, hp.2⟩)

/-- **Cocycle continuation along `forwardSemiflowInterval`.** Any local product-neighborhood
property `Q : Set (ℝ × E) → ℝ × E → Prop` of `forwardSemiflow X S` that implies joint continuity,
is closed under restriction, neighborhood-within localization, and cocycle time-shifting, and holds
locally around every point of `S`, propagates to `Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ S)` for every
`T ∈ forwardSemiflowInterval X S x₀`. -/
theorem exists_Icc_prod_of_mem_forwardSemiflowInterval
    (hX : LocallyLipschitzOn S X) {Q : Set (ℝ × E) → ℝ × E → Prop}
    (hQ_mono : ∀ ⦃S₁ S₂ p⦄, p ∈ S₁ → S₁ ⊆ S₂ → Q S₂ p → Q S₁ p)
    (hQ_cont : ∀ ⦃S'⦄, (∀ p ∈ S', Q S' p) → ContinuousOn (uncurry (forwardSemiflow X S)) S')
    (hQ_nhds : ∀ ⦃S₁ S₂ p⦄, S₁ ⊆ S₂ → S₁ ∈ 𝓝[S₂] p → Q S₁ p → Q S₂ p)
    (hQ_shift : ∀ {s δ τ : ℝ} {B₁ B₂ : Set E},
      (∀ p ∈ Icc 0 (s + δ) ×ˢ B₁, Q (Icc 0 (s + δ) ×ˢ B₁) p) →
      (∀ p ∈ Icc 0 τ ×ˢ B₂, Q (Icc 0 τ ×ˢ B₂) p) → 0 ≤ s → 0 < δ →
      (∀ y ∈ B₁, forwardSemiflow X S s y ∈ B₂) →
      (∀ p ∈ Icc s (s + τ) ×ˢ B₁, uncurry (forwardSemiflow X S) p =
        uncurry (forwardSemiflow X S) (p.1 - s, forwardSemiflow X S s p.2)) →
      ∀ p ∈ Icc s (s + τ) ×ˢ B₁, Q (Icc s (s + τ) ×ˢ B₁) p)
    (hQ_loc : ∀ x ∈ S, ∃ r > 0, ∃ τ > 0,
      (∀ y ∈ ball x r ∩ S, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X S y) ∧
      ∀ p ∈ Icc 0 τ ×ˢ (ball x r ∩ S), Q (Icc 0 τ ×ˢ (ball x r ∩ S)) p)
    {x₀ : E} {T : ℝ} (hx₀ : x₀ ∈ S) (hT : T ∈ forwardSemiflowInterval X S x₀) :
    ∃ r > 0, ∃ δ > 0,
      (∀ y ∈ ball x₀ r ∩ S, Ico 0 (T + 2 * δ) ⊆ forwardSemiflowInterval X S y) ∧
      ∀ p ∈ Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ S), Q (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ S)) p := by
  let Φ := forwardSemiflow X S
  let P : ℝ → Prop := fun t ↦ ∃ r > 0, ∃ δ > 0,
    (∀ y ∈ ball x₀ r ∩ S, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X S y) ∧
    ∀ p ∈ Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ S), Q (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ S)) p
  have hP_ext {t r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
      (hsub : ∀ y ∈ ball x₀ r ∩ S, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X S y)
      (hQ : ∀ p ∈ Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ S), Q (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ S)) p)
      {u : ℝ} (hu : u ≤ t + δ / 2) : P u :=
    ⟨r, hr, δ / 4, by positivity,
      fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub y hy),
      fun p hp ↦ hQ_mono hp (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)
        (hQ p ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)⟩
  -- Step 1: Assume `¬ P T` and let `b = sInf {t ∈ [0, T] | ¬ P t}`; show `0 < b ≤ T`.
  by_contra hnotPT
  let B : Set ℝ := {t ∈ Icc 0 T | ¬ P t}
  have hBne : B.Nonempty := ⟨T, ⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  have hBbdd : BddBelow B := ⟨0, fun _ ht ↦ ht.1.1⟩
  set b := sInf B
  have hb0 : 0 ≤ b := le_csInf hBne fun _ ht ↦ ht.1.1
  have hbT : b ≤ T := csInf_le hBbdd ⟨⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  obtain ⟨r₀, hr₀, τ₀, hτ₀, hsub₀, hQ₀⟩ := hQ_loc x₀ hx₀
  have hb_pos : 0 < b := lt_of_lt_of_le (by positivity : 0 < τ₀ / 4) <|
    le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦ ht.2 <|
      hP_ext (t := 0) hr₀ (half_pos hτ₀)
        (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub₀ y hy))
        (fun p hp ↦ hQ_mono hp (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)
          (hQ₀ p ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)) (by linarith)
  -- Step 2: Take a local neighborhood `(rz, τz)` around `Φ b x₀` and step back to `s = b - η < b`.
  have hbJ : b ∈ forwardSemiflowInterval X S x₀ :=
    Icc_subset_forwardSemiflowInterval_of_mem hT ⟨hb0, hbT⟩
  obtain ⟨rz, hrz, τz, hτz, hsubz, hQz⟩ := hQ_loc (Φ b x₀) (forwardSemiflow_mem hbJ)
  obtain ⟨η₀, hη₀, hclose_b⟩ := Metric.continuousAt_iff.mp
    ((hX.hasDerivAt_forwardSemiflow hbJ hb_pos).continuousAt) rz hrz
  set η := min (b / 2) (min (η₀ / 2) (τz / 3))
  have hη : 0 < η := by positivity
  set s := b - η
  have hs_pos : 0 < s := by linarith [min_le_left (b / 2) (min (η₀ / 2) (τz / 3))]
  have hs_lt_b : s < b := sub_lt_self b hη
  have hΦs_mem : Φ s x₀ ∈ ball (Φ b x₀) rz := hclose_b <| by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt_b)]
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_left (η₀ / 2) (τz / 3)]
  -- Step 3: Use `P s` and continuity of `Φ s` to shrink `r' ≤ rs` so `Φ s` maps
  -- `ball x₀ r' ∩ S` into `ball (Φ b x₀) rz ∩ S`.
  have hPs : P s := by_contra fun hnotPs ↦
    not_lt_of_ge (csInf_le hBbdd ⟨⟨hs_pos.le, hs_lt_b.le.trans hbT⟩, hnotPs⟩) hs_lt_b
  obtain ⟨rs, hrs, δs, hδs, hsubs, hQs⟩ := hPs
  have hΦs_cont : ContinuousOn (fun y ↦ Φ s y) (ball x₀ rs ∩ S) := (hQ_cont hQs).comp
    (continuousOn_const.prodMk continuousOn_id) fun _ hy ↦ ⟨⟨hs_pos.le, by linarith⟩, hy⟩
  obtain ⟨rc, hrc, hballc⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hΦs_cont x₀ ⟨mem_ball_self hrs, hx₀⟩).eventually (isOpen_ball.mem_nhds hΦs_mem))
  set r' := min rs rc
  have hΦs_ball (y : E) (hy : y ∈ ball x₀ r' ∩ S) : Φ s y ∈ ball (Φ b x₀) rz ∩ S := by
    have hy_rs : y ∈ ball x₀ rs ∩ S := ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    exact ⟨hballc ⟨ball_subset_ball (min_le_right _ _) hy.1, hy_rs⟩,
      forwardSemiflow_mem (hsubs y hy_rs ⟨hs_pos.le, by linarith⟩)⟩
  -- Step 4: Glue via `cocycle_glue_Icc_prod` to push `P` past `b`, contradicting `b = sInf B`.
  obtain ⟨hsub_all, hglue⟩ := hX.cocycle_glue_Icc_prod hQ_mono hQ_nhds hQ_shift hs_pos.le hδs hτz
    (inter_subset_inter_left S (ball_subset_ball (min_le_left _ _)))
    hsubs hsubz hQs hQz hΦs_ball
  have hbs_le : b - s ≤ τz / 3 := by
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_right (η₀ / 2) (τz / 3)]
  have hb_contra : b + τz / 6 ≤ b := le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦
    ht.2 <| hP_ext (t := b) (lt_min hrs hrc) (by positivity : 0 < τz / 3)
      (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub_all y hy))
      (fun p hp ↦ hQ_mono hp (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)
        (hglue p ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)) (by linarith)
  linarith

/-- **No cluster point with uniform local restart.** If `X` is locally Lipschitz on `S`,
`forwardSemiflowInterval X S x` is nonempty with least upper bound `b`, and every point of `S`
near `z` admits a uniform positive forward existence time `τ > 0`, then
`forwardSemiflow X S · x` cannot accumulate at `z` as `t → b⁻`. -/
theorem not_mapClusterPt_nhdsLT_forwardSemiflow (hX : LocallyLipschitzOn S X) {x z : E} {b : ℝ}
    (hne : (forwardSemiflowInterval X S x).Nonempty)
    (hb : IsLUB (forwardSemiflowInterval X S x) b)
    (hrest : ∃ V ∈ 𝓝 z, ∃ τ > 0, ∀ y ∈ V ∩ S, τ ∈ forwardSemiflowInterval X S y) :
    ¬ MapClusterPt z (𝓝[<] b) (fun t ↦ forwardSemiflow X S t x) := by
  intro hcl
  obtain ⟨t₀, ht₀⟩ := hne
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X S x :=
    Icc_subset_forwardSemiflowInterval_of_mem ht₀
      ⟨le_rfl, nonneg_of_mem_forwardSemiflowInterval ht₀⟩
  have hb_pos := pos_of_isLUB_forwardSemiflowInterval h0 hb
  obtain ⟨V, hV, τ, hτ, hsub⟩ := hrest
  obtain ⟨s, hs_V, hs_Ioo⟩ := ((hcl.frequently hV).and_eventually
    (Ioo_mem_nhdsLT (max_lt hb_pos (sub_lt_self b hτ)))).exists
  have hsJ : s ∈ forwardSemiflowInterval X S x :=
    hb.forwardSemiflowInterval_eq_Ico ▸ ⟨(le_max_left 0 (b - τ)).trans hs_Ioo.1.le, hs_Ioo.2⟩
  have huJ : τ ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x) :=
    hsub _ ⟨hs_V, forwardSemiflow_mem hsJ⟩
  linarith [hb.1 ((hX.add_mem_forwardSemiflowInterval_iff hsJ hτ.le).mpr huJ),
    (le_max_right 0 (b - τ)).trans_lt hs_Ioo.1]

end LocallyLipschitzOn
