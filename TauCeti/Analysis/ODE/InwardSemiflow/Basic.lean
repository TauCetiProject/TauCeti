/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Convex.Cone.StrictInward
import TauCeti.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.Gluing
import Mathlib.Tactic.Module

/-!
# Maximal forward semiflows of strictly inward vector fields in convex sets

Defines `TauCeti.forwardSemiflowInterval`, `TauCeti.forwardSemiflowDomain`, and
`TauCeti.forwardSemiflow` for a locally Lipschitz vector field `X` on `S ⊆ C` strictly inward to a
convex set `C`, and proves interior entry, maximal interval characterization, uniqueness, and the
semiflow cocycle law. Local existence/continuity and `C^m` regularity appear in `Existence.lean` and
`Smooth.lean`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.24–9.26.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
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

/-- When every trajectory starting in `C` is globally forward complete, `forwardSemiflowDomain X C`
is equal to `Ici 0 ×ˢ C`. -/
theorem forwardSemiflowDomain_eq_Ici_prod {X : E → E} {C : Set E}
    (hglob : ∀ x ∈ C, forwardSemiflowInterval X C x = Ici 0) :
    forwardSemiflowDomain X C = Ici 0 ×ˢ C := by
  ext ⟨t, x⟩; simp only [mem_forwardSemiflowDomain_iff, mem_prod, and_comm]
  exact and_congr_right fun hx ↦ by rw [hglob x hx]

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` stays in `S`. -/
theorem forwardSemiflow_mem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) : forwardSemiflow X S t x ∈ S := by
  classical
  dsimp only [forwardSemiflow]; rw [dite_eq_left ht]
  obtain ⟨_, _, htI, _, hS, _⟩ := ht.choose_spec; exact hS htI

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

section ForwardSemiflowGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C S : Set E} {X : E → E} {x : E}

/-- **Interior entry and persistence of `forwardSemiflow`.** When `S ⊆ C` for a convex set `C` and
`X` is strictly inward to `C` on `S`, `forwardSemiflow X S` lies in `interior C` at every strictly
positive time in its forward interval. -/
theorem Convex.forwardSemiflow_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    forwardSemiflow X S t x ∈ interior C := by
  classical
  dsimp only [forwardSemiflow]; rw [dite_eq_left ht]
  obtain ⟨b, _, htI, _, hS, hγ'⟩ := ht.choose_spec
  exact hC.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico (hS.mono_right hSC)
    (fun _ hs ↦ hγ' _ (Ioo_subset_Ico_self hs))
    (fun _ hs ↦ hX_in _ (hS (Ioo_subset_Ico_self hs))) ⟨ht_pos, htI.2⟩

/-- If `x ∈ interior C`, then `forwardSemiflow X S t x ∈ interior C` for all times `t` in its
forward interval (including `t = 0`). -/
theorem Convex.forwardSemiflow_mem_interior_of_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    (hx : x ∈ interior C) {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ interior C := by
  rcases (nonneg_of_mem_forwardSemiflowInterval ht).eq_or_lt with rfl | ht_pos
  exacts [by simpa using hx, hC.forwardSemiflow_mem_interior hSC hX_in ht ht_pos]

end ForwardSemiflowGeometry

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
  obtain ⟨b₁, _, ht₁, h0₁, hS₁, hγ₁'⟩ := ht_mem.choose_spec
  exact hX.eqOn_Ico_of_hasDerivWithinAt_Ico
    (fun s hs ↦ (hγ' s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_left _ _)))
    (hS.mono_left (Ico_subset_Ico_right (min_le_left _ _)))
    (fun s hs ↦ (hγ₁' s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_right _ _)))
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

end LocallyLipschitzOn
