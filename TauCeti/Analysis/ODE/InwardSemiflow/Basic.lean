/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Convex.Cone.StrictInward
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Module

/-!
# Maximal forward semiflows of strictly inward vector fields in convex sets

On a closed convex set `C` with boundary or corners, backward trajectories of a vector field
generally leave `C` immediately, and forward integration requires inwardness along `∂C`. When `X` is
locally Lipschitz on a subset `S ⊆ C` and *strictly inward* to `C` (`X x ∈ strictInwardCone C x`),
forward integral curves immediately enter `interior C`, are uniquely determined by their initial
value, and assemble into a maximal forward semiflow satisfying the cocycle law.

Local existence via constrained Picard contraction, openness of the maximal domain, joint
continuity, forward compact escape, and global forward completeness criteria are proved in
`TauCeti/Analysis/ODE/InwardSemiflow/Existence.lean`; joint `C^m` smoothness up to `t = 0` and `∂C`
and `C^m` inward deformations are established in `TauCeti/Analysis/ODE/InwardSemiflow/Smooth.lean`.

## Main definitions

* `TauCeti.forwardSemiflowInterval X S x`: maximal forward existence interval `[0, T(x))` of an
  integral curve of `X` in `S` starting at `x`.
* `TauCeti.forwardSemiflowDomain X S`: maximal joint domain
  `{(t, x) | x ∈ S ∧ t ∈ forwardSemiflowInterval X S x}`.
* `TauCeti.forwardSemiflow X S`: maximal forward semiflow `(t, x) ↦ Φ_t(x)`.

## Main results

* `HasDerivWithinAt.eventually_mem_interior_of_mem_strictInwardCone`,
  `Convex.mem_interior_of_hasDerivWithinAt_Iic`,
  `Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt`: immediate entry into and persistence inside
  `interior C`.
* `LocallyLipschitzOn.eqOn_Icc_of_hasDerivWithinAt_Ici`,
  `LocallyLipschitzOn.eqOn_Ico_of_hasDerivWithinAt_Ico`: forward uniqueness for locally Lipschitz
  ODEs on arbitrary subsets.
* `TauCeti.eqOn_forwardSemiflow`, `TauCeti.forwardSemiflow_mem_interior`,
  `TauCeti.add_mem_forwardSemiflowInterval_iff`, `TauCeti.forwardSemiflow_add`: uniqueness,
  interior entry, and cocycle law of `forwardSemiflow`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.24–9.26.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
-/

public section

open Filter Function Metric Set
open scoped NNReal Topology

/-! ### Interior entry and persistence along curves -/

section InteriorPersistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve whose right derivative at `a` lies in `strictInwardCone s (γ a)` lies in `interior s`
for all sufficiently small times strictly greater than `a`. No convexity of `s` is required. -/
theorem HasDerivWithinAt.eventually_mem_interior_of_mem_strictInwardCone {s : Set E} {γ : ℝ → E}
    {v : E} {a : ℝ} (hγ : HasDerivWithinAt γ v (Ici a) a)
    (hv : v ∈ TauCeti.strictInwardCone s (γ a)) :
    ∀ᶠ t in 𝓝[>] a, γ t ∈ interior s := by
  obtain ⟨ε, hε, δ, hδ, hball⟩ := TauCeti.mem_strictInwardCone_iff.mp hv
  have ho : ∀ᶠ t in 𝓝[>] a, ‖γ t - γ a - (t - a) • v‖ ≤ ε / 2 * ‖t - a‖ :=
    ((hasDerivWithinAt_iff_isLittleO.mp hγ).bound (half_pos hε)).filter_mono
      (nhdsWithin_mono a Ioi_subset_Ici_self)
  filter_upwards [ho, Ioo_mem_nhdsGT (lt_add_of_pos_right a hδ)] with t ht hIoo
  have hpos : 0 < t - a := sub_pos.mpr hIoo.1
  rw [Real.norm_of_nonneg hpos.le] at ht
  refine mem_interior.mpr ⟨ball (γ t) (ε / 2 * (t - a)), Subset.trans (fun z hz ↦ ?_)
    (hball (t - a) ⟨hpos, sub_lt_iff_lt_add'.mpr hIoo.2⟩), isOpen_ball,
    mem_ball_self (mul_pos (half_pos hε) hpos)⟩
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖z - (γ a + (t - a) • v)‖
      = ‖(z - γ t) + (γ t - γ a - (t - a) • v)‖ := by congr 1; abel
    _ ≤ ‖z - γ t‖ + ‖γ t - γ a - (t - a) • v‖ := norm_add_le _ _
    _ < ε * (t - a) := by linarith

/-- In a convex set `C`, if `γ` lies in `C` for times just before `t` and has left derivative at `t`
in `strictInwardCone C (γ t)`, then `γ t` already lies in `interior C`. -/
theorem Convex.mem_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C) {γ : ℝ → E}
    {v : E} {t : ℝ} (hγ' : HasDerivWithinAt γ v (Iic t) t) (hγC : ∀ᶠ s in 𝓝[<] t, γ s ∈ C)
    (hv : v ∈ TauCeti.strictInwardCone C (γ t)) :
    γ t ∈ interior C := by
  obtain ⟨ε, hε, δ, hδ, hball⟩ := TauCeti.mem_strictInwardCone_iff.mp hv
  have ho : ∀ᶠ s in 𝓝[<] t, ‖γ s - γ t - (s - t) • v‖ ≤ ε / 2 * ‖s - t‖ :=
    ((hasDerivWithinAt_iff_isLittleO.mp hγ').bound (half_pos hε)).filter_mono
      (nhdsWithin_mono t Iio_subset_Iic_self)
  obtain ⟨s, hs_err, hsC, hsIoo⟩ :=
    (ho.and (hγC.and (eventually_mem_set.mpr (Ioo_mem_nhdsLT (sub_lt_self t hδ))))).exists
  set h := t - s
  have hh_pos : 0 < h := sub_pos.mpr hsIoo.2
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos hh_pos] at hs_err
  -- Every `z` within `ε * h / 4` of `γ t` is the midpoint of `γ s ∈ C` and `2 • z - γ s ∈ C`.
  refine mem_interior.mpr ⟨ball (γ t) (ε * h / 4), fun z hz ↦ ?_, isOpen_ball,
    mem_ball_self (by positivity)⟩
  rw [mem_ball, dist_eq_norm] at hz
  have hq : (2 : ℝ) • z - γ s ∈ C := by
    refine hball h ⟨hh_pos, sub_lt_comm.mp hsIoo.1⟩ (mem_ball_iff_norm.mpr ?_)
    calc ‖(2 : ℝ) • z - γ s - (γ t + h • v)‖
        = ‖(2 : ℝ) • (z - γ t) - (γ s - γ t - (s - t) • v)‖ := by
          congr 1; simp only [h]; module
      _ ≤ 2 * ‖z - γ t‖ + ‖γ s - γ t - (s - t) • v‖ :=
          (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_of_nonneg zero_le_two])
      _ < ε * h := by linarith
  rw [← show (1 / 2 : ℝ) • γ s + (1 / 2 : ℝ) • ((2 : ℝ) • z - γ s) = z by module]
  exact hC hsC hq (by norm_num) (by norm_num) (by norm_num)

/-- Any curve in a convex set `C` on `[a, b]` whose left derivatives on `(a, b]` lie in the strict
inward cone of `C` stays in `interior C` for all `t ∈ (a, b]`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (X (γ t)) (Iic t) t)
    (hX : ∀ t ∈ Ioc a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) := fun t ht ↦
  hC.mem_interior_of_hasDerivWithinAt_Iic (hγ' t ht)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT ht.1) fun _ hs ↦ hγ ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    (hX t ht)

/-- Any curve in a convex set `C` on `[a, b]` solving `γ' = X ∘ γ` within `[a, b]` for a strictly
inward field `X` maps `(a, b]` into `interior C`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (X (γ t)) (Icc a b) t)
    (hX : ∀ t ∈ Ioc a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) :=
  hC.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic hγ
    (fun t ht ↦ (hγ' t ht).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Ioi a, isOpen_Ioi, ht.1, fun _ hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩⟩) hX

/-- Any curve in a convex set `C` on `[a, b)` solving `γ' = X ∘ γ` within `[a, b)` for a strictly
inward field `X` maps `(a, b)` into `interior C`. -/
theorem Convex.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Ico a b) C)
    (hγ' : ∀ t ∈ Ioo a b, HasDerivWithinAt γ (X (γ t)) (Ico a b) t)
    (hX : ∀ t ∈ Ioo a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioo a b) (interior C) := fun t ht ↦
  hC.mem_interior_of_hasDerivWithinAt_Iic
    (((hγ' t ht).hasDerivAt (Ico_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT ht.1) fun _ hs ↦ hγ ⟨hs.1.le, hs.2.trans ht.2⟩)
    (hX t ht)

end InteriorPersistence

/-! ### Forward uniqueness for locally Lipschitz fields on subsets -/

namespace LocallyLipschitzOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Forward uniqueness on `[a, b]`.** If `X` is locally Lipschitz on `S`, any two continuous
curves on `[a, b]` mapping `[a, b)` into `S` with right derivative `X (γ t)` on `[a, b)` and the
same value at `a` agree on `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivWithinAt_Ici {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {f g : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (X (f t)) (Ici t) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (X (g t)) (Ici t) t)
    (hg_mem : MapsTo g (Ico a b) S)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := by
  have hIco : EqOn f g (Ico a b) := fun c hc ↦ by
    have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
    let Kset := f '' Icc a c ∪ g '' Icc a c
    have hKcomp : IsCompact Kset :=
      (isCompact_Icc.image_of_continuousOn (hf.mono (hsub.trans Ico_subset_Icc_self))).union
        (isCompact_Icc.image_of_continuousOn (hg.mono (hsub.trans Ico_subset_Icc_self)))
    have hKsub : Kset ⊆ S := union_subset (image_subset_iff.mpr fun t ht ↦ hf_mem (hsub ht))
      (image_subset_iff.mpr fun t ht ↦ hg_mem (hsub ht))
    obtain ⟨K, hKLip⟩ := (hX.mono hKsub).exists_lipschitzOnWith_of_compact hKcomp
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ X) (s := fun _ ↦ Kset)
      (fun _ _ ↦ hKLip) (hf.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hf' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inl (mem_image_of_mem f (Ico_subset_Icc_self ht)))
      (hg.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hg' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inr (mem_image_of_mem g (Ico_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩
  rcases lt_or_ge a b with hab | hba
  · exact hIco.of_subset_closure hf hg Ico_subset_Icc_self (closure_Ico hab.ne ▸ Subset.rfl)
  · intro t ht
    obtain rfl : a = b := le_antisymm (ht.1.trans ht.2) hba
    simpa [le_antisymm ht.1 ht.2] using ha

/-- **Forward uniqueness on `[a, b)`.** Two curves on `[a, b)` mapping into `S`, solving
`γ' = X ∘ γ` within `[a, b)` for a locally Lipschitz field `X` on `S`, and agreeing at `a` agree on
`[a, b)`. -/
theorem eqOn_Ico_of_hasDerivWithinAt_Ico {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {f g : ℝ → E} {a b : ℝ}
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (X (f t)) (Ico a b) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (X (g t)) (Ico a b) t)
    (hg_mem : MapsTo g (Ico a b) S)
    (ha : f a = g a) :
    EqOn f g (Ico a b) := fun c hc ↦ by
  have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
  have hIci {γ : ℝ → E} (h : ∀ t ∈ Ico a b, HasDerivWithinAt γ (X (γ t)) (Ico a b) t) :
      ∀ t ∈ Ico a c, HasDerivWithinAt γ (X (γ t)) (Ici t) t := fun t ht ↦
    (h t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio b, isOpen_Iio, ht.2.trans hc.2, fun _ hs ↦ ⟨ht.1.trans hs.2, hs.1⟩⟩
  exact hX.eqOn_Icc_of_hasDerivWithinAt_Ici
    (fun t ht ↦ ((hf' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hf') (fun t ht ↦ hf_mem (hsub (Ico_subset_Icc_self ht)))
    (fun t ht ↦ ((hg' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hg') (fun t ht ↦ hg_mem (hsub (Ico_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩

end LocallyLipschitzOn

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
    (ht : t ∈ forwardSemiflowInterval X S x) : 0 ≤ t := by
  obtain ⟨_, _, _, htI, -⟩ := ht; exact htI.1

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
    (ht : t ∈ forwardSemiflowInterval X S x) :
    ∃ b > t, Ico 0 b ⊆ forwardSemiflowInterval X S x :=
  let ⟨_, b, hb, htI, h0, hS, hγ'⟩ := ht
  ⟨b, htI.2, Ico_subset_forwardSemiflowInterval hb h0 hS hγ'⟩

/-- `forwardSemiflowInterval` is downward-closed in `[0, ∞)`. -/
theorem Icc_subset_of_mem_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) :
    Icc 0 t ⊆ forwardSemiflowInterval X S x :=
  let ⟨_, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  fun _ hs ↦ hsub ⟨hs.1, hs.2.trans_lt htb⟩

/-- `forwardSemiflowInterval` is order-connected. -/
theorem ordConnected_forwardSemiflowInterval (X : E → E) (S : Set E) (x : E) :
    (forwardSemiflowInterval X S x).OrdConnected :=
  ⟨fun _ hs _ ht _ hr ↦ Icc_subset_of_mem_forwardSemiflowInterval ht
    ⟨(nonneg_of_mem_forwardSemiflowInterval hs).trans hr.1, hr.2⟩⟩

/-- At time `0`, `forwardSemiflow` is always the identity. -/
@[simp]
theorem forwardSemiflow_zero (X : E → E) (S : Set E) (x : E) :
    forwardSemiflow X S 0 x = x := by
  classical
  simp only [forwardSemiflow]
  split_ifs with h0
  · exact h0.choose_spec.choose_spec.2.2.1
  · rfl

/-- Outside `forwardSemiflowInterval X S x`, `forwardSemiflow` returns `x`. -/
theorem forwardSemiflow_of_notMem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∉ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x = x := by
  classical simp [forwardSemiflow, ht]

/-- When every trajectory starting in `C` is globally forward complete, `forwardSemiflowDomain X C`
is equal to `Ici 0 ×ˢ C`. -/
theorem forwardSemiflowDomain_eq_Ici_prod {X : E → E} {C : Set E}
    (hglob : ∀ x ∈ C, forwardSemiflowInterval X C x = Ici 0) :
    forwardSemiflowDomain X C = Ici 0 ×ˢ C := by
  ext ⟨t, x⟩
  simp only [mem_forwardSemiflowDomain_iff, mem_prod, and_comm]
  exact and_congr_right fun hx ↦ by rw [hglob x hx]

end ForwardSemiflowDefs

section ForwardSemiflowUnique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C S : Set E} {X : E → E} {x : E}

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
  dsimp only [forwardSemiflow]
  rw [dite_eq_left ht_mem]
  obtain ⟨b₁, _, ht₁, h0₁, hS₁, hγ₁'⟩ := ht_mem.choose_spec
  set c := min b b₁
  exact hX.eqOn_Ico_of_hasDerivWithinAt_Ico
    (fun s hs ↦ (hγ' s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_left _ _)))
    (hS.mono_left (Ico_subset_Ico_right (min_le_left _ _)))
    (fun s hs ↦ (hγ₁' s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_right _ _)))
    (hS₁.mono_left (Ico_subset_Ico_right (min_le_right _ _)))
    (h0.trans h0₁.symm) ⟨ht.1, lt_min ht.2 ht₁.2⟩

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` stays in `S`. -/
theorem forwardSemiflow_mem (hX : LocallyLipschitzOn S X)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ S := by
  obtain ⟨γ, b, hb, htI, h0, hS, hγ'⟩ := ht
  have heq : γ t = forwardSemiflow X S t x := eqOn_forwardSemiflow hX hb h0 hS hγ' htI
  exact heq ▸ hS htI

/-- On any `[0, b) ⊆ forwardSemiflowInterval X S x` (`0 < b`), `forwardSemiflow` solves
`γ' = X ∘ γ` within `[0, b)`. -/
theorem hasDerivWithinAt_forwardSemiflow_Ico (hX : LocallyLipschitzOn S X) {b t : ℝ}
    (hsub : Ico 0 b ⊆ forwardSemiflowInterval X S x) (ht : t ∈ Ico 0 b) :
    HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (Ico 0 b) t := by
  obtain ⟨γ, d, hd, htI, h0, hS, hγ'⟩ := hsub ht
  have heq := eqOn_forwardSemiflow hX hd h0 hS hγ'
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
  exact (hasDerivWithinAt_forwardSemiflow_Ico hX hsub
    ⟨nonneg_of_mem_forwardSemiflowInterval ht, htb⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio b, isOpen_Iio, htb, fun _ hs ↦ ⟨nonneg_of_mem_forwardSemiflowInterval hs.2, hs.1⟩⟩

/-- At every strictly positive time in `forwardSemiflowInterval X S x`, `forwardSemiflow` has a
two-sided derivative equal to `X (forwardSemiflow X S t x)`. -/
theorem hasDerivAt_forwardSemiflow (hX : LocallyLipschitzOn S X) {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    HasDerivAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) t := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact (hasDerivWithinAt_forwardSemiflow_Ico hX hsub ⟨ht_pos.le, htb⟩).hasDerivAt
    (Ico_mem_nhds ht_pos htb)

/-- **Interior entry and persistence of `forwardSemiflow`.** When `S ⊆ C` for a convex set `C` and
`X` is locally Lipschitz on `S` and strictly inward to `C` on `S`, `forwardSemiflow X S` lies in
`interior C` at every strictly positive time in its forward interval. -/
theorem forwardSemiflow_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX : LocallyLipschitzOn S X) (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    forwardSemiflow X S t x ∈ interior C := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact hC.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico
    (fun _ hs ↦ hSC (forwardSemiflow_mem hX (hsub hs)))
    (fun _ hs ↦ hasDerivWithinAt_forwardSemiflow_Ico hX hsub (Ioo_subset_Ico_self hs))
    (fun _ hs ↦ hX_in _ (forwardSemiflow_mem hX (hsub (Ioo_subset_Ico_self hs)))) ⟨ht_pos, htb⟩

/-- If `x ∈ interior C`, then `forwardSemiflow X S t x ∈ interior C` for all times `t` in its
forward interval (including `t = 0`). -/
theorem forwardSemiflow_mem_interior_of_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX : LocallyLipschitzOn S X) (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    (hx : x ∈ interior C) {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ interior C := by
  rcases (nonneg_of_mem_forwardSemiflowInterval ht).eq_or_lt with rfl | ht_pos
  · simpa using hx
  · exact forwardSemiflow_mem_interior hC hSC hX hX_in ht ht_pos

/-- Concatenating an integral curve on `[0, b₁)` (`0 < s < b₁`) with an integral curve `γ₂` on
`[0, b₂)` starting at `γ₁ s` yields an integral curve on `[0, s + b₂)`. -/
private theorem hasDerivWithinAt_concat_Ico {γ₁ γ₂ : ℝ → E} {s b₁ b₂ : ℝ}
    (hs_pos : 0 < s) (hsb₁ : s < b₁) (hb₂ : 0 < b₂) (h0₂ : γ₂ 0 = γ₁ s)
    (hγ₁' : ∀ u ∈ Ico 0 b₁, HasDerivWithinAt γ₁ (X (γ₁ u)) (Ico 0 b₁) u)
    (hγ₂' : ∀ u ∈ Ico 0 b₂, HasDerivWithinAt γ₂ (X (γ₂ u)) (Ico 0 b₂) u) :
    ∀ u ∈ Ico 0 (s + b₂),
      HasDerivWithinAt (fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s))
        (X ((fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)) u)) (Ico 0 (s + b₂)) u := by
  set γ : ℝ → E := fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)
  intro u hu
  rcases lt_trichotomy u s with hus | rfl | hsu
  · have hγu : γ u = γ₁ u := ite_eq_left hus.le
    have hd := (hγ₁' u ⟨hu.1, hus.trans hsb₁⟩).mono_of_mem_nhdsWithin (s := Ico 0 (s + b₂))
      (mem_nhdsWithin.mpr ⟨Iio s, isOpen_Iio, hus, fun _ hr ↦ ⟨hr.2.1, hr.1.trans hsb₁⟩⟩)
    exact (hγu ▸ hd).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hus))
        fun _ hr ↦ ite_eq_left (mem_Iio.mp hr).le) hγu
  · have hγs : γ u = γ₁ u := ite_eq_left le_rfl
    have hleft : HasDerivWithinAt γ (X (γ u)) (Iic u) u :=
      (hγs ▸ ((hγ₁' u ⟨hs_pos.le, hsb₁⟩).hasDerivAt
        (Ico_mem_nhds hs_pos hsb₁)).hasDerivWithinAt).congr (fun _ hr ↦ ite_eq_left hr) hγs
    have hright : HasDerivWithinAt γ (X (γ u)) (Ici u) u := by
      have hd₂ := HasDerivWithinAt.scomp_of_eq (s := Ici u ∩ Iio (u + b₂)) u
        (hγ₂' 0 ⟨le_rfl, hb₂⟩) ((hasDerivAt_id u).sub_const u).hasDerivWithinAt
        (fun _ hr ↦ ⟨sub_nonneg.mpr hr.1, sub_lt_iff_lt_add'.mpr hr.2⟩) (sub_self u).symm
      simp only [Function.comp_def, id_eq, h0₂, one_smul, ← hγs] at hd₂
      refine (hd₂.mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
        ⟨Iio (u + b₂), isOpen_Iio, mem_Iio.mpr (by linarith), fun _ hr ↦ ⟨hr.2, hr.1⟩⟩).congr
        (fun r (hr : r ∈ Ici u) ↦ ?_) (by simp [γ, h0₂])
      rcases hr.eq_or_lt with rfl | hsr
      · simp [γ, h0₂]
      · exact ite_eq_right (not_le_of_gt hsr)
    have hboth : HasDerivWithinAt γ (X (γ u)) (Iic u ∪ Ici u) u := hleft.union hright
    rw [Iic_union_Ici] at hboth
    exact hboth.mono (subset_univ _)
  · have hγu : γ u = γ₂ (u - s) := ite_eq_right (not_le_of_gt hsu)
    have hd₂ := ((hγ₂' (u - s) ⟨by linarith, by linarith [hu.2]⟩).hasDerivAt
      (Ico_mem_nhds (by linarith) (by linarith [hu.2]))).comp_sub_const u s
    exact (hγu ▸ hd₂.hasDerivWithinAt).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds hsu))
        fun _ hr ↦ ite_eq_right (not_le_of_gt (mem_Ioi.mp hr))) hγu

/-- Time-shifted derivative of `forwardSemiflow` on `[0, b - s)`. -/
private theorem hasDerivWithinAt_forwardSemiflow_shift (hX : LocallyLipschitzOn S X)
    {s b u : ℝ} (hs0 : 0 ≤ s) (hsub : Ico 0 b ⊆ forwardSemiflowInterval X S x)
    (hu : u ∈ Ico 0 (b - s)) :
    HasDerivWithinAt (fun r ↦ forwardSemiflow X S (r + s) x)
      (X (forwardSemiflow X S (u + s) x)) (Ico 0 (b - s)) u := by
  have hcomp := HasDerivWithinAt.scomp (t' := Ico 0 b) (s := Ico 0 (b - s)) u
    (h := fun r ↦ r + s)
    (hasDerivWithinAt_forwardSemiflow_Ico hX hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    ((hasDerivAt_id u).add_const s).hasDerivWithinAt
    (fun _ hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  simpa [Function.comp_def, one_smul] using hcomp

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
      (fun u hu ↦ forwardSemiflow_mem hX (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
      (fun _ hu ↦ hasDerivWithinAt_forwardSemiflow_shift hX hs0 hsub hu) ⟨ht, by linarith⟩
  · rcases hs0.eq_or_lt with rfl | hs_pos
    · simpa using ht'
    obtain ⟨b₁, hsb₁, hsub₁⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hs
    obtain ⟨γ₂, b₂, hb₂, htI₂, h0₂, hS₂, hγ₂'⟩ := ht'
    refine Ico_subset_forwardSemiflowInterval
      (γ := fun u ↦ if u ≤ s then forwardSemiflow X S u x else γ₂ (u - s))
      (by positivity : 0 < s + b₂) (by simp [hs_pos.le])
      (fun u hu ↦ by
        dsimp only
        split_ifs with hus
        · exact forwardSemiflow_mem hX (hsub₁ ⟨hu.1, hus.trans_lt hsb₁⟩)
        · exact hS₂ ⟨by linarith, by linarith [hu.2]⟩)
      (hasDerivWithinAt_concat_Ico hs_pos hsb₁ hb₂ h0₂
        (fun _ hu ↦ hasDerivWithinAt_forwardSemiflow_Ico hX hsub₁ hu) hγ₂')
      ⟨by positivity, by linarith [htI₂.2]⟩

/-- **The semiflow cocycle law.** When `s` lies in the forward interval at `x` and `t` lies in the
forward interval at `forwardSemiflow X S s x`, shifting time by `s` composes the semiflow. -/
theorem forwardSemiflow_add (hX : LocallyLipschitzOn S X)
    {s t : ℝ} (hs : s ∈ forwardSemiflowInterval X S x)
    (ht : t ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x)) :
    forwardSemiflow X S (t + s) x =
      forwardSemiflow X S t (forwardSemiflow X S s x) := by
  have hs0 := nonneg_of_mem_forwardSemiflowInterval hs
  have ht0 := nonneg_of_mem_forwardSemiflowInterval ht
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval
    ((add_mem_forwardSemiflowInterval_iff hX hs ht0).mpr ht)
  exact eqOn_forwardSemiflow hX (by linarith : 0 < b - s) (by simp)
    (fun u hu ↦ forwardSemiflow_mem hX (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
    (fun _ hu ↦ hasDerivWithinAt_forwardSemiflow_shift hX hs0 hsub hu) ⟨ht0, by linarith⟩

end ForwardSemiflowUnique

end TauCeti
