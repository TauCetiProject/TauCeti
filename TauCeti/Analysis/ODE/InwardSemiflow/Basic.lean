/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Convex.Cone.StrictInward
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

/-!
# Maximal forward semiflows of strictly inward vector fields in convex sets

On an open subset of a Banach space, a locally Lipschitz autonomous vector field generates local
two-sided integral curves by Picard–Lindelöf iteration. On a closed convex set `C` with boundary or
corners — such as a closed quadrant or half-space modeling charts with corners — backward
trajectories generally leave `C` immediately, and even forward integration requires an inwardness
hypothesis along `∂C`.

When `X` is locally Lipschitz on `U ∩ C` (for an open set `U` and a closed convex set `C`) and
*strictly inward* to `C` (`X x ∈ strictInwardCone C x`), forward integration becomes well-posed up
to `∂C` and immediately pushes every trajectory into `interior C`:

1. **Interior entry and persistence.** Any curve whose right derivative at `a` lies in
   `strictInwardCone s (γ a)` enters `interior s` for small positive times, without convexity
   (`HasDerivWithinAt.eventually_mem_interior_of_mem_strictInwardCone`). In a convex set `C`, a
   curve lying in `C` before time `t` whose left derivative at `t` lies in
   `strictInwardCone C (γ t)` already lies in `interior C` at time `t`
   (`Convex.mem_interior_of_hasDerivWithinAt_Iic`); hence any forward integral curve of a strictly
   inward field in `C` maps positive times into `interior C`.
2. **Forward uniqueness.** Forward integral curves of a locally Lipschitz field `X` on an arbitrary
   set `S` are uniquely determined by their initial value
   (`LocallyLipschitzOn.eqOn_Icc_of_hasDerivWithinAt_Ici`,
   `LocallyLipschitzOn.eqOn_Ico_of_hasDerivWithinAt_Ico`).
3. **Maximal forward semiflow.** `TauCeti.forwardSemiflowInterval X S x`,
   `TauCeti.forwardSemiflowDomain X S`, and `TauCeti.forwardSemiflow X S` assemble the maximal
   forward trajectory `[0, T(x)) → S` starting at `x`, satisfying the differential equation,
   immediate entry into `interior C`, and the semiflow cocycle law
   `forwardSemiflow X S (t + s) x = forwardSemiflow X S t (forwardSemiflow X S s x)`.
4. **Local existence, openness of domain, and joint continuity.** Constrained Picard iteration on
   the closed subset of continuous paths lying in the inward cone tube
   `closedBall (x + t • X x) (ε / 2 * t) ⊆ C` produces uniform local forward trajectories,
   spatial Lipschitz dependence, and joint continuity
   (`TauCeti.exists_local_forwardSemiflow_continuousOn`). Propagating along maximal trajectories
   shows that `forwardSemiflowDomain X (U ∩ C)` is relatively open in `Ici 0 ×ˢ (U ∩ C)`
   (`TauCeti.exists_isOpen_forwardSemiflowDomain`) and that `uncurry (forwardSemiflow X (U ∩ C))`
   is continuous there (`TauCeti.continuousOn_forwardSemiflow`).
5. **Forward compact escape and global forward completeness.** At any finite least upper bound of
   `forwardSemiflowInterval X (U ∩ C) x`, the trajectory has no cluster point in `U ∩ C`
   (`TauCeti.not_mapClusterPt_nhdsLT_forwardSemiflow`) and leaves every compact subset of `U ∩ C`
   (`TauCeti.eventually_notMem_nhdsLT_forwardSemiflow`). Compactness of `C` or a proper Lyapunov
   function with bounded derivative along `X` therefore yields global forward completeness on
   `[0, ∞)` (`TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact`,
   `TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel`).

Higher `C^m` smoothness up to `t = 0` and `∂C` and `C^m` inward deformations into `interior C` are
established in `TauCeti/Analysis/ODE/InwardSemiflow/Smooth.lean`.

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
* `TauCeti.forwardSemiflow_mem_interior`, `TauCeti.add_mem_forwardSemiflowInterval_iff`,
  `TauCeti.forwardSemiflow_add`: interior entry and cocycle law of `forwardSemiflow`.
* `TauCeti.exists_isOpen_forwardSemiflowDomain`, `TauCeti.continuousOn_forwardSemiflow`: relative
  openness of the maximal domain and joint continuity of the semiflow.
* `TauCeti.not_mapClusterPt_nhdsLT_forwardSemiflow`,
  `TauCeti.eventually_notMem_nhdsLT_forwardSemiflow`,
  `TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact`,
  `TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel`: forward compact escape and global
  forward completeness criteria.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12, 9.16, and 9.24–9.26.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
-/

public section

open Filter Function Metric Set intervalIntegral
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
  have ho := (hasDerivWithinAt_iff_isLittleO.mp hγ).bound (half_pos hε)
  have ho' : ∀ᶠ t in 𝓝[>] a, ‖γ t - γ a - (t - a) • v‖ ≤ ε / 2 * ‖t - a‖ :=
    ho.filter_mono (nhdsWithin_mono a Ioi_subset_Ici_self)
  filter_upwards [ho', Ioo_mem_nhdsGT (lt_add_of_pos_right a hδ)] with t ht hIoo
  have hpos : 0 < t - a := sub_pos.mpr hIoo.1
  have hlt : t - a < δ := sub_lt_iff_lt_add'.mpr hIoo.2
  rw [Real.norm_of_nonneg hpos.le] at ht
  refine mem_interior.mpr ⟨ball (γ t) (ε / 2 * (t - a)), ?_, isOpen_ball,
    mem_ball_self (mul_pos (half_pos hε) hpos)⟩
  refine Subset.trans (fun z hz ↦ ?_) (hball (t - a) ⟨hpos, hlt⟩)
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have hdecomp : z - (γ a + (t - a) • v) = (z - γ t) + (γ t - γ a - (t - a) • v) := by abel
  rw [hdecomp]
  calc ‖(z - γ t) + (γ t - γ a - (t - a) • v)‖
      ≤ ‖z - γ t‖ + ‖γ t - γ a - (t - a) • v‖ := norm_add_le _ _
    _ < ε / 2 * (t - a) + ε / 2 * (t - a) := add_lt_add_of_lt_of_le hz ht
    _ = ε * (t - a) := by ring

/-- In a convex set `C`, if `γ` lies in `C` for times just before `t` and has left derivative at `t`
in `strictInwardCone C (γ t)`, then `γ t` already lies in `interior C`. -/
theorem Convex.mem_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C) {γ : ℝ → E}
    {v : E} {t : ℝ} (hγ' : HasDerivWithinAt γ v (Iic t) t) (hγC : ∀ᶠ s in 𝓝[<] t, γ s ∈ C)
    (hv : v ∈ TauCeti.strictInwardCone C (γ t)) :
    γ t ∈ interior C := by
  obtain ⟨ε, hε, δ, hδ, hball⟩ := TauCeti.mem_strictInwardCone_iff.mp hv
  have ho := (hasDerivWithinAt_iff_isLittleO.mp hγ').bound (half_pos hε)
  have ho' : ∀ᶠ s in 𝓝[<] t, ‖γ s - γ t - (s - t) • v‖ ≤ ε / 2 * ‖s - t‖ :=
    ho.filter_mono (nhdsWithin_mono t Iio_subset_Iic_self)
  have hev := ho'.and (hγC.and (eventually_mem_set.mpr (Ioo_mem_nhdsLT (sub_lt_self t hδ))))
  obtain ⟨s, hs_err, hsC, hsIoo⟩ := hev.exists
  set h := t - s
  have hh_pos : 0 < h := sub_pos.mpr hsIoo.2
  have hh_lt : h < δ := sub_lt_comm.mp hsIoo.1
  have hnorm : ‖s - t‖ = h := by
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos hh_pos]
  rw [hnorm] at hs_err
  -- Every `z` within `ε * h / 4` of `γ t` is the midpoint of `γ s ∈ C` and `2 • z - γ s`, which
  -- lies in `ball (γ t + h • v) (ε * h) ⊆ C`.
  refine mem_interior.mpr ⟨ball (γ t) (ε * h / 4), fun z hz ↦ ?_, isOpen_ball,
    mem_ball_self (by positivity)⟩
  rw [mem_ball, dist_eq_norm] at hz
  have hq : (2 : ℝ) • z - γ s ∈ C := by
    apply hball h ⟨hh_pos, hh_lt⟩
    rw [mem_ball, dist_eq_norm]
    have hq_eq : (2 : ℝ) • z - γ s - (γ t + h • v) =
        (2 : ℝ) • (z - γ t) - (γ s - γ t - (s - t) • v) := by
      simp only [h]
      module
    rw [hq_eq]
    calc ‖(2 : ℝ) • (z - γ t) - (γ s - γ t - (s - t) • v)‖
        ≤ ‖(2 : ℝ) • (z - γ t)‖ + ‖γ s - γ t - (s - t) • v‖ := norm_sub_le _ _
      _ = 2 * ‖z - γ t‖ + ‖γ s - γ t - (s - t) • v‖ := by
          rw [norm_smul, Real.norm_of_nonneg zero_le_two]
      _ < 2 * (ε * h / 4) + ε / 2 * h := by linarith
      _ = ε * h := by ring
  have hmid : (1 / 2 : ℝ) • γ s + (1 / 2 : ℝ) • ((2 : ℝ) • z - γ s) = z := by module
  rw [← hmid]
  exact hC hsC hq (by norm_num) (by norm_num) (by norm_num)

/-- Any curve in a convex set `C` on `[a, b]` whose left derivatives on `(a, b]` lie in the strict
inward cone of `C` stays in `interior C` for all `t ∈ (a, b]`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (X (γ t)) (Iic t) t)
    (hX : ∀ t ∈ Ioc a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) := by
  intro t ht
  refine hC.mem_interior_of_hasDerivWithinAt_Iic (hγ' t ht) ?_ (hX t ht)
  filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
  exact hγ ⟨hs.1.le, hs.2.le.trans ht.2⟩

/-- Any curve in a convex set `C` on `[a, b]` solving `γ' = X ∘ γ` within `[a, b]` for a strictly
inward field `X` maps `(a, b]` into `interior C`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (X (γ t)) (Icc a b) t)
    (hX : ∀ t ∈ Ioc a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) := by
  refine hC.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic hγ (fun t ht ↦ ?_) hX
  refine (hγ' t ht).mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Ioi a, Ioi_mem_nhds ht.1, fun s hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩⟩

/-- Any curve in a convex set `C` on `[a, b)` solving `γ' = X ∘ γ` within `[a, b)` for a strictly
inward field `X` maps `(a, b)` into `interior C`. -/
theorem Convex.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico {C : Set E} (hC : Convex ℝ C)
    {X : E → E} {γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Ico a b) C)
    (hγ' : ∀ t ∈ Ioo a b, HasDerivWithinAt γ (X (γ t)) (Ico a b) t)
    (hX : ∀ t ∈ Ioo a b, X (γ t) ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioo a b) (interior C) := by
  intro t ht
  refine hC.mem_interior_of_hasDerivWithinAt_Iic ?_ ?_ (hX t ht)
  · exact ((hγ' t ht).hasDerivAt (Ico_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  · filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
    exact hγ ⟨hs.1.le, hs.2.trans ht.2⟩

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
  -- First agree on `[a, b)` by restricting to compact subintervals `[a, c] ⊆ [a, b)`.
  have hIco : EqOn f g (Ico a b) := by
    intro c hc
    have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
    let Kset := f '' Icc a c ∪ g '' Icc a c
    have hKcomp : IsCompact Kset :=
      (isCompact_Icc.image_of_continuousOn (hf.mono (hsub.trans Ico_subset_Icc_self))).union
        (isCompact_Icc.image_of_continuousOn (hg.mono (hsub.trans Ico_subset_Icc_self)))
    have hKsub : Kset ⊆ S := union_subset
      (image_subset_iff.mpr fun t ht ↦ hf_mem (hsub ht))
      (image_subset_iff.mpr fun t ht ↦ hg_mem (hsub ht))
    obtain ⟨K, hKLip⟩ := (hX.mono hKsub).exists_lipschitzOnWith_of_compact hKcomp
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ X) (s := fun _ ↦ Kset)
      (fun _ _ ↦ hKLip)
      (hf.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hf' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inl (mem_image_of_mem f (Ico_subset_Icc_self ht)))
      (hg.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hg' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inr (mem_image_of_mem g (Ico_subset_Icc_self ht)))
      ha ⟨hc.1, le_rfl⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact hIco.of_subset_closure hf hg Ico_subset_Icc_self (closure_Ico hab.ne ▸ Subset.rfl)
  · intro t ht
    rw [Icc_self, mem_singleton_iff] at ht
    exact ht ▸ ha
  · intro t ht
    exact False.elim ((not_le_of_gt hba) (ht.1.trans ht.2))

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
    EqOn f g (Ico a b) := by
  intro c hc
  have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
  have hIci {γ : ℝ → E} (h : ∀ t ∈ Ico a b, HasDerivWithinAt γ (X (γ t)) (Ico a b) t) :
      ∀ t ∈ Ico a c, HasDerivWithinAt γ (X (γ t)) (Ici t) t := by
    intro t ht
    refine (h t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Iio b, Iio_mem_nhds (ht.2.trans hc.2), fun s hs ↦ ⟨ht.1.trans hs.2, hs.1⟩⟩
  exact hX.eqOn_Icc_of_hasDerivWithinAt_Ici
    (fun t ht ↦ ((hf' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hf') (fun t ht ↦ hf_mem (hsub (Ico_subset_Icc_self ht)))
    (fun t ht ↦ ((hg' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hg') (fun t ht ↦ hg_mem (hsub (Ico_subset_Icc_self ht)))
    ha ⟨hc.1, le_rfl⟩

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
  obtain ⟨_, _, _, htI, -⟩ := ht
  exact htI.1

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
    ∃ b > t, Ico 0 b ⊆ forwardSemiflowInterval X S x := by
  obtain ⟨γ, b, hb, htI, h0, hS, hγ'⟩ := ht
  exact ⟨b, htI.2, Ico_subset_forwardSemiflowInterval hb h0 hS hγ'⟩

/-- `forwardSemiflowInterval` is downward-closed in `[0, ∞)`. -/
theorem Icc_subset_of_mem_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) :
    Icc 0 t ⊆ forwardSemiflowInterval X S x := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact fun s hs ↦ hsub ⟨hs.1, hs.2.trans_lt htb⟩

/-- `forwardSemiflowInterval` is order-connected. -/
theorem ordConnected_forwardSemiflowInterval (X : E → E) (S : Set E) (x : E) :
    (forwardSemiflowInterval X S x).OrdConnected := by
  refine ⟨fun s hs t ht r hr ↦ ?_⟩
  exact Icc_subset_of_mem_forwardSemiflowInterval ht
    ⟨(nonneg_of_mem_forwardSemiflowInterval hs).trans hr.1, hr.2⟩

/-- At time `0`, `forwardSemiflow` is always the identity. -/
@[simp]
theorem forwardSemiflow_zero (X : E → E) (S : Set E) (x : E) :
    forwardSemiflow X S 0 x = x := by
  classical
  unfold forwardSemiflow
  split_ifs with h0
  · exact h0.choose_spec.choose_spec.2.2.1
  · rfl

/-- Outside `forwardSemiflowInterval X S x`, `forwardSemiflow` returns `x`. -/
theorem forwardSemiflow_of_notMem {X : E → E} {S : Set E} {x : E} {t : ℝ}
    (ht : t ∉ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x = x := by
  classical
  unfold forwardSemiflow
  exact dite_eq_right ht

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
  dsimp only
  unfold forwardSemiflow
  rw [dite_eq_left ht_mem]
  set γ₁ := ht_mem.choose
  obtain ⟨b₁, _, ht₁, h0₁, hS₁, hγ₁'⟩ := ht_mem.choose_spec
  set c := min b b₁
  have hsub : Ico 0 c ⊆ Ico 0 b := Ico_subset_Ico_right (min_le_left _ _)
  have hsub₁ : Ico 0 c ⊆ Ico 0 b₁ := Ico_subset_Ico_right (min_le_right _ _)
  have hderiv {δ : ℝ → E} {d : ℝ} (hd : c ≤ d)
      (h : ∀ s ∈ Ico 0 d, HasDerivWithinAt δ (X (δ s)) (Ico 0 d) s) :
      ∀ s ∈ Ico 0 c, HasDerivWithinAt δ (X (δ s)) (Ico 0 c) s :=
    fun s hs ↦ (h s ⟨hs.1, hs.2.trans_le hd⟩).mono (Ico_subset_Ico_right hd)
  exact hX.eqOn_Ico_of_hasDerivWithinAt_Ico
    (hderiv (min_le_left _ _) hγ') (hS.mono_left hsub)
    (hderiv (min_le_right _ _) hγ₁') (hS₁.mono_left hsub₁)
    (h0.trans h0₁.symm) ⟨ht.1, lt_min ht.2 ht₁.2⟩

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` stays in `S`. -/
theorem forwardSemiflow_mem (hX : LocallyLipschitzOn S X)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ S := by
  obtain ⟨γ, b, hb, htI, h0, hS, hγ'⟩ := ht
  have heq : γ t = forwardSemiflow X S t x := eqOn_forwardSemiflow hX hb h0 hS hγ' htI
  rw [← heq]
  exact hS htI

/-- On any `[0, b) ⊆ forwardSemiflowInterval X S x` (`0 < b`), `forwardSemiflow` solves
`γ' = X ∘ γ` within `[0, b)`. -/
theorem hasDerivWithinAt_forwardSemiflow_Ico (hX : LocallyLipschitzOn S X) {b t : ℝ}
    (hsub : Ico 0 b ⊆ forwardSemiflowInterval X S x) (ht : t ∈ Ico 0 b) :
    HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (Ico 0 b) t := by
  obtain ⟨γ, d, hd, htI, h0, hS, hγ'⟩ := hsub ht
  have heq := eqOn_forwardSemiflow hX hd h0 hS hγ'
  set c := min b d
  have htc : t ∈ Ico 0 c := ⟨ht.1, lt_min ht.2 htI.2⟩
  have hd_c : HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (Ico 0 c) t := by
    have h1 := (hγ' t htI).mono (Ico_subset_Ico_right (min_le_right b d))
    rw [heq htI] at h1
    exact h1.congr (fun s hs ↦ (heq ⟨hs.1, hs.2.trans_le (min_le_right b d)⟩).symm)
      (heq htI).symm
  refine hd_c.mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Iio c, Iio_mem_nhds htc.2, fun s hs ↦ ⟨hs.2.1, hs.1⟩⟩

/-- On `forwardSemiflowInterval X S x`, `forwardSemiflow` solves `γ' = X ∘ γ` within its maximal
forward interval. -/
theorem hasDerivWithinAt_forwardSemiflow (hX : LocallyLipschitzOn S X) {t : ℝ}
    (ht : t ∈ forwardSemiflowInterval X S x) :
    HasDerivWithinAt (fun s ↦ forwardSemiflow X S s x)
      (X (forwardSemiflow X S t x)) (forwardSemiflowInterval X S x) t := by
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  have hd := hasDerivWithinAt_forwardSemiflow_Ico hX hsub
    ⟨nonneg_of_mem_forwardSemiflowInterval ht, htb⟩
  refine hd.mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Iio b, Iio_mem_nhds htb,
    fun s hs ↦ ⟨nonneg_of_mem_forwardSemiflowInterval hs.2, hs.1⟩⟩

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
    (fun s hs ↦ hSC (forwardSemiflow_mem hX (hsub hs)))
    (fun s hs ↦ hasDerivWithinAt_forwardSemiflow_Ico hX hsub (Ioo_subset_Ico_self hs))
    (fun s hs ↦ hX_in _ (forwardSemiflow_mem hX (hsub (Ioo_subset_Ico_self hs))))
    ⟨ht_pos, htb⟩

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
  rcases lt_trichotomy u s with hus | hus_eq | hsu
  · have hγu : γ u = γ₁ u := ite_eq_left hus.le
    have hd := (hγ₁' u ⟨hu.1, hus.trans hsb₁⟩).mono_of_mem_nhdsWithin (s := Ico 0 (s + b₂)) (by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Iio s, Iio_mem_nhds hus, fun r hr ↦ ⟨hr.2.1, hr.1.trans hsb₁⟩⟩)
    rw [← hγu] at hd
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hus)] with r hr
      exact ite_eq_left (mem_Iio.mp hr).le) hγu
  · subst hus_eq
    have hγs : γ u = γ₁ u := ite_eq_left le_rfl
    have hleft : HasDerivWithinAt γ (X (γ u)) (Iic u) u := by
      have hd := ((hγ₁' u ⟨hs_pos.le, hsb₁⟩).hasDerivAt
        (Ico_mem_nhds hs_pos hsb₁)).hasDerivWithinAt (s := Iic u)
      rw [← hγs] at hd
      exact hd.congr (fun r hr ↦ ite_eq_left hr) hγs
    have hright : HasDerivWithinAt γ (X (γ u)) (Ici u) u := by
      have hd₂ := HasDerivWithinAt.scomp_of_eq (s := Ici u ∩ Iio (u + b₂)) u
        (hγ₂' 0 ⟨le_rfl, hb₂⟩) ((hasDerivAt_id u).sub_const u).hasDerivWithinAt
        (fun r hr ↦ ⟨sub_nonneg.mpr hr.1, sub_lt_iff_lt_add'.mpr hr.2⟩) (sub_self u).symm
      simp only [Function.comp_def, id_eq, h0₂, one_smul] at hd₂
      rw [← hγs] at hd₂
      have hd₂' := hd₂.mono_of_mem_nhdsWithin (s := Ici u) (by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Iio (u + b₂), Iio_mem_nhds (by linarith), fun r hr ↦ ⟨hr.2, hr.1⟩⟩)
      refine hd₂'.congr (fun r (hr : r ∈ Ici u) ↦ ?_) (by simp [γ, h0₂])
      rcases hr.eq_or_lt with rfl | hsr
      · simp [γ, h0₂]
      · exact ite_eq_right (not_le_of_gt hsr)
    have hboth : HasDerivWithinAt γ (X (γ u)) (Iic u ∪ Ici u) u := hleft.union hright
    rw [Iic_union_Ici] at hboth
    exact hboth.mono (subset_univ _)
  · have hγu : γ u = γ₂ (u - s) := ite_eq_right (not_le_of_gt hsu)
    have hd₂ := ((hγ₂' (u - s) ⟨by linarith, by linarith [hu.2]⟩).hasDerivAt
      (Ico_mem_nhds (by linarith) (by linarith [hu.2]))).comp_sub_const u s
    rw [← hγu] at hd₂
    exact hd₂.hasDerivWithinAt.congr_of_eventuallyEq (by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hsu)] with r hr
      exact ite_eq_right (not_le_of_gt (mem_Ioi.mp hr))) hγu

/-- **Translation characterization of `forwardSemiflowInterval`.** For `s` in the forward interval
at `x` and `0 ≤ t`, `t + s` lies in the forward interval at `x` if and only if `t` lies in the
forward interval at `forwardSemiflow X S s x`. -/
theorem add_mem_forwardSemiflowInterval_iff (hX : LocallyLipschitzOn S X)
    {s t : ℝ} (hs : s ∈ forwardSemiflowInterval X S x) (ht : 0 ≤ t) :
    t + s ∈ forwardSemiflowInterval X S x ↔
      t ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x) := by
  have hs0 := nonneg_of_mem_forwardSemiflowInterval hs
  constructor
  · intro hts
    obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hts
    have hb_sub : 0 < b - s := by linarith
    refine Ico_subset_forwardSemiflowInterval (γ := fun u ↦ forwardSemiflow X S (u + s) x)
      hb_sub (by simp)
      (fun u hu ↦ forwardSemiflow_mem hX (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
      (fun u hu ↦ ?_) ⟨ht, by linarith⟩
    have hd := hasDerivWithinAt_forwardSemiflow_Ico hX hsub
      (t := u + s) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcomp := HasDerivWithinAt.scomp (t' := Ico 0 b) (s := Ico 0 (b - s)) u
      (h := fun r ↦ r + s) hd ((hasDerivAt_id u).add_const s).hasDerivWithinAt
      (fun r hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    simpa [Function.comp_def, one_smul] using hcomp
  · intro ht'
    rcases hs0.eq_or_lt with rfl | hs_pos
    · simpa using ht'
    obtain ⟨b₁, hsb₁, hsub₁⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hs
    obtain ⟨γ₂, b₂, hb₂, htI₂, h0₂, hS₂, hγ₂'⟩ := ht'
    let γ : ℝ → E := fun u ↦ if u ≤ s then forwardSemiflow X S u x else γ₂ (u - s)
    have hγ0 : γ 0 = x := by simp [γ, hs_pos.le]
    have hγS : MapsTo γ (Ico 0 (s + b₂)) S := by
      intro u hu
      dsimp only [γ]
      split_ifs with hus
      · exact forwardSemiflow_mem hX (hsub₁ ⟨hu.1, hus.trans_lt hsb₁⟩)
      · exact hS₂ ⟨by linarith, by linarith [hu.2]⟩
    exact Ico_subset_forwardSemiflowInterval (by positivity : 0 < s + b₂) hγ0 hγS
      (hasDerivWithinAt_concat_Ico (γ₁ := fun u ↦ forwardSemiflow X S u x) hs_pos hsb₁ hb₂ h0₂
        (fun u hu ↦ hasDerivWithinAt_forwardSemiflow_Ico hX hsub₁ hu) hγ₂')
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
  have hts : t + s ∈ forwardSemiflowInterval X S x :=
    (add_mem_forwardSemiflowInterval_iff hX hs ht0).mpr ht
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval hts
  have hb_sub : 0 < b - s := by linarith
  have heq := eqOn_forwardSemiflow hX hb_sub (x := forwardSemiflow X S s x)
    (γ := fun u ↦ forwardSemiflow X S (u + s) x) (by simp)
    (fun u hu ↦ forwardSemiflow_mem hX
      (hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩))
    (fun u hu ↦ by
      have hd := hasDerivWithinAt_forwardSemiflow_Ico hX hsub
        (t := u + s) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hcomp := HasDerivWithinAt.scomp (t' := Ico 0 b) (s := Ico 0 (b - s)) u
        (h := fun r ↦ r + s) hd ((hasDerivAt_id u).add_const s).hasDerivWithinAt
        (fun r hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
      simpa [Function.comp_def, one_smul] using hcomp)
  exact heq ⟨ht0, by linarith⟩

end ForwardSemiflowUnique

/-! ### Constrained Picard contraction, openness of domain, and joint continuity -/

section LocalExistenceAndContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every continuous path on `[0, b]` lying in the inward cone tube
`closedBall (x + t • X x) (ε / 2 * t)` stays in `ball x₀ (2 * r) ∩ C` and within distance
`(‖X x‖ + ε / 2) * b` of `x`. -/
private theorem mem_ball_and_norm_sub_le_of_mem_inwardTube {C : Set E} {X : E → E}
    {x₀ x : E} {r b ε : ℝ} (hx : x ∈ ball x₀ r ∩ C) (hε : 0 < ε)
    (hin : ∀ t ∈ Ioc 0 b, closedBall (x + t • X x) (ε / 2 * t) ⊆ C)
    (hrad : (‖X x‖ + ε / 2) * b < r) {γ : C(Icc 0 b, E)}
    (hγ : ∀ t : Icc 0 b, γ t ∈ closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ)))
    (t : Icc 0 b) :
    γ t ∈ ball x₀ (2 * r) ∩ C ∧ ‖γ t - x‖ ≤ (‖X x‖ + ε / 2) * b := by
  have ht_cb := hγ t
  have hnorm : ‖γ t - x‖ ≤ (‖X x‖ + ε / 2) * b := by
    have hcb : ‖γ t - (x + (t : ℝ) • X x)‖ ≤ ε / 2 * (t : ℝ) :=
      mem_closedBall_iff_norm.mp ht_cb
    calc ‖γ t - x‖ = ‖(γ t - (x + (t : ℝ) • X x)) + (t : ℝ) • X x‖ := by congr 1; abel
      _ ≤ ‖γ t - (x + (t : ℝ) • X x)‖ + ‖(t : ℝ) • X x‖ := norm_add_le _ _
      _ ≤ ε / 2 * (t : ℝ) + (t : ℝ) * ‖X x‖ := by
          rw [norm_smul, Real.norm_of_nonneg t.2.1]; linarith
      _ = (‖X x‖ + ε / 2) * (t : ℝ) := by ring
      _ ≤ (‖X x‖ + ε / 2) * b :=
          mul_le_mul_of_nonneg_left t.2.2 (by positivity)
  have hC_t : γ t ∈ C := by
    rcases t.2.1.eq_or_lt with ht0 | ht_pos
    · have h0 : γ t ∈ closedBall x 0 := by simpa [← ht0] using ht_cb
      rw [mem_closedBall, dist_le_zero] at h0
      exact h0 ▸ hx.2
    · exact hin t ⟨ht_pos, t.2.2⟩ ht_cb
  refine ⟨⟨?_, hC_t⟩, hnorm⟩
  rw [mem_ball]
  have hd_lt : dist (γ t) x < r := by simpa [dist_eq_norm] using hnorm.trans_lt hrad
  calc dist (γ t) x₀ ≤ dist (γ t) x + dist x x₀ := dist_triangle _ _ _
    _ < r + r := add_lt_add hd_lt hx.1
    _ = 2 * r := by ring

/-- Constrained Picard contraction for a single initial point `x ∈ ball x₀ r ∩ C`, on the closed
subset of `C(Icc 0 b, E)` consisting of paths in `closedBall (x + t • X x) (ε / 2 * t) ⊆ C`. -/
private theorem exists_Icc_trajectory_of_ball_subset {C : Set E} (hC_closed : IsClosed C)
    {X : E → E} {x₀ x : E} {r b ε : ℝ} {K : ℝ≥0} (hx : x ∈ ball x₀ r ∩ C) (hb : 0 < b)
    (hε : 0 < ε) (hK : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C))
    (hin : ∀ t ∈ Ioc 0 b, closedBall (x + t • X x) (ε / 2 * t) ⊆ C)
    (hrad : (‖X x‖ + ε / 2) * b < r)
    (hself : (K : ℝ) * ((‖X x‖ + ε / 2) * b) ≤ ε / 2)
    (hcontr : (K : ℝ) * b ≤ 1 / 2) :
    ∃ γ : ℝ → E, γ 0 = x ∧ MapsTo γ (Icc 0 b) (ball x₀ (2 * r) ∩ C) ∧
      (∀ t ∈ Icc 0 b, γ t = x + ∫ s in (0 : ℝ)..t, X (γ s)) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt γ (X (γ t)) (Icc 0 b) t := by
  let _ := hC_closed
  -- Step 1: Set up the complete metric space `S` of paths inside the inward cone tube.
  let S : Set C(Icc 0 b, E) :=
    {γ | ∀ t : Icc 0 b, γ t ∈ closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ))}
  have hS_closed : IsClosed S := by
    have hS_eq : S = ⋂ t : Icc 0 b,
        (fun γ : C(Icc 0 b, E) ↦ γ t) ⁻¹' closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ)) := by
      ext γ; simp [S]
    rw [hS_eq]
    exact isClosed_iInter fun _ ↦ isClosed_closedBall.preimage (by fun_prop)
  have : CompleteSpace S := hS_closed.completeSpace_coe
  have : Nonempty S := ⟨⟨⟨fun t ↦ x + (t : ℝ) • X x, by fun_prop⟩,
    fun t ↦ mem_closedBall_self (mul_nonneg (half_pos hε).le t.2.1)⟩⟩
  have hS_mem (γ : S) (t : Icc 0 b) :=
    mem_ball_and_norm_sub_le_of_mem_inwardTube hx hε hin hrad γ.2 t
  -- Step 2: Define the Picard integral operator `P : S → S` and verify `1 / 2`-contractivity.
  let f : S → ℝ → E := fun γ s ↦ X (γ.1 (projIcc 0 b hb.le s))
  have hf_cont (γ : S) : Continuous (f γ) :=
    hK.continuousOn.comp_continuous (γ.1.continuous.comp continuous_projIcc)
      fun s ↦ (hS_mem γ _).1
  let P₀ : S → C(Icc 0 b, E) := fun γ ↦ ⟨fun t ↦ x + ∫ s in (0 : ℝ)..(t : ℝ), f γ s,
    ((continuous_primitive (fun _ _ ↦ (hf_cont γ).intervalIntegrable _ _) 0).const_add x).comp
      continuous_subtype_val⟩
  have hr_pos : 0 < r := dist_nonneg.trans_lt hx.1
  let P : S → S := fun γ ↦ ⟨P₀ γ, fun t ↦ by
    simp only [P₀, ContinuousMap.coe_mk, mem_closedBall, dist_eq_norm]
    have hconst : x + (t : ℝ) • X x = x + ∫ _ in (0 : ℝ)..(t : ℝ), X x := by
      simp [intervalIntegral.integral_const]
    rw [hconst, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hf_cont γ).intervalIntegrable _ _)
        intervalIntegrable_const]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2)
      fun s _ ↦ ?_).trans ?_
    · calc ‖f γ s - X x‖ ≤ (K : ℝ) * ‖γ.1 (projIcc 0 b hb.le s) - x‖ := by
            simpa [f, dist_eq_norm] using hK.dist_le_mul _ (hS_mem γ _).1 x
              ⟨ball_subset_ball (by linarith) hx.1, hx.2⟩
        _ ≤ (K : ℝ) * ((‖X x‖ + ε / 2) * b) :=
            mul_le_mul_of_nonneg_left (hS_mem γ _).2 K.coe_nonneg
        _ ≤ ε / 2 := hself
    · rw [sub_zero, abs_of_nonneg t.2.1]⟩
  have hP : ContractingWith (1 / 2) P := by
    refine ⟨by norm_num, lipschitzWith_iff_dist_le_mul.mpr fun γ₁ γ₂ ↦ ?_⟩
    rw [Subtype.dist_eq, ContinuousMap.dist_le (by positivity)]
    intro t
    simp only [P, P₀, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub ((hf_cont γ₁).intervalIntegrable _ _)
      ((hf_cont γ₂).intervalIntegrable _ _)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (K : ℝ) * dist γ₁ γ₂) fun s _ ↦ ?_).trans ?_
    · calc ‖f γ₁ s - f γ₂ s‖ ≤ (K : ℝ) * dist (γ₁.1 (projIcc 0 b hb.le s))
            (γ₂.1 (projIcc 0 b hb.le s)) := by
            simpa [f, dist_eq_norm] using hK.dist_le_mul _ (hS_mem γ₁ _).1 _ (hS_mem γ₂ _).1
        _ ≤ (K : ℝ) * dist γ₁ γ₂ :=
            mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist _) K.coe_nonneg
    · rw [sub_zero, abs_of_nonneg t.2.1]
      calc (K : ℝ) * dist γ₁ γ₂ * (t : ℝ) = ((K : ℝ) * (t : ℝ)) * dist γ₁ γ₂ := by ring
        _ ≤ (1 / 2 : ℝ) * dist γ₁ γ₂ :=
            mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_left t.2.2 K.coe_nonneg).trans hcontr) dist_nonneg
        _ = ↑(1 / 2 : ℝ≥0) * dist γ₁ γ₂ := by norm_num
  -- Step 3: Differentiate the fixed point via the fundamental theorem of calculus.
  set γstar : S := hP.fixedPoint
  have hfix : P γstar = γstar := hP.fixedPoint_isFixedPt
  let γ : ℝ → E := fun t ↦ x + ∫ s in (0 : ℝ)..t, f γstar s
  have hγ_eq (t : ℝ) (ht : t ∈ Icc 0 b) : γ t = γstar.1 ⟨t, ht⟩ :=
    congr_arg (fun z : S ↦ z.1 ⟨t, ht⟩) hfix
  have hf_eq (t : ℝ) (ht : t ∈ Icc 0 b) : f γstar t = X (γ t) := by
    simp only [f, projIcc_of_mem hb.le ht, hγ_eq t ht]
  refine ⟨γ, by simp [γ], fun t ht ↦ hγ_eq t ht ▸ (hS_mem γstar ⟨t, ht⟩).1,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [γ, add_right_inj]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    exact hf_eq s ⟨hs.1, hs.2.trans ht.2⟩
  · have hd := ((hf_cont γstar).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x
    rw [hf_eq t ht] at hd
    exact hd.hasDerivWithinAt

/-- **Uniform local forward existence, spatial Lipschitz dependence, and joint continuity** of
`forwardSemiflow` around a point `x₀ ∈ U ∩ C` where `X x₀ ∈ strictInwardCone C x₀`. -/
theorem exists_local_forwardSemiflow_continuousOn {C U : Set E} (hC : Convex ℝ C)
    (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) {x₀ : E} (hx₀ : x₀ ∈ U ∩ C)
    (hX_in : X x₀ ∈ strictInwardCone C x₀) :
    ∃ r > 0, ∃ τ > 0, ∃ K KΦ : ℝ≥0,
      ball x₀ (2 * r) ⊆ U ∧
      LipschitzOnWith K X (ball x₀ (2 * r) ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y = y + ∫ s in (0 : ℝ)..t,
          X (forwardSemiflow X (U ∩ C) s y)) ∧
      (∀ t ∈ Icc 0 τ,
        LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C)) ∧
      ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  -- Step 1: Choose uniform neighborhood radius `r` and short time `τ`.
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨K, V, hV, hKLipV⟩ := hX hx₀
  obtain ⟨rL, hrL, hballV⟩ := Metric.mem_nhdsWithin_iff.mp hV
  obtain ⟨ε, hε, δ, hδ, hev⟩ := hC.exists_uniform_ball_subset_of_mem_strictInwardCone hX_in
  have hpair_cont : ContinuousWithinAt (fun y ↦ (y, X y)) (U ∩ C) x₀ :=
    continuousWithinAt_id.prodMk (hX.continuousOn x₀ hx₀)
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp (hpair_cont.eventually hev)
  set r := min (min rU rL) rI / 3 with hr_def
  have hr : 0 < r := by positivity
  have h2r_rU : 2 * r ≤ rU := by
    linarith [hr_def, min_le_left (min rU rL) rI, min_le_left rU rL]
  have h2r_rL : 2 * r ≤ rL := by
    linarith [hr_def, min_le_left (min rU rL) rI, min_le_right rU rL]
  have hr_rI : r ≤ rI := by
    linarith [hr_def, min_le_right (min rU rL) rI]
  have h2rU : ball x₀ (2 * r) ⊆ U := (ball_subset_ball h2r_rU).trans hballU
  have hKLip : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C) :=
    hKLipV.mono fun y hy ↦ hballV ⟨ball_subset_ball h2r_rL hy.1, h2rU hy.1, hy.2⟩
  set M : ℝ := ‖X x₀‖ + (K : ℝ) * r + ε / 2 + 1 with hM_def
  have hM : 0 < M := by positivity
  set L : ℝ := (K : ℝ) + 1 with hL_def
  have hL : 0 < L := by positivity
  set τ : ℝ := min (min (δ / 4) (r / (4 * M))) (min (ε / (8 * L * M)) (1 / (8 * L)))
  have hτ : 0 < τ := by positivity
  -- Step 2: Construct each trajectory on `[0, 2 * τ]` and identify it with `forwardSemiflow`.
  have htraj (y : E) (hy : y ∈ ball x₀ r ∩ C) :
      Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y ∧
      (∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C) ∧
      (∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y =
        y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y)) := by
    have hyX : ‖X y‖ + ε / 2 < M := by
      have hdist : ‖X y - X x₀‖ ≤ (K : ℝ) * r := by
        calc ‖X y - X x₀‖ ≤ (K : ℝ) * dist y x₀ := by
              simpa [dist_eq_norm] using hKLip.dist_le_mul y
                ⟨ball_subset_ball (by linarith) hy.1, hy.2⟩ x₀
                ⟨mem_ball_self (by positivity), hx₀.2⟩
          _ ≤ (K : ℝ) * r := mul_le_mul_of_nonneg_left hy.1.le K.coe_nonneg
      linarith [hM_def, norm_sub_norm_le (X y) (X x₀)]
    have hin (t : ℝ) (ht : t ∈ Ioc 0 (2 * τ)) :
        closedBall (y + t • X y) (ε / 2 * t) ⊆ C := by
      have hyI : y ∈ ball x₀ rI ∩ (U ∩ C) :=
        ⟨ball_subset_ball hr_rI hy.1,
          h2rU (ball_subset_ball (by linarith) hy.1), hy.2⟩
      have hτ_δ : τ ≤ δ / 4 := (min_le_left _ _).trans (min_le_left _ _)
      have htδ : t < δ := lt_of_le_of_lt ht.2 (by linarith)
      exact (closedBall_subset_ball (mul_lt_mul_of_pos_right (half_lt_self hε) ht.1)).trans
        (hballI hyI hy.2 t ⟨ht.1, htδ⟩)
    obtain ⟨γ, hγ0, hγmem, hγint, hγ'⟩ := exists_Icc_trajectory_of_ball_subset hC_closed hy
      (by positivity : 0 < 2 * τ) hε hKLip hin
      (calc (‖X y‖ + ε / 2) * (2 * τ) < M * (2 * τ) :=
              mul_lt_mul_of_pos_right hyX (by positivity)
        _ ≤ M * (2 * (r / (4 * M))) := by
              gcongr
              exact (min_le_left _ _).trans (min_le_right _ _)
        _ = r / 2 := by have := hM.ne'; field_simp; ring
        _ < r := by linarith)
      (calc (K : ℝ) * ((‖X y‖ + ε / 2) * (2 * τ)) ≤ L * (M * (2 * τ)) := by
              have hKL : (K : ℝ) ≤ L := by linarith [hL_def]
              gcongr
        _ ≤ L * (M * (2 * (ε / (8 * L * M)))) := by
              gcongr
              exact (min_le_right _ _).trans (min_le_left _ _)
        _ = ε / 4 := by have := hL.ne'; have := hM.ne'; field_simp; ring
        _ ≤ ε / 2 := by linarith)
      (calc (K : ℝ) * (2 * τ) ≤ L * (2 * (1 / (8 * L))) := by
              have hKL : (K : ℝ) ≤ L := by linarith [hL_def]
              have hτ_le : τ ≤ 1 / (8 * L) := (min_le_right _ _).trans (min_le_right _ _)
              gcongr
        _ = 1 / 4 := by have := hL.ne'; field_simp; ring
        _ ≤ 1 / 2 := by norm_num)
    have hγU : MapsTo γ (Ico 0 (2 * τ)) (U ∩ C) :=
      fun s hs ↦ ⟨h2rU (hγmem (Ico_subset_Icc_self hs)).1, (hγmem (Ico_subset_Icc_self hs)).2⟩
    have hγ'_Ico : ∀ s ∈ Ico 0 (2 * τ), HasDerivWithinAt γ (X (γ s)) (Ico 0 (2 * τ)) s :=
      fun s hs ↦ (hγ' s (Ico_subset_Icc_self hs)).mono Ico_subset_Icc_self
    have hsub := Ico_subset_forwardSemiflowInterval (by positivity) hγ0 hγU hγ'_Ico
    have heq := eqOn_forwardSemiflow hX (by positivity) hγ0 hγU hγ'_Ico
    have heq' (s : ℝ) (hs : s ∈ Ico 0 (2 * τ)) : forwardSemiflow X (U ∩ C) s y = γ s :=
      (heq hs).symm
    refine ⟨hsub, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [heq' t ⟨ht.1, by linarith [ht.2]⟩]
      exact hγmem ⟨ht.1, by linarith [ht.2]⟩
    · rw [heq' t ⟨ht.1, by linarith [ht.2]⟩, hγint t ⟨ht.1, by linarith [ht.2]⟩]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      rw [heq' s ⟨hs.1, by linarith [hs.2, ht.2]⟩]
  -- Step 3: Deduce spatial Lipschitz continuity via Grönwall and joint continuity.
  set KΦ : ℝ≥0 := ⟨Real.exp ((K : ℝ) * τ), (Real.exp_pos _).le⟩
  have hLipΦ (t : ℝ) (ht : t ∈ Icc 0 τ) :
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun y₁ hy₁ y₂ hy₂ ↦ ?_
    have hIci {y : E} (hy : y ∈ ball x₀ r ∩ C) :
        ∀ s ∈ Ico 0 τ, HasDerivWithinAt (fun u ↦ forwardSemiflow X (U ∩ C) u y)
          (X (forwardSemiflow X (U ∩ C) s y)) (Ici s) s := by
      intro s hs
      refine (hasDerivWithinAt_forwardSemiflow_Ico hX (htraj y hy).1
        ⟨hs.1, by linarith [hs.2]⟩).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Iio (2 * τ), Iio_mem_nhds (by linarith [hs.2]),
        fun u hu ↦ ⟨hs.1.trans hu.2, hu.1⟩⟩
    have hcont {y : E} (hy : y ∈ ball x₀ r ∩ C) :
        ContinuousOn (fun u ↦ forwardSemiflow X (U ∩ C) u y) (Icc 0 τ) :=
      fun s hs ↦ ((hasDerivWithinAt_forwardSemiflow_Ico hX (htraj y hy).1
        ⟨hs.1, by linarith [hs.2]⟩).continuousWithinAt).mono
        fun u hu ↦ ⟨hu.1, by linarith [hu.2]⟩
    have hd := dist_le_of_trajectories_ODE_of_mem (v := fun _ ↦ X)
      (s := fun _ ↦ ball x₀ (2 * r) ∩ C) (fun _ _ ↦ hKLip)
      (hcont hy₁) (hIci hy₁) (fun s hs ↦ (htraj y₁ hy₁).2.1 s (Ico_subset_Icc_self hs))
      (hcont hy₂) (hIci hy₂) (fun s hs ↦ (htraj y₂ hy₂).2.1 s (Ico_subset_Icc_self hs))
      (by simp : dist (forwardSemiflow X (U ∩ C) 0 y₁)
        (forwardSemiflow X (U ∩ C) 0 y₂) ≤ dist y₁ y₂) t ht
    calc dist (forwardSemiflow X (U ∩ C) t y₁) (forwardSemiflow X (U ∩ C) t y₂)
        ≤ dist y₁ y₂ * Real.exp ((K : ℝ) * (t - 0)) := hd
      _ ≤ dist y₁ y₂ * Real.exp ((K : ℝ) * τ) := by
          gcongr
          linarith [ht.2]
      _ = (KΦ : ℝ) * dist y₁ y₂ := mul_comm _ _
  refine ⟨r, hr, τ, hτ, K, KΦ, h2rU, hKLip, fun y hy ↦ (htraj y hy).1,
    fun y hy ↦ (htraj y hy).2.1, fun y hy ↦ (htraj y hy).2.2, hLipΦ,
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ KΦ hLipΦ fun y hy s hs ↦
      ((hasDerivWithinAt_forwardSemiflow_Ico hX (htraj y hy).1
        ⟨hs.1, by linarith [hs.2]⟩).continuousWithinAt).mono
        fun u hu ↦ ⟨hu.1, by linarith [hu.2]⟩⟩

/-- At any point `x ∈ U ∩ C` where a locally Lipschitz field `X` is strictly inward to the closed
convex set `C`, `0` belongs to `forwardSemiflowInterval X (U ∩ C) x`. -/
theorem zero_mem_forwardSemiflowInterval {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x : E} (hx : x ∈ U ∩ C)
    (hX_in : X x ∈ strictInwardCone C x) :
    (0 : ℝ) ∈ forwardSemiflowInterval X (U ∩ C) x := by
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, _, _, _, _⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hx hX_in
  exact hsub x ⟨mem_ball_self hr, hx.2⟩ ⟨le_rfl, by positivity⟩

/-- Propagation of local existence and joint continuity of `forwardSemiflow` up to any time
`T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
theorem exists_continuousOn_Icc_of_mem_forwardSemiflowInterval {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {x₀ : E} {T : ℝ}
    (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (T + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      ContinuousOn (uncurry (forwardSemiflow X (U ∩ C)))
        (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  let Φ := forwardSemiflow X (U ∩ C)
  let P : ℝ → Prop := fun t ↦ ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
    (∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
    ContinuousOn (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C))
  have hP_ext {t r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hrU : ball x₀ r ⊆ U)
      (hsub : ∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y)
      (hcont : ContinuousOn (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C)))
      {u : ℝ} (hu : u ≤ t + δ / 2) : P u :=
    ⟨r, hr, δ / 4, by positivity, hrU, fun y hy ↦
      (Ico_subset_Ico_right (by linarith)).trans (hsub y hy),
      hcont.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)⟩
  by_contra hnotPT
  -- Step 1: Take the infimum `b` of times in `[0, T]` where `P` fails and show `0 < b`.
  let B : Set ℝ := {t ∈ Icc 0 T | ¬ P t}
  have hBne : B.Nonempty := ⟨T, ⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  have hBbdd : BddBelow B := ⟨0, fun t ht ↦ ht.1.1⟩
  set b := sInf B
  have hb0 : 0 ≤ b := le_csInf hBne fun t ht ↦ ht.1.1
  have hbT : b ≤ T := csInf_le hBbdd ⟨⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  obtain ⟨r₀, hr₀, τ₀, hτ₀, _, _, h2r₀U, _, hsub₀, _, _, _, hcont₀⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hx₀ (hX_in x₀ hx₀)
  have hb_pos : 0 < b := by
    have hle : τ₀ / 4 ≤ b := le_csInf hBne fun t ht ↦ by
      by_contra hlt
      exact ht.2 (hP_ext (t := 0) hr₀ (half_pos hτ₀)
        ((ball_subset_ball (by linarith)).trans h2r₀U)
        (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub₀ y hy))
        (hcont₀.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)) (by linarith))
    linarith
  -- Step 2: Apply local existence at `Φ b x₀` and step from `s < b` across `b` via the cocycle.
  have hbJ : b ∈ forwardSemiflowInterval X (U ∩ C) x₀ :=
    Icc_subset_of_mem_forwardSemiflowInterval hT ⟨hb0, hbT⟩
  have hzU : Φ b x₀ ∈ U ∩ C := forwardSemiflow_mem hX hbJ
  obtain ⟨rz, hrz, τz, hτz, _, _, _, _, hsubz, _, _, _, hcontz⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hzU (hX_in _ hzU)
  have hcont_b : ContinuousAt (fun t ↦ Φ t x₀) b :=
    (hasDerivAt_forwardSemiflow hX hbJ hb_pos).continuousAt
  obtain ⟨η₀, hη₀, hclose_b⟩ := Metric.continuousAt_iff.mp hcont_b rz hrz
  set η := min (b / 2) (min (η₀ / 2) (τz / 3))
  have hη : 0 < η := by positivity
  set s := b - η
  have hs_pos : 0 < s := by linarith [min_le_left (b / 2) (min (η₀ / 2) (τz / 3))]
  have hs_lt_b : s < b := sub_lt_self b hη
  have hbs_le : b - s ≤ τz / 3 := by
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_right (η₀ / 2) (τz / 3)]
  have hΦs_mem : Φ s x₀ ∈ ball (Φ b x₀) rz := by
    refine hclose_b ?_
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt_b)]
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_left (η₀ / 2) (τz / 3)]
  have hPs : P s := by
    by_contra hnotPs
    exact not_lt_of_ge (csInf_le hBbdd ⟨⟨hs_pos.le, hs_lt_b.le.trans hbT⟩, hnotPs⟩) hs_lt_b
  obtain ⟨rs, hrs, δs, hδs, hrsU, hsubs, hconts⟩ := hPs
  have hΦs_cont : ContinuousOn (fun y ↦ Φ s y) (ball x₀ rs ∩ C) :=
    hconts.comp (continuousOn_const.prodMk continuousOn_id)
      fun y hy ↦ ⟨⟨hs_pos.le, by linarith⟩, hy⟩
  obtain ⟨rc, hrc, hballc⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hΦs_cont x₀ ⟨mem_ball_self hrs, hx₀.2⟩).eventually (isOpen_ball.mem_nhds hΦs_mem))
  set r' := min rs rc
  have hr' : 0 < r' := lt_min hrs hrc
  have hΦs_ball (y : E) (hy : y ∈ ball x₀ r' ∩ C) : Φ s y ∈ ball (Φ b x₀) rz ∩ C := by
    have hy_rs : y ∈ ball x₀ rs ∩ C := ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    have hy_rc : y ∈ ball x₀ rc ∩ (ball x₀ rs ∩ C) :=
      ⟨ball_subset_ball (min_le_right _ _) hy.1, hy_rs⟩
    exact ⟨hballc hy_rc, (forwardSemiflow_mem hX
      (hsubs y hy_rs ⟨hs_pos.le, by linarith⟩)).2⟩
  have hsub_all (y : E) (hy : y ∈ ball x₀ r' ∩ C) :
      Ico 0 (s + 2 * τz) ⊆ forwardSemiflowInterval X (U ∩ C) y := by
    intro t ht
    have hy_rs : y ∈ ball x₀ rs ∩ C := ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    have hsJ : s ∈ forwardSemiflowInterval X (U ∩ C) y :=
      hsubs y hy_rs ⟨hs_pos.le, by linarith⟩
    rcases le_or_gt t s with hts | hst
    · exact Icc_subset_of_mem_forwardSemiflowInterval hsJ ⟨ht.1, hts⟩
    · have huJ : t - s ∈ forwardSemiflowInterval X (U ∩ C) (Φ s y) :=
        hsubz (Φ s y) (hΦs_ball y hy) ⟨by linarith, by linarith [ht.2]⟩
      have hadd := (add_mem_forwardSemiflowInterval_iff hX hsJ (by linarith)).mpr huJ
      rw [sub_add_cancel] at hadd
      exact hadd
  -- Step 3: Glue joint continuity across the overlap `[s, min (s + δs) (s + τz)]`.
  have hstep_cont : ContinuousOn (uncurry Φ) (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) := by
    let stepMap : ℝ × E → ℝ × E := fun p ↦ (p.1 - s, Φ s p.2)
    have hstepMap_cont : ContinuousOn stepMap (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) :=
      (continuousOn_fst.sub continuousOn_const).prodMk
        ((hΦs_cont.mono (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _)))).comp
          continuousOn_snd fun p hp ↦ hp.2)
    have hstepMap_maps : MapsTo stepMap (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C))
        (Icc 0 τz ×ˢ (ball (Φ b x₀) rz ∩ C)) := fun p hp ↦
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hΦs_ball p.2 hp.2⟩
    refine (hcontz.comp hstepMap_cont hstepMap_maps).congr fun p hp ↦ ?_
    have hsJ : s ∈ forwardSemiflowInterval X (U ∩ C) p.2 :=
      hsub_all p.2 hp.2 ⟨hs_pos.le, by linarith⟩
    have huJ : p.1 - s ∈ forwardSemiflowInterval X (U ∩ C) (Φ s p.2) :=
      hsubz (Φ s p.2) (hΦs_ball p.2 hp.2) ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    have heq := forwardSemiflow_add hX hsJ huJ
    rw [sub_add_cancel] at heq
    exact heq
  have hglue : ContinuousOn (uncurry Φ) (Icc 0 (s + τz) ×ˢ (ball x₀ r' ∩ C)) := by
    set T₁ := min (s + δs) (s + τz)
    have hT₁ : s < T₁ := lt_min (by linarith) (by linarith)
    intro p hp
    rcases lt_or_ge p.1 T₁ with hlt | hge
    · have hp₁ : p ∈ Icc 0 (s + δs) ×ˢ (ball x₀ rs ∩ C) :=
        ⟨⟨hp.1.1, hlt.le.trans (min_le_left _ _)⟩,
          ball_subset_ball (min_le_left _ _) hp.2.1, hp.2.2⟩
      refine (hconts p hp₁).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Iio T₁ ×ˢ ball x₀ rs, (isOpen_Iio.prod isOpen_ball).mem_nhds ⟨hlt, hp₁.2.1⟩,
        fun q hq ↦ ⟨⟨hq.2.1.1, hq.1.1.le.trans (min_le_left _ _)⟩, hq.1.2, hq.2.2.2⟩⟩
    · have hgt : s < p.1 := hT₁.trans_le hge
      refine (hstep_cont p ⟨⟨hgt.le, hp.1.2⟩, hp.2⟩).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Ioi s ×ˢ univ, (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hgt, trivial⟩,
        fun q hq ↦ ⟨⟨hq.1.1.le, hq.2.1.2⟩, hq.2.2⟩⟩
  have hb_contra : b + τz / 6 ≤ b := le_csInf hBne fun t ht ↦ by
    by_contra hlt
    exact ht.2 (hP_ext (t := b) hr' (by positivity : 0 < τz / 3)
      ((ball_subset_ball (min_le_left _ _)).trans hrsU)
      (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub_all y hy))
      (hglue.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl))
      (by linarith))
  linarith

/-- **Relative openness of the maximal forward semiflow domain.** If `X` is locally Lipschitz on
`U ∩ C` and strictly inward to the closed convex set `C` at every point of `U ∩ C`, then
`forwardSemiflowDomain X (U ∩ C)` is open in the subspace topology of `Ici 0 ×ˢ (U ∩ C)`. -/
theorem exists_isOpen_forwardSemiflowDomain {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ∃ Ω : Set (ℝ × E), IsOpen Ω ∧
      forwardSemiflowDomain X (U ∩ C) = Ω ∩ (Ici 0 ×ˢ (U ∩ C)) := by
  have hloc (p : forwardSemiflowDomain X (U ∩ C)) :
      ∃ W : Set (ℝ × E), IsOpen W ∧ p.1 ∈ W ∧
        W ∩ (Ici 0 ×ˢ (U ∩ C)) ⊆ forwardSemiflowDomain X (U ∩ C) := by
    obtain ⟨r, hr, δ, hδ, _, hsub, _⟩ :=
      exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hX hX_in
        p.2.1 p.2.2
    refine ⟨Iio (p.1.1 + 2 * δ) ×ˢ ball p.1.2 r, isOpen_Iio.prod isOpen_ball,
      ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun q hq ↦ ?_⟩
    exact ⟨hq.2.2, hsub q.2 ⟨hq.1.2, hq.2.2.2⟩ ⟨hq.2.1, hq.1.1⟩⟩
  choose W hW_open hpW hW_sub using hloc
  refine ⟨⋃ p, W p, isOpen_iUnion hW_open, Subset.antisymm (fun q hq ↦ ?_) (fun q hq ↦ ?_)⟩
  · exact ⟨mem_iUnion.mpr ⟨⟨q, hq⟩, hpW ⟨q, hq⟩⟩,
      nonneg_of_mem_forwardSemiflowInterval hq.2, hq.1⟩
  · obtain ⟨p, hqp⟩ := mem_iUnion.mp hq.1
    exact hW_sub p ⟨hqp, hq.2⟩

/-- **Joint continuity of the maximal forward semiflow.** If `X` is locally Lipschitz on `U ∩ C`
and strictly inward to the closed convex set `C` on `U ∩ C`, then
`uncurry (forwardSemiflow X (U ∩ C))` is continuous on `forwardSemiflowDomain X (U ∩ C)`. -/
theorem continuousOn_forwardSemiflow {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (forwardSemiflowDomain X (U ∩ C)) := by
  intro p hp
  obtain ⟨r, hr, δ, hδ, _, _, hcont⟩ :=
    exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hX hX_in hp.1 hp.2
  refine (hcont p ⟨⟨nonneg_of_mem_forwardSemiflowInterval hp.2, by linarith⟩,
    mem_ball_self hr, hp.1.2⟩).mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Iio (p.1 + δ) ×ˢ ball p.2 r, (isOpen_Iio.prod isOpen_ball).mem_nhds
    ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun q hq ↦
      ⟨⟨nonneg_of_mem_forwardSemiflowInterval hq.2.2, hq.1.1.le⟩, hq.1.2, hq.2.1.2⟩⟩

end LocalExistenceAndContinuity

/-! ### Forward compact escape and global forward completeness -/

section EscapeAndGlobal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any finite least upper bound of a `forwardSemiflowInterval` containing `0` is strictly
positive. -/
theorem pos_of_isLUB_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (h0 : (0 : ℝ) ∈ forwardSemiflowInterval X S x)
    (hb : IsLUB (forwardSemiflowInterval X S x) b) : 0 < b := by
  obtain ⟨c, hc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval h0
  have hc2 : c / 2 ∈ forwardSemiflowInterval X S x := hsub ⟨by linarith, by linarith⟩
  exact lt_of_lt_of_le (half_pos hc) (hb.1 hc2)

/-- If `forwardSemiflowInterval X S x` has a finite least upper bound `b`, then it equals
`Ico 0 b`. -/
theorem eq_Ico_of_isLUB_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (hb : IsLUB (forwardSemiflowInterval X S x) b) :
    forwardSemiflowInterval X S x = Ico 0 b := by
  refine Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨c, htc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
    have hmid : (t + c) / 2 ∈ forwardSemiflowInterval X S x :=
      hsub ⟨by linarith [nonneg_of_mem_forwardSemiflowInterval ht], by linarith⟩
    exact ⟨nonneg_of_mem_forwardSemiflowInterval ht,
      lt_of_lt_of_le (by linarith) (hb.1 hmid)⟩
  · obtain ⟨s, hs, hts, _⟩ := hb.exists_between ht.2
    exact Icc_subset_of_mem_forwardSemiflowInterval hs ⟨ht.1, hts.le⟩

/-- **No cluster point in `U ∩ C` at a finite forward endpoint.** If `b` is the least upper bound
of `forwardSemiflowInterval X (U ∩ C) x`, then `forwardSemiflow X (U ∩ C) · x` cannot accumulate
at any point `z ∈ U ∩ C` as `t → b⁻`. -/
theorem not_mapClusterPt_nhdsLT_forwardSemiflow [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x z : E} {b : ℝ} (hx : x ∈ U ∩ C)
    (hb : IsLUB (forwardSemiflowInterval X (U ∩ C) x) b) (hz : z ∈ U ∩ C) :
    ¬ MapClusterPt z (𝓝[<] b) (fun t ↦ forwardSemiflow X (U ∩ C) t x) := by
  intro hcl
  have h0 := zero_mem_forwardSemiflowInterval hC hC_closed hU hX hx (hX_in x hx)
  have hb_pos := pos_of_isLUB_forwardSemiflowInterval h0 hb
  have hIco := eq_Ico_of_isLUB_forwardSemiflowInterval hb
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, _, _, _, _⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hz (hX_in z hz)
  have hIoo : Ioo (max 0 (b - τ)) b ∈ 𝓝[<] b :=
    Ioo_mem_nhdsLT (max_lt hb_pos (sub_lt_self b hτ))
  obtain ⟨s, hs_ball, hs_Ioo⟩ :=
    ((hcl.frequently (Metric.ball_mem_nhds z hr)).and_eventually hIoo).exists
  have hsJ : s ∈ forwardSemiflowInterval X (U ∩ C) x := by
    rw [hIco]
    exact ⟨(le_max_left 0 (b - τ)).trans hs_Ioo.1.le, hs_Ioo.2⟩
  have hΦs_mem : forwardSemiflow X (U ∩ C) s x ∈ ball z r ∩ C :=
    ⟨hs_ball, (forwardSemiflow_mem hX hsJ).2⟩
  have huJ : b - s + τ / 2 ∈
      forwardSemiflowInterval X (U ∩ C) (forwardSemiflow X (U ∩ C) s x) :=
    hsub _ hΦs_mem ⟨by linarith [hs_Ioo.2],
      by linarith [(le_max_right 0 (b - τ)).trans_lt hs_Ioo.1]⟩
  have hadd := (add_mem_forwardSemiflowInterval_iff hX hsJ
    (by linarith [hs_Ioo.2, hτ])).mpr huJ
  have hle := hb.1 hadd
  linarith

/-- **Forward compact-escape lemma.** At a finite least upper bound `b` of
`forwardSemiflowInterval X (U ∩ C) x`, the trajectory leaves every compact subset `K ⊆ U ∩ C`
as `t → b⁻`. -/
theorem eventually_notMem_nhdsLT_forwardSemiflow [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x : E} {b : ℝ} (hx : x ∈ U ∩ C)
    (hb : IsLUB (forwardSemiflowInterval X (U ∩ C) x) b) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U ∩ C) :
    ∀ᶠ t in 𝓝[<] b, forwardSemiflow X (U ∩ C) t x ∉ K := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_not] at h
  obtain ⟨z, hzK, hz⟩ := hK.exists_mapClusterPt_of_frequently h
  exact not_mapClusterPt_nhdsLT_forwardSemiflow hC hC_closed hU hX hX_in hx hb (hKU hzK) hz

/-- **Global forward existence under compact trapping.** If a trajectory of `forwardSemiflow` stays
inside a compact subset `K ⊆ U ∩ C`, then it is defined on all of `[0, ∞)`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x : E} (hx : x ∈ U ∩ C) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U ∩ C)
    (hmem : MapsTo (fun t ↦ forwardSemiflow X (U ∩ C) t x)
      (forwardSemiflowInterval X (U ∩ C) x) K) :
    forwardSemiflowInterval X (U ∩ C) x = Ici 0 := by
  have h0 := zero_mem_forwardSemiflowInterval hC hC_closed hU hX hx (hX_in x hx)
  have hup : ¬ BddAbove (forwardSemiflowInterval X (U ∩ C) x) := fun hbdd ↦ by
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    have hb_pos := pos_of_isLUB_forwardSemiflowInterval h0 hlub
    have hIco := eq_Ico_of_isLUB_forwardSemiflowInterval hlub
    obtain ⟨t, ht, htK⟩ := ((eventually_mem_set.mpr (Ioo_mem_nhdsLT hb_pos)).and
      (eventually_notMem_nhdsLT_forwardSemiflow hC hC_closed hU hX hX_in hx hlub hK hKU)).exists
    exact htK (hmem (hIco.symm ▸ ⟨ht.1.le, ht.2⟩))
  refine Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) (fun t ht ↦ ?_)
  obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.mp hup t
  exact Icc_subset_of_mem_forwardSemiflowInterval hs ⟨ht, hts.le⟩

/-- **Global forward completeness on a compact convex set.** Every locally Lipschitz strictly inward
vector field on a compact convex set `C` generates a forward semiflow defined for all `t ≥ 0`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact [CompleteSpace E] {C : Set E}
    (hC : Convex ℝ C) (hC_compact : IsCompact C) {X : E → E} (hX : LocallyLipschitzOn C X)
    (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  have h := forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo hC hC_compact.isClosed
    isOpen_univ (by simpa only [univ_inter] using hX)
    (fun y hy ↦ hX_in y hy.2) ⟨trivial, hx⟩ hC_compact (fun y hy ↦ ⟨trivial, hy⟩)
    fun t ht ↦ (forwardSemiflow_mem (by simpa only [univ_inter] using hX) ht).2
  simpa only [univ_inter] using h

/-- **Global forward completeness via a proper Lyapunov / exhaustion function.** If `C` is closed
and convex, `f : E → ℝ` is continuous on `C` with compact sublevel sets `{y ∈ C | f y ≤ R}`, and
`f` is differentiable on `interior C` with `df y (X y) ≤ c`, then every forward trajectory of a
locally Lipschitz strictly inward field `X` on `C` is defined on all of `[0, ∞)`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel [CompleteSpace E] {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) {X : E → E} (hX : LocallyLipschitzOn C X)
    (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y) {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {c : ℝ}
    (hf_cont : ContinuousOn f C) (hf_deriv : ∀ y ∈ interior C, HasFDerivAt f (df y) y)
    (hf_le : ∀ y ∈ interior C, df y (X y) ≤ c)
    (hf_compact : ∀ R : ℝ, IsCompact {y ∈ C | f y ≤ R}) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  have hX' : LocallyLipschitzOn (univ ∩ C) X := by simpa only [univ_inter] using hX
  have hX_in' : ∀ y ∈ univ ∩ C, X y ∈ strictInwardCone C y := fun y hy ↦ hX_in y hy.2
  have hx' : x ∈ univ ∩ C := ⟨trivial, hx⟩
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X C x := by
    simpa only [univ_inter] using
      zero_mem_forwardSemiflowInterval hC hC_closed isOpen_univ hX' hx' (hX_in x hx)
  have hup : ¬ BddAbove (forwardSemiflowInterval X C x) := fun hbdd ↦ by
    set b := sSup (forwardSemiflowInterval X C x)
    have hlub : IsLUB (forwardSemiflowInterval X C x) b := isLUB_csSup ⟨0, h0⟩ hbdd
    have hb_pos := pos_of_isLUB_forwardSemiflowInterval h0 hlub
    have hIco := eq_Ico_of_isLUB_forwardSemiflowInterval hlub
    set c' := max c 0
    have hc' : 0 ≤ c' := le_max_right _ _
    set R := f x + c' * b
    have htrap : ∀ T ∈ Ioo 0 b, forwardSemiflow X C T x ∈ {y ∈ C | f y ≤ R} := by
      intro T hT
      have hTJ : T ∈ forwardSemiflowInterval X C x := hIco ▸ ⟨hT.1.le, hT.2⟩
      refine ⟨forwardSemiflow_mem hX hTJ, ?_⟩
      let g : ℝ → ℝ := fun s ↦ f (forwardSemiflow X C s x) - c' * s
      have hΦ_cont : ContinuousOn (fun s ↦ forwardSemiflow X C s x) (Icc 0 T) :=
        fun s hs ↦ ((hasDerivWithinAt_forwardSemiflow hX
          (Icc_subset_of_mem_forwardSemiflowInterval hTJ hs)).continuousWithinAt).mono
          (Icc_subset_of_mem_forwardSemiflowInterval hTJ)
      have hg_cont : ContinuousOn g (Icc 0 T) :=
        (hf_cont.comp hΦ_cont fun s hs ↦
          forwardSemiflow_mem hX
            (Icc_subset_of_mem_forwardSemiflowInterval hTJ hs)).sub
          (continuousOn_const.mul continuousOn_id)
      have hg_anti : AntitoneOn g (Icc 0 T) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos
          (f' := fun s ↦ df (forwardSemiflow X C s x) (X (forwardSemiflow X C s x)) - c')
          (convex_Icc 0 T) hg_cont (fun s hs ↦ ?_) (fun s hs ↦ ?_)
        · rw [interior_Icc] at hs
          have hsJ : s ∈ forwardSemiflowInterval X C x :=
            Icc_subset_of_mem_forwardSemiflowInterval hTJ (Ioo_subset_Icc_self hs)
          have hintC : forwardSemiflow X C s x ∈ interior C :=
            forwardSemiflow_mem_interior hC Subset.rfl hX hX_in hsJ hs.1
          have hdΦ := hasDerivAt_forwardSemiflow hX hsJ hs.1
          have hdf_s := (hf_deriv _ hintC).comp_hasDerivAt s hdΦ
          exact ((hdf_s.sub ((hasDerivAt_id' s).const_mul c')).congr_deriv
            (by ring)).hasDerivWithinAt
        · rw [interior_Icc] at hs
          have hsJ : s ∈ forwardSemiflowInterval X C x :=
            Icc_subset_of_mem_forwardSemiflowInterval hTJ (Ioo_subset_Icc_self hs)
          have hintC : forwardSemiflow X C s x ∈ interior C :=
            forwardSemiflow_mem_interior hC Subset.rfl hX hX_in hsJ hs.1
          linarith [hf_le _ hintC, le_max_left c 0]
      have hle0T := hg_anti ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1.le
      simp only [g, forwardSemiflow_zero, mul_zero, sub_zero] at hle0T
      have hc'T : c' * T ≤ c' * b := mul_le_mul_of_nonneg_left hT.2.le hc'
      linarith
    have hesc : ∀ᶠ t in 𝓝[<] b, forwardSemiflow X C t x ∉ {y ∈ C | f y ≤ R} := by
      simpa only [univ_inter] using
        eventually_notMem_nhdsLT_forwardSemiflow hC hC_closed isOpen_univ hX' hX_in' hx'
          (by simpa only [univ_inter] using hlub) (hf_compact R) (fun y hy ↦ ⟨trivial, hy.1⟩)
    obtain ⟨t, ht, htK⟩ :=
      ((eventually_mem_set.mpr (Ioo_mem_nhdsLT hb_pos)).and hesc).exists
    exact htK (htrap t ht)
  refine Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) (fun t ht ↦ ?_)
  obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.mp hup t
  exact Icc_subset_of_mem_forwardSemiflowInterval hs ⟨ht, hts.le⟩

/-- When every trajectory starting in `C` is globally forward complete, `forwardSemiflowDomain X C`
is equal to `Ici 0 ×ˢ C`. -/
theorem forwardSemiflowDomain_eq_Ici_prod {X : E → E} {C : Set E}
    (hglob : ∀ x ∈ C, forwardSemiflowInterval X C x = Ici 0) :
    forwardSemiflowDomain X C = Ici 0 ×ˢ C := by
  ext p
  simp only [mem_forwardSemiflowDomain_iff, mem_prod]
  constructor
  · rintro ⟨hpC, hpI⟩
    rw [hglob p.2 hpC] at hpI
    exact ⟨hpI, hpC⟩
  · rintro ⟨hpI, hpC⟩
    rw [hglob p.2 hpC]
    exact ⟨hpC, hpI⟩

end EscapeAndGlobal

/-! ### Closed-form model checks -/

section ModelExamples

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the constant inward field `X = 1`
has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_const_one_Ici {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflowInterval (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) x = Ici 0 := by
  refine Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) (fun t ht ↦ ?_)
  exact Ico_subset_forwardSemiflowInterval (b := t + 1) (by linarith [mem_Ici.mp ht])
    (add_zero x) (fun s hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
    (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt)
    ⟨ht, lt_add_one t⟩

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the forward semiflow of the constant
inward field `X = 1` is `forwardSemiflow (fun _ ↦ 1) (Ici 0) t x = x + t`. -/
theorem forwardSemiflow_const_one_Ici {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflow (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) t x = x + t := by
  have hLip : LocallyLipschitzOn (Ici (0 : ℝ)) (fun _ : ℝ ↦ (1 : ℝ)) :=
    (LipschitzWith.const (1 : ℝ)).locallyLipschitz.locallyLipschitzOn
  exact (eqOn_forwardSemiflow hLip (γ := fun s ↦ x + s) (b := t + 1) (by linarith) (add_zero x)
    (fun s hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
    (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt) ⟨ht, lt_add_one t⟩).symm

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the affine inward field
`X y = 1 / 2 - y` has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_half_sub_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflowInterval (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) x = Ici 0 := by
  refine Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) (fun t ht ↦ ?_)
  let γ : ℝ → ℝ := fun s ↦ 1 / 2 + (x - 1 / 2) * Real.exp (-s)
  have hγ_maps : MapsTo γ (Ico 0 (t + 1)) (Icc (0 : ℝ) 1) := fun s hs ↦ by
    have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
    have hexp_le : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    dsimp only [γ]
    exact ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩
  have hγ_deriv (s : ℝ) (_ : s ∈ Ico 0 (t + 1)) :
      HasDerivWithinAt γ (1 / 2 - γ s) (Ico 0 (t + 1)) s := by
    have hd := (((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id' s).neg).const_mul
      (x - 1 / 2)).const_add (1 / 2 : ℝ)
    exact (hd.congr_deriv (by simp [γ])).hasDerivWithinAt
  exact Ico_subset_forwardSemiflowInterval (by linarith [mem_Ici.mp ht]) (by simp [γ])
    hγ_maps hγ_deriv ⟨ht, lt_add_one t⟩

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the forward semiflow of the affine
inward field `X y = 1 / 2 - y` is `1 / 2 + (x - 1 / 2) * exp (-t)`. -/
theorem forwardSemiflow_half_sub_Icc {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflow (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) t x =
      1 / 2 + (x - 1 / 2) * Real.exp (-t) := by
  let γ : ℝ → ℝ := fun s ↦ 1 / 2 + (x - 1 / 2) * Real.exp (-s)
  have hLip : LocallyLipschitzOn (Icc (0 : ℝ) 1) (fun y : ℝ ↦ 1 / 2 - y) :=
    ((LipschitzWith.const (1 / 2 : ℝ)).sub LipschitzWith.id).locallyLipschitz.locallyLipschitzOn
  have hγ_maps : MapsTo γ (Ico 0 (t + 1)) (Icc (0 : ℝ) 1) := fun s hs ↦ by
    have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
    have hexp_le : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    dsimp only [γ]
    exact ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩
  have hγ_deriv (s : ℝ) (_ : s ∈ Ico 0 (t + 1)) :
      HasDerivWithinAt γ (1 / 2 - γ s) (Ico 0 (t + 1)) s := by
    have hd := (((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id' s).neg).const_mul
      (x - 1 / 2)).const_add (1 / 2 : ℝ)
    exact (hd.congr_deriv (by simp [γ])).hasDerivWithinAt
  exact (eqOn_forwardSemiflow hLip (b := t + 1) (by linarith) (by simp [γ]) hγ_maps hγ_deriv
    ⟨ht, lt_add_one t⟩).symm

end ModelExamples

end TauCeti
