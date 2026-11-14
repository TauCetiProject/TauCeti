/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Analysis.Calculus.LocalPotentials.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Topology.Homotopy.Path

/-!
# Curve integrals of covector fields with local potentials along continuous paths

When a covector field `φ : E → E →L[ℝ] F` admits local potentials (`TauCeti.HasLocalPotentials`),
it can be integrated along an arbitrary continuous path `γ : Path a b` without differentiating `γ`
or assuming completeness of the coefficient space `F`: one subdivides `[0, 1]` into finitely many
subintervals mapped into balls carrying local potentials of `φ`, and sums the endpoint differences
of those potentials.

## Main definitions

* `TauCeti.HasLocalPotentialCurveIntegral φ γ v`: `v` is the sum of endpoint differences of local
  potentials of `φ` over a monotone finite subdivision of `[0, 1]` adapted to `γ`.
* `TauCeti.localPotentialCurveIntegral φ γ`: total value of the continuous curve integral, equal to
  the unique `v` satisfying `HasLocalPotentialCurveIntegral φ γ v` when one exists and `0`
  otherwise.
* `TauCeti.localPotentialPrimitive s φ x₀`: candidate global potential obtained by integrating `φ`
  from `x₀` along paths in `s` (returning `0` outside the path component of `x₀` in `s`).

## Main results

* `TauCeti.HasLocalPotentialCurveIntegral.unique`: independence from the choice of subdivision,
  balls, and local potentials.
* `TauCeti.HasLocalPotentials.hasLocalPotentialCurveIntegral`: existence for every continuous path
  in a domain where `φ` has local potentials.
* `TauCeti.localPotentialCurveIntegral_symm`,
  `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_trans`: reversal and concatenation laws,
  together with linearity in `φ` and evaluation on constant covector fields and global primitives.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_map'`: pullback naturality along
  differentiable maps of open sets.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_of_homotopy`: invariance under path
  homotopy relative to endpoints inside the domain.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral`: agreement with
  Mathlib's Bochner `curveIntegral` along `C¹` paths when `F` is complete.
* `TauCeti.HasLocalPotentials.contDiffOn_localPotentialPrimitive`,
  `TauCeti.HasLocalPotentials.hasFDerivAt_localPotentialPrimitive`,
  `TauCeti.HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero`: on a path-connected
  domain, `φ` admits a global `C¹` potential if and only if its integral vanishes over every loop,
  in which case `localPotentialPrimitive s φ x₀` is a `C¹` potential vanishing at `x₀`.

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §§1, 3 (primitives along continuous paths and homotopy invariance).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §§1.3, 4.3 (line integrals of locally
  exact differentials by chains of discs).
-/

public section

open Filter Finset Function MeasureTheory Metric Set
open scoped ContDiff Topology unitInterval

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Subdivision predicate and total curve integral -/

section Defs

variable {a b c d : E} {s : Set E} {φ ψ : E → E →L[ℝ] F}

/-- A covector field `φ` has local-potential curve integral `v` along a continuous path `γ` if
`[0, 1]` admits a finite monotone subdivision whose subintervals map under `γ` into balls on each
of which `φ` is the Fréchet derivative of a function, with `v` equal to the sum of endpoint
differences of those local potentials. -/
def HasLocalPotentialCurveIntegral (φ : E → E →L[ℝ] F) (γ : Path a b) (v : F) : Prop :=
  ∃ (n : ℕ) (t : ℕ → I) (z : ℕ → E) (r : ℕ → ℝ) (g : ℕ → E → F),
    t 0 = 0 ∧ t n = 1 ∧ (∀ i < n, t i ≤ t (i + 1)) ∧
    (∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (ball (z i) (r i))) ∧
    (∀ i < n, ∀ y ∈ ball (z i) (r i), HasFDerivAt (g i) (φ y) y) ∧
    v = ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))

/-- Subdivision characterization of `HasLocalPotentialCurveIntegral`. -/
theorem hasLocalPotentialCurveIntegral_iff {γ : Path a b} {v : F} :
    HasLocalPotentialCurveIntegral φ γ v ↔
      ∃ (n : ℕ) (t : ℕ → I) (z : ℕ → E) (r : ℕ → ℝ) (g : ℕ → E → F),
        t 0 = 0 ∧ t n = 1 ∧ (∀ i < n, t i ≤ t (i + 1)) ∧
        (∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (ball (z i) (r i))) ∧
        (∀ i < n, ∀ y ∈ ball (z i) (r i), HasFDerivAt (g i) (φ y) y) ∧
        v = ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i))) :=
  Iff.rfl

/-- The curve integral of `φ` along a continuous path `γ` computed from local potentials, returning
`0` when no adapted local-potential subdivision exists. -/
noncomputable def localPotentialCurveIntegral (φ : E → E →L[ℝ] F) (γ : Path a b) : F :=
  open Classical in
  if h : ∃ v, HasLocalPotentialCurveIntegral φ γ v then h.choose else 0

private theorem clamp_sub_eq_clamp_sub {γ : Path a b}
    {u₀ u₁ v₀ v₁ : I} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    {z₁ z₂ : E} {r₁ r₂ : ℝ} {g₁ g₂ : E → F}
    (hγ₁ : MapsTo γ (Icc u₀ u₁) (ball z₁ r₁)) (hγ₂ : MapsTo γ (Icc v₀ v₁) (ball z₂ r₂))
    (hd₁ : ∀ w ∈ ball z₁ r₁, HasFDerivAt g₁ (φ w) w)
    (hd₂ : ∀ w ∈ ball z₂ r₂, HasFDerivAt g₂ (φ w) w) :
    g₁ (γ ((v₁ ⊔ u₀) ⊓ u₁)) - g₁ (γ ((v₀ ⊔ u₀) ⊓ u₁)) =
      g₂ (γ ((u₁ ⊔ v₀) ⊓ v₁)) - g₂ (γ ((u₀ ⊔ v₀) ⊓ v₁)) := by
  rcases le_or_gt v₁ u₀ with hvu | huv
  · have hv₀u₀ : v₀ ≤ u₀ := hv.trans hvu
    have h₁ : (v₁ ⊔ u₀) ⊓ u₁ = u₀ := by rw [sup_eq_right.mpr hvu, inf_eq_left.mpr hu]
    have h₂ : (v₀ ⊔ u₀) ⊓ u₁ = u₀ := by rw [sup_eq_right.mpr hv₀u₀, inf_eq_left.mpr hu]
    have h₃ : (u₁ ⊔ v₀) ⊓ v₁ = v₁ := by
      rw [sup_eq_left.mpr (hv₀u₀.trans hu), inf_eq_right.mpr (hvu.trans hu)]
    have h₄ : (u₀ ⊔ v₀) ⊓ v₁ = v₁ := by rw [sup_eq_left.mpr hv₀u₀, inf_eq_right.mpr hvu]
    rw [h₁, h₂, h₃, h₄, sub_self, sub_self]
  · rcases le_or_gt u₁ v₀ with huv' | hvu'
    · have hu₀v₀ : u₀ ≤ v₀ := hu.trans huv'
      have h₁ : (v₁ ⊔ u₀) ⊓ u₁ = u₁ := by
        rw [sup_eq_left.mpr (hu₀v₀.trans hv), inf_eq_right.mpr (huv'.trans hv)]
      have h₂ : (v₀ ⊔ u₀) ⊓ u₁ = u₁ := by rw [sup_eq_left.mpr hu₀v₀, inf_eq_right.mpr huv']
      have h₃ : (u₁ ⊔ v₀) ⊓ v₁ = v₀ := by rw [sup_eq_right.mpr huv', inf_eq_left.mpr hv]
      have h₄ : (u₀ ⊔ v₀) ⊓ v₁ = v₀ := by rw [sup_eq_right.mpr hu₀v₀, inf_eq_left.mpr hv]
      rw [h₁, h₂, h₃, h₄, sub_self, sub_self]
    · have h₁ : (v₁ ⊔ u₀) ⊓ u₁ = u₁ ⊓ v₁ := by rw [sup_eq_left.mpr huv.le, inf_comm]
      have h₂ : (v₀ ⊔ u₀) ⊓ u₁ = u₀ ⊔ v₀ := by
        rw [sup_comm, inf_eq_left.mpr (sup_le hu hvu'.le)]
      have h₃ : (u₁ ⊔ v₀) ⊓ v₁ = u₁ ⊓ v₁ := by rw [sup_eq_left.mpr hvu'.le]
      have h₄ : (u₀ ⊔ v₀) ⊓ v₁ = u₀ ⊔ v₀ := inf_eq_left.mpr (sup_le huv.le hv)
      obtain ⟨c, hc⟩ := (isOpen_ball.inter isOpen_ball).exists_eq_add_of_fderiv_eq
        ((convex_ball z₁ r₁).inter (convex_ball z₂ r₂)).isPreconnected
        (fun w hw ↦ (hd₁ w hw.1).differentiableAt.differentiableWithinAt)
        (fun w hw ↦ (hd₂ w hw.2).differentiableAt.differentiableWithinAt)
        (fun w hw ↦ (hd₁ w hw.1).fderiv.trans (hd₂ w hw.2).fderiv.symm)
      have hx : γ (u₀ ⊔ v₀) ∈ ball z₁ r₁ ∩ ball z₂ r₂ :=
        ⟨hγ₁ ⟨le_sup_left, sup_le hu hvu'.le⟩, hγ₂ ⟨le_sup_right, sup_le huv.le hv⟩⟩
      have hy : γ (u₁ ⊓ v₁) ∈ ball z₁ r₁ ∩ ball z₂ r₂ :=
        ⟨hγ₁ ⟨le_inf hu huv.le, inf_le_left⟩, hγ₂ ⟨le_inf hvu'.le hv, inf_le_right⟩⟩
      rw [h₁, h₂, h₃, h₄, hc hy, hc hx, add_sub_add_right_eq_sub]

/-- The value in `HasLocalPotentialCurveIntegral` is independent of the subdivision, balls, and
local potentials. -/
theorem HasLocalPotentialCurveIntegral.unique {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialCurveIntegral φ γ v₁) (h₂ : HasLocalPotentialCurveIntegral φ γ v₂) :
    v₁ = v₂ := by
  rcases h₁ with ⟨m, t₁, z₁, r₁, g₁, ht₁0, ht₁m, hle₁, hγ₁, hd₁, rfl⟩
  rcases h₂ with ⟨n, t₂, z₂, r₂, g₂, ht₂0, ht₂n, hle₂, hγ₂, hd₂, rfl⟩
  -- Clamp `t₂` to `[t₁ i, t₁ (i + 1)]` and `t₁` to `[t₂ j, t₂ (j + 1)]`, then exchange the sums.
  let τ : ℕ → ℕ → I := fun i j ↦ (t₂ j ⊔ t₁ i) ⊓ t₁ (i + 1)
  let υ : ℕ → ℕ → I := fun i j ↦ (t₁ i ⊔ t₂ j) ⊓ t₂ (j + 1)
  have hτ_sum : ∀ i < m, g₁ i (γ (t₁ (i + 1))) - g₁ i (γ (t₁ i)) =
      ∑ j ∈ Finset.range n, (g₁ i (γ (τ i (j + 1))) - g₁ i (γ (τ i j))) := by
    intro i hi
    rw [Finset.sum_range_sub (fun j ↦ g₁ i (γ (τ i j))) n]
    have h0 : τ i 0 = t₁ i := by
      dsimp only [τ]
      rw [ht₂0, sup_eq_right.mpr unitInterval.nonneg', inf_eq_left.mpr (hle₁ i hi)]
    have hn : τ i n = t₁ (i + 1) := by
      dsimp only [τ]
      rw [ht₂n, sup_eq_left.mpr unitInterval.le_one', inf_eq_right.mpr unitInterval.le_one']
    rw [h0, hn]
  have hυ_sum : ∀ j < n, g₂ j (γ (t₂ (j + 1))) - g₂ j (γ (t₂ j)) =
      ∑ i ∈ Finset.range m, (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))) := by
    intro j hj
    rw [Finset.sum_range_sub (fun i ↦ g₂ j (γ (υ i j))) m]
    have h0 : υ 0 j = t₂ j := by
      dsimp only [υ]
      rw [ht₁0, sup_eq_right.mpr unitInterval.nonneg', inf_eq_left.mpr (hle₂ j hj)]
    have hm : υ m j = t₂ (j + 1) := by
      dsimp only [υ]
      rw [ht₁m, sup_eq_left.mpr unitInterval.le_one', inf_eq_right.mpr unitInterval.le_one']
    rw [h0, hm]
  calc
    ∑ i ∈ Finset.range m, (g₁ i (γ (t₁ (i + 1))) - g₁ i (γ (t₁ i)))
      = ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n, (g₁ i (γ (τ i (j + 1))) - g₁ i (γ (τ i j))) :=
        Finset.sum_congr rfl fun i hi ↦ hτ_sum i (Finset.mem_range.mp hi)
    _ = ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n, (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))) := by
        refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
        exact clamp_sub_eq_clamp_sub (hle₁ i (Finset.mem_range.mp hi))
          (hle₂ j (Finset.mem_range.mp hj)) (hγ₁ i (Finset.mem_range.mp hi))
          (hγ₂ j (Finset.mem_range.mp hj)) (hd₁ i (Finset.mem_range.mp hi))
          (hd₂ j (Finset.mem_range.mp hj))
    _ = ∑ j ∈ Finset.range n,
          ∑ i ∈ Finset.range m, (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range n, (g₂ j (γ (t₂ (j + 1))) - g₂ j (γ (t₂ j))) :=
        Finset.sum_congr rfl fun j hj ↦ (hυ_sum j (Finset.mem_range.mp hj)).symm

/-- A witness for `HasLocalPotentialCurveIntegral` computes `localPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.localPotentialCurveIntegral_eq {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    localPotentialCurveIntegral φ γ = v := by
  have hex : ∃ w, HasLocalPotentialCurveIntegral φ γ w := ⟨v, h⟩
  rw [localPotentialCurveIntegral, dite_eq_left hex]
  exact hex.choose_spec.unique h

/-- When no adapted local-potential subdivision exists, `localPotentialCurveIntegral` returns
`0`. -/
theorem localPotentialCurveIntegral_of_not_exists {γ : Path a b}
    (h : ¬∃ v, HasLocalPotentialCurveIntegral φ γ v) :
    localPotentialCurveIntegral φ γ = 0 := by
  rw [localPotentialCurveIntegral, dite_eq_right h]

/-- Every continuous path in a domain `s` where `φ` has local potentials admits a finite monotone
subdivision of `[0, 1]` whose subintervals map into balls contained in `s` carrying `C¹` local
potentials of `φ`. -/
theorem HasLocalPotentials.exists_subdivision (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    ∃ (n : ℕ) (t : ℕ → I) (z : ℕ → E) (r : ℕ → ℝ) (g : ℕ → E → F),
      t 0 = 0 ∧ t n = 1 ∧ (∀ i < n, t i ≤ t (i + 1)) ∧
      (∀ i < n, ball (z i) (r i) ⊆ s) ∧
      (∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (ball (z i) (r i))) ∧
      (∀ i < n, ContDiffOn ℝ 1 (g i) (ball (z i) (r i))) ∧
      ∀ i < n, ∀ y ∈ ball (z i) (r i), HasFDerivAt (g i) (φ y) y := by
  choose r hr hrs g hg hd using fun x : s ↦ hasLocalPotentials_iff.mp hφ x.1 x.2
  let c : s → Set I := fun x ↦ γ ⁻¹' ball x.1 (r x)
  have hc₁ : ∀ x : s, IsOpen (c x) := fun x ↦ isOpen_ball.preimage γ.continuous
  have hc₂ : (univ : Set I) ⊆ ⋃ x : s, c x := fun τ _ ↦
    mem_iUnion.mpr ⟨⟨γ τ, hγ τ⟩, mem_ball_self (hr ⟨γ τ, hγ τ⟩)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  choose idx hidx using hsub
  exact ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun i ↦ g (idx i), ht0, hn n le_rfl,
    fun i _ ↦ hmono (Nat.le_succ i), fun i _ ↦ hrs (idx i), fun i _ τ hτ ↦ hidx i hτ,
    fun i _ ↦ hg (idx i), fun i _ ↦ hd (idx i)⟩

/-- Every continuous path in a domain with local potentials admits a local-potential curve
integral. -/
theorem HasLocalPotentials.exists_hasLocalPotentialCurveIntegral (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    ∃ v, HasLocalPotentialCurveIntegral φ γ v := by
  obtain ⟨n, t, z, r, g, ht0, htn, hle, -, hmap, -, hd⟩ := hφ.exists_subdivision hγ
  exact ⟨_, n, t, z, r, g, ht0, htn, hle, hmap, hd, rfl⟩

/-- If `φ` has local potentials on `s`, then `localPotentialCurveIntegral φ γ` satisfies
`HasLocalPotentialCurveIntegral` for every continuous path `γ` in `s`. -/
theorem HasLocalPotentials.hasLocalPotentialCurveIntegral (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialCurveIntegral φ γ (localPotentialCurveIntegral φ γ) := by
  obtain ⟨v, hv⟩ := hφ.exists_hasLocalPotentialCurveIntegral hγ
  rwa [hv.localPotentialCurveIntegral_eq]

/-- For a continuous path `γ` inside a domain where `φ` has local potentials, `v` satisfies
`HasLocalPotentialCurveIntegral φ γ v` if and only if `localPotentialCurveIntegral φ γ = v`. -/
theorem HasLocalPotentials.hasLocalPotentialCurveIntegral_iff_eq (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) {v : F} :
    HasLocalPotentialCurveIntegral φ γ v ↔ localPotentialCurveIntegral φ γ = v :=
  ⟨fun h ↦ h.localPotentialCurveIntegral_eq,
    fun h ↦ h ▸ hφ.hasLocalPotentialCurveIntegral hγ⟩

/-- If `φ` is the Fréchet derivative of a global function `g` on an open set `s`, then its
local-potential curve integral along any path in `s` from `a` to `b` is `g b - g a`. -/
theorem hasLocalPotentialCurveIntegral_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hd : ∀ y ∈ s, HasFDerivAt g (φ y) y) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialCurveIntegral φ γ (g b - g a) := by
  choose r hr hrs using fun x : s ↦ Metric.isOpen_iff.mp hs x.1 x.2
  let c : s → Set I := fun x ↦ γ ⁻¹' ball x.1 (r x)
  have hc₁ : ∀ x : s, IsOpen (c x) := fun x ↦ isOpen_ball.preimage γ.continuous
  have hc₂ : (univ : Set I) ⊆ ⋃ x : s, c x := fun τ _ ↦
    mem_iUnion.mpr ⟨⟨γ τ, hγ τ⟩, mem_ball_self (hr ⟨γ τ, hγ τ⟩)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  choose idx hidx using hsub
  refine ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun _ ↦ g, ht0, hn n le_rfl,
    fun i _ ↦ hmono (Nat.le_succ i), fun i _ τ hτ ↦ hidx i hτ,
    fun i _ y hy ↦ hd y (hrs (idx i) hy), ?_⟩
  rw [Finset.sum_range_sub (fun i ↦ g (γ (t i))) n, hn n le_rfl, ht0, γ.target, γ.source]

/-- Evaluating `localPotentialCurveIntegral` on a field with a global primitive `g` on an open set
`s` gives the endpoint difference `g b - g a`. -/
theorem localPotentialCurveIntegral_eq_sub_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hd : ∀ y ∈ s, HasFDerivAt g (φ y) y) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = g b - g a :=
  (hasLocalPotentialCurveIntegral_of_hasFDerivAt hs hd hγ).localPotentialCurveIntegral_eq

end Defs

/-! ### Path operations and algebraic properties -/

section Operations

variable {a b c d : E} {s : Set E} {φ ψ : E → E →L[ℝ] F}

/-- The curve integral along a constant path is zero. -/
@[simp]
theorem localPotentialCurveIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    localPotentialCurveIntegral φ (Path.refl a) = 0 := by
  by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ (Path.refl a) v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialCurveIntegral_eq]
    rcases hv with ⟨n, t, z, r, g, -, -, -, -, -, rfl⟩
    simp
  · exact localPotentialCurveIntegral_of_not_exists h

/-- Casting path endpoints preserves `HasLocalPotentialCurveIntegral`. -/
@[simp]
theorem hasLocalPotentialCurveIntegral_cast_iff {γ : Path a b} {ha : c = a} {hb : d = b} {v : F} :
    HasLocalPotentialCurveIntegral φ (γ.cast ha hb) v ↔
      HasLocalPotentialCurveIntegral φ γ v := by
  subst ha hb
  rfl

/-- Casting path endpoints preserves `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_cast (φ : E → E →L[ℝ] F) (γ : Path a b)
    (ha : c = a) (hb : d = b) :
    localPotentialCurveIntegral φ (γ.cast ha hb) = localPotentialCurveIntegral φ γ := by
  subst ha hb
  rfl

/-- Pointwise equal paths have the same `HasLocalPotentialCurveIntegral` witnesses. -/
theorem HasLocalPotentialCurveIntegral.congr_path {γ₁ γ₂ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ₁ v) (hγ : ∀ t, γ₁ t = γ₂ t) :
    HasLocalPotentialCurveIntegral φ γ₂ v := by
  have heq : γ₁ = γ₂ := Path.ext (funext hγ)
  rwa [← heq]

/-- If two fields agree on `s` and have local potentials on `s`, they have the same curve integral
along every path in `s`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_congr (hφ : HasLocalPotentials s φ)
    (h : EqOn φ ψ s) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = localPotentialCurveIntegral ψ γ := by
  obtain ⟨n, t, z, r, g, ht0, htn, hle, hrs, hmap, -, hd⟩ := hφ.exists_subdivision hγ
  have h₁ : HasLocalPotentialCurveIntegral φ γ
      (∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))) :=
    ⟨n, t, z, r, g, ht0, htn, hle, hmap, hd, rfl⟩
  have h₂ : HasLocalPotentialCurveIntegral ψ γ
      (∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))) :=
    ⟨n, t, z, r, g, ht0, htn, hle, hmap,
      fun i hi y hy ↦ h (hrs i hi hy) ▸ hd i hi y hy, rfl⟩
  rw [h₁.localPotentialCurveIntegral_eq, h₂.localPotentialCurveIntegral_eq]

/-- Reversing a path negates `HasLocalPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.symm {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    HasLocalPotentialCurveIntegral φ γ.symm (-v) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  refine ⟨n, fun k ↦ unitInterval.symm (t (n - k)), fun k ↦ z (n - 1 - k),
    fun k ↦ r (n - 1 - k), fun k ↦ g (n - 1 - k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [htn]
  · simp [ht0]
  · intro k hk
    dsimp only
    have hk1 : n - k = n - 1 - k + 1 := by omega
    have hk2 : n - (k + 1) = n - 1 - k := by omega
    rw [hk1, hk2, ← Subtype.coe_le_coe]
    simp only [unitInterval.coe_symm_eq, sub_le_sub_iff_left]
    exact hle (n - 1 - k) (by omega)
  · intro k hk τ hτ
    have hk1 : n - k = n - 1 - k + 1 := by omega
    have hk2 : n - (k + 1) = n - 1 - k := by omega
    rw [Path.symm_apply, Function.comp_apply]
    refine hγ (n - 1 - k) (by omega) ⟨?_, ?_⟩
    · rw [← Subtype.coe_le_coe]
      have h2 := Subtype.coe_le_coe.mpr hτ.2
      dsimp only at h2
      rw [hk2, unitInterval.coe_symm_eq] at h2
      rw [unitInterval.coe_symm_eq]
      linarith
    · rw [← Subtype.coe_le_coe]
      have h1 := Subtype.coe_le_coe.mpr hτ.1
      dsimp only at h1
      rw [hk1, unitInterval.coe_symm_eq] at h1
      rw [unitInterval.coe_symm_eq]
      linarith
  · intro k hk
    exact hd (n - 1 - k) (by omega)
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k < n := Finset.mem_range.mp hk
    have hk1 : n - k = n - 1 - k + 1 := by omega
    have hk2 : n - (k + 1) = n - 1 - k := by omega
    dsimp only
    simp only [hk1, hk2, Path.symm_apply, Function.comp_apply, unitInterval.symm_symm, neg_sub]

/-- Reversing a path negates `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_symm (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral φ γ.symm = -localPotentialCurveIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialCurveIntegral_eq, hv.symm.localPotentialCurveIntegral_eq]
  · have h' : ¬∃ w, HasLocalPotentialCurveIntegral φ γ.symm w := by
      rintro ⟨w, hw⟩
      exact h ⟨-w, by simpa only [Path.symm_symm, neg_neg] using hw.symm⟩
    rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
      neg_zero]

/-- Concatenating two paths adds their local-potential curve integrals. -/
theorem HasLocalPotentialCurveIntegral.trans {γ₁ : Path a b} {γ₂ : Path b c} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialCurveIntegral φ γ₁ v₁) (h₂ : HasLocalPotentialCurveIntegral φ γ₂ v₂) :
    HasLocalPotentialCurveIntegral φ (γ₁.trans γ₂) (v₁ + v₂) := by
  rcases h₁ with ⟨m, t₁, z₁, r₁, g₁, ht₁0, ht₁m, hle₁, hγ₁, hd₁, rfl⟩
  rcases h₂ with ⟨n, t₂, z₂, r₂, g₂, ht₂0, ht₂n, hle₂, hγ₂, hd₂, rfl⟩
  -- Rescale `t₁` into `[0, 1 / 2]` and `t₂` into `[1 / 2, 1]`, joining at `t m = 1 / 2`.
  have hm_pos : 0 < m := by
    by_contra hm0
    exact zero_ne_one (ht₁0.symm.trans (Nat.eq_zero_of_not_pos hm0 ▸ ht₁m))
  let halfLeft : I → I := fun x ↦ ⟨(x : ℝ) / 2, ⟨by linarith [x.2.1], by linarith [x.2.2]⟩⟩
  let halfRight : I → I := fun x ↦ ⟨((x : ℝ) + 1) / 2, ⟨by linarith [x.2.1], by linarith [x.2.2]⟩⟩
  let t : ℕ → I := fun k ↦ if k < m then halfLeft (t₁ k) else halfRight (t₂ (k - m))
  have ht_left : ∀ i ≤ m, t i = halfLeft (t₁ i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with him | rfl
    · exact ite_eq_left him
    · simp only [t, lt_irrefl, ↓reduceIte, Nat.sub_self, ht₂0, ht₁m]
      ext
      simp [halfLeft, halfRight]
  have ht_right : ∀ j, t (m + j) = halfRight (t₂ j) := fun j ↦ by
    simp [t, Nat.not_lt.mpr (Nat.le_add_right m j)]
  have htrans_left : ∀ x : I, (γ₁.trans γ₂) (halfLeft x) = γ₁ x := fun x ↦
    γ₁.trans_apply_of_eq_two_mul γ₂ x (by simp [halfLeft]; ring)
  have htrans_right : ∀ x : I, (γ₁.trans γ₂) (halfRight x) = γ₂ x := fun x ↦
    γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ x (by simp [halfRight]; ring)
  refine ⟨m + n, t, fun k ↦ if k < m then z₁ k else z₂ (k - m),
    fun k ↦ if k < m then r₁ k else r₂ (k - m),
    fun k ↦ if k < m then g₁ k else g₂ (k - m), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht_left 0 hm_pos.le, ht₁0]
    ext
    simp [halfLeft]
  · rw [ht_right n, ht₂n]
    ext
    simp [halfRight]
  · intro k hk
    by_cases hkm : k < m
    · rw [ht_left k hkm.le, ht_left (k + 1) (Nat.succ_le_of_lt hkm), ← Subtype.coe_le_coe]
      dsimp only [halfLeft]
      linarith [Subtype.coe_le_coe.mpr (hle₁ k hkm)]
    · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, (Nat.add_sub_of_le (Nat.not_lt.mp hkm)).symm⟩
      rw [Nat.add_assoc, ht_right j, ht_right (j + 1), ← Subtype.coe_le_coe]
      dsimp only [halfRight]
      linarith [Subtype.coe_le_coe.mpr (hle₂ j (by omega))]
  · intro k hk τ hτ
    by_cases hkm : k < m
    · simp only [ite_eq_left hkm, ht_left k hkm.le,
        ht_left (k + 1) (Nat.succ_le_of_lt hkm)] at hτ ⊢
      have h1 := Subtype.coe_le_coe.mpr hτ.1
      have h2 := Subtype.coe_le_coe.mpr hτ.2
      have hmem : 2 * (τ : ℝ) ∈ I :=
        ⟨by linarith [τ.2.1], by dsimp only [halfLeft] at h2; linarith [(t₁ (k + 1)).2.2]⟩
      rw [γ₁.trans_apply_of_eq_two_mul γ₂ ⟨2 * τ, hmem⟩ rfl]
      exact hγ₁ k hkm ⟨Subtype.coe_le_coe.mp (by dsimp only [halfLeft] at h1 ⊢; linarith),
        Subtype.coe_le_coe.mp (by dsimp only [halfLeft] at h2 ⊢; linarith)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, (Nat.add_sub_of_le (Nat.not_lt.mp hkm)).symm⟩
      simp only [ite_eq_right hkm, Nat.add_sub_cancel_left, Nat.add_assoc, ht_right j,
        ht_right (j + 1)] at hτ ⊢
      have h1 := Subtype.coe_le_coe.mpr hτ.1
      have h2 := Subtype.coe_le_coe.mpr hτ.2
      have hmem : 2 * (τ : ℝ) - 1 ∈ I :=
        ⟨by dsimp only [halfRight] at h1; linarith [(t₂ j).2.1], by linarith [τ.2.2]⟩
      rw [γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ ⟨2 * τ - 1, hmem⟩ rfl]
      exact hγ₂ j (by omega) ⟨Subtype.coe_le_coe.mp (by dsimp only [halfRight] at h1 ⊢; linarith),
        Subtype.coe_le_coe.mp (by dsimp only [halfRight] at h2 ⊢; linarith)⟩
  · intro k hk
    by_cases hkm : k < m
    · simp only [ite_eq_left hkm]
      exact hd₁ k hkm
    · simp only [ite_eq_right hkm]
      exact hd₂ (k - m) (by omega)
  · rw [Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have him : i < m := Finset.mem_range.mp hi
      simp only [ite_eq_left him, ht_left i him.le, ht_left (i + 1) (Nat.succ_le_of_lt him),
        htrans_left]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hmj : ¬m + j < m := Nat.not_lt.mpr (Nat.le_add_right m j)
      simp only [ite_eq_right hmj, Nat.add_sub_cancel_left, Nat.add_assoc, ht_right, htrans_right]

/-- Concatenating two paths adds `localPotentialCurveIntegral` whenever both paths admit
local-potential subdivisions. -/
theorem localPotentialCurveIntegral_trans {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : ∃ v, HasLocalPotentialCurveIntegral φ γ₁ v)
    (h₂ : ∃ v, HasLocalPotentialCurveIntegral φ γ₂ v) :
    localPotentialCurveIntegral φ (γ₁.trans γ₂) =
      localPotentialCurveIntegral φ γ₁ + localPotentialCurveIntegral φ γ₂ := by
  obtain ⟨v₁, hv₁⟩ := h₁
  obtain ⟨v₂, hv₂⟩ := h₂
  rw [hv₁.localPotentialCurveIntegral_eq, hv₂.localPotentialCurveIntegral_eq,
    (hv₁.trans hv₂).localPotentialCurveIntegral_eq]

/-- Concatenating two paths inside a domain with local potentials adds their curve integrals. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_trans (hφ : HasLocalPotentials s φ)
    {γ₁ : Path a b} {γ₂ : Path b c} (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialCurveIntegral φ (γ₁.trans γ₂) =
      localPotentialCurveIntegral φ γ₁ + localPotentialCurveIntegral φ γ₂ :=
  TauCeti.localPotentialCurveIntegral_trans
    (hφ.exists_hasLocalPotentialCurveIntegral hγ₁)
    (hφ.exists_hasLocalPotentialCurveIntegral hγ₂)

/-- A constant covector field `fun _ ↦ L` has curve integral `L b - L a` along every continuous
path `γ : Path a b`. -/
theorem hasLocalPotentialCurveIntegral_const (L : E →L[ℝ] F) (γ : Path a b) :
    HasLocalPotentialCurveIntegral (fun _ ↦ L) γ (L b - L a) := by
  obtain ⟨R, hR⟩ := (isCompact_range γ.continuous).isBounded.subset_ball (0 : E)
  refine ⟨1, fun k ↦ if k = 0 then 0 else 1, fun _ ↦ 0, fun _ ↦ R, fun _ ↦ L,
    rfl, by simp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    exact zero_le_one
  · intro i _ τ _
    exact hR (mem_range_self τ)
  · intro _ _ _ _
    exact L.hasFDerivAt
  · simp [γ.target, γ.source]

/-- The curve integral of a constant covector field `fun _ ↦ L` along any continuous path is
`L b - L a`. -/
@[simp]
theorem localPotentialCurveIntegral_const (L : E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral (fun _ ↦ L) γ = L b - L a :=
  (hasLocalPotentialCurveIntegral_const L γ).localPotentialCurveIntegral_eq

/-- The curve integral of the zero covector field is zero along every path. -/
@[simp]
theorem localPotentialCurveIntegral_zero (γ : Path a b) :
    localPotentialCurveIntegral (0 : E → E →L[ℝ] F) γ = 0 := by
  rw [Pi.zero_def, localPotentialCurveIntegral_const, zero_apply, zero_apply, sub_self]

/-- Negating a covector field negates `HasLocalPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.neg {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    HasLocalPotentialCurveIntegral (-φ) γ (-v) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  refine ⟨n, t, z, r, fun i ↦ -g i, ht0, htn, hle, hγ,
    fun i hi y hy ↦ (hd i hi y hy).neg, ?_⟩
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.neg_apply]
  abel

/-- Negating a covector field negates `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_neg (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral (-φ) γ = -localPotentialCurveIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialCurveIntegral_eq, hv.neg.localPotentialCurveIntegral_eq]
  · have h' : ¬∃ w, HasLocalPotentialCurveIntegral (-φ) γ w := by
      rintro ⟨w, hw⟩
      exact h ⟨-w, by simpa only [neg_neg] using hw.neg⟩
    rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
      neg_zero]

/-- Scaling a covector field by a real constant scales `HasLocalPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.smul (c : ℝ) {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    HasLocalPotentialCurveIntegral (c • φ) γ (c • v) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  refine ⟨n, t, z, r, fun i ↦ c • g i, ht0, htn, hle, hγ,
    fun i hi y hy ↦ (hd i hi y hy).const_smul c, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_sub]

/-- Scaling a covector field by a real constant scales `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_smul (c : ℝ) (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral (c • φ) γ = c • localPotentialCurveIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
    · obtain ⟨v, hv⟩ := h
      rw [hv.localPotentialCurveIntegral_eq, (hv.smul c).localPotentialCurveIntegral_eq]
    · have h' : ¬∃ w, HasLocalPotentialCurveIntegral (c • φ) γ w := by
        rintro ⟨w, hw⟩
        exact h ⟨c⁻¹ • w, by simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hw.smul c⁻¹⟩
      rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
        smul_zero]

/-- Adding two covector fields with local potentials adds their curve integrals along any path in
their common domain. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_add (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral (φ + ψ) γ =
      localPotentialCurveIntegral φ γ + localPotentialCurveIntegral ψ γ := by
  choose r₁ hr₁ _ g₁ _ hd₁ using fun x : s ↦ hasLocalPotentials_iff.mp hφ x.1 x.2
  choose r₂ hr₂ _ g₂ _ hd₂ using fun x : s ↦ hasLocalPotentials_iff.mp hψ x.1 x.2
  let r : s → ℝ := fun x ↦ min (r₁ x) (r₂ x)
  have hr : ∀ x : s, 0 < r x := fun x ↦ lt_min (hr₁ x) (hr₂ x)
  let c : s → Set I := fun x ↦ γ ⁻¹' ball x.1 (r x)
  have hc₁ : ∀ x : s, IsOpen (c x) := fun x ↦ isOpen_ball.preimage γ.continuous
  have hc₂ : (univ : Set I) ⊆ ⋃ x : s, c x := fun τ _ ↦
    mem_iUnion.mpr ⟨⟨γ τ, hγ τ⟩, mem_ball_self (hr ⟨γ τ, hγ τ⟩)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  choose idx hidx using hsub
  have hb₁ : ∀ i, ball (idx i).1 (r (idx i)) ⊆ ball (idx i).1 (r₁ (idx i)) :=
    fun i ↦ ball_subset_ball (min_le_left _ _)
  have hb₂ : ∀ i, ball (idx i).1 (r (idx i)) ⊆ ball (idx i).1 (r₂ (idx i)) :=
    fun i ↦ ball_subset_ball (min_le_right _ _)
  have h₁ : HasLocalPotentialCurveIntegral φ γ
      (∑ i ∈ Finset.range n, (g₁ (idx i) (γ (t (i + 1))) - g₁ (idx i) (γ (t i)))) :=
    ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun i ↦ g₁ (idx i), ht0, hn n le_rfl,
      fun i _ ↦ hmono (Nat.le_succ i), fun i _ τ hτ ↦ hidx i hτ,
      fun i _ y hy ↦ hd₁ (idx i) y (hb₁ i hy), rfl⟩
  have h₂ : HasLocalPotentialCurveIntegral ψ γ
      (∑ i ∈ Finset.range n, (g₂ (idx i) (γ (t (i + 1))) - g₂ (idx i) (γ (t i)))) :=
    ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun i ↦ g₂ (idx i), ht0, hn n le_rfl,
      fun i _ ↦ hmono (Nat.le_succ i), fun i _ τ hτ ↦ hidx i hτ,
      fun i _ y hy ↦ hd₂ (idx i) y (hb₂ i hy), rfl⟩
  have h₁₂ : HasLocalPotentialCurveIntegral (φ + ψ) γ
      ((∑ i ∈ Finset.range n, (g₁ (idx i) (γ (t (i + 1))) - g₁ (idx i) (γ (t i)))) +
        ∑ i ∈ Finset.range n, (g₂ (idx i) (γ (t (i + 1))) - g₂ (idx i) (γ (t i)))) := by
    refine ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun i ↦ g₁ (idx i) + g₂ (idx i),
      ht0, hn n le_rfl, fun i _ ↦ hmono (Nat.le_succ i), fun i _ τ hτ ↦ hidx i hτ,
      fun i _ y hy ↦ (hd₁ (idx i) y (hb₁ i hy)).add (hd₂ (idx i) y (hb₂ i hy)), ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.add_apply]
    abel
  rw [h₁.localPotentialCurveIntegral_eq, h₂.localPotentialCurveIntegral_eq,
    h₁₂.localPotentialCurveIntegral_eq]

/-- Subtracting two covector fields with local potentials subtracts their curve integrals along any
path in their common domain. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_sub (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral (φ - ψ) γ =
      localPotentialCurveIntegral φ γ - localPotentialCurveIntegral ψ γ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, hφ.localPotentialCurveIntegral_add hψ.neg hγ,
    localPotentialCurveIntegral_neg]

end Operations

/-! ### Pullback naturality -/

section Pullback

variable {s : Set E} {φ : E → E →L[ℝ] F}

/-- Pulling back a covector field with local potentials along a differentiable map `f : G → E` on an
open set `u` equals integrating `φ` along the mapped path `γ.map'`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_map' {u : Set G} {f : G → E}
    {a b : G} {γ : Path a b} (hφ : HasLocalPotentials s φ) (hu : IsOpen u)
    (hf : DifferentiableOn ℝ f u) (hfs : MapsTo f u s) (hγ : ∀ t, γ t ∈ u) :
    localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialCurveIntegral φ
        (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) := by
  have hfc : ContinuousOn f (range γ) := hf.continuousOn.mono (range_subset_iff.mpr hγ)
  have hex : ∀ x : u, ∃ (r : ℝ) (q : ℝ) (g : E → F), 0 < q ∧ ball x.1 q ⊆ u ∧
      MapsTo f (ball x.1 q) (ball (f x.1) r) ∧
      ∀ y ∈ ball (f x.1) r, HasFDerivAt g (φ y) y := by
    intro x
    obtain ⟨r, hr, -, g, -, hd⟩ := hasLocalPotentials_iff.mp hφ (f x.1) (hfs x.2)
    have hfx_cont : ContinuousAt f x.1 :=
      (hf x.1 x.2).differentiableAt (hu.mem_nhds x.2) |>.continuousAt
    have hn : f ⁻¹' ball (f x.1) r ∩ u ∈ 𝓝 x.1 :=
      inter_mem (hfx_cont.preimage_mem_nhds (ball_mem_nhds _ hr)) (hu.mem_nhds x.2)
    obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hn
    exact ⟨r, q, g, hq, fun y hy ↦ (hqsub hy).2, fun y hy ↦ (hqsub hy).1, hd⟩
  choose r q g hq hqu hqf hd using hex
  let c : u → Set I := fun x ↦ γ ⁻¹' ball x.1 (q x)
  have hc₁ : ∀ x : u, IsOpen (c x) := fun x ↦ isOpen_ball.preimage γ.continuous
  have hc₂ : (univ : Set I) ⊆ ⋃ x : u, c x := fun τ _ ↦
    mem_iUnion.mpr ⟨⟨γ τ, hγ τ⟩, mem_ball_self (hq ⟨γ τ, hγ τ⟩)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  choose idx hidx using hsub
  let val : F := ∑ i ∈ Finset.range n,
    (g (idx i) (f (γ (t (i + 1)))) - g (idx i) (f (γ (t i))))
  have h₁ : HasLocalPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ val := by
    refine ⟨n, t, fun i ↦ (idx i).1, fun i ↦ q (idx i), fun i ↦ g (idx i) ∘ f,
      ht0, hn n le_rfl, fun i _ ↦ hmono (Nat.le_succ i), fun i _ τ hτ ↦ hidx i hτ, ?_, rfl⟩
    intro i _ y hy
    have hyu : y ∈ u := hqu (idx i) hy
    exact (hd (idx i) (f y) (hqf (idx i) hy)).comp y
      ((hf y hyu).differentiableAt (hu.mem_nhds hyu)).hasFDerivAt
  have h₂ : HasLocalPotentialCurveIntegral φ (γ.map' hfc) val :=
    ⟨n, t, fun i ↦ f (idx i).1, fun i ↦ r (idx i), fun i ↦ g (idx i),
      ht0, hn n le_rfl, fun i _ ↦ hmono (Nat.le_succ i),
      fun i _ τ hτ ↦ hqf (idx i) (hidx i hτ), fun i _ ↦ hd (idx i), rfl⟩
  rw [h₁.localPotentialCurveIntegral_eq, h₂.localPotentialCurveIntegral_eq]

/-- Pulling back a covector field with local potentials along a globally differentiable map
`f : G → E` equals integrating `φ` along `γ.map hf.continuous`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_map {f : G → E}
    {a b : G} {γ : Path a b} (hφ : HasLocalPotentials s φ)
    (hf : Differentiable ℝ f) (hγ : ∀ t, f (γ t) ∈ s) :
    localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialCurveIntegral φ (γ.map hf.continuous) :=
  hφ.localPotentialCurveIntegral_map' (hφ.isOpen.preimage hf.continuous)
    hf.differentiableOn (mapsTo_preimage f s) hγ

end Pullback

/-! ### Homotopy invariance relative to endpoints -/

section Homotopy

variable {a b : E} {s : Set E} {φ : E → E →L[ℝ] F}

/-- The local-potential curve integral is invariant under path homotopy relative to endpoints
inside `s`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_of_homotopy (hφ : HasLocalPotentials s φ)
    {γ₀ γ₁ : Path a b} (H : γ₀.Homotopy γ₁) (hH : ∀ p, H p ∈ s) :
    localPotentialCurveIntegral φ γ₀ = localPotentialCurveIntegral φ γ₁ := by
  -- Subdivide `I × I` into a grid `0 = t 0 ≤ ⋯ ≤ t n = 1` whose cells map into potential balls.
  choose r hr _ g _ hd using fun x : s ↦ hasLocalPotentials_iff.mp hφ x.1 x.2
  let c : s → Set (I × I) := fun x ↦ H ⁻¹' ball x.1 (r x)
  have hc₁ : ∀ x : s, IsOpen (c x) := fun x ↦ isOpen_ball.preimage H.continuous
  have hc₂ : (univ : Set (I × I)) ⊆ ⋃ x : s, c x := fun p _ ↦
    mem_iUnion.mpr ⟨⟨H p, hH p⟩, mem_ball_self (hr ⟨H p, hH p⟩)⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc₁ hc₂
  choose idx hidx using hsub
  have htn : t n = 1 := hn n le_rfl
  let z : ℕ → ℕ → E := fun i j ↦ (idx i j).1
  let ρ : ℕ → ℕ → ℝ := fun i j ↦ r (idx i j)
  let G : ℕ → ℕ → E → F := fun i j ↦ g (idx i j)
  -- Across each row `[t i, t (i + 1)]`, vertical potential differences telescope to `0`.
  have hstep : ∀ i < n,
      localPotentialCurveIntegral φ (H.eval (t (i + 1))) -
        localPotentialCurveIntegral φ (H.eval (t i)) = 0 := by
    intro i _
    have hti : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
    have hrow₀ : HasLocalPotentialCurveIntegral φ (H.eval (t i))
        (∑ j ∈ Finset.range n, (G i j (H (t i, t (j + 1))) - G i j (H (t i, t j)))) :=
      ⟨n, t, z i, ρ i, G i, ht0, htn, fun j _ ↦ hmono (Nat.le_succ j),
        fun j _ τ hτ ↦ hidx i j ⟨left_mem_Icc.mpr hti, hτ⟩,
        fun j _ ↦ hd (idx i j), rfl⟩
    have hrow₁ : HasLocalPotentialCurveIntegral φ (H.eval (t (i + 1)))
        (∑ j ∈ Finset.range n,
          (G i j (H (t (i + 1), t (j + 1))) - G i j (H (t (i + 1), t j)))) :=
      ⟨n, t, z i, ρ i, G i, ht0, htn, fun j _ ↦ hmono (Nat.le_succ j),
        fun j _ τ hτ ↦ hidx i j ⟨right_mem_Icc.mpr hti, hτ⟩,
        fun j _ ↦ hd (idx i j), rfl⟩
    rw [hrow₀.localPotentialCurveIntegral_eq, hrow₁.localPotentialCurveIntegral_eq,
      ← Finset.sum_sub_distrib]
    let δ : ℕ → F := fun j ↦
      if j < n then G i j (H (t (i + 1), t j)) - G i j (H (t i, t j)) else 0
    have hterm : ∀ j ∈ Finset.range n,
        (G i j (H (t (i + 1), t (j + 1))) - G i j (H (t (i + 1), t j))) -
          (G i j (H (t i, t (j + 1))) - G i j (H (t i, t j))) =
        δ (j + 1) - δ j := by
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hδj : δ j = G i j (H (t (i + 1), t j)) - G i j (H (t i, t j)) := ite_eq_left hjn
      have hδj1 : δ (j + 1) = G i j (H (t (i + 1), t (j + 1))) - G i j (H (t i, t (j + 1))) := by
        by_cases hj1 : j + 1 < n
        · dsimp only [δ]
          rw [ite_eq_left hj1]
          have htj : t j ≤ t (j + 1) := hmono (Nat.le_succ j)
          have htj1 : t (j + 1) ≤ t (j + 2) := hmono (Nat.le_succ (j + 1))
          obtain ⟨c₀, hc₀⟩ := (isOpen_ball.inter isOpen_ball).exists_eq_add_of_fderiv_eq
            ((convex_ball (z i j) (ρ i j)).inter
              (convex_ball (z i (j + 1)) (ρ i (j + 1)))).isPreconnected
            (fun w hw ↦ (hd (idx i j) w hw.1).differentiableAt.differentiableWithinAt)
            (fun w hw ↦ (hd (idx i (j + 1)) w hw.2).differentiableAt.differentiableWithinAt)
            (fun w hw ↦ (hd (idx i j) w hw.1).fderiv.trans (hd (idx i (j + 1)) w hw.2).fderiv.symm)
          have hp₀ : H (t i, t (j + 1)) ∈ ball (z i j) (ρ i j) ∩ ball (z i (j + 1)) (ρ i (j + 1)) :=
            ⟨hidx i j ⟨left_mem_Icc.mpr hti, right_mem_Icc.mpr htj⟩,
              hidx i (j + 1) ⟨left_mem_Icc.mpr hti, left_mem_Icc.mpr htj1⟩⟩
          have hp₁ : H (t (i + 1), t (j + 1)) ∈
              ball (z i j) (ρ i j) ∩ ball (z i (j + 1)) (ρ i (j + 1)) :=
            ⟨hidx i j ⟨right_mem_Icc.mpr hti, right_mem_Icc.mpr htj⟩,
              hidx i (j + 1) ⟨right_mem_Icc.mpr hti, left_mem_Icc.mpr htj1⟩⟩
          dsimp only [G]
          rw [hc₀ hp₁, hc₀ hp₀, add_sub_add_right_eq_sub]
        · have hjeq : j + 1 = n := by omega
          simp [δ, hjeq, htn]
      rw [hδj, hδj1]
      abel
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub δ n]
    have hδn : δ n = 0 := ite_eq_right (lt_irrefl n)
    have hδ0 : δ 0 = 0 := by
      by_cases hn0 : 0 < n
      · simp [δ, hn0, ht0]
      · simp [δ, hn0]
    rw [hδn, hδ0, sub_self]
  -- Telescope across all `n` rows from `H.eval (t 0) = γ₀` to `H.eval (t n) = γ₁`.
  have htel := Finset.sum_range_sub (fun i ↦ localPotentialCurveIntegral φ (H.eval (t i))) n
  have hzero : ∑ i ∈ Finset.range n,
      (localPotentialCurveIntegral φ (H.eval (t (i + 1))) -
        localPotentialCurveIntegral φ (H.eval (t i))) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ hstep i (Finset.mem_range.mp hi)
  rw [hzero, htn, ht0, H.eval_one, H.eval_zero] at htel
  exact (sub_eq_zero.mp htel.symm).symm

end Homotopy

/-! ### Comparison with Mathlib's Bochner `curveIntegral` -/

section CurveIntegralComparison

variable [CompleteSpace F] {a b : E} {s : Set E} {φ : E → E →L[ℝ] F}

/-- If `γ.extend` is differentiable on `(0, 1)` and `φ` is `CurveIntegrable` along `γ`, then any
`HasLocalPotentialCurveIntegral` value equals Mathlib's `curveIntegral φ γ`. -/
theorem HasLocalPotentialCurveIntegral.eq_curveIntegral_of_differentiableOn {γ : Path a b} {v : F}
    (hφγ : HasLocalPotentialCurveIntegral φ γ v)
    (hdiff : DifferentiableOn ℝ γ.extend (Ioo 0 1)) (hint : CurveIntegrable φ γ) :
    v = ∫ᶜ x in γ, φ x := by
  rcases hφγ with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  have hae : EqOn (curveIntegralFun φ γ) (fun τ ↦ φ (γ.extend τ) (deriv γ.extend τ)) (Ioo 0 1) := by
    intro τ hτ
    rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)]
  have hint_deriv : IntervalIntegrable (fun τ ↦ φ (γ.extend τ) (deriv γ.extend τ)) volume 0 1 := by
    refine hint.congr_ae ?_
    rw [Set.uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    exact hae hτ
  have hint_sub : ∀ i < n,
      IntervalIntegrable (fun τ ↦ φ (γ.extend τ) (deriv γ.extend τ))
        volume (t i : ℝ) (t (i + 1) : ℝ) := by
    intro i hi
    refine hint_deriv.mono_set ?_
    rw [Set.uIcc_of_le (Subtype.coe_le_coe.mpr (hle i hi)), Set.uIcc_of_le zero_le_one]
    exact fun τ hτ ↦ ⟨(t i).2.1.trans hτ.1, hτ.2.trans (t (i + 1)).2.2⟩
  rw [curveIntegral_eq_intervalIntegral_deriv]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i ↦ (t i : ℝ)) hint_sub
  have ht0' : ((t 0 : I) : ℝ) = 0 := by simp [ht0]
  have htn' : ((t n : I) : ℝ) = 1 := by simp [htn]
  rw [ht0', htn'] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hmem_ball : ∀ τ ∈ Icc (t i : ℝ) (t (i + 1) : ℝ), γ.extend τ ∈ ball (z i) (r i) := by
    intro τ hτ
    have hτI : τ ∈ I := ⟨(t i).2.1.trans hτ.1, hτ.2.trans (t (i + 1)).2.2⟩
    rw [γ.extend_apply hτI]
    exact hγ i hin ⟨Subtype.coe_le_coe.mp hτ.1, Subtype.coe_le_coe.mp hτ.2⟩
  have hgi_cont : ContinuousOn (g i) (ball (z i) (r i)) :=
    fun y hy ↦ (hd i hin y hy).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (g i ∘ γ.extend) (Icc (t i : ℝ) (t (i + 1) : ℝ)) :=
    hgi_cont.comp γ.continuous_extend.continuousOn hmem_ball
  have hderiv : ∀ τ ∈ Ioo (t i : ℝ) (t (i + 1) : ℝ),
      HasDerivAt (g i ∘ γ.extend) (φ (γ.extend τ) (deriv γ.extend τ)) τ := by
    intro τ hτ
    have hτ01 : τ ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (t i).2.1 hτ.1, lt_of_lt_of_le hτ.2 (t (i + 1)).2.2⟩
    have hγd : HasDerivAt γ.extend (deriv γ.extend τ) τ :=
      ((hdiff τ hτ01).differentiableAt (Ioo_mem_nhds hτ01.1 hτ01.2)).hasDerivAt
    exact (hd i hin (γ.extend τ) (hmem_ball τ (Ioo_subset_Icc_self hτ))).comp_hasDerivAt τ hγd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (Subtype.coe_le_coe.mpr (hle i hin))
      hcont hderiv (hint_sub i hin)]
  simp only [Function.comp_apply, γ.extend_extends']

/-- When `γ.extend` is differentiable on `(0, 1)` and `φ` is `CurveIntegrable` along `γ` with a
local-potential subdivision, `localPotentialCurveIntegral` agrees with `curveIntegral`. -/
theorem localPotentialCurveIntegral_eq_curveIntegral_of_differentiableOn {γ : Path a b}
    (hex : ∃ v, HasLocalPotentialCurveIntegral φ γ v)
    (hdiff : DifferentiableOn ℝ γ.extend (Ioo 0 1)) (hint : CurveIntegrable φ γ) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x := by
  obtain ⟨v, hv⟩ := hex
  rw [hv.localPotentialCurveIntegral_eq, hv.eq_curveIntegral_of_differentiableOn hdiff hint]

/-- Along any `C¹` path in `s`, `localPotentialCurveIntegral` agrees with Mathlib's Bochner
`curveIntegral` when `F` is complete. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral
    (hφ : HasLocalPotentials s φ) {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x :=
  localPotentialCurveIntegral_eq_curveIntegral_of_differentiableOn
    (hφ.exists_hasLocalPotentialCurveIntegral hγs)
    ((hγ.differentiableOn one_ne_zero).mono Ioo_subset_Icc_self)
    (hφ.continuousOn.curveIntegrable_of_contDiffOn hγ hγs)

end CurveIntegralComparison

/-! ### Vanishing loop integrals and global potentials on path-connected domains -/

section LoopCriterion

variable {a b x₀ : E} {s : Set E} {φ : E → E →L[ℝ] F}

/-- If every loop in `s` based at `x₀` has zero curve integral, then any two paths in `s` sharing
endpoints in the path component of `x₀` in `s` have the same curve integral. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_of_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    (hjoin : JoinedIn s x₀ a) {p q : Path a b} (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    localPotentialCurveIntegral φ p = localPotentialCurveIntegral φ q := by
  let α : Path x₀ a := hjoin.somePath
  have hα : ∀ t, α t ∈ s := hjoin.somePath_mem
  have hps : ∀ t, (α.trans p) t ∈ s := fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hp _]
  have hqs : ∀ t, (α.trans q) t ∈ s := fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hq _]
  have hqs_symm : ∀ t, (α.trans q).symm t ∈ s := fun t ↦ hqs (unitInterval.symm t)
  let η : Path x₀ x₀ := (α.trans p).trans (α.trans q).symm
  have hη : localPotentialCurveIntegral φ η = 0 := hloop η fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hps _; exact hqs_symm _]
  rw [hφ.localPotentialCurveIntegral_trans hps hqs_symm, localPotentialCurveIntegral_symm,
    hφ.localPotentialCurveIntegral_trans hα hp,
    hφ.localPotentialCurveIntegral_trans hα hq] at hη
  calc
    localPotentialCurveIntegral φ p
      = ((localPotentialCurveIntegral φ α + localPotentialCurveIntegral φ p) +
          -(localPotentialCurveIntegral φ α + localPotentialCurveIntegral φ q)) +
        localPotentialCurveIntegral φ q := by abel
    _ = localPotentialCurveIntegral φ q := by rw [hη, zero_add]

/-- Candidate global potential of `φ` on `s` anchored at `x₀`, defined at `y` by integrating `φ`
along a path in `s` from `x₀` to `y` when one exists, and `0` otherwise. -/
noncomputable def localPotentialPrimitive (s : Set E) (φ : E → E →L[ℝ] F) (x₀ y : E) : F :=
  open Classical in
  if h : JoinedIn s x₀ y then localPotentialCurveIntegral φ h.somePath else 0

/-- Outside the path component of `x₀` in `s`, `localPotentialPrimitive` returns `0`. -/
theorem localPotentialPrimitive_of_not_joinedIn {y : E} (h : ¬JoinedIn s x₀ y) :
    localPotentialPrimitive s φ x₀ y = 0 := by
  rw [localPotentialPrimitive, dite_eq_right h]

/-- On the empty domain, `localPotentialPrimitive` is identically zero. -/
@[simp]
theorem localPotentialPrimitive_empty (φ : E → E →L[ℝ] F) (x₀ y : E) :
    localPotentialPrimitive ∅ φ x₀ y = 0 :=
  localPotentialPrimitive_of_not_joinedIn fun ⟨_, hγ⟩ ↦ hγ 0

/-- When loops at `x₀` in `s` have zero integral, `localPotentialPrimitive s φ x₀ y` equals the
integral along any path in `s` from `x₀` to `y`. -/
theorem HasLocalPotentials.localPotentialPrimitive_eq (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {y : E} (γ : Path x₀ y) (hγ : ∀ t, γ t ∈ s) :
    localPotentialPrimitive s φ x₀ y = localPotentialCurveIntegral φ γ := by
  have hj : JoinedIn s x₀ y := ⟨γ, hγ⟩
  rw [localPotentialPrimitive, dite_eq_left hj]
  exact hφ.localPotentialCurveIntegral_eq_of_forall_loop_eq_zero hloop
    (JoinedIn.refl (γ.source ▸ hγ 0)) hj.somePath_mem hγ

/-- When loops at `x₀` in `s` have zero integral and `x₀ ∈ s`, `localPotentialPrimitive` vanishes
at the base point `x₀`. -/
theorem HasLocalPotentials.localPotentialPrimitive_self (hφ : HasLocalPotentials s φ)
    (hx₀ : x₀ ∈ s)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0) :
    localPotentialPrimitive s φ x₀ x₀ = 0 := by
  rw [hφ.localPotentialPrimitive_eq hloop (Path.refl x₀) (fun _ ↦ hx₀),
    localPotentialCurveIntegral_refl]

private theorem exists_eventuallyEq_localPotentialPrimitive (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    ∃ g : E → F, ContDiffAt ℝ 1 g z ∧ HasFDerivAt g (φ z) z ∧
      localPotentialPrimitive s φ x₀ =ᶠ[𝓝 z] g := by
  obtain ⟨r, hr, hrs, gz, hgz, hdz⟩ := hasLocalPotentials_iff.mp hφ z hjoin.target_mem
  let α : Path x₀ z := hjoin.somePath
  have hα : ∀ t, α t ∈ s := hjoin.somePath_mem
  have heq : EqOn (localPotentialPrimitive s φ x₀)
      (fun y ↦ gz y + (localPotentialCurveIntegral φ α - gz z)) (ball z r) := by
    intro y hy
    have hseg_ball : ∀ t, (Path.segment z y) t ∈ ball z r := fun t ↦
      (convex_ball z r).segment_subset (mem_ball_self hr) hy
        (Path.range_segment z y ▸ mem_range_self t)
    have hseg_s : ∀ t, (Path.segment z y) t ∈ s := fun t ↦ hrs (hseg_ball t)
    have htrans_s : ∀ t, (α.trans (Path.segment z y)) t ∈ s := fun t ↦ by
      rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hseg_s _]
    dsimp only
    rw [hφ.localPotentialPrimitive_eq hloop (α.trans (Path.segment z y)) htrans_s,
      hφ.localPotentialCurveIntegral_trans hα hseg_s,
      localPotentialCurveIntegral_eq_sub_of_hasFDerivAt isOpen_ball hdz hseg_ball]
    abel
  refine ⟨fun y ↦ gz y + (localPotentialCurveIntegral φ α - gz z),
    (hgz.contDiffAt (ball_mem_nhds z hr)).add contDiffAt_const,
    by simpa only [add_zero] using
      (hdz z (mem_ball_self hr)).add_const (localPotentialCurveIntegral φ α - gz z),
    Filter.eventuallyEq_of_mem (ball_mem_nhds z hr) heq⟩

/-- At any point `z` joined to `x₀` in `s`, if all loops at `x₀` in `s` have zero integral, then
`localPotentialPrimitive s φ x₀` is `C¹` at `z`. -/
theorem HasLocalPotentials.contDiffAt_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    ContDiffAt ℝ 1 (localPotentialPrimitive s φ x₀) z := by
  obtain ⟨g, hc, -, hev⟩ := exists_eventuallyEq_localPotentialPrimitive hφ hloop hjoin
  exact hc.congr_of_eventuallyEq hev

/-- At any point `z` joined to `x₀` in `s`, if all loops at `x₀` in `s` have zero integral, then
`localPotentialPrimitive s φ x₀` has Fréchet derivative `φ z` at `z`. -/
theorem HasLocalPotentials.hasFDerivAt_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    HasFDerivAt (localPotentialPrimitive s φ x₀) (φ z) z := by
  obtain ⟨g, -, hd, hev⟩ := exists_eventuallyEq_localPotentialPrimitive hφ hloop hjoin
  exact hd.congr_of_eventuallyEq hev

/-- If `x₀` can be joined in `s` to every point of `s` and all loops in `s` based at `x₀` have zero
curve integral, then `localPotentialPrimitive s φ x₀` is `C¹` on `s`. -/
theorem HasLocalPotentials.contDiffOn_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ) (hconn : ∀ y ∈ s, JoinedIn s x₀ y)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0) :
    ContDiffOn ℝ 1 (localPotentialPrimitive s φ x₀) s := fun w hw ↦
  (hφ.contDiffAt_localPotentialPrimitive hloop (hconn w hw)).contDiffWithinAt

/-- On a path-connected domain, a covector field with local potentials admits a global `C¹`
potential if and only if its curve integral vanishes along every loop in the domain. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ) (hs : IsPathConnected s) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w) ↔
      ∀ x ∈ s, ∀ η : Path x x, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0 := by
  refine ⟨fun ⟨g, _, hd⟩ x _ η hη ↦ ?_, fun hloop ↦ ?_⟩
  · rw [localPotentialCurveIntegral_eq_sub_of_hasFDerivAt hφ.isOpen hd hη, sub_self]
  · obtain ⟨x₀, hx₀, hjoin⟩ := hs
    exact ⟨localPotentialPrimitive s φ x₀,
      hφ.contDiffOn_localPotentialPrimitive (fun y hy ↦ hjoin hy) (hloop x₀ hx₀),
      fun w hw ↦ hφ.hasFDerivAt_localPotentialPrimitive (hloop x₀ hx₀) (hjoin hw)⟩

end LoopCriterion

end TauCeti
