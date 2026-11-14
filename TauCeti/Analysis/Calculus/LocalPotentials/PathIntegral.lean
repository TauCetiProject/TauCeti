/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Analysis.Calculus.LocalPotentials.Basic

import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.Path.Map

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

## Main results

* `TauCeti.HasLocalPotentialCurveIntegral.unique`: independence from the choice of subdivision,
  balls, and local potentials.
* `TauCeti.HasLocalPotentials.hasLocalPotentialCurveIntegral`: existence for every continuous path
  in a domain where `φ` has local potentials.
* `TauCeti.localPotentialCurveIntegral_symm`, `TauCeti.localPotentialCurveIntegral_trans`: reversal
  and concatenation laws, together with linearity and scalar multiplication in `φ` and evaluation
  on constant covector fields and global primitives.
* `TauCeti.localPotentialCurveIntegral_map'`,
  `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_map'`: pullback naturality along
  differentiable maps of open sets.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_of_homotopy`: invariance under path
  homotopy relative to endpoints inside the domain.

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §§1, 3 (primitives along continuous paths and homotopy invariance).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §§1.3, 4.3 (line integrals of locally
  exact differentials by chains of discs).
-/

public section

open Filter Function Metric Set
open scoped ContDiff Topology unitInterval

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem localPotential_sub_eq_sub_on_ball_inter {φ : E → E →L[ℝ] F}
    {z₁ z₂ : E} {r₁ r₂ : ℝ} {g₁ g₂ : E → F}
    (hd₁ : ∀ w ∈ ball z₁ r₁, HasFDerivAt g₁ (φ w) w)
    (hd₂ : ∀ w ∈ ball z₂ r₂, HasFDerivAt g₂ (φ w) w)
    {x y : E} (hx : x ∈ ball z₁ r₁ ∩ ball z₂ r₂) (hy : y ∈ ball z₁ r₁ ∩ ball z₂ r₂) :
    g₁ y - g₁ x = g₂ y - g₂ x := by
  obtain ⟨c, hc⟩ := (isOpen_ball.inter isOpen_ball).exists_eq_add_of_fderiv_eq
    ((convex_ball z₁ r₁).inter (convex_ball z₂ r₂)).isPreconnected
    (fun w hw ↦ (hd₁ w hw.1).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd₂ w hw.2).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd₁ w hw.1).fderiv.trans (hd₂ w hw.2).fderiv.symm)
  rw [hc hy, hc hx, add_sub_add_right_eq_sub]

private theorem exists_ball_subdivision_Icc {X : Type*} [PseudoMetricSpace X] {u : Set X}
    {x₀ x₁ : X} {γ : Path x₀ x₁} {u₀ u₁ : I} (hu : u₀ ≤ u₁)
    (hγ : MapsTo γ (Icc u₀ u₁) u) (r : u → ℝ) (hr : ∀ x : u, 0 < r x) :
    ∃ (n : ℕ) (t : ℕ → I) (idx : ℕ → u),
      t 0 = u₀ ∧ t n = u₁ ∧ (∀ i < n, t i ≤ t (i + 1)) ∧
      ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (ball (idx i).1 (r (idx i))) := by
  let γs : Icc (u₀ : ℝ) (u₁ : ℝ) → X := fun τ ↦ γ ⟨τ.1, u₀.2.1.trans τ.2.1, τ.2.2.trans u₁.2.2⟩
  have hγs_cont : Continuous γs := γ.continuous.comp (continuous_subtype_val.subtype_mk _)
  let c : u → Set (Icc (u₀ : ℝ) (u₁ : ℝ)) := fun x ↦ γs ⁻¹' ball x.1 (r x)
  have hc₁ : ∀ x : u, IsOpen (c x) := fun x ↦ isOpen_ball.preimage hγs_cont
  have hc₂ : (univ : Set (Icc (u₀ : ℝ) (u₁ : ℝ))) ⊆ ⋃ x : u, c x := fun τ _ ↦ by
    let τI : I := ⟨τ.1, u₀.2.1.trans τ.2.1, τ.2.2.trans u₁.2.2⟩
    have hτI : τI ∈ Icc u₀ u₁ := ⟨Subtype.coe_le_coe.mp τ.2.1, Subtype.coe_le_coe.mp τ.2.2⟩
    exact mem_iUnion.mpr ⟨⟨γ τI, hγ hτI⟩, mem_ball_self (hr ⟨γ τI, hγ hτI⟩)⟩
  obtain ⟨t', ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc (Subtype.coe_le_coe.mpr hu) hc₁ hc₂
  choose idx hidx using hsub
  let t : ℕ → I := fun k ↦ ⟨(t' k).1, u₀.2.1.trans (t' k).2.1, (t' k).2.2.trans u₁.2.2⟩
  refine ⟨n, t, idx, Subtype.ext ht0, Subtype.ext (hn n le_rfl),
    fun i _ ↦ Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mpr (hmono (Nat.le_succ i))),
    fun i _ τ hτ ↦ ?_⟩
  have hτ_mem : (⟨τ.1, (t' i).2.1.trans (Subtype.coe_le_coe.mpr hτ.1),
      (Subtype.coe_le_coe.mpr hτ.2).trans (t' (i + 1)).2.2⟩ : Icc (u₀ : ℝ) (u₁ : ℝ)) ∈
      Icc (t' i) (t' (i + 1)) :=
    ⟨Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mpr hτ.1),
      Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mpr hτ.2)⟩
  exact hidx i hτ_mem

private def HasSubdivisionUpTo {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) (u : I) (v : F) :
    Prop :=
  ∃ (n : ℕ) (t : ℕ → I) (z : ℕ → E) (r : ℕ → ℝ) (g : ℕ → E → F),
    t 0 = 0 ∧ t n = u ∧ (∀ i < n, t i ≤ t (i + 1)) ∧
    (∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (ball (z i) (r i))) ∧
    (∀ i < n, ∀ y ∈ ball (z i) (r i), HasFDerivAt (g i) (φ y) y) ∧
    v = ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))

private theorem HasSubdivisionUpTo.zero {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) :
    HasSubdivisionUpTo φ γ 0 0 :=
  ⟨0, fun _ ↦ 0, fun _ ↦ a, fun _ ↦ 1, fun _ ↦ 0, rfl, rfl, by simp, by simp, by simp, by simp⟩

private theorem HasSubdivisionUpTo.step {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    {u₀ u₁ : I} {v : F} (h : HasSubdivisionUpTo φ γ u₀ v) (hu : u₀ ≤ u₁)
    {U : Set E} (hU : IsOpen U) (hγ : MapsTo γ (Icc u₀ u₁) U) {g₀ : E → F}
    (hd₀ : ∀ y ∈ U, HasFDerivAt g₀ (φ y) y) :
    HasSubdivisionUpTo φ γ u₁ (v + (g₀ (γ u₁) - g₀ (γ u₀))) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hmap, hd, rfl⟩
  choose ρ hρ hρU using fun x : U ↦ Metric.isOpen_iff.mp hU x.1 x.2
  obtain ⟨m, s, idx, hs0, hsm, hsle, hsmap⟩ := exists_ball_subdivision_Icc hu hγ ρ hρ
  let T : ℕ → I := fun k ↦ if k < n then t k else s (k - n)
  have hT_left : ∀ k ≤ n, T k = t k := fun k hk ↦ by
    rcases lt_or_eq_of_le hk with hkn | rfl <;> [exact ite_eq_left hkn; simp [T, hs0, htn]]
  have hT_right : ∀ j, T (n + j) = s j := fun j ↦ by simp [T, Nat.not_lt.mpr (Nat.le_add_right n j)]
  refine ⟨n + m, T, fun k ↦ if k < n then z k else (idx (k - n)).1,
    fun k ↦ if k < n then r k else ρ (idx (k - n)), fun k ↦ if k < n then g k else g₀,
    (hT_left 0 (Nat.zero_le n)).trans ht0, (hT_right m).trans hsm, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hkn : k < n
    · rw [hT_left k hkn.le, hT_left (k + 1) (Nat.succ_le_of_lt hkn)]; exact hle k hkn
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, (Nat.add_sub_of_le (Nat.not_lt.mp hkn)).symm⟩
      rw [Nat.add_assoc, hT_right j, hT_right (j + 1)]; exact hsle j (by omega)
  · intro k hk
    by_cases hkn : k < n
    · simpa only [ite_eq_left hkn, hT_left k hkn.le,
        hT_left (k + 1) (Nat.succ_le_of_lt hkn)] using hmap k hkn
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, (Nat.add_sub_of_le (Nat.not_lt.mp hkn)).symm⟩
      simpa only [ite_eq_right hkn, Nat.add_sub_cancel_left, Nat.add_assoc, hT_right j,
        hT_right (j + 1)] using hsmap j (by omega)
  · intro k _
    by_cases hkn : k < n
    · simpa only [ite_eq_left hkn] using hd k hkn
    · simpa only [ite_eq_right hkn] using fun y hy ↦ hd₀ y (hρU (idx (k - n)) hy)
  · rw [Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hin : i < n := Finset.mem_range.mp hi
      simp only [ite_eq_left hin, hT_left i hin.le, hT_left (i + 1) (Nat.succ_le_of_lt hin)]
    · have hsum_s : ∑ j ∈ Finset.range m,
          ((if n + j < n then g (n + j) else g₀) (γ (T (n + j + 1))) -
            (if n + j < n then g (n + j) else g₀) (γ (T (n + j)))) =
          ∑ j ∈ Finset.range m, (g₀ (γ (s (j + 1))) - g₀ (γ (s j))) :=
        Finset.sum_congr rfl fun j _ ↦ by
          simp [Nat.not_lt.mpr (Nat.le_add_right n j), Nat.add_assoc, hT_right]
      rw [hsum_s, Finset.sum_range_sub (fun j ↦ g₀ (γ (s j))) m, hsm, hs0]

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

private theorem HasSubdivisionUpTo.toHasLocalPotentialCurveIntegral {γ : Path a b}
    {u : I} {v : F} (h : HasSubdivisionUpTo φ γ u v) (hu : u = 1) :
    HasLocalPotentialCurveIntegral φ γ v := by subst hu; exact h

private theorem hasLocalPotentialCurveIntegral_of_open_subdivision {γ : Path a b}
    {n : ℕ} {t : ℕ → I} {U : ℕ → Set E} {g : ℕ → E → F}
    (ht0 : t 0 = 0) (htn : t n = 1) (hle : ∀ i < n, t i ≤ t (i + 1))
    (hU : ∀ i < n, IsOpen (U i)) (hγ : ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (U i))
    (hd : ∀ i < n, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y) :
    HasLocalPotentialCurveIntegral φ γ
      (∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))) := by
  suffices ∀ k ≤ n, HasSubdivisionUpTo φ γ (t k)
      (∑ i ∈ Finset.range k, (g i (γ (t (i + 1))) - g i (γ (t i)))) from
    (this n le_rfl).toHasLocalPotentialCurveIntegral htn
  intro k hk
  induction k with
  | zero => simpa only [ht0, Finset.range_zero, Finset.sum_empty] using HasSubdivisionUpTo.zero φ γ
  | succ k ih =>
    have hkn : k < n := Nat.lt_of_succ_le hk
    rw [Finset.sum_range_succ]
    exact (ih hkn.le).step (hle k hkn) (hU k hkn) (hγ k hkn) (hd k hkn)

/-- The curve integral of `φ` along a continuous path `γ` computed from local potentials, returning
`0` when no adapted local-potential subdivision exists. -/
noncomputable def localPotentialCurveIntegral (φ : E → E →L[ℝ] F) (γ : Path a b) : F :=
  open Classical in
  if h : ∃ v, HasLocalPotentialCurveIntegral φ γ v then h.choose else 0

private theorem clamp_pair_cases {α : Type*} [LinearOrder α] {u₀ u₁ v₀ v₁ : α}
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) :
    ((v₁ ⊔ u₀) ⊓ u₁ = u₀ ∧ (v₀ ⊔ u₀) ⊓ u₁ = u₀ ∧ (u₁ ⊔ v₀) ⊓ v₁ = v₁ ∧ (u₀ ⊔ v₀) ⊓ v₁ = v₁) ∨
    ((v₁ ⊔ u₀) ⊓ u₁ = u₁ ∧ (v₀ ⊔ u₀) ⊓ u₁ = u₁ ∧ (u₁ ⊔ v₀) ⊓ v₁ = v₀ ∧ (u₀ ⊔ v₀) ⊓ v₁ = v₀) ∨
    (u₀ ≤ v₁ ∧ v₀ ≤ u₁ ∧ (v₁ ⊔ u₀) ⊓ u₁ = u₁ ⊓ v₁ ∧ (v₀ ⊔ u₀) ⊓ u₁ = u₀ ⊔ v₀ ∧
      (u₁ ⊔ v₀) ⊓ v₁ = u₁ ⊓ v₁ ∧ (u₀ ⊔ v₀) ⊓ v₁ = u₀ ⊔ v₀) := by
  rcases le_or_gt v₁ u₀ with hvu | huv
  · have hv₀u₀ := hv.trans hvu
    exact Or.inl ⟨by rw [sup_eq_right.mpr hvu, inf_eq_left.mpr hu],
      by rw [sup_eq_right.mpr hv₀u₀, inf_eq_left.mpr hu],
      by rw [sup_eq_left.mpr (hv₀u₀.trans hu), inf_eq_right.mpr (hvu.trans hu)],
      by rw [sup_eq_left.mpr hv₀u₀, inf_eq_right.mpr hvu]⟩
  · rcases le_or_gt u₁ v₀ with huv' | hvu'
    · have hu₀v₀ := hu.trans huv'
      exact Or.inr <| Or.inl
        ⟨by rw [sup_eq_left.mpr (hu₀v₀.trans hv), inf_eq_right.mpr (huv'.trans hv)],
          by rw [sup_eq_left.mpr hu₀v₀, inf_eq_right.mpr huv'],
          by rw [sup_eq_right.mpr huv', inf_eq_left.mpr hv],
          by rw [sup_eq_right.mpr hu₀v₀, inf_eq_left.mpr hv]⟩
    · exact Or.inr <| Or.inr ⟨huv.le, hvu'.le, by rw [sup_eq_left.mpr huv.le, inf_comm],
        by rw [sup_comm, inf_eq_left.mpr (sup_le hu hvu'.le)],
        by rw [sup_eq_left.mpr hvu'.le], inf_eq_left.mpr (sup_le huv.le hv)⟩

private theorem clamp_sub_eq_clamp_sub {γ : Path a b}
    {u₀ u₁ v₀ v₁ : I} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    {z₁ z₂ : E} {r₁ r₂ : ℝ} {g₁ g₂ : E → F}
    (hγ₁ : MapsTo γ (Icc u₀ u₁) (ball z₁ r₁)) (hγ₂ : MapsTo γ (Icc v₀ v₁) (ball z₂ r₂))
    (hd₁ : ∀ w ∈ ball z₁ r₁, HasFDerivAt g₁ (φ w) w)
    (hd₂ : ∀ w ∈ ball z₂ r₂, HasFDerivAt g₂ (φ w) w) :
    g₁ (γ ((v₁ ⊔ u₀) ⊓ u₁)) - g₁ (γ ((v₀ ⊔ u₀) ⊓ u₁)) =
      g₂ (γ ((u₁ ⊔ v₀) ⊓ v₁)) - g₂ (γ ((u₀ ⊔ v₀) ⊓ v₁)) := by
  rcases clamp_pair_cases hu hv with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ |
      ⟨huv, hvu', h₁, h₂, h₃, h₄⟩
  · rw [h₁, h₂, h₃, h₄, sub_self, sub_self]
  · rw [h₁, h₂, h₃, h₄, sub_self, sub_self]
  · rw [h₁, h₂, h₃, h₄]
    exact localPotential_sub_eq_sub_on_ball_inter hd₁ hd₂
      ⟨hγ₁ ⟨le_sup_left, sup_le hu hvu'⟩, hγ₂ ⟨le_sup_right, sup_le huv hv⟩⟩
      ⟨hγ₁ ⟨le_inf hu huv, inf_le_left⟩, hγ₂ ⟨le_inf hvu' hv, inf_le_right⟩⟩

private theorem sub_eq_sum_range_clamp_sub {M : Type*} [AddCommGroup M] (f : I → M)
    {k : ℕ} {s : ℕ → I} (hs0 : s 0 = 0) (hsk : s k = 1) {u₀ u₁ : I} (hu : u₀ ≤ u₁) :
    f u₁ - f u₀ =
      ∑ j ∈ Finset.range k, (f ((s (j + 1) ⊔ u₀) ⊓ u₁) - f ((s j ⊔ u₀) ⊓ u₁)) := by
  rw [Finset.sum_range_sub (fun j ↦ f ((s j ⊔ u₀) ⊓ u₁)) k, hs0, hsk,
    sup_eq_right.mpr unitInterval.nonneg', inf_eq_left.mpr hu,
    sup_eq_left.mpr unitInterval.le_one', inf_eq_right.mpr unitInterval.le_one']

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
  calc
    ∑ i ∈ Finset.range m, (g₁ i (γ (t₁ (i + 1))) - g₁ i (γ (t₁ i)))
      = ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n, (g₁ i (γ (τ i (j + 1))) - g₁ i (γ (τ i j))) :=
        Finset.sum_congr rfl fun i hi ↦
          sub_eq_sum_range_clamp_sub (g₁ i ∘ γ) ht₂0 ht₂n (hle₁ i (Finset.mem_range.mp hi))
    _ = ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n, (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))) :=
        Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦
          clamp_sub_eq_clamp_sub (hle₁ i (Finset.mem_range.mp hi))
            (hle₂ j (Finset.mem_range.mp hj)) (hγ₁ i (Finset.mem_range.mp hi))
            (hγ₂ j (Finset.mem_range.mp hj)) (hd₁ i (Finset.mem_range.mp hi))
            (hd₂ j (Finset.mem_range.mp hj))
    _ = ∑ j ∈ Finset.range n,
          ∑ i ∈ Finset.range m, (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range n, (g₂ j (γ (t₂ (j + 1))) - g₂ j (γ (t₂ j))) :=
        Finset.sum_congr rfl fun j hj ↦
          (sub_eq_sum_range_clamp_sub (g₂ j ∘ γ) ht₁0 ht₁m (hle₂ j (Finset.mem_range.mp hj))).symm

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

/-- Whenever `φ` admits some local-potential curve integral along `γ`, `v` satisfies
`HasLocalPotentialCurveIntegral φ γ v` if and only if `localPotentialCurveIntegral φ γ = v`. -/
theorem hasLocalPotentialCurveIntegral_iff_eq {γ : Path a b}
    (hex : ∃ w, HasLocalPotentialCurveIntegral φ γ w) {v : F} :
    HasLocalPotentialCurveIntegral φ γ v ↔ localPotentialCurveIntegral φ γ = v := by
  obtain ⟨w, hw⟩ := hex
  exact ⟨fun h ↦ h.localPotentialCurveIntegral_eq,
    fun h ↦ h ▸ hw.localPotentialCurveIntegral_eq ▸ hw⟩

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
  obtain ⟨n, t, idx, ht0, htn, hle, hmap⟩ :=
    exists_ball_subdivision_Icc (zero_le_one : (0 : I) ≤ 1) (fun τ _ ↦ hγ τ) r hr
  exact ⟨n, t, fun i ↦ (idx i).1, fun i ↦ r (idx i), fun i ↦ g (idx i), ht0, htn, hle,
    fun i _ ↦ hrs (idx i), hmap, fun i _ ↦ hg (idx i), fun i _ ↦ hd (idx i)⟩

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
  TauCeti.hasLocalPotentialCurveIntegral_iff_eq (hφ.exists_hasLocalPotentialCurveIntegral hγ)

/-- If `φ` is the Fréchet derivative of a global function `g` on an open set `s`, then its
local-potential curve integral along any path in `s` from `a` to `b` is `g b - g a`. -/
theorem hasLocalPotentialCurveIntegral_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hd : ∀ y ∈ s, HasFDerivAt g (φ y) y) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialCurveIntegral φ γ (g b - g a) := by
  have h := hasLocalPotentialCurveIntegral_of_open_subdivision (n := 1)
    (t := fun i ↦ if i = 0 then 0 else 1) (U := fun _ ↦ s) (g := fun _ ↦ g) rfl (by simp)
    (fun i hi ↦ by obtain rfl := Nat.lt_one_iff.mp hi; exact zero_le_one)
    (fun _ _ ↦ hs) (fun _ _ τ _ ↦ hγ τ) (fun _ _ ↦ hd)
  simpa only [Finset.range_one, Finset.sum_singleton, Nat.zero_add, one_ne_zero, ↓reduceIte,
    γ.target, γ.source] using h

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
      HasLocalPotentialCurveIntegral φ γ v := by subst ha hb; rw [Path.cast_rfl_rfl]

/-- Casting path endpoints preserves `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_cast (φ : E → E →L[ℝ] F) (γ : Path a b)
    (ha : c = a) (hb : d = b) :
    localPotentialCurveIntegral φ (γ.cast ha hb) = localPotentialCurveIntegral φ γ := by
  subst ha hb; rw [Path.cast_rfl_rfl]

/-- Pointwise equal paths have the same `HasLocalPotentialCurveIntegral` witnesses. -/
theorem HasLocalPotentialCurveIntegral.congr_path {γ₁ : Path a b} {γ₂ : Path c d} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ₁ v) (hγ : ∀ t, γ₁ t = γ₂ t) :
    HasLocalPotentialCurveIntegral φ γ₂ v := by
  have ha : c = a := (γ₂.source.symm.trans (hγ 0).symm).trans γ₁.source
  have hb : d = b := (γ₂.target.symm.trans (hγ 1).symm).trans γ₁.target
  subst ha hb; exact Path.ext (funext hγ) ▸ h

/-- Pointwise equal paths have equal `localPotentialCurveIntegral`. -/
theorem localPotentialCurveIntegral_congr_path {γ₁ : Path a b} {γ₂ : Path c d}
    (hγ : ∀ t, γ₁ t = γ₂ t) :
    localPotentialCurveIntegral φ γ₁ = localPotentialCurveIntegral φ γ₂ := by
  have ha : c = a := (γ₂.source.symm.trans (hγ 0).symm).trans γ₁.source
  have hb : d = b := (γ₂.target.symm.trans (hγ 1).symm).trans γ₁.target
  subst ha hb; exact congrArg (localPotentialCurveIntegral φ) (Path.ext (funext hγ))

/-- If two fields agree on an open set `s` containing `γ`, any `HasLocalPotentialCurveIntegral`
witness for `φ` along `γ` is also one for `ψ`. -/
theorem HasLocalPotentialCurveIntegral.congr {γ : Path a b} {v : F}
    (hφ : HasLocalPotentialCurveIntegral φ γ v) (hs : IsOpen s) (h : EqOn φ ψ s)
    (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialCurveIntegral ψ γ v := by
  rcases hφ with ⟨n, t, z, r, g, ht0, htn, hle, hmap, hd, rfl⟩
  exact hasLocalPotentialCurveIntegral_of_open_subdivision ht0 htn hle
    (fun _ _ ↦ isOpen_ball.inter hs) (fun i hi τ hτ ↦ ⟨hmap i hi hτ, hγ τ⟩)
    (fun i hi y hy ↦ h hy.2 ▸ hd i hi y hy.1)

/-- On an open set `s` containing `γ`, `EqOn φ ψ s` preserves and reflects
`HasLocalPotentialCurveIntegral`. -/
theorem hasLocalPotentialCurveIntegral_congr_iff (hs : IsOpen s) (h : EqOn φ ψ s)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) {v : F} :
    HasLocalPotentialCurveIntegral φ γ v ↔ HasLocalPotentialCurveIntegral ψ γ v :=
  ⟨fun hφ ↦ hφ.congr hs h hγ, fun hψ ↦ hψ.congr hs h.symm hγ⟩

/-- Two covector fields that agree on an open set `s` have the same `localPotentialCurveIntegral`
along every path in `s`. -/
theorem localPotentialCurveIntegral_congr (hs : IsOpen s) (h : EqOn φ ψ s)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = localPotentialCurveIntegral ψ γ := by
  by_cases hex : ∃ v, HasLocalPotentialCurveIntegral φ γ v
  · obtain ⟨v, hv⟩ := hex
    rw [hv.localPotentialCurveIntegral_eq, (hv.congr hs h hγ).localPotentialCurveIntegral_eq]
  · have hex' : ¬∃ v, HasLocalPotentialCurveIntegral ψ γ v := fun ⟨v, hv⟩ ↦
      hex ⟨v, hv.congr hs h.symm hγ⟩
    rw [localPotentialCurveIntegral_of_not_exists hex,
      localPotentialCurveIntegral_of_not_exists hex']

/-- If two fields agree on `s` and have local potentials on `s`, they have the same curve integral
along every path in `s`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_congr (hφ : HasLocalPotentials s φ)
    (h : EqOn φ ψ s) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = localPotentialCurveIntegral ψ γ :=
  TauCeti.localPotentialCurveIntegral_congr hφ.isOpen h hγ

/-- Reversing a path negates `HasLocalPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.symm {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    HasLocalPotentialCurveIntegral φ γ.symm (-v) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  have hsub : ∀ k < n, n - k = n - 1 - k + 1 ∧ n - (k + 1) = n - 1 - k := fun _ _ ↦ by omega
  refine ⟨n, fun k ↦ unitInterval.symm (t (n - k)), fun k ↦ z (n - 1 - k),
    fun k ↦ r (n - 1 - k), fun k ↦ g (n - 1 - k), by simp [htn], by simp [ht0], ?_, ?_,
    fun k hk ↦ hd (n - 1 - k) (by omega), ?_⟩
  · intro k hk; dsimp only
    rw [(hsub k hk).1, (hsub k hk).2, unitInterval.symm_le_symm]; exact hle (n - 1 - k) (by omega)
  · intro k hk τ hτ
    rw [Path.symm_apply, Function.comp_apply]
    exact hγ (n - 1 - k) (by omega)
      ⟨(hsub k hk).2 ▸ unitInterval.le_symm_comm.mp hτ.2,
        (hsub k hk).1 ▸ unitInterval.symm_le_comm.mp hτ.1⟩
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k < n := Finset.mem_range.mp hk
    dsimp only; simp only [(hsub k hkn).1, (hsub k hkn).2, Path.symm_apply, Function.comp_apply,
      unitInterval.symm_symm, neg_sub]

/-- Reversing a path negates `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_symm (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral φ γ.symm = -localPotentialCurveIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialCurveIntegral_eq, hv.symm.localPotentialCurveIntegral_eq]
  · have h' : ¬∃ w, HasLocalPotentialCurveIntegral φ γ.symm w := fun ⟨w, hw⟩ ↦
      h ⟨-w, by simpa only [Path.symm_symm, neg_neg] using hw.symm⟩
    rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
      neg_zero]

private noncomputable def halfLeft (x : I) : I :=
  ⟨(x : ℝ) / 2, ⟨by linarith [x.2.1], by linarith [x.2.2]⟩⟩

private noncomputable def halfRight (x : I) : I :=
  ⟨((x : ℝ) + 1) / 2, ⟨by linarith [x.2.1], by linarith [x.2.2]⟩⟩

private theorem halfLeft_zero : halfLeft 0 = 0 := by ext; simp [halfLeft]
private theorem halfLeft_one_eq_halfRight_zero : halfLeft 1 = halfRight 0 := by
  ext; simp [halfLeft, halfRight]
private theorem halfRight_one : halfRight 1 = 1 := by ext; simp [halfRight]
private theorem halfLeft_mono : Monotone halfLeft := fun _ _ huv ↦
  Subtype.coe_le_coe.mp (by dsimp only [halfLeft]; linarith [Subtype.coe_le_coe.mpr huv])
private theorem halfRight_mono : Monotone halfRight := fun _ _ huv ↦
  Subtype.coe_le_coe.mp (by dsimp only [halfRight]; linarith [Subtype.coe_le_coe.mpr huv])

private theorem trans_halfLeft {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (γ₁ : Path x₀ x₁) (γ₂ : Path x₁ x₂) (x : I) :
    (γ₁.trans γ₂) (halfLeft x) = γ₁ x :=
  γ₁.trans_apply_of_eq_two_mul γ₂ x (by simp [halfLeft]; ring)

private theorem trans_halfRight {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (γ₁ : Path x₀ x₁) (γ₂ : Path x₁ x₂) (x : I) :
    (γ₁.trans γ₂) (halfRight x) = γ₂ x :=
  γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ x (by simp [halfRight]; ring)

private theorem mapsTo_trans_Icc_halfLeft {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    {γ₁ : Path x₀ x₁} (γ₂ : Path x₁ x₂) {u v : I} {U : Set X} (hγ₁ : MapsTo γ₁ (Icc u v) U) :
    MapsTo (γ₁.trans γ₂) (Icc (halfLeft u) (halfLeft v)) U := fun τ hτ ↦ by
  have h1 := Subtype.coe_le_coe.mpr hτ.1
  have h2 := Subtype.coe_le_coe.mpr hτ.2
  have hmem : 2 * (τ : ℝ) ∈ I := ⟨by linarith [τ.2.1], by dsimp [halfLeft] at h2; linarith [v.2.2]⟩
  rw [γ₁.trans_apply_of_eq_two_mul γ₂ ⟨2 * τ, hmem⟩ rfl]
  exact hγ₁ ⟨Subtype.coe_le_coe.mp (by dsimp [halfLeft] at h1 ⊢; linarith),
    Subtype.coe_le_coe.mp (by dsimp [halfLeft] at h2 ⊢; linarith)⟩

private theorem mapsTo_trans_Icc_halfRight {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (γ₁ : Path x₀ x₁) {γ₂ : Path x₁ x₂} {u v : I} {U : Set X} (hγ₂ : MapsTo γ₂ (Icc u v) U) :
    MapsTo (γ₁.trans γ₂) (Icc (halfRight u) (halfRight v)) U := fun τ hτ ↦ by
  have h1 := Subtype.coe_le_coe.mpr hτ.1
  have h2 := Subtype.coe_le_coe.mpr hτ.2
  have hmem : 2 * (τ : ℝ) - 1 ∈ I :=
    ⟨by dsimp [halfRight] at h1; linarith [u.2.1], by linarith [τ.2.2]⟩
  rw [γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ ⟨2 * τ - 1, hmem⟩ rfl]
  exact hγ₂ ⟨Subtype.coe_le_coe.mp (by dsimp [halfRight] at h1 ⊢; linarith),
    Subtype.coe_le_coe.mp (by dsimp [halfRight] at h2 ⊢; linarith)⟩

/-- Concatenating two paths adds their local-potential curve integrals. -/
theorem HasLocalPotentialCurveIntegral.trans {γ₁ : Path a b} {γ₂ : Path b c} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialCurveIntegral φ γ₁ v₁) (h₂ : HasLocalPotentialCurveIntegral φ γ₂ v₂) :
    HasLocalPotentialCurveIntegral φ (γ₁.trans γ₂) (v₁ + v₂) := by
  rcases h₁ with ⟨m, t₁, z₁, r₁, g₁, ht₁0, ht₁m, hle₁, hγ₁, hd₁, rfl⟩
  rcases h₂ with ⟨n, t₂, z₂, r₂, g₂, ht₂0, ht₂n, hle₂, hγ₂, hd₂, rfl⟩
  -- Rescale `t₁` into `[0, 1 / 2]` and `t₂` into `[1 / 2, 1]`, joining at `t m = 1 / 2`.
  have hm_pos : 0 < m := by
    by_contra hm0; exact zero_ne_one (ht₁0.symm.trans (Nat.eq_zero_of_not_pos hm0 ▸ ht₁m))
  let t : ℕ → I := fun k ↦ if k < m then halfLeft (t₁ k) else halfRight (t₂ (k - m))
  have ht_left : ∀ i ≤ m, t i = halfLeft (t₁ i) := fun i hi ↦ by
    rcases lt_or_eq_of_le hi with him | rfl <;>
      [exact ite_eq_left him; simp [t, ht₂0, ht₁m, halfLeft_one_eq_halfRight_zero]]
  have ht_right : ∀ j, t (m + j) = halfRight (t₂ j) := fun j ↦ by
    simp [t, Nat.not_lt.mpr (Nat.le_add_right m j)]
  refine ⟨m + n, t, fun k ↦ if k < m then z₁ k else z₂ (k - m),
    fun k ↦ if k < m then r₁ k else r₂ (k - m), fun k ↦ if k < m then g₁ k else g₂ (k - m),
    by rw [ht_left 0 hm_pos.le, ht₁0, halfLeft_zero],
    by rw [ht_right n, ht₂n, halfRight_one], ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hkm : k < m
    · rw [ht_left k hkm.le, ht_left (k + 1) (Nat.succ_le_of_lt hkm)]
      exact halfLeft_mono (hle₁ k hkm)
    · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, (Nat.add_sub_of_le (Nat.not_lt.mp hkm)).symm⟩
      rw [Nat.add_assoc, ht_right j, ht_right (j + 1)]; exact halfRight_mono (hle₂ j (by omega))
  · intro k hk
    by_cases hkm : k < m
    · simpa only [ite_eq_left hkm, ht_left k hkm.le,
        ht_left (k + 1) (Nat.succ_le_of_lt hkm)] using mapsTo_trans_Icc_halfLeft γ₂ (hγ₁ k hkm)
    · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, (Nat.add_sub_of_le (Nat.not_lt.mp hkm)).symm⟩
      simpa only [ite_eq_right hkm, Nat.add_sub_cancel_left, Nat.add_assoc, ht_right j,
        ht_right (j + 1)] using mapsTo_trans_Icc_halfRight γ₁ (hγ₂ j (by omega))
  · intro k hk
    by_cases hkm : k < m <;>
      [simpa only [ite_eq_left hkm] using hd₁ k hkm;
        simpa only [ite_eq_right hkm] using hd₂ (k - m) (by omega)]
  · rw [Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have him : i < m := Finset.mem_range.mp hi
      simp [him, ht_left i him.le, ht_left (i + 1) (Nat.succ_le_of_lt him), trans_halfLeft]
    · exact Finset.sum_congr rfl fun j _ ↦ by
        simp [Nat.not_lt.mpr (Nat.le_add_right m j), Nat.add_assoc, ht_right, trans_halfRight]

/-- Concatenating two paths adds `localPotentialCurveIntegral` whenever both paths admit
local-potential subdivisions. -/
theorem localPotentialCurveIntegral_trans {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : ∃ v, HasLocalPotentialCurveIntegral φ γ₁ v)
    (h₂ : ∃ v, HasLocalPotentialCurveIntegral φ γ₂ v) :
    localPotentialCurveIntegral φ (γ₁.trans γ₂) =
      localPotentialCurveIntegral φ γ₁ + localPotentialCurveIntegral φ γ₂ := by
  obtain ⟨v₁, hv₁⟩ := h₁; obtain ⟨v₂, hv₂⟩ := h₂
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
    HasLocalPotentialCurveIntegral (fun _ ↦ L) γ (L b - L a) :=
  hasLocalPotentialCurveIntegral_of_hasFDerivAt isOpen_univ (fun _ _ ↦ L.hasFDerivAt)
    fun _ ↦ mem_univ _

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
  refine ⟨n, t, z, r, fun i ↦ -g i, ht0, htn, hle, hγ, fun i hi y hy ↦ (hd i hi y hy).neg, ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.neg_apply]; abel

/-- Negating a covector field negates `localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_neg (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral (-φ) γ = -localPotentialCurveIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialCurveIntegral_eq, hv.neg.localPotentialCurveIntegral_eq]
  · have h' : ¬∃ w, HasLocalPotentialCurveIntegral (-φ) γ w := fun ⟨w, hw⟩ ↦
      h ⟨-w, by simpa only [neg_neg] using hw.neg⟩
    rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
      neg_zero]

/-- Scaling a covector field by a constant scalar scales `HasLocalPotentialCurveIntegral`. -/
theorem HasLocalPotentialCurveIntegral.smul {R : Type*} [Monoid R] [DistribMulAction R F]
    [SMulCommClass ℝ R F] [ContinuousConstSMul R F] (c : R) {γ : Path a b} {v : F}
    (h : HasLocalPotentialCurveIntegral φ γ v) :
    HasLocalPotentialCurveIntegral (c • φ) γ (c • v) := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  refine ⟨n, t, z, r, fun i ↦ c • g i, ht0, htn, hle, hγ,
    fun i hi y hy ↦ (hd i hi y hy).const_smul c, ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.smul_apply, smul_sub]

/-- Scaling a covector field by a scalar in a division ring scales
`localPotentialCurveIntegral`. -/
@[simp]
theorem localPotentialCurveIntegral_smul {R : Type*} [DivisionRing R] [Module R F]
    [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialCurveIntegral (c • φ) γ = c • localPotentialCurveIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases h : ∃ v, HasLocalPotentialCurveIntegral φ γ v
    · obtain ⟨v, hv⟩ := h
      rw [hv.localPotentialCurveIntegral_eq, (hv.smul c).localPotentialCurveIntegral_eq]
    · have h' : ¬∃ w, HasLocalPotentialCurveIntegral (c • φ) γ w := fun ⟨w, hw⟩ ↦
        h ⟨c⁻¹ • w, by simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hw.smul c⁻¹⟩
      rw [localPotentialCurveIntegral_of_not_exists h, localPotentialCurveIntegral_of_not_exists h',
        smul_zero]

private theorem exists_mem_subinterval {n : ℕ} {s : ℕ → I}
    (hs0 : s 0 = 0) (hsn : s n = 1) (x : I) :
    ∃ j < n, x ∈ Icc (s j) (s (j + 1)) := by
  have hn_pos : 0 < n := by
    by_contra hn0; exact zero_ne_one (hs0.symm.trans (Nat.eq_zero_of_not_pos hn0 ▸ hsn))
  suffices ∀ k, 1 ≤ k → k ≤ n → x ∈ Icc (s 0) (s k) → ∃ j < k, x ∈ Icc (s j) (s (j + 1)) from
    this n hn_pos le_rfl ⟨hs0 ▸ unitInterval.nonneg', hsn ▸ unitInterval.le_one'⟩
  intro k hk1 _ hx
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hk1 with _ | _
    · obtain rfl : k = 0 := by omega
      exact ⟨0, Nat.zero_lt_one, hx⟩
    · rcases le_or_gt x (s k) with hxk | hxk
      · obtain ⟨j, hj, hxj⟩ := ih (by omega) (by omega) ⟨hx.1, hxk⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
      · exact ⟨k, Nat.lt_succ_self k, ⟨hxk.le, hx.2⟩⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem exists_ball_inter_clamp_add {γ : Path a b}
    {n : ℕ} {t₂ : ℕ → I} {z₂ : ℕ → E} {r₂ : ℕ → ℝ} {g₂ : ℕ → E → F}
    (ht₂0 : t₂ 0 = 0) (ht₂n : t₂ n = 1) (hle₂ : ∀ j < n, t₂ j ≤ t₂ (j + 1))
    (hγ₂ : ∀ j < n, MapsTo γ (Icc (t₂ j) (t₂ (j + 1))) (ball (z₂ j) (r₂ j)))
    {u₀ u₁ : I} (hu : u₀ ≤ u₁) {z₁ : E} {r₁ : ℝ} (g₁ : E → F)
    (hγ₁ : MapsTo γ (Icc u₀ u₁) (ball z₁ r₁)) {j : ℕ} (hj : j < n) :
    ∃ j' < n,
      MapsTo γ (Icc ((t₂ j ⊔ u₀) ⊓ u₁) ((t₂ (j + 1) ⊔ u₀) ⊓ u₁))
        (ball z₁ r₁ ∩ ball (z₂ j') (r₂ j')) ∧
      (g₁ + g₂ j') (γ ((t₂ (j + 1) ⊔ u₀) ⊓ u₁)) - (g₁ + g₂ j') (γ ((t₂ j ⊔ u₀) ⊓ u₁)) =
        (g₁ (γ ((t₂ (j + 1) ⊔ u₀) ⊓ u₁)) - g₁ (γ ((t₂ j ⊔ u₀) ⊓ u₁))) +
          (g₂ j (γ ((u₁ ⊔ t₂ j) ⊓ t₂ (j + 1))) - g₂ j (γ ((u₀ ⊔ t₂ j) ⊓ t₂ (j + 1)))) := by
  rcases clamp_pair_cases hu (hle₂ j hj) with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ |
      ⟨_, _, h₁, h₂, h₃, h₄⟩
  · obtain ⟨j', hj', hmem⟩ := exists_mem_subinterval ht₂0 ht₂n u₀
    refine ⟨j', hj', ?_, by rw [h₁, h₂, h₃, h₄]; simp⟩
    rw [h₁, h₂, Icc_self]
    exact fun τ hτ ↦ mem_singleton_iff.mp hτ ▸ ⟨hγ₁ ⟨le_rfl, hu⟩, hγ₂ j' hj' hmem⟩
  · obtain ⟨j', hj', hmem⟩ := exists_mem_subinterval ht₂0 ht₂n u₁
    refine ⟨j', hj', ?_, by rw [h₁, h₂, h₃, h₄]; simp⟩
    rw [h₁, h₂, Icc_self]
    exact fun τ hτ ↦ mem_singleton_iff.mp hτ ▸ ⟨hγ₁ ⟨hu, le_rfl⟩, hγ₂ j' hj' hmem⟩
  · refine ⟨j, hj, fun τ hτ ↦ ?_, by rw [h₁, h₂, h₃, h₄]; simp only [Pi.add_apply]; abel⟩
    rw [h₂, h₁] at hτ
    exact ⟨hγ₁ ⟨le_sup_left.trans hτ.1, hτ.2.trans inf_le_left⟩,
      hγ₂ j hj ⟨le_sup_right.trans hτ.1, hτ.2.trans inf_le_right⟩⟩

private theorem HasSubdivisionUpTo.add_row {γ : Path a b}
    {n : ℕ} {t₂ : ℕ → I} {z₂ : ℕ → E} {r₂ : ℕ → ℝ} {g₂ : ℕ → E → F}
    (ht₂0 : t₂ 0 = 0) (ht₂n : t₂ n = 1) (hle₂ : ∀ j < n, t₂ j ≤ t₂ (j + 1))
    (hγ₂ : ∀ j < n, MapsTo γ (Icc (t₂ j) (t₂ (j + 1))) (ball (z₂ j) (r₂ j)))
    (hd₂ : ∀ j < n, ∀ y ∈ ball (z₂ j) (r₂ j), HasFDerivAt (g₂ j) (ψ y) y)
    {u₀ u₁ : I} (hu : u₀ ≤ u₁) {z₁ : E} {r₁ : ℝ} {g₁ : E → F}
    (hγ₁ : MapsTo γ (Icc u₀ u₁) (ball z₁ r₁))
    (hd₁ : ∀ y ∈ ball z₁ r₁, HasFDerivAt g₁ (φ y) y)
    {v : F} (huv : HasSubdivisionUpTo (φ + ψ) γ u₀ v) :
    HasSubdivisionUpTo (φ + ψ) γ u₁
      (v + ∑ j ∈ Finset.range n,
        ((g₁ (γ ((t₂ (j + 1) ⊔ u₀) ⊓ u₁)) - g₁ (γ ((t₂ j ⊔ u₀) ⊓ u₁))) +
          (g₂ j (γ ((u₁ ⊔ t₂ j) ⊓ t₂ (j + 1))) - g₂ j (γ ((u₀ ⊔ t₂ j) ⊓ t₂ (j + 1)))))) := by
  have h0 : (t₂ 0 ⊔ u₀) ⊓ u₁ = u₀ := by
    rw [ht₂0, sup_eq_right.mpr unitInterval.nonneg', inf_eq_left.mpr hu]
  have hn : (t₂ n ⊔ u₀) ⊓ u₁ = u₁ := by
    rw [ht₂n, sup_eq_left.mpr unitInterval.le_one', inf_eq_right.mpr unitInterval.le_one']
  suffices ∀ k ≤ n, HasSubdivisionUpTo (φ + ψ) γ ((t₂ k ⊔ u₀) ⊓ u₁)
      (v + ∑ j ∈ Finset.range k,
        ((g₁ (γ ((t₂ (j + 1) ⊔ u₀) ⊓ u₁)) - g₁ (γ ((t₂ j ⊔ u₀) ⊓ u₁))) +
          (g₂ j (γ ((u₁ ⊔ t₂ j) ⊓ t₂ (j + 1))) - g₂ j (γ ((u₀ ⊔ t₂ j) ⊓ t₂ (j + 1)))))) by
    simpa only [hn] using this n le_rfl
  intro k hk
  induction k with
  | zero => simpa only [h0, Finset.range_zero, Finset.sum_empty, add_zero] using huv
  | succ k ih =>
    have hkn : k < n := Nat.lt_of_succ_le hk
    obtain ⟨j', hj', hmap_inter, hdiff⟩ :=
      exists_ball_inter_clamp_add ht₂0 ht₂n hle₂ hγ₂ hu g₁ hγ₁ hkn
    have hstep := (ih hkn.le).step (inf_le_inf_right _ (sup_le_sup_right (hle₂ k hkn) _))
      (isOpen_ball.inter isOpen_ball) hmap_inter fun y hy ↦ (hd₁ y hy.1).add (hd₂ j' hj' y hy.2)
    rwa [hdiff, add_assoc v, ← Finset.sum_range_succ] at hstep

/-- Adding two covector fields adds their `HasLocalPotentialCurveIntegral` values along any
path. -/
theorem HasLocalPotentialCurveIntegral.add {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialCurveIntegral φ γ v₁) (h₂ : HasLocalPotentialCurveIntegral ψ γ v₂) :
    HasLocalPotentialCurveIntegral (φ + ψ) γ (v₁ + v₂) := by
  rcases h₁ with ⟨m, t₁, z₁, r₁, g₁, ht₁0, ht₁m, hle₁, hγ₁, hd₁, rfl⟩
  rcases h₂ with ⟨n, t₂, z₂, r₂, g₂, ht₂0, ht₂n, hle₂, hγ₂, hd₂, rfl⟩
  let τ : ℕ → ℕ → I := fun i j ↦ (t₂ j ⊔ t₁ i) ⊓ t₁ (i + 1)
  let υ : ℕ → ℕ → I := fun i j ↦ (t₁ i ⊔ t₂ j) ⊓ t₂ (j + 1)
  have hall : ∀ k ≤ m, HasSubdivisionUpTo (φ + ψ) γ (t₁ k)
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range n,
        ((g₁ i (γ (τ i (j + 1))) - g₁ i (γ (τ i j))) +
          (g₂ j (γ (υ (i + 1) j)) - g₂ j (γ (υ i j))))) := by
    intro k hk
    induction k with
    | zero =>
      simpa only [ht₁0, Finset.range_zero, Finset.sum_empty] using
        HasSubdivisionUpTo.zero (φ + ψ) γ
    | succ k ih =>
      have hkm : k < m := Nat.lt_of_succ_le hk
      rw [Finset.sum_range_succ]
      exact (ih hkm.le).add_row ht₂0 ht₂n hle₂ hγ₂ hd₂ (hle₁ k hkm) (hγ₁ k hkm) (hd₁ k hkm)
  convert (hall m le_rfl).toHasLocalPotentialCurveIntegral ht₁m using 1
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i hi ↦
      sub_eq_sum_range_clamp_sub (g₁ i ∘ γ) ht₂0 ht₂n (hle₁ i (Finset.mem_range.mp hi))
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j hj ↦
      sub_eq_sum_range_clamp_sub (g₂ j ∘ γ) ht₁0 ht₁m (hle₂ j (Finset.mem_range.mp hj))

/-- Subtracting two covector fields subtracts their `HasLocalPotentialCurveIntegral` values along
any path. -/
theorem HasLocalPotentialCurveIntegral.sub {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialCurveIntegral φ γ v₁) (h₂ : HasLocalPotentialCurveIntegral ψ γ v₂) :
    HasLocalPotentialCurveIntegral (φ - ψ) γ (v₁ - v₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Adding two covector fields adds `localPotentialCurveIntegral` whenever both admit
local-potential subdivisions along `γ`. -/
theorem localPotentialCurveIntegral_add {γ : Path a b}
    (hφ : ∃ v, HasLocalPotentialCurveIntegral φ γ v)
    (hψ : ∃ v, HasLocalPotentialCurveIntegral ψ γ v) :
    localPotentialCurveIntegral (φ + ψ) γ =
      localPotentialCurveIntegral φ γ + localPotentialCurveIntegral ψ γ := by
  obtain ⟨v₁, hv₁⟩ := hφ; obtain ⟨v₂, hv₂⟩ := hψ
  rw [hv₁.localPotentialCurveIntegral_eq, hv₂.localPotentialCurveIntegral_eq,
    (hv₁.add hv₂).localPotentialCurveIntegral_eq]

/-- Subtracting two covector fields subtracts `localPotentialCurveIntegral` whenever both admit
local-potential subdivisions along `γ`. -/
theorem localPotentialCurveIntegral_sub {γ : Path a b}
    (hφ : ∃ v, HasLocalPotentialCurveIntegral φ γ v)
    (hψ : ∃ v, HasLocalPotentialCurveIntegral ψ γ v) :
    localPotentialCurveIntegral (φ - ψ) γ =
      localPotentialCurveIntegral φ γ - localPotentialCurveIntegral ψ γ := by
  obtain ⟨v₁, hv₁⟩ := hφ; obtain ⟨v₂, hv₂⟩ := hψ
  rw [hv₁.localPotentialCurveIntegral_eq, hv₂.localPotentialCurveIntegral_eq,
    (hv₁.sub hv₂).localPotentialCurveIntegral_eq]

/-- Adding two covector fields with local potentials adds their curve integrals along any path in
their common domain. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_add (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral (φ + ψ) γ =
      localPotentialCurveIntegral φ γ + localPotentialCurveIntegral ψ γ :=
  TauCeti.localPotentialCurveIntegral_add
    (hφ.exists_hasLocalPotentialCurveIntegral hγ)
    (hψ.exists_hasLocalPotentialCurveIntegral hγ)

/-- Subtracting two covector fields with local potentials subtracts their curve integrals along any
path in their common domain. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_sub (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral (φ - ψ) γ =
      localPotentialCurveIntegral φ γ - localPotentialCurveIntegral ψ γ :=
  TauCeti.localPotentialCurveIntegral_sub
    (hφ.exists_hasLocalPotentialCurveIntegral hγ)
    (hψ.exists_hasLocalPotentialCurveIntegral hγ)

end Operations

/-! ### Pullback naturality -/

section Pullback

variable {s : Set E} {φ : E → E →L[ℝ] F}

/-- Pulling back a `HasLocalPotentialCurveIntegral` witness along `f : G → E` differentiable on an
open set `u` containing `γ` yields a `HasLocalPotentialCurveIntegral` witness for the pulled-back
covector field along `γ`. -/
theorem HasLocalPotentialCurveIntegral.of_map' {u : Set G} {f : G → E} {a b : G} {γ : Path a b}
    {v : F} (hu : IsOpen u) (hf : DifferentiableOn ℝ f u) (hγ : ∀ t, γ t ∈ u)
    (h : HasLocalPotentialCurveIntegral φ
      (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) v) :
    HasLocalPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ v := by
  rcases h with ⟨n, t, z, r, g, ht0, htn, hle, hmap, hd, rfl⟩
  have hU_open : ∀ i < n, IsOpen (u ∩ f ⁻¹' ball (z i) (r i)) := fun _ _ ↦
    isOpen_iff_mem_nhds.mpr fun x hx ↦ inter_mem (hu.mem_nhds hx.1)
      (((hf x hx.1).differentiableAt (hu.mem_nhds hx.1)).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds hx.2))
  have hγU : ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (u ∩ f ⁻¹' ball (z i) (r i)) :=
    fun i hi τ hτ ↦ ⟨hγ τ, mem_preimage.mpr
      (by simpa only [Path.map'_coe, Function.comp_apply] using hmap i hi hτ)⟩
  have hsub := hasLocalPotentialCurveIntegral_of_open_subdivision
    (φ := fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) (g := fun i ↦ g i ∘ f)
    ht0 htn hle hU_open hγU fun i hi y hy ↦
      (hd i hi (f y) hy.2).comp y (((hf y hy.1).differentiableAt (hu.mem_nhds hy.1)).hasFDerivAt)
  simpa only [Path.map'_coe, Function.comp_apply] using hsub

/-- Pulling back a `HasLocalPotentialCurveIntegral` witness along a globally differentiable map
`f : G → E` yields a witness for the pulled-back covector field along `γ`. -/
theorem HasLocalPotentialCurveIntegral.of_map {f : G → E} {a b : G} {γ : Path a b} {v : F}
    (hf : Differentiable ℝ f) (h : HasLocalPotentialCurveIntegral φ (γ.map hf.continuous) v) :
    HasLocalPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ v := by
  have heq : γ.map' (hf.differentiableOn.continuousOn.mono
      (range_subset_iff.mpr fun _ ↦ mem_univ _)) = γ.map hf.continuous := by
    ext τ; simp only [Path.map'_coe, Path.map_coe]
  exact HasLocalPotentialCurveIntegral.of_map' isOpen_univ hf.differentiableOn
    (fun _ ↦ mem_univ _) (heq ▸ h)

/-- Integrating `φ` along `γ.map'` equals integrating its Fréchet pullback along `γ` whenever
`γ.map'` admits a local-potential subdivision. -/
theorem localPotentialCurveIntegral_map' {u : Set G} {f : G → E} {a b : G} {γ : Path a b}
    (hu : IsOpen u) (hf : DifferentiableOn ℝ f u) (hγ : ∀ t, γ t ∈ u)
    (hex : ∃ v, HasLocalPotentialCurveIntegral φ
      (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) v) :
    localPotentialCurveIntegral φ (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) =
      localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ := by
  obtain ⟨v, hv⟩ := hex; rw [hv.localPotentialCurveIntegral_eq,
    (HasLocalPotentialCurveIntegral.of_map' hu hf hγ hv).localPotentialCurveIntegral_eq]

/-- Integrating `φ` along `γ.map hf.continuous` equals integrating its Fréchet pullback along `γ`
whenever `γ.map hf.continuous` admits a local-potential subdivision. -/
theorem localPotentialCurveIntegral_map {f : G → E} {a b : G} {γ : Path a b}
    (hf : Differentiable ℝ f)
    (hex : ∃ v, HasLocalPotentialCurveIntegral φ (γ.map hf.continuous) v) :
    localPotentialCurveIntegral φ (γ.map hf.continuous) =
      localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ := by
  obtain ⟨v, hv⟩ := hex; rw [hv.localPotentialCurveIntegral_eq,
    (HasLocalPotentialCurveIntegral.of_map hf hv).localPotentialCurveIntegral_eq]

/-- Integrating a covector field with local potentials on `s` along `γ.map'` equals integrating its
pullback along a map `f : G → E` differentiable on an open set `u` containing `γ`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_map' {u : Set G} {f : G → E}
    {a b : G} {γ : Path a b} (hφ : HasLocalPotentials s φ) (hu : IsOpen u)
    (hf : DifferentiableOn ℝ f u) (hγ : ∀ t, γ t ∈ u) (hγs : ∀ t, f (γ t) ∈ s) :
    localPotentialCurveIntegral φ (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) =
      localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ :=
  TauCeti.localPotentialCurveIntegral_map' hu hf hγ
    (hφ.exists_hasLocalPotentialCurveIntegral fun t ↦ by simpa [Path.map'_coe] using hγs t)

/-- Integrating a covector field with local potentials on `s` along `γ.map hf.continuous` equals
integrating its pullback along a globally differentiable map `f : G → E`. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_map {f : G → E}
    {a b : G} {γ : Path a b} (hφ : HasLocalPotentials s φ)
    (hf : Differentiable ℝ f) (hγ : ∀ t, f (γ t) ∈ s) :
    localPotentialCurveIntegral φ (γ.map hf.continuous) =
      localPotentialCurveIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ :=
  TauCeti.localPotentialCurveIntegral_map hf
    (hφ.exists_hasLocalPotentialCurveIntegral fun t ↦ by simpa [Path.map_coe] using hγ t)

end Pullback

/-! ### Homotopy invariance relative to endpoints -/

section Homotopy

variable {a b : E} {s : Set E} {φ : E → E →L[ℝ] F}

private theorem localPotentialCurveIntegral_eval_sub_eq_zero {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) {n : ℕ} {t : ℕ → I} (ht0 : t 0 = 0) (htn : t n = 1)
    (hle : ∀ j < n, t j ≤ t (j + 1)) {u₀ u₁ : I} (hu : u₀ ≤ u₁)
    {z : ℕ → E} {ρ : ℕ → ℝ} {G : ℕ → E → F}
    (hcell : ∀ j < n, ∀ p ∈ Icc u₀ u₁ ×ˢ Icc (t j) (t (j + 1)), H p ∈ ball (z j) (ρ j))
    (hd : ∀ j < n, ∀ w ∈ ball (z j) (ρ j), HasFDerivAt (G j) (φ w) w) :
    localPotentialCurveIntegral φ (H.eval u₁) - localPotentialCurveIntegral φ (H.eval u₀) = 0 := by
  have heval : ∀ u τ, (H.eval u) τ = H (u, τ) := fun _ _ ↦ by simp [Path.Homotopy.eval_apply]
  have hrow₀ : HasLocalPotentialCurveIntegral φ (H.eval u₀)
      (∑ j ∈ Finset.range n, (G j (H (u₀, t (j + 1))) - G j (H (u₀, t j)))) :=
    ⟨n, t, z, ρ, G, ht0, htn, hle, fun j hj τ hτ ↦ by
        rw [heval]; exact hcell j hj (u₀, τ) ⟨left_mem_Icc.mpr hu, hτ⟩, hd, by simp only [heval]⟩
  have hrow₁ : HasLocalPotentialCurveIntegral φ (H.eval u₁)
      (∑ j ∈ Finset.range n, (G j (H (u₁, t (j + 1))) - G j (H (u₁, t j)))) :=
    ⟨n, t, z, ρ, G, ht0, htn, hle, fun j hj τ hτ ↦ by
        rw [heval]; exact hcell j hj (u₁, τ) ⟨right_mem_Icc.mpr hu, hτ⟩, hd, by simp only [heval]⟩
  rw [hrow₀.localPotentialCurveIntegral_eq, hrow₁.localPotentialCurveIntegral_eq,
    ← Finset.sum_sub_distrib]
  let δ : ℕ → F := fun j ↦ if j < n then G j (H (u₁, t j)) - G j (H (u₀, t j)) else 0
  have hterm : ∀ j ∈ Finset.range n,
      (G j (H (u₁, t (j + 1))) - G j (H (u₁, t j))) -
        (G j (H (u₀, t (j + 1))) - G j (H (u₀, t j))) = δ (j + 1) - δ j := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hδj : δ j = G j (H (u₁, t j)) - G j (H (u₀, t j)) := ite_eq_left hjn
    have hδj1 : δ (j + 1) = G j (H (u₁, t (j + 1))) - G j (H (u₀, t (j + 1))) := by
      by_cases hj1 : j + 1 < n
      · dsimp only [δ]; rw [ite_eq_left hj1]
        exact (localPotential_sub_eq_sub_on_ball_inter (hd j hjn) (hd (j + 1) hj1)
          ⟨hcell j hjn (u₀, t (j + 1)) ⟨left_mem_Icc.mpr hu, right_mem_Icc.mpr (hle j hjn)⟩,
            hcell (j + 1) hj1 (u₀, t (j + 1))
              ⟨left_mem_Icc.mpr hu, left_mem_Icc.mpr (hle (j + 1) hj1)⟩⟩
          ⟨hcell j hjn (u₁, t (j + 1)) ⟨right_mem_Icc.mpr hu, right_mem_Icc.mpr (hle j hjn)⟩,
            hcell (j + 1) hj1 (u₁, t (j + 1))
              ⟨right_mem_Icc.mpr hu, left_mem_Icc.mpr (hle (j + 1) hj1)⟩⟩).symm
      · have hjeq : j + 1 = n := by omega
        simp [δ, hjeq, htn]
    rw [hδj, hδj1]; abel
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub δ n]
  have hδn : δ n = 0 := ite_eq_right (lt_irrefl n)
  have hδ0 : δ 0 = 0 := by by_cases hn0 : 0 < n <;> simp [δ, hn0, ht0]
  rw [hδn, hδ0, sub_self]

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
  have hle : ∀ j < n, t j ≤ t (j + 1) := fun j _ ↦ hmono (Nat.le_succ j)
  -- Telescope across all `n` rows from `H.eval (t 0) = γ₀` to `H.eval (t n) = γ₁`.
  have htel := Finset.sum_range_sub (fun i ↦ localPotentialCurveIntegral φ (H.eval (t i))) n
  have hzero : ∑ i ∈ Finset.range n,
      (localPotentialCurveIntegral φ (H.eval (t (i + 1))) -
        localPotentialCurveIntegral φ (H.eval (t i))) = 0 :=
    Finset.sum_eq_zero fun i hi ↦
      localPotentialCurveIntegral_eval_sub_eq_zero H ht0 htn hle (hle i (Finset.mem_range.mp hi))
        (fun j _ p hp ↦ hidx i j hp) (fun j _ ↦ hd (idx i j))
  rw [hzero, htn, ht0, H.eval_one, H.eval_zero] at htel
  exact (sub_eq_zero.mp htel.symm).symm

end Homotopy

end TauCeti
