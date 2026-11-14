/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Subpath
public import TauCeti.Analysis.Calculus.LocalPotentials.Basic
public import TauCeti.Topology.UnitInterval
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.Topology.Homotopy.Path

/-!
# Continuous path integration of one-forms with local potentials

For a continuous path `γ : Path a b` in a real normed space `E` and a covector field
`φ : E → E →L[ℝ] F` taking values in a real normed space `F`, we define the continuous path
integral `TauCeti.localPotentialIntegral φ γ` through subdivisions of the unit interval into
subintervals mapped into open balls on which `φ` has ambient `C¹` potentials. On each subinterval
we take the endpoint difference of the chosen potential, so neither smoothness of `γ` nor
completeness of `F` is used.

Two subdivisions have the same sum of potential increments: clipping one partition to the
subintervals of the other reduces the comparison to overlapping intervals mapped into the convex
intersection of two balls, where any two potentials of `φ` have the same endpoint increment by the
mean value theorem. Consequently `TauCeti.HasLocalPotentialIntegral` is single-valued, and
`TauCeti.localPotentialIntegral` satisfies the standard calculus of path integrals:

* evaluation on any global potential (`localPotentialIntegral_eq_sub_of_hasFDerivAt`) and on
  constant covector fields (`localPotentialIntegral_const`), valid along arbitrary continuous paths;
* path operations (`localPotentialIntegral_refl`, `localPotentialIntegral_cast`,
  `localPotentialIntegral_symm`, `HasLocalPotentials.localPotentialIntegral_trans`, and subdivision
  into subpaths `HasLocalPotentials.localPotentialIntegral_eq_sum_subpath`);
* linearity in the covector field and congruence on open domains;
* naturality under `C¹` maps (`HasLocalPotentials.localPotentialIntegral_pullback`);
* invariance under path homotopy relative to the endpoints inside the domain
  (`HasLocalPotentials.localPotentialIntegral_eq_of_homotopy`), proved by subdividing `I × I` into
  small rectangles mapped into potential balls and cancelling the vertical potential increments;
* agreement with Mathlib's Bochner `curveIntegral` along `C¹` paths when `F` is complete
  (`HasLocalPotentials.localPotentialIntegral_eq_curveIntegral`);
* construction of a global `C¹` potential on a path-connected open set from vanishing loop
  integrals
  (`HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialIntegral_loop_eq_zero`).

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, Section 1.4 (integration along
  continuous curves by chains of discs and homotopy invariance).
* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, Section 2 (curvilinear integrals of locally exact differential forms along continuous
  paths and exactness on simply connected domains).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
-/

public section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff unitInterval Interval

namespace TauCeti

section UniquenessOfPotentials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s u : Set E} {φ : E → E →L[ℝ] F}

/-- On a preconnected open set, two functions with the same Fréchet derivative at every point have
equal endpoint increments. -/
theorem sub_eq_sub_of_hasFDerivAt_of_isPreconnected (hu : IsOpen u) (hconn : IsPreconnected u)
    {g₁ g₂ : E → F} (hd₁ : ∀ y ∈ u, HasFDerivAt g₁ (φ y) y)
    (hd₂ : ∀ y ∈ u, HasFDerivAt g₂ (φ y) y) {p q : E} (hp : p ∈ u) (hq : q ∈ u) :
    g₁ q - g₁ p = g₂ q - g₂ p := by
  have hconst : (g₁ - g₂) q = (g₁ - g₂) p := by
    refine hu.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hconn ?_ ?_ hq hp
    · intro y hy
      exact ((hd₁ y hy).sub (hd₂ y hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      simpa using ((hd₁ y hy).sub (hd₂ y hy)).fderiv
  simp only [Pi.sub_apply] at hconst
  calc
    g₁ q - g₁ p = (g₁ q - g₂ q) - (g₁ p - g₂ p) + (g₂ q - g₂ p) := by abel
    _ = (g₁ p - g₂ p) - (g₁ p - g₂ p) + (g₂ q - g₂ p) := by rw [hconst]
    _ = g₂ q - g₂ p := by abel

/-- On a preconnected open set, two potentials of the same covector field differ by an additive
constant. -/
theorem exists_eqOn_add_const_of_hasFDerivAt (hu : IsOpen u) (hconn : IsPreconnected u)
    {g₁ g₂ : E → F} (hd₁ : ∀ y ∈ u, HasFDerivAt g₁ (φ y) y)
    (hd₂ : ∀ y ∈ u, HasFDerivAt g₂ (φ y) y) :
    ∃ c : F, EqOn g₁ (fun x ↦ g₂ x + c) u := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp⟩
  · refine ⟨g₁ x₀ - g₂ x₀, fun x hx ↦ ?_⟩
    have h := sub_eq_sub_of_hasFDerivAt_of_isPreconnected hu hconn hd₁ hd₂ hx₀ hx
    dsimp only
    rw [← add_sub_assoc, eq_sub_iff_add_eq]
    calc
      g₁ x + g₂ x₀ = (g₁ x - g₁ x₀) + g₁ x₀ + g₂ x₀ := by abel
      _ = (g₂ x - g₂ x₀) + g₁ x₀ + g₂ x₀ := by rw [h]
      _ = g₂ x + g₁ x₀ := by abel

/-- Any function whose Fréchet derivative on `s` agrees with a locally potential covector field `φ`
is automatically `C¹` on `s`, since on each potential ball it differs from a `C¹` potential by a
constant. -/
theorem HasLocalPotentials.contDiffOn_of_hasFDerivAt (hφ : HasLocalPotentials s φ) {g : E → F}
    (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x) : ContDiffOn ℝ 1 g s := by
  intro x hx
  obtain ⟨r, hr, hrs, g₀, hg₀, hd₀⟩ := hasLocalPotentials_iff.mp hφ x hx
  have heq : g =ᶠ[𝓝 x] fun y ↦ g₀ y + (g x - g₀ x) := by
    filter_upwards [ball_mem_nhds x hr] with y hy
    have h := sub_eq_sub_of_hasFDerivAt_of_isPreconnected isOpen_ball
      (convex_ball x r).isPreconnected (fun z hz ↦ hd z (hrs hz)) hd₀ (mem_ball_self hr) hy
    calc
      g y = (g y - g x) + g x := by abel
      _ = (g₀ y - g₀ x) + g x := by rw [h]
      _ = g₀ y + (g x - g₀ x) := by abel
  exact (((hg₀.contDiffAt (ball_mem_nhds x hr)).add contDiffAt_const).congr_of_eventuallyEq
    heq).contDiffWithinAt

end UniquenessOfPotentials

section Definition

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : Set E} {φ ψ φ₁ φ₂ : E → E →L[ℝ] F} {a b c a' b' : E}

/-- `HasLocalPotentialIntegral φ γ v` states that `γ : Path a b` admits a partition
`0 = t₀ ≤ ⋯ ≤ tₙ = 1` of the unit interval whose consecutive subintervals map into open balls on
each of which `φ` is the derivative of an ambient `C¹` function, with the endpoint differences of
those potentials summing to `v`. -/
def HasLocalPotentialIntegral (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) (v : F) : Prop :=
  ∃ (n : ℕ) (P : unitInterval.Partition n) (c : Fin n → E) (r : Fin n → ℝ) (g : Fin n → E → F),
    (∀ k, MapsTo γ (Icc (P.t k.castSucc) (P.t k.succ)) (ball (c k) (r k))) ∧
    (∀ k, ContDiffOn ℝ 1 (g k) (ball (c k) (r k))) ∧
    (∀ k, ∀ y ∈ ball (c k) (r k), HasFDerivAt (g k) (φ y) y) ∧
    ∑ k : Fin n, (g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc))) = v

/-- Unfolded characterization of `HasLocalPotentialIntegral`. -/
theorem hasLocalPotentialIntegral_iff {γ : Path a b} {v : F} :
    HasLocalPotentialIntegral φ γ v ↔
      ∃ (n : ℕ) (P : unitInterval.Partition n) (c : Fin n → E) (r : Fin n → ℝ) (g : Fin n → E → F),
        (∀ k, MapsTo γ (Icc (P.t k.castSucc) (P.t k.succ)) (ball (c k) (r k))) ∧
        (∀ k, ContDiffOn ℝ 1 (g k) (ball (c k) (r k))) ∧
        (∀ k, ∀ y ∈ ball (c k) (r k), HasFDerivAt (g k) (φ y) y) ∧
        ∑ k : Fin n, (g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc))) = v := Iff.rfl

/-- The continuous path integral via local potentials is independent of the partition, the balls,
and the chosen local potentials. -/
theorem HasLocalPotentialIntegral.unique {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialIntegral φ γ v₁) (h₂ : HasLocalPotentialIntegral φ γ v₂) :
    v₁ = v₂ := by
  obtain ⟨n₁, P₁, c₁, r₁, g₁, hmap₁, -, hd₁, rfl⟩ := h₁
  obtain ⟨n₂, P₂, c₂, r₂, g₂, hmap₂, -, hd₂, rfl⟩ := h₂
  -- Clip `P₂` to each subinterval of `P₁` and vice versa; both double sums telescope.
  let clip₁ : Fin n₁ → Fin (n₂ + 1) → I := fun i k ↦
    min (P₁.t i.succ) (max (P₁.t i.castSucc) (P₂.t k))
  let clip₂ : Fin n₂ → Fin (n₁ + 1) → I := fun j k ↦
    min (P₂.t j.succ) (max (P₂.t j.castSucc) (P₁.t k))
  have htel₁ (i : Fin n₁) :
      g₁ i (γ (P₁.t i.succ)) - g₁ i (γ (P₁.t i.castSucc)) =
        ∑ j : Fin n₂, (g₁ i (γ (clip₁ i j.succ)) - g₁ i (γ (clip₁ i j.castSucc))) := by
    have h0 : clip₁ i 0 = P₁.t i.castSucc := by
      simp [clip₁, P₁.t_castSucc_le_succ i]
    have hlast : clip₁ i (Fin.last n₂) = P₁.t i.succ := by
      have hle1 : P₁.t i.castSucc ≤ 1 := (P₁.t i.castSucc).2.2
      have hle2 : P₁.t i.succ ≤ 1 := (P₁.t i.succ).2.2
      simp [clip₁, max_eq_right hle1, min_eq_left hle2]
    rw [← hlast, ← h0, ← Fin.sum_univ_succ_sub_castSucc (fun k ↦ g₁ i (γ (clip₁ i k)))]
  have htel₂ (j : Fin n₂) :
      g₂ j (γ (P₂.t j.succ)) - g₂ j (γ (P₂.t j.castSucc)) =
        ∑ i : Fin n₁, (g₂ j (γ (clip₂ j i.succ)) - g₂ j (γ (clip₂ j i.castSucc))) := by
    have h0 : clip₂ j 0 = P₂.t j.castSucc := by
      simp [clip₂, P₂.t_castSucc_le_succ j]
    have hlast : clip₂ j (Fin.last n₁) = P₂.t j.succ := by
      have hle1 : P₂.t j.castSucc ≤ 1 := (P₂.t j.castSucc).2.2
      have hle2 : P₂.t j.succ ≤ 1 := (P₂.t j.succ).2.2
      simp [clip₂, max_eq_right hle1, min_eq_left hle2]
    rw [← hlast, ← h0, ← Fin.sum_univ_succ_sub_castSucc (fun k ↦ g₂ j (γ (clip₂ j k)))]
  simp_rw [htel₁, htel₂]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := P₁.t_castSucc_le_succ i
  have hj := P₂.t_castSucc_le_succ j
  rcases le_or_gt (P₂.t j.succ) (P₁.t i.castSucc) with hdisj₁ | hlt₁
  · -- `[P₂.t j, P₂.t (j+1)]` lies to the left of `[P₁.t i, P₁.t (i+1)]`.
    have h₁_lo : clip₁ i j.castSucc = P₁.t i.castSucc := by
      simp [clip₁, max_eq_left (hj.trans hdisj₁), min_eq_right hi]
    have h₁_hi : clip₁ i j.succ = P₁.t i.castSucc := by
      simp [clip₁, max_eq_left hdisj₁, min_eq_right hi]
    have h₂_lo : clip₂ j i.castSucc = P₂.t j.succ := by
      simp [clip₂, max_eq_right (hj.trans hdisj₁), min_eq_left hdisj₁]
    have h₂_hi : clip₂ j i.succ = P₂.t j.succ := by
      simp [clip₂, max_eq_right (hj.trans (hdisj₁.trans hi)), min_eq_left (hdisj₁.trans hi)]
    simp [h₁_lo, h₁_hi, h₂_lo, h₂_hi]
  rcases le_or_gt (P₁.t i.succ) (P₂.t j.castSucc) with hdisj₂ | hlt₂
  · -- `[P₁.t i, P₁.t (i+1)]` lies to the left of `[P₂.t j, P₂.t (j+1)]`.
    have h₁_lo : clip₁ i j.castSucc = P₁.t i.succ := by
      simp [clip₁, max_eq_right (hi.trans hdisj₂), min_eq_left hdisj₂]
    have h₁_hi : clip₁ i j.succ = P₁.t i.succ := by
      simp [clip₁, max_eq_right (hi.trans (hdisj₂.trans hj)), min_eq_left (hdisj₂.trans hj)]
    have h₂_lo : clip₂ j i.castSucc = P₂.t j.castSucc := by
      simp [clip₂, max_eq_left (hi.trans hdisj₂), min_eq_right hj]
    have h₂_hi : clip₂ j i.succ = P₂.t j.castSucc := by
      simp [clip₂, max_eq_left hdisj₂, min_eq_right hj]
    simp [h₁_lo, h₁_hi, h₂_lo, h₂_hi]
  · -- The two intervals overlap on `[max (P₁.t i) (P₂.t j), min (P₁.t (i+1)) (P₂.t (j+1))]`.
    let lo : I := max (P₁.t i.castSucc) (P₂.t j.castSucc)
    let hi' : I := min (P₁.t i.succ) (P₂.t j.succ)
    have h₁_lo : clip₁ i j.castSucc = lo := min_eq_right (max_le hi hlt₂.le)
    have h₂_lo : clip₂ j i.castSucc = lo := by
      simp only [clip₂, lo, max_comm (P₁.t i.castSucc)]
      exact min_eq_right (max_le hj hlt₁.le)
    have h₁_hi : clip₁ i j.succ = hi' := by
      dsimp only [clip₁, hi']
      rw [max_eq_right hlt₁.le]
    have h₂_hi : clip₂ j i.succ = hi' := by
      dsimp only [clip₂, hi']
      rw [max_eq_right hlt₂.le, min_comm]
    rw [h₁_lo, h₂_lo, h₁_hi, h₂_hi]
    have hlo₁ : lo ∈ Icc (P₁.t i.castSucc) (P₁.t i.succ) := ⟨le_max_left _ _, max_le hi hlt₂.le⟩
    have hlo₂ : lo ∈ Icc (P₂.t j.castSucc) (P₂.t j.succ) := ⟨le_max_right _ _, max_le hlt₁.le hj⟩
    have hhi₁ : hi' ∈ Icc (P₁.t i.castSucc) (P₁.t i.succ) := ⟨le_min hi hlt₁.le, min_le_left _ _⟩
    have hhi₂ : hi' ∈ Icc (P₂.t j.castSucc) (P₂.t j.succ) := ⟨le_min hlt₂.le hj, min_le_right _ _⟩
    exact sub_eq_sub_of_hasFDerivAt_of_isPreconnected (isOpen_ball.inter isOpen_ball)
      ((convex_ball (c₁ i) (r₁ i)).inter (convex_ball (c₂ j) (r₂ j))).isPreconnected
      (fun y hy ↦ hd₁ i y hy.1) (fun y hy ↦ hd₂ j y hy.2)
      ⟨hmap₁ i hlo₁, hmap₂ j hlo₂⟩ ⟨hmap₁ i hhi₁, hmap₂ j hhi₂⟩

/-- The continuous path integral of `φ` along `γ`, defined as the sum of endpoint differences of
local `C¹` potentials over a ball subdivision of `[0, 1]`, or `0` if no such subdivision exists. -/
noncomputable def localPotentialIntegral (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) : F :=
  open Classical in
  if h : ∃ v, HasLocalPotentialIntegral φ γ v then h.choose else 0

/-- A valid potential-subdivision sum equals `localPotentialIntegral φ γ`. -/
theorem HasLocalPotentialIntegral.localPotentialIntegral_eq {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) : localPotentialIntegral φ γ = v := by
  classical
  have hex : ∃ w, HasLocalPotentialIntegral φ γ w := ⟨v, h⟩
  simp only [localPotentialIntegral, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- When `φ` admits no ball-potential subdivision along `γ`, `localPotentialIntegral φ γ` takes the
junk value `0`. -/
theorem localPotentialIntegral_of_not_exists {γ : Path a b}
    (h : ¬ ∃ v, HasLocalPotentialIntegral φ γ v) : localPotentialIntegral φ γ = 0 := by
  classical
  simp only [localPotentialIntegral, h, ↓reduceDIte]

/-- Every continuous path inside a domain carrying local potentials admits a potential-subdivision
integral, obtained by subdividing `[0, 1]` via the Lebesgue number lemma. -/
theorem HasLocalPotentials.exists_hasLocalPotentialIntegral (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    ∃ v, HasLocalPotentialIntegral φ γ v := by
  obtain ⟨n, P, hcover⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (x : E) (r : ℝ) (g : E → F),
      U = ball x r ∧ ContDiffOn ℝ 1 g (ball x r) ∧ ∀ y ∈ ball x r, HasFDerivAt g (φ y) y)
    (fun z ⟨t, ht⟩ ↦ by
      obtain ⟨r, hr, _, g, hg, hd⟩ := hasLocalPotentials_iff.mp hφ z (ht ▸ hγ t)
      exact ⟨ball z r, isOpen_ball, mem_ball_self hr, z, r, g, rfl, hg, hd⟩)
  choose U _ hUP hmaps using hcover
  choose c r g hUeq hg hd using hUP
  refine ⟨∑ k : Fin n, (g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc))), n, P, c, r, g, ?_, hg,
    hd, rfl⟩
  intro k
  simpa only [← hUeq k] using hmaps k

/-- If `φ` has local potentials on `s` and `γ` stays in `s`, then `localPotentialIntegral φ γ`
witnesses `HasLocalPotentialIntegral`. -/
theorem HasLocalPotentials.hasLocalPotentialIntegral (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialIntegral φ γ (localPotentialIntegral φ γ) := by
  obtain ⟨v, hv⟩ := hφ.exists_hasLocalPotentialIntegral hγ
  rwa [hv.localPotentialIntegral_eq]

/-- A path admits a potential-subdivision sum if and only if its image lies in an open set on which
`φ` has local potentials. -/
theorem exists_hasLocalPotentialIntegral_iff_exists_hasLocalPotentials {γ : Path a b} :
    (∃ v, HasLocalPotentialIntegral φ γ v) ↔ ∃ s, HasLocalPotentials s φ ∧ ∀ t, γ t ∈ s := by
  refine ⟨?_, fun ⟨s, hφ, hγ⟩ ↦ hφ.exists_hasLocalPotentialIntegral hγ⟩
  rintro ⟨v, n, P, c, r, g, hmaps, hg, hd, -⟩
  refine ⟨⋃ k : Fin n, ball (c k) (r k),
    hasLocalPotentials_iUnion fun k ↦ hasLocalPotentials_of_hasFDerivAt isOpen_ball (hg k) (hd k),
    fun t ↦ ?_⟩
  -- Locate a subinterval `[P.t k, P.t (k + 1)]` containing `t`.
  have hcov : ∃ k : Fin n, t ∈ Icc (P.t k.castSucc) (P.t k.succ) := by
    by_contra! hnot
    have hlt : ∀ m : Fin (n + 1), P.t m ≤ t := by
      intro m
      induction m using Fin.induction with
      | zero =>
        rw [P.t_zero]
        exact t.2.1
      | succ k ih =>
        by_contra hle
        exact hnot k ⟨ih, (lt_of_not_ge hle).le⟩
    have h1 : (1 : I) ≤ t := P.t_last ▸ hlt (Fin.last n)
    have ht1 : t = 1 := le_antisymm t.2.2 h1
    cases n with
    | zero => exact IsEmpty.false P
    | succ m =>
      refine hnot (Fin.last m) ⟨hlt _, ?_⟩
      rw [ht1, Fin.succ_last, P.t_last]
  obtain ⟨k, hk⟩ := hcov
  exact mem_iUnion.mpr ⟨k, hmaps k hk⟩

/-! ### Global potentials and constant covectors -/

/-- If `g` is a `C¹` potential for `φ` on an open set `s` containing `γ`, then `g b - g a` is the
potential-subdivision integral of `φ` along `γ`. -/
theorem hasLocalPotentialIntegral_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hg : ContDiffOn ℝ 1 g s) (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialIntegral φ γ (g b - g a) := by
  obtain ⟨n, P, hcover⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (x : E) (r : ℝ), U = ball x r ∧ ball x r ⊆ s)
    (fun z ⟨t, ht⟩ ↦ by
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs z (ht ▸ hγ t)
      exact ⟨ball z r, isOpen_ball, mem_ball_self hr, z, r, rfl, hrs⟩)
  choose U _ hUP hmaps using hcover
  choose c r hUeq hrs using hUP
  refine ⟨n, P, c, r, fun _ ↦ g, fun k ↦ hUeq k ▸ hmaps k, fun k ↦ hg.mono (hrs k),
    fun k y hy ↦ hd y (hrs k hy), ?_⟩
  simpa using Fin.sum_univ_succ_sub_castSucc (fun k ↦ g (γ (P.t k)))

/-- If `φ` has local potentials on `s` and `g` has Fréchet derivative `φ` at every point of `s`,
then `localPotentialIntegral φ γ = g b - g a` along every continuous path `γ : Path a b` in `s`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_sub_of_hasFDerivAt
    (hφ : HasLocalPotentials s φ) {g : E → F} (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = g b - g a :=
  (hasLocalPotentialIntegral_of_hasFDerivAt hφ.isOpen (hφ.contDiffOn_of_hasFDerivAt hd) hd
    hγ).localPotentialIntegral_eq

/-- If `g` is a `C¹` potential for `φ` on an open set `s`, then the continuous path integral along
any path `γ : Path a b` in `s` equals `g b - g a`. -/
theorem localPotentialIntegral_eq_sub_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hg : ContDiffOn ℝ 1 g s) (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = g b - g a :=
  (hasLocalPotentialIntegral_of_hasFDerivAt hs hg hd hγ).localPotentialIntegral_eq

/-- A constant covector field `L` has potential-subdivision integral `L b - L a` along every
continuous path `γ : Path a b`, even when `γ` is nowhere differentiable. -/
theorem hasLocalPotentialIntegral_const (L : E →L[ℝ] F) (γ : Path a b) :
    HasLocalPotentialIntegral (fun _ ↦ L) γ (L b - L a) :=
  hasLocalPotentialIntegral_of_hasFDerivAt isOpen_univ L.contDiff.contDiffOn
    (fun _ _ ↦ L.hasFDerivAt) (fun _ ↦ mem_univ _)

/-- Integrating a constant covector field `L` along any continuous path `γ : Path a b` gives
`L b - L a`. -/
@[simp]
theorem localPotentialIntegral_const (L : E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (fun _ ↦ L) γ = L b - L a :=
  (hasLocalPotentialIntegral_const L γ).localPotentialIntegral_eq

/-! ### Algebraic operations and congruence -/

/-- The zero covector field has potential-subdivision integral `0` along every path. -/
theorem hasLocalPotentialIntegral_zero (γ : Path a b) :
    HasLocalPotentialIntegral (0 : E → E →L[ℝ] F) γ 0 := by
  rw [Pi.zero_def]
  simpa using hasLocalPotentialIntegral_const (0 : E →L[ℝ] F) γ

@[simp]
theorem localPotentialIntegral_zero (γ : Path a b) :
    localPotentialIntegral (0 : E → E →L[ℝ] F) γ = 0 :=
  (hasLocalPotentialIntegral_zero γ).localPotentialIntegral_eq

/-- Negating the covector field negates its potential-subdivision integral. -/
theorem HasLocalPotentialIntegral.neg {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) :
    HasLocalPotentialIntegral (-φ) γ (-v) := by
  obtain ⟨n, P, c, r, g, hmaps, hg, hd, rfl⟩ := h
  refine ⟨n, P, c, r, fun k ↦ -g k, hmaps, fun k ↦ (hg k).neg,
    fun k y hy ↦ (hd k y hy).neg, ?_⟩
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Pi.neg_apply]
  abel

@[simp]
theorem hasLocalPotentialIntegral_neg_iff {γ : Path a b} {v : F} :
    HasLocalPotentialIntegral (-φ) γ v ↔ HasLocalPotentialIntegral φ γ (-v) :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ by simpa using h.neg⟩

@[simp]
theorem localPotentialIntegral_neg (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (-φ) γ = -localPotentialIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialIntegral_eq, hv.neg.localPotentialIntegral_eq]
  · have h' : ¬ ∃ w, HasLocalPotentialIntegral (-φ) γ w := by
      rintro ⟨w, hw⟩
      exact h ⟨-w, by simpa using hw.neg⟩
    rw [localPotentialIntegral_of_not_exists h, localPotentialIntegral_of_not_exists h', neg_zero]

@[simp]
theorem localPotentialIntegral_fun_neg (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (fun x ↦ -φ x) γ = -localPotentialIntegral φ γ :=
  localPotentialIntegral_neg φ γ

/-- Scaling the covector field by a real constant scales its potential-subdivision integral. -/
theorem HasLocalPotentialIntegral.smul {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) (c : ℝ) :
    HasLocalPotentialIntegral (c • φ) γ (c • v) := by
  obtain ⟨n, P, pt, r, g, hmaps, hg, hd, rfl⟩ := h
  refine ⟨n, P, pt, r, fun k ↦ c • g k, hmaps, fun k ↦ (hg k).const_smul c,
    fun k y hy ↦ (hd k y hy).const_smul c, ?_⟩
  simp [Finset.smul_sum, smul_sub]

@[simp]
theorem localPotentialIntegral_smul (c : ℝ) (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (c • φ) γ = c • localPotentialIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases h : ∃ v, HasLocalPotentialIntegral φ γ v
    · obtain ⟨v, hv⟩ := h
      rw [hv.localPotentialIntegral_eq, (hv.smul c).localPotentialIntegral_eq]
    · have h' : ¬ ∃ w, HasLocalPotentialIntegral (c • φ) γ w := by
        rintro ⟨w, hw⟩
        exact h ⟨c⁻¹ • w, by simpa [smul_smul, inv_mul_cancel₀ hc] using hw.smul c⁻¹⟩
      rw [localPotentialIntegral_of_not_exists h, localPotentialIntegral_of_not_exists h',
        smul_zero]

@[simp]
theorem localPotentialIntegral_fun_smul (c : ℝ) (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (fun x ↦ c • φ x) γ = c • localPotentialIntegral φ γ :=
  localPotentialIntegral_smul c φ γ

/-- Adding two covector fields adds their potential-subdivision integrals along `γ`. -/
theorem HasLocalPotentialIntegral.add {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialIntegral φ₁ γ v₁) (h₂ : HasLocalPotentialIntegral φ₂ γ v₂) :
    HasLocalPotentialIntegral (φ₁ + φ₂) γ (v₁ + v₂) := by
  obtain ⟨s₁, hs₁, hγ₁⟩ :=
    exists_hasLocalPotentialIntegral_iff_exists_hasLocalPotentials.mp ⟨v₁, h₁⟩
  obtain ⟨s₂, hs₂, hγ₂⟩ :=
    exists_hasLocalPotentialIntegral_iff_exists_hasLocalPotentials.mp ⟨v₂, h₂⟩
  obtain ⟨n, P, hcover⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (x : E) (r : ℝ) (g₁ g₂ : E → F), U = ball x r ∧
      ContDiffOn ℝ 1 g₁ (ball x r) ∧ (∀ y ∈ ball x r, HasFDerivAt g₁ (φ₁ y) y) ∧
      ContDiffOn ℝ 1 g₂ (ball x r) ∧ (∀ y ∈ ball x r, HasFDerivAt g₂ (φ₂ y) y))
    (fun z ⟨t, ht⟩ ↦ by
      obtain ⟨r₁, hr₁, _, g₁, hg₁, hd₁⟩ := hasLocalPotentials_iff.mp hs₁ z (ht ▸ hγ₁ t)
      obtain ⟨r₂, hr₂, _, g₂, hg₂, hd₂⟩ := hasLocalPotentials_iff.mp hs₂ z (ht ▸ hγ₂ t)
      have hb₁ : ball z (min r₁ r₂) ⊆ ball z r₁ := ball_subset_ball (min_le_left _ _)
      have hb₂ : ball z (min r₁ r₂) ⊆ ball z r₂ := ball_subset_ball (min_le_right _ _)
      exact ⟨ball z (min r₁ r₂), isOpen_ball, mem_ball_self (lt_min hr₁ hr₂),
        z, min r₁ r₂, g₁, g₂, rfl, hg₁.mono hb₁, fun y hy ↦ hd₁ y (hb₁ hy),
        hg₂.mono hb₂, fun y hy ↦ hd₂ y (hb₂ hy)⟩)
  choose U _ hUP hmaps using hcover
  choose c r g₁ g₂ hUeq hg₁ hd₁ hg₂ hd₂ using hUP
  have hmaps' : ∀ k, MapsTo γ (Icc (P.t k.castSucc) (P.t k.succ)) (ball (c k) (r k)) :=
    fun k ↦ hUeq k ▸ hmaps k
  have hv₁ : ∑ k : Fin n, (g₁ k (γ (P.t k.succ)) - g₁ k (γ (P.t k.castSucc))) = v₁ :=
    HasLocalPotentialIntegral.unique ⟨n, P, c, r, g₁, hmaps', hg₁, hd₁, rfl⟩ h₁
  have hv₂ : ∑ k : Fin n, (g₂ k (γ (P.t k.succ)) - g₂ k (γ (P.t k.castSucc))) = v₂ :=
    HasLocalPotentialIntegral.unique ⟨n, P, c, r, g₂, hmaps', hg₂, hd₂, rfl⟩ h₂
  refine ⟨n, P, c, r, fun k ↦ g₁ k + g₂ k, hmaps', fun k ↦ (hg₁ k).add (hg₂ k),
    fun k y hy ↦ (hd₁ k y hy).add (hd₂ k y hy), ?_⟩
  calc
    ∑ k : Fin n, ((g₁ k + g₂ k) (γ (P.t k.succ)) - (g₁ k + g₂ k) (γ (P.t k.castSucc))) =
        (∑ k : Fin n, (g₁ k (γ (P.t k.succ)) - g₁ k (γ (P.t k.castSucc)))) +
        ∑ k : Fin n, (g₂ k (γ (P.t k.succ)) - g₂ k (γ (P.t k.castSucc))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [Pi.add_apply]
      abel
    _ = v₁ + v₂ := by rw [hv₁, hv₂]

/-- Additivity of `localPotentialIntegral` in the covector field. -/
theorem HasLocalPotentials.localPotentialIntegral_add (hφ₁ : HasLocalPotentials s φ₁)
    (hφ₂ : HasLocalPotentials s φ₂) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ₁ + φ₂) γ =
      localPotentialIntegral φ₁ γ + localPotentialIntegral φ₂ γ :=
  ((hφ₁.hasLocalPotentialIntegral hγ).add
    (hφ₂.hasLocalPotentialIntegral hγ)).localPotentialIntegral_eq

/-- Subtracting two covector fields subtracts their potential-subdivision integrals along `γ`. -/
theorem HasLocalPotentialIntegral.sub {γ : Path a b} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialIntegral φ₁ γ v₁) (h₂ : HasLocalPotentialIntegral φ₂ γ v₂) :
    HasLocalPotentialIntegral (φ₁ - φ₂) γ (v₁ - v₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Subtraction of locally potential covector fields subtracts their continuous path integrals. -/
theorem HasLocalPotentials.localPotentialIntegral_sub (hφ₁ : HasLocalPotentials s φ₁)
    (hφ₂ : HasLocalPotentials s φ₂) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ₁ - φ₂) γ =
      localPotentialIntegral φ₁ γ - localPotentialIntegral φ₂ γ :=
  ((hφ₁.hasLocalPotentialIntegral hγ).sub
    (hφ₂.hasLocalPotentialIntegral hγ)).localPotentialIntegral_eq

/-- Congruence of `HasLocalPotentialIntegral` for covector fields agreeing on an open set containing
the path. -/
theorem HasLocalPotentialIntegral.congr {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) (hs : IsOpen s) (heq : EqOn φ ψ s) (hγ : ∀ t, γ t ∈ s) :
    HasLocalPotentialIntegral ψ γ v := by
  obtain ⟨u, hu, hγu⟩ := exists_hasLocalPotentialIntegral_iff_exists_hasLocalPotentials.mp ⟨v, h⟩
  have hφ' : HasLocalPotentials (u ∩ s) φ := hu.mono (hu.isOpen.inter hs) inter_subset_left
  -- Both `φ` and `ψ` share the same local potentials on balls contained in `u ∩ s`.
  obtain ⟨n, P, hcover⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (x : E) (r : ℝ) (g : E → F), U = ball x r ∧ ball x r ⊆ u ∩ s ∧
      ContDiffOn ℝ 1 g (ball x r) ∧ ∀ y ∈ ball x r, HasFDerivAt g (φ y) y)
    (fun z ⟨t, ht⟩ ↦ by
      obtain ⟨r, hr, hrs, g, hg, hd⟩ := hasLocalPotentials_iff.mp hφ' z (ht ▸ ⟨hγu t, hγ t⟩)
      exact ⟨ball z r, isOpen_ball, mem_ball_self hr, z, r, g, rfl, hrs, hg, hd⟩)
  choose U _ hUP hmaps using hcover
  choose c r g hUeq hrs hg hd using hUP
  have hmaps' : ∀ k, MapsTo γ (Icc (P.t k.castSucc) (P.t k.succ)) (ball (c k) (r k)) :=
    fun k ↦ hUeq k ▸ hmaps k
  have hv : ∑ k : Fin n, (g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc))) = v :=
    HasLocalPotentialIntegral.unique ⟨n, P, c, r, g, hmaps', hg, hd, rfl⟩ h
  exact ⟨n, P, c, r, g, hmaps', hg, fun k y hy ↦ heq (hrs k hy).2 ▸ hd k y hy, hv⟩

/-- The continuous path integral depends only on the values of the covector field on any open set
containing the path. -/
theorem localPotentialIntegral_congr (hs : IsOpen s) (heq : EqOn φ ψ s) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = localPotentialIntegral ψ γ := by
  by_cases h : ∃ v, HasLocalPotentialIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialIntegral_eq, (hv.congr hs heq hγ).localPotentialIntegral_eq]
  · have h' : ¬ ∃ w, HasLocalPotentialIntegral ψ γ w := by
      rintro ⟨w, hw⟩
      exact h ⟨w, hw.congr hs heq.symm hγ⟩
    rw [localPotentialIntegral_of_not_exists h, localPotentialIntegral_of_not_exists h']

/-- Congruence of `localPotentialIntegral` on the domain of `HasLocalPotentials`. -/
theorem HasLocalPotentials.localPotentialIntegral_congr (hφ : HasLocalPotentials s φ)
    (heq : EqOn φ ψ s) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = localPotentialIntegral ψ γ :=
  TauCeti.localPotentialIntegral_congr hφ.isOpen heq hγ

/-! ### Path operations: constant path, endpoint casts, reversal, concatenation, and subpaths -/

/-- Any potential-subdivision sum along a constant path vanishes. -/
theorem HasLocalPotentialIntegral.refl_eq_zero {v : F}
    (h : HasLocalPotentialIntegral φ (.refl a) v) : v = 0 := by
  obtain ⟨n, P, c, r, g, -, -, -, rfl⟩ := h
  simp

/-- The continuous path integral along a constant path is `0`. -/
@[simp]
theorem localPotentialIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    localPotentialIntegral φ (.refl a) = 0 := by
  by_cases h : ∃ v, HasLocalPotentialIntegral φ (.refl a) v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialIntegral_eq, hv.refl_eq_zero]
  · exact localPotentialIntegral_of_not_exists h

/-- Casting the endpoints of a path preserves `HasLocalPotentialIntegral`. -/
theorem HasLocalPotentialIntegral.cast {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) (ha : a' = a) (hb : b' = b) :
    HasLocalPotentialIntegral φ (γ.cast ha hb) v := by
  subst ha hb
  exact h

@[simp]
theorem hasLocalPotentialIntegral_cast_iff {γ : Path a b} {v : F} (ha : a' = a) (hb : b' = b) :
    HasLocalPotentialIntegral φ (γ.cast ha hb) v ↔ HasLocalPotentialIntegral φ γ v := by
  subst ha hb
  exact Iff.rfl

/-- Casting path endpoints does not change `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_cast (φ : E → E →L[ℝ] F) (γ : Path a b) (ha : a' = a)
    (hb : b' = b) :
    localPotentialIntegral φ (γ.cast ha hb) = localPotentialIntegral φ γ := by
  subst ha hb
  rfl

/-- Reversing a path negates its potential-subdivision integral. -/
theorem HasLocalPotentialIntegral.symm {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) :
    HasLocalPotentialIntegral φ γ.symm (-v) := by
  obtain ⟨n, P, c, r, g, hmaps, hg, hd, rfl⟩ := h
  let P' : unitInterval.Partition n :=
    { t := fun k ↦ σ (P.t k.rev)
      mono := fun i j hij ↦ unitInterval.symm_le_symm.mpr (P.mono (Fin.rev_le_rev.mpr hij))
      t_zero := by simp
      t_last := by simp }
  have hrev_succ (k : Fin n) : k.succ.rev = k.rev.castSucc :=
    Fin.ext (by simp [Fin.rev])
  have hrev_cast (k : Fin n) : k.castSucc.rev = k.rev.succ :=
    Fin.ext (by simp [Fin.rev]; omega)
  refine ⟨n, P', fun k ↦ c k.rev, fun k ↦ r k.rev, fun k ↦ g k.rev, ?_, fun k ↦ hg k.rev,
    fun k ↦ hd k.rev, ?_⟩
  · intro k s hs
    rw [Path.symm_apply]
    apply hmaps k.rev
    refine ⟨?_, ?_⟩
    · have h2 : s ≤ σ (P.t k.succ.rev) := hs.2
      rw [hrev_succ] at h2
      exact unitInterval.le_symm_comm.mp h2
    · have h1 : σ (P.t k.castSucc.rev) ≤ s := hs.1
      rw [hrev_cast] at h1
      exact unitInterval.symm_le_comm.mp h1
  · have hterm (k : Fin n) :
        g k.rev (γ.symm (P'.t k.succ)) - g k.rev (γ.symm (P'.t k.castSucc)) =
          -(g k.rev (γ (P.t k.rev.succ)) - g k.rev (γ (P.t k.rev.castSucc))) := by
      simp only [P', Path.symm_apply, Function.comp_apply, unitInterval.symm_symm, hrev_succ,
        hrev_cast, neg_sub]
    simp_rw [hterm, Finset.sum_neg_distrib]
    congr 1
    exact Equiv.sum_comp Fin.revPerm
      (fun k : Fin n ↦ g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc)))

@[simp]
theorem hasLocalPotentialIntegral_symm_iff {γ : Path a b} {v : F} :
    HasLocalPotentialIntegral φ γ.symm v ↔ HasLocalPotentialIntegral φ γ (-v) :=
  ⟨fun h ↦ by simpa using h.symm, fun h ↦ by simpa using h.symm⟩

/-- Reversing a path negates its continuous path integral. -/
@[simp]
theorem localPotentialIntegral_symm (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral φ γ.symm = -localPotentialIntegral φ γ := by
  by_cases h : ∃ v, HasLocalPotentialIntegral φ γ v
  · obtain ⟨v, hv⟩ := h
    rw [hv.localPotentialIntegral_eq, hv.symm.localPotentialIntegral_eq]
  · have h' : ¬ ∃ w, HasLocalPotentialIntegral φ γ.symm w := by
      rintro ⟨w, hw⟩
      exact h ⟨-w, by simpa using hw.symm⟩
    rw [localPotentialIntegral_of_not_exists h, localPotentialIntegral_of_not_exists h', neg_zero]

/-- Concatenating two paths adds their potential-subdivision integrals. -/
theorem HasLocalPotentialIntegral.trans {γ₁ : Path a b} {γ₂ : Path b c} {v₁ v₂ : F}
    (h₁ : HasLocalPotentialIntegral φ γ₁ v₁) (h₂ : HasLocalPotentialIntegral φ γ₂ v₂) :
    HasLocalPotentialIntegral φ (γ₁.trans γ₂) (v₁ + v₂) := by
  obtain ⟨n₁, P₁, c₁, r₁, g₁, hmaps₁, hg₁, hd₁, rfl⟩ := h₁
  obtain ⟨n₂, P₂, c₂, r₂, g₂, hmaps₂, hg₂, hd₂, rfl⟩ := h₂
  -- Rescale `P₁` onto `[0, 1 / 2]` and `P₂` onto `[1 / 2, 1]`.
  let halfL (u : I) : I := ⟨(u : ℝ) / 2, ⟨by linarith [u.2.1], by linarith [u.2.2]⟩⟩
  let halfR (u : I) : I := ⟨(1 + (u : ℝ)) / 2, ⟨by linarith [u.2.1], by linarith [u.2.2]⟩⟩
  let tFun : Fin (n₁ + n₂ + 1) → I := fun k ↦
    if hk : k.1 ≤ n₁ then halfL (P₁.t ⟨k.1, Nat.lt_succ_of_le hk⟩)
    else halfR (P₂.t ⟨k.1 - n₁, by omega⟩)
  have htL (k : Fin (n₁ + 1)) : tFun ⟨k.1, by omega⟩ = halfL (P₁.t k) := by
    simp [tFun, Nat.le_of_lt_succ k.2]
  have htR (k : Fin (n₂ + 1)) : tFun ⟨n₁ + k.1, by omega⟩ = halfR (P₂.t k) := by
    rcases eq_or_ne k.1 0 with hk0 | hk0
    · have hk : k = 0 := Fin.ext hk0
      subst hk
      have hlast₁ : (⟨n₁, Nat.lt_succ_self n₁⟩ : Fin (n₁ + 1)) = Fin.last n₁ := rfl
      apply Subtype.ext
      simp [tFun, halfL, halfR, hlast₁]
    · have hnot : ¬ n₁ + k.1 ≤ n₁ := by omega
      simp [tFun, hnot]
  let P : unitInterval.Partition (n₁ + n₂) :=
    { t := tFun
      mono := by
        intro i j hij
        rw [← Subtype.coe_le_coe]
        by_cases hi : i.1 ≤ n₁ <;> by_cases hj : j.1 ≤ n₁
        · have hle : P₁.t ⟨i.1, Nat.lt_succ_of_le hi⟩ ≤ P₁.t ⟨j.1, Nat.lt_succ_of_le hj⟩ :=
            P₁.mono hij
          simp only [tFun, hi, hj, ↓reduceDIte, halfL]
          linarith [Subtype.coe_le_coe.mpr hle]
        · have h1 := (P₁.t ⟨i.1, Nat.lt_succ_of_le hi⟩).2.2
          have h2 := (P₂.t ⟨j.1 - n₁, by omega⟩).2.1
          simp only [tFun, hi, hj, ↓reduceDIte, halfL, halfR]
          linarith
        · omega
        · have hle : P₂.t ⟨i.1 - n₁, by omega⟩ ≤ P₂.t ⟨j.1 - n₁, by omega⟩ :=
            P₂.mono (by simp only [Fin.le_def]; omega)
          simp only [tFun, hi, hj, ↓reduceDIte, halfR]
          linarith [Subtype.coe_le_coe.mpr hle]
      t_zero := by
        apply Subtype.ext
        simp [tFun, halfL]
      t_last := by
        have hlast₂ : Fin.last (n₁ + n₂) = ⟨n₁ + (Fin.last n₂).1, by simp⟩ := rfl
        rw [hlast₂, htR (Fin.last n₂)]
        apply Subtype.ext
        simp [halfR] }
  let c' : Fin (n₁ + n₂) → E := Fin.addCases c₁ c₂
  let r' : Fin (n₁ + n₂) → ℝ := Fin.addCases r₁ r₂
  let g' : Fin (n₁ + n₂) → E → F := Fin.addCases g₁ g₂
  have hcastL (i : Fin n₁) :
      P.t (Fin.castAdd n₂ i).castSucc = halfL (P₁.t i.castSucc) ∧
        P.t (Fin.castAdd n₂ i).succ = halfL (P₁.t i.succ) :=
    ⟨htL i.castSucc, htL i.succ⟩
  have hcastR (j : Fin n₂) :
      P.t (Fin.natAdd n₁ j).castSucc = halfR (P₂.t j.castSucc) ∧
        P.t (Fin.natAdd n₁ j).succ = halfR (P₂.t j.succ) :=
    ⟨htR j.castSucc, htR j.succ⟩
  refine ⟨n₁ + n₂, P, c', r', g', ?_, ?_, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun i s hs ↦ ?_) (fun j s hs ↦ ?_) k
    · rw [(hcastL i).1, (hcastL i).2] at hs
      have hs1 : (P₁.t i.castSucc : ℝ) ≤ 2 * (s : ℝ) := by
        have := Subtype.coe_le_coe.mpr hs.1; dsimp [halfL] at this; linarith
      have hs2 : 2 * (s : ℝ) ≤ (P₁.t i.succ : ℝ) := by
        have := Subtype.coe_le_coe.mpr hs.2; dsimp [halfL] at this; linarith
      let v : I := ⟨2 * (s : ℝ), ⟨le_trans (P₁.t i.castSucc).2.1 hs1,
        le_trans hs2 (P₁.t i.succ).2.2⟩⟩
      rw [(γ₁.trans_apply_of_eq_two_mul γ₂ v rfl)]
      simpa [c', r'] using hmaps₁ i (show v ∈ Icc (P₁.t i.castSucc) (P₁.t i.succ) from ⟨hs1, hs2⟩)
    · rw [(hcastR j).1, (hcastR j).2] at hs
      have hs1 : (P₂.t j.castSucc : ℝ) ≤ 2 * (s : ℝ) - 1 := by
        have := Subtype.coe_le_coe.mpr hs.1; dsimp [halfR] at this; linarith
      have hs2 : 2 * (s : ℝ) - 1 ≤ (P₂.t j.succ : ℝ) := by
        have := Subtype.coe_le_coe.mpr hs.2; dsimp [halfR] at this; linarith
      let v : I := ⟨2 * (s : ℝ) - 1, ⟨le_trans (P₂.t j.castSucc).2.1 hs1,
        le_trans hs2 (P₂.t j.succ).2.2⟩⟩
      rw [(γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ v rfl)]
      simpa [c', r'] using hmaps₂ j (show v ∈ Icc (P₂.t j.castSucc) (P₂.t j.succ) from ⟨hs1, hs2⟩)
  · intro k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa only [c', r', g', Fin.addCases_left] using hg₁ i
    · simpa only [c', r', g', Fin.addCases_right] using hg₂ j
  · intro k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa only [c', r', g', Fin.addCases_left] using hd₁ i
    · simpa only [c', r', g', Fin.addCases_right] using hd₂ j
  · rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [(hcastL i).1, (hcastL i).2]
      have he1 : (γ₁.trans γ₂) (halfL (P₁.t i.succ)) = γ₁ (P₁.t i.succ) :=
        γ₁.trans_apply_of_eq_two_mul γ₂ (P₁.t i.succ) (by dsimp [halfL]; ring)
      have he0 : (γ₁.trans γ₂) (halfL (P₁.t i.castSucc)) = γ₁ (P₁.t i.castSucc) :=
        γ₁.trans_apply_of_eq_two_mul γ₂ (P₁.t i.castSucc) (by dsimp [halfL]; ring)
      simp [g', he1, he0]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [(hcastR j).1, (hcastR j).2]
      have he1 : (γ₁.trans γ₂) (halfR (P₂.t j.succ)) = γ₂ (P₂.t j.succ) :=
        γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ (P₂.t j.succ) (by dsimp [halfR]; ring)
      have he0 : (γ₁.trans γ₂) (halfR (P₂.t j.castSucc)) = γ₂ (P₂.t j.castSucc) :=
        γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ (P₂.t j.castSucc) (by dsimp [halfR]; ring)
      simp [g', he1, he0]

/-- Concatenating two paths in `s` adds their continuous path integrals. -/
theorem HasLocalPotentials.localPotentialIntegral_trans (hφ : HasLocalPotentials s φ)
    {γ₁ : Path a b} {γ₂ : Path b c} (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ (γ₁.trans γ₂) =
      localPotentialIntegral φ γ₁ + localPotentialIntegral φ γ₂ :=
  ((hφ.hasLocalPotentialIntegral hγ₁).trans
    (hφ.hasLocalPotentialIntegral hγ₂)).localPotentialIntegral_eq

/-! ### Naturality under `C¹` maps -/

/-- **Naturality of the continuous path integral under `C¹` maps.** Pulling a locally potential
covector field `φ` back along a `C¹` map `f : G → E` (`MapsTo f u s`, `IsOpen u`) and integrating
along `γ` in `u` gives the integral of `φ` along the image path `γ.map' _`. -/
theorem HasLocalPotentials.localPotentialIntegral_pullback {u : Set G} {f : G → E}
    (hφ : HasLocalPotentials s φ) (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u)
    (hfs : MapsTo f u s) {x₀ x₁ : G} {γ : Path x₀ x₁} (hγ : ∀ t, γ t ∈ u) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) := by
  -- Pull local potential balls back along `f` and compose each local potential with `f`.
  let γf := γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))
  obtain ⟨n, P, hcover⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (x : G) (q : ℝ) (y : E) (r : ℝ) (g : E → F),
      U = ball x q ∧ ball x q ⊆ u ∧ MapsTo f (ball x q) (ball y r) ∧
      ContDiffOn ℝ 1 g (ball y r) ∧ ∀ w ∈ ball y r, HasFDerivAt g (φ w) w)
    (fun z ⟨t, ht⟩ ↦ by
      have hzu : z ∈ u := ht ▸ hγ t
      obtain ⟨r, hr, _, g, hg, hd⟩ := hasLocalPotentials_iff.mp hφ (f z) (hfs hzu)
      have hn : f ⁻¹' ball (f z) r ∩ u ∈ 𝓝 z :=
        inter_mem ((hf.continuousOn.continuousAt (hu.mem_nhds hzu)).preimage_mem_nhds
          (ball_mem_nhds _ hr)) (hu.mem_nhds hzu)
      obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hn
      exact ⟨ball z q, isOpen_ball, mem_ball_self hq, z, q, f z, r, g, rfl,
        fun w hw ↦ (hqsub hw).2, fun w hw ↦ (hqsub hw).1, hg, hd⟩)
  choose U _ hUP hmaps using hcover
  choose cG q cE r g hUeq hqu hqb hg hd using hUP
  have hmapsG : ∀ k, MapsTo γ (Icc (P.t k.castSucc) (P.t k.succ)) (ball (cG k) (q k)) :=
    fun k ↦ hUeq k ▸ hmaps k
  have hmapsE : ∀ k, MapsTo γf (Icc (P.t k.castSucc) (P.t k.succ)) (ball (cE k) (r k)) :=
    fun k t ht ↦ hqb k (hmapsG k ht)
  have hpull : HasLocalPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ
      (∑ k : Fin n, (g k (f (γ (P.t k.succ))) - g k (f (γ (P.t k.castSucc))))) := by
    refine ⟨n, P, cG, q, fun k ↦ g k ∘ f, hmapsG,
      fun k ↦ (hg k).comp (hf.mono (hqu k)) (hqb k), fun k w hw ↦ ?_, rfl⟩
    exact (hd k (f w) (hqb k hw)).comp w
      (((hf.differentiableOn one_ne_zero w (hqu k hw)).differentiableAt
        (hu.mem_nhds (hqu k hw)))).hasFDerivAt
  have himg : HasLocalPotentialIntegral φ γf
      (∑ k : Fin n, (g k (f (γ (P.t k.succ))) - g k (f (γ (P.t k.castSucc))))) :=
    ⟨n, P, cE, r, g, hmapsE, hg, hd, rfl⟩
  rw [hpull.localPotentialIntegral_eq, himg.localPotentialIntegral_eq]

/-- Global-`C¹` specialization of `HasLocalPotentials.localPotentialIntegral_pullback` using
`Path.map`. -/
theorem HasLocalPotentials.localPotentialIntegral_pullback_map {f : G → E}
    (hφ : HasLocalPotentials s φ) (hf : ContDiff ℝ 1 f) {x₀ x₁ : G} {γ : Path x₀ x₁}
    (hγ : ∀ t, f (γ t) ∈ s) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ (γ.map hf.continuous) := by
  have hu : IsOpen (f ⁻¹' s) := hφ.isOpen.preimage hf.continuous
  have hfs : MapsTo f (f ⁻¹' s) s := fun _ hx ↦ hx
  have hγ' : ∀ t, γ t ∈ f ⁻¹' s := hγ
  have hmap : γ.map' (hf.contDiffOn.continuousOn.mono (range_subset_iff.mpr hγ')) =
      γ.map hf.continuous := by ext t; rfl
  rw [← hmap]
  exact hφ.localPotentialIntegral_pullback hu hf.contDiffOn hfs hγ'

/-! ### Homotopy invariance and subpath additivity -/

/-- **Homotopy invariance of the continuous path integral.** If `H` is a path homotopy relative to
the endpoints from `γ₀` to `γ₁` whose image stays inside `s`, then
`localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_homotopy (hφ : HasLocalPotentials s φ)
    {γ₀ γ₁ : Path a b} (H : γ₀.Homotopy γ₁) (hH : ∀ t u, H (t, u) ∈ s) :
    localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁ := by
  -- Subdivide `I × I` into grid rectangles mapped into potential balls; across each row of
  -- rectangles the vertical potential increments telescope to zero.
  choose r hr hrest using fun z : s ↦ hasLocalPotentials_iff.mp hφ z.1 z.2
  choose _ g hg hd using hrest
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (c := fun z : s ↦ H ⁻¹' ball z.1 (r z))
      (fun z ↦ isOpen_ball.preimage H.continuous)
      (fun p _ ↦ mem_iUnion.mpr ⟨⟨H p, hH p.1 p.2⟩, mem_ball_self (hr _)⟩)
  let M := max N 1
  have hM_pos : 0 < M := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  have htM : t M = 1 := hN M (le_max_left N 1)
  let P : unitInterval.Partition M :=
    { t := fun k ↦ t k.1
      mono := fun i j hij ↦ ht_mono hij
      t_zero := ht0
      t_last := htM }
  choose idx hidx using hcell
  -- Compare consecutive horizontal slice paths `H.eval (t n)` and `H.eval (t (n + 1))`.
  have hstep (n : ℕ) :
      localPotentialIntegral φ (H.eval (t n)) =
        localPotentialIntegral φ (H.eval (t (n + 1))) := by
    let zn (m : Fin M) : s := idx n m.1
    let cn (m : Fin M) : E := (zn m).1
    let rn (m : Fin M) : ℝ := r (zn m)
    let gn (m : Fin M) : E → F := g (zn m)
    have hmem_cell (m : Fin M) {u : I} (hu : u ∈ Icc (P.t m.castSucc) (P.t m.succ)) :
        H (t n, u) ∈ ball (cn m) (rn m) ∧ H (t (n + 1), u) ∈ ball (cn m) (rn m) :=
      ⟨hidx n m.1 ⟨⟨le_rfl, ht_mono (Nat.le_succ n)⟩, hu⟩,
        hidx n m.1 ⟨⟨ht_mono (Nat.le_succ n), le_rfl⟩, hu⟩⟩
    have hint₀ : HasLocalPotentialIntegral φ (H.eval (t n))
        (∑ m : Fin M, (gn m (H (t n, P.t m.succ)) - gn m (H (t n, P.t m.castSucc)))) :=
      ⟨M, P, cn, rn, gn, fun m u hu ↦ (hmem_cell m hu).1, fun m ↦ hg (zn m),
        fun m ↦ hd (zn m), rfl⟩
    have hint₁ : HasLocalPotentialIntegral φ (H.eval (t (n + 1)))
        (∑ m : Fin M,
          (gn m (H (t (n + 1), P.t m.succ)) - gn m (H (t (n + 1), P.t m.castSucc)))) :=
      ⟨M, P, cn, rn, gn, fun m u hu ↦ (hmem_cell m hu).2, fun m ↦ hg (zn m),
        fun m ↦ hd (zn m), rfl⟩
    rw [eq_comm, hint₁.localPotentialIntegral_eq, hint₀.localPotentialIntegral_eq, ← sub_eq_zero,
      ← Finset.sum_sub_distrib]
    -- Define the vertical potential increment at each grid column `j : Fin (M + 1)`.
    let Δ : Fin (M + 1) → F := fun j ↦
      if hj : j.1 < M then
        gn ⟨j.1, hj⟩ (H (t (n + 1), P.t j)) - gn ⟨j.1, hj⟩ (H (t n, P.t j))
      else 0
    have hΔ0 : Δ 0 = 0 := by
      simp only [Δ, Fin.val_zero, hM_pos, ↓reduceDIte, P.t_zero]
      have hL₀ : H (t n, 0) = a := (H.eval (t n)).source
      have hL₁ : H (t (n + 1), 0) = a := (H.eval (t (n + 1))).source
      rw [hL₀, hL₁, sub_self]
    have hΔlast : Δ (Fin.last M) = 0 := by
      simp [Δ]
    have hedge (m : Fin M) :
        (gn m (H (t (n + 1), P.t m.succ)) - gn m (H (t (n + 1), P.t m.castSucc))) -
          (gn m (H (t n, P.t m.succ)) - gn m (H (t n, P.t m.castSucc))) =
          Δ m.succ - Δ m.castSucc := by
      have hleft : Δ m.castSucc =
          gn m (H (t (n + 1), P.t m.castSucc)) - gn m (H (t n, P.t m.castSucc)) := by
        simp [Δ, m.2]
      have hright :
          gn m (H (t (n + 1), P.t m.succ)) - gn m (H (t n, P.t m.succ)) = Δ m.succ := by
        by_cases hm : m.1 + 1 < M
        · simp only [Δ, Fin.val_succ, hm, ↓reduceDIte]
          let m' : Fin M := ⟨m.1 + 1, hm⟩
          have hpm : P.t m.succ ∈ Icc (P.t m.castSucc) (P.t m.succ) :=
            ⟨P.t_castSucc_le_succ m, le_rfl⟩
          have hpm' : P.t m.succ ∈ Icc (P.t m'.castSucc) (P.t m'.succ) :=
            ⟨le_rfl, P.t_castSucc_le_succ m'⟩
          exact sub_eq_sub_of_hasFDerivAt_of_isPreconnected (isOpen_ball.inter isOpen_ball)
            ((convex_ball (cn m) (rn m)).inter (convex_ball (cn m') (rn m'))).isPreconnected
            (fun y hy ↦ hd (zn m) y hy.1) (fun y hy ↦ hd (zn m') y hy.2)
            ⟨(hmem_cell m hpm).1, (hmem_cell m' hpm').1⟩
            ⟨(hmem_cell m hpm).2, (hmem_cell m' hpm').2⟩
        · have hlast : m.succ = Fin.last M := Fin.ext (by simp; omega)
          rw [hlast, hΔlast, P.t_last]
          have hR₀ : H (t n, 1) = b := (H.eval (t n)).target
          have hR₁ : H (t (n + 1), 1) = b := (H.eval (t (n + 1))).target
          rw [hR₀, hR₁, sub_self]
      rw [hleft, ← hright]
      abel
    simp_rw [hedge]
    rw [Fin.sum_univ_succ_sub_castSucc Δ, hΔlast, hΔ0, sub_self]
  have hind : ∀ k : ℕ, localPotentialIntegral φ (H.eval (t 0)) =
      localPotentialIntegral φ (H.eval (t k)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact ih.trans (hstep k)
  have heval := hind M
  rwa [ht0, htM, H.eval_zero, H.eval_one] at heval

/-- A loop homotopic relative to its basepoint inside `s` to the constant loop has vanishing
continuous path integral. -/
theorem HasLocalPotentials.localPotentialIntegral_loop_eq_zero_of_homotopy_refl
    (hφ : HasLocalPotentials s φ) {ℓ : Path a a} (H : ℓ.Homotopy (.refl a))
    (hH : ∀ t u, H (t, u) ∈ s) :
    localPotentialIntegral φ ℓ = 0 := by
  rw [hφ.localPotentialIntegral_eq_of_homotopy H hH, localPotentialIntegral_refl]

/-- Reparametrizing a path in `s` does not change its continuous path integral. -/
theorem HasLocalPotentials.localPotentialIntegral_reparam (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) :
    localPotentialIntegral φ (γ.reparam f hf hf₀ hf₁) = localPotentialIntegral φ γ := by
  symm
  exact hφ.localPotentialIntegral_eq_of_homotopy (Path.Homotopy.reparam γ f hf hf₀ hf₁)
    (fun _ _ ↦ hγ _)

/-- Additivity of `localPotentialIntegral` over adjacent subpaths `γ.subpath t₀ t₁` and
`γ.subpath t₁ t₂`, for arbitrary parameters `t₀, t₁, t₂ ∈ I`. -/
theorem HasLocalPotentials.localPotentialIntegral_subpath_trans (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) (t₀ t₁ t₂ : I) :
    localPotentialIntegral φ (γ.subpath t₀ t₂) =
      localPotentialIntegral φ (γ.subpath t₀ t₁) + localPotentialIntegral φ (γ.subpath t₁ t₂) := by
  let γs : Path (⟨a, γ.source ▸ hγ 0⟩ : s) ⟨b, γ.target ▸ hγ 1⟩ := γ.codRestrict hγ
  let Hsub := Path.Homotopy.subpathTransSubpath γs t₀ t₁ t₂
  let incl : C(s, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcoe (u : I) : incl (γs u) = γ u := by simp [γs, incl]
  have hhom := hφ.localPotentialIntegral_eq_of_homotopy (Hsub.map incl)
    (fun t u ↦ (Hsub (t, u)).2)
  have h₀ : ((γs.subpath t₀ t₁).trans (γs.subpath t₁ t₂)).map incl.continuous =
      ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)).cast (hcoe t₀) (hcoe t₂) := by
    ext u
    simp [γs, incl, Path.trans_apply]
  have h₁ : (γs.subpath t₀ t₂).map incl.continuous =
      (γ.subpath t₀ t₂).cast (hcoe t₀) (hcoe t₂) := by
    ext u
    simp [γs, incl]
  rw [h₀, h₁, localPotentialIntegral_cast, localPotentialIntegral_cast] at hhom
  rw [← hhom]
  exact hφ.localPotentialIntegral_trans (γ₁ := γ.subpath t₀ t₁) (γ₂ := γ.subpath t₁ t₂)
    (fun u ↦ by simp [Path.subpath, hγ]) (fun u ↦ by simp [Path.subpath, hγ])

/-- Subdividing `γ : Path a b` along any sequence `t : Fin (n + 1) → I` expresses the continuous
path integral on `γ.subpath (t 0) (t (Fin.last n))` as the sum over consecutive subpaths. -/
theorem HasLocalPotentials.localPotentialIntegral_subpath_eq_sum (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) {n : ℕ} (t : Fin (n + 1) → I) :
    localPotentialIntegral φ (γ.subpath (t 0) (t (Fin.last n))) =
      ∑ k : Fin n, localPotentialIntegral φ (γ.subpath (t k.castSucc) (t k.succ)) := by
  induction n with
  | zero =>
    simp
  | succ m ih =>
    have ih' := ih (fun k ↦ t k.castSucc)
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at ih'
    rw [Fin.sum_univ_castSucc, ← ih', Fin.succ_last]
    exact hφ.localPotentialIntegral_subpath_trans hγ (t 0) (t (Fin.last m).castSucc)
      (t (Fin.last (m + 1)))

/-- Subdividing `γ : Path a b` along any partition `P : unitInterval.Partition n` expresses
`localPotentialIntegral φ γ` as the sum of the integrals along the consecutive subpaths. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_sum_subpath (hφ : HasLocalPotentials s φ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) {n : ℕ} (P : unitInterval.Partition n) :
    localPotentialIntegral φ γ =
      ∑ k : Fin n, localPotentialIntegral φ (γ.subpath (P.t k.castSucc) (P.t k.succ)) := by
  have h := hφ.localPotentialIntegral_subpath_eq_sum hγ P.t
  rwa [P.t_zero, P.t_last, Path.subpath_zero_one, localPotentialIntegral_cast] at h

/-! ### Comparison with the Bochner `curveIntegral` -/

/-- When `F` is complete and `γ` is `C¹` on `[0, 1]`, any potential-subdivision integral of `φ`
along `γ` agrees with Mathlib's Bochner `curveIntegral φ γ`. -/
theorem HasLocalPotentialIntegral.eq_curveIntegral [CompleteSpace F] {γ : Path a b} {v : F}
    (h : HasLocalPotentialIntegral φ γ v) (hγ_diff : ContDiffOn ℝ 1 γ.extend I) :
    v = ∫ᶜ x in γ, φ x := by
  obtain ⟨u, hu, hγu⟩ := exists_hasLocalPotentialIntegral_iff_exists_hasLocalPotentials.mp ⟨v, h⟩
  obtain ⟨n, P, c, r, g, hmaps, hg, hd, rfl⟩ := h
  have hint_all : IntervalIntegrable (fun t ↦ φ (γ.extend t) (deriv γ.extend t)) volume 0 1 :=
    (curveIntegrable_iff_intervalIntegrable_deriv φ γ).mp
      (hu.continuousOn.curveIntegrable_of_contDiffOn hγ_diff hγu)
  have hmem_uIcc (x : I) : (x : ℝ) ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le zero_le_one]
    exact x.2
  rw [curveIntegral_eq_intervalIntegral_deriv]
  have hseg (k : Fin n) :
      g k (γ (P.t k.succ)) - g k (γ (P.t k.castSucc)) =
        ∫ t in (P.t k.castSucc : ℝ)..(P.t k.succ : ℝ), φ (γ.extend t) (deriv γ.extend t) := by
    have hle : (P.t k.castSucc : ℝ) ≤ (P.t k.succ : ℝ) := P.t_castSucc_le_succ k
    have hsub : Icc (P.t k.castSucc : ℝ) (P.t k.succ : ℝ) ⊆ I :=
      fun t ht ↦ ⟨le_trans (P.t k.castSucc).2.1 ht.1, le_trans ht.2 (P.t k.succ).2.2⟩
    have hmem_ball (t : ℝ) (ht : t ∈ Icc (P.t k.castSucc : ℝ) (P.t k.succ : ℝ)) :
        γ.extend t ∈ ball (c k) (r k) := by
      rw [γ.extend_apply (hsub ht)]
      exact hmaps k ht
    have hcont : ContinuousOn (g k ∘ γ.extend) (Icc (P.t k.castSucc : ℝ) (P.t k.succ : ℝ)) :=
      (hg k).continuousOn.comp (γ.continuous_extend.continuousOn) hmem_ball
    have hderiv (t : ℝ) (ht : t ∈ Ioo (P.t k.castSucc : ℝ) (P.t k.succ : ℝ)) :
        HasDerivAt (g k ∘ γ.extend) (φ (γ.extend t) (deriv γ.extend t)) t := by
      have htIoo : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt (P.t k.castSucc).2.1 ht.1, lt_of_lt_of_le ht.2 (P.t k.succ).2.2⟩
      have hγt : HasDerivAt γ.extend (deriv γ.extend t) t :=
        ((hγ_diff.differentiableOn one_ne_zero t (Ioo_subset_Icc_self htIoo)).differentiableAt
          (Icc_mem_nhds htIoo.1 htIoo.2)).hasDerivAt
      exact (hd k (γ.extend t) (hmem_ball t (Ioo_subset_Icc_self ht))).comp_hasDerivAt t hγt
    have hint_k : IntervalIntegrable (fun t ↦ φ (γ.extend t) (deriv γ.extend t)) volume
        (P.t k.castSucc : ℝ) (P.t k.succ : ℝ) :=
      hint_all.mono_set (uIcc_subset_uIcc (hmem_uIcc _) (hmem_uIcc _))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint_k]
    simp [Function.comp_apply, γ.extend_apply (P.t k.succ).2, γ.extend_apply (P.t k.castSucc).2]
  simp_rw [hseg]
  -- Concatenate the adjacent interval integrals across `P`.
  let a : ℕ → ℝ := fun k ↦ if hk : k < n + 1 then (P.t ⟨k, hk⟩ : ℝ) else 1
  have ha (k : Fin (n + 1)) : a k.1 = (P.t k : ℝ) := by simp [a]; omega
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t ↦ φ (γ.extend t) (deriv γ.extend t)) (μ := volume) (a := a) (n := n)
    fun k hk ↦ by
      let i : Fin n := ⟨k, hk⟩
      have h1 : a k = (P.t i.castSucc : ℝ) := ha i.castSucc
      have h2 : a (k + 1) = (P.t i.succ : ℝ) := ha i.succ
      rw [h1, h2]
      exact hint_all.mono_set (uIcc_subset_uIcc (hmem_uIcc _) (hmem_uIcc _))
  rw [← Fin.sum_univ_eq_sum_range, show a 0 = 0 by simpa [P.t_zero] using ha 0,
    show a n = 1 by simpa [P.t_last] using ha (Fin.last n)] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [← ha k.castSucc, ← ha k.succ, Fin.val_castSucc, Fin.val_succ]

/-- For a `C¹` path `γ` inside `s` and a complete target space `F`, the continuous path integral
`localPotentialIntegral φ γ` equals Mathlib's `curveIntegral φ γ`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_curveIntegral [CompleteSpace F]
    (hφ : HasLocalPotentials s φ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s)
    (hγ_diff : ContDiffOn ℝ 1 γ.extend I) :
    localPotentialIntegral φ γ = ∫ᶜ x in γ, φ x :=
  (hφ.hasLocalPotentialIntegral hγ).eq_curveIntegral hγ_diff

/-! ### Global potentials from vanishing loop integrals -/

/-- If every loop at `a` in `s` has vanishing continuous path integral, then any two paths from `a`
to `b` in `s` have the same continuous path integral. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ ℓ : Path a a, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0)
    {γ₁ γ₂ : Path a b} (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ γ₁ = localPotentialIntegral φ γ₂ := by
  have h0 : localPotentialIntegral φ (γ₁.trans γ₂.symm) = 0 :=
    hloop (γ₁.trans γ₂.symm) fun t ↦ by
      rw [Path.trans_apply]
      split_ifs <;> [exact hγ₁ _; exact hγ₂ _]
  rw [hφ.localPotentialIntegral_trans hγ₁ (fun t ↦ hγ₂ _), localPotentialIntegral_symm,
    ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0

/-- **Constructing a global `C¹` potential by integrating from a basepoint.** On a path-connected
domain `s` carrying local potentials for `φ`, if every loop at `x₀ ∈ s` has vanishing continuous
path integral, then integrating `φ` along paths in `s` from `x₀` yields an ambient function
`g : E → F`, `C¹` on `s`, vanishing at `x₀`, with derivative `φ x` at every `x ∈ s` and value
`localPotentialIntegral φ η` along every path `η : Path x₀ x` in `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_localPotentialIntegral_loop_eq_zero
    (hφ : HasLocalPotentials s φ) {x₀ : E} (hx₀ : x₀ ∈ s) (hs : IsPathConnected s)
    (hloop : ∀ ℓ : Path x₀ x₀, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0) :
    ∃ g : E → F, g x₀ = 0 ∧ ContDiffOn ℝ 1 g s ∧ (∀ x ∈ s, HasFDerivAt g (φ x) x) ∧
      ∀ x ∈ s, ∀ (η : Path x₀ x), (∀ t, η t ∈ s) → g x = localPotentialIntegral φ η := by
  classical
  have hjoin : ∀ x ∈ s, ∃ γ : Path x₀ x, ∀ t, γ t ∈ s := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hs.joinedIn x₀ hx₀ x hx
    exact ⟨γ, hγ⟩
  choose γ hγ using hjoin
  let g : E → F := fun x ↦ if hx : x ∈ s then localPotentialIntegral φ (γ x hx) else 0
  have hg_eq : ∀ x ∈ s, ∀ (η : Path x₀ x), (∀ t, η t ∈ s) →
      g x = localPotentialIntegral φ η := by
    intro x hx η hη
    simp only [g, hx, ↓reduceDIte]
    exact hφ.localPotentialIntegral_eq_of_forall_loop_eq_zero hloop (hγ x hx) hη
  have hgx₀ : g x₀ = 0 := by
    rw [hg_eq x₀ hx₀ (.refl x₀) (fun _ ↦ hx₀), localPotentialIntegral_refl]
  have hderiv : ∀ x ∈ s, HasFDerivAt g (φ x) x := by
    intro x hx
    obtain ⟨r, hr, hrs, g₀, hg₀, hd₀⟩ := hasLocalPotentials_iff.mp hφ x hx
    -- For `y ∈ ball x r`, reach `y` by following `γ x hx` and then `Path.segment x y`.
    have heq : g =ᶠ[𝓝 x] fun y ↦ g₀ y + (g x - g₀ x) := by
      filter_upwards [ball_mem_nhds x hr] with y hy
      have hseg_ball : ∀ t, Path.segment x y t ∈ ball x r := fun t ↦
        (convex_ball x r).segment_subset (mem_ball_self hr) hy
          (Path.range_segment x y ▸ mem_range_self t)
      have hseg_int : localPotentialIntegral φ (Path.segment x y) = g₀ y - g₀ x :=
        TauCeti.localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_ball hg₀ hd₀ hseg_ball
      have hcat_s : ∀ t, ((γ x hx).trans (Path.segment x y)) t ∈ s := fun t ↦ by
        rw [Path.trans_apply]
        split_ifs
        · exact hγ x hx _
        · exact hrs (hseg_ball _)
      rw [hg_eq y (hrs hy) ((γ x hx).trans (Path.segment x y)) hcat_s,
        hφ.localPotentialIntegral_trans (hγ x hx) (fun t ↦ hrs (hseg_ball t)), hseg_int]
      simp only [g, hx, ↓reduceDIte]
      abel
    exact ((hd₀ x (mem_ball_self hr)).add_const (g x - g₀ x)).congr_of_eventuallyEq heq
  exact ⟨g, hgx₀, hφ.contDiffOn_of_hasFDerivAt hderiv, hderiv, hg_eq⟩

/-- **Loop-integral criterion for global potentials (fixed basepoint).** On a path-connected set `s`
with `x₀ ∈ s`, a locally potential covector field `φ` has a global `C¹` potential on `s` if and
only if its continuous path integral vanishes along every loop at `x₀` in `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_basepoint_loop_eq_zero
    (hφ : HasLocalPotentials s φ) {x₀ : E} (hx₀ : x₀ ∈ s) (hs : IsPathConnected s) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x) ↔
      ∀ ℓ : Path x₀ x₀, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0 := by
  refine ⟨fun ⟨g, _, hd⟩ ℓ hℓ ↦ ?_, fun hloop ↦ ?_⟩
  · rw [hφ.localPotentialIntegral_eq_sub_of_hasFDerivAt hd hℓ, sub_self]
  · obtain ⟨g, -, hg, hd, -⟩ :=
      hφ.exists_hasFDerivAt_of_forall_localPotentialIntegral_loop_eq_zero hx₀ hs hloop
    exact ⟨g, hg, hd⟩

/-- **Loop-integral criterion for global potentials.** On a path-connected domain `s` (possibly
empty), a locally potential covector field `φ` has a global `C¹` potential on `s` if and only if
every loop in `s` has vanishing continuous path integral. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialIntegral_loop_eq_zero
    (hφ : HasLocalPotentials s φ) (hs : IsPreconnected s) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x) ↔
      ∀ x₀ ∈ s, ∀ ℓ : Path x₀ x₀, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [contDiffOn_empty]
  · have hpc : IsPathConnected s :=
      ⟨hne.some, hne.some_mem, fun {y} hy ↦ by
        have hconn : IsConnected s := ⟨hne, hs⟩
        exact (hφ.isOpen.isConnected_iff_isPathConnected.mp hconn).joinedIn
          hne.some hne.some_mem y hy⟩
    refine ⟨fun ⟨g, _, hd⟩ x₀ _ ℓ hℓ ↦ ?_, fun hloop ↦ ?_⟩
    · rw [hφ.localPotentialIntegral_eq_sub_of_hasFDerivAt hd hℓ, sub_self]
    · exact (hφ.exists_hasFDerivAt_iff_forall_basepoint_loop_eq_zero hne.some_mem hpc).mpr
        (hloop hne.some hne.some_mem)

end Definition

end TauCeti
