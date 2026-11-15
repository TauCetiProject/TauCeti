/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous path integrals via local potentials

When a covector field `φ : E → E →L[ℝ] F` admits local `C¹` potentials on an open domain `s`, it
can be integrated along any *continuous* path `γ : Path a b` in `s` without differentiating `γ` or
assuming completeness of `F`. Compactness of `[0, 1]` refines the open cover by potential balls to
a finite monotone partition `0 = t 0 ≤ t 1 ≤ ⋯ ≤ t n = 1` such that `γ` maps each `[t i, t (i + 1)]`
into an open set `U i` carrying a primitive `g i` of `φ`; the integral is the sum of endpoint
differences `∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i)))`.

Two primitives of `φ` on overlapping open sets have zero-derivative difference on the overlap, so
their difference is locally constant there (`IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero`) and
therefore constant along any connected subinterval mapped into both sets. Clamping one monotone
partition against another refines both simultaneously, showing that the endpoint-difference sum
is independent of the open sets, primitives, and partition.

Homotopy invariance relative to endpoints follows by applying the Lebesgue-number partition of
`unitInterval × unitInterval` to a homotopy `H : γ₀.Homotopy γ₁`: each cell
`[t i, t (i + 1)] × [t j, t (j + 1)]` maps into a single potential ball, so one row of potentials
evaluates both `H.eval (t i)` and `H.eval (t (i + 1))`, and their difference telescopes along the
vertical cell edges between the fixed endpoints `H (·, 0) = a` and `H (·, 1) = b`. Neither Stokes'
theorem nor any derivative of `H` is used. Completeness of `F` enters only when comparing
`localPotentialIntegral` for a `C¹` path with Mathlib's Bochner integral `curveIntegral`.

## Main declarations

* `TauCeti.localPotentialIntegral φ γ`: the endpoint-difference path integral of `φ` along `γ`
  (returning `0` when no open-set primitive subdivision exists along `γ`).
* `TauCeti.localPotentialIntegral_eq_sum_sub_of_hasFDerivAt` and
  `TauCeti.localPotentialIntegral_eq_sub_of_hasFDerivAt`: evaluation from any open-set primitive
  subdivision or single primitive along `γ`, with no `C¹` hypothesis on the primitives.
* `TauCeti.localPotentialIntegral_refl`, `TauCeti.localPotentialIntegral_symm`,
  `TauCeti.HasLocalPotentials.localPotentialIntegral_trans`, and
  `TauCeti.HasLocalPotentials.localPotentialIntegral_map'`: path operations and naturality under
  `C¹` maps.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_eq_of_homotopy`: invariance under path
  homotopy relative to endpoints inside `s`.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_eq_curveIntegral`: agreement with
  `curveIntegral φ γ` for `C¹` paths when `F` is complete.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_forall_loop_localPotentialIntegral_eq_zero` and
  `TauCeti.HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_localPotentialIntegral_eq_zero`:
  on a path-connected domain, vanishing of loop integrals at a basepoint is necessary and
  sufficient for a global `C¹` potential, constructed by path-independent integration from the
  basepoint.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §1.3 (line integrals
  along arbitrary continuous curves by chains of discs carrying primitives, and invariance under
  homotopy).
-/

public section

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Internal choice witness for `localPotentialIntegral`: a finite monotone subdivision of
`unitInterval` together with open sets and ambient primitives of `φ` covering the corresponding
segments of `γ`. -/
private structure PotentialSubdivision {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) where
  n : ℕ
  t : ℕ → unitInterval
  t_zero : t 0 = 0
  mono : Monotone t
  t_ge : ∀ m ≥ n, t m = 1
  U : ℕ → Set E
  g : ℕ → E → F
  isOpen_U : ∀ i < n, IsOpen (U i)
  hasFDerivAt_g : ∀ i < n, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y
  mapsTo_γ : ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (U i)

private theorem PotentialSubdivision.n_pos {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : 0 < S.n := by
  refine Nat.pos_of_ne_zero fun h0 ↦ zero_ne_one (α := unitInterval) ?_
  rw [← S.t_zero, S.t_ge 0 (h0 ▸ le_rfl)]

/-- The sum of endpoint potential differences associated with a `PotentialSubdivision`. -/
private def PotentialSubdivision.eval {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : F :=
  ∑ i ∈ Finset.range S.n, (S.g i (γ (S.t (i + 1))) - S.g i (γ (S.t i)))

/-- Two ambient primitives of `φ` on open sets `U₁` and `U₂` have equal endpoint increments along
any subinterval `[u, v] ⊆ unitInterval` mapped by `γ` into `U₁ ∩ U₂`. The intersection `U₁ ∩ U₂`
need not be connected: `[u, v]` maps into a single open connected component of `U₁ ∩ U₂`, on which
`g₁` and `g₂` differ by an additive constant (`IsOpen.exists_eq_add_of_fderiv_eq`). -/
private theorem eq_sub_of_mapsTo_Icc {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    {U₁ U₂ : Set E} {g₁ g₂ : E → F} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hd₁ : ∀ y ∈ U₁, HasFDerivAt g₁ (φ y) y) (hd₂ : ∀ y ∈ U₂, HasFDerivAt g₂ (φ y) y)
    {u v : unitInterval} (huv : u ≤ v)
    (hγ₁ : MapsTo γ (Icc u v) U₁) (hγ₂ : MapsTo γ (Icc u v) U₂) :
    g₁ (γ v) - g₁ (γ u) = g₂ (γ v) - g₂ (γ u) := by
  let U : Set E := U₁ ∩ U₂
  let C : Set E := connectedComponentIn U (γ u)
  have hCU : C ⊆ U := connectedComponentIn_subset U (γ u)
  have hC_open : IsOpen C := (hU₁.inter hU₂).connectedComponentIn
  have hmem : ∀ τ ∈ Icc (u : ℝ) (v : ℝ), γ.extend τ ∈ U := by
    intro τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨u.2.1.trans hτ.1, hτ.2.trans v.2.2⟩
    have hτuv : (⟨τ, hτI⟩ : unitInterval) ∈ Icc u v := hτ
    rw [γ.extend_apply hτI]
    exact ⟨hγ₁ hτuv, hγ₂ hτuv⟩
  have himg_pre : IsPreconnected (γ.extend '' Icc (u : ℝ) v) :=
    isPreconnected_Icc.image _ γ.continuous_extend.continuousOn
  have himg_sub : γ.extend '' Icc (u : ℝ) v ⊆ C :=
    himg_pre.subset_connectedComponentIn ⟨u, ⟨le_rfl, huv⟩, γ.extend_apply u.2⟩
      (image_subset_iff.mpr hmem)
  have huC : γ u ∈ C := mem_connectedComponentIn ⟨hγ₁ ⟨le_rfl, huv⟩, hγ₂ ⟨le_rfl, huv⟩⟩
  have hvC : γ v ∈ C := himg_sub ⟨v, ⟨huv, le_rfl⟩, γ.extend_apply v.2⟩
  obtain ⟨c, hc⟩ := hC_open.exists_eq_add_of_fderiv_eq isPreconnected_connectedComponentIn
    (fun y hy ↦ (hd₁ y (hCU hy).1).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd₂ y (hCU hy).2).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd₁ y (hCU hy).1).fderiv.trans (hd₂ y (hCU hy).2).fderiv.symm)
  rw [hc hvC, hc huC]
  exact add_sub_add_right_eq_sub (g₂ (γ v)) (g₂ (γ u)) c

/-- Any two `PotentialSubdivision`s of the same path yield the same sum of endpoint differences:
clamping one monotone partition to each subinterval of the other produces a common grid on which
matching cells agree by `eq_sub_of_mapsTo_Icc` and non-overlapping cells collapse to zero. -/
private theorem PotentialSubdivision.eval_eq {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    (S₁ S₂ : PotentialSubdivision φ γ) : S₁.eval = S₂.eval := by
  let α₁ (i k : ℕ) : unitInterval := max (S₁.t i) (min (S₁.t (i + 1)) (S₂.t k))
  let α₂ (j k : ℕ) : unitInterval := max (S₂.t j) (min (S₂.t (j + 1)) (S₁.t k))
  have hle_one (x : unitInterval) : x ≤ 1 := x.2.2
  have hrow₁ (i : ℕ) : S₁.g i (γ (S₁.t (i + 1))) - S₁.g i (γ (S₁.t i)) =
      ∑ j ∈ Finset.range S₂.n, (S₁.g i (γ (α₁ i (j + 1))) - S₁.g i (γ (α₁ i j))) := by
    rw [Finset.sum_range_sub (fun k ↦ S₁.g i (γ (α₁ i k))) S₂.n]
    have h0 : α₁ i 0 = S₁.t i := by simp [α₁, S₂.t_zero]
    have hn : α₁ i S₂.n = S₁.t (i + 1) := by
      simp only [α₁, S₂.t_ge S₂.n le_rfl, min_eq_left (hle_one _),
        max_eq_right (S₁.mono (Nat.le_succ i))]
    rw [h0, hn]
  have hrow₂ (j : ℕ) : S₂.g j (γ (S₂.t (j + 1))) - S₂.g j (γ (S₂.t j)) =
      ∑ i ∈ Finset.range S₁.n, (S₂.g j (γ (α₂ j (i + 1))) - S₂.g j (γ (α₂ j i))) := by
    rw [Finset.sum_range_sub (fun k ↦ S₂.g j (γ (α₂ j k))) S₁.n]
    have h0 : α₂ j 0 = S₂.t j := by simp [α₂, S₁.t_zero]
    have hn : α₂ j S₁.n = S₂.t (j + 1) := by
      simp only [α₂, S₁.t_ge S₁.n le_rfl, min_eq_left (hle_one _),
        max_eq_right (S₂.mono (Nat.le_succ j))]
    rw [h0, hn]
  unfold PotentialSubdivision.eval
  rw [Finset.sum_congr rfl fun i _ ↦ hrow₁ i, Finset.sum_congr rfl fun j _ ↦ hrow₂ j,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi hj
  have h₁ : S₁.t i ≤ S₁.t (i + 1) := S₁.mono (Nat.le_succ i)
  have h₂ : S₂.t j ≤ S₂.t (j + 1) := S₂.mono (Nat.le_succ j)
  by_cases hle : max (S₁.t i) (S₂.t j) ≤ min (S₁.t (i + 1)) (S₂.t (j + 1))
  · have hu₁v₂ : S₁.t i ≤ S₂.t (j + 1) := (le_max_left _ _).trans (hle.trans (min_le_right _ _))
    have hu₂v₁ : S₂.t j ≤ S₁.t (i + 1) := (le_max_right _ _).trans (hle.trans (min_le_left _ _))
    have hα₁₀ : α₁ i j = max (S₁.t i) (S₂.t j) := by simp [α₁, min_eq_right hu₂v₁]
    have hα₂₀ : α₂ j i = max (S₁.t i) (S₂.t j) := by simp [α₂, min_eq_right hu₁v₂, max_comm]
    have hα₁₁ : α₁ i (j + 1) = min (S₁.t (i + 1)) (S₂.t (j + 1)) :=
      max_eq_right ((le_max_left _ _).trans hle)
    have hα₂₁ : α₂ j (i + 1) = min (S₁.t (i + 1)) (S₂.t (j + 1)) := by
      simp only [α₂, min_comm (S₂.t (j + 1)) (S₁.t (i + 1))]
      exact max_eq_right ((le_max_right _ _).trans hle)
    rw [hα₁₀, hα₂₀, hα₁₁, hα₂₁]
    refine eq_sub_of_mapsTo_Icc (S₁.isOpen_U i hi) (S₂.isOpen_U j hj)
      (S₁.hasFDerivAt_g i hi) (S₂.hasFDerivAt_g j hj) hle
      ((S₁.mapsTo_γ i hi).mono ?_ Subset.rfl) ((S₂.mapsTo_γ j hj).mono ?_ Subset.rfl)
    · exact fun τ hτ ↦ ⟨(le_max_left _ _).trans hτ.1, hτ.2.trans (min_le_left _ _)⟩
    · exact fun τ hτ ↦ ⟨(le_max_right _ _).trans hτ.1, hτ.2.trans (min_le_right _ _)⟩
  · -- When `min v₁ v₂ < max u₁ u₂`, one interval precedes the other and both clamped segments
    -- collapse to single points.
    rcases lt_max_iff.mp (lt_of_not_ge hle) with hcase | hcase
    · have hv₂u₁ : S₂.t (j + 1) ≤ S₁.t i := by
        rcases min_cases (S₁.t (i + 1)) (S₂.t (j + 1)) with ⟨hmin, -⟩ | ⟨hmin, -⟩
        · exact False.elim ((hmin ▸ hcase).not_ge h₁)
        · exact (hmin ▸ hcase).le
      have hα₁₀ : α₁ i j = S₁.t i :=
        max_eq_left ((min_le_right _ _).trans (h₂.trans hv₂u₁))
      have hα₁₁ : α₁ i (j + 1) = S₁.t i :=
        max_eq_left ((min_le_right _ _).trans hv₂u₁)
      have hα₂₀ : α₂ j i = S₂.t (j + 1) := by
        simp [α₂, min_eq_left hv₂u₁, max_eq_right h₂]
      have hα₂₁ : α₂ j (i + 1) = S₂.t (j + 1) := by
        simp [α₂, min_eq_left (hv₂u₁.trans h₁), max_eq_right h₂]
      simp [hα₁₀, hα₁₁, hα₂₀, hα₂₁]
    · have hv₁u₂ : S₁.t (i + 1) ≤ S₂.t j := by
        rcases min_cases (S₁.t (i + 1)) (S₂.t (j + 1)) with ⟨hmin, -⟩ | ⟨hmin, -⟩
        · exact (hmin ▸ hcase).le
        · exact False.elim ((hmin ▸ hcase).not_ge h₂)
      have hα₁₀ : α₁ i j = S₁.t (i + 1) := by
        simp [α₁, min_eq_left hv₁u₂, max_eq_right h₁]
      have hα₁₁ : α₁ i (j + 1) = S₁.t (i + 1) := by
        simp [α₁, min_eq_left (hv₁u₂.trans h₂), max_eq_right h₁]
      have hα₂₀ : α₂ j i = S₂.t j :=
        max_eq_left ((min_le_right _ _).trans (h₁.trans hv₁u₂))
      have hα₂₁ : α₂ j (i + 1) = S₂.t j :=
        max_eq_left ((min_le_right _ _).trans hv₁u₂)
      simp [hα₁₀, hα₁₁, hα₂₀, hα₂₁]

/-- Existence of a `PotentialSubdivision` along any continuous path inside a domain where `φ` has
local potentials, via the Lebesgue-number partition of `unitInterval`. -/
private theorem HasLocalPotentials.nonempty_potentialSubdivision {s : Set E} {a b : E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    Nonempty (PotentialSubdivision φ γ) := by
  choose r hr _ g _ hd using fun τ : unitInterval ↦ hasLocalPotentials_iff.mp hφ (γ τ) (hγ τ)
  have hopen (τ : unitInterval) : IsOpen (γ ⁻¹' ball (γ τ) (r τ)) :=
    isOpen_ball.preimage γ.continuous
  have hcov : (univ : Set unitInterval) ⊆ ⋃ τ, γ ⁻¹' ball (γ τ) (r τ) :=
    fun τ _ ↦ mem_iUnion.mpr ⟨τ, mem_ball_self (hr τ)⟩
  obtain ⟨t, ht0, hmono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcov
  choose idx hidx using hsub
  exact ⟨{
    n := n
    t := t
    t_zero := ht0
    mono := hmono
    t_ge := htn
    U := fun i ↦ ball (γ (idx i)) (r (idx i))
    g := fun i ↦ g (idx i)
    isOpen_U := fun _ _ ↦ isOpen_ball
    hasFDerivAt_g := fun i _ ↦ hd (idx i)
    mapsTo_γ := fun i _ τ hτ ↦ hidx i hτ }⟩

/-- The continuous path integral of a covector field `φ : E → E →L[ℝ] F` along a path `γ : Path a b`
through local potentials, defined as the sum of endpoint differences of local primitives over any
finite monotone subdivision of `unitInterval` (and `0` if no such subdivision exists). Neither
completeness of `F` nor differentiability of `φ` or `γ` is required. -/
def localPotentialIntegral {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) : F :=
  open Classical in
  if h : Nonempty (PotentialSubdivision φ γ) then h.some.eval else 0

private theorem localPotentialIntegral_eq_eval {a b : E} {φ : E → E →L[ℝ] F} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : localPotentialIntegral φ γ = S.eval := by
  classical
  have h : Nonempty (PotentialSubdivision φ γ) := ⟨S⟩
  simp only [localPotentialIntegral, h, ↓reduceDIte]
  exact h.some.eval_eq S

/-! ### Subdivision and single-primitive evaluation -/

/-- Evaluate `localPotentialIntegral φ γ` from any finite monotone partition of `unitInterval`
whose subintervals are mapped by `γ` into open sets carrying ambient primitives of `φ`. -/
theorem localPotentialIntegral_eq_sum_sub_of_hasFDerivAt {a b : E} {φ : E → E →L[ℝ] F}
    {γ : Path a b} {n : ℕ} {t : ℕ → unitInterval} (ht₀ : t 0 = 0) (hmono : Monotone t)
    (htn : t n = 1) {U : ℕ → Set E} {g : ℕ → E → F} (hU : ∀ i < n, IsOpen (U i))
    (hd : ∀ i < n, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y)
    (hγ : ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (U i)) :
    localPotentialIntegral φ γ = ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i))) := by
  let t' : ℕ → unitInterval := fun k ↦ if k ≤ n then t k else 1
  have ht'₀ : t' 0 = 0 := by simp [t', ht₀]
  have hmono' : Monotone t' := by
    intro i j hij
    simp only [t']
    split_ifs with hi hj hj
    · exact hmono hij
    · exact (t i).2.2
    · omega
    · exact le_rfl
  have ht'ge : ∀ m ≥ n, t' m = 1 := by
    intro m hm
    simp only [t']
    split_ifs with hmn
    · obtain rfl : m = n := le_antisymm hmn hm
      exact htn
    · rfl
  have hagree : ∀ k ≤ n, t' k = t k := fun k hk ↦ by simp [t', hk]
  let S : PotentialSubdivision φ γ := {
    n := n
    t := t'
    t_zero := ht'₀
    mono := hmono'
    t_ge := ht'ge
    U := U
    g := g
    isOpen_U := hU
    hasFDerivAt_g := hd
    mapsTo_γ := fun i hi ↦ by
      rw [hagree i (Nat.le_of_lt hi), hagree (i + 1) (Nat.succ_le_of_lt hi)]
      exact hγ i hi }
  rw [localPotentialIntegral_eq_eval S]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  simp only [S, hagree i (Nat.le_of_lt hi), hagree (i + 1) (Nat.succ_le_of_lt hi)]

/-- Fundamental theorem of calculus for `localPotentialIntegral`: if `g` differentiates to `φ` at
every point of an open set `s` containing the image of `γ`, then `localPotentialIntegral φ γ` is
the endpoint difference `g b - g a`. -/
theorem localPotentialIntegral_eq_sub_of_hasFDerivAt {s : Set E} {a b : E} {φ : E → E →L[ℝ] F}
    {g : E → F} (hs : IsOpen s) (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) : localPotentialIntegral φ γ = g b - g a := by
  let t : ℕ → unitInterval := fun k ↦ if k = 0 then 0 else 1
  have hmono : Monotone t := by
    intro i j hij
    simp only [t]
    split_ifs with hi hj hj
    · exact le_rfl
    · exact zero_le_one
    · omega
    · exact le_rfl
  have h := localPotentialIntegral_eq_sum_sub_of_hasFDerivAt (φ := φ) (γ := γ) (n := 1) (t := t)
    (by simp [t]) hmono (by simp [t]) (U := fun _ ↦ s) (g := fun _ ↦ g)
    (fun _ _ ↦ hs) (fun _ _ ↦ hd) (fun _ _ τ _ ↦ hγ τ)
  simpa [t] using h

/-- `localPotentialIntegral` depends only on the values of `φ` on any open set containing the
path: if `φ` and `ψ` agree on an open neighbourhood of `range γ`, their path integrals coincide. -/
theorem localPotentialIntegral_congr_of_isOpen {s : Set E} {a b : E} {φ ψ : E → E →L[ℝ] F}
    (hs : IsOpen s) (h : EqOn φ ψ s) {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = localPotentialIntegral ψ γ := by
  let tr (ψ₁ ψ₂ : E → E →L[ℝ] F) (hψ : EqOn ψ₁ ψ₂ s)
      (S : PotentialSubdivision ψ₁ γ) : PotentialSubdivision ψ₂ γ := {
    n := S.n
    t := S.t
    t_zero := S.t_zero
    mono := S.mono
    t_ge := S.t_ge
    U := fun i ↦ S.U i ∩ s
    g := S.g
    isOpen_U := fun i hi ↦ (S.isOpen_U i hi).inter hs
    hasFDerivAt_g := fun i hi y hy ↦ hψ hy.2 ▸ S.hasFDerivAt_g i hi y hy.1
    mapsTo_γ := fun i hi τ hτ ↦ ⟨S.mapsTo_γ i hi hτ, hγ τ⟩ }
  classical
  by_cases hne : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := hne
    rw [localPotentialIntegral_eq_eval S, localPotentialIntegral_eq_eval (tr φ ψ h S)]
    unfold PotentialSubdivision.eval
    rfl
  · have hne' : ¬ Nonempty (PotentialSubdivision ψ γ) :=
      fun ⟨S⟩ ↦ hne ⟨tr ψ φ h.symm S⟩
    simp [localPotentialIntegral, hne, hne']

/-- If `φ` has local potentials on `s` and agrees with `ψ` on `s`, then `φ` and `ψ` have the same
path integral along every path in `s`. -/
theorem HasLocalPotentials.localPotentialIntegral_congr {s : Set E} {a b : E}
    {φ ψ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (h : EqOn φ ψ s) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) : localPotentialIntegral φ γ = localPotentialIntegral ψ γ :=
  localPotentialIntegral_congr_of_isOpen hφ.isOpen h hγ

/-! ### Path and algebraic operations -/

/-- A constant path has zero potential integral. -/
@[simp]
theorem localPotentialIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    localPotentialIntegral φ (Path.refl a) = 0 := by
  classical
  by_cases h : Nonempty (PotentialSubdivision φ (Path.refl a))
  · obtain ⟨S⟩ := h
    rw [localPotentialIntegral_eq_eval S]
    simp [PotentialSubdivision.eval]
  · simp [localPotentialIntegral, h]

/-- Casting path endpoints preserves `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_cast {a b a' b' : E} (φ : E → E →L[ℝ] F) (γ : Path a b)
    (ha : a' = a) (hb : b' = b) :
    localPotentialIntegral φ (γ.cast ha hb) = localPotentialIntegral φ γ := by
  subst ha; subst hb; rfl

/-- Reversing a path negates its potential integral. -/
@[simp]
theorem localPotentialIntegral_symm {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral φ γ.symm = -localPotentialIntegral φ γ := by
  have rev (x y : E) (p : Path x y) (S : PotentialSubdivision φ p) :
      ∃ S' : PotentialSubdivision φ p.symm, S'.eval = -S.eval := by
    let t' : ℕ → unitInterval := fun i ↦
      if i ≤ S.n then unitInterval.symm (S.t (S.n - i)) else 1
    have ht'₀ : t' 0 = 0 := by simp [t', S.t_ge S.n le_rfl]
    have hmono' : Monotone t' := by
      intro i j hij
      simp only [t']
      split_ifs with hi hj hj
      · exact unitInterval.strictAnti_symm.antitone (S.mono (Nat.sub_le_sub_left hij S.n))
      · exact (unitInterval.symm (S.t (S.n - i))).2.2
      · omega
      · exact le_rfl
    have ht'ge : ∀ m ≥ S.n, t' m = 1 := by
      intro m hm
      simp only [t']
      split_ifs with hmn
      · obtain rfl : m = S.n := le_antisymm hmn hm
        simp [S.t_zero]
      · rfl
    let S' : PotentialSubdivision φ p.symm := {
      n := S.n
      t := t'
      t_zero := ht'₀
      mono := hmono'
      t_ge := ht'ge
      U := fun i ↦ S.U (S.n - 1 - i)
      g := fun i ↦ S.g (S.n - 1 - i)
      isOpen_U := fun i hi ↦ S.isOpen_U _ (by omega)
      hasFDerivAt_g := fun i hi ↦ S.hasFDerivAt_g _ (by omega)
      mapsTo_γ := fun i hi τ hτ ↦ by
        have hk : S.n - 1 - i < S.n := by omega
        have hsub₁ : S.n - i = (S.n - 1 - i) + 1 := by omega
        have hsub₂ : S.n - (i + 1) = S.n - 1 - i := by omega
        have ht₁ : t' i = unitInterval.symm (S.t ((S.n - 1 - i) + 1)) := by
          simp [t', Nat.le_of_lt hi, hsub₁]
        have ht₂ : t' (i + 1) = unitInterval.symm (S.t (S.n - 1 - i)) := by
          simp [t', Nat.succ_le_of_lt hi, hsub₂]
        rw [ht₁, ht₂] at hτ
        have hsymm : unitInterval.symm τ ∈ Icc (S.t (S.n - 1 - i)) (S.t ((S.n - 1 - i) + 1)) :=
          ⟨unitInterval.le_symm_comm.mp hτ.2, unitInterval.symm_le_comm.mp hτ.1⟩
        change p.symm τ ∈ S.U (S.n - 1 - i)
        rw [Path.symm_apply]
        exact S.mapsTo_γ _ hk hsymm }
    refine ⟨S', ?_⟩
    unfold PotentialSubdivision.eval
    rw [← Finset.sum_neg_distrib, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have hidx : S.n - 1 - (S.n - 1 - i) = i := by omega
    have hle₁ : S.n - 1 - i + 1 ≤ S.n := by omega
    have hle₂ : S.n - 1 - i ≤ S.n := by omega
    have hsub₁ : S.n - (S.n - 1 - i + 1) = i := by omega
    have hsub₂ : S.n - (S.n - 1 - i) = i + 1 := by omega
    have ht_succ : t' (S.n - 1 - i + 1) = unitInterval.symm (S.t i) := by
      simp [t', hle₁, hsub₁]
    have ht_curr : t' (S.n - 1 - i) = unitInterval.symm (S.t (i + 1)) := by
      simp [t', hle₂, hsub₂]
    simp only [S', hidx, Path.symm_apply, Function.comp_apply, ht_succ, ht_curr,
      unitInterval.symm_symm, neg_sub]
  classical
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    obtain ⟨S', hS'⟩ := rev a b γ S
    rw [localPotentialIntegral_eq_eval S, localPotentialIntegral_eq_eval S', hS']
  · have h' : ¬ Nonempty (PotentialSubdivision φ γ.symm) := by
      rintro ⟨S'⟩
      obtain ⟨S'', _⟩ := rev b a γ.symm S'
      rw [Path.symm_symm] at S''
      exact h ⟨S''⟩
    simp [localPotentialIntegral, h, h']

/-- Additivity of `localPotentialIntegral` under path concatenation. -/
theorem HasLocalPotentials.localPotentialIntegral_trans {s : Set E} {a b c : E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {γ₁ : Path a b} {γ₂ : Path b c}
    (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ (γ₁.trans γ₂) =
      localPotentialIntegral φ γ₁ + localPotentialIntegral φ γ₂ := by
  obtain ⟨S₁⟩ := hφ.nonempty_potentialSubdivision hγ₁
  obtain ⟨S₂⟩ := hφ.nonempty_potentialSubdivision hγ₂
  let halfLeft (u : unitInterval) : unitInterval :=
    ⟨(u : ℝ) / 2, ⟨div_nonneg u.2.1 zero_le_two, by linarith [u.2.2]⟩⟩
  let halfRight (v : unitInterval) : unitInterval :=
    ⟨((v : ℝ) + 1) / 2, ⟨by linarith [v.2.1], by linarith [v.2.2]⟩⟩
  have hleft_apply (u : unitInterval) : (γ₁.trans γ₂) (halfLeft u) = γ₁ u := by
    have hle : ((halfLeft u : unitInterval) : ℝ) ≤ 1 / 2 := by
      change (u : ℝ) / 2 ≤ 1 / 2
      linarith [u.2.2]
    rw [Path.trans_apply]
    simp only [hle, ↓reduceDIte]
    congr 1; ext; change 2 * ((u : ℝ) / 2) = u; ring
  have hright_apply (v : unitInterval) : (γ₁.trans γ₂) (halfRight v) = γ₂ v := by
    by_cases hv : (v : ℝ) = 0
    · have hv0 : v = 0 := Subtype.ext hv
      subst hv0
      have hle : ((halfRight 0 : unitInterval) : ℝ) ≤ 1 / 2 := by
        change ((0 : ℝ) + 1) / 2 ≤ 1 / 2
        norm_num
      rw [Path.trans_apply]
      simp only [hle, ↓reduceDIte]
      have h1 : (⟨2 * ((halfRight 0 : unitInterval) : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(halfRight 0).2.1, hle⟩⟩ : unitInterval) =
          1 := by
        ext; change 2 * (((0 : ℝ) + 1) / 2) = 1; ring
      rw [h1, γ₁.target, γ₂.source]
    · have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.2.1 (Ne.symm hv)
      have hnle : ¬ (((halfRight v : unitInterval) : ℝ) ≤ 1 / 2) := by
        change ¬ (((v : ℝ) + 1) / 2 ≤ 1 / 2)
        linarith
      rw [Path.trans_apply]
      simp only [hnle, ↓reduceDIte]
      congr 1; ext; change 2 * (((v : ℝ) + 1) / 2) - 1 = v; ring
  let t : ℕ → unitInterval := fun k ↦
    if k ≤ S₁.n then halfLeft (S₁.t k) else halfRight (S₂.t (k - S₁.n))
  have ht_left (k : ℕ) (hk : k ≤ S₁.n) : t k = halfLeft (S₁.t k) := by simp [t, hk]
  have ht_right (k : ℕ) : t (S₁.n + k) = halfRight (S₂.t k) := by
    by_cases hk : k = 0
    · subst hk
      simp only [t, Nat.add_zero, le_rfl, ↓reduceIte, S₁.t_ge S₁.n le_rfl, S₂.t_zero]
      ext; change (1 : ℝ) / 2 = ((0 : ℝ) + 1) / 2; ring
    · have hgt : ¬ (S₁.n + k ≤ S₁.n) := by omega
      simp [t, hgt]
  have ht0 : t 0 = 0 := by
    rw [ht_left 0 (Nat.zero_le _), S₁.t_zero]
    ext; simp [halfLeft]
  have htn : t (S₁.n + S₂.n) = 1 := by
    rw [ht_right S₂.n, S₂.t_ge S₂.n le_rfl]
    ext; change ((1 : ℝ) + 1) / 2 = 1; ring
  have hmono : Monotone t := by
    intro i j hij
    simp only [t]
    split_ifs with hi hj hj
    · have hle : (S₁.t i : ℝ) ≤ S₁.t j := S₁.mono hij
      change (S₁.t i : ℝ) / 2 ≤ (S₁.t j : ℝ) / 2
      linarith
    · change (S₁.t i : ℝ) / 2 ≤ ((S₂.t (j - S₁.n) : ℝ) + 1) / 2
      linarith [(S₁.t i).2.2, (S₂.t (j - S₁.n)).2.1]
    · omega
    · have hle : (S₂.t (i - S₁.n) : ℝ) ≤ S₂.t (j - S₁.n) :=
        S₂.mono (Nat.sub_le_sub_right hij S₁.n)
      change ((S₂.t (i - S₁.n) : ℝ) + 1) / 2 ≤ ((S₂.t (j - S₁.n) : ℝ) + 1) / 2
      linarith
  let U : ℕ → Set E := fun k ↦ if k < S₁.n then S₁.U k else S₂.U (k - S₁.n)
  let g : ℕ → E → F := fun k ↦ if k < S₁.n then S₁.g k else S₂.g (k - S₁.n)
  have hmaps : ∀ k < S₁.n + S₂.n, MapsTo (γ₁.trans γ₂) (Icc (t k) (t (k + 1))) (U k) := by
    intro k hk τ hτ
    by_cases hk₁ : k < S₁.n
    · simp only [U, hk₁, ↓reduceIte]
      rw [ht_left k (Nat.le_of_lt hk₁), ht_left (k + 1) (Nat.succ_le_of_lt hk₁)] at hτ
      have hτ_le : (τ : ℝ) ≤ 1 / 2 := by
        have h2 : (τ : ℝ) ≤ (S₁.t (k + 1) : ℝ) / 2 := hτ.2
        linarith [(S₁.t (k + 1)).2.2]
      rw [Path.trans_apply]
      simp only [hτ_le, ↓reduceDIte]
      refine S₁.mapsTo_γ k hk₁ ⟨?_, ?_⟩
      · have h1 : (S₁.t k : ℝ) / 2 ≤ τ := hτ.1
        change (S₁.t k : ℝ) ≤ 2 * (τ : ℝ)
        linarith
      · have h2 : (τ : ℝ) ≤ (S₁.t (k + 1) : ℝ) / 2 := hτ.2
        change 2 * (τ : ℝ) ≤ S₁.t (k + 1)
        linarith
    · have hge : S₁.n ≤ k := Nat.le_of_not_lt hk₁
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      have hj : j < S₂.n := by omega
      simp only [U, hk₁, ↓reduceIte, Nat.add_sub_cancel_left]
      have hnext : S₁.n + j + 1 = S₁.n + (j + 1) := by omega
      rw [ht_right j, hnext, ht_right (j + 1)] at hτ
      by_cases hτ_half : (τ : ℝ) ≤ 1 / 2
      · have h1 : ((S₂.t j : ℝ) + 1) / 2 ≤ τ := hτ.1
        have hτ_eq : τ = halfRight 0 := by
          ext; change (τ : ℝ) = ((0 : ℝ) + 1) / 2; linarith [(S₂.t j).2.1]
        have hj0 : S₂.t j = 0 := by
          ext; change (S₂.t j : ℝ) = 0; linarith [(S₂.t j).2.1]
        rw [hτ_eq, hright_apply]
        exact S₂.mapsTo_γ j hj ⟨hj0.le, (S₂.t (j + 1)).2.1⟩
      · rw [Path.trans_apply]
        simp only [hτ_half, ↓reduceDIte]
        refine S₂.mapsTo_γ j hj ⟨?_, ?_⟩
        · have h1 : ((S₂.t j : ℝ) + 1) / 2 ≤ τ := hτ.1
          change (S₂.t j : ℝ) ≤ 2 * (τ : ℝ) - 1
          linarith
        · have h2 : (τ : ℝ) ≤ ((S₂.t (j + 1) : ℝ) + 1) / 2 := hτ.2
          change 2 * (τ : ℝ) - 1 ≤ S₂.t (j + 1)
          linarith
  have hU_open : ∀ k < S₁.n + S₂.n, IsOpen (U k) := by
    intro k hk
    simp only [U]
    split_ifs with hk₁
    · exact S₁.isOpen_U k hk₁
    · exact S₂.isOpen_U _ (by omega)
  have hd_g : ∀ k < S₁.n + S₂.n, ∀ y ∈ U k, HasFDerivAt (g k) (φ y) y := by
    intro k hk
    simp only [U, g]
    split_ifs with hk₁
    · exact S₁.hasFDerivAt_g k hk₁
    · exact S₂.hasFDerivAt_g _ (by omega)
  rw [localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono htn hU_open hd_g hmaps,
    Finset.sum_range_add, localPotentialIntegral_eq_eval S₁, localPotentialIntegral_eq_eval S₂]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    simp only [g, hi, ↓reduceIte, ht_left i (Nat.le_of_lt hi),
      ht_left (i + 1) (Nat.succ_le_of_lt hi), hleft_apply]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hnlt : ¬ (S₁.n + j < S₁.n) := by omega
    have hnext : S₁.n + j + 1 = S₁.n + (j + 1) := by omega
    simp only [g, hnlt, ↓reduceIte, Nat.add_sub_cancel_left, ht_right j, hnext,
      ht_right (j + 1), hright_apply]

/-- The zero covector field has zero path integral along every path. -/
@[simp]
theorem localPotentialIntegral_zero {a b : E} (γ : Path a b) :
    localPotentialIntegral (0 : E → E →L[ℝ] F) γ = 0 := by
  simpa [Pi.zero_def] using localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_univ
    (φ := fun _ ↦ (0 : E →L[ℝ] F)) (g := fun _ ↦ (0 : F))
    (fun _ _ ↦ hasFDerivAt_const 0 _) (fun _ ↦ mem_univ _)

/-- A constant covector field `L` integrates along any continuous path from `a` to `b` to
`L b - L a`, regardless of the regularity of the path. -/
theorem localPotentialIntegral_const {a b : E} (L : E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (fun _ ↦ L) γ = L b - L a :=
  localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_univ (fun _ _ ↦ L.hasFDerivAt)
    (fun _ ↦ mem_univ _)

/-- Negating the covector field negates its potential integral. -/
@[simp]
theorem localPotentialIntegral_neg {a b : E} (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (-φ) γ = -localPotentialIntegral φ γ := by
  have negSub (ψ : E → E →L[ℝ] F) (S : PotentialSubdivision ψ γ) :
      ∃ S' : PotentialSubdivision (-ψ) γ, S'.eval = -S.eval :=
    ⟨{ n := S.n, t := S.t, t_zero := S.t_zero, mono := S.mono, t_ge := S.t_ge, U := S.U,
       g := fun i ↦ -S.g i, isOpen_U := S.isOpen_U,
       hasFDerivAt_g := fun i hi y hy ↦ (S.hasFDerivAt_g i hi y hy).neg,
       mapsTo_γ := S.mapsTo_γ },
     by
       unfold PotentialSubdivision.eval
       rw [← Finset.sum_neg_distrib]
       refine Finset.sum_congr rfl fun _ _ ↦ ?_
       simp only [Pi.neg_apply]
       abel⟩
  classical
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    obtain ⟨S', hS'⟩ := negSub φ S
    rw [localPotentialIntegral_eq_eval S, localPotentialIntegral_eq_eval S', hS']
  · have h' : ¬ Nonempty (PotentialSubdivision (-φ) γ) := by
      rintro ⟨S'⟩
      obtain ⟨S'', _⟩ := negSub (-φ) S'
      rw [neg_neg] at S''
      exact h ⟨S''⟩
    simp [localPotentialIntegral, h, h']

/-- Scaling the covector field by a real scalar scales its potential integral. -/
@[simp]
theorem localPotentialIntegral_smul {a b : E} (c : ℝ) (φ : E → E →L[ℝ] F) (γ : Path a b) :
    localPotentialIntegral (c • φ) γ = c • localPotentialIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have smulSub (d : ℝ) (ψ : E → E →L[ℝ] F) (S : PotentialSubdivision ψ γ) :
        ∃ S' : PotentialSubdivision (d • ψ) γ, S'.eval = d • S.eval :=
      ⟨{ n := S.n, t := S.t, t_zero := S.t_zero, mono := S.mono, t_ge := S.t_ge, U := S.U,
         g := fun i ↦ d • S.g i, isOpen_U := S.isOpen_U,
         hasFDerivAt_g := fun i hi y hy ↦ (S.hasFDerivAt_g i hi y hy).const_smul d,
         mapsTo_γ := S.mapsTo_γ },
       by simp [PotentialSubdivision.eval, Finset.smul_sum, smul_sub]⟩
    classical
    by_cases h : Nonempty (PotentialSubdivision φ γ)
    · obtain ⟨S⟩ := h
      obtain ⟨S', hS'⟩ := smulSub c φ S
      rw [localPotentialIntegral_eq_eval S, localPotentialIntegral_eq_eval S', hS']
    · have h' : ¬ Nonempty (PotentialSubdivision (c • φ) γ) := by
        rintro ⟨S'⟩
        obtain ⟨S'', _⟩ := smulSub c⁻¹ (c • φ) S'
        rw [inv_smul_smul₀ hc] at S''
        exact h ⟨S''⟩
      simp [localPotentialIntegral, h, h']

/-- Linearity of `localPotentialIntegral` in the covector field under addition. -/
theorem HasLocalPotentials.localPotentialIntegral_add {s : Set E} {a b : E}
    {φ ψ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ + ψ) γ =
      localPotentialIntegral φ γ + localPotentialIntegral ψ γ := by
  choose r₁ hr₁ _ g₁ _ hd₁ using fun τ : unitInterval ↦ hasLocalPotentials_iff.mp hφ (γ τ) (hγ τ)
  choose r₂ hr₂ _ g₂ _ hd₂ using fun τ : unitInterval ↦ hasLocalPotentials_iff.mp hψ (γ τ) (hγ τ)
  let r (τ : unitInterval) : ℝ := min (r₁ τ) (r₂ τ)
  have hr (τ : unitInterval) : 0 < r τ := lt_min (hr₁ τ) (hr₂ τ)
  have hopen (τ : unitInterval) : IsOpen (γ ⁻¹' ball (γ τ) (r τ)) :=
    isOpen_ball.preimage γ.continuous
  have hcov : (univ : Set unitInterval) ⊆ ⋃ τ, γ ⁻¹' ball (γ τ) (r τ) :=
    fun τ _ ↦ mem_iUnion.mpr ⟨τ, mem_ball_self (hr τ)⟩
  obtain ⟨t, ht0, hmono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcov
  choose idx hidx using hsub
  let U (i : ℕ) : Set E := ball (γ (idx i)) (r (idx i))
  have hb₁ (i : ℕ) : U i ⊆ ball (γ (idx i)) (r₁ (idx i)) := ball_subset_ball (min_le_left _ _)
  have hb₂ (i : ℕ) : U i ⊆ ball (γ (idx i)) (r₂ (idx i)) := ball_subset_ball (min_le_right _ _)
  have hmaps : ∀ i < n, MapsTo γ (Icc (t i) (t (i + 1))) (U i) := fun i _ τ hτ ↦ hidx i hτ
  change localPotentialIntegral (fun y ↦ φ y + ψ y) γ = _
  rw [localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono (htn n le_rfl)
        (U := U) (g := fun i ↦ g₁ (idx i) + g₂ (idx i)) (fun _ _ ↦ isOpen_ball)
        (fun i _ y hy ↦ (hd₁ (idx i) y (hb₁ i hy)).add (hd₂ (idx i) y (hb₂ i hy))) hmaps,
      localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono (htn n le_rfl)
        (U := U) (g := fun i ↦ g₁ (idx i)) (fun _ _ ↦ isOpen_ball)
        (fun i _ y hy ↦ hd₁ (idx i) y (hb₁ i hy)) hmaps,
      localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono (htn n le_rfl)
        (U := U) (g := fun i ↦ g₂ (idx i)) (fun _ _ ↦ isOpen_ball)
        (fun i _ y hy ↦ hd₂ (idx i) y (hb₂ i hy)) hmaps,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.add_apply]
  abel

/-- Linearity of `localPotentialIntegral` in the covector field under subtraction. -/
theorem HasLocalPotentials.localPotentialIntegral_sub {s : Set E} {a b : E}
    {φ ψ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ)
    {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ - ψ) γ =
      localPotentialIntegral φ γ - localPotentialIntegral ψ γ := by
  rw [sub_eq_add_neg, hφ.localPotentialIntegral_add hψ.neg hγ, localPotentialIntegral_neg,
    sub_eq_add_neg]

/-- Continuous linear maps commute with `localPotentialIntegral`. -/
theorem HasLocalPotentials.localPotentialIntegral_continuousLinearMap_comp {s : Set E} {a b : E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (L : F →L[ℝ] G) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (fun x ↦ L.comp (φ x)) γ = L (localPotentialIntegral φ γ) := by
  obtain ⟨S⟩ := hφ.nonempty_potentialSubdivision hγ
  rw [localPotentialIntegral_eq_eval S,
      localPotentialIntegral_eq_sum_sub_of_hasFDerivAt S.t_zero S.mono (S.t_ge S.n le_rfl)
        S.isOpen_U (g := fun i ↦ L ∘ S.g i)
        (fun i hi y hy ↦ L.hasFDerivAt.comp y (S.hasFDerivAt_g i hi y hy)) S.mapsTo_γ]
  simp [PotentialSubdivision.eval, map_sum, map_sub]

/-! ### Naturality under `C¹` pullback -/

/-- Naturality of `localPotentialIntegral` under a `C¹` map of open domains: integrating the
pullback covector field `(φ (f ·)).comp (fderiv ℝ f ·)` along `γ` equals integrating `φ` along
the pushed-forward path `γ.map'`. -/
theorem HasLocalPotentials.localPotentialIntegral_map' {s : Set E} {u : Set G} {a b : G}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hu : IsOpen u) {f : G → E}
    (hf : ContDiffOn ℝ 1 f u) (hfs : MapsTo f u s) {γ : Path a b} (hγ : ∀ t, γ t ∈ u) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ
        (γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))) := by
  let fγ := γ.map' (hf.continuousOn.mono (range_subset_iff.mpr hγ))
  have hfγ : ∀ t, fγ t ∈ s := fun t ↦ hfs (hγ t)
  obtain ⟨S⟩ := hφ.nonempty_potentialSubdivision hfγ
  let V (i : ℕ) : Set G := u ∩ f ⁻¹' S.U i
  have hV (i : ℕ) (hi : i < S.n) : IsOpen (V i) :=
    hf.continuousOn.isOpen_inter_preimage hu (S.isOpen_U i hi)
  have hdV (i : ℕ) (hi : i < S.n) (x : G) (hx : x ∈ V i) :
      HasFDerivAt (S.g i ∘ f) ((φ (f x)).comp (fderiv ℝ f x)) x :=
    (S.hasFDerivAt_g i hi (f x) hx.2).comp x
      ((hf.differentiableOn one_ne_zero x hx.1).differentiableAt (hu.mem_nhds hx.1)).hasFDerivAt
  have hmaps (i : ℕ) (hi : i < S.n) : MapsTo γ (Icc (S.t i) (S.t (i + 1))) (V i) :=
    fun τ hτ ↦ ⟨hγ τ, S.mapsTo_γ i hi hτ⟩
  rw [localPotentialIntegral_eq_sum_sub_of_hasFDerivAt S.t_zero S.mono (S.t_ge S.n le_rfl)
        hV hdV hmaps,
      localPotentialIntegral_eq_eval S]
  unfold PotentialSubdivision.eval
  rfl

/-- Naturality of `localPotentialIntegral` under a globally `C¹` map `f : G → E`. -/
theorem HasLocalPotentials.localPotentialIntegral_map {s : Set E} {a b : G}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {f : G → E} (hf : ContDiff ℝ 1 f)
    {γ : Path a b} (hγ : ∀ t, f (γ t) ∈ s) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ (γ.map hf.continuous) := by
  let u : Set G := f ⁻¹' s
  have hu : IsOpen u := hφ.isOpen.preimage hf.continuous
  have hγu : ∀ t, γ t ∈ u := hγ
  have h := hφ.localPotentialIntegral_map' hu hf.contDiffOn (mapsTo_preimage f s) hγu
  have hmap : γ.map hf.continuous =
      γ.map' (hf.contDiffOn.continuousOn.mono (range_subset_iff.mpr hγu)) := by
    ext; rfl
  rw [hmap, h]

/-! ### Homotopy invariance -/

/-- **Homotopy invariance of `localPotentialIntegral`.** If `H : γ₀.Homotopy γ₁` is a homotopy
relative to endpoints whose image lies in `s`, and `φ` has local potentials on `s`, then
`localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁`. The proof partitions `I × I` into
cells mapped into potential balls and cancels the vertical boundary increments without using
Stokes' theorem or differentiating `H`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_homotopy {s : Set E} {a b : E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) (hH : ∀ p, H p ∈ s) :
    localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁ := by
  choose r hr _ g _ hd using
    fun p : unitInterval × unitInterval ↦ hasLocalPotentials_iff.mp hφ (H p) (hH p)
  have hopen (p : unitInterval × unitInterval) : IsOpen (H ⁻¹' ball (H p) (r p)) :=
    isOpen_ball.preimage H.continuous
  have hcov : (univ : Set (unitInterval × unitInterval)) ⊆ ⋃ p, H ⁻¹' ball (H p) (r p) :=
    fun p _ ↦ mem_iUnion.mpr ⟨p, mem_ball_self (hr p)⟩
  obtain ⟨t, ht0, hmono, ⟨N, htN⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hopen hcov
  choose idx hidx using hcell
  let U (i j : ℕ) : Set E := ball (H (idx i j)) (r (idx i j))
  let G (i j : ℕ) : E → F := g (idx i j)
  -- Each horizontal slice `H.eval (t i)` and `H.eval (t (i + 1))` maps `[t j, t (j + 1)]` into
  -- the same row of balls `U i j`, so their difference telescopes along the vertical edges.
  have hstep (i : ℕ) (hi : i < N) :
      localPotentialIntegral φ (H.eval (t (i + 1))) -
        localPotentialIntegral φ (H.eval (t i)) = 0 := by
    have hti : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
    have hmaps₀ : ∀ j < N, MapsTo (H.eval (t i)) (Icc (t j) (t (j + 1))) (U i j) :=
      fun j _ τ hτ ↦ hidx i j ⟨⟨le_rfl, hti⟩, hτ⟩
    have hmaps₁ : ∀ j < N, MapsTo (H.eval (t (i + 1))) (Icc (t j) (t (j + 1))) (U i j) :=
      fun j _ τ hτ ↦ hidx i j ⟨⟨hti, le_rfl⟩, hτ⟩
    rw [localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono (htN N le_rfl)
          (U := U i) (g := G i) (fun _ _ ↦ isOpen_ball) (fun j _ ↦ hd (idx i j)) hmaps₁,
        localPotentialIntegral_eq_sum_sub_of_hasFDerivAt ht0 hmono (htN N le_rfl)
          (U := U i) (g := G i) (fun _ _ ↦ isOpen_ball) (fun j _ ↦ hd (idx i j)) hmaps₀,
        ← Finset.sum_sub_distrib]
    let δ : ℕ → F := fun k ↦
      if k = 0 then 0 else G i (k - 1) (H (t (i + 1), t k)) - G i (k - 1) (H (t i, t k))
    have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
        (G i j ((H.eval (t (i + 1))) (t (j + 1))) - G i j ((H.eval (t (i + 1))) (t j))) -
          (G i j ((H.eval (t i)) (t (j + 1))) - G i j ((H.eval (t i)) (t j))) =
          δ (j + 1) - δ j := by
      rw [Finset.mem_range] at hj
      have hδ_succ : δ (j + 1) =
          G i j (H (t (i + 1), t (j + 1))) - G i j (H (t i, t (j + 1))) := by simp [δ]
      have hδ_curr : G i j (H (t (i + 1), t j)) - G i j (H (t i, t j)) = δ j := by
        rcases eq_or_ne j 0 with rfl | hj0
        · simp [δ, ht0]
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          simp only [δ, Nat.succ_ne_zero, ↓reduceIte]
          -- Along the vertical edge `σ ↦ H (σ, t (m + 1))`, both `G i (m + 1)` and `G i m`
          -- are primitives of `φ` on `[t i, t (i + 1)]`.
          let vert : Path (H (0, t (m + 1))) (H (1, t (m + 1))) := {
            toFun := fun σ ↦ H (σ, t (m + 1))
            continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
            source' := rfl
            target' := rfl }
          have htm_left : t (m + 1) ∈ Icc (t m) (t (m + 1)) :=
            ⟨hmono (Nat.le_succ m), le_rfl⟩
          have htm_right : t (m + 1) ∈ Icc (t (m + 1)) (t (m + 2)) :=
            ⟨le_rfl, hmono (Nat.le_succ (m + 1))⟩
          exact eq_sub_of_mapsTo_Icc (γ := vert) isOpen_ball isOpen_ball
            (hd (idx i (m + 1))) (hd (idx i m)) hti
            (fun σ hσ ↦ hidx i (m + 1) ⟨hσ, htm_right⟩)
            (fun σ hσ ↦ hidx i m ⟨hσ, htm_left⟩)
      change (G i j (H (t (i + 1), t (j + 1))) - G i j (H (t (i + 1), t j))) -
          (G i j (H (t i, t (j + 1))) - G i j (H (t i, t j))) = δ (j + 1) - δ j
      calc (G i j (H (t (i + 1), t (j + 1))) - G i j (H (t (i + 1), t j))) -
            (G i j (H (t i, t (j + 1))) - G i j (H (t i, t j)))
          = (G i j (H (t (i + 1), t (j + 1))) - G i j (H (t i, t (j + 1)))) -
            (G i j (H (t (i + 1), t j)) - G i j (H (t i, t j))) := by abel
        _ = δ (j + 1) - δ j := by rw [hδ_succ, hδ_curr]
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub δ N]
    have hδ0 : δ 0 = 0 := rfl
    have hδN : δ N = 0 := by
      rcases eq_or_ne N 0 with rfl | hN0
      · rfl
      · simp [δ, hN0, htN N le_rfl]
    simp [hδ0, hδN]
  have htel : localPotentialIntegral φ (H.eval (t N)) -
      localPotentialIntegral φ (H.eval (t 0)) = 0 := by
    rw [← Finset.sum_range_sub (fun i ↦ localPotentialIntegral φ (H.eval (t i))) N]
    exact Finset.sum_eq_zero fun i hi ↦ hstep i (Finset.mem_range.mp hi)
  rw [ht0, H.eval_zero, htN N le_rfl, H.eval_one, sub_eq_zero] at htel
  exact htel.symm

/-- A loop homotopic relative to its basepoint inside `s` to the constant path has zero
`localPotentialIntegral`. -/
theorem HasLocalPotentials.localPotentialIntegral_loop_eq_zero_of_homotopy_refl {s : Set E}
    {a : E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {γ : Path a a}
    (H : γ.Homotopy (Path.refl a)) (hH : ∀ p, H p ∈ s) :
    localPotentialIntegral φ γ = 0 := by
  rw [hφ.localPotentialIntegral_eq_of_homotopy H hH, localPotentialIntegral_refl]

/-! ### Comparison with `curveIntegral` for `C¹` paths -/

/-- When `F` is complete and `γ` is `C¹` on `[0, 1]`, the potential-difference integral
`localPotentialIntegral φ γ` agrees with Mathlib's Bochner curve integral `curveIntegral φ γ`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_curveIntegral [CompleteSpace F] {s : Set E}
    {a b : E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) (hγ' : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) :
    localPotentialIntegral φ γ = curveIntegral φ γ := by
  obtain ⟨S⟩ := hφ.nonempty_potentialSubdivision hγ
  have hci : CurveIntegrable φ γ :=
    hφ.continuousOn.curveIntegrable_of_contDiffOn hγ' hγ
  have hint : ∀ i < S.n,
      IntervalIntegrable (curveIntegralFun φ γ) volume (S.t i : ℝ) (S.t (i + 1) : ℝ) := by
    intro i _
    have hle_coe : (S.t i : ℝ) ≤ (S.t (i + 1) : ℝ) := S.mono (Nat.le_succ i)
    refine hci.mono_set ?_
    rw [uIcc_of_le hle_coe, uIcc_of_le zero_le_one]
    exact fun τ hτ ↦ ⟨(S.t i).2.1.trans hτ.1, hτ.2.trans (S.t (i + 1)).2.2⟩
  rw [localPotentialIntegral_eq_eval S, curveIntegral_def]
  have h0 : ((S.t 0 : unitInterval) : ℝ) = 0 := congrArg Subtype.val S.t_zero
  have hn : ((S.t S.n : unitInterval) : ℝ) = 1 := congrArg Subtype.val (S.t_ge S.n le_rfl)
  rw [← h0, ← hn,
      ← intervalIntegral.sum_integral_adjacent_intervals (a := fun k ↦ (S.t k : ℝ)) hint]
  unfold PotentialSubdivision.eval
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  have hle : (S.t i : ℝ) ≤ (S.t (i + 1) : ℝ) := S.mono (Nat.le_succ i)
  have hmemU : ∀ τ ∈ Icc (S.t i : ℝ) (S.t (i + 1) : ℝ), γ.extend τ ∈ S.U i := by
    intro τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨(S.t i).2.1.trans hτ.1, hτ.2.trans (S.t (i + 1)).2.2⟩
    rw [γ.extend_apply hτI]
    exact S.mapsTo_γ i hi hτ
  have hg_cont : ContinuousOn (S.g i ∘ γ.extend) (Icc (S.t i : ℝ) (S.t (i + 1) : ℝ)) := by
    have hgU : ContinuousOn (S.g i) (S.U i) :=
      fun y hy ↦ (S.hasFDerivAt_g i hi y hy).continuousAt.continuousWithinAt
    exact hgU.comp γ.continuous_extend.continuousOn hmemU
  have hg_deriv : ∀ τ ∈ Ioo (S.t i : ℝ) (S.t (i + 1) : ℝ),
      HasDerivAt (S.g i ∘ γ.extend) (curveIntegralFun φ γ τ) τ := by
    intro τ hτ
    have hτIoo : τ ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (S.t i).2.1 hτ.1, lt_of_lt_of_le hτ.2 (S.t (i + 1)).2.2⟩
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 τ := Icc_mem_nhds hτIoo.1 hτIoo.2
    have hγ_diff : DifferentiableAt ℝ γ.extend τ :=
      (hγ'.differentiableOn one_ne_zero τ ⟨hτIoo.1.le, hτIoo.2.le⟩).differentiableAt hnhds
    have hγ_hasDeriv : HasDerivAt γ.extend (derivWithin γ.extend (Icc 0 1) τ) τ := by
      rw [derivWithin_of_mem_nhds hnhds]
      exact hγ_diff.hasDerivAt
    rw [curveIntegralFun_def]
    exact (S.hasFDerivAt_g i hi (γ.extend τ) (hmemU τ ⟨hτ.1.le, hτ.2.le⟩)).comp_hasDerivAt τ
      hγ_hasDeriv
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hg_cont hg_deriv
    (hint i hi)
  simpa [Function.comp_apply, γ.extend_apply (S.t i).2, γ.extend_apply (S.t (i + 1)).2] using
    hftc.symm

/-! ### Global potentials from vanishing loop integrals on path-connected domains -/

/-- On a path-connected domain `s` where `φ` has local potentials, if every loop based at `x₀ ∈ s`
has zero `localPotentialIntegral`, then integrating `φ` from `x₀` along paths in `s` defines a
global `C¹` potential `g : E → F` on `s` vanishing at `x₀`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_loop_localPotentialIntegral_eq_zero
    {s : Set E} {x₀ : E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ)
    (hs : IsPathConnected s) (hx₀ : x₀ ∈ s)
    (hloop : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0) :
    ∃ g : E → F, g x₀ = 0 ∧ ContDiffOn ℝ 1 g s ∧ (∀ x ∈ s, HasFDerivAt g (φ x) x) ∧
      ∀ x ∈ s, ∀ γ : Path x₀ x, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = g x := by
  classical
  have hpath_indep {x : E} {γ₁ γ₂ : Path x₀ x}
      (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
      localPotentialIntegral φ γ₁ = localPotentialIntegral φ γ₂ := by
    have hγ₂_symm : ∀ t, γ₂.symm t ∈ s := fun t ↦ hγ₂ (unitInterval.symm t)
    have hmem_loop : ∀ t, (γ₁.trans γ₂.symm) t ∈ s := by
      intro t
      rcases Path.trans_range γ₁ γ₂.symm ▸ mem_range_self t with ⟨u, hu⟩ | ⟨v, hv⟩
      · exact hu ▸ hγ₁ u
      · exact hv ▸ hγ₂_symm v
    have h0 := hloop (γ₁.trans γ₂.symm) hmem_loop
    rw [hφ.localPotentialIntegral_trans hγ₁ hγ₂_symm, localPotentialIntegral_symm,
         ← sub_eq_add_neg, sub_eq_zero] at h0
    exact h0
  let g : E → F := fun x ↦
    if hx : x ∈ s then localPotentialIntegral φ (hs.joinedIn x₀ hx₀ x hx).somePath else 0
  have hg_eval {x : E} (hx : x ∈ s) (γ : Path x₀ x) (hγ : ∀ t, γ t ∈ s) :
      localPotentialIntegral φ γ = g x := by
    simp only [g, hx, ↓reduceDIte]
    exact hpath_indep hγ (hs.joinedIn x₀ hx₀ x hx).somePath_mem
  have hgx₀ : g x₀ = 0 := by
    simpa [localPotentialIntegral_refl] using (hg_eval hx₀ (Path.refl x₀) (fun _ ↦ hx₀)).symm
  -- On each ball `ball x r ⊆ s` carrying a local C¹ potential `g₀`, `g` differs from `g₀` by the
  -- constant `g x - g₀ x` via straight-line segments `Path.segment x y`.
  have hlocal {x : E} (hx : x ∈ s) :
      ContDiffAt ℝ 1 g x ∧ HasFDerivAt g (φ x) x := by
    obtain ⟨r, hr, hrs, g₀, hg₀, hd₀⟩ := hasLocalPotentials_iff.mp hφ x hx
    let γx : Path x₀ x := (hs.joinedIn x₀ hx₀ x hx).somePath
    have hγx : ∀ t, γx t ∈ s := (hs.joinedIn x₀ hx₀ x hx).somePath_mem
    have heq : g =ᶠ[𝓝 x] fun y ↦ g₀ y + (g x - g₀ x) := by
      filter_upwards [ball_mem_nhds x hr] with y hy
      have hseg_ball : ∀ t, Path.segment x y t ∈ ball x r := fun t ↦
        (convex_ball x r).segment_subset (mem_ball_self hr) hy
          (segment_eq_image_lineMap ℝ x y ▸ mem_image_of_mem _ t.2)
      have hseg_s : ∀ t, Path.segment x y t ∈ s := fun t ↦ hrs (hseg_ball t)
      have htrans_s : ∀ t, (γx.trans (Path.segment x y)) t ∈ s := by
        intro t
        rcases Path.trans_range γx (Path.segment x y) ▸ mem_range_self t with ⟨u, hu⟩ | ⟨v, hv⟩
        · exact hu ▸ hγx u
        · exact hv ▸ hseg_s v
      have hgy := (hg_eval (hrs hy) (γx.trans (Path.segment x y)) htrans_s).symm
      rw [hφ.localPotentialIntegral_trans hγx hseg_s, hg_eval hx γx hγx,
          localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_ball hd₀ hseg_ball] at hgy
      calc g y = g x + (g₀ y - g₀ x) := hgy
        _ = g₀ y + (g x - g₀ x) := by abel
    exact ⟨((hg₀.contDiffAt (ball_mem_nhds x hr)).add contDiffAt_const).congr_of_eventuallyEq heq,
      ((hd₀ x (mem_ball_self hr)).add_const (g x - g₀ x)).congr_of_eventuallyEq heq⟩
  exact ⟨g, hgx₀, fun x hx ↦ (hlocal hx).1.contDiffWithinAt, fun x hx ↦ (hlocal hx).2,
    fun x hx γ hγ ↦ hg_eval hx γ hγ⟩

/-- On a path-connected domain `s` where `φ` has local potentials, `φ` admits a global primitive on
`s` if and only if every loop in `s` based at `x₀ ∈ s` has zero `localPotentialIntegral`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_localPotentialIntegral_eq_zero
    {s : Set E} {x₀ : E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ)
    (hs : IsPathConnected s) (hx₀ : x₀ ∈ s) :
    (∃ g : E → F, ∀ x ∈ s, HasFDerivAt g (φ x) x) ↔
      ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0 := by
  refine ⟨fun ⟨g, hd⟩ γ hγ ↦ ?_, fun hloop ↦ ?_⟩
  · rw [localPotentialIntegral_eq_sub_of_hasFDerivAt hφ.isOpen hd hγ, sub_self]
  · obtain ⟨g, -, -, hd, -⟩ :=
      hφ.exists_hasFDerivAt_of_forall_loop_localPotentialIntegral_eq_zero hs hx₀ hloop
    exact ⟨g, hd⟩

end TauCeti
