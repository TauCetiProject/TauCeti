/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.Basic
public import TauCeti.Topology.UnitInterval
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.Path.Map
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Path integrals of continuous one-forms with local potentials

Given a covector field `φ : E → E →L[ℝ] F` and a continuous path `γ : Path a b` in a real normed
space `E`, `TauCeti.localPotentialIntegral φ γ` integrates `φ` along `γ` by subdividing `[0, 1]`
into subintervals mapped into open sets carrying primitives of `φ` and summing the endpoint
differences of those primitives. Neither differentiability of `γ` nor completeness of `E` or `F`
is required.

## Main definitions and results

* `TauCeti.localPotentialIntegral`: the continuous path integral of a covector field along a
  continuous path, taking the value `0` when no subdivision into open potential sets exists.
* `TauCeti.localPotentialIntegral_eq_sum_of_partition` and
  `TauCeti.HasLocalPotentials.exists_partition_hasFDerivAt`: any partition into open sets carrying
  primitives computes the integral, and `TauCeti.HasLocalPotentials` supplies such a partition.
* `TauCeti.localPotentialIntegral_of_hasFDerivAt` and `TauCeti.localPotentialIntegral_const`:
  evaluation by a single primitive on an open set, and along constant covector fields.
* Algebraic and path laws: `localPotentialIntegral_refl`, `localPotentialIntegral_cast`,
  `localPotentialIntegral_symm`, `localPotentialIntegral_trans`, `localPotentialIntegral_zero`,
  `localPotentialIntegral_neg`, `localPotentialIntegral_smul`, `localPotentialIntegral_add`,
  `localPotentialIntegral_sub`, `localPotentialIntegral_congr`, and
  `localPotentialIntegral_congr_path`.
* `TauCeti.localPotentialIntegral_map'` and `TauCeti.localPotentialIntegral_map`: naturality under
  pullback along `C¹` maps of open sets.
* `TauCeti.localPotentialIntegral_eq_of_homotopy` and
  `TauCeti.localPotentialIntegral_map_subtype_eq_of_homotopic`: invariance under path homotopy
  relative to endpoints inside the domain of local potentials.
* `TauCeti.localPotentialIntegral_eq_curveIntegral`: agreement with Mathlib's `curveIntegral`
  along `C¹` paths when `F` is complete.
* `TauCeti.HasLocalPotentials.hasFDerivAt_of_eq_localPotentialIntegral` and
  `TauCeti.HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero`: on a path-connected
  domain, vanishing of all based loop integrals is equivalent to the existence of a global `C¹`
  potential, constructed by integrating from a base point.
-/

public section

noncomputable section

open Set Metric Filter Topology AffineMap
open scoped unitInterval ContDiff Interval

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Potential subdivisions and well-definedness -/

/-- A subdivision of `I` into segments mapped by `γ` into open sets carrying primitives of `φ`. -/
private structure PotentialSubdivision (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) where
  n : ℕ
  part : unitInterval.Partition n
  U : Fin n → Set E
  g : Fin n → E → F
  isOpen_U : ∀ i, IsOpen (U i)
  mapsTo_U : ∀ i, MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) (U i)
  hasFDerivAt_g : ∀ i, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y

/-- The sum of endpoint increments of the primitives in a `PotentialSubdivision`. -/
private def PotentialSubdivision.sum {φ : E → E →L[ℝ] F} {a b : E} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : F :=
  ∑ i : Fin S.n, (S.g i (γ (S.part.t i.succ)) - S.g i (γ (S.part.t i.castSucc)))

/-- Two primitives of `φ` on open sets containing `γ '' Icc u v` (`u ≤ v`) have the same endpoint
increment from `u` to `v`. -/
private theorem PotentialSubdivision.sub_eq_of_subset {φ : E → E →L[ℝ] F} {a b : E} {γ : Path a b}
    (S₁ S₂ : PotentialSubdivision φ γ) (i : Fin S₁.n) (j : Fin S₂.n) {u v : I} (huv : u ≤ v)
    (h₁ : Icc u v ⊆ Icc (S₁.part.t i.castSucc) (S₁.part.t i.succ))
    (h₂ : Icc u v ⊆ Icc (S₂.part.t j.castSucc) (S₂.part.t j.succ)) :
    S₁.g i (γ v) - S₁.g i (γ u) = S₂.g j (γ v) - S₂.g j (γ u) := by
  let W : Set E := S₁.U i ∩ S₂.U j
  have hW : IsOpen W := (S₁.isOpen_U i).inter (S₂.isOpen_U j)
  let d : W → F := fun w ↦ S₁.g i w.1 - S₂.g j w.1
  have hd : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp hW w.1 w.2
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (ball_mem_nhds w.1 hr)] with z hz
    have hdiff : ∀ y ∈ ball w.1 r, HasFDerivAt (S₁.g i - S₂.g j) 0 y := fun y hy ↦ by
      simpa only [sub_self] using
        (S₁.hasFDerivAt_g i y (hrb hy).1).sub (S₂.hasFDerivAt_g j y (hrb hy).2)
    exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball w.1 r).isPreconnected
      (fun y hy ↦ (hdiff y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hdiff y hy).fderiv) hz (mem_ball_self hr)
  have hmem (s : I) : Icc.convexComb u v s ∈ Icc u v := by
    constructor <;> simp only [← Subtype.coe_le_coe, Icc.coe_convexComb]
    · nlinarith [s.2.1, s.2.2, Subtype.coe_le_coe.mpr huv]
    · nlinarith [s.2.1, s.2.2, Subtype.coe_le_coe.mpr huv]
  let τ : I → W := fun s ↦ ⟨γ (Icc.convexComb u v s),
    S₁.mapsTo_U i (h₁ (hmem s)), S₂.mapsTo_U j (h₂ (hmem s))⟩
  have hτ : Continuous τ := Continuous.subtype_mk (by fun_prop) _
  have heq := (hd.comp_continuous hτ).apply_eq_of_preconnectedSpace 1 0
  simp only [Function.comp_apply, τ, d, Icc.convexComb_one, Icc.convexComb_zero] at heq
  exact sub_eq_sub_iff_sub_eq_sub.mp heq

/-- Any two potential subdivisions of the same path give the same sum of increments. -/
private theorem PotentialSubdivision.sum_eq {φ : E → E →L[ℝ] F} {a b : E} {γ : Path a b}
    (S₁ S₂ : PotentialSubdivision φ γ) : S₁.sum = S₂.sum := by
  -- Clamp S₂'s partition points into each interval of S₁, and symmetrically.
  let q (i : Fin S₁.n) (j : Fin (S₂.n + 1)) : I :=
    max (S₁.part.t i.castSucc) (min (S₁.part.t i.succ) (S₂.part.t j))
  let p (j : Fin S₂.n) (i : Fin (S₁.n + 1)) : I :=
    max (S₂.part.t j.castSucc) (min (S₂.part.t j.succ) (S₁.part.t i))
  have hS₁ : S₁.sum = ∑ i : Fin S₁.n, ∑ j : Fin S₂.n,
      (S₁.g i (γ (q i j.succ)) - S₁.g i (γ (q i j.castSucc))) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hfirst := Fin.sum_univ_succ fun j : Fin (S₂.n + 1) ↦ S₁.g i (γ (q i j))
    have hlast := Fin.sum_univ_castSucc fun j : Fin (S₂.n + 1) ↦ S₁.g i (γ (q i j))
    have hq0 : q i 0 = S₁.part.t i.castSucc := by
      dsimp [q]; rw [S₂.part.t_zero, min_eq_right unitInterval.nonneg',
        max_eq_left unitInterval.nonneg']
    have hql : q i (Fin.last S₂.n) = S₁.part.t i.succ := by
      dsimp [q]; rw [S₂.part.t_last, min_eq_left unitInterval.le_one',
        max_eq_right (S₁.part.t_castSucc_le_succ i)]
    symm
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add, add_comm _ (S₁.g i _), ← hq0,
      ← hfirst, hlast, hql, add_comm]
  have hS₂ : S₂.sum = ∑ j : Fin S₂.n, ∑ i : Fin S₁.n,
      (S₂.g j (γ (p j i.succ)) - S₂.g j (γ (p j i.castSucc))) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hfirst := Fin.sum_univ_succ fun i : Fin (S₁.n + 1) ↦ S₂.g j (γ (p j i))
    have hlast := Fin.sum_univ_castSucc fun i : Fin (S₁.n + 1) ↦ S₂.g j (γ (p j i))
    have hp0 : p j 0 = S₂.part.t j.castSucc := by
      dsimp [p]; rw [S₁.part.t_zero, min_eq_right unitInterval.nonneg',
        max_eq_left unitInterval.nonneg']
    have hpl : p j (Fin.last S₁.n) = S₂.part.t j.succ := by
      dsimp [p]; rw [S₁.part.t_last, min_eq_left unitInterval.le_one',
        max_eq_right (S₂.part.t_castSucc_le_succ j)]
    symm
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add, add_comm _ (S₂.g j _), ← hp0,
      ← hfirst, hlast, hpl, add_comm]
  -- Disjoint pairs contribute zero on both sides; overlapping pairs agree by `sub_eq_of_subset`.
  rw [hS₁, hS₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := S₁.part.t_castSucc_le_succ i
  have hj := S₂.part.t_castSucc_le_succ j
  rcases le_or_gt (S₂.part.t j.succ) (S₁.part.t i.castSucc) with hle | hgt₁
  · have hq₁ : q i j.succ = S₁.part.t i.castSucc :=
      max_eq_left ((min_le_right _ _).trans hle)
    have hq₀ : q i j.castSucc = S₁.part.t i.castSucc :=
      max_eq_left ((min_le_right _ _).trans (hj.trans hle))
    have hp₁ : p j i.succ = S₂.part.t j.succ := by
      dsimp [p]; rw [min_eq_left (hle.trans hi), max_eq_right hj]
    have hp₀ : p j i.castSucc = S₂.part.t j.succ := by
      dsimp [p]; rw [min_eq_left hle, max_eq_right hj]
    simp [hq₁, hq₀, hp₁, hp₀]
  · rcases le_or_gt (S₁.part.t i.succ) (S₂.part.t j.castSucc) with hle | hgt₂
    · have hq₁ : q i j.succ = S₁.part.t i.succ := by
        dsimp [q]; rw [min_eq_left (hle.trans hj), max_eq_right hi]
      have hq₀ : q i j.castSucc = S₁.part.t i.succ := by
        dsimp [q]; rw [min_eq_left hle, max_eq_right hi]
      have hp₁ : p j i.succ = S₂.part.t j.castSucc :=
        max_eq_left ((min_le_right _ _).trans hle)
      have hp₀ : p j i.castSucc = S₂.part.t j.castSucc :=
        max_eq_left ((min_le_right _ _).trans (hi.trans hle))
      simp [hq₁, hq₀, hp₁, hp₀]
    · have hlo₁ : q i j.castSucc = max (S₁.part.t i.castSucc) (S₂.part.t j.castSucc) := by
        dsimp [q]; rw [min_eq_right hgt₂.le]
      have hlo₂ : p j i.castSucc = max (S₁.part.t i.castSucc) (S₂.part.t j.castSucc) := by
        dsimp [p]; rw [min_eq_right hgt₁.le, max_comm]
      have hhi₁ : q i j.succ = min (S₁.part.t i.succ) (S₂.part.t j.succ) := by
        dsimp [q]; rw [max_eq_right (le_min hi hgt₁.le)]
      have hhi₂ : p j i.succ = min (S₁.part.t i.succ) (S₂.part.t j.succ) := by
        dsimp [p]; rw [max_eq_right (le_min hj hgt₂.le), min_comm]
      rw [hlo₁, hlo₂, hhi₁, hhi₂]
      exact S₁.sub_eq_of_subset S₂ i j
        (max_le (le_min hi hgt₁.le) (le_min hgt₂.le hj))
        (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
        (Icc_subset_Icc (le_max_right _ _) (min_le_right _ _))

/-- The path integral of a covector field `φ` along a continuous path `γ`, defined by summing
endpoint differences of local primitives over a partition of `[0, 1]`. If no partition into open
sets carrying primitives of `φ` exists along `γ`, this takes the default value `0`. -/
noncomputable def localPotentialIntegral (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) : F :=
  open Classical in
  if h : Nonempty (PotentialSubdivision φ γ) then h.some.sum else 0

private theorem PotentialSubdivision.localPotentialIntegral_eq {φ : E → E →L[ℝ] F} {a b : E}
    {γ : Path a b} (S : PotentialSubdivision φ γ) :
    localPotentialIntegral φ γ = S.sum := by
  have hne : Nonempty (PotentialSubdivision φ γ) := ⟨S⟩
  simp only [localPotentialIntegral, hne, ↓reduceDIte]
  exact hne.some.sum_eq S

/-- Any partition of `[0, 1]` whose segments map into open sets carrying primitives of `φ`
computes `localPotentialIntegral φ γ`. -/
theorem localPotentialIntegral_eq_sum_of_partition {φ : E → E →L[ℝ] F} {a b : E} {γ : Path a b}
    {n : ℕ} (part : unitInterval.Partition n) {U : Fin n → Set E} {g : Fin n → E → F}
    (hU : ∀ i, IsOpen (U i))
    (hγ : ∀ i, MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) (U i))
    (hg : ∀ i, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y) :
    localPotentialIntegral φ γ =
      ∑ i : Fin n, (g i (γ (part.t i.succ)) - g i (γ (part.t i.castSucc))) :=
  PotentialSubdivision.localPotentialIntegral_eq ⟨n, part, U, g, hU, hγ, hg⟩

/-- A path inside a domain where `φ` has local potentials admits a partition into open subsets of
the domain carrying `C¹` primitives of `φ`. -/
theorem HasLocalPotentials.exists_partition_hasFDerivAt {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
    ∃ (n : ℕ) (part : unitInterval.Partition n) (U : Fin n → Set E) (g : Fin n → E → F),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ s) ∧
      (∀ i, MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) (U i)) ∧
      (∀ i, ContDiffOn ℝ 1 (g i) (U i)) ∧
      ∀ i, ∀ y ∈ U i, HasFDerivAt (g i) (φ y) y := by
  obtain ⟨n, part, hpart⟩ := γ.exists_partition_with_property
    (fun U ↦ U ⊆ s ∧ ∃ g : E → F, ContDiffOn ℝ 1 g U ∧ ∀ y ∈ U, HasFDerivAt g (φ y) y)
    (by
      rintro z ⟨t, rfl⟩
      obtain ⟨r, hr, hrs, g, hg, hd⟩ := hasLocalPotentials_iff.mp hφ (γ t) (hγ t)
      exact ⟨ball (γ t) r, isOpen_ball, mem_ball_self hr, hrs, g, hg, hd⟩)
  choose U hU hsubg hmaps using hpart
  choose hUs g hg hd using hsubg
  exact ⟨n, part, U, g, hU, hUs, hmaps, hg, hd⟩

private theorem HasLocalPotentials.nonempty_potentialSubdivision {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) {a b : E} {γ : Path a b} (hγ : ∀ t, γ t ∈ s) :
    Nonempty (PotentialSubdivision φ γ) := by
  obtain ⟨n, part, U, g, hU, -, hmaps, -, hd⟩ := hφ.exists_partition_hasFDerivAt γ hγ
  exact ⟨⟨n, part, U, g, hU, hmaps, hd⟩⟩

/-- When `φ` has a single primitive `g` on an open set containing `γ`, the path integral is the
endpoint difference `g b - g a`. -/
theorem localPotentialIntegral_of_hasFDerivAt {s : Set E} {φ : E → E →L[ℝ] F} {g : E → F}
    (hs : IsOpen s) (hg : ∀ x ∈ s, HasFDerivAt g (φ x) x) {a b : E} {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = g b - g a := by
  let part : unitInterval.Partition 1 :=
    { t := ![0, 1]
      mono := fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij ⊢
      t_zero := rfl
      t_last := rfl }
  rw [localPotentialIntegral_eq_sum_of_partition part (U := fun _ ↦ s) (g := fun _ ↦ g)
    (fun _ ↦ hs) (fun _ t _ ↦ hγ t) (fun _ ↦ hg)]
  simp [part]

/-- Along any continuous path from `a` to `b`, the integral of a constant covector `L` is
`L (b - a)`. -/
@[simp]
theorem localPotentialIntegral_const (L : E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (fun _ ↦ L) γ = L (b - a) := by
  rw [localPotentialIntegral_of_hasFDerivAt isOpen_univ (fun _ _ ↦ L.hasFDerivAt)
    (fun _ ↦ mem_univ _), map_sub]

/-! ### Path operations and algebraic laws -/

/-- The integral along the constant path is zero. -/
@[simp]
theorem localPotentialIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    localPotentialIntegral φ (.refl a) = 0 := by
  classical
  by_cases h : Nonempty (PotentialSubdivision φ (.refl a))
  · obtain ⟨S⟩ := h
    rw [S.localPotentialIntegral_eq]
    simp [PotentialSubdivision.sum]
  · simp [localPotentialIntegral, h]

/-- Endpoint casts do not change the path integral. -/
@[simp]
theorem localPotentialIntegral_cast (φ : E → E →L[ℝ] F) {a b c d : E} (γ : Path a b)
    (hc : c = a) (hd : d = b) :
    localPotentialIntegral φ (γ.cast hc hd) = localPotentialIntegral φ γ := by
  subst hc hd
  rfl

private def PotentialSubdivision.symm {φ : E → E →L[ℝ] F} {a b : E} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : PotentialSubdivision φ γ.symm where
  n := S.n
  part :=
    { t := fun k ↦ unitInterval.symm (S.part.t k.rev)
      mono := fun i j hij ↦ by
        have hle := Subtype.coe_le_coe.mpr (S.part.mono (Fin.rev_le_rev.mpr hij))
        exact Subtype.coe_le_coe.mp (by simp only [unitInterval.coe_symm_eq]; linarith)
      t_zero := by simp
      t_last := by simp }
  U := fun i ↦ S.U i.rev
  g := fun i ↦ S.g i.rev
  isOpen_U := fun i ↦ S.isOpen_U i.rev
  mapsTo_U := fun i s hs ↦ by
    rw [Path.symm_apply]
    apply S.mapsTo_U i.rev
    simp only [mem_Icc, ← Subtype.coe_le_coe, unitInterval.coe_symm_eq, Fin.rev_castSucc,
      Fin.rev_succ] at hs ⊢
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  hasFDerivAt_g := fun i ↦ S.hasFDerivAt_g i.rev

/-- Reversing a path negates its integral. -/
@[simp]
theorem localPotentialIntegral_symm (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral φ γ.symm = -localPotentialIntegral φ γ := by
  classical
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    rw [S.localPotentialIntegral_eq, S.symm.localPotentialIntegral_eq]
    simp only [PotentialSubdivision.sum, PotentialSubdivision.symm, Path.symm_apply,
      Fin.rev_succ, Fin.rev_castSucc]
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Fin.revPerm_apply]
  · have h' : ¬ Nonempty (PotentialSubdivision φ γ.symm) := fun ⟨S⟩ ↦
      h ⟨by simpa only [Path.symm_symm] using S.symm⟩
    simp [localPotentialIntegral, h, h']

/-- The zero covector field integrates to zero along every path. -/
@[simp]
theorem localPotentialIntegral_zero {a b : E} (γ : Path a b) :
    localPotentialIntegral (0 : E → E →L[ℝ] F) γ = 0 := by
  simp [Pi.zero_def]

/-- Negating the covector field negates the path integral. -/
@[simp]
theorem localPotentialIntegral_neg (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (-φ) γ = -localPotentialIntegral φ γ := by
  classical
  let negSub {ψ : E → E →L[ℝ] F} (S : PotentialSubdivision ψ γ) :
      PotentialSubdivision (-ψ) γ :=
    { n := S.n
      part := S.part
      U := S.U
      g := fun i ↦ -S.g i
      isOpen_U := S.isOpen_U
      mapsTo_U := S.mapsTo_U
      hasFDerivAt_g := fun i y hy ↦ (S.hasFDerivAt_g i y hy).neg }
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    rw [S.localPotentialIntegral_eq, (negSub S).localPotentialIntegral_eq]
    simp only [PotentialSubdivision.sum, negSub, Pi.neg_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by abel
  · have h' : ¬ Nonempty (PotentialSubdivision (-φ) γ) := fun ⟨S⟩ ↦
      h ⟨by simpa only [neg_neg] using negSub S⟩
    simp [localPotentialIntegral, h, h']

/-- Scaling the covector field by a real scalar scales the path integral. -/
@[simp]
theorem localPotentialIntegral_smul (c : ℝ) (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (c • φ) γ = c • localPotentialIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  classical
  let smulSub (d : ℝ) {ψ : E → E →L[ℝ] F} (S : PotentialSubdivision ψ γ) :
      PotentialSubdivision (d • ψ) γ :=
    { n := S.n
      part := S.part
      U := S.U
      g := fun i ↦ d • S.g i
      isOpen_U := S.isOpen_U
      mapsTo_U := S.mapsTo_U
      hasFDerivAt_g := fun i y hy ↦ (S.hasFDerivAt_g i y hy).const_smul d }
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    rw [S.localPotentialIntegral_eq, (smulSub c S).localPotentialIntegral_eq]
    simp only [PotentialSubdivision.sum, smulSub, Pi.smul_apply, Finset.smul_sum, smul_sub]
  · have h' : ¬ Nonempty (PotentialSubdivision (c • φ) γ) := fun ⟨S⟩ ↦
      h ⟨by simpa only [inv_smul_smul₀ hc] using smulSub c⁻¹ S⟩
    simp [localPotentialIntegral, h, h']

/-- The path integral depends only on the values of the covector field on an open neighborhood of
the path. -/
theorem localPotentialIntegral_congr {s : Set E} {φ ψ : E → E →L[ℝ] F} (hs : IsOpen s)
    {a b : E} {γ : Path a b} (hγ : ∀ t, γ t ∈ s) (h : EqOn φ ψ s) :
    localPotentialIntegral φ γ = localPotentialIntegral ψ γ := by
  classical
  let restrict {ω₁ ω₂ : E → E →L[ℝ] F} (heq : EqOn ω₁ ω₂ s) (S : PotentialSubdivision ω₁ γ) :
      PotentialSubdivision ω₂ γ :=
    { n := S.n
      part := S.part
      U := fun i ↦ S.U i ∩ s
      g := S.g
      isOpen_U := fun i ↦ (S.isOpen_U i).inter hs
      mapsTo_U := fun i t ht ↦ ⟨S.mapsTo_U i ht, hγ t⟩
      hasFDerivAt_g := fun i y hy ↦ heq hy.2 ▸ S.hasFDerivAt_g i y hy.1 }
  by_cases hne : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := hne
    rw [S.localPotentialIntegral_eq, (restrict h S).localPotentialIntegral_eq]
    rfl
  · have hne' : ¬ Nonempty (PotentialSubdivision ψ γ) := fun ⟨S⟩ ↦ hne ⟨restrict h.symm S⟩
    simp [localPotentialIntegral, hne, hne']

/-- Paths that agree pointwise have the same continuous path integral, regardless of how their
endpoints are written. -/
theorem localPotentialIntegral_congr_path (φ : E → E →L[ℝ] F) {a b a' b' : E}
    {γ₁ : Path a b} {γ₂ : Path a' b'} (h : ∀ t, γ₁ t = γ₂ t) :
    localPotentialIntegral φ γ₁ = localPotentialIntegral φ γ₂ := by
  have ha : a = a' := γ₁.source.symm.trans ((h 0).trans γ₂.source)
  have hb : b = b' := γ₁.target.symm.trans ((h 1).trans γ₂.target)
  subst ha hb
  obtain rfl : γ₁ = γ₂ := Path.ext (funext h)
  rfl

/-- Additivity of the path integral in the covector field. -/
theorem localPotentialIntegral_add {s : Set E} {φ ψ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ) {a b : E} {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ + ψ) γ =
      localPotentialIntegral φ γ + localPotentialIntegral ψ γ := by
  obtain ⟨n, part, hpart⟩ := γ.exists_partition_with_property
    (fun U ↦ ∃ (g₁ g₂ : E → F), (∀ y ∈ U, HasFDerivAt g₁ (φ y) y) ∧
      ∀ y ∈ U, HasFDerivAt g₂ (ψ y) y)
    (by
      rintro z ⟨t, rfl⟩
      obtain ⟨r₁, hr₁, -, g₁, -, hd₁⟩ := hasLocalPotentials_iff.mp hφ (γ t) (hγ t)
      obtain ⟨r₂, hr₂, -, g₂, -, hd₂⟩ := hasLocalPotentials_iff.mp hψ (γ t) (hγ t)
      exact ⟨ball (γ t) (min r₁ r₂), isOpen_ball, mem_ball_self (lt_min hr₁ hr₂), g₁, g₂,
        fun y hy ↦ hd₁ y (ball_subset_ball (min_le_left _ _) hy),
        fun y hy ↦ hd₂ y (ball_subset_ball (min_le_right _ _) hy)⟩)
  choose U hU hg hmaps using hpart
  choose g₁ g₂ hd₁ hd₂ using hg
  rw [localPotentialIntegral_eq_sum_of_partition (φ := φ + ψ) part hU hmaps
      (g := fun i ↦ g₁ i + g₂ i) (fun i y hy ↦ (hd₁ i y hy).add (hd₂ i y hy)),
    localPotentialIntegral_eq_sum_of_partition part hU hmaps hd₁,
    localPotentialIntegral_eq_sum_of_partition part hU hmaps hd₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.add_apply]; abel

/-- Subtraction of locally potential covector fields subtracts their path integrals. -/
theorem localPotentialIntegral_sub {s : Set E} {φ ψ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ) {a b : E} {γ : Path a b}
    (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ - ψ) γ =
      localPotentialIntegral φ γ - localPotentialIntegral ψ γ := by
  rw [sub_eq_add_neg, localPotentialIntegral_add hφ hψ.neg hγ, localPotentialIntegral_neg,
    sub_eq_add_neg]

/-- Concatenate the partition points of two unit-interval partitions onto `[0, 1/2]` and
`[1/2, 1]`. -/
private def transPartition {n₁ n₂ : ℕ} (p₁ : unitInterval.Partition n₁)
    (p₂ : unitInterval.Partition n₂) : unitInterval.Partition (n₁ + n₂) where
  t k :=
    if hk : (k : ℕ) ≤ n₁ then
      ⟨(p₁.t ⟨k, Nat.lt_succ_of_le hk⟩ : ℝ) / 2,
        div_nonneg (p₁.t ⟨k, Nat.lt_succ_of_le hk⟩).2.1 zero_le_two,
        by linarith [(p₁.t ⟨k, Nat.lt_succ_of_le hk⟩).2.2]⟩
    else
      ⟨((p₂.t ⟨k - n₁, by omega⟩ : ℝ) + 1) / 2,
        div_nonneg (by linarith [(p₂.t ⟨k - n₁, by omega⟩).2.1]) zero_le_two,
        by linarith [(p₂.t ⟨k - n₁, by omega⟩).2.2]⟩
  mono i j hij := by
    rw [← Subtype.coe_le_coe]
    by_cases hi : (i : ℕ) ≤ n₁ <;> by_cases hj : (j : ℕ) ≤ n₁
    · simp only [hi, hj, ↓reduceDIte]
      have hidx : (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (n₁ + 1)) ≤ ⟨j, Nat.lt_succ_of_le hj⟩ :=
        Fin.mk_le_mk.mpr hij
      linarith [Subtype.coe_le_coe.mpr (p₁.mono hidx)]
    · simp only [hi, hj, ↓reduceDIte]
      linarith [(p₁.t ⟨i, Nat.lt_succ_of_le hi⟩).2.2, (p₂.t ⟨j - n₁, by omega⟩).2.1]
    · omega
    · simp only [hi, hj, ↓reduceDIte]
      have hidx : (⟨(i : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1)) ≤ ⟨(j : ℕ) - n₁, by omega⟩ :=
        Fin.mk_le_mk.mpr (Nat.sub_le_sub_right hij n₁)
      linarith [Subtype.coe_le_coe.mpr (p₂.mono hidx)]
  t_zero := Subtype.ext (by simp)
  t_last := by
    rcases eq_or_ne n₂ 0 with rfl | hn₂
    · exact isEmptyElim p₂
    · refine Subtype.ext ?_
      have hnle : ¬ n₁ + n₂ ≤ n₁ := by omega
      have hidx : (⟨n₁ + n₂ - n₁, by omega⟩ : Fin (n₂ + 1)) = Fin.last n₂ :=
        Fin.ext (by simp [Fin.val_last])
      simp only [Fin.val_last, hnle, ↓reduceDIte, hidx, p₂.t_last, Set.Icc.coe_one]
      norm_num

private theorem coe_transPartition_left {n₁ n₂ : ℕ} (p₁ : unitInterval.Partition n₁)
    (p₂ : unitInterval.Partition n₂) (k : Fin (n₁ + 1)) :
    ((transPartition p₁ p₂).t ⟨k, by omega⟩ : ℝ) = (p₁.t k : ℝ) / 2 := by
  simp [transPartition, Nat.le_of_lt_succ k.isLt]

private theorem coe_transPartition_right {n₁ n₂ : ℕ} (p₁ : unitInterval.Partition n₁)
    (p₂ : unitInterval.Partition n₂) (k : Fin (n₂ + 1)) :
    ((transPartition p₁ p₂).t ⟨n₁ + k, by omega⟩ : ℝ) = ((p₂.t k : ℝ) + 1) / 2 := by
  rcases eq_or_ne (k : ℕ) 0 with hk0 | hk0
  · have hk : k = 0 := Fin.ext hk0
    subst hk
    have hidx : (⟨n₁, Nat.lt_succ_self n₁⟩ : Fin (n₁ + 1)) = Fin.last n₁ := rfl
    simp [transPartition, hidx]
  · have hnle : ¬ n₁ + (k : ℕ) ≤ n₁ := by omega
    simp [transPartition, hnle]

/-- Concatenate two potential subdivisions across `[0, 1/2]` and `[1/2, 1]`. -/
private def PotentialSubdivision.trans {φ : E → E →L[ℝ] F} {a b c : E}
    {γ₁ : Path a b} {γ₂ : Path b c} (S₁ : PotentialSubdivision φ γ₁)
    (S₂ : PotentialSubdivision φ γ₂) : PotentialSubdivision φ (γ₁.trans γ₂) where
  n := S₁.n + S₂.n
  part := transPartition S₁.part S₂.part
  U := Fin.addCases S₁.U S₂.U
  g := Fin.addCases S₁.g S₂.g
  isOpen_U := Fin.addCases (fun i ↦ by simpa using S₁.isOpen_U i)
    (fun j ↦ by simpa using S₂.isOpen_U j)
  mapsTo_U := by
    refine Fin.addCases (fun i u hu ↦ ?_) (fun j u hu ↦ ?_)
    · have hu0 := coe_transPartition_left S₁.part S₂.part i.castSucc ▸ Subtype.coe_le_coe.mpr hu.1
      have hu1 := coe_transPartition_left S₁.part S₂.part i.succ ▸ Subtype.coe_le_coe.mpr hu.2
      let v : I := ⟨2 * (u : ℝ), by linarith [(S₁.part.t i.castSucc).2.1],
        by linarith [(S₁.part.t i.succ).2.2]⟩
      have hv : v ∈ Icc (S₁.part.t i.castSucc) (S₁.part.t i.succ) :=
        ⟨Subtype.coe_le_coe.mp (by dsimp [v]; linarith),
          Subtype.coe_le_coe.mp (by dsimp [v]; linarith)⟩
      simpa only [Fin.addCases_left, γ₁.trans_apply_of_eq_two_mul γ₂ v rfl] using S₁.mapsTo_U i hv
    · have hu0 := coe_transPartition_right S₁.part S₂.part j.castSucc ▸ Subtype.coe_le_coe.mpr hu.1
      have hu1 := coe_transPartition_right S₁.part S₂.part j.succ ▸ Subtype.coe_le_coe.mpr hu.2
      let v : I := ⟨2 * (u : ℝ) - 1, by linarith [(S₂.part.t j.castSucc).2.1],
        by linarith [(S₂.part.t j.succ).2.2]⟩
      have hv : v ∈ Icc (S₂.part.t j.castSucc) (S₂.part.t j.succ) :=
        ⟨Subtype.coe_le_coe.mp (by dsimp [v]; linarith),
          Subtype.coe_le_coe.mp (by dsimp [v]; linarith)⟩
      simpa only [Fin.addCases_right, γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ v rfl] using
        S₂.mapsTo_U j hv
  hasFDerivAt_g := Fin.addCases (fun i ↦ by simpa using S₁.hasFDerivAt_g i)
    (fun j ↦ by simpa using S₂.hasFDerivAt_g j)

/-- Concatenating two paths in a domain of local potentials adds their path integrals. -/
theorem localPotentialIntegral_trans {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) {a b c : E} {γ₁ : Path a b} {γ₂ : Path b c}
    (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ (γ₁.trans γ₂) =
      localPotentialIntegral φ γ₁ + localPotentialIntegral φ γ₂ := by
  obtain ⟨S₁⟩ := hφ.nonempty_potentialSubdivision hγ₁
  obtain ⟨S₂⟩ := hφ.nonempty_potentialSubdivision hγ₂
  rw [(S₁.trans S₂).localPotentialIntegral_eq, S₁.localPotentialIntegral_eq,
    S₂.localPotentialIntegral_eq]
  dsimp only [PotentialSubdivision.sum, PotentialSubdivision.trans]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hidx0 : (Fin.castAdd S₂.n i).castSucc = ⟨i.castSucc, by omega⟩ := Fin.ext (by simp)
    have hidx1 : (Fin.castAdd S₂.n i).succ = ⟨i.succ, by omega⟩ := Fin.ext (by simp)
    have heq0 : (γ₁.trans γ₂) ((transPartition S₁.part S₂.part).t (Fin.castAdd S₂.n i).castSucc) =
        γ₁ (S₁.part.t i.castSucc) :=
      γ₁.trans_apply_of_eq_two_mul γ₂ (S₁.part.t i.castSucc)
        (by rw [hidx0, coe_transPartition_left]; ring)
    have heq1 : (γ₁.trans γ₂) ((transPartition S₁.part S₂.part).t (Fin.castAdd S₂.n i).succ) =
        γ₁ (S₁.part.t i.succ) :=
      γ₁.trans_apply_of_eq_two_mul γ₂ (S₁.part.t i.succ)
        (by rw [hidx1, coe_transPartition_left]; ring)
    simp only [Fin.addCases_left, heq0, heq1]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hidx0 : (Fin.natAdd S₁.n j).castSucc = ⟨S₁.n + j.castSucc, by omega⟩ := Fin.ext (by simp)
    have hidx1 : (Fin.natAdd S₁.n j).succ = ⟨S₁.n + j.succ, by omega⟩ :=
      Fin.ext (by simp [Nat.add_assoc])
    have heq0 : (γ₁.trans γ₂) ((transPartition S₁.part S₂.part).t (Fin.natAdd S₁.n j).castSucc) =
        γ₂ (S₂.part.t j.castSucc) :=
      γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ (S₂.part.t j.castSucc)
        (by rw [hidx0, coe_transPartition_right]; ring)
    have heq1 : (γ₁.trans γ₂) ((transPartition S₁.part S₂.part).t (Fin.natAdd S₁.n j).succ) =
        γ₂ (S₂.part.t j.succ) :=
      γ₁.trans_apply_of_eq_two_mul_sub_one γ₂ (S₂.part.t j.succ)
        (by rw [hidx1, coe_transPartition_right]; ring)
    simp only [Fin.addCases_right, heq0, heq1]

/-! ### Pullback along `C¹` maps -/

/-- Naturality of the continuous path integral under pullback along a map `f` that is `C¹` on an
open neighborhood of the path: integrating `φ` along `γ.map' hcont` equals integrating the
pulled-back covector field `x ↦ (φ (f x)).comp (fderiv ℝ f x)` along `γ`. -/
theorem localPotentialIntegral_map' {u : Set G} {s : Set E} {f : G → E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u)
    (hfs : MapsTo f u s) {a b : G} {γ : Path a b} (hγ : ∀ t, γ t ∈ u)
    (hcont : ContinuousOn f (range γ)) :
    localPotentialIntegral φ (γ.map' hcont) =
      localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ := by
  have hmem : ∀ t, (γ.map' hcont) t ∈ s := fun t ↦ hfs (hγ t)
  obtain ⟨S⟩ := hφ.nonempty_potentialSubdivision hmem
  have hU' (i : Fin S.n) : IsOpen (u ∩ f ⁻¹' S.U i) :=
    hf.continuousOn.isOpen_inter_preimage hu (S.isOpen_U i)
  have hmaps' (i : Fin S.n) :
      MapsTo γ (Icc (S.part.t i.castSucc) (S.part.t i.succ)) (u ∩ f ⁻¹' S.U i) :=
    fun t ht ↦ ⟨hγ t, S.mapsTo_U i ht⟩
  have hd' (i : Fin S.n) (x : G) (hx : x ∈ u ∩ f ⁻¹' S.U i) :
      HasFDerivAt (S.g i ∘ f) ((φ (f x)).comp (fderiv ℝ f x)) x :=
    (S.hasFDerivAt_g i (f x) hx.2).comp x
      ((hf.differentiableOn one_ne_zero x hx.1).differentiableAt (hu.mem_nhds hx.1)).hasFDerivAt
  rw [S.localPotentialIntegral_eq, localPotentialIntegral_eq_sum_of_partition S.part hU' hmaps' hd']
  rfl

/-- Naturality of the continuous path integral under a globally continuous map that is `C¹` on an
open neighborhood of the path. -/
theorem localPotentialIntegral_map {u : Set G} {s : Set E} {f : G → E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u)
    (hfs : MapsTo f u s) (hfc : Continuous f) {a b : G} {γ : Path a b} (hγ : ∀ t, γ t ∈ u) :
    localPotentialIntegral φ (γ.map hfc) =
      localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ :=
  localPotentialIntegral_map' hφ hu hf hfs hγ hfc.continuousOn

/-! ### Homotopy invariance -/

/-- **Homotopy invariance of the continuous path integral.** If `H` is a path homotopy (fixing
endpoints) from `γ₀` to `γ₁` whose image lies in `s`, and `φ` has local potentials on `s`, then
`localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁`. -/
theorem localPotentialIntegral_eq_of_homotopy {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) {a b : E} {γ₀ γ₁ : Path a b} (H : γ₀.Homotopy γ₁)
    (hH : ∀ t u, H (t, u) ∈ s) :
    localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁ := by
  -- Cover `I × I` by preimages of potential balls and extract a Lebesgue number `δ > 0`.
  choose r hr _ g _ hdg using fun q : I × I ↦ hasLocalPotentials_iff.mp hφ (H q) (hH q.1 q.2)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (c := fun q : I × I ↦ H ⁻¹' ball (H q) (r q))
    (fun q ↦ isOpen_ball.preimage H.continuous)
    (fun q _ ↦ mem_iUnion.2 ⟨q, mem_ball_self (hr q)⟩)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  let M : ℕ := N + 1
  have hMpos : (0 : ℝ) < M := by positivity
  let part : unitInterval.Partition M :=
    { t := fun k ↦ ⟨(k : ℝ) / M, div_nonneg (Nat.cast_nonneg _) hMpos.le,
        (div_le_one hMpos).2 (by exact_mod_cast Fin.is_le k)⟩
      mono := fun i j hij ↦ Subtype.coe_le_coe.mp (div_le_div_of_nonneg_right
        (by exact_mod_cast hij) hMpos.le)
      t_zero := Subtype.ext (by simp)
      t_last := Subtype.ext (by simp) }
  -- Each cell `[t_i, t_{i+1}] × [t_j, t_{j+1}]` has diameter `< δ` from its corner, so maps into
  -- one potential ball `B i j` with primitive `G i j`.
  have hcell (i j : Fin M) : ∃ q₀ : I × I,
      ∀ t ∈ Icc (part.t i.castSucc) (part.t i.succ),
      ∀ u ∈ Icc (part.t j.castSucc) (part.t j.succ), H (t, u) ∈ ball (H q₀) (r q₀) := by
    obtain ⟨q₀, hq₀⟩ := hleb (part.t i.castSucc, part.t j.castSucc) (mem_univ _)
    refine ⟨q₀, fun t ht u hu ↦ hq₀ ?_⟩
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    have hstep (k : Fin M) (x : I) (hx : x ∈ Icc (part.t k.castSucc) (part.t k.succ)) :
        dist x (part.t k.castSucc) < δ := by
      have hx0 : (part.t k.castSucc : ℝ) ≤ x := Subtype.coe_le_coe.mpr hx.1
      have hcast : (part.t k.castSucc : ℝ) = (k : ℝ) / M := rfl
      have hx1 : (x : ℝ) ≤ ((k : ℝ) + 1) / M := by
        simpa [part, Nat.cast_add, Nat.cast_one] using Subtype.coe_le_coe.mpr hx.2
      have hdiff : ((k : ℝ) + 1) / M - (k : ℝ) / M = 1 / (N + 1 : ℝ) := by
        dsimp [M]; push_cast; ring
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx0), hcast]
      exact (sub_le_sub_right hx1 _).trans_lt (hdiff.trans_lt hN)
    exact ⟨hstep i t ht, hstep j u hu⟩
  choose q₀ hq₀ using hcell
  -- Vertical rung path across row strip `i` at column `k`.
  let rung (i : Fin M) (k : Fin (M + 1)) :
      Path (H (part.t i.castSucc, part.t k)) (H (part.t i.succ, part.t k)) :=
    { toFun := fun v ↦ H (Icc.convexComb (part.t i.castSucc) (part.t i.succ) v, part.t k)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hrung_mem (i : Fin M) (v : I) :
      Icc.convexComb (part.t i.castSucc) (part.t i.succ) v ∈
        Icc (part.t i.castSucc) (part.t i.succ) := by
    have hi := Subtype.coe_le_coe.mpr (part.t_castSucc_le_succ i)
    exact ⟨Subtype.coe_le_coe.mp (by rw [Icc.coe_convexComb]; nlinarith [v.2.1, v.2.2]),
      Subtype.coe_le_coe.mp (by rw [Icc.coe_convexComb]; nlinarith [v.2.1, v.2.2])⟩
  -- Telescope vertical rung increments across row `i`; the boundary rungs at `0` and `M` vanish.
  have hrow_step (i : Fin M) :
      localPotentialIntegral φ (H.eval (part.t i.succ)) =
        localPotentialIntegral φ (H.eval (part.t i.castSucc)) := by
    rw [localPotentialIntegral_eq_sum_of_partition part (fun j ↦ isOpen_ball)
        (fun j u hu ↦ hq₀ i j (part.t i.succ) ⟨part.t_castSucc_le_succ i, le_rfl⟩ u hu)
        (fun j ↦ hdg (q₀ i j)),
      localPotentialIntegral_eq_sum_of_partition part (fun j ↦ isOpen_ball)
        (fun j u hu ↦ hq₀ i j (part.t i.castSucc) ⟨le_rfl, part.t_castSucc_le_succ i⟩ u hu)
        (fun j ↦ hdg (q₀ i j)), ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have heval (t u : I) : H.eval t u = H (t, u) := by simp
    simp only [heval]
    have hcell_eq (j : Fin M) :
        (g (q₀ i j) (H (part.t i.succ, part.t j.succ)) -
          g (q₀ i j) (H (part.t i.succ, part.t j.castSucc))) -
        (g (q₀ i j) (H (part.t i.castSucc, part.t j.succ)) -
          g (q₀ i j) (H (part.t i.castSucc, part.t j.castSucc))) =
        localPotentialIntegral φ (rung i j.succ) -
          localPotentialIntegral φ (rung i j.castSucc) := by
      rw [localPotentialIntegral_of_hasFDerivAt isOpen_ball (hdg (q₀ i j))
          (fun v ↦ hq₀ i j _ (hrung_mem i v) _ ⟨part.t_castSucc_le_succ j, le_rfl⟩),
        localPotentialIntegral_of_hasFDerivAt isOpen_ball (hdg (q₀ i j))
          (fun v ↦ hq₀ i j _ (hrung_mem i v) _ ⟨le_rfl, part.t_castSucc_le_succ j⟩)]
      abel
    rw [Finset.sum_congr rfl fun j _ ↦ hcell_eq j]
    have hfirst := Fin.sum_univ_succ fun k : Fin (M + 1) ↦ localPotentialIntegral φ (rung i k)
    have hlast := Fin.sum_univ_castSucc fun k : Fin (M + 1) ↦ localPotentialIntegral φ (rung i k)
    have hr0 : localPotentialIntegral φ (rung i 0) = 0 := by
      have hcast : rung i 0 = (Path.refl a).cast (by simp) (by simp) := by
        ext v; simp [rung]
      rw [hcast, localPotentialIntegral_cast, localPotentialIntegral_refl]
    have hrl : localPotentialIntegral φ (rung i (Fin.last M)) = 0 := by
      have hcast : rung i (Fin.last M) = (Path.refl b).cast (by simp) (by simp) := by
        ext v; simp [rung]
      rw [hcast, localPotentialIntegral_cast, localPotentialIntegral_refl]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    have hsum : (∑ x : Fin M, localPotentialIntegral φ (rung i x.succ)) +
        localPotentialIntegral φ (rung i 0) =
        localPotentialIntegral φ (rung i (Fin.last M)) +
          ∑ x : Fin M, localPotentialIntegral φ (rung i x.castSucc) := by
      rw [add_comm _ (localPotentialIntegral φ (rung i 0)), ← hfirst, hlast, add_comm]
    simpa only [hr0, hrl, add_zero, zero_add] using hsum
  have hchain (k : Fin (M + 1)) :
      localPotentialIntegral φ (H.eval (part.t k)) =
        localPotentialIntegral φ (H.eval (part.t 0)) := by
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hrow_step i).trans ih
  have h := hchain (Fin.last M)
  simpa using h.symm

/-- Two paths in the subtype `↥s` that are homotopic relative to their endpoints have equal path
integrals in the ambient space `E`. -/
theorem localPotentialIntegral_map_subtype_eq_of_homotopic {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) {a b : s} {γ₀ γ₁ : Path a b} (h : γ₀.Homotopic γ₁) :
    localPotentialIntegral φ (γ₀.map continuous_subtype_val) =
      localPotentialIntegral φ (γ₁.map continuous_subtype_val) := by
  obtain ⟨H⟩ := h
  exact localPotentialIntegral_eq_of_homotopy hφ
    (H.map ⟨Subtype.val, continuous_subtype_val⟩) fun t u ↦ (H (t, u)).2

/-! ### Comparison with `curveIntegral` -/

/-- When the target space `F` is complete and `γ` is a `C¹` path in `s`, the continuous path
integral agrees with Mathlib's Bochner `curveIntegral`. -/
theorem localPotentialIntegral_eq_curveIntegral [CompleteSpace F] {s : Set E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {a b : E} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = ∫ᶜ x in γ, φ x := by
  -- Split `∫₀¹` across the subintervals of a potential partition for `γ`.
  obtain ⟨n, part, U, g, hU, -, hmaps, -, hdg⟩ := hφ.exists_partition_hasFDerivAt γ hγs
  rw [localPotentialIntegral_eq_sum_of_partition part hU hmaps hdg, curveIntegral_def]
  have hint : IntervalIntegrable (curveIntegralFun φ γ) MeasureTheory.volume 0 1 :=
    hφ.continuousOn.curveIntegrable_of_contDiffOn hγ hγs
  let pts : ℕ → ℝ := fun k ↦ if hk : k < n + 1 then (part.t ⟨k, hk⟩ : ℝ) else 1
  have hpts_mem (k : ℕ) : pts k ∈ Icc (0 : ℝ) 1 := by
    dsimp only [pts]
    split_ifs with hk
    · exact (part.t ⟨k, hk⟩).2
    · exact ⟨zero_le_one, le_rfl⟩
  have hpts0 : pts 0 = 0 := by simp [pts]
  have hptsn : pts n = 1 := by
    have : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
    simp [pts, this]
  have hint_sub (k : ℕ) (_ : k < n) :
      IntervalIntegrable (curveIntegralFun φ γ) MeasureTheory.volume (pts k) (pts (k + 1)) := by
    refine hint.mono_set ?_
    rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc (hpts_mem k) (hpts_mem (k + 1))
  rw [← hpts0, ← hptsn, ← intervalIntegral.sum_integral_adjacent_intervals hint_sub,
    ← Fin.sum_univ_eq_sum_range]
  -- Apply the fundamental theorem of calculus to `g i ∘ γ.extend` on each subinterval.
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hk0 : pts i = (part.t i.castSucc : ℝ) := by
    simp only [pts, Nat.lt_succ_of_lt i.isLt, ↓reduceDIte]; rfl
  have hk1 : pts (i + 1) = (part.t i.succ : ℝ) := by
    simp only [pts, Nat.succ_lt_succ i.isLt, ↓reduceDIte]; rfl
  rw [hk0, hk1]
  have hle : (part.t i.castSucc : ℝ) ≤ (part.t i.succ : ℝ) :=
    Subtype.coe_le_coe.mpr (part.t_castSucc_le_succ i)
  have hmemU {t : ℝ} (ht : t ∈ Icc (part.t i.castSucc : ℝ) (part.t i.succ : ℝ)) :
      γ.extend t ∈ U i := by
    have htI : t ∈ I := ⟨(part.t i.castSucc).2.1.trans ht.1, ht.2.trans (part.t i.succ).2.2⟩
    rw [γ.extend_apply htI]
    exact hmaps i ⟨Subtype.coe_le_coe.mp ht.1, Subtype.coe_le_coe.mp ht.2⟩
  have hcont : ContinuousOn (fun t ↦ g i (γ.extend t))
      (Icc (part.t i.castSucc : ℝ) (part.t i.succ : ℝ)) := fun t ht ↦
    ((hdg i _ (hmemU ht)).continuousAt.comp_continuousWithinAt
      γ.continuous_extend.continuousWithinAt)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (part.t i.castSucc : ℝ) (part.t i.succ : ℝ)) :
      HasDerivAt (fun τ ↦ g i (γ.extend τ)) (curveIntegralFun φ γ t) t := by
    have htIoo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨(part.t i.castSucc).2.1.trans_lt ht.1, ht.2.trans_le (part.t i.succ).2.2⟩
    have hnhds : I ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
    have hdγ : HasDerivAt γ.extend (derivWithin γ.extend I t) t := by
      rw [derivWithin_of_mem_nhds hnhds]
      exact ((hγ.differentiableOn one_ne_zero t (Ioo_subset_Icc_self htIoo)).differentiableAt
        hnhds).hasDerivAt
    rw [curveIntegralFun_def]
    exact (hdg i _ (hmemU (Ioo_subset_Icc_self ht))).comp_hasDerivAt t hdγ
  have hint_i : IntervalIntegrable (curveIntegralFun φ γ) MeasureTheory.volume
      (part.t i.castSucc : ℝ) (part.t i.succ : ℝ) := by
    rw [← hk0, ← hk1]
    exact hint_sub i i.isLt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint_i,
    γ.extend_apply (part.t i.succ).2, γ.extend_apply (part.t i.castSucc).2]

/-- Along a straight line segment in `s`, the continuous path integral agrees with `curveIntegral`
when `F` is complete. -/
theorem localPotentialIntegral_segment_eq_curveIntegral [CompleteSpace F] {s : Set E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) {a b : E} (hs : segment ℝ a b ⊆ s) :
    localPotentialIntegral φ (.segment a b) = ∫ᶜ x in .segment a b, φ x := by
  refine localPotentialIntegral_eq_curveIntegral hφ ?_ fun t ↦ hs (lineMap_mem_segment ℝ a b t.2)
  exact ((contDiff_id.smul contDiff_const).add contDiff_const).contDiffOn.congr fun t ht ↦
    (Path.eqOn_extend_segment a b ht).trans (lineMap_apply_module' a b t)

/-! ### Vanishing loop integrals and global potentials -/

private theorem trans_mem {X : Type*} [TopologicalSpace X] {s : Set X} {a b c : X}
    {γ₁ : Path a b} {γ₂ : Path b c} (h₁ : ∀ t, γ₁ t ∈ s) (h₂ : ∀ t, γ₂ t ∈ s) (t : I) :
    (γ₁.trans γ₂) t ∈ s := by
  rcases Path.trans_range γ₁ γ₂ ▸ mem_range_self t with ⟨u, hu⟩ | ⟨u, hu⟩
  exacts [hu ▸ h₁ u, hu ▸ h₂ u]

/-- If every based loop at `x₀ ∈ s` has vanishing path integral on a path-connected domain `s`,
then the path integral between any two points of `s` is independent of the path in `s`. -/
theorem localPotentialIntegral_eq_of_forall_loop_eq_zero {s : Set E} {φ : E → E →L[ℝ] F}
    (hφ : HasLocalPotentials s φ) (hs : IsPathConnected s) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hloop : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0)
    {a b : E} {γ₁ γ₂ : Path a b} (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ γ₁ = localPotentialIntegral φ γ₂ := by
  have ha : a ∈ s := γ₁.source ▸ hγ₁ 0
  obtain ⟨α, hα⟩ := hs.joinedIn x₀ hx₀ a ha
  have hm₁ : ∀ t, (α.trans γ₁) t ∈ s := trans_mem hα hγ₁
  have hm₂ : ∀ t, (α.trans γ₂).symm t ∈ s := fun t ↦ trans_mem hα hγ₂ (σ t)
  let ℓ : Path x₀ x₀ := (α.trans γ₁).trans (α.trans γ₂).symm
  have hℓ : ∀ t, ℓ t ∈ s := trans_mem hm₁ hm₂
  have hz := hloop ℓ hℓ
  rw [localPotentialIntegral_trans hφ hm₁ hm₂, localPotentialIntegral_symm,
    localPotentialIntegral_trans hφ hα hγ₁, localPotentialIntegral_trans hφ hα hγ₂] at hz
  exact eq_of_sub_eq_zero (by
    have hsub : localPotentialIntegral φ γ₁ - localPotentialIntegral φ γ₂ =
        (localPotentialIntegral φ α + localPotentialIntegral φ γ₁) +
          -(localPotentialIntegral φ α + localPotentialIntegral φ γ₂) := by abel
    exact hsub.trans hz)

/-- On a path-connected domain where every based loop at `x₀` integrates to zero, any function `g`
whose value at each `y ∈ s` is the path integral of `φ` from `x₀` to `y` along a path in `s` is a
global `C¹` potential of `φ` on `s`. -/
theorem HasLocalPotentials.hasFDerivAt_of_eq_localPotentialIntegral {s : Set E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hs : IsPathConnected s) {x₀ : E}
    (hx₀ : x₀ ∈ s) (hloop : ∀ ℓ : Path x₀ x₀, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0)
    (γ : ∀ y, y ∈ s → Path x₀ y) (hγ : ∀ y (hy : y ∈ s) (t : I), γ y hy t ∈ s)
    {g : E → F} (hg : ∀ y (hy : y ∈ s), g y = localPotentialIntegral φ (γ y hy)) :
    ContDiffOn ℝ 1 g s ∧ ∀ y ∈ s, HasFDerivAt g (φ y) y := by
  have hlocal (y : E) (hy : y ∈ s) :
      ∃ r > 0, ball y r ⊆ s ∧ ∃ gloc : E → F, ContDiffOn ℝ 1 gloc (ball y r) ∧
        (∀ z ∈ ball y r, HasFDerivAt gloc (φ z) z) ∧
        ∀ z ∈ ball y r, g z = gloc z + (g y - gloc y) := by
    obtain ⟨r, hr, hrs, gloc, hgloc, hdloc⟩ := hasLocalPotentials_iff.mp hφ y hy
    refine ⟨r, hr, hrs, gloc, hgloc, hdloc, fun z hz ↦ ?_⟩
    have hseg : ∀ t, (Path.segment y z) t ∈ ball y r := fun t ↦
      (convex_ball y r).segment_subset (mem_ball_self hr) hz (lineMap_mem_segment ℝ y z t.2)
    have htrans_mem : ∀ t, ((γ y hy).trans (Path.segment y z)) t ∈ s :=
      trans_mem (hγ y hy) fun t ↦ hrs (hseg t)
    have heq := localPotentialIntegral_eq_of_forall_loop_eq_zero hφ hs hx₀ hloop
      (hγ z (hrs hz)) htrans_mem
    rw [localPotentialIntegral_trans hφ (hγ y hy) (fun t ↦ hrs (hseg t)),
      localPotentialIntegral_of_hasFDerivAt isOpen_ball hdloc hseg] at heq
    rw [hg z (hrs hz), hg y hy, heq]
    abel
  refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨r, hr, -, gloc, hgloc, -, heq⟩ := hlocal y hy
    have hnhds := ball_mem_nhds y hr
    exact (((hgloc.contDiffAt hnhds).add contDiffAt_const).congr_of_eventuallyEq
      (eventually_of_mem hnhds heq)).contDiffWithinAt
  · obtain ⟨r, hr, -, gloc, -, hdloc, heq⟩ := hlocal y hy
    exact ((hdloc y (mem_ball_self hr)).add_const _).congr_of_eventuallyEq
      (eventually_of_mem (ball_mem_nhds y hr) heq)

/-- On a path-connected domain where `φ` has local potentials, `φ` admits a global `C¹` potential
on `s` if and only if every loop in `s` based at `x₀` has zero path integral. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero {s : Set E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hs : IsPathConnected s)
    {x₀ : E} (hx₀ : x₀ ∈ s) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ y ∈ s, HasFDerivAt g (φ y) y) ↔
      ∀ ℓ : Path x₀ x₀, (∀ t, ℓ t ∈ s) → localPotentialIntegral φ ℓ = 0 := by
  refine ⟨fun ⟨g, _, hdg⟩ ℓ hℓ ↦ ?_, fun hloop ↦ ?_⟩
  · rw [localPotentialIntegral_of_hasFDerivAt hφ.isOpen hdg hℓ, sub_self]
  · classical
    let γ (y : E) (hy : y ∈ s) : Path x₀ y := (hs.joinedIn x₀ hx₀ y hy).somePath
    exact ⟨fun y ↦ if hy : y ∈ s then localPotentialIntegral φ (γ y hy) else 0,
      hφ.hasFDerivAt_of_eq_localPotentialIntegral hs hx₀ hloop γ
        (fun y hy t ↦ (hs.joinedIn x₀ hx₀ y hy).somePath_mem t)
        fun y hy ↦ by simp [hy]⟩

end TauCeti

end
