/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Sections along a curve with a prescribed interior value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth
manifold, and let `γ` be a curve which is `C^n` on a parameter set `s`. For `a < c < b`, every
vector `v` of the fibre of `V` at `γ c` is the value at `c` of a section along `γ` which is `C^n`
on `s` and vanishes at `a` and `b`: extend `v` to a global `C^n` section with
`FiberBundle.exists_contMDiff_section_eq`, restrict it to `γ`, and multiply by a smooth bump
function around `c` supported in `(a, b)`. Similarly, for a strictly increasing partition `τ` and
an interior vertex `τ j.castSucc.succ`, `exists_contDiff_smul_section_isolating_vertex` produces a
smooth cutoff supported in `(τ 0, τ (Fin.last (k + 1)))` and a global `C^n` section whose product
attains a prescribed fibre vector at that vertex while vanishing at every other vertex. The model
fibre need not be finite-dimensional.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- For `a < c < b`, every vector of `V` at `γ c` is the value at `c` of a section along `γ`
which vanishes at `a` and `b` and is `C^n` on a given parameter set on which `γ` is `C^n`. -/
theorem exists_contMDiffOn_sectionAlong_eq_zero_endpoints {n : ℕ∞}
    [ContMDiffVectorBundle n F V I] {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ s) {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (v : V (γ c)) :
    ∃ W : ∀ t, V (γ t),
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) n (fun t ↦ TotalSpace.mk' F (γ t) (W t)) s ∧
        W a = 0 ∧ W b = 0 ∧ W c = v := by
  obtain ⟨X, hX, hXc⟩ := FiberBundle.exists_contMDiff_section_eq I F n v
  let δ := min (c - a) (b - c) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let φ : ContDiffBump c := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hφa : φ a = 0 := φ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hac)]
    dsimp only [φ, δ]
    linarith [min_le_left (c - a) (b - c)])
  have hφb : φ b = 0 := φ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hcb)]
    dsimp only [φ, δ]
    linarith [min_le_right (c - a) (b - c)])
  refine ⟨fun t ↦ φ t • X (γ t),
    (φ.contDiff (n := n)).contMDiff.contMDiffOn.smul_totalSpace (hX.comp_contMDiffOn hγ), ?_, ?_,
    ?_⟩
  · simp only [hφa, zero_smul]
  · simp only [hφb, zero_smul]
  · simp only [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_smul, hXc]

/-- For a strictly increasing partition `τ` and an interior index `j : Fin k`, every fibre vector
`v` at `γ (τ j.castSucc.succ)` is attained by `φ t • X (γ t)` for a smooth cutoff `φ : ℝ → ℝ`
supported in `(τ 0, τ (Fin.last (k + 1)))` that vanishes at every other vertex of `τ` and a global
`C^n` section `X` (`n ≤ ∞`). -/
theorem exists_contDiff_smul_section_isolating_vertex {n : ℕ∞ω} [ENat.LEInfty n]
    [ContMDiffVectorBundle n F V I] {γ : ℝ → M} {k : ℕ}
    (τ : Fin (k + 2) → ℝ) (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (j : Fin k) (v : V (γ (τ j.castSucc.succ))) :
    ∃ (φ : ℝ → ℝ) (X : ∀ x, V x),
      ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Ioo (τ 0) (τ (Fin.last (k + 1))) ∧
        ContMDiff I (I.prod 𝓘(ℝ, F)) n (T% X) ∧
        φ (τ j.castSucc.succ) • X (γ (τ j.castSucc.succ)) = v ∧
        ∀ i : Fin (k + 2), i ≠ j.castSucc.succ → φ (τ i) = 0 := by
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  let c := τ j.castSucc.succ
  have hleft : τ j.castSucc.castSucc < c := hτ j.castSucc
  have hright : c < τ j.succ.succ := hτ j.succ
  let δ := min (c - τ j.castSucc.castSucc) (τ j.succ.succ - c) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let φ : ContDiffBump c := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hφ_tsupp : tsupport φ ⊆ Ioo (τ j.castSucc.castSucc) (τ j.succ.succ) := by
    rw [φ.tsupport_eq, Real.closedBall_eq_Icc]
    refine Icc_subset_Ioo ?_ ?_ <;> dsimp only [φ, δ]
    · linarith [min_le_left (c - τ j.castSucc.castSucc) (τ j.succ.succ - c)]
    · linarith [min_le_right (c - τ j.castSucc.castSucc) (τ j.succ.succ - c)]
  obtain ⟨X, hX, hXc⟩ := FiberBundle.exists_contMDiff_section_eq I F n v
  refine ⟨φ, X, φ.contDiff,
    hφ_tsupp.trans (Ioo_subset_Ioo (hmono (Fin.zero_le _)) (hmono (Fin.le_last _))), hX, ?_,
    fun i hij ↦ image_eq_zero_of_notMem_tsupport fun hi ↦ ?_⟩
  · simp [c, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), hXc]
  · have hi' := hφ_tsupp hi
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hi'.1.not_ge (hmono (Fin.le_iff_val_le_val.mpr
        (by simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hlt ⊢; omega)))
    · exact hi'.2.not_ge (hmono (Fin.le_iff_val_le_val.mpr
        (by simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hgt ⊢; omega)))

end TauCeti.Manifold
