/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.ContDiff.Puncture

/-!
# Regularity at the origin of positively homogeneous maps

A degree `p` homogeneous map which is `Cᵏ` away from zero and vanishes at zero is globally `Cᵏ`
when `k < p` in finite-dimensional sources. Such maps give finite-regularity examples with
vanishing jets at the origin and allow singular homogeneous formulas to extend across zero.
More generally, punctured derivative bounds of degree `p-j` give the same extension on arbitrary
normed sources, without compactness or finite-dimensionality assumptions.

Away from zero, on a real inner product space, the homogeneous extension
`ξ ↦ ‖ξ‖ ^ m • g (‖ξ‖⁻¹ • ξ)` of a map `g` that is `C^n` off zero is `C^n`, with `C^n` dependence
on an extra parameter (`ContDiffOn.norm_rpow_smul_comp_normalize`).
-/

public section

open Set Filter Topology Metric
open scoped ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {p : ℝ}

/-- A continuous positively homogeneous map on the punctured space has the expected radial
bound. Neither a nonzero source nor completeness of the target is required. -/
theorem exists_norm_le_mul_rpow_of_homogeneous
    (hf : ContinuousOn f {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ p • f x) :
    ∃ C ≥ 0, ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖ ^ p := by
  let g : ℝ × E → F := fun q ↦ f q.2
  have hg : ContDiffOn ℝ 0 g {q | q.2 ≠ 0} :=
    (contDiffOn_zero.mpr hf).comp contDiffOn_snd (fun _ hq ↦ hq)
  have hhomg : ∀ (a : ℝ) x, x ≠ 0 → ∀ t : ℝ, 0 < t →
      g (a, t • x) = t ^ p • g (a, x) := fun _ x _ t ht ↦ hhom t ht x
  obtain ⟨C, hC, hb⟩ := exists_norm_iteratedFDeriv_le_of_smul_snd_eq
    (K := {(0 : ℝ)}) isCompact_singleton hg hhomg (k := 0) le_rfl
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  simpa [g, iteratedFDeriv_zero_apply] using hb 0 rfl x hx (fun i ↦ Fin.elim0 i)

/-- A homogeneous map of degree greater than one has zero derivative at the origin.
This uses only continuity away from the origin, not global differentiability. -/
theorem hasFDerivAt_zero_of_homogeneous (hf : ContinuousOn f {0}ᶜ) (h0 : f 0 = 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ p • f x) (hp : 1 < p) :
    HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
  obtain ⟨C, _, hbound⟩ := exists_norm_le_mul_rpow_of_homogeneous hf hhom
  exact hasFDerivAt_zero_of_norm_rpow_bound h0 hbound hp

omit [ProperSpace E] in
/-- Differentiation lowers the degree of a positively homogeneous map by one. -/
theorem fderiv_smul_of_homogeneous
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ p • f x)
    {t : ℝ} (ht : 0 < t) (x : E)
    (hfx : DifferentiableAt ℝ f x) (hftx : DifferentiableAt ℝ f (t • x)) :
    fderiv ℝ f (t • x) = t ^ (p - 1) • fderiv ℝ f x := by
  let L : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  have hcomp : f ∘ L = t ^ p • f := funext (hhom t ht)
  ext v
  have h := congrArg (fun g ↦ fderiv ℝ g x v) hcomp
  have hd : DifferentiableAt ℝ f (L x) := by simpa only [L, smul_apply,
    ContinuousLinearMap.id_apply] using hftx
  rw [fderiv_comp _ hd L.differentiableAt, L.fderiv,
    fderiv_const_smul hfx] at h
  have hh := congrArg (fun w : F ↦ t⁻¹ • w) h
  simpa [L, smul_smul, ht.ne', Real.rpow_sub_one, div_eq_mul_inv, mul_comm] using hh

omit [ProperSpace E] in
/-- A positively homogeneous map of degree `p > k`, vanishing at the origin and `Cᵏ` elsewhere,
is globally `Cᵏ`. The target may be infinite-dimensional and need not be complete. -/
theorem contDiff_of_homogeneous [FiniteDimensional ℝ E] {k : ℕ}
    (hf : ContDiffOn ℝ k f {0}ᶜ) (h0 : f 0 = 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ p • f x) (hp : (k : ℝ) < p) :
    ContDiff ℝ k f := by
  -- Compactness of the unit sphere supplies origin bounds; the zero derivative is
  -- established before applying induction to the derivative field.
  induction k generalizing F p with
  | zero =>
    simp only [Nat.cast_zero] at hf hp ⊢
    rw [contDiff_zero, continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      obtain ⟨C, _, hbound⟩ := exists_norm_le_mul_rpow_of_homogeneous hf.continuousOn hhom
      have hn : ContinuousAt (fun x : E ↦ ‖x‖ ^ p) 0 :=
        continuousAt_id.norm.rpow_const (Or.inr hp.le)
      rw [ContinuousAt, h0]
      refine squeeze_zero_norm (a := fun x : E ↦ C * ‖x‖ ^ p) (fun x ↦ ?_) ?_
      · by_cases hx : x = 0
        · simp [hx, h0, Real.zero_rpow hp.ne']
        · exact hbound x hx
      · have hc : ContinuousAt (fun x : E ↦ C * ‖x‖ ^ p) 0 :=
          continuousAt_const.mul hn
        simpa only [norm_zero, Real.zero_rpow hp.ne', mul_zero] using hc.tendsto
    · exact hf.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  | succ k ih =>
    have hp1 : 1 < p :=
      lt_of_le_of_lt (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) hp
    have hzero := hasFDerivAt_zero_of_homogeneous hf.continuousOn h0 hhom hp1
    have hd : Differentiable ℝ f := by
      intro x
      by_cases hx : x = 0
      · simpa only [hx] using hzero.differentiableAt
      · exact (hf.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt
          (by simp)
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨hd, by simp, fun v ↦ ?_⟩
    apply ih ((hf.fderiv_of_isOpen isOpen_compl_singleton
      (show (k : ℕ∞ω) + 1 ≤ ↑(k + 1) by simp)).clm_apply contDiffOn_const)
    · simp only [hzero.fderiv, zero_apply]
    · intro t ht x
      rw [fderiv_smul_of_homogeneous hhom ht x (hd x) (hd (t • x))]
      rfl
    · push_cast at hp
      linarith

omit [ProperSpace E] in
/-- Decay of the punctured derivatives at a rate `‖x‖^(p-j)`, with `p > k`, extends a map
vanishing at zero to a global `Cᵏ` map. No finite-dimensionality or completeness is required. -/
theorem contDiff_of_iteratedFDeriv_norm_rpow_bound {f : E → F} {k : ℕ} {p : ℝ}
    (hf : ContDiffOn ℝ k f {0}ᶜ) (h0 : f 0 = 0) (hp : (k : ℝ) < p)
    (hb : ∀ j ≤ k, ∃ C : ℝ, ∀ x ≠ 0,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C * ‖x‖ ^ (p - j)) : ContDiff ℝ k f := by
  have hz : ∀ j ≤ k, iteratedFDeriv ℝ j f 0 = 0 := by
    intro j hj
    induction j with
    | zero =>
      ext v
      simp [h0]
    | succ j ih =>
      obtain ⟨C, hC⟩ := hb j (by omega)
      have hder := hasFDerivAt_zero_of_norm_rpow_bound (ih (by omega)) hC (by
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
        linarith : 1 < p - j)
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hder.fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).symm.map_zero
  rw [contDiff_nat_iff_continuous_differentiable]
  constructor
  · intro j hj
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      obtain ⟨C, hC⟩ := hb j hj
      have hpos : 0 < p - j := by
        have : (j : ℝ) ≤ k := by exact_mod_cast hj
        linarith
      rw [ContinuousAt, hz j hj]
      apply squeeze_zero_norm (a := fun x : E ↦ C * ‖x‖ ^ (p - j))
      · intro x
        by_cases hx : x = 0
        · simp [hx, hz j hj, Real.zero_rpow hpos.ne']
        · exact hC x hx
      · have hc : ContinuousAt (fun x : E ↦ C * ‖x‖ ^ (p - j)) 0 :=
          continuousAt_const.mul (continuousAt_id.norm.rpow_const (Or.inr hpos.le))
        simpa only [norm_zero, Real.zero_rpow hpos.ne', mul_zero] using hc.tendsto
    · exact (hf.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).continuousAt_iteratedFDeriv
        (by exact_mod_cast hj)
  · intro j hj x
    by_cases hx : x = 0
    · subst x
      obtain ⟨C, hC⟩ := hb j (by omega)
      exact (hasFDerivAt_zero_of_norm_rpow_bound (hz j (by omega)) hC (by
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
        linarith : 1 < p - j)).differentiableAt
    · exact (hf.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast hj)

end TauCeti

/-- The homogeneous extension `(y, ξ) ↦ ‖ξ‖ ^ m • g (y, ‖ξ‖⁻¹ • ξ)` of degree `m` from the unit
sphere of an inner product space is `C^n` off `ξ = 0` when `g` is. -/
theorem ContDiffOn.norm_rpow_smul_comp_normalize {Y E F : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : WithTop ℕ∞} {g : Y × E → F} (hg : ContDiffOn ℝ n g {q | q.2 ≠ 0})
    (m : ℝ) :
    ContDiffOn ℝ n (fun q : Y × E ↦ ‖q.2‖ ^ m • g (q.1, ‖q.2‖⁻¹ • q.2)) {q | q.2 ≠ 0} := by
  intro q hq
  have hq' : q.2 ≠ 0 := hq
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq'
  have hnorm : ContDiffAt ℝ n (fun q : Y × E ↦ ‖q.2‖) q :=
    (contDiffAt_norm ℝ hq').comp q contDiffAt_snd
  -- The radial projection stays off `ξ = 0`, where `g` is smooth.
  have hmem : (q.1, ‖q.2‖⁻¹ • q.2) ∈ {q : Y × E | q.2 ≠ 0} := smul_ne_zero (inv_ne_zero hn) hq'
  have hg' := (hg.contDiffAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hmem)).comp
    q (contDiffAt_fst.prodMk ((hnorm.inv hn).smul contDiffAt_snd))
  exact ((hnorm.rpow_const_of_ne (p := m) hn).smul hg').contDiffWithinAt
