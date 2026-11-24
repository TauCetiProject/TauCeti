/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Topology.Algebra.Module.Matrix

/-!
# Grönwall uniqueness for linear differential systems on convex and preconnected domains

Over any nontrivially normed `ℝ`-algebra field `𝕜` and normed `𝕜`-space `E`, two solutions of the
linear differential system `v' = A(z) v` for a continuous operator family `A : 𝕜 → E →L[𝕜] E` that
agree at one point of their domain agree throughout the domain whenever the domain is convex over
`ℝ` (`Convex.eqOn_of_hasDerivWithinAt_clm_apply`) or open and preconnected
(`IsOpen.eqOn_of_hasDerivAt_clm_apply`). Neither completeness of `E` nor analyticity of `A` is
required: restricting along real affine line segments reduces the convex statement to Mathlib's
Grönwall uniqueness theorem `ODE_solution_unique_of_mem_Icc_right`, and covering an open
preconnected domain by open metric balls extends uniqueness from local convexity to global
preconnectedness, generalizing the real-line uniqueness theorem
`Continuous.eq_of_hasDerivAt_clm_apply`.

Bundling finite matrices via `Matrix.mulVecCLM` specializes both results to linear matrix
differential systems `v' = M(z) *ᵥ v` with entrywise continuous coefficients
(`Convex.eqOn_of_hasDerivWithinAt_mulVec`, `IsOpen.eqOn_of_hasDerivAt_mulVec`).

## Main declarations

* `Convex.eqOn_of_hasDerivWithinAt_clm_apply`: uniqueness of solutions to `v' = A(z) v` within a
  real-convex set `s ⊆ 𝕜`.
* `IsOpen.eqOn_of_hasDerivAt_clm_apply`: uniqueness of solutions to `v' = A(z) v` on an open
  preconnected set `s ⊆ 𝕜`.
* `Convex.eqOn_of_hasDerivWithinAt_mulVec`, `IsOpen.eqOn_of_hasDerivAt_mulVec`: the corresponding
  uniqueness theorems for linear matrix systems `v' = M(z) *ᵥ v`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §2.4 and §4.2.
-/

public section

open Filter Function Metric Set Topology
open scoped NNReal Matrix

/-- **Uniqueness for linear differential equations on convex sets.** Over any nontrivially normed
real-algebra field `𝕜`, two solutions of `v' = A(z) v` within a convex set `s` for a continuous
operator family `A` that agree at one point of `s` agree throughout `s`. -/
theorem Convex.eqOn_of_hasDerivWithinAt_clm_apply
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set 𝕜} (hs : Convex ℝ s) {A : 𝕜 → E →L[𝕜] E} (hA : ContinuousOn A s)
    {v w : 𝕜 → E} (hv : ∀ z ∈ s, HasDerivWithinAt v (A z (v z)) s z)
    (hw : ∀ z ∈ s, HasDerivWithinAt w (A z (w z)) s z)
    {z₀ : 𝕜} (hz₀ : z₀ ∈ s) (h : v z₀ = w z₀) : EqOn v w s := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro z hz
  set γ : ℝ → 𝕜 := ⇑(AffineMap.lineMap (k := ℝ) z₀ z)
  have hγ : MapsTo γ (Icc 0 1) s := hs.mapsTo_lineMap hz₀ hz
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.comp (AffineMap.lineMap_continuous (R := ℝ)).continuousOn hγ)
  set K : ℝ≥0 := Real.toNNReal (‖z - z₀‖ * max C 0)
  have hLip (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      LipschitzOnWith K (fun x : E ↦ (z - z₀) • A (γ t) x) univ := by
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y ↦ ?_)
    have hAt : ‖A (γ t)‖ ≤ max C 0 :=
      (hC t (Ico_subset_Icc_self ht)).trans (le_max_left C 0)
    have hnorm : ‖(z - z₀) • A (γ t) (x - y)‖ ≤ (K : ℝ) * ‖x - y‖ := by
      calc
        ‖(z - z₀) • A (γ t) (x - y)‖
            ≤ ‖z - z₀‖ * (‖A (γ t)‖ * ‖x - y‖) := by
              rw [norm_smul]
              gcongr
              exact (A (γ t)).le_opNorm (x - y)
        _ ≤ ‖z - z₀‖ * (max C 0 * ‖x - y‖) := by gcongr
        _ = (K : ℝ) * ‖x - y‖ := by
              rw [Real.coe_toNNReal _ (by positivity), mul_assoc]
    simpa [dist_eq_norm, smul_sub] using hnorm
  have hchain {u : 𝕜 → E} (hu : ∀ p ∈ s, HasDerivWithinAt u (A p (u p)) s p) :
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (u ∘ γ) ((z - z₀) • A (γ t) (u (γ t))) (Icc 0 1) t :=
    fun t ht ↦ by
      simpa using ((hu (γ t) (hγ ht)).hasFDerivWithinAt.restrictScalars ℝ).comp_hasDerivWithinAt t
        (AffineMap.hasDerivWithinAt_lineMap (𝕜 := ℝ)) hγ
  have hvI := hchain hv
  have hwI := hchain hw
  have h0 : (v ∘ γ) 0 = (w ∘ γ) 0 := by simpa [γ] using h
  have h1 := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x ↦ (z - z₀) • A (γ t) x) (s := fun _ ↦ univ) hLip
    (fun t ht ↦ (hvI t ht).continuousWithinAt)
    (fun t ht ↦ (hvI t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun _ _ ↦ mem_univ _)
    (fun t ht ↦ (hwI t ht).continuousWithinAt)
    (fun t ht ↦ (hwI t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun _ _ ↦ mem_univ _) h0 ⟨zero_le_one, le_rfl⟩
  simpa [γ] using h1

/-- **Uniqueness for linear differential equations on open preconnected domains.** Two solutions of
`v' = A(z) v` on an open preconnected set `s` for a continuous operator family `A` that agree at
one point of `s` agree throughout `s`. -/
theorem IsOpen.eqOn_of_hasDerivAt_clm_apply
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set 𝕜} (hs : IsOpen s) (hs' : IsPreconnected s)
    {A : 𝕜 → E →L[𝕜] E} (hA : ContinuousOn A s)
    {v w : 𝕜 → E} (hv : ∀ z ∈ s, HasDerivAt v (A z (v z)) z)
    (hw : ∀ z ∈ s, HasDerivAt w (A z (w z)) z)
    {z₀ : 𝕜} (hz₀ : z₀ ∈ s) (h : v z₀ = w z₀) : EqOn v w s := by
  let U₁ : Set 𝕜 := {z | z ∈ s ∧ v z = w z}
  let U₂ : Set 𝕜 := {z | z ∈ s ∧ v z ≠ w z}
  have hU₁ : IsOpen U₁ := Metric.isOpen_iff.mpr fun z ⟨hzs, hzw⟩ ↦ by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hs z hzs
    refine ⟨r, hr, fun y hy ↦ ⟨hsub hy, ?_⟩⟩
    exact (convex_ball z r).eqOn_of_hasDerivWithinAt_clm_apply (hA.mono hsub)
      (fun p hp ↦ (hv p (hsub hp)).hasDerivWithinAt)
      (fun p hp ↦ (hw p (hsub hp)).hasDerivWithinAt)
      (mem_ball_self hr) hzw hy
  have hU₂ : IsOpen U₂ := isOpen_iff_mem_nhds.mpr fun z ⟨hzs, hne⟩ ↦ by
    have hcont : ContinuousAt (fun y ↦ v y - w y) z :=
      (hv z hzs).continuousAt.sub (hw z hzs).continuousAt
    filter_upwards [hs.mem_nhds hzs,
      hcont.eventually_ne (sub_ne_zero.mpr hne)] with y hys hyne
    exact ⟨hys, sub_ne_zero.mp hyne⟩
  intro z hzs
  by_contra hne
  obtain ⟨p, -, hp₁, hp₂⟩ := hs' U₁ U₂ hU₁ hU₂
    (fun y hy ↦ by by_cases hyw : v y = w y <;> [exact Or.inl ⟨hy, hyw⟩; exact Or.inr ⟨hy, hyw⟩])
    ⟨z₀, hz₀, hz₀, h⟩ ⟨z, hzs, hzs, hne⟩
  exact hp₂.2 hp₁.2

/-- **Uniqueness for linear matrix differential systems on convex sets.** -/
theorem Convex.eqOn_of_hasDerivWithinAt_mulVec
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [Fintype ι]
    {s : Set 𝕜} (hs : Convex ℝ s) {M : 𝕜 → Matrix ι ι 𝕜}
    (hM : ∀ i j, ContinuousOn (fun z ↦ M z i j) s)
    {v w : 𝕜 → ι → 𝕜} (hv : ∀ z ∈ s, HasDerivWithinAt v (M z *ᵥ v z) s z)
    (hw : ∀ z ∈ s, HasDerivWithinAt w (M z *ᵥ w z) s z)
    {z₀ : 𝕜} (hz₀ : z₀ ∈ s) (h : v z₀ = w z₀) : EqOn v w s :=
  hs.eqOn_of_hasDerivWithinAt_clm_apply (Matrix.continuousOn_mulVecCLM hM)
    (fun z hz ↦ by simpa using hv z hz) (fun z hz ↦ by simpa using hw z hz) hz₀ h

/-- **Uniqueness for linear matrix differential systems on open preconnected domains.** -/
theorem IsOpen.eqOn_of_hasDerivAt_mulVec
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [Fintype ι]
    {s : Set 𝕜} (hs : IsOpen s) (hs' : IsPreconnected s) {M : 𝕜 → Matrix ι ι 𝕜}
    (hM : ∀ i j, ContinuousOn (fun z ↦ M z i j) s)
    {v w : 𝕜 → ι → 𝕜} (hv : ∀ z ∈ s, HasDerivAt v (M z *ᵥ v z) z)
    (hw : ∀ z ∈ s, HasDerivAt w (M z *ᵥ w z) z)
    {z₀ : 𝕜} (hz₀ : z₀ ∈ s) (h : v z₀ = w z₀) : EqOn v w s :=
  hs.eqOn_of_hasDerivAt_clm_apply hs' (Matrix.continuousOn_mulVecCLM hM)
    (fun z hz ↦ by simpa using hv z hz) (fun z hz ↦ by simpa using hw z hz) hz₀ h
