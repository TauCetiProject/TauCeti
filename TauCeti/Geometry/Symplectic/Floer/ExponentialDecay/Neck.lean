/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall

/-!
# Floer cylinders in a neck near a nondegenerate orbit

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C²` Hamiltonian and `x` a
nondegenerate `1`-periodic orbit of its Hamiltonian vector field: the propagator of the linearized
equation `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at time `1`. Consider a solution `u`
of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a finite cylinder
`[a, b] × ℝ / ℤ`, for almost complex structures with fixed taming constants
`c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖`, all of whose loops `u(s, ·)` stay close to `x`. Such
*necks* appear in every degeneration of Floer cylinders and pairs of pants, between the levels of
a broken limit. This file shows that the energy of a neck concentrates exponentially at its two
ends, and that a whole Floer cylinder of finite energy near `x` is the stationary cylinder over
`x`.

**Exponential decay in a neck.** There are `δ > 0` and `κ > 0`, depending only on `H`, `x`, `c`
and `M`, such that for every such solution whose loops are `δ`-close to `x` on `[a, b]`, and every
`T ≥ 0`,

`∫_{[a + T, b - T] × [0, 1]} e ≤ 2 exp (-κ T) ∫_{[a, b] × [0, 1]} e`

(`TauCeti.SymplecticForm.exists_pos_forall_setIntegral_floerEnergyDensity_le_two_mul_exp_mul`),
where `e` is the Floer energy density. The constants do not depend on `u`, `J`, `a`, `b` or `T`,
which is what makes the estimate usable for sequences of solutions on longer and longer necks.

The proof uses the action defect `g(s) = A_H(u(s, ·)) - A_H(x)`. By the energy identity
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`), the energy of the
subcylinder `[s₁, s₂] × [0, 1]` is `g(s₂) - g(s₁)`, so `g` is nondecreasing, with derivative the
energy `ε(s) = ∫₀¹ e(s, t) dt` of the slice. Near the nondegenerate orbit the action defect is
controlled by the slice energy, `|g(s)| ≤ K ε(s)`
(`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity`).
Integrating this over a step of length `K` shows that `g` at least doubles over the step where it
is nonnegative, and that `-g` at least halves where `g` is nonpositive. Hence the part of the
energy at distance `T` from the two ends of the neck is at most `2^{-⌊T / K⌋}` times the total,
whichever sign `g` has in the middle of the neck (`TauCeti.sub_le_two_mul_exp_mul_sub`).

**Local uniqueness.** There is `δ > 0` such that a finite-energy Floer cylinder `u : ℝ × ℝ → V`,
with taming constants `c` and `M`, all of whose loops are `δ`-close to `x`, is the stationary
cylinder over `x`: `u(s, t) = x(t)`
(`TauCeti.SymplecticForm.exists_pos_forall_eq_of_forall_norm_sub_le`). Indeed, the neck estimate
on `[a - T, b + T]` bounds the energy over `[a, b] × [0, 1]` by `2 exp (-κ T)` times the total
energy, which tends to zero as `T → ∞`. So the energy vanishes and `u` is stationary
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`); its loop is then an orbit
`δ`-close to `x`, hence equal to `x` by the isolation of nondegenerate orbits
(`TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_integral_of_nondegenerate`). In the
compactness theory of Floer trajectories this rules out nonstationary levels which never leave a
small neighbourhood of a nondegenerate orbit, and the neck estimate shows that no energy is lost
in the necks between the levels of a broken limit.

## Main results

* `TauCeti.SymplecticForm.exists_pos_forall_setIntegral_floerEnergyDensity_le_two_mul_exp_mul`:
  exponential decay of the energy away from the ends of a neck near a nondegenerate orbit, with
  constants independent of the solution.
* `TauCeti.SymplecticForm.exists_pos_forall_eq_of_forall_norm_sub_le`: a finite-energy Floer
  cylinder all of whose loops are close to a nondegenerate orbit is stationary at that orbit.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate orbits and its use in the
  compactness of the moduli spaces of Floer trajectories.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Chapter 4, on long cylinders of small energy.
-/

public section

open Set Filter Topology MeasureTheory Function

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V}

/-- **Exponential decay of the energy in a neck near a nondegenerate orbit.** Let `H` be a `C²`
Hamiltonian, let `x` be an orbit of its Hamiltonian vector field with `x 1 = x 0` which is
nondegenerate: the propagator of `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at time `1`.
Fix taming constants `c > 0` and `M`. Then there are `δ > 0` and `κ > 0` with the following
property. Let `u` be `C²` on an open set `U ⊇ [a, b] × ℝ`, with `u(s, 1) = u(s, 0)`, solving the
Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for almost complex
structures with `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` there, and suppose that every loop
`u(s, ·)`, `s ∈ [a, b]`, is `δ`-close to `x` on `[0, 1]`. Then for every `T ≥ 0` the energy over
`[a + T, b - T] × [0, 1]` is at most `2 exp (-κ T)` times the energy over `[a, b] × [0, 1]`. The
constants `δ` and `κ` depend only on `H`, `x`, `c` and `M`. -/
theorem exists_pos_forall_setIntegral_floerEnergyDensity_le_two_mul_exp_mul
    (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ δ > 0, ∃ κ > 0, ∀ {U : Set (ℝ × ℝ)} {u : ℝ × ℝ → V}
      {J : ℝ × ℝ → AlmostComplexStructure V} {a b T : ℝ}, IsOpen U → ContDiffOn ℝ 2 u U →
      Icc a b ×ˢ univ ⊆ U → (∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖u z - x z.2‖ ≤ δ) → 0 ≤ T →
      ∫ z in Icc (a + T) (b - T) ×ˢ Icc 0 1,
          ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z ≤
        2 * Real.exp (-(κ * T)) *
          ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z := by
  obtain ⟨δ, hδ, K, hK, hslice⟩ :=
    exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity hH hx hx1 hnd hc M
  refine ⟨δ, hδ, Real.log 2 / K, div_pos (Real.log_pos one_lt_two) hK,
    fun {U u J a b T} hU hu hUab hper hJc hJM hfloer hclose hT ↦ ?_⟩
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u with he
  set ε : ℝ → ℝ := fun s ↦ ∫ t in Icc (0 : ℝ) 1, e (s, t)
  set g : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t)) - ω.hamiltonianAction H x
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have he0 (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) : 0 ≤ e z :=
    ω.floerEnergyDensity_nonneg (ω.tames_of_mul_norm_sq_le hc (hJc z hz)) (hfloer z hz)
  have hsub {s₁ s₂ : ℝ} (h₁ : a ≤ s₁) (h₂ : s₂ ≤ b) :
      Icc s₁ s₂ ×ˢ Icc (0 : ℝ) 1 ⊆ Icc a b ×ˢ Icc 0 1 :=
    prod_mono (Icc_subset_Icc h₁ h₂) le_rfl
  have hRU {s₁ s₂ : ℝ} (h₁ : a ≤ s₁) (h₂ : s₂ ≤ b) : Icc s₁ s₂ ×ˢ Icc (0 : ℝ) 1 ⊆ U :=
    (hsub h₁ h₂).trans ((prod_mono le_rfl (subset_univ _)).trans hUab)
  -- The energy of a subcylinder is the increase of the action defect `g`.
  have henergy {s₁ s₂ : ℝ} (h₁ : a ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂ : s₂ ≤ b) :
      ∫ z in Icc s₁ s₂ ×ˢ Icc 0 1, e z = g s₂ - g s₁ := by
    rw [he, ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH1 hU hu h₁₂ (hRU h₁ h₂)
      fun s hs ↦ hper s ⟨h₁.trans hs.1, hs.2.trans h₂⟩]
    simp only [g]
    ring
  have hmono : MonotoneOn g (Icc a b) := fun s₁ hs₁ s₂ hs₂ h ↦ by
    have h0 : 0 ≤ ∫ z in Icc s₁ s₂ ×ˢ Icc (0 : ℝ) 1, e z :=
      setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
        he0 z (hsub hs₁.1 hs₂.2 hz)
    linarith [henergy hs₁.1 h hs₂.2]
  -- Near `x`, the action defect is controlled by the slice energy.
  have hg (r : ℝ) (hr : r ∈ Icc a b) : |g r| ≤ K * ε r :=
    hslice hU (hu.of_le one_le_two) (fun t ↦ hUab ⟨hr, mem_univ t⟩) (hper r hr)
      (fun t ht ↦ hJc (r, t) ⟨hr, ht⟩) (fun t ht ↦ hJM (r, t) ⟨hr, ht⟩)
      (fun t ht ↦ hfloer (r, t) ⟨hr, ht⟩) fun t ht ↦ hclose (r, t) ⟨hr, ht⟩
  -- Over a step of length `K`, a lower bound `m ≤ K ε` integrates to `m ≤ g(s + K) - g(s)`.
  have hstep {s m : ℝ} (hs : a ≤ s) (hsb : s + K ≤ b)
      (hm : ∀ r ∈ Icc s (s + K), m ≤ K * ε r) : m ≤ g (s + K) - g s := by
    have h := le_hamiltonianAction_sub_of_forall_le_mul_setIntegral_floerEnergyDensity hH1 hU hu
      hK (hRU hs hsb) (fun r hr ↦ hper r ⟨hs.trans hr.1, hr.2.trans hsb⟩) hm
    simp only [g]
    linarith
  have hpos (s : ℝ) (hs : a ≤ s) (hsb : s + K ≤ b) : 2 * g s ≤ g (s + K) := by
    have := hstep hs hsb fun r hr ↦
      (hmono ⟨hs, by linarith⟩ ⟨hs.trans hr.1, hr.2.trans hsb⟩ hr.1).trans
        ((le_abs_self _).trans (hg r ⟨hs.trans hr.1, hr.2.trans hsb⟩))
    linarith
  have hneg (s : ℝ) (hs : a ≤ s) (hsb : s + K ≤ b) : g s ≤ 2 * g (s + K) := by
    have := hstep (m := -g (s + K)) hs hsb fun r hr ↦
      (neg_le_neg (hmono ⟨hs.trans hr.1, hr.2.trans hsb⟩ ⟨by linarith, hsb⟩ hr.2)).trans
        ((neg_le_abs _).trans (hg r ⟨hs.trans hr.1, hr.2.trans hsb⟩))
    linarith
  -- If the shrunken neck is empty there is nothing to prove.
  by_cases hab : a + T ≤ b - T
  · rw [henergy (by linarith) hab (by linarith), henergy le_rfl (by linarith) le_rfl]
    exact sub_le_two_mul_exp_mul_sub hK hmono (fun s hs hsb _ ↦ hpos s hs hsb)
      (fun s hs hsb _ ↦ hneg s hs hsb) hT hab
  · rw [Icc_eq_empty hab, empty_prod, Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (by positivity) (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
      fun z hz ↦ he0 z hz)

/-- A nonnegative function on the strip `ℝ × T` whose integral vanishes over every finite part
`[-n, n] × T` has vanishing integral over the whole strip. -/
private theorem setLIntegral_univ_prod_eq_zero {f : ℝ × ℝ → ENNReal} {T : Set ℝ}
    (h : ∀ n : ℕ, ∫⁻ z in Icc (-n : ℝ) n ×ˢ T, f z = 0) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z = 0 := by
  refine le_antisymm ?_ zero_le
  have hcover : (univ : Set ℝ) ×ˢ T ⊆ ⋃ n : ℕ, Icc (-n : ℝ) n ×ˢ T := by
    rintro ⟨s, t⟩ ⟨-, ht⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |s|
    exact mem_iUnion.2 ⟨n, ⟨abs_le.1 hn, ht⟩⟩
  calc ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ≤ ∫⁻ z in ⋃ n : ℕ, Icc (-n : ℝ) n ×ˢ T, f z :=
        lintegral_mono_set hcover
    _ ≤ ∑' n : ℕ, ∫⁻ z in Icc (-n : ℝ) n ×ˢ T, f z := lintegral_iUnion_le _ _
    _ = 0 := tsum_eq_zero_iff.2 h

/-- Where a solution of the Floer equation is stationary in `s`, its loop solves Hamilton's
equation: since `∂_s u = 0` there, the Floer equation kills the defect `∂_t u - X_{H_t}(u)`. -/
private theorem fderiv_apply_sub_hamiltonianVectorField_eq_zero_of_forall_eq {u : ℝ × ℝ → V}
    {J : AlmostComplexStructure V} {s t : ℝ} (hu : DifferentiableAt ℝ u (s, t))
    (hstat : ∀ r, u (r, t) = u (s, t))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t) : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ u (s, t) (0, 1) - ω.hamiltonianVectorField (H t) (u (s, t)) = 0 := by
  have hds : fderiv ℝ u (s, t) (1, 0) = 0 :=
    (hasDerivAt_slice_left hu).unique
      ((hasDerivAt_const s (u (s, t))).congr_of_eventuallyEq (Eventually.of_forall hstat))
  have h := (isComplexLinearMap_stdComplexLine_iff _).1 hfloer
  simp only [ContinuousLinearMap.coe_coe, perturbedFDeriv_cylindrical_apply_stdComplexLineImag,
    perturbedFDeriv_cylindrical_apply_stdComplexLineReal, hds, map_zero] at h
  exact h

/-- **Local uniqueness at a nondegenerate orbit.** Let `H` be a `C²` Hamiltonian and `x` an orbit
of its Hamiltonian vector field with `x 1 = x 0` which is nondegenerate, and fix taming constants
`c > 0` and `M`. Then there is `δ > 0` such that every `C²` Floer cylinder `u` with
`u(s, 1) = u(s, 0)`, solving `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for almost complex structures
with `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` on the strip `ℝ × [0, 1]`, of finite energy, and
all of whose loops are `δ`-close to `x` on `[0, 1]`, is the stationary cylinder over `x`:
`u(s, t) = x(t)` for `t ∈ [0, 1]`. -/
theorem exists_pos_forall_eq_of_forall_norm_sub_le
    (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ δ > 0, ∀ {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}, ContDiff ℝ 2 u →
      (∀ s, u (s, 1) = u (s, 0)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤ →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ‖u z - x z.2‖ ≤ δ) →
      ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, u z = x z.2 := by
  obtain ⟨δ₁, hδ₁, κ, hκ, hneck⟩ :=
    exists_pos_forall_setIntegral_floerEnergyDensity_le_two_mul_exp_mul hH hx hx1 hnd hc M
  obtain ⟨δ₂, hδ₂, C, -, hiso⟩ :=
    exists_forall_norm_sub_le_mul_integral_of_nondegenerate hH hx hx1 hnd
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {u J} hu hper hJc hJM hfloer hE hclose ↦ ?_⟩
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u
  set E := ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (e z)
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hJ (z : ℝ × ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) : ω.Tames (J z) :=
    ω.tames_of_mul_norm_sq_le hc (hJc z hz)
  have hec : ContinuousOn e univ :=
    ω.continuousOn_floerEnergyDensity isOpen_univ (hu.of_le one_le_two).contDiffOn contDiffOn_const
      (contDiff_uncurry_cylindrical hH1).contDiffOn
  have hstrip {a b : ℝ} : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  -- The energy of a finite cylinder is the integral of a continuous nonnegative function.
  have hlint (a b : ℝ) : ENNReal.ofReal (∫ z in Icc a b ×ˢ Icc 0 1, e z) =
      ∫⁻ z in Icc a b ×ˢ Icc 0 1, ENNReal.ofReal (e z) :=
    ofReal_integral_eq_lintegral_ofReal
      ((hec.mono (subset_univ _)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
        (Eventually.of_forall fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hstrip hz))
          (hfloer z (hstrip hz))))
  -- Every finite cylinder `[-n, n] × [0, 1]` sits in the middle of arbitrarily long necks, so it
  -- carries no energy.
  have hR0 (a b : ℝ) : ∫ z in Icc a b ×ˢ Icc 0 1, e z = 0 := by
    refine le_antisymm ?_ (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
      fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hstrip hz)) (hfloer z (hstrip hz)))
    have hbound (T : ℝ) (hT : 0 ≤ T) :
        ∫ z in Icc a b ×ˢ Icc 0 1, e z ≤ 2 * Real.exp (-(κ * T)) * E.toReal := by
      have h := hneck (a := a - T) (b := b + T) isOpen_univ (hu.of_le le_rfl).contDiffOn
        (subset_univ _) (fun s _ ↦ hper s) (fun z hz ↦ hJc z (hstrip hz))
        (fun z hz ↦ hJM z (hstrip hz)) (fun z hz ↦ hfloer z (hstrip hz))
        (fun z hz ↦ (hclose z (hstrip hz)).trans (min_le_left _ _)) hT
      rw [sub_add_cancel, add_sub_cancel_right] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← ENNReal.ofReal_le_iff_le_toReal hE, hlint]
      exact lintegral_mono_set hstrip
    have htend : Tendsto (fun T ↦ 2 * Real.exp (-(κ * T)) * E.toReal) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hκ))
      simpa using (h.const_mul 2).mul_const E.toReal
    exact ge_of_tendsto htend ((eventually_ge_atTop 0).mono hbound)
  -- Hence the total energy vanishes and `u` is stationary.
  have hE0 : E = 0 := setLIntegral_univ_prod_eq_zero fun n ↦ by
    rw [← hlint, hR0, ENNReal.ofReal_zero]
  have hstat := (ω.lintegral_floerEnergyDensity_eq_zero_iff hH1 isOpen_univ
    (hu.of_le one_le_two).contDiffOn (subset_univ _) hJ hfloer).1 hE0
  -- The loop `u(0, ·)` is an orbit: since `∂_s u = 0`, the Floer equation kills the defect.
  have hdu := hu.differentiable two_ne_zero
  have hdefect (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ u (0, t) (0, 1) - ω.hamiltonianVectorField (H t) (u (0, t)) = 0 :=
    fderiv_apply_sub_hamiltonianVectorField_eq_zero_of_forall_eq (hdu (0, t))
      (fun r ↦ hstat r t ht) (hfloer (0, t) ⟨mem_univ _, ht⟩)
  have hiso' := hiso (γ := fun t ↦ u (0, t)) (γ' := fun t ↦ fderiv ℝ u (0, t) (0, 1))
    (((hu.continuous_fderiv two_ne_zero).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id))
    (fun t ↦ hasDerivAt_slice_right (hdu (0, t))) (hper 0)
    (fun t ht ↦ (hclose (0, t) ⟨mem_univ _, ht⟩).trans (min_le_right _ _))
  have hint : ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (0, t) (0, 1) - ω.hamiltonianVectorField (H t) (u (0, t))‖ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      rw [uIcc_of_le zero_le_one] at ht
      simp [hdefect t ht]]
    simp
  rintro ⟨s, t⟩ ⟨-, ht⟩
  have h := hiso' t ht
  rw [hint, mul_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact (hstat s t ht).trans h

end TauCeti.SymplecticForm
