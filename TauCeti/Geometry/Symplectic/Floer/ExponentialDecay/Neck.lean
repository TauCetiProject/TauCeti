/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
import TauCeti.Analysis.SpecificLimits.ShiftDoubling
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# Exponential decay along a long Floer neck near a nondegenerate orbit

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C²` Hamiltonian and `x` a
`1`-periodic orbit of its Hamiltonian vector field which is nondegenerate: the propagator of the
linearized equation `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at time `1`. A *neck* is a
finite cylinder `[a, b] × [0, 1]` on which a solution `u` of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`, for uniformly tame almost complex structures, stays close to
`x`. Necks appear between the levels of a breaking sequence of Floer trajectories, along the ends of
a pair of pants that is about to break, and in the glued solutions near a broken one.

This file shows that on a neck the energy concentrates exponentially at its two ends, with
constants that depend only on `ω`, `H`, `x` and the tameness constants `c`, `M`, not on the
solution or on the length of the neck. There are `δ > 0` and `κ > 0` such that if the loops of `u`
are `δ`-close to `x` on `[a, b] × [0, 1]`, then for `a ≤ s₁ ≤ s₂ ≤ b`

`E([s₁, s₂]) ≤ 4 E([a, b]) (exp (-κ (b - s₂)) + exp (-κ (s₁ - a)))`,

where `E(I)` is the energy of `u` over `I × [0, 1]`
(`TauCeti.SymplecticForm.exists_pos_forall_setIntegral_floerEnergyDensity_le_mul_exp_add_exp`).
If moreover `‖∂_s u‖ ≤ L` on the neck, its loops converge to `x` exponentially fast towards the
middle of the neck: for some `κ' > 0` and `C` depending only on the same data,

`‖u(s, t) - x(t)‖ ≤ (C (1 + √E([a, b])) + L) exp (-κ' min (s - a, b - s))`

(`TauCeti.SymplecticForm.exists_pos_forall_norm_sub_le_mul_exp_min`). Such estimates control the
middle of the long necks that appear in the compactness and gluing theory of Floer trajectories and
pairs of pants: no energy is lost there, and the loops there are uniformly close to the orbit.

**The proof.** Write `g(s) = A_H(u(s, ·)) - A_H(x)` for the action of the loop at `s` relative to
the orbit. By the energy identity
`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`, `g` is
nondecreasing and the energy over `[s₁, s₂] × [0, 1]` is `g(s₂) - g(s₁)`. Near the nondegenerate
orbit, `|g(s)|` is at most `K` times the energy of the slice at `s`
(`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity`),
with `K` independent of `u`. Integrating this over a step `[s, s + K]` shows that the positive part
of `g` doubles forwards and its negative part doubles backwards, `2 g(s) ≤ g(s + K)` and
`g(s) ≤ 2 g(s + K)` (`TauCeti.two_mul_sub_le_and_sub_le_two_mul_of_abs_sub_le_mul`), and
`TauCeti.sub_le_mul_exp_add_exp_of_two_mul_le` turns this into the
two-sided decay at the rate `κ = log 2 / K`. For the `C⁰` estimate, a slice of small energy in a
short window `[s, s + h]` is uniformly close to `x` by
`TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_sqrt_setIntegral_floerEnergyDensity`, and the
bound on `∂_s u` carries this to the loop at `s`. The window length `h = exp (-κ' d)`, with
`d = min (s - a, b - s)` and `κ' = κ / 3`, balances the two errors.

## Main results

* `TauCeti.SymplecticForm.exists_pos_forall_setIntegral_floerEnergyDensity_le_mul_exp_add_exp`:
  the energy in the middle of a neck near a nondegenerate orbit is exponentially small, uniformly
  in the solution and in the length of the neck.
* `TauCeti.SymplecticForm.exists_pos_forall_norm_sub_le_mul_exp_min`: the loops in the middle of
  such a neck converge to the orbit exponentially fast, given a bound on `∂_s u`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on exponential decay at nondegenerate orbits and the
  compactness and gluing of Floer trajectories.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Chapter 4,
  on long cylinders of small energy in the bubbling analysis.
-/

public section

open Set MeasureTheory Function

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V}

/-- **The energy on a neck near a nondegenerate orbit concentrates at its ends.** Let `H` be a `C²`
Hamiltonian, `x` a nondegenerate orbit of its Hamiltonian vector field with `x 1 = x 0`, and `c > 0`
and `M` tameness constants. Then there are `δ > 0` and `κ > 0`, depending only on `ω`, `H`, `x`,
`c` and `M`, with the following property. Let `u` be `C²` on an open set containing
`[a, b] × ℝ`, with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for almost complex structures
satisfying `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` there, and `δ`-close to `x` there:
`‖u(s, t) - x(t)‖ ≤ δ`. Then for `a ≤ s₁ ≤ s₂ ≤ b` the energy over `[s₁, s₂] × [0, 1]` is at most
`4 E (exp (-κ (b - s₂)) + exp (-κ (s₁ - a)))`, where `E` is the energy over `[a, b] × [0, 1]`. -/
theorem exists_pos_forall_setIntegral_floerEnergyDensity_le_mul_exp_add_exp
    (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) (c M : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ κ > 0, ∀ {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
      {U : Set (ℝ × ℝ)} {a b : ℝ}, IsOpen U → ContDiffOn ℝ 2 u U → Icc a b ×ˢ univ ⊆ U →
      (∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖u z - x z.2‖ ≤ δ) →
      ∀ ⦃s₁ s₂ : ℝ⦄, a ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ b →
        ∫ z in Icc s₁ s₂ ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z ≤
          4 * (∫ z in Icc a b ×ˢ Icc 0 1,
            ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) *
            (Real.exp (-(κ * (b - s₂))) + Real.exp (-(κ * (s₁ - a)))) := by
  obtain ⟨δ, hδ, K, hK, hslice⟩ :=
    exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity hH hx hx1 hnd c M hc
  refine ⟨δ, hδ, Real.log 2 / K, div_pos (Real.log_pos one_lt_two) hK,
    fun {u J U a b} hU hu hab hper hJc hJM hfloer hclose s₁ s₂ h₁ h₁₂ h₂ ↦ ?_⟩
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u
  set g : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t)) - ω.hamiltonianAction H x
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hrect {s s' : ℝ} (hs : a ≤ s) (hs' : s' ≤ b) : Icc s s' ×ˢ Icc (0 : ℝ) 1 ⊆ U :=
    fun z hz ↦ hab ⟨⟨hs.trans hz.1.1, hz.1.2.trans hs'⟩, mem_univ _⟩
  -- The energy over a subrectangle is the increase of `g`.
  have henergy {s s' : ℝ} (hs : a ≤ s) (hss' : s ≤ s') (hs' : s' ≤ b) :
      ∫ z in Icc s s' ×ˢ Icc 0 1, e z = g s' - g s := by
    rw [ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH1 hU hu hss' (hrect hs hs')
      fun r hr ↦ hper r ⟨hs.trans hr.1, hr.2.trans hs'⟩]
    ring
  have he0 (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc 0 1) : 0 ≤ e z :=
    ω.floerEnergyDensity_nonneg (tames_of_mul_norm_sq_le hc (hJc z hz)) (hfloer z hz)
  have hmono : MonotoneOn g (Icc a b) := fun s hs s' hs' hss' ↦ by
    have h := henergy hs.1 hss' hs'.2
    have : 0 ≤ ∫ z in Icc s s' ×ˢ Icc 0 1, e z :=
      setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
        he0 z ⟨⟨hs.1.trans hz.1.1, hz.1.2.trans hs'.2⟩, hz.2⟩
    linarith
  -- Near `x` the action defect of a loop is at most `K` times the energy of its slice.
  have hg (r : ℝ) (hr : r ∈ Icc a b) : |g r| ≤ K * ∫ t in Icc (0 : ℝ) 1, e (r, t) :=
    hslice hU (hu.of_le (by norm_num)) (fun t ↦ hab ⟨hr, mem_univ t⟩) (hper r hr)
      (fun t ht ↦ hJc _ ⟨hr, ht⟩) (fun t ht ↦ hJM _ ⟨hr, ht⟩) (fun t ht ↦ hfloer _ ⟨hr, ht⟩)
      fun t ht ↦ hclose _ ⟨hr, ht⟩
  -- Hence the positive part of `g` doubles forwards and its negative part doubles backwards.
  have hstep (s : ℝ) (hs : a ≤ s) (hsK : s + K ≤ b) :
      2 * g s ≤ g (s + K) ∧ g s ≤ 2 * g (s + K) := by
    obtain ⟨hint, heq⟩ := ω.integrableOn_and_integral_setIntegral_floerEnergyDensity_eq hH1 hU hu
      (by linarith : s ≤ s + K) (hrect hs hsK) fun r hr ↦ hper r ⟨hs.trans hr.1, hr.2.trans hsK⟩
    simpa only [sub_zero] using two_mul_sub_le_and_sub_le_two_mul_of_abs_sub_le_mul (a₀ := 0)
      (σ := fun r ↦ ∫ t in Icc (0 : ℝ) 1, e (r, t)) hK (hmono.mono (Icc_subset_Icc hs hsK))
      (fun r hr ↦ by simpa only [sub_zero] using hg r ⟨hs.trans hr.1, hr.2.trans hsK⟩) hint
      (heq.trans (by simp only [g]; ring))
  have hab' : a ≤ b := h₁.trans (h₁₂.trans h₂)
  rw [henergy h₁ h₁₂ h₂, henergy le_rfl hab' le_rfl]
  exact sub_le_mul_exp_add_exp_of_two_mul_le hmono hstep h₁ h₁₂ h₂

/-- The bound of `TauCeti.SymplecticForm.exists_pos_forall_norm_sub_le_mul_exp_min` at distance
`d < 1` from an end follows from the closeness `δ` alone, once `C ≥ δ exp κ`. -/
private theorem le_mul_exp_neg_of_lt_one {δ κ d C E L : ℝ} (hδ : 0 ≤ δ) (hκ : 0 < κ) (hd1 : d < 1)
    (hC : δ * Real.exp κ ≤ C) (hL : 0 ≤ L) :
    δ ≤ (C * (1 + √E) + L) * Real.exp (-(κ * d)) := by
  have hκd : 1 ≤ Real.exp κ * Real.exp (-(κ * d)) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ δ * Real.exp κ).trans hC
  calc δ ≤ δ * Real.exp κ * Real.exp (-(κ * d)) := by
        rw [mul_assoc]
        exact le_mul_of_one_le_right hδ hκd
    _ ≤ (C * (1 + √E) + L) * Real.exp (-(κ * d)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [Real.sqrt_nonneg E]) (Real.exp_pos _).le

/-- In the proof of `TauCeti.SymplecticForm.exists_pos_forall_norm_sub_le_mul_exp_min`: the energy
bound of a window `[s, s + h] ⊆ [a, b]` with `h = exp (-κ₀ d / 3) ≤ 1`, where `d ≤ s - a` and
`d ≤ b - s`, gives `W / h ≤ 4 (exp κ₀ + 1) E h²`. -/
private theorem div_le_mul_sq_of_le_mul_exp_add_exp {W E κ₀ a b s d h : ℝ} (hκ₀ : 0 < κ₀)
    (hE : 0 ≤ E) (hda : d ≤ s - a) (hdb : d ≤ b - s) (hh : h = Real.exp (-(κ₀ / 3 * d)))
    (hh1 : h ≤ 1)
    (hW : W ≤ 4 * E * (Real.exp (-(κ₀ * (b - (s + h)))) + Real.exp (-(κ₀ * (s - a))))) :
    W / h ≤ 4 * (Real.exp κ₀ + 1) * E * h ^ 2 := by
  have hh0 : 0 < h := hh ▸ Real.exp_pos _
  have hh3 : h ^ 3 = Real.exp (-(κ₀ * d)) := by
    rw [hh, ← Real.exp_natCast_mul]
    congr 1
    push_cast
    ring
  have h₁ : Real.exp (-(κ₀ * (b - (s + h)))) ≤ Real.exp κ₀ * h ^ 3 := by
    rw [hh3, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have h₂ : Real.exp (-(κ₀ * (s - a))) ≤ h ^ 3 := by
    rw [hh3, Real.exp_le_exp]
    nlinarith
  rw [div_le_iff₀ hh0]
  refine hW.trans ?_
  nlinarith

/-- **The loops on a neck near a nondegenerate orbit converge to it exponentially.** Let `H`, `x`,
`c` and `M` be as in
`TauCeti.SymplecticForm.exists_pos_forall_setIntegral_floerEnergyDensity_le_mul_exp_add_exp`. Then
there are `δ > 0`, `κ > 0` and `C`, depending only on `ω`, `H`, `x`, `c` and `M`, with the
following property. Let `u` be a `C²` solution of the Floer equation on `[a, b] × [0, 1]` which is
`δ`-close to `x` there, under the hypotheses of that theorem, and suppose that `‖∂_s u‖ ≤ L` there.
Then for `s ∈ [a, b]` and `t ∈ [0, 1]`

`‖u(s, t) - x(t)‖ ≤ (C (1 + √E) + L) exp (-κ min (s - a, b - s))`,

where `E` is the energy of `u` over `[a, b] × [0, 1]`. -/
theorem exists_pos_forall_norm_sub_le_mul_exp_min
    (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) (c M : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ κ > 0, ∃ C, ∀ {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
      {U : Set (ℝ × ℝ)} {a b L : ℝ}, IsOpen U → ContDiffOn ℝ 2 u U → Icc a b ×ˢ univ ⊆ U →
      (∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖u z - x z.2‖ ≤ δ) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ u z (1, 0)‖ ≤ L) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤
        (C * (1 + √(∫ z in Icc a b ×ˢ Icc 0 1,
          ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)) + L) *
          Real.exp (-(κ * min (s - a) (b - s))) := by
  obtain ⟨δ₁, hδ₁, κ₀, hκ₀, hdecay⟩ :=
    exists_pos_forall_setIntegral_floerEnergyDensity_le_mul_exp_add_exp hH hx hx1 hnd c M hc
  obtain ⟨δ₂, hδ₂, K, hK, hwin⟩ :=
    exists_forall_norm_sub_le_mul_add_mul_sqrt_setIntegral_floerEnergyDensity hH hx hx1 hnd c M hc
  set δ := min δ₁ δ₂
  set κ := κ₀ / 3
  set C := max (δ * Real.exp κ) (K * √(4 * (Real.exp κ₀ + 1)))
  refine ⟨δ, lt_min hδ₁ hδ₂, κ, by positivity, C,
    fun {u J U a b L} hU hu hab hper hJc hJM hfloer hclose hL s hs t ht ↦ ?_⟩
  set E := ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z
  set d := min (s - a) (b - s)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL (s, t) ⟨hs, ht⟩)
  have hκ : 0 < κ := by positivity
  have hd : 0 ≤ d := le_min (sub_nonneg.2 hs.1) (sub_nonneg.2 hs.2)
  have hda : d ≤ s - a := min_le_left _ _
  have hdb : d ≤ b - s := min_le_right _ _
  set h := Real.exp (-(κ * d)) with hhdef
  have hh : 0 < h := Real.exp_pos _
  have hE0 : 0 ≤ E := setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_nonneg (tames_of_mul_norm_sq_le hc (hJc z hz)) (hfloer z hz)
  rcases lt_or_ge (b - s) 1 with hshort | hlong
  · -- Near the right end the closeness to `x` already gives the bound.
    exact (hclose (s, t) ⟨hs, ht⟩).trans (le_mul_exp_neg_of_lt_one (lt_min hδ₁ hδ₂).le hκ
      (by linarith) (le_max_left _ _) hL0)
  -- Otherwise use the energy of the window `[s, s + h]`, `h ≤ 1`.
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ.le hd))
  have hwab : Icc s (s + h) ⊆ Icc a b := Icc_subset_Icc hs.1 (by linarith)
  have hwin' := div_le_mul_sq_of_le_mul_exp_add_exp hκ₀ hE0 hda hdb hhdef hh1
    (hdecay hU hu hab hper hJc hJM hfloer (fun z hz ↦ (hclose z hz).trans (min_le_left _ _))
      hs.1 (by linarith) (by linarith))
  have hw (z : ℝ × ℝ) (hz : z ∈ Icc s (s + h) ×ˢ Icc 0 1) : z ∈ Icc a b ×ˢ Icc 0 1 :=
    ⟨hwab hz.1, hz.2⟩
  refine (hwin hU (hu.of_le (by norm_num)) ((prod_mono hwab le_rfl).trans hab) hh
    (fun r hr ↦ hper r (hwab hr)) (fun z hz ↦ hJc z (hw z hz)) (fun z hz ↦ hJM z (hw z hz))
    (fun z hz ↦ hfloer z (hw z hz)) (fun z hz ↦ (hclose z (hw z hz)).trans (min_le_right _ _))
    (fun z hz ↦ hL z (hw z hz)) t ht).trans ?_
  calc _ ≤ L * h + K * √(4 * (Real.exp κ₀ + 1) * E * h ^ 2) :=
        add_le_add_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hwin') hK) _
    _ = (L + K * √(4 * (Real.exp κ₀ + 1)) * √E) * h := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hh.le]
        ring
    _ ≤ (C * (1 + √E) + L) * h := by
        refine mul_le_mul_of_nonneg_right ?_ hh.le
        have hC : 0 ≤ C := le_max_of_le_left (by positivity)
        have h₁ := mul_le_mul_of_nonneg_right (le_max_right _ _ : K * √(4 * (Real.exp κ₀ + 1)) ≤ C)
          (Real.sqrt_nonneg E)
        nlinarith

end TauCeti.SymplecticForm
