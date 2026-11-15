/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic

/-!
# Floer cylinders of small energy stay near a single orbit

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H` a `C³` Hamiltonian, `1`-periodic
in time, and `J_t(x)` a `C²`, `1`-periodic family of almost complex structures tamed by `ω` on a
compact set `K`. When a sequence of Floer cylinders breaks, its energy concentrates at finitely
many levels, and between two consecutive levels it runs along a *neck*: a long window of the
cylinder carrying little energy. The levels are joined at the orbits to which the necks converge,
and this file proves the uniform estimate behind that matching.

If every `1`-periodic orbit in `K` is nondegenerate, then for every `ε > 0` there are an energy
`δ > 0` and a margin `ρ > 0` such that every Floer cylinder `u`, defined on a window
`(a, b) × ℝ` with `a + ρ ≤ b - ρ` and with loops in `K`, whose energy over `(a, b) × [0, 1]` is
less than `δ`, stays uniformly within `ε` of one single `1`-periodic orbit `x` on
`[a + ρ, b - ρ] × ℝ`
(`TauCeti.SymplecticForm.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt_of_floer`).
The constants do not depend on `u` or on the length `b - a` of the window.

The proof has three steps.

* Small energy over a window bounds the derivative of `u` away from its two ends, by the
  mean-value inequality
  (`TauCeti.SymplecticForm.exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le`).
* The energy bounds the squared `L²` norm of the defect `∂_t u - X_{H_t}(u)` of the loops from
  Hamilton's equation (`TauCeti.SymplecticForm.lintegral_norm_sq_sliceDefect_le`).
* For loops with bounded derivative and small defect, nondegenerate orbits being isolated, the
  statement is `TauCeti.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt`: every loop
  is close to some orbit, and the orbit cannot change along the connected window.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the compactness of Floer trajectories and the behaviour of
  their necks.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {K : Set V}

/-- **A Floer cylinder of small energy stays near a single orbit.** Let `H` be a `C³`,
`1`-periodic Hamiltonian and `J_t(x)` a `1`-periodic family of almost complex structures, `C²` on
an open set `W ⊆ ℝ × V` containing `ℝ × K` for a compact `K ⊆ V`, and tamed by `ω` on `ℝ × K`.
Suppose that the suspension of the Hamiltonian vector field is globally Lipschitz, so that its
evolution `φ` is defined, and that every `1`-periodic orbit `x` in `K` is nondegenerate: `x(0)` is
a nondegenerate fixed point of the time-one map `φ(0, 1)`.

Then for every `ε > 0` there are `δ > 0` and `ρ > 0` with the following property. Let `u` be `C³`
on a window `(a, b) × ℝ` with `a + ρ ≤ b - ρ`, with `1`-periodic loops `t ↦ u(s, t)` in `K`, solving
the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on `(a, b) × [0, 1]`. If the energy of
`u` over `(a, b) × [0, 1]` is less than `δ`, then there is a `1`-periodic orbit `x` in `K` such that
`u(s, t)` is within `ε` of `x(t)` for all `s ∈ [a + ρ, b - ρ]` and all `t`. -/
theorem exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt_of_floer
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ ρ > 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃a b : ℝ⦄, a + ρ ≤ b - ρ →
      ContDiffOn ℝ 3 u (Ioo a b ×ˢ univ) → (∀ s ∈ Ioo a b, Periodic (fun t ↦ u (s, t)) 1) →
      (∀ s ∈ Ioo a b, ∀ t, u (s, t) ∈ K) →
      (∀ z ∈ Ioo a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) <
          ENNReal.ofReal δ →
      ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
        (∀ t, x t ∈ K) ∧ ∀ s ∈ Icc (a + ρ) (b - ρ), ∀ t, dist (u (s, t)) (x t) < ε := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  have hX : Continuous (uncurry X) := (ω.contDiff_hamiltonianVectorField_uncurry (n := 0)
    (by simpa using (hH.of_le (by norm_num) : ContDiff ℝ 1 (uncurry H)))).continuous
  have hXper : ∀ v, Periodic (fun t ↦ X t v) 1 := fun v t ↦ by simp only [X, hHper t]
  -- Small energy over a band bounds the derivative, and the energy bounds the defect.
  obtain ⟨r, hr, ε₁, hε₁, B, hB⟩ :=
    exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le hH hHper hW hJ hJper
      hK hKW hJt
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  -- Nondegenerate orbits are isolated among the periodic orbits.
  obtain ⟨δ₀, hδ₀, η, hη, hneck⟩ :=
    exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt hK hX hXper
      (fun x hxper hx hxK ↦ (exists_pos_forall_eq_of_isNondegenerateFixedPt hL hx
        (hnd x hxper hx hxK)).imp fun _ ⟨hε, h⟩ ↦ ⟨hε, fun y hyper hy _ ↦ h y hyper hy⟩) B hε
  refine ⟨min ε₁ (δ₀ * c / (1 + M ^ 2)), by positivity, r + η, by positivity,
    fun u a b hab hu hper huK hfloer hE ↦ ?_⟩
  -- On the window shrunk by `r` the derivative is bounded by `B`.
  have hsub : Ioo (a + r) (b - r) ⊆ Ioo a b := Ioo_subset_Ioo (by linarith) (by linarith)
  have hderiv : ∀ z ∈ Ioo (a + r) (b - r) ×ˢ univ, ‖fderiv ℝ u z‖ ≤ B := by
    intro z hz
    have hwin : Icc (z.1 - r) (z.1 + r) ⊆ Ioo a b := fun s hs ↦
      ⟨by linarith [hz.1.1, hs.1], by linarith [hz.1.2, hs.2]⟩
    exact hB (p := z) isOpen_Ioo hwin hu hper huK hfloer <|
      (lintegral_mono_set (prod_mono hwin (le_refl (Icc (0 : ℝ) 1)))).trans
        (hE.le.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  -- The squared defect over the shrunk window is below `δ₀`.
  have hUsub : Ioo (a + r) (b - r) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo a b ×ˢ Icc 0 1 := prod_mono hsub le_rfl
  have hdef : ∫⁻ z in Ioo (a + r) (b - r) ×ˢ Icc 0 1,
      ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) < ENNReal.ofReal δ₀ := by
    refine (lintegral_norm_sq_sliceDefect_le (J := fun z ↦ J z.2 (u z))
      (measurableSet_Ioo.prod measurableSet_Icc) hc
      (fun z hz v ↦ (hcM z.2 _ (huK z.1 (hsub hz.1) z.2) v).1)
      (fun z hz v ↦ (hcM z.2 _ (huK z.1 (hsub hz.1) z.2) v).2)
      fun z hz ↦ hfloer z (hUsub hz)).trans_lt ?_
    calc ENNReal.ofReal ((1 + M ^ 2) / c) * ∫⁻ z in Ioo (a + r) (b - r) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)
        < ENNReal.ofReal ((1 + M ^ 2) / c) * ENNReal.ofReal (δ₀ * c / (1 + M ^ 2)) :=
          ENNReal.mul_lt_mul_right
            (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ENNReal.ofReal_ne_top
            ((lintegral_mono_set hUsub).trans_lt
              (hE.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
      _ = ENNReal.ofReal δ₀ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  obtain ⟨x, hxper, hx, hxK, hxd⟩ := hneck (a := a + r) (b := b - r) (by linarith)
    ((hu.of_le (by norm_num)).mono (prod_mono hsub le_rfl)) (fun s hs ↦ hper s (hsub hs))
    (fun s hs ↦ huK s (hsub hs)) hderiv hdef
  exact ⟨x, hxper, hx, hxK, fun s hs ↦ hxd s (by rwa [add_assoc, sub_sub])⟩

end TauCeti.SymplecticForm
