/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Trajectory
import TauCeti.Geometry.Symplectic.Hamiltonian.SmallPeriodicOrbit

/-!
# The energy of Floer trajectories of small autonomous Hamiltonians

Let `(V, ω)` be a symplectic vector space, `F : V → ℝ` a `C²` function and `K ⊆ V` a compact
set. For a real number `ε`, the Floer trajectories of the autonomous Hamiltonian `ε F` are the
solutions `u : ℝ × ℝ → V` of `∂_s u + J (∂_t u - ε X_F(u)) = 0` with `1`-periodic loops, for
uniformly tame almost complex structures `J z`. When `F` is a Morse function and `ε` is small,
these are the cylinders whose counts are compared with the Morse trajectories of `F`.

This file shows that for `ε` small, depending only on `ω`, `F` and `K`, the limiting actions at
the two ends of every finite-energy Floer trajectory of `ε F` with loops in `K` are `ε F(x₀)` and
`ε F(x₁)` for rest points `x₀`, `x₁ ∈ K` of the Hamiltonian vector field of `ε F`, that is,
critical points of `F` when `ε ≠ 0`, and that its energy is

`E(u) = ε (F(x₁) - F(x₀))`

(`TauCeti.SymplecticForm.exists_pos_forall_lintegral_floerEnergyDensity_const_mul_eq`). In
particular the energy of such trajectories is at most `|ε|` times the oscillation of `F` on `K`,
so for every `δ > 0` it is at most `δ` once `ε` is small enough
(`TauCeti.SymplecticForm.exists_pos_forall_lintegral_floerEnergyDensity_const_mul_le`). No energy
bound is assumed beyond finiteness, and `J` may depend on the domain point.

Two inputs combine. The limiting actions at the two ends of a finite-energy Floer trajectory are
realized by `1`-periodic orbits in `K`, and its energy is the difference of their actions
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`). The
`1`-periodic orbits of `ε F` in `K` are constant once `ε` is small
(`TauCeti.SymplecticForm.exists_pos_forall_eq_const_of_periodic_hamiltonianVectorField_const_mul`,
by Yorke's period bound). The action of the constant loop at `x` is `ε F(x)`
(`TauCeti.SymplecticForm.hamiltonianAction_const`).

On a closed manifold the corresponding statement about the `1`-periodic orbits of `ε F` is
`exists_pos_forall_periodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`. The statements here are for a symplectic vector
space, the local model of a symplectic manifold.

## Main results

* `TauCeti.SymplecticForm.exists_pos_forall_lintegral_floerEnergyDensity_const_mul_eq`: for small
  `ε`, the loop actions of a finite-energy Floer trajectory of `ε F` in `K` tend to `ε F(x₀)` and
  `ε F(x₁)` for rest points `x₀`, `x₁` of the field of `ε F`, and its energy is
  `ε (F(x₁) - F(x₀))`.
* `TauCeti.SymplecticForm.exists_pos_forall_lintegral_floerEnergyDensity_const_mul_le`: for every
  `δ > 0` and small `ε`, such trajectories have energy at most `δ`.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the Floer trajectories of a `C²`-small Hamiltonian.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  **22** (1969), 509–512.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {F : V → ℝ} {K : Set V}

/-- **The energy of a Floer trajectory of a small autonomous Hamiltonian.** Let `F` be a `C²`
function and `K` a compact set. There is `ε₀ > 0` such that for `|ε| < ε₀` the following holds.
Let `u` be a `C²` solution of the Floer equation `∂_s u + J (∂_t u - ε X_F(u)) = 0` on
`ℝ × [0, 1]`, with `1`-periodic loops in `K`, uniformly tame almost complex structures and finite
energy. Then there are rest points `x₀`, `x₁ ∈ K` of the Hamiltonian vector field of `ε F` (for
`ε ≠ 0`, critical points of `F`) such that the actions of the loops of `u` tend to `ε F(x₀)` as
`s → -∞` and to `ε F(x₁)` as `s → ∞`, and the energy of `u` is `ε (F(x₁) - F(x₀))`. -/
theorem exists_pos_forall_lintegral_floerEnergyDensity_const_mul_eq (hF : ContDiff ℝ 2 F)
    (hK : IsCompact K) :
    ∃ ε₀ > (0 : ℝ), ∀ ⦃ε : ℝ⦄, |ε| < ε₀ → ∀ ⦃u : ℝ × ℝ → V⦄
      ⦃J : ℝ × ℝ → AlmostComplexStructure V⦄ ⦃c M : ℝ⦄, ContDiff ℝ 2 u →
      (∀ s, Periodic (fun t ↦ u (s, t)) 1) → (∀ s t, u (s, t) ∈ K) → 0 < c →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z) ≠ ⊤ →
      ∃ x₀ ∈ K, ∃ x₁ ∈ K, ω.hamiltonianVectorField (fun x ↦ ε * F x) x₀ = 0 ∧
        ω.hamiltonianVectorField (fun x ↦ ε * F x) x₁ = 0 ∧
        Tendsto (fun s ↦ ω.hamiltonianAction (fun _ x ↦ ε * F x) (fun t ↦ u (s, t))) atBot
          (𝓝 (ε * F x₀)) ∧
        Tendsto (fun s ↦ ω.hamiltonianAction (fun _ x ↦ ε * F x) (fun t ↦ u (s, t))) atTop
          (𝓝 (ε * F x₁)) ∧
        ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
            ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z) =
          ENNReal.ofReal (ε * (F x₁ - F x₀)) := by
  obtain ⟨ε₀, hε₀, hconst⟩ :=
    exists_pos_forall_eq_const_of_periodic_hamiltonianVectorField_const_mul (ω := ω) hF
      hK.isBounded
  refine ⟨ε₀, hε₀, fun ε hε u J c M hu hper huK hc hJc hJM hfloer hE ↦ ?_⟩
  have hH : ContDiff ℝ 1 (uncurry fun (_ : ℝ) (x : V) ↦ ε * F x) :=
    contDiff_const.mul ((hF.of_le one_le_two).comp contDiff_snd)
  obtain ⟨x₀, x₁, ⟨hx₀per, hx₀, hx₀K⟩, ⟨hx₁per, hx₁, hx₁K⟩, hbot, htop, hEeq⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq (H := fun _ x ↦ ε * F x) hH
      (fun _ ↦ rfl) hu hper hK huK hc hJc hJM hfloer hE
  -- For small `ε` both end orbits are constant, so they rest at zeros of the field ...
  have h₀ := hconst hε hx₀per hx₀ hx₀K
  have h₁ := hconst hε hx₁per hx₁ hx₁K
  have hzero {x : ℝ → V}
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ ε * F y) (x t)) t)
      (h : x = fun _ ↦ x 0) : ω.hamiltonianVectorField (fun y ↦ ε * F y) (x 0) = 0 := by
    have h0 := hx 0
    rw [h] at h0
    exact h0.unique (hasDerivAt_const _ _)
  -- ... and the action of the constant loop at `p` is `ε F(p)`.
  have haction {x : ℝ → V} (h : x = fun _ ↦ x 0) :
      ω.hamiltonianAction (fun _ y ↦ ε * F y) x = ε * F (x 0) := by
    rw [h]
    simp
  rw [haction h₀] at hbot
  rw [haction h₁] at htop
  rw [haction h₀, haction h₁, ← mul_sub] at hEeq
  exact ⟨x₀ 0, hx₀K 0, x₁ 0, hx₁K 0, hzero hx₀ h₀, hzero hx₁ h₁, hbot, htop, hEeq⟩

/-- **Floer trajectories of small autonomous Hamiltonians have small energy.** Let `F` be a `C²`
function, `K` a compact set and `δ > 0`. There is `ε₀ > 0` such that for `|ε| < ε₀` every `C²`
finite-energy solution `u` of the Floer equation `∂_s u + J (∂_t u - ε X_F(u)) = 0` on
`ℝ × [0, 1]`, with `1`-periodic loops in `K` and uniformly tame almost complex structures, has
energy at most `δ`. -/
theorem exists_pos_forall_lintegral_floerEnergyDensity_const_mul_le (hF : ContDiff ℝ 2 F)
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ > (0 : ℝ), ∀ ⦃ε : ℝ⦄, |ε| < ε₀ → ∀ ⦃u : ℝ × ℝ → V⦄
      ⦃J : ℝ × ℝ → AlmostComplexStructure V⦄ ⦃c M : ℝ⦄, ContDiff ℝ 2 u →
      (∀ s, Periodic (fun t ↦ u (s, t)) 1) → (∀ s t, u (s, t) ∈ K) → 0 < c →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z) ≠ ⊤ →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * F x) u z) ≤
          ENNReal.ofReal δ := by
  obtain ⟨ε₀, hε₀, henergy⟩ :=
    exists_pos_forall_lintegral_floerEnergyDensity_const_mul_eq (ω := ω) hF hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  refine ⟨min ε₀ (δ / (2 * |B| + 1)), lt_min hε₀ (by positivity),
    fun ε hε u J c M hu hper huK hc hJc hJM hfloer hE ↦ ?_⟩
  obtain ⟨x₀, hx₀, x₁, hx₁, -, -, -, -, hEeq⟩ :=
    henergy (hε.trans_le (min_le_left _ _)) hu hper huK hc hJc hJM hfloer hE
  rw [hEeq]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `ε (F(x₁) - F(x₀)) ≤ |ε| (|F(x₁)| + |F(x₀)|) ≤ |ε| (2 |B| + 1) ≤ δ`.
  have hεδ : |ε| * (2 * |B| + 1) < δ :=
    (lt_div_iff₀ (by positivity)).1 (hε.trans_le (min_le_right _ _))
  have hF₀ : |F x₀| ≤ |B| := (Real.norm_eq_abs _ ▸ hB x₀ hx₀).trans (le_abs_self B)
  have hF₁ : |F x₁| ≤ |B| := (Real.norm_eq_abs _ ▸ hB x₁ hx₁).trans (le_abs_self B)
  calc ε * (F x₁ - F x₀) ≤ |ε| * (|F x₁| + |F x₀|) :=
        (le_abs_self _).trans ((abs_mul _ _).trans_le
          (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ε)))
    _ ≤ |ε| * (2 * |B| + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ε)
    _ ≤ δ := hεδ.le

end TauCeti.SymplecticForm
