/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder

/-!
# Compactness of the capping family over compact windows of neck lengths

The unit of the pair-of-pants product is the count of negative PSS planes, and the unit property is
proved with the *capping family*: the negative plane with Hamiltonian `H_1` is glued into the input
end at `1` of the pair of pants with Hamiltonians `H_0`, `H_1`, `H_∞` along a neck of length `L`.
The result is a cylinder whose ends are the remaining input at `0` and the output at `∞`, carrying
the perturbation `K_L` with components `TauCeti.Floer.cappedCylinderComponent H L v` on the
standard cylinder `ℝ × ℝ/ℤ` (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder`).
This file proves the interior part of Gromov–Floer compactness for this family over a compact
window `C ⊆ (4, ∞)` of neck lengths, for a symplectic vector space target `(V, ω)`.

The inputs are the following.

* The data are jointly smooth in the neck length, the cylinder point and the target point
  (`TauCeti.Floer.contDiffOn_cappedCylinderComponent_family`).
* The energy over one period `ℝ × [0, 1]` of the cylinder of a solution with limiting actions
  `a_0` at `+∞` and `a_∞` at `-∞` is at most `a_0 - a_∞ + B_1 + (B_0 + B_1 + B_∞)` when
  `|H_r| ≤ B_r`, uniformly in the neck length
  (`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_cappedCylinderComponent_le`).
* The energy density of a solution of period one in `t` has period one in `t`
  (`TauCeti.SymplecticForm.periodic_floerEnergyDensity`), so its energy over `N` consecutive
  periods is at most `N` times that bound
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_cappedCylinderComponent_le`).

With these, compactness over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D` of the cylinder lying in `N` consecutive periods. The main
result, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedCylinder`)
gives a threshold `δ > 0` such that every sequence of solutions for neck lengths `Lₖ ∈ C`, for any
family of almost complex structures `J_L(z, x)` tamed by `ω` and jointly `C²` in `(L, z, x)`, with
action differences `aₖ(0) - aₖ(∞) ≤ A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V`, has a
subsequence whose neck lengths converge to some `L₀ ∈ C` and which converges locally uniformly on
`Ω` off a finite set `Z` of bubbling points, with `#Z * δ ≤ N (A + B_1 + (B_0 + B_1 + B_∞))`. The
structures are arbitrary, as for domain-dependent structures perturbed for transversality. The
regularity of the limit, the bubbles at the points of `Z`, breaking along the two ends, and the
long-neck end `L → ∞` of the family are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Hb : Puncture → ℝ → V → ℝ}

/-- **Solutions of the capping family converge off finitely many bubbling points.** Let `Hb` be
period-one `C³` Hamiltonians with `|Hb r| ≤ Bb r`, and for neck lengths `L > 4` let `J_L(z, x)` be
`ω`-tame structures, jointly `C²` in `L`, the cylinder point `z` and the target point `x`. Fix a
compact window `C ⊆ (4, ∞)` of neck lengths, a compact set `K ⊆ V` and a compact set `D` of the
cylinder lying in the `N` periods `ℝ × [m, m + N)`. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` maps of period one in `t` solving the Floer equation
`(du - X_{K_{Lₖ}})^{0,1} = 0` for the capped datum on the cylinder and the structures
`J_{Lₖ}(z, u)`, with `Lₖ ∈ C`, whose actions for `Hb ∞` tend to `a_∞(k)` as `s → -∞` and for
`Hb 0` to `a_0(k)` as `s → ∞`, with `a_0(k) - a_∞(k) ≤ A`, and with `uₖ(Ω) ⊆ K` for an open
`Ω ⊆ D`. Then there are a subsequence `φ`, a limit `L₀ ∈ C` of `L_{φ n}`, a finite set `Z ⊆ Ω`
with `#Z * δ ≤ N (A + Bb 1 + ∑ r, Bb r)`, and a continuous `v : Ω \ Z → K` such that along `φ`
every disc about a point of `Z` eventually carries Floer energy at least `δ`, the differentials
are uniformly bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on
`Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedCylinder
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) {Bb : Puncture → ℝ}
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × ((ℝ × ℝ) × V) ↦
      (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) (Ioi 4 ×ˢ univ))
    (hJt : ∀ L, 4 < L → ∀ z x, ω.Tames (J L z x)) {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V}
    (hC : IsCompact C) (hC₄ : C ⊆ Ioi 4) (hD : IsCompact D) (hK : IsCompact K) {m : ℤ} {N : ℕ}
    (hDN : D ⊆ (univ : Set ℝ) ×ˢ Ico (m : ℝ) (m + N)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a_inf : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (L k) z (u k z))
        (ω.perturbedFDeriv (cappedCylinderComponent Hb (L k) 1)
          (cappedCylinderComponent Hb (L k) I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u k (s, t))) atBot
        (𝓝 (a_inf k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u k (s, t))) atTop
        (𝓝 (a₀ k))) →
      (∀ k, a₀ k - a_inf k ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (L₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ L₀ ∈ C ∧
        Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ N * (A + Bb one + ∑ r, Bb r) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (cappedCylinderComponent Hb (L (φ n)) 1) (cappedCylinderComponent Hb (L (φ n)) I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun L z x ↦ cappedCylinderComponent Hb L 1 z x)
    (Kt := fun L z x ↦ cappedCylinderComponent Hb L I z x) (J := J)
    (isOpen_Ioi.prod isOpen_univ) (contDiffOn_cappedCylinderComponent_family hHb hHbs 1)
    (contDiffOn_cappedCylinderComponent_family hHb hHbs I) hJ hC hD hK
    (prod_mono hC₄ (subset_univ _)) fun L hL z _ x _ ↦ hJt L (hC₄ hL) z x
  refine ⟨δ, hδ, fun Ω L u a₀ a_inf A hΩ hΩD hLC hu hper hfl hinf h₀ hA huK ↦ ?_⟩
  have hHbs₁ (r : Puncture) : ContDiff ℝ 1 (uncurry (Hb r)) := (hHbs r).of_le (by norm_num)
  have hL (k : ℕ) : 4 < L k := hC₄ (hLC k)
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity (cappedCylinderComponent Hb (L k) 1)
      (cappedCylinderComponent Hb (L k) I) (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt _ (hL k) _ _) (hfl k z)
  -- The action bound `a_∞ ≤ a_0 + Bb 1 + ∑ r, Bb r` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + Bb one + ∑ r, Bb r := by
    have h := le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent ω hHb hHbs₁
      (hL 0) hBb isOpen_univ ((hu 0).contDiffOn.of_le (by norm_num)) (subset_univ _)
      (fun s ↦ by simpa using hper 0 s 0)
      (fun z _ ↦ hJt _ (hL 0) _ _) (fun z _ ↦ hfl 0 z) (hinf 0) (h₀ 0)
    linarith [hA 0]
  -- The energy over `Ω` is at most `N` times the energy bound over one period.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity
      (cappedCylinderComponent Hb (L k) 1) (cappedCylinderComponent Hb (L k) I) (u k) z) ≤
      ENNReal.ofReal (N * (A + Bb one + ∑ r, Bb r)) :=
    (setLIntegral_floerEnergyDensity_cappedCylinderComponent_le ω hHb hHbs₁ (hL k) hBb isOpen_univ
      ((hu k).contDiffOn.of_le (by norm_num)) (subset_univ _) (hper k) (fun z _ ↦ hJt _ (hL k) _ _)
      (fun z _ ↦ hfl k z) (hinf k) (h₀ k) (hΩD.trans hDN)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hA k])
        (Nat.cast_nonneg N)))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb (L k) 1)
      (cappedCylinderComponent Hb (L k) I) (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_univ ((hu k).contDiffOn.of_le (by norm_num))
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs₁ (hL k) 1).contDiffOn
      (contDiff_uncurry_cappedCylinderComponent hHb hHbs₁ (hL k) I).contDiffOn).mono
        (subset_univ Ω)).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact hconv hΩ hΩD hLC (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)
      (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg N) hE0) (hlin k)

end TauCeti.SymplecticForm
