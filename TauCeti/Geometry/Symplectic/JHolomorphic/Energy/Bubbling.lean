/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Quantization
public import TauCeti.MeasureTheory.Integral.EnergyConcentration

/-!
# Finitely many bubbling points

Let `J` be a `C²` almost complex structure, written as a matrix-valued function
`J : V → (V →L[ℝ] V)` on an open set `W` of a real inner product space, and let `K ⊆ W` be
compact. Consider a sequence of solutions `uₖ : ℂ → V` of the Cauchy--Riemann equation
`∂ₜu = J(u) ∂ₛu` on an open set `Ω ⊆ ℂ`, with image in `K` and energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`.

This file proves the first step of Gromov compactness for such a sequence. There is a threshold
`δ > 0`, depending only on `J` and `K`, such that after passing to a subsequence the differentials
`duₖ` are uniformly bounded on every compact subset of `Ω` off a finite set `Z ⊆ Ω` of *bubbling
points*, with `#Z ≤ E / δ`. At every point of `Z` energy at least `δ` concentrates: for each
`ε > 0`, the disk of radius `ε` about it eventually carries energy at least `δ`.

The threshold is that of the energy concentration theorem
`TauCeti.exists_pos_forall_eventually_le_setIntegral_norm_fderiv_one_sq_ball`: wherever the
differentials blow up, every small disk eventually carries energy at least `δ`. The counting
argument that turns this into finitely many blow-up points is
`TauCeti.exists_strictMono_finset_forall_le_of_concentration`.

Off `Z`, these uniform bounds are the input for Arzelà--Ascoli, which extracts a subsequence
converging uniformly on compact sets. That extraction, the elliptic regularity that upgrades it to
`C^∞` convergence to a `J`-holomorphic limit, and the rescaling that produces bubbles at the
points of `Z` are not carried out here.

## Main results

* `TauCeti.exists_pos_forall_exists_strictMono_finset_norm_fderiv_le`: a sequence of
  `J`-holomorphic curves with bounded energy has a subsequence whose differentials are uniformly
  bounded on compact sets off finitely many bubbling points, each carrying energy at least `δ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.6 (the finite set of points at which the
  derivatives of a sequence of curves with bounded energy blow up).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V}

/-- **Finitely many bubbling points.** Let `J` be `C²` on an open set `W` containing a compact
set `K`, with `J(x)² = -1` on `K`. There is a threshold `δ > 0` with the following property. Let
`uₖ` be `C³` solutions of `∂ₜu = J(u) ∂ₛu` on an open set `Ω ⊆ ℂ`, with image in `K`, integrable
energy density on `Ω`, and energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`. Then there are a subsequence `φ` and a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E` such that, along `φ`, every disk about a point of `Z`
eventually carries energy at least `δ`, and the differentials `du_{φ n}` are uniformly bounded on
every compact subset of `Ω \ Z`. -/
theorem exists_pos_forall_exists_strictMono_finset_norm_fderiv_le
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I = J (u k y) (fderiv ℝ (u k) y 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset ℂ, ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        ∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M := by
  obtain ⟨δ, hδ, hconc⟩ :=
    exists_pos_forall_eventually_le_setIntegral_norm_fderiv_one_sq_ball hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun Ω u E hΩ hu hCR huK hint hE ↦ ?_⟩
  refine exists_strictMono_finset_forall_le_of_concentration hΩ.measurableSet hδ
    (fun k ↦ ((hu k).continuousOn_fderiv_of_isOpen hΩ (by norm_num)).norm)
    (fun k y _ ↦ sq_nonneg _) hint hE ?_
  -- A blow-up point `z₀` is the centre of a disk `B_r(z₀) ⊆ Ω`, on which the energy
  -- concentration theorem applies; the energy of `B_{min ε r}(z₀)` bounds that of `B_ε(z₀) ∩ Ω`.
  intro φ _ z z₀ _ hz₀ hz hblow ε hε
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  filter_upwards [hconc (u := fun n ↦ u (φ n)) (fun n ↦ (hu (φ n)).mono hrΩ)
    (fun n y hy ↦ hCR (φ n) y (hrΩ hy)) (fun n ↦ (huK (φ n)).mono_left hrΩ)
    (fun n ↦ (hint (φ n)).mono_set hrΩ) hz hblow (min ε r) (lt_min hε hr) (min_le_right _ _)]
    with n hn
  have hsub : ball z₀ (min ε r) ⊆ ball z₀ ε ∩ Ω :=
    subset_inter (ball_subset_ball (min_le_left _ _))
      ((ball_subset_ball (min_le_right _ _)).trans hrΩ)
  exact hn.trans (setIntegral_mono_set ((hint (φ n)).mono_set inter_subset_right)
    (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ.measurableSet)
      fun _ _ ↦ sq_nonneg _) hsub.eventuallyLE)

end TauCeti
