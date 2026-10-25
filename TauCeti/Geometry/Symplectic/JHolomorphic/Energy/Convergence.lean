/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Bubbling
public import TauCeti.Analysis.Calculus.FDeriv.Compactness

/-!
# Locally uniform convergence away from bubbling points

A bounded-energy sequence of pseudoholomorphic curves with image in a fixed compact set has a
subsequence converging locally uniformly off a finite set of energy concentration points. The
limit is continuous and remains in the same compact target set. The finite set retains its
quantitative cardinality bound, and energy still concentrates at each of its points along the
final subsequence. The differentials remain uniformly bounded on compact subsets of the
complement, providing the estimates needed for subsequent elliptic arguments.

This combines the finite concentration set and differential bounds of
`TauCeti.exists_pos_forall_exists_strictMono_finset_norm_fderiv_le` with compact-open
Arzelà–Ascoli, via local bounds on the differentials. The domain may be any open subset of the
complex plane. The almost complex structure may vary with the image point; neither tameness
nor compatibility is needed.

This is only the continuous compactness step. It does not assert that the limit is
pseudoholomorphic, that the convergence is smooth, or that the concentration points support
holomorphic bubbles. Those conclusions require further elliptic and rescaling arguments.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.6.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : V → V →L[ℝ] V} {W K : Set V}

/-- **Continuous compactness away from finitely many bubbling points.** Bounded energy and a
compact target image give a locally uniformly convergent subsequence off a finite set. The
limit stays in the compact target. Each exceptional point carries energy at least `δ`, and
their number is bounded by the total energy divided by `δ`. The differentials along the final
subsequence remain locally uniformly bounded off the exceptional set. No equation for the
limit is asserted. -/
theorem exists_pos_forall_exists_tendstoLocallyUniformlyOn_off_finset
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I = J (u k y) (fderiv ℝ (u k) y 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset ℂ) (v : ℂ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        IsLocallyBoundedOn (fun n ↦ fderiv ℝ (u (φ n))) (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_pos_forall_exists_strictMono_finset_norm_fderiv_le hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun Ω u E hΩ hu hCR huK hint hE ↦ ?_⟩
  obtain ⟨φ, hφ, Z, hZΩ, hZE, hconc, hderiv⟩ := hbound hΩ hu hCR huK hint hE
  have hU : IsOpen (Ω \ (↑Z : Set ℂ)) := hΩ.sdiff Z.finite_toSet.isClosed
  have hb : IsLocallyBoundedOn (fun n ↦ fderiv ℝ (u (φ n))) (Ω \ ↑Z) :=
    isLocallyBoundedOn_def.mpr fun C hCU hC ↦ hderiv C hC hCU
  obtain ⟨ψ, v, hψ, hv, hvK, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_of_isLocallyBoundedOn_fderiv hU
      (fun n ↦ ((hu (φ n)).differentiableOn (by norm_num)).mono sdiff_subset) hb hK
      (fun n ↦ (huK (φ n)).mono_left sdiff_subset)
  exact ⟨φ ∘ ψ, Z, v, hφ.comp hψ, hZΩ, hZE,
    fun z hz ε hε ↦ hψ.tendsto_atTop.eventually (hconc z hz ε hε), hv, hvK, hb.comp ψ, hconv⟩

end TauCeti
