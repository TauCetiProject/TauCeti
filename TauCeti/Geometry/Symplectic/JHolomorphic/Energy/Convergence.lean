/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Bubbling
public import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Sequences

/-!
# Compact convergence away from bubbling points

A sequence of pseudoholomorphic curves on an open subset of `ℂ`, with uniformly bounded
energy and image in a fixed compact target set, has a subsequence converging locally uniformly
off a finite set. The same subsequence retains energy concentration at each exceptional point
and uniform derivative bounds on every compact subset of the complement.

The finite-set and derivative estimates come from
`TauCeti.exists_pos_forall_exists_strictMono_finset_norm_fderiv_le`. The mean-value inequality
turns the derivative bounds into equicontinuity on the complement, and Arzelà–Ascoli in the
compact-open topology extracts a single subsequence valid on all compact subsets at once.
The limit is continuous and takes values in the original compact target set. This result does
not assert differentiability of the limit or construct rescaled bubbles; those require further
elliptic estimates and rescaling arguments.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.6.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V}

/-- Bounded-energy pseudoholomorphic curves with compact target image have a subsequence
converging locally uniformly off finitely many energy-concentration points. The energy
threshold depends only on the almost complex structure and the compact target set. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
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
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  classical
  obtain ⟨δ, hδ, hδprop⟩ :=
    exists_pos_forall_exists_strictMono_finset_norm_fderiv_le hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun Ω u E hΩ hu hCR huK hint hE ↦ ?_⟩
  obtain ⟨ψ, hψ, Z, hZΩ, hZE, hconc, hb⟩ := hδprop hΩ hu hCR huK hint hE
  let D : Set ℂ := Ω \ ↑Z
  have hD : IsOpen D := hΩ.sdiff Z.finite_toSet.isClosed
  let : LocallyCompactSpace D := hD.locallyCompactSpace
  have hequi : EquicontinuousOn (fun n ↦ u (ψ n)) D :=
    equicontinuousOn_of_forall_isCompact_norm_fderiv_le hD
      (fun n ↦ ((hu (ψ n)).differentiableOn (by norm_num)).mono sdiff_subset) hb
  let U : ℕ → C(D, V) := fun n ↦
    ⟨D.domRestrict (u (ψ n)), (hequi.continuousOn n).domRestrict⟩
  have hcompact : IsCompact (closure (range U)) :=
    ArzelaAscoli.isCompact_closure_of_equicontinuous (by
      rw [← Set.comp_rangeSplitting U]
      exact (equicontinuous_restrict_iff _).mpr hequi |>.comp (Set.rangeSplitting U))
      (fun x ↦ ⟨K, hK, by
        rintro _ ⟨n, rfl⟩
        exact huK (ψ n) x.2.1⟩)
  obtain ⟨a, -, χ, hχ, hlim⟩ := hcompact.tendsto_subseq (x := U)
    (fun n ↦ subset_closure (mem_range_self n))
  -- Extend by zero only to express convergence on a subset of the original domain.
  let v : ℂ → V := fun z ↦ if hz : z ∈ D then a ⟨z, hz⟩ else 0
  have hv : v ∘ (Subtype.val : D → ℂ) = fun x : D ↦ a x := by
    funext x
    simp [v, x.2]
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ u (ψ (χ n))) v atTop D := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hv]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  refine ⟨ψ ∘ χ, Z, v, hψ.comp hχ, hZΩ, hZE, ?_, ?_, ?_, ?_, hconv⟩
  · intro z hz ε hε
    exact hχ.tendsto_atTop.eventually (hconc z hz ε hε)
  · intro C hC hCD
    obtain ⟨M, hM⟩ := hb C hC hCD
    exact ⟨M, fun n ↦ hM (χ n)⟩
  · exact hconv.continuousOn (Eventually.of_forall fun n ↦
      (hu (ψ (χ n))).continuousOn.mono sdiff_subset).frequently
  · intro z hz
    exact hK.isClosed.mem_of_tendsto (hconv.tendsto_at hz)
      (Eventually.of_forall fun n ↦ huK (ψ (χ n)) hz.1)

end TauCeti
