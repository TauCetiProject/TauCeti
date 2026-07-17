/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import TauCeti.Analysis.Contour.CauchyPrincipalValueOn
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
public import TauCeti.Analysis.Contour.Residue
public import TauCeti.Analysis.Contour.WindingNumber
import TauCeti.Analysis.Contour.ConditionDischarge
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.MeromorphicLaurent
import TauCeti.Analysis.Contour.PolarPartDecomposition
import TauCeti.Analysis.Contour.ResidueAssembly
import TauCeti.Analysis.Contour.WindingNumberReverse

/-!
# The Hungerbühler–Wasem generalized residue theorem

The summit of the contour-integration roadmap (HW Thm 3.3): for `f` holomorphic on `U ∖ S`
and meromorphic at each point of the finite `S ⊆ U`, and a **null-homologous, closed**
piecewise-`C¹` **immersion** `γ` in `U` rooted off the poles, under the regularity conditions
(A′) and (B), the set-level Cauchy principal value of `f` along `γ` exists and equals
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f` — with the generalized (non-integer) winding numbers as
weights, valid when singularities lie **on** the curve. The half-residue case
(`S = {s}`, `n_s(γ) = ½`) evaluates to `πi · Res_s f` — the on-cycle acceptance gate, and the
value the valence formula uses at `i` and `ρ`.

Both statements follow the roadmap signatures. The proof instantiates the canonical polar
decomposition, discharges the conditions into the per-pole hypotheses, and assembles the
residue sum; a reversed parametrization (`b ≤ a`) reduces to the oriented case through the
orientation lemmas, every ingredient being endpoint-swap invariant.

## Main results

* `Contour.hungerbuhlerWasem_residueTheorem` — HW Thm 3.3.
* `Contour.hasCauchyPV_half_residue` — the winding-`½` on-cycle case.

## Provenance

Migrated from `residueTheorem_crossing_paper_faithful_clean` of `MultiCrossingCPV.lean`
(re-exported as `hw_3_3_clean_full_mero` in `HW33Clean.lean`) in the AINTLIB
`LeanModularForms` development, restated for a raw curve over `[a, b]`; the basepoint
hypothesis `hγa` is that statement's `hx_notin_S`. See N. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997,
Thm 3.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- The oriented (`a ≤ b`) case of the generalized residue theorem: instantiate the canonical
polar decomposition, discharge conditions (A′) and (B) into the per-pole hypotheses, and
assemble the residue sum. -/
private theorem hungerbuhlerWasem_residueTheorem_of_le {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f S) (hB : ConditionB γ a b f) (hab : a ≤ b) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) := by
  classical
  have h_interior : ∀ s : S, ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b := fun s =>
    mem_Ioo_of_closed_of_ne hclosed fun h => hγa (h ▸ Finset.mem_coe.mpr s.2)
  have h_ord : ∀ s : S, (PolarPartDecomposition.ofMeromorphic hU hf hmero).order s
      = meromorphicPolarOrderAt f ↑s := fun s =>
    PolarPartDecomposition.ofMeromorphic_order s
  exact (PolarPartDecomposition.ofMeromorphic hU hf hmero).hasCauchyPV_residue_sum hU
    hγ_imm hab hclosed hγU hnull h_interior
    (fun s k hk1 _ => hA.flatOfOrder_of_crossing _ s s.2 hγ_imm hab (h_interior s)
      (h_ord s) k hk1)
    (fun s => hB.pow_unit_tangent_eq_of_coeff_ne_zero _ hU hSU s (hmero ↑s s.2) hγ_imm hab
      (h_interior s) (h_ord s))

/-- **The Hungerbühler–Wasem generalized residue theorem** (HW Thm 3.3): for `f` holomorphic
on `U ∖ S` and meromorphic at each point of the finite `S ⊆ U`, and a null-homologous closed
piecewise-`C¹` immersion `γ` in `U` rooted off the poles, under conditions (A′) and (B) the
set-level Cauchy principal value of `f` along `γ` is
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`, with the generalized (non-integer) winding numbers as
weights — valid when singularities of `f` lie **on** the curve. -/
theorem hungerbuhlerWasem_residueTheorem {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f S) (hB : ConditionB γ a b f) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) := by
  classical
  rcases le_total a b with hab | hba
  · exact hungerbuhlerWasem_residueTheorem_of_le hU S γ a b hγ_imm hSU hclosed hγa hγU hf
      hmero hnull hA hB hab
  · -- reduce the reversed parametrization to the oriented case on `(b, a)`
    have h_kernel_int : ∀ z ∉ U, IntervalIntegrable
        (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b := fun z hz =>
      intervalIntegrable_inv_sub_mul_deriv hγ_imm.continuousOn
        (fun t ht h_eq => hz (h_eq ▸ hγU t ht))
        hγ_imm.isPiecewiseC1On.intervalIntegrable_deriv
    have h_core := hungerbuhlerWasem_residueTheorem_of_le hU S γ b a hγ_imm.symm hSU
      hclosed.symm (fun h => hγa (hclosed ▸ h))
      (fun t ht => hγU t (by rwa [Set.uIcc_comm])) hf hmero
      (hnull.symm_of_avoidance hγU hγ_imm.continuousOn h_kernel_int)
      (conditionAprime_comm.mp hA) (conditionB_comm.mp hB) hba
    have h_exists : ∀ s ∈ S, CauchyPVExistsAt γ b a (fun w => (w - s)⁻¹) s := fun s hs =>
      (hγ_imm.symm.cauchyPVExistsAt_inv_sub hba
        (mem_Ioo_of_closed_of_ne hclosed.symm
          (fun h => hγa (hclosed ▸ h ▸ Finset.mem_coe.mpr hs))))
    have h_val : (∑ s ∈ S, windingNumber γ b a s * residue f s)
        = -∑ s ∈ S, windingNumber γ a b s * residue f s := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [windingNumber_symm (h_exists s hs)]
      ring
    have h := h_core.symm
    rw [h_val] at h
    simpa using h

/-- **Half-residue: the winding-`½` on-cycle case of HW Thm 3.3** — the `S = {s}`
specialisation: when the generalized winding number of the closed, null-homologous immersion
about the on-cycle singularity `s` is `½`, the principal value is `πi · Res_s f`. -/
theorem hasCauchyPV_half_residue {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (γ : ℝ → ℂ)
    (a b : ℝ) (s : ℂ) (hγ_imm : IsPwC1ImmersionOn γ a b) (hsU : s ∈ U)
    (hclosed : γ a = γ b) (hγa : γ a ≠ s)
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ {s}))
    (hmero : MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f {s}) (hB : ConditionB γ a b f)
    (hwind : windingNumber γ a b s = 1 / 2) :
    HasCauchyPV γ a b f ((Real.pi : ℂ) * Complex.I * residue f s) := by
  have h := hungerbuhlerWasem_residueTheorem hU {s} γ a b hγ_imm
    (by simpa using hsU) hclosed (by simpa using hγa) hγU (by simpa using hf)
    (fun s' hs' => (Finset.mem_singleton.mp hs') ▸ hmero) hnull hA hB
  rw [Finset.sum_singleton, hwind] at h
  rw [show (Real.pi : ℂ) * Complex.I * residue f s
    = 2 * (Real.pi : ℂ) * Complex.I * (1 / 2 * residue f s) by ring]
  exact h

end TauCeti.Contour

end
