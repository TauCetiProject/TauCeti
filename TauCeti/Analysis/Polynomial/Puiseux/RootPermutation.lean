/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Conjugation

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.Covering.PowerSubstitution

/-!
# The conjugation permutation of power-substituted root labels

Let `F` be a family of complex polynomials over `U × ball 0 R` whose coefficients respect a
parameter involution `τ` together with complex conjugation of the disc coordinate, and whose
leading coefficient does not vanish off the hyperplane `t = 0`. After the power substitution
`t = s ^ n`, a complete distinct labelling of the roots by continuous functions on the punctured
product `U × (ball 0 R' \ {0})` is permuted by conjugation according to one unique involutive
permutation of the labels.

This specialises `TauCeti.existsUnique_root_conj_perm_of_subset_closure`: the punctured product
is connected when `U` is, so a single permutation serves at every parameter. The labels only need
to be continuous; the base `U` only needs to be connected, not simply connected. The nonmonic
and Laurent Puiseux constructions and the root-difference symmetry apply it to the analytic
labels they build.
-/

public section

open Function Metric Polynomial Set ComplexConjugate

namespace TauCeti.Polynomial

variable {E : Type*} [TopologicalSpace E] {U : Set E} [ConnectedSpace U] {F : E × ℂ → ℂ[X]}
  {d n : ℕ} {R R' : ℝ} {τ : E → E}

/-- The conjugation symmetry of continuous punctured root labels of a power-substituted family
is carried by a unique involutive permutation of the labels. The base needs only to be
connected, and the leading coefficient only nonzero off the hyperplane. -/
theorem existsUnique_root_conj_perm_of_powerSubstitution (hR' : 0 < R') (hn : n ≠ 0)
    (hR : R' ^ n ≤ R) (hl : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).coeff d ≠ 0)
    (hτ : ContinuousOn τ U) (hτU : MapsTo τ U U) (hττ : ∀ x ∈ U, τ (τ x) = x)
    (hconj : ∀ b ∈ U ×ˢ (ball 0 R \ {0}),
      F (τ b.1, conj b.2) = (F b).map (starRingEnd ℂ))
    {r : Fin d → E × ℂ → ℂ} (hrc : ∀ i, ContinuousOn (r i) (U ×ˢ (ball 0 R' \ {0})))
    (hr : ∀ b ∈ U ×ˢ (ball 0 R' \ {0}), Injective (fun i ↦ r i b) ∧
      F (b.1, b.2 ^ n) = C ((F (b.1, b.2 ^ n)).coeff d) * ∏ i, (X - C (r i b))) :
    ∃! σ : Equiv.Perm (Fin d), Involutive σ ∧
      ∀ i b, b ∈ U ×ˢ (ball 0 R' \ {0}) → r (σ i) b = conj (r i (τ b.1, conj b.2)) := by
  let S := U ×ˢ (ball (0 : ℂ) R' \ {0})
  let κ : E × ℂ → E × ℂ := fun b ↦ (τ b.1, conj b.2)
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hST : S ⊆ U ×ˢ ball (0 : ℂ) R' := prod_mono subset_rfl sdiff_subset
  have hq : MapsTo q S (U ×ˢ (ball 0 R \ {0})) :=
    (mapsTo_id U).prodMap (mapsTo_pow_ball_zero_diff_singleton hn hR)
  obtain ⟨hκ, -, hκS⟩ := TauCeti.continuousOn_mapsTo_prodMap_conj hτ hτU
  have hroot (b : E × ℂ) (hb : b ∈ S) (z : ℂ) :
      (F (q b)).IsRoot z ↔ ∃ i, r i b = z := by
    rw [(hr b hb).2, isRoot_C_mul_prod_X_sub_C_iff (hl _ (hq hb))]
    simp only [Finset.mem_univ, true_and]
  -- The punctured product is connected, so conjugation uses one permutation of all labels.
  have hSc : IsConnected S := (isConnected_iff_connectedSpace.2 inferInstance).prod
    (isConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex]) (0 : ℂ) hR')
  exact TauCeti.existsUnique_root_conj_perm_of_subset_closure
    hSc.isPreconnected subset_rfl subset_closure hrc (fun b hb ↦ (hr b hb).1) hroot
    (hκ.mono hST) hκS hκS (fun b hb ↦ Prod.ext (hττ b.1 hb.1) (Complex.conj_conj b.2))
    (fun b hb ↦ by simpa only [q, κ, map_pow] using hconj _ (hq hb))
    ⟨_, hSc.nonempty.some_mem⟩

end TauCeti.Polynomial
