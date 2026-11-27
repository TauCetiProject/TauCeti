/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Lp.C0Ideal
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Module.Dual.Quotient

/-!
# A norm-one functional annihilating the `c₀` ideal

`lp.exists_dual_infty_annihilates_c0` gives a normalized functional on bounded scalar
families that vanishes on families vanishing at infinity. It uses Mathlib's
`exists_dual_vector` and Tau Ceti's `lp.norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one` and
`Submodule.quotientDualEquivAnnihilator`.

This functional can be used to produce a nonzero rank-one operator on bounded sequences
that kills every finitely supported sequence.

## References

* J. van Neerven, *Functional Analysis*, §4.2, for Hahn–Banach.
-/

public section

open scoped ENNReal

namespace lp

/-- On bounded real or complex families indexed by an infinite type, there is a continuous
linear functional of norm one that sends the constant family `1` to `1` and vanishes on
`lp.c0Ideal`. This is an application of Hahn–Banach (van Neerven, *Functional Analysis*, §4.2)
to the class of the constant family in the quotient. -/
theorem exists_dual_infty_annihilates_c0 (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Infinite ι] :
    ∃ φ : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) ∞), ‖φ‖ = 1 ∧ φ 1 = 1 ∧
      ∀ a ∈ c0Ideal (fun _ : ι ↦ 𝕜), φ a = 0 := by
  let I := c0Ideal (fun _ : ι ↦ 𝕜)
  let S : Submodule 𝕜 (lp (fun _ : ι ↦ 𝕜) ∞) := I.asIdeal.restrictScalars 𝕜
  let u : lp (fun _ : ι ↦ 𝕜) ∞ := 1
  have hnorm : ‖(Submodule.Quotient.mk u : _ ⧸ S)‖ = 1 :=
    (congrArg norm (TwoSidedIdeal.Quotient.idealQuotientMk_asIdeal_eq_mk I u)).trans
      (norm_mk_c0Ideal_eq_one_of_forall_norm_eq_one u (fun _ ↦ by
        simp only [u, infty_coeFn_one, Pi.one_apply, norm_one]))
  obtain ⟨ψ, hψnorm, hψu⟩ :=
    exists_dual_vector 𝕜 (Submodule.Quotient.mk u : _ ⧸ S) (by rw [hnorm]; exact one_ne_zero)
  refine ⟨S.quotientDualEquivAnnihilator ψ, ?_, ?_, ?_⟩
  · exact (S.quotientDualEquivAnnihilator.norm_map ψ).trans hψnorm
  · rw [Submodule.quotientDualEquivAnnihilator_apply]
    exact hψu.trans (by rw [hnorm, RCLike.ofReal_one])
  · intro a ha
    have haS : a ∈ S := (Submodule.restrictScalars_mem 𝕜 I.asIdeal a).2
      (TwoSidedIdeal.mem_asIdeal.2 ha)
    simpa only [LinearMap.flip_apply, topDualPairing_apply] using
      (Submodule.mem_orthogonalBilin.1 (S.quotientDualEquivAnnihilator ψ).property) a haS

end lp
