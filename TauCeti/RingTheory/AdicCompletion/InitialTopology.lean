/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

import TauCeti.Topology.Discrete

/-!
# Adic topology on completions as an initial topology of discrete quotients

When `I` is a finitely generated ideal of a commutative ring `R`, the kernel of the evaluation map
`AdicCompletion I R → R ⧸ I ^ n` is the `n`-th power of the extended ideal
`I · AdicCompletion I R` (`AdicCompletion.ker_evalₐ_eq_map_pow`). Combining this with
`Ideal.adicTopology_eq_iInf_induced` and `Ideal.adicTopology_eq_iInf_induced_pow` shows that the
adic topology of the extended ideal on `AdicCompletion I R` coincides with the inverse-limit
topology induced by the evaluations into the discrete quotients `R ⧸ I ^ (n + 1)` (or `R ⧸ I ^ n`).
This identifies the topology on basic open sections of the formal spectrum with the adic topology
of completed localisations.

## Main results

* `AdicCompletion.adicTopology_map_eq_iInf_induced`,
  `AdicCompletion.adicTopology_map_eq_iInf_induced_pow`: for finitely generated `I`, the adic
  topology of `I · AdicCompletion I R` is the initial topology of the evaluation maps
  `AdicCompletion I R → R ⧸ I ^ (n + 1)` (respectively `R ⧸ I ^ n`).

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 12.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2 (7.2.1–7.2.2).
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

private theorem induced_mk_map_pow_eq_induced_evalₐ (fg : I.FG) (n : ℕ) :
    TopologicalSpace.induced
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)) ⊥ =
      TopologicalSpace.induced (evalₐ I n) ⊥ := by
  have hfun : (evalₐ I n : AdicCompletion I R → R ⧸ I ^ n) =
      (quotientMapPowAlgEquiv fg n ∘ Ideal.quotEquivOfEq (Ideal.map_pow _ I n).symm) ∘
        Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) := by
    ext x
    simp [Function.comp_apply, Ideal.quotEquivOfEq_mk]
  rw [hfun, ← induced_compose,
    TauCeti.induced_bot_of_injective
      ((quotientMapPowAlgEquiv fg n).injective.comp (Ideal.quotEquivOfEq _).injective)]

/-- For a finitely generated ideal `I`, the adic topology of the extended ideal
`I · AdicCompletion I R` is the initial topology induced by the evaluation maps
`AdicCompletion I R → R ⧸ I ^ (n + 1)` into the discrete quotients. -/
theorem adicTopology_map_eq_iInf_induced (fg : I.FG) :
    (I.map (algebraMap R (AdicCompletion I R))).adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (evalₐ I (n + 1)) ⊥ := by
  rw [Ideal.adicTopology_eq_iInf_induced]
  exact iInf_congr fun n ↦ induced_mk_map_pow_eq_induced_evalₐ fg (n + 1)

/-- For a finitely generated ideal `I`, the adic topology of the extended ideal
`I · AdicCompletion I R` is the initial topology induced by all evaluation maps
`AdicCompletion I R → R ⧸ I ^ n` into the discrete quotients. -/
theorem adicTopology_map_eq_iInf_induced_pow (fg : I.FG) :
    (I.map (algebraMap R (AdicCompletion I R))).adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (evalₐ I n) ⊥ := by
  rw [Ideal.adicTopology_eq_iInf_induced_pow]
  exact iInf_congr fun n ↦ induced_mk_map_pow_eq_induced_evalₐ fg n

end AdicCompletion
