/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Invertibility of `1 - f • W` on derived complete modules

Let `R` be a commutative ring, `I` an ideal of `R`, and `M` a derived `I`-complete `R`-module
(`TauCeti.IsDerivedComplete`). For any `f ∈ I` and any `R`-linear endomorphism `W : Module.End R M`,
the operator `1 - f • W` is bijective (`TauCeti.IsDerivedComplete.bijective_one_sub_smul`), hence
a unit in `Module.End R M` (`TauCeti.IsDerivedComplete.isUnit_one_sub_smul`), and likewise
`1 + f • W` is bijective (`TauCeti.IsDerivedComplete.bijective_one_add_smul`).

Injectivity follows from the injectivity of the telescope map `TauCeti.telescope M f` applied to
the orbit sequences `n ↦ (W ^ n) x` and `n ↦ (W ^ n) y`, while surjectivity follows from successive
approximation (`TauCeti.IsDerivedComplete.subset_range_of_subset_range_add_smul`) applied to
`Set.univ`, using the decomposition `x = (1 - f • W) x + f • W x`.

## Main results

* `TauCeti.IsDerivedComplete.bijective_one_sub_smul`: `1 - f • W` is bijective on a derived
  `I`-complete module for `f ∈ I`.
* `TauCeti.IsDerivedComplete.isUnit_one_sub_smul`: `1 - f • W` is a unit in `Module.End R M`.
* `TauCeti.IsDerivedComplete.bijective_one_add_smul`: `1 + f • W` is bijective on a derived
  `I`-complete module for `f ∈ I`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicComparison/Crystalline/DividedPowerEnvelope.lean`, declaration
`New.Variety.IsCompleteTorsionFree.bijective_one_sub_smul`, generalized from `p`-adically complete
`p`-torsion-free algebras to arbitrary derived `I`-complete modules over any commutative ring `R`.
-/

public section

namespace TauCeti.IsDerivedComplete

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- If `M` is derived `I`-complete and `f ∈ I`, then `1 - f • W` is bijective for every
`R`-linear endomorphism `W` of `M`. -/
theorem bijective_one_sub_smul (hM : IsDerivedComplete I M) {f : R} (hf : f ∈ I)
    (W : Module.End R M) : Function.Bijective (1 - f • W : Module.End R M) := by
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · have h_tel : telescope M f (fun n ↦ (W ^ n) x) = telescope M f (fun n ↦ (W ^ n) y) := by
      ext n
      have h_iter : (W ^ n) ((1 - f • W) x) = (W ^ n) ((1 - f • W) y) := congrArg (W ^ n) hxy
      simpa [telescope_apply, pow_succ, mul_apply_eq_comp] using h_iter
    have h0 := congrFun ((hM.bijective hf).injective h_tel) 0
    simpa using h0
  · have h_sub : (Set.univ : Set M) ⊆ LinearMap.range (1 - f • W : Module.End R M) :=
      hM.subset_range_of_subset_range_add_smul hM hf (1 - f • W) fun z _ ↦
        ⟨(1 - f • W) z, ⟨z, rfl⟩, f • W z, ⟨W z, trivial, rfl⟩, sub_add_cancel z (f • W z)⟩
    exact h_sub trivial

/-- If `M` is derived `I`-complete and `f ∈ I`, then `1 - f • W` is a unit in `Module.End R M`
for every `R`-linear endomorphism `W` of `M`. -/
theorem isUnit_one_sub_smul (hM : IsDerivedComplete I M) {f : R} (hf : f ∈ I)
    (W : Module.End R M) : IsUnit (1 - f • W : Module.End R M) := by
  let e := LinearEquiv.ofBijective (1 - f • W : Module.End R M) (hM.bijective_one_sub_smul hf W)
  exact ⟨⟨e.toLinearMap, e.symm.toLinearMap,
    LinearMap.ext e.apply_symm_apply, LinearMap.ext e.symm_apply_apply⟩, rfl⟩

/-- If `M` is derived `I`-complete and `f ∈ I`, then `1 + f • W` is bijective for every
`R`-linear endomorphism `W` of `M`. -/
theorem bijective_one_add_smul (hM : IsDerivedComplete I M) {f : R} (hf : f ∈ I)
    (W : Module.End R M) : Function.Bijective ((1 : Module.End R M) + f • W) := by
  simpa [sub_eq_add_neg, smul_neg] using hM.bijective_one_sub_smul hf (-W)

end TauCeti.IsDerivedComplete
