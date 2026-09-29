/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Filtration
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Local nilpotence of the higher bar perturbation

The higher bar differential strictly lowers tensor length, while the tensor-trick homotopy
preserves it. Their composite is locally nilpotent. Thus the unit `1 + δ H` required by the
basic perturbation lemma exists without a completion or a global bound on word length.

This is the finite bar perturbation used in homological transfer. See Gugenheim--Lambe--Stasheff,
*Perturbation theory in differential homological algebra II*, and Keller, *Introduction to
A-infinity algebras and modules*, Section 3.3.
-/

public section

open scoped DirectSum

universe uR uA uH

namespace TauCeti.AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The higher bar perturbation followed by a tensor-trick homotopy is locally nilpotent. -/
theorem exists_pow_higherBarDifferential_comp_homotopy_eq_zero
    {H : Type uH} [AddCommGroup H] [Module R H]
    {dA : Module.End R A} {dH : Module.End R H}
    (𝒜 : AInfinityAlgebra R A) (c : LinearSpecialContraction dA dH)
    (z : ReducedTensorWords R A) :
    ∃ n, ((𝒜.higherBarDifferential ∘ₗ
        c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)) ^ n) z = 0 :=
  ReducedTensorWords.exists_pow_comp_apply_eq_zero_of_filtration_lowering
    R A 𝒜.higherBarDifferential (c.reducedTensorWordsHomotopy (𝒜.grading.shift 1))
    𝒜.higherBarDifferential_filtration
    (c.reducedTensorWordsHomotopy_filtration (𝒜.grading.shift 1)) z

/-- The unit required by the perturbation lemma exists for the higher bar differential. -/
theorem isUnit_one_add_higherBarDifferential_comp_homotopy
    {H : Type uH} [AddCommGroup H] [Module R H]
    {dA : Module.End R A} {dH : Module.End R H}
    (𝒜 : AInfinityAlgebra R A) (c : LinearSpecialContraction dA dH) :
    IsUnit (1 + 𝒜.higherBarDifferential *
      c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)) := by
  apply Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero
  intro z
  exact 𝒜.exists_pow_higherBarDifferential_comp_homotopy_eq_zero c z

end TauCeti.AInfinityAlgebra
