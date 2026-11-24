/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Octonion.Simple
import TauCeti.Algebra.Lie.Presentation.Serre.Injective

/-!
# The derivation algebra of the split octonions is the split Lie algebra of type `G₂`

`TauCeti/Algebra/Octonion/Serre.lean` builds the homomorphism
`TauCeti.Octonion.g₂ToDerivationLieAlgebra : LieAlgebra.g₂ →ₗ⁅R⁆ Der 𝕆` out of the Lie algebra
presented by Serre's relations for `CartanMatrix.G₂`, sending the Serre generators to Chevalley
generators of the derivation algebra `Der 𝕆` of the split octonions, and shows that it is
surjective once `2` and `3` are invertible. This file shows that over a field of characteristic
zero it is also injective, so it identifies the split Lie algebra `LieAlgebra.g₂` with `Der 𝕆`.

By `TauCeti/Algebra/Octonion/Simple.lean`, the Chevalley generators of `Der 𝕆` form a
`LieAlgebra.Basis` with transposed Cartan matrix `CartanMatrix.G₂`, and `Der 𝕆` has nondegenerate
Killing form in characteristic zero. Serre's theorem for a Lie algebra basis,
`LieAlgebra.Basis.serreLiftEquiv`, then identifies the Serre presentation with `Der 𝕆`, and the
identification agrees with `TauCeti.Octonion.g₂ToDerivationLieAlgebra` on the Serre generators.

Through this isomorphism the split `LieAlgebra.g₂` inherits the dimension `14` of `Der 𝕆` and its
nondegenerate Killing form.

## Main definitions

* `TauCeti.Octonion.g₂EquivDerivationLieAlgebra`: the isomorphism `LieAlgebra.g₂ ≃ₗ⁅K⁆ Der 𝕆`.

## Main results

* `TauCeti.Octonion.g₂ToDerivationLieAlgebra_injective`: the homomorphism from the split Lie
  algebra of type `G₂` to `Der 𝕆` is injective in characteristic zero.
* `TauCeti.Octonion.finrank_g₂`: the split Lie algebra of type `G₂` has dimension `14`.
* `TauCeti.Octonion.instIsKillingG₂`: its Killing form is nondegenerate.

## References

* J.P. Serre, *Complex Semisimple Lie Algebras*, chapter VI, appendix, for the presentation.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Ch. III, §8, for the derivation
  algebra of a Cayley algebra as the simple Lie algebra of type `G₂`.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 22.
-/

public section

namespace TauCeti

namespace Octonion

open LieAlgebra

variable {K : Type*} [Field K] [CharZero K]

variable (K) in
/-- **The derivation algebra of the split octonions is the split Lie algebra of type `G₂`**: over
a field of characteristic zero, the Lie algebra presented by Serre's relations for
`CartanMatrix.G₂` is isomorphic to `Der 𝕆`, by the isomorphism that Serre's theorem attaches to the
Chevalley generators `TauCeti.Octonion.lieBasis`. As a map it is
`TauCeti.Octonion.g₂ToDerivationLieAlgebra` (`TauCeti.Octonion.coe_g₂EquivDerivationLieAlgebra`). -/
noncomputable def g₂EquivDerivationLieAlgebra :
    LieAlgebra.g₂ (R := K) ≃ₗ⁅K⁆ derivationLieAlgebra K (Octonion K) :=
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : K) := invertibleOfNonzero three_ne_zero
  lieBasis.serreLiftEquiv (by simp)

/-- The isomorphism of `LieAlgebra.g₂` with `Der 𝕆` is the homomorphism determined by the Chevalley
generators. -/
@[simp]
theorem coe_g₂EquivDerivationLieAlgebra :
    ⇑(g₂EquivDerivationLieAlgebra K) = g₂ToDerivationLieAlgebra := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : K) := invertibleOfNonzero three_ne_zero
  -- Both homomorphisms send the Serre generators to the Chevalley generators of `Der 𝕆`.
  refine congrArg DFunLike.coe (serre_hom_ext (g₁ := (g₂EquivDerivationLieAlgebra K).toLieHom)
    (fun i => ?_) fun i => ?_) <;> simp [g₂EquivDerivationLieAlgebra]

/-- **The split Lie algebra of type `G₂` embeds in `Der 𝕆`.** Over a field of characteristic
zero, the homomorphism `TauCeti.Octonion.g₂ToDerivationLieAlgebra` from the Lie algebra presented
by Serre's relations for `CartanMatrix.G₂` to the derivations of the split octonions is
injective. -/
theorem g₂ToDerivationLieAlgebra_injective :
    Function.Injective (g₂ToDerivationLieAlgebra (R := K)) := by
  rw [← coe_g₂EquivDerivationLieAlgebra]
  exact (g₂EquivDerivationLieAlgebra K).injective

/-- The inverse of the isomorphism of `LieAlgebra.g₂` with `Der 𝕆` sends each Cartan generator
of `Der 𝕆` to the corresponding Cartan generator of the presentation. -/
@[simp]
theorem g₂EquivDerivationLieAlgebra_symm_cartanDerivation (i : Fin 2) :
    (g₂EquivDerivationLieAlgebra K).symm (cartanDerivation i) = serreH K CartanMatrix.G₂ i := by
  rw [LieEquiv.symm_apply_eq, coe_g₂EquivDerivationLieAlgebra, g₂ToDerivationLieAlgebra_serreH]

/-- The inverse of the isomorphism of `LieAlgebra.g₂` with `Der 𝕆` sends each raising generator
of `Der 𝕆` to the corresponding raising generator of the presentation. -/
@[simp]
theorem g₂EquivDerivationLieAlgebra_symm_raisingDerivation (i : Fin 2) :
    (g₂EquivDerivationLieAlgebra K).symm (raisingDerivation i) = serreE K CartanMatrix.G₂ i := by
  rw [LieEquiv.symm_apply_eq, coe_g₂EquivDerivationLieAlgebra, g₂ToDerivationLieAlgebra_serreE]

/-- The inverse of the isomorphism of `LieAlgebra.g₂` with `Der 𝕆` sends each lowering generator
of `Der 𝕆` to the corresponding lowering generator of the presentation. -/
@[simp]
theorem g₂EquivDerivationLieAlgebra_symm_loweringDerivation (i : Fin 2) :
    (g₂EquivDerivationLieAlgebra K).symm (loweringDerivation i) = serreF K CartanMatrix.G₂ i := by
  rw [LieEquiv.symm_apply_eq, coe_g₂EquivDerivationLieAlgebra, g₂ToDerivationLieAlgebra_serreF]

variable (K) in
/-- **The split Lie algebra of type `G₂` is finite-dimensional** over a field of characteristic
zero, being isomorphic to `Der 𝕆`. -/
instance instFiniteDimensionalG₂ : FiniteDimensional K (LieAlgebra.g₂ (R := K)) :=
  Module.Finite.equiv (g₂EquivDerivationLieAlgebra K).toLinearEquiv.symm

variable (K) in
/-- **The split Lie algebra of type `G₂` has dimension `14`** over a field of characteristic
zero, the dimension of `Der 𝕆`. -/
theorem finrank_g₂ : Module.finrank K (LieAlgebra.g₂ (R := K)) = 14 :=
  (g₂EquivDerivationLieAlgebra K).toLinearEquiv.finrank_eq.trans (finrank_derivationLieAlgebra K)

variable (K) in
/-- **The Killing form of the split Lie algebra of type `G₂` is nondegenerate** over a field of
characteristic zero, as it is for `Der 𝕆`. -/
instance instIsKillingG₂ : IsKilling K (LieAlgebra.g₂ (R := K)) :=
  isKilling_of_equiv (g₂EquivDerivationLieAlgebra K).symm

end Octonion

end TauCeti
