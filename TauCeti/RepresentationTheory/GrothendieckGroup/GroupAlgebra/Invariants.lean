/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Universal
import TauCeti.RepresentationTheory.Invariants

/-!
# Invariant dimensions on the Grothendieck group of a group algebra

Let `G` be a finite group and `k` a field whose characteristic does not divide `#G`. Maschke's
theorem makes the invariants functor exact, so the dimension of the invariant subspace is additive
in short exact sequences of finite-dimensional representations
(`FDRep.finrank_invariants_add_of_shortExact`). This file descends that dimension to a
homomorphism

`finrankInvariantsK0 k G : G₀(k[G]) →+ ℤ`.

The Grothendieck ring product is induced by the tensor product of representations. Hence, for a
fixed finite-dimensional representation `A`, multiplication by `[A]` followed by invariant
dimension gives another additive homomorphism,

`finrankTensorInvariantsK0 A : G₀(k[G]) →+ ℤ`,

whose value at `[M]` is `dimₖ (M ⊗ A)^G`. This packages the semisimple representation-theoretic
functional used in Euler characteristic calculations.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §§1.4 and 14.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]

/-- **Invariant dimension on the group-algebra Grothendieck group.** When `#G` is nonzero in
`k`, this homomorphism sends the class of a finite-dimensional representation `V` to
`dimₖ(Vᴳ)`. -/
noncomputable def finrankInvariantsK0 :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  liftFDRepK0 (fun V ↦ (Module.finrank k (Representation.invariants V.ρ) : ℤ))
    fun {_} hS ↦ by
    exact_mod_cast FDRep.finrank_invariants_add_of_shortExact hS

/-- The invariant-dimension homomorphism evaluates on the class of the group-algebra module of a
representation `V` as the dimension of the invariant subspace of `V`. -/
@[simp]
theorem finrankInvariantsK0_of (V : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    finrankInvariantsK0 (ExactK0.of (FGModuleCat.of k[G] (Representation.asModule V.ρ))) =
      Module.finrank k (Representation.invariants V.ρ) :=
  liftFDRepK0_of _ _ V

/-- **Invariant dimension after tensoring with `A`.** This additive homomorphism sends a class
`[M]` to `dimₖ (M ⊗ A)ᴳ`. -/
noncomputable def finrankTensorInvariantsK0 (A : FDRep k G) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  (finrankInvariantsK0 (k := k) (G := G)).comp
    (AddMonoidHom.mulRight (fdRepK0RingEquiv k G (ExactK0.of A)))

/-- `finrankTensorInvariantsK0 A` is invariant dimension after multiplication by the class of
`A`. -/
theorem finrankTensorInvariantsK0_apply (A : FDRep k G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    finrankTensorInvariantsK0 A x =
      finrankInvariantsK0 (x * fdRepK0RingEquiv k G (ExactK0.of A)) := by
  rw [finrankTensorInvariantsK0, AddMonoidHom.comp_apply, AddMonoidHom.mulRight_apply]

/-- Evaluating `finrankTensorInvariantsK0 A` on the class of the group-algebra module of `M`
gives the dimension of the invariants of the tensor product `M ⊗ A`. -/
@[simp]
theorem finrankTensorInvariantsK0_of (A M : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule M.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    finrankTensorInvariantsK0 A (ExactK0.of (FGModuleCat.of k[G] (Representation.asModule M.ρ))) =
      Module.finrank k (Representation.invariants (M ⊗ A).ρ) := by
  rw [← fdRepK0RingEquiv_of, finrankTensorInvariantsK0_apply, ← map_mul, ExactK0.of_mul_of,
    fdRepK0RingEquiv_of, finrankInvariantsK0_of]

end TauCeti
