/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.Topology.Algebra.Group.Transfer

/-!
# Corestriction of continuous characters

For trivial coefficients, degree-one corestriction is the character-theoretic transfer.
`cochainsCor1_eq_transfer` identifies the transversal sum with Mathlib's `MonoidHom.transfer`
already on cochains, for every transversal. `H1EquivOfSmulEqSelf_explicitCor1_eq_transfer`
states the commuting square between corestriction on continuous `H¹` and transfer on characters,
using the existing character equivalence `H1EquivOfSmulEqSelf`.

In particular, transfer of a character of an abelian quotient of an open subgroup is
precomposition with the transfer into that quotient, by `MonoidHom.transfer_comp`.
This is the bridge from cohomological corestriction to transfer on abelianizations.
The character obtained by transfer is continuous by `TauCeti.continuous_transfer`.

The action must be trivial: otherwise the corestriction sum contains the factors `t q •`,
and it is not the transfer of an ordinary homomorphism. The coefficients need not be discrete.

## References

* Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.9).
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public section

namespace TauCeti.ContCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  {U : Subgroup G} [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- For trivial coefficients, the corestriction cochain of a homomorphism is its transfer,
independently of the transversal. This identity needs no topology. -/
theorem cochainsCor1_eq_transfer (htriv : ∀ (g : G) (m : M), g • m = m)
    (t : G ⧸ U → G) (ht : ∀ q : G ⧸ U, (QuotientGroup.mk (t q) : G ⧸ U) = q)
    (φ : U →* Multiplicative M) :
    cochainsCor1 G M U t ht (fun u => Multiplicative.toAdd (φ u)) =
      fun g => Multiplicative.toAdd (MonoidHom.transfer φ g) := by
  ext g
  rw [cochainsCor1_apply_of_smul_eq_self G M U t ht htriv,
    transfer_eq_prod_lWord t ht φ g]
  simp

variable [TopologicalSpace G] [SeparatelyContinuousMul G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]

/-- Under the continuous-character description of `H¹` for trivial coefficients,
corestriction is Mathlib's transfer. This is an equality of homomorphisms, not just classes. -/
@[simp]
theorem H1EquivOfSmulEqSelf_explicitCor1_eq_transfer
    (htriv : ∀ (g : G) (m : M), g • m = m) (hU : IsOpen (U : Set G)) (x : H1 U M) :
    (↑(Additive.toMul (H1EquivOfSmulEqSelf htriv (explicitCor1 G M U hU x))) :
      G →* Multiplicative M) =
      MonoidHom.transfer
        (↑(Additive.toMul (H1EquivOfSmulEqSelf (fun (u : U) m => htriv u m) x)) :
          U →* Multiplicative M) := by
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    apply MonoidHom.ext
    intro g
    have h := congrFun (cochainsCor1_eq_transfer htriv Quotient.out Quotient.out_eq
      (Additive.toMul (Z1EquivOfSmulEqSelf (fun (u : U) m => htriv u m) f)).toMonoidHom) g
    simpa only [explicitCor1_mk, H1EquivOfSmulEqSelf_mk,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, Z1EquivOfSmulEqSelf_apply,
      coe_cocyclesCor1, toAdd_ofAdd, ofAdd_toAdd] using
      congrArg Multiplicative.ofAdd h

end TauCeti.ContCohomology
