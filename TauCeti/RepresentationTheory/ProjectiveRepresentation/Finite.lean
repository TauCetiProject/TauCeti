/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.SchurMultiplier
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Finite
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Finiteness of the Schur multiplier

For a finite group `G` over an algebraically closed field `k`, every class in `H²(G, kˣ)`
has a normalized factor set taking values in the `|G|`-th roots of unity. Consequently the
Schur multiplier is finite. This is the finiteness input to the construction of finite
representation groups.

We use the existing realization of every cohomology class by a twisted regular representation,
and the invariance of its class under rescaling. No restriction on the characteristic of `k`
is needed: even when it divides `|G|`, the group of `|G|`-th roots of unity is finite.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapter 2.
-/

public section

namespace TauCeti

variable {k G : Type} [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- Every Schur-multiplier class of a finite group has a factor set whose values are roots of
unity of order dividing the group order. The representative is realized by the twisted regular
representation on `G →₀ k`. -/
theorem exists_isFactorSet_pow_card_eq_one_cohomologyClass_eq (x : schurMultiplier k G) :
    ∃ (α : G → G → kˣ) (_ : IsFactorSet α),
      (∀ g h, α g h ^ Nat.card G = 1) ∧
      (isProjectiveRep_twistedRegularRep k G α).cohomologyClass = x := by
  obtain ⟨α, ρ, hρ, hx⟩ := exists_isProjectiveRep_cohomologyClass_eq x
  let := hρ.isFactorSet
  obtain ⟨c, hc, hpow⟩ := IsFactorSet.exists_rescale_pow_card_eq_one α
  let β (g h : G) := c g * c h * (c (g * h))⁻¹ * α g h
  have hβ := hρ.rescale c hc
  let : IsFactorSet β := hβ.isFactorSet
  refine ⟨β, inferInstance, hpow, ?_⟩
  exact (IsProjectiveRep.cohomologyClass_congr
    (isProjectiveRep_twistedRegularRep k G β) hβ rfl).trans
      ((hρ.cohomologyClass_rescale c hc).trans hx)

/-- The Schur multiplier of a finite group over an algebraically closed field is finite. -/
instance : Finite (schurMultiplier k G) := by
  classical
  let : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let S := {α : G → G → kˣ // IsFactorSet α ∧ ∀ g h, α g h ^ Nat.card G = 1}
  let encode (a : S) (g h : G) : rootsOfUnity (Nat.card G) k :=
    ⟨a.1 g h, (mem_rootsOfUnity _ _).2 (a.2.2 g h)⟩
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext g h
    exact congrArg (fun f ↦ (f g h : kˣ)) hab
  let : Finite S := Finite.of_injective encode hinj
  let f (a : S) : schurMultiplier k G :=
    let := a.2.1
    (isProjectiveRep_twistedRegularRep k G a.1).cohomologyClass
  apply Finite.of_surjective f
  intro x
  obtain ⟨α, hα, hpow, hx⟩ := exists_isFactorSet_pow_card_eq_one_cohomologyClass_eq x
  exact ⟨⟨α, hα, hpow⟩, hx⟩

end TauCeti
