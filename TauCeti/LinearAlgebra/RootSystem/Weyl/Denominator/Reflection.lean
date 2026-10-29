/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign

/-!
# Reflections of the Weyl denominator

The Weyl denominator
`Δ = ∏_{α > 0} (1 - e^{-α})` is alternating under the dot action of the Weyl group. This file
establishes the simple-reflection case, the cancellation step behind the Weyl denominator identity
`Δ = N(0)`.

A simple reflection `sᵢ` permutes all positive roots other than `αᵢ` and sends `αᵢ` to `-αᵢ`.
Consequently its linear action on the integral group algebra sends

`Δ` to `-e^{αᵢ} Δ`.

The dot action includes the compensating translation by `-αᵢ`, so the coefficients of `Δ` at
`x` and `sᵢ ⬝ x` are negatives of one another.

The consequences of that transformation law — in particular the vanishing of a coefficient at a
weight fixed by an odd Weyl-group element, so on a dot-action wall — are proved once for every
alternating element in `TauCeti/LinearAlgebra/RootSystem/Weyl/Alternating.lean`, and reach `Δ`
through `TauCeti.isDotAlternating_weylDenominator`.

## Main results

* `TauCeti.mapDomain_reflection_weylDenominator`: a simple reflection sends `Δ` to
  `-e^{αᵢ} Δ`.
* `TauCeti.coeff_weylDenominator_dotAction`: the coefficient function of `Δ` transforms by the
  sign character under the dot action of the whole Weyl group.

## References

This is the simple-reflection cancellation step in the combinatorial Weyl denominator identity
required by `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 6 ("the Weyl
character formula").

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)
  [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **A simple reflection sends the Weyl denominator to `-e^{αᵢ} Δ`.**

This is the case `w = sᵢ` of
`TauCeti.mapDomain_smul_weylDenominator`, `αᵢ` being the only inversion of `sᵢ`. -/
@[simp]
theorem mapDomain_reflection_weylDenominator {i : ι} (hi : i ∈ b.support) :
    AddMonoidAlgebra.mapDomain (P.reflection i) (weylDenominator P b) =
      -AddMonoidAlgebra.single (P.root i) 1 * weylDenominator P b := by
  classical
  have h := mapDomain_smul_weylDenominator P b (RootPairing.weylGroup.ofIdx P i)
  simp only [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.weylGroup.ofIdx_inv_eq, inversionsFinset_ofIdx P b hi,
    Finset.sum_singleton, Finset.card_singleton, pow_one] at h
  rw [h, AddMonoidAlgebra.single_neg]

variable [Invertible (2 : R)]

/-- **The coefficients of the Weyl denominator transform by the sign character under the dot
action of the whole Weyl group:**
`[e^{w ⬝ x}] Δ = sgn(w) [e^x] Δ`. -/
@[simp]
theorem coeff_weylDenominator_dotAction (w : P.weylGroup) (x : M) :
    (weylDenominator P b).coeff (dotAction P b w x) =
      (weylSign P b w : ℤ) * (weylDenominator P b).coeff x := by
  have h := congrArg (fun f : AddMonoidAlgebra ℤ M ↦ f.coeff (w • x))
    (mapDomain_smul_weylDenominator_eq_zsmul P b w)
  -- Expose `Finsupp.mapDomain` to evaluate the coefficient at the injective image of `x`.
  change (Finsupp.mapDomain (w • ·) (weylDenominator P b).coeff) (w • x) = _ at h
  rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective w)] at h
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at h
  have harg : -(weylVector P b - w • weylVector P b) + w • x = dotAction P b w x := by
    rw [dotAction_def, smul_add]
    abel
  rw [harg] at h
  calc
    _ = (weylSign P b w : ℤ) * ((weylSign P b w : ℤ) *
        (weylDenominator P b).coeff (dotAction P b w x)) := by
      rw [← mul_assoc, Int.units_coe_mul_self, one_mul]
    _ = _ := congrArg ((weylSign P b w : ℤ) * ·) h.symm

end TauCeti
