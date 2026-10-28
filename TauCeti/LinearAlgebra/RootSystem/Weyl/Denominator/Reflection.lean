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

The reflection permutes the factors belonging to the positive roots other than `αᵢ`. Its one
exceptional factor changes from `1 - e^{-αᵢ}` to `1 - e^{αᵢ}`, and
`1 - e^{αᵢ} = -e^{αᵢ}(1 - e^{-αᵢ})`. This is the case `w = sᵢ` of
`TauCeti.mapDomain_smul_weylDenominator`, `αᵢ` being the only inversion of `sᵢ`. -/
@[simp]
theorem mapDomain_reflection_weylDenominator {i : ι} (hi : i ∈ b.support) :
    AddMonoidAlgebra.mapDomain (P.reflection i) (weylDenominator P b) =
      -AddMonoidAlgebra.single (P.root i) 1 * weylDenominator P b := by
  classical
  have hinv : inversionsFinset P b (RootPairing.weylGroup.ofIdx P i)⁻¹ = {i} := by
    rw [RootPairing.weylGroup.ofIdx_inv_eq, ← Finset.coe_inj, coe_inversionsFinset,
      inversions_ofIdx P b hi, Finset.coe_singleton]
  have h := mapDomain_smul_weylDenominator P b (RootPairing.weylGroup.ofIdx P i)
  simp only [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul, hinv,
    Finset.sum_singleton, Finset.card_singleton, pow_one] at h
  rw [h, AddMonoidAlgebra.single_neg]

variable [Invertible (2 : R)]

/-- **The coefficients of the Weyl denominator are alternating under a simple reflection for the
dot action:** the coefficients at `x` and `sᵢ ⬝ x` are negatives of one another.

The translation in the dot action exactly cancels the monomial `e^{αᵢ}` in
`TauCeti.mapDomain_reflection_weylDenominator`. -/
theorem coeff_weylDenominator_dotAction_ofIdx {i : ι} (hi : i ∈ b.support) (x : M) :
    (weylDenominator P b).coeff
        (dotAction P b (RootPairing.weylGroup.ofIdx P i) x) =
      -(weylDenominator P b).coeff x := by
  have h := congrArg (fun f : AddMonoidAlgebra ℤ M ↦
    f.coeff ((P.reflection i) x)) (mapDomain_reflection_weylDenominator P b hi)
  -- Expose the underlying `Finsupp.mapDomain` to read its coefficient at the image of `x`.
  change (Finsupp.mapDomain (P.reflection i) (weylDenominator P b).coeff)
      ((P.reflection i) x) = _ at h
  rw [Finsupp.mapDomain_apply_of_injective (P.reflection i).injective] at h
  simp only [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at h
  rw [dotAction_ofIdx P b hi]
  have harg : -P.root i + (x - P.coroot' i x • P.root i) =
      x - (P.coroot' i x + 1) • P.root i := by
    module
  rw [RootPairing.reflection_apply, harg] at h
  omega

/-- **The coefficients of the Weyl denominator transform by the sign character under the dot
action of the whole Weyl group:**
`[e^{w ⬝ x}] Δ = sgn(w) [e^x] Δ`.

Every Weyl-group element is a product of simple reflections. The result therefore follows by
iterating `TauCeti.coeff_weylDenominator_dotAction_ofIdx`; the parity of the word is recorded by
`TauCeti.weylSign`. -/
@[simp]
theorem coeff_weylDenominator_dotAction (w : P.weylGroup) (x : M) :
    (weylDenominator P b).coeff (dotAction P b w x) =
      (weylSign P b w : ℤ) * (weylDenominator P b).coeff x := by
  obtain ⟨l, rfl⟩ := exists_wordProd_eq P b w
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [wordProd_cons, dotAction_mul,
        coeff_weylDenominator_dotAction_ofIdx P b i.2, ih, map_mul,
        weylSign_ofIdx P b]
      norm_num

end TauCeti
