/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# The Weyl denominator moved by a Weyl-group element

A Weyl-group element `w` acts on the integral group algebra `ℤ[M]` of the weight space through
its linear action on the exponents. It sends the Weyl denominator `Δ = ∏_{α > 0} (1 - e^{-α})` to
`w Δ = ∏_{α > 0} (1 - e^{-w α})`, and this file computes that product exactly, factor by factor:

`w Δ = (-1)^{ℓ} e^{∑_{β > 0, w⁻¹ β < 0} β} Δ`,

where `ℓ` is the number of positive roots `β` with `w⁻¹ β < 0`. The factors of the positive roots
that `w` keeps positive are permuted among the factors of `Δ`. Each positive root `α` that `w`
inverts gives `β = -w α`, a positive root that `w⁻¹` inverts, and its factor is inverted:
`1 - e^{β} = -e^{β} (1 - e^{-β})`. Every inverted factor contributes one sign and one shift by
its root, and neither the crystallographic nor the reduced hypothesis is used.

With the Weyl vector `ρ`, the shift is `ρ - w ρ` (`TauCeti.smul_weylVector_sub_weylVector`) and
the sign is `sgn(w)`, so `w Δ = sgn(w) e^{ρ - w ρ} Δ`. Multiplied by `e^{w λ}` this says

`e^{w λ} Δ = sgn(w) e^{w ⬝ λ} (w Δ)`,

the denominator-free form of `e^{w λ} / ∏_{α > 0} (1 - e^{-w α}) = sgn(w) e^{w ⬝ λ} / Δ`. Summed
over `W`, the right-hand sides add up to the Weyl numerator over `Δ`, which is how the fixed-point
form `∑_{w ∈ W} e^{w λ} / ∏_{α > 0} (1 - e^{-w α})` of the Weyl character formula is compared with
its normalized form `∑_{w ∈ W} sgn(w) e^{w(λ + ρ) - ρ} / ∏_{α > 0} (1 - e^{-α})`.

## Main results

* `RootPairing.mapDomain_smul_weylDenominator_eq_prod`: `w Δ = ∏_{α > 0} (1 - e^{-w α})`.
* `TauCeti.mapDomain_smul_weylDenominator`: `w Δ = (-1)^{ℓ} e^{∑_{β > 0, w⁻¹ β < 0} β} Δ`.
* `TauCeti.mapDomain_smul_weylDenominator_eq_zsmul`: `w Δ = sgn(w) e^{ρ - w ρ} Δ`.
* `TauCeti.coeff_weylDenominator_dotAction`: the coefficient function of `Δ` transforms by the
  sign character under the dot action of the whole Weyl group.
* `TauCeti.single_smul_mul_weylDenominator`: `e^{w λ} Δ = sgn(w) e^{w ⬝ λ} (w Δ)`.
* `RootPairing.map_mapDomain_smul_weylDenominator_ne_zero`: `f (w Δ) ≠ 0` when `f Δ ≠ 0`, for
  any ring homomorphism `f` out of `ℤ[M]`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.1.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Ch. VI, §3.
-/

public section

universe u v w x y

namespace RootPairing

open TauCeti

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base) (w : P.weylGroup)

/-- **A Weyl-group element moves the Weyl denominator factor by factor**:
`w Δ = ∏_{α > 0} (1 - e^{-w α})`. -/
theorem mapDomain_smul_weylDenominator_eq_prod :
    AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b) =
      ∏ i ∈ posRootsFinset P b, (1 - AddMonoidAlgebra.single (-(w • P.root i)) 1) := by
  -- `(w • ·)` is the underlying function of `DistribSMul.toAddMonoidHom M w`, along which
  -- `mapDomain` is a ring homomorphism.
  have hring : AddMonoidAlgebra.mapDomain (R := ℤ) (w • ·) (weylDenominator P b) =
      AddMonoidAlgebra.mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w)
        (weylDenominator P b) := rfl
  rw [hring, weylDenominator_def, map_prod]
  simp only [map_sub, map_one, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, DistribSMul.toAddMonoidHom_apply, smul_neg]

end RootPairing

namespace TauCeti

open RootPairing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base) (w : P.weylGroup)

/-- **A Weyl-group element sends the Weyl denominator to a signed monomial multiple of itself**:
`w Δ = (-1)^{ℓ} e^{∑_{β > 0, w⁻¹ β < 0} β} Δ`, where `ℓ` is the number of positive roots `β` with
`w⁻¹ β < 0`. -/
theorem mapDomain_smul_weylDenominator :
    AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b) =
      AddMonoidAlgebra.single (∑ i ∈ inversionsFinset P b w⁻¹, P.root i)
          ((-1) ^ (inversionsFinset P b w⁻¹).card) * weylDenominator P b := by
  classical
  let := P.indexNeg
  let F : ι → AddMonoidAlgebra ℤ M := fun i ↦ 1 - AddMonoidAlgebra.single (-P.root i) 1
  -- The factors over the inversions of `w⁻¹`, inverted.
  have hinv : ∏ i ∈ inversionsFinset P b w⁻¹, (1 - AddMonoidAlgebra.single (P.root i) 1) =
      AddMonoidAlgebra.single (∑ i ∈ inversionsFinset P b w⁻¹, P.root i)
          ((-1) ^ (inversionsFinset P b w⁻¹).card) * ∏ i ∈ inversionsFinset P b w⁻¹, F i := by
    have hfactor (y : M) : (1 - AddMonoidAlgebra.single y 1 : AddMonoidAlgebra ℤ M) =
        -AddMonoidAlgebra.single y 1 * (1 - AddMonoidAlgebra.single (-y) 1) := by
      rw [mul_sub, mul_one, neg_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one,
        ← AddMonoidAlgebra.one_def]
      abel
    rw [Finset.prod_congr rfl fun i _ ↦ hfactor (P.root i), Finset.prod_mul_distrib]
    simp_rw [← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.prod_single, Finset.prod_const, F]
  rw [mapDomain_smul_weylDenominator_eq_prod, weylDenominator_def,
    ← Finset.prod_sdiff (inversionsFinset_subset_posRootsFinset P b w)]
  simp only [weylGroup_apply_root]
  rw [prod_posRootsFinset_sdiff_inversionsFinset_comp_weylGroupToPerm P b w F]
  -- On an inversion `α` of `w`, the factor `1 - e^{-w α}` is `1 - e^{β}` for `β = -w α`.
  have hflip : ∏ i ∈ inversionsFinset P b w,
      (1 - AddMonoidAlgebra.single (-P.root (P.weylGroupToPerm w i)) 1 : AddMonoidAlgebra ℤ M) =
        ∏ i ∈ inversionsFinset P b w⁻¹, (1 - AddMonoidAlgebra.single (P.root i) 1) :=
    (Finset.prod_congr rfl fun i _ ↦ by
      rw [root_neg_index]).trans
      (prod_inversionsFinset_comp_neg_weylGroupToPerm P b w fun j ↦
        (1 - AddMonoidAlgebra.single (P.root j) 1 : AddMonoidAlgebra ℤ M))
  rw [hflip, hinv, mul_left_comm,
    Finset.prod_sdiff (inversionsFinset_subset_posRootsFinset P b w⁻¹)]

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [Invertible (2 : R)]

/-- **A Weyl-group element multiplies the Weyl denominator by its sign and a shift by the Weyl
vector**: `w Δ = sgn(w) e^{ρ - w ρ} Δ`. -/
theorem mapDomain_smul_weylDenominator_eq_zsmul :
    AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b) =
      (weylSign P b w : ℤ) • (AddMonoidAlgebra.single (weylVector P b - w • weylVector P b) 1 *
        weylDenominator P b) := by
  rw [mapDomain_smul_weylDenominator, ← neg_sub, smul_weylVector_sub_weylVector, neg_neg,
    card_inversionsFinset, ncard_inversions_inv, weylSign_apply, ← smul_mul_assoc,
    AddMonoidAlgebra.smul_single', mul_one, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- **The fixed-point term against the normalized term**: `e^{w λ} Δ = sgn(w) e^{w ⬝ λ} (w Δ)`.
This is the denominator-free form of
`e^{w λ} / ∏_{α > 0} (1 - e^{-w α}) = sgn(w) e^{w(λ + ρ) - ρ} / ∏_{α > 0} (1 - e^{-α})`. -/
theorem single_smul_mul_weylDenominator (lam : M) :
    AddMonoidAlgebra.single (w • lam) 1 * weylDenominator P b =
      (weylSign P b w : ℤ) • (AddMonoidAlgebra.single (dotAction P b w lam) 1 *
        AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b)) := by
  rw [mapDomain_smul_weylDenominator_eq_zsmul, mul_smul_comm, smul_smul, Int.units_coe_mul_self,
    one_smul, ← mul_assoc, AddMonoidAlgebra.single_mul_single, mul_one, dotAction_def,
    smul_add]
  congr 2
  abel

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

namespace RootPairing

open TauCeti

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

/-- **The moved Weyl denominator does not vanish where the Weyl denominator does not**: for a ring
homomorphism `f` into a semiring, if `f Δ ≠ 0` then `f (w Δ) ≠ 0`, since `w Δ` is `Δ` times a
signed exponential, a unit of `ℤ[M]`. -/
theorem map_mapDomain_smul_weylDenominator_ne_zero {S : Type y} [Semiring S]
    (f : AddMonoidAlgebra ℤ M →+* S) (hf : f (weylDenominator P b) ≠ 0) (w : P.weylGroup) :
    f (AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b)) ≠ 0 := by
  rw [mapDomain_smul_weylDenominator, map_mul]
  refine fun h ↦ hf ((IsUnit.map f ?_).mul_right_eq_zero.mp h)
  refine IsUnit.of_mul_eq_one
    (AddMonoidAlgebra.single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i)
      ((-1) ^ (inversionsFinset P b w⁻¹).card)) ?_
  simp [AddMonoidAlgebra.single_mul_single, ← mul_pow, AddMonoidAlgebra.one_def]

end RootPairing
