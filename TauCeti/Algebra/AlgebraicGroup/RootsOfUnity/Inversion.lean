/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inclusion
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Equalizer
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.MonoidAlgebra.Smooth
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Augmentation

/-!
# Fixed-point subgroup of `𝔾ₘ` under inversion is `μ₂`

On `MonoidAlgebra R (Multiplicative ℤ)` (coordinate Hopf algebra of `𝔾ₘ`), inversion `t ↦ t⁻¹` is
`MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv _)`. Its equalizer Hopf ideal with `id` has
underlying ideal `(single (ofAdd 2) 1 - 1)` (`equalizer_inv_monoidAlgebra_int_toIdeal`), giving a
canonical bialgebra isomorphism `(𝔾ₘ)^{-1} ≃ μ₂` (`quotientEqualizerInvMonoidAlgebraIntBialgEquiv`,
`quotientEqualizerInvMonoidAlgebraIntBialgEquiv_mk`). This quotient is étale when `IsUnit (2 : R)`
(`etale_quotient_equalizer_inv_monoidAlgebra_int`) and smooth over a field `k` iff `IsUnit (2 : k)`
(`smooth_quotient_equalizer_inv_monoidAlgebra_int_iff`), showing sharpness of tameness in
Edixhoven's fixed-point smoothness theorem.

## Main declarations

* `TauCeti.RootsOfUnityGroup.quotientEqualizerInvMonoidAlgebraIntBialgEquiv`: canonical bialgebra
  isomorphism between the inversion-fixed quotient of `R[Multiplicative ℤ]` and
  `R[Multiplicative (ZMod 2)]`.
* `TauCeti.RootsOfUnityGroup.equalizer_inv_monoidAlgebra_int_toIdeal` and
  `TauCeti.RootsOfUnityGroup.smooth_quotient_equalizer_inv_monoidAlgebra_int_iff`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Prop. 3.4, p. 295.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), §1.h and §12.
-/

public section

namespace TauCeti.RootsOfUnityGroup

open HopfIdeal _root_.MonoidAlgebra _root_.TauCeti.MonoidAlgebra Multiplicative

universe u

/-- **The fixed-point ideal of inversion on `𝔾ₘ` is `(T² - 1)`.** -/
theorem equalizer_inv_monoidAlgebra_int_toIdeal (R : Type u) [CommRing R] :
    (equalizer
      (mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
      (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal =
      Ideal.span {single (ofAdd (2 : ℤ)) (1 : R) - 1} := by
  let invHom :=
    mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ)
  have hker := ker_mapDomainRingHom_toMultiplicativeZMod R 2
  simp only [Nat.cast_ofNat] at hker
  rw [← hker]
  refine le_antisymm ?_ ?_
  · rw [equalizer_le_ker_iff]
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | single m r =>
      induction m using Multiplicative.rec with | ofAdd k => ?_
      rw [mapDomainBialgHom_single, BialgHom.id_apply]
      simp [← ofAdd_neg, ZMod.neg_eq_self_mod_two]
  · rw [hker, Ideal.span_singleton_le_iff_mem]
    have hmul := (equalizer invHom (BialgHom.id R _)).toIdeal.mul_mem_left
      (-single (ofAdd (1 : ℤ)) (1 : R)) (sub_mem_equalizer (single (ofAdd (1 : ℤ)) (1 : R)))
    have hinv : (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ)
        (ofAdd (1 : ℤ)) = ofAdd (-1 : ℤ) := by simp [← ofAdd_neg]
    have hcalc : -single (ofAdd (1 : ℤ)) (1 : R) *
          (invHom (single (ofAdd (1 : ℤ)) (1 : R)) - single (ofAdd (1 : ℤ)) (1 : R)) =
        single (ofAdd (2 : ℤ)) (1 : R) - 1 := by
      rw [neg_mul, mul_sub, neg_sub, mapDomainBialgHom_single, hinv, single_mul_single,
        single_mul_single, ← ofAdd_add, ← ofAdd_add, one_add_one_eq_two, add_neg_cancel, ofAdd_zero,
        mul_one, MonoidAlgebra.one_def]
    rwa [BialgHom.id_apply, hcalc] at hmul

/-- The equalizer Hopf ideal of inversion on `𝔾ₘ` equals the kernel Hopf ideal of the coordinate
surjection `R[Multiplicative ℤ] ↠ R[Multiplicative (ZMod 2)]`. -/
theorem equalizer_inv_monoidAlgebra_int_eq_kerOfSurjective (R : Type u) [CommRing R] :
    equalizer
      (mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
      (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ))) =
      kerOfSurjective (mapDomainBialgHom R (toMultiplicativeZMod 2))
        (_root_.MonoidAlgebra.mapDomain_surjective (toMultiplicativeZMod_surjective 2)) := by
  have hker := ker_mapDomainRingHom_toMultiplicativeZMod R 2
  simp only [Nat.cast_ofNat] at hker
  have hEq := (equalizer_inv_monoidAlgebra_int_toIdeal R).trans <| hker.symm.trans <|
    (congrArg RingHom.ker (mapDomainBialgHom_toRingHom R (toMultiplicativeZMod 2)).symm).trans
      (kerOfSurjective_toIdeal (mapDomainBialgHom R (toMultiplicativeZMod 2))
        (_root_.MonoidAlgebra.mapDomain_surjective (toMultiplicativeZMod_surjective 2))).symm
  exact le_antisymm (toIdeal_le_toIdeal.mp hEq.le) (toIdeal_le_toIdeal.mp hEq.ge)

/-- **Fixed-point subgroup of `𝔾ₘ` under inversion is `μ₂`.** -/
noncomputable def quotientEqualizerInvMonoidAlgebraIntBialgEquiv (R : Type u) [CommRing R] :
    (MonoidAlgebra R (Multiplicative ℤ) ⧸
      (equalizer
        (mapDomainBialgHom R
          (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
        (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal) ≃ₐc[R]
      MonoidAlgebra R (Multiplicative (ZMod 2)) :=
  _root_.CommHopfAlgCat.ofIso
    (CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
      (_root_.CommHopfAlgCat.ofHom (mapDomainBialgHom R (toMultiplicativeZMod 2)))
      (_root_.MonoidAlgebra.mapDomain_surjective (toMultiplicativeZMod_surjective 2))
      (equalizer_inv_monoidAlgebra_int_eq_kerOfSurjective R).symm)

/-- `quotientEqualizerInvMonoidAlgebraIntBialgEquiv` acts on cosets via
`mapDomainBialgHom R (toMultiplicativeZMod 2)`. -/
@[simp]
theorem quotientEqualizerInvMonoidAlgebraIntBialgEquiv_mk (R : Type u) [CommRing R]
    (x : MonoidAlgebra R (Multiplicative ℤ)) :
    quotientEqualizerInvMonoidAlgebraIntBialgEquiv R
      (Ideal.Quotient.mk
        (equalizer
          (mapDomainBialgHom R
            (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal x) =
      mapDomainBialgHom R (toMultiplicativeZMod 2) x := by
  have h := CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom
    (_root_.CommHopfAlgCat.ofHom (mapDomainBialgHom R (toMultiplicativeZMod 2)))
    (_root_.MonoidAlgebra.mapDomain_surjective (toMultiplicativeZMod_surjective 2))
    (equalizer_inv_monoidAlgebra_int_eq_kerOfSurjective R).symm
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, _root_.CommHopfAlgCat.hom_ofHom,
    CommHopfAlgCat.hom_mkQuotient, Bialgebra.Quotient.mkBialgHom_apply,
    quotientEqualizerInvMonoidAlgebraIntBialgEquiv, ← TauCeti.CommHopfAlgCat.coe_ofIso,
    BialgEquiv.coe_toBialgHom] using congrArg (fun m ↦ m.hom x) h

/-- On basis elements, `quotientEqualizerInvMonoidAlgebraIntBialgEquiv` sends the coset of
`single (ofAdd k) r` to `single (ofAdd (k : ZMod 2)) r`. Not `@[simp]` because `_mk` simplifies. -/
theorem quotientEqualizerInvMonoidAlgebraIntBialgEquiv_mk_single (R : Type u) [CommRing R]
    (k : ℤ) (r : R) :
    quotientEqualizerInvMonoidAlgebraIntBialgEquiv R
      (Ideal.Quotient.mk
        (equalizer
          (mapDomainBialgHom R
            (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal
        (single (ofAdd k) r)) =
      single (ofAdd (k : ZMod 2)) r := by simp

/-- The inverse of `quotientEqualizerInvMonoidAlgebraIntBialgEquiv` lifts
`single (ofAdd (k : ZMod 2)) r` to the coset of `single (ofAdd k) r`. -/
@[simp]
theorem quotientEqualizerInvMonoidAlgebraIntBialgEquiv_symm_single_ofAdd_intCast
    (R : Type u) [CommRing R] (k : ℤ) (r : R) :
    (quotientEqualizerInvMonoidAlgebraIntBialgEquiv R).symm (single (ofAdd (k : ZMod 2)) r) =
      Ideal.Quotient.mk
        (equalizer
          (mapDomainBialgHom R
            (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal
        (single (ofAdd k) r) :=
  (quotientEqualizerInvMonoidAlgebraIntBialgEquiv R).symm_apply_eq.mpr
    (quotientEqualizerInvMonoidAlgebraIntBialgEquiv_mk_single R k r).symm

/-- When `2` is invertible in `R`, the inversion-fixed quotient of `𝔾ₘ` is étale over `R`. -/
theorem etale_quotient_equalizer_inv_monoidAlgebra_int (R : Type u) [CommRing R]
    (h2 : IsUnit (2 : R)) :
    Algebra.Etale R
      (MonoidAlgebra R (Multiplicative ℤ) ⧸
        (equalizer
          (mapDomainBialgHom R
            (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal) := by
  have _ : Algebra.Etale R (MonoidAlgebra R (Multiplicative (ZMod 2))) :=
    etale_of_isUnit_card R (Multiplicative (ZMod 2))
      (by simpa [Nat.card_eq_fintype_card, Fintype.card_multiplicative] using h2)
  exact Algebra.Etale.of_equiv (quotientEqualizerInvMonoidAlgebraIntBialgEquiv R).symm.toAlgEquiv

/-- **Sharpness of tameness for inversion on `𝔾ₘ`.** Over a field `k`, the inversion-fixed subgroup
quotient of `𝔾ₘ` (`μ₂`) is smooth over `k` if and only if `2` is invertible in `k`. -/
theorem smooth_quotient_equalizer_inv_monoidAlgebra_int_iff (k : Type u) [Field k] :
    Algebra.Smooth k
      (MonoidAlgebra k (Multiplicative ℤ) ⧸
        (equalizer
          (mapDomainBialgHom k
            (MulEquiv.inv (Multiplicative ℤ) : Multiplicative ℤ →* Multiplicative ℤ))
          (BialgHom.id k (MonoidAlgebra k (Multiplicative ℤ)))).toIdeal) ↔
      IsUnit (2 : k) := by
  refine ⟨fun hs ↦ ?_, fun h2 ↦ ?_⟩
  · have hs' : Algebra.Smooth k (MonoidAlgebra k (Multiplicative (ZMod 2))) :=
      Algebra.Smooth.of_equiv (quotientEqualizerInvMonoidAlgebraIntBialgEquiv k).toAlgEquiv
    simpa [Nat.card_eq_fintype_card, Fintype.card_multiplicative] using
      (smooth_iff_isUnit_card k (Multiplicative (ZMod 2))).mp hs'
  · have _ := etale_quotient_equalizer_inv_monoidAlgebra_int k h2
    infer_instance

end TauCeti.RootsOfUnityGroup
