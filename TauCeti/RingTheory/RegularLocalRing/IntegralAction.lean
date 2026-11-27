/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Ring
public import TauCeti.RingTheory.Finiteness.Action
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.Projective
import TauCeti.RingTheory.Depth.Flat
import TauCeti.RingTheory.Flat.TensorProduct
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.RegularLocalRing.Free

/-!
# Projectivity for finite actions of regular rings

A nonzero finite projective module over a Noetherian domain `R` detects an action by a
domain `S` of the same finite dimension. The action is faithful, `S` is finite over `R`,
and if both rings are regular the module is projective over `S`.

For projectivity it suffices that the base is Cohen–Macaulay and that the acting algebra is
integral and regular. At a prime `q` over `p`, incomparability bounds the height of `q` by
that of `p`. The localized module is still flat over `R_p`, so its depth over `S_q` is at least
the depth of `R_p`, which equals the height of `p`. The maximal Cohen–Macaulay freeness criterion
then applies over `S_q`.

## References

* M. Kisin, *Moduli of finite flat group schemes, and modularity*, Lemma 3.3.4, p. 1159.
-/

public section

universe u v w

open TensorProduct

namespace Module

variable (R : Type u) (S : Type v) (M : Type w) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- For an integral regular algebra over a Cohen–Macaulay ring, a finite module over the
algebra which is flat over the base is projective over the algebra. -/
theorem projective_of_isIntegral_of_flat [TauCeti.Ring.IsCohenMacaulay R] [IsRegularRing S]
    [Algebra.IsIntegral R S] [Module.Finite S M] [Flat R M] : Projective S M := by
  have : FinitePresentation S M := finitePresentation_of_finite S M
  apply projective_of_localization_maximal
  intro q hq
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let N := Sq ⊗[S] M
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap Rp Sq) := Localization.isLocalHom_localRingHom _ _ _ _
  have : Flat R N := Flat.tensorProduct_of_flat (R := R) (B := S) (M := M) Sq
  have : Flat Rp N := (flat_iff_of_isLocalization Rp p.primeCompl N).2 this
  have hcm := TauCeti.Ring.IsCohenMacaulay.isCohenMacaulay_localization (R := R) p
  have : Free Sq N := TauCeti.IsRegularLocalRing.free_of_ringKrullDim_le_depth N <| calc
    ringKrullDim Sq ≤ ringKrullDim Rp := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Sq,
        IsLocalization.AtPrime.ringKrullDim_eq_height p Rp]
      exact WithBot.coe_le_coe.mpr (q.height_le_height_under_of_isIntegral (R := R))
    _ = (IsLocalRing.depth (ModuleCat.of Rp Rp) : WithBot ℕ∞) :=
      (hcm.depth_eq.trans (supportDim_self_eq_ringKrullDim Rp)).symm
    _ ≤ _ := by
      -- Apply the tensor depth formula to N and the free rank-one base module.
      -- The lifts put its two factors in the same universe.
      let e : ULift.{u} N ⊗[Rp] ULift.{max v w} Rp ≃ₗ[Sq] N :=
        (AlgebraTensorModule.congr ULift.moduleEquiv ULift.moduleEquiv).trans
          (AlgebraTensorModule.rid Rp Sq N)
      have h := IsLocalRing.depth_tensorProduct_eq_add_of_flat (R := Rp) (S := Sq)
        (N := ULift.{u} N) (M := ULift.{max v w} Rp)
      rw [IsLocalRing.depth_eq_of_linearEquiv e, IsLocalRing.depth_eq_of_linearEquiv
        (ULift.moduleEquiv : ULift.{max v w} Rp ≃ₗ[Rp] Rp)] at h
      exact WithBot.coe_le_coe.mpr (h ▸ le_self_add)
  exact Projective.of_equiv (LocalizedModule.equivTensorProduct q.primeCompl M).symm

/-- A nonzero finite flat module over a Noetherian domain detects any compatible action by a
domain of at most the same finite dimension. The algebra is finite over the base and acts
faithfully. The module is projective over it when the base is Cohen–Macaulay and the algebra
is regular.
In particular this applies to finite projective base modules over regular domains. -/
theorem finite_and_faithfulSMul_and_projective_of_ringKrullDim_le
    [IsDomain R] [IsDomain S] [FiniteRingKrullDim S]
    [IsNoetherian R M] [Nontrivial M] [Flat R M] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    Module.Finite R S ∧ FaithfulSMul S M ∧
      (TauCeti.Ring.IsCohenMacaulay R → IsRegularRing S → Projective S M) := by
  have hs : supportDim R M = ringKrullDim R := by
    rw [supportDim, support_of_isTorsionFree (R := R) (M := M)]
    exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ
  obtain ⟨hfin, hfaith⟩ := finite_and_faithfulSMul_of_ringKrullDim_le_supportDim R S M
    (hdim.trans_eq hs.symm)
  have : Module.Finite S M := .of_restrictScalars_finite R S M
  exact ⟨hfin, hfaith, fun _ _ ↦ projective_of_isIntegral_of_flat R S M⟩

end Module
