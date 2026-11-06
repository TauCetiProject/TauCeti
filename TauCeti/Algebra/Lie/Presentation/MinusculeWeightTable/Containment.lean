/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.RankOne.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Integral containment of minuscule rank-one maps

The two-dimensional block action at a minuscule node is natural in its coefficient ring.
If its special-linear restriction lies in an integral closed subgroup of `GL` over every
field, it lies in that subgroup over every commutative ring, including nonreduced rings.
Indeed, it suffices to test the universal `SL₂` point. Its coordinate ring is reduced by
smoothness over `ℤ`, so vanishing can be tested in the fraction fields of its prime quotients.
Specializing that universal point then gives containment over arbitrary rings.

This upgrades field-valued rank-one constructions to natural maps of represented groups;
it does not assert that elementary matrices generate `SL₂` over an arbitrary ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.

The block action is `MinusculeWeightTable.sl2BlockSL`; smoothness is supplied by
`TauCeti.SpecialLinear.instSmoothCoordinateHopfAlgebra`.
-/

public section

open WithConv

namespace TauCeti.MinusculeWeightTable

variable {B : Type*} {n : ℕ} (T : MinusculeWeightTable B (Fin n))

/-- Field-valued containment of a minuscule rank-one action in an integral closed subgroup
implies containment over every commutative ring. No reducedness is required of the value ring. -/
theorem sl2BlockSL_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n)) (i : B)
    (hfield : ∀ (K : Type) [Field K] (g : Matrix.SpecialLinearGroup (Fin 2) K),
      T.sl2BlockSL i g ∈ GeneralLinear.hopfIdealPointsSubgroup n I K)
    (R : Type*) [CommRing R] (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    T.sl2BlockSL i g ∈ GeneralLinear.hopfIdealPointsSubgroup n I R := by
  let U := SpecialLinear.coordinateHopfAlgebra ℤ 2
  let u : Matrix.SpecialLinearGroup (Fin 2) U :=
    (SpecialLinear.pointsMulEquiv (A := U) ℤ 2) (toConv (AlgHom.id ℤ U))
  have huniv : T.sl2BlockSL i u ∈ GeneralLinear.hopfIdealPointsSubgroup n I U := by
    let _ : IsReduced U := isReduced_of_smooth ℤ U
    rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff]
    intro x hx
    apply IsReduced.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro p hp
    let _ : p.IsPrime := hp
    let K : Type := FractionRing (U ⧸ p)
    let _ : Field K := FractionRing.field (U ⧸ p)
    let _ : Algebra ℤ K := Ring.toIntAlgebra K
    let f : U →ₐ[ℤ] K :=
      { __ := (algebraMap (U ⧸ p) K).comp (Ideal.Quotient.mk p)
        commutes' := by intro z; simp }
    have hz := (GeneralLinear.mem_hopfIdealPointsSubgroup_iff n I K _).mp
      (hfield K (Matrix.SpecialLinearGroup.map f.toRingHom u)) x hx
    simp only [← map_sl2BlockSL, AlgHom.toRingHom_eq_coe,
      ← GeneralLinear.mapValue_pointsMulEquiv_symm_apply,
      AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at hz
    -- The prime quotient embeds in its fraction field, so zero evaluation means membership in p.
    have hquot : Ideal.Quotient.mk p
        (((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm (T.sl2BlockSL i u)).ofConv x) = 0 :=
      (IsFractionRing.injective (U ⧸ p) K) (hz.trans (map_zero _).symm)
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hquot
  let f := ((SpecialLinear.pointsMulEquiv (R := ℤ) (A := R) 2).symm g).ofConv
  have hu : Matrix.SpecialLinearGroup.map f.toRingHom u = g :=
    SpecialLinear.map_pointsMulEquiv_id ℤ 2 g
  have h := GeneralLinear.map_mem_hopfIdealPointsSubgroup n I f huniv
  rw [map_sl2BlockSL] at h
  exact hu ▸ h

end TauCeti.MinusculeWeightTable
