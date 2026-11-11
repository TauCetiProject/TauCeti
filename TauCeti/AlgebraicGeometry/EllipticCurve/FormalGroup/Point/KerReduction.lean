/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Range
-- Proof-only: `O_u` is Henselian.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The formal group is the kernel of reduction

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A`, and let
`C` be a Weierstrass curve over the completed valuation ring `O_u` which is elliptic over the
completion `F_u`. The points of `C` over `F_u` reduce modulo `u` (`Point.reduction`), and the
points reducing to `(0 : 1 : 0)` form the kernel of reduction `E₁(F_u)`. This file makes that set a
subgroup and identifies it with the group `Ê(𝔪_u)` of formal-group parameters in the maximal
ideal: Silverman AEC VII.2.2.

## Main definitions

* `WeierstrassCurve.kerReduction`: the kernel of reduction `E₁(F_u)`, as a subgroup of the points
  of `C` over `F_u`.
* `WeierstrassCurve.formalPointAddEquivKerReduction`: the isomorphism `Ê(𝔪_u) ≃+ E₁(F_u)`.

## Main results

* `WeierstrassCurve.range_formalPointHomAdicCompletion_eq_kerReduction`: the image of the formal
  parametrisation is the kernel of reduction.
* `WeierstrassCurve.index_kerReduction`: the reduction exact sequence computes the index of
  `E₁(F_u)` as the nonsingular reduction count times the index of `E₀(F_u)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.2.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

-- `adicCompletionIntegers` is by definition `Valued.v.valuationSubring`, so the Henselian
-- structure on `O_u` also supplies the valuation-ring instance used by reduction.
private local instance : HenselianLocalRing R_u := inferInstanceAs (HenselianLocalRing O_u)

local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))

variable [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The kernel of reduction** `E₁(F_u)`: the points of `C` over the completion `F_u` that reduce
to `(0 : 1 : 0)` modulo `u`. -/
noncomputable def kerReduction : AddSubgroup (C.baseChange F_u).toAffine.Point :=
  (C.formalPointHomAdicCompletion u).range.copy
    {P | Affine.Point.reduction Valued.v P = ⟦![0, 1, 0]⟧} <| by
      ext P
      rw [Set.mem_ofPred_eq, Affine.Point.reduction_eq_zero_iff, AddMonoidHom.coe_range,
        range_formalPointHomAdicCompletion, Set.mem_ofPred_eq]

open scoped Classical in
@[simp]
theorem mem_kerReduction_iff {P : (C.baseChange F_u).toAffine.Point} :
    P ∈ C.kerReduction u ↔ Affine.Point.reduction Valued.v P = ⟦![0, 1, 0]⟧ :=
  Iff.rfl

open scoped Classical in
/-- **The image of the formal parametrisation is the kernel of reduction.** -/
theorem range_formalPointHomAdicCompletion_eq_kerReduction :
    (C.formalPointHomAdicCompletion u).range = C.kerReduction u :=
  (AddSubgroup.copy_eq _ _ _).symm

open scoped Classical in
/-- **The formal group is the kernel of reduction**, Silverman AEC VII.2.2: the formal
parametrisation `t ↦ (t / w(t), -1 / w(t))` is an isomorphism from the group `Ê(𝔪_u)` of
formal-group parameters in the maximal ideal onto the kernel of reduction `E₁(F_u)`. -/
noncomputable def formalPointAddEquivKerReduction :
    FormalGroupPoint C m_u ≃+ C.kerReduction u :=
  ((C.formalPointHomAdicCompletion u).ofInjective
      (C.formalPointHomAdicCompletion_injective u)).trans
    (AddEquiv.addSubgroupCongr (C.range_formalPointHomAdicCompletion_eq_kerReduction u))

open scoped Classical in
@[simp]
theorem coe_formalPointAddEquivKerReduction_apply (P : FormalGroupPoint C m_u) :
    (C.formalPointAddEquivKerReduction u P : (C.baseChange F_u).toAffine.Point) =
      C.formalPointHomAdicCompletion u P :=
  (rfl)

open scoped Classical in
/-- The reduction exact sequence computes the index of `E₁` in the whole point group. This
holds for any integral equation, including one with bad or nonminimal reduction. -/
theorem index_kerReduction :
    (C.kerReduction u).index =
      Nat.card ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point *
        ((C.baseChange F_u).toAffine.nonsingularReduction Valued.v).index := by
  have : IsIntegral O_u (C.baseChange F_u) := ⟨C, rfl⟩
  let W := (C.baseChange F_u).toAffine
  have hle : C.kerReduction u ≤ W.nonsingularReduction Valued.v := by
    intro P hP
    rw [Affine.mem_nonsingularReduction_iff, C.mem_kerReduction_iff u |>.mp hP,
      Projective.nonsingularLift_iff]
    exact Projective.nonsingular_zero
  have hker : (C.kerReduction u).addSubgroupOf (W.nonsingularReduction Valued.v) =
      (W.nonsingularReductionHom Valued.v).ker := by
    ext P
    rw [AddSubgroup.mem_addSubgroupOf, Affine.mem_ker_nonsingularReductionHom_iff,
      C.mem_kerReduction_iff u, Affine.Point.reduction_eq_zero_iff]
  rw [← AddSubgroup.relIndex_mul_index hle, AddSubgroup.relIndex, hker,
    AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr
      (Affine.nonsingularReductionHom_surjective Valued.v), AddSubgroup.card_top]

end WeierstrassCurve
