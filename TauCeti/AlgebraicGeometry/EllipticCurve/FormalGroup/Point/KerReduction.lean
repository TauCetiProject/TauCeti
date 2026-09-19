/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Range

/-!
# The formal group is the kernel of reduction

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A`, and let
`C` be a Weierstrass curve over the completed valuation ring `O_u` which is elliptic over the
completion `F_u`. The points of `C` over `F_u` reduce modulo `u` (`Point.reduction`), and the
points reducing to `(0 : 1 : 0)` form the kernel of reduction `E₁(F_u)`. This file makes that set a
subgroup and identifies it with the group `Ê(𝔪_u)` of formal-group parameters in the maximal
ideal: Silverman AEC VII.2.2.

Both halves are already on hand. `Point.reduction_eq_zero_iff` describes the kernel of reduction
as the point at infinity together with the points whose `x`-coordinate has a pole, and
`range_formalPointHomAdicCompletion` shows that this is exactly the image of the formal
parametrisation, which is injective. In particular the kernel of reduction is a subgroup because it
is the image of an additive homomorphism.

## Main definitions

* `WeierstrassCurve.kerReduction`: the kernel of reduction `E₁(F_u)`, as a subgroup of the points
  of `C` over `F_u`.
* `WeierstrassCurve.formalPointAddEquivKerReduction`: the isomorphism `Ê(𝔪_u) ≃+ E₁(F_u)`.

## Main results

* `WeierstrassCurve.range_formalPointHomAdicCompletion_eq_kerReduction`: the image of the formal
  parametrisation is the kernel of reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.2.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u

local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))

/-- A curve over the completed valuation ring has an integral model for the valuation of the
completion, namely itself: the completed valuation ring is by definition the valuation subring of
that valuation. -/
instance isIntegral_baseChange_adicCompletion :
    IsIntegral (Valued.v : Valuation F_u (WithZero (Multiplicative ℤ))).valuationSubring
      (C.baseChange F_u) :=
  ⟨C, rfl⟩

variable [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The kernel of reduction** `E₁(F_u)`: the points of `C` over the completion `F_u` that reduce
to `(0 : 1 : 0)` modulo `u`. It is a subgroup because it is the image of the formal
parametrisation (`range_formalPointHomAdicCompletion_eq_kerReduction`). -/
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

end WeierstrassCurve
