/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.GroupTheory.GroupAction.FixedPoints
public import TauCeti.RepresentationTheory.Continuous.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The trivial F₂ coefficient representation

This file defines a trivial object of `TopRep ℤ G` whose carrier is a universe lift of `ZMod 2`.
It is stable under restriction and is smooth discrete, as needed for continuous cohomology with
trivial `𝔽₂` coefficients.

For `G : Type u`, Mathlib's continuous-cohomology resolution requires the coefficient module to
live in `Type u`. The carrier of `trivialF2 G` is therefore `ULift.{u} (ZMod 2)`, not
`ZMod 2`. The action is trivial, and restriction to a subgroup is definitionally the corresponding
trivial coefficient object for that subgroup.

## Main definitions

* `TauCeti.trivialF2`: trivial `𝔽₂` coefficients over an arbitrary
  universe.
* `TauCeti.trivialF2ResMap`: restriction on continuous cohomology with trivial `𝔽₂`
  coefficients.
* `TauCeti.trivialF2QuotientEquivFixedPoints`: trivial `𝔽₂` coefficients on a quotient `G ⧸ N`,
  identified with the `N`-fixed points of the ambient trivial `𝔽₂` coefficients.

## Main results

* `TauCeti.trivialF2_V`: the carrier is `ULift (ZMod 2)`.
* `TauCeti.trivialF2Equiv`: the additive equivalence that crosses the universe lift.
* `TauCeti.trivialF2_ρ_apply_apply`: every monoid element acts trivially.
* `TauCeti.trivialF2Pairing`: multiplication in `𝔽₂` as a biadditive pairing on the lifted
  carrier, with `TauCeti.trivialF2Pairing_smul_smul` its equivariance.
* `TauCeti.ofDiscreteModule_trivialF2`: the coefficient dictionary recovers `trivialF2`.
* `TauCeti.res_trivialF2`: restriction preserves the coefficient object on the nose.
* `TauCeti.isSmoothDiscrete_trivialF2`: the coefficient object is smooth discrete.
* `TauCeti.trivialF2QuotientEquivFixedPoints_smul`: that identification is equivariant for the
  `G ⧸ N`-actions, with `TauCeti.trivialF2Equiv_apply_trivialF2QuotientEquivFixedPoints` its
  value rule.
-/

public section

namespace TauCeti

universe u

section Monoid

variable (G : Type u) [Monoid G]

/-- Trivial `𝔽₂` coefficients as an object of `TopRep ℤ G` in the universe of `G`.

The lift is forced by the universe of Mathlib's continuous-cohomology resolution. -/
noncomputable def trivialF2 : TopRep ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} (ZMod 2)))

/-- The carrier of `trivialF2 G` is the universe lift of `ZMod 2`. -/
@[simp] theorem trivialF2_V : (trivialF2 G).V = ULift.{u} (ZMod 2) := (rfl)

/-- The additive equivalence from the lifted carrier of `trivialF2 G` to `ZMod 2`. -/
noncomputable def trivialF2Equiv : (trivialF2 G).V ≃+ ZMod 2 :=
  -- The carrier is `ULift.{u} (ZMod 2)` by `trivialF2_V`; that equality is definitional but is an
  -- equality of types, so it cannot be rewritten into the statement of the equivalence, and
  -- `AddEquiv.ulift` is elaborated against the unfolded carrier instead.
  AddEquiv.ulift

/-- `trivialF2Equiv` sends a lifted element to its underlying value. -/
@[simp]
theorem trivialF2Equiv_apply (x : ULift.{u} (ZMod 2)) :
    trivialF2Equiv G (cast (trivialF2_V G).symm x) = x.down :=
  -- `(rfl)`, not `rfl`: the body of `trivialF2Equiv` is hidden, and this lemma is its public
  -- application rule.
  (rfl)

/-- The inverse of `trivialF2Equiv` lifts a value. -/
@[simp]
theorem trivialF2Equiv_symm_apply (x : ZMod 2) :
    (trivialF2Equiv G).symm x = cast (trivialF2_V G).symm (ULift.up x) :=
  -- As above, the parenthesized proof keeps the hidden definition out of downstream reduction.
  (rfl)

/-- The lifted carrier of `trivialF2 G` has the discrete topology. -/
instance : DiscreteTopology (trivialF2 G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod 2)))

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Applying the discrete coefficient dictionary to the carrier of `trivialF2` recovers the
coefficient object itself.

Comparisons between explicit cocycle groups and continuous cohomology are stated for the
coefficient object `ofDiscreteModule ℤ G M` attached to a discrete module `M`. Taking
`M := (trivialF2 G).V`, this equality identifies that object with `trivialF2 G`, so such a
comparison carries a class computed from explicit cochains into continuous cohomology with
trivial `𝔽₂` coefficients. -/
@[simp]
theorem ofDiscreteModule_trivialF2 :
    ofDiscreteModule ℤ G (trivialF2 G).V = trivialF2 G :=
  ofDiscreteModule_eq_self (trivialF2 G)

/-- Every monoid element acts trivially on `trivialF2 G`.

This is the public action rule of the object, in the same role as
`TauCeti.ofDiscreteModule_ρ_apply_apply`: the body of `trivialF2` is not exposed, so a consumer
cannot reach `ContRepresentation.trivial_apply` through it. -/
@[simp]
theorem trivialF2_ρ_apply_apply (g : G) (x : (trivialF2 G).V) :
    (trivialF2 G).ρ g x = x :=
  ContRepresentation.trivial_apply g x

/-- Multiplication in `𝔽₂`, transported along `trivialF2Equiv` to a biadditive pairing on the
lifted carrier of `trivialF2 G`. It is the coefficient pairing of the `𝔽₂`-valued cup products
and of the identities of the Evens norm. -/
noncomputable def trivialF2Pairing : (trivialF2 G).V →+ (trivialF2 G).V →+ (trivialF2 G).V :=
  ((AddMonoidHom.mul.comp (trivialF2Equiv G).toAddMonoidHom).compl₂
    (trivialF2Equiv G).toAddMonoidHom).compr₂ (trivialF2Equiv G).symm.toAddMonoidHom

/-- The pairing multiplies the underlying values in `ZMod 2`. -/
@[simp]
theorem trivialF2Pairing_apply (x y : (trivialF2 G).V) :
    trivialF2Pairing G x y =
      (trivialF2Equiv G).symm (trivialF2Equiv G x * trivialF2Equiv G y) :=
  (rfl)

/-- The pairing is `G`-equivariant, the action being trivial. -/
theorem trivialF2Pairing_smul_smul (g : G) (x y : (trivialF2 G).V) :
    trivialF2Pairing G (g • x) (g • y) = g • trivialF2Pairing G x y := by
  simp

variable [TopologicalSpace G]

/-- The trivial `𝔽₂` coefficient object is smooth discrete. -/
theorem isSmoothDiscrete_trivialF2 : IsSmoothDiscrete ℤ (trivialF2 G) :=
  isSmoothDiscrete_trivial ℤ (ULift.{u} (ZMod 2))

end Monoid

section Group

variable (G : Type u) [Group G]

/-- Restriction preserves the trivial `𝔽₂` coefficient object on the nose. -/
@[simp]
theorem res_trivialF2 (S : Subgroup G) :
    TopRep.res (S.subtype : S →* G) (trivialF2 G) = trivialF2 S :=
  res_trivial ℤ G (ULift.{u} (ZMod 2)) S.subtype

open CategoryTheory _root_.ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction on continuous cohomology with trivial `𝔽₂` coefficients. This is the
generic restriction map followed by the on-the-nose identification `res_trivialF2`. -/
noncomputable def trivialF2ResMap (S : Subgroup G) (n : ℕ) :
    continuousCohomology n (trivialF2 G) ⟶ continuousCohomology n (trivialF2 S) :=
  ContinuousCohomology.res S (trivialF2 G) n ≫
    eqToHom (congrArg (continuousCohomology n) (res_trivialF2 G S))

/-- The defining equation of restriction with trivial `𝔽₂` coefficients. -/
theorem trivialF2ResMap_def (S : Subgroup G) (n : ℕ) :
    trivialF2ResMap G S n = ContinuousCohomology.res S (trivialF2 G) n ≫
      eqToHom (congrArg (continuousCohomology n) (res_trivialF2 G S)) :=
  (rfl)

end Group

section Quotient

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Trivial `𝔽₂` coefficients on `G / N` are additively equivalent to the `N`-fixed points of
the ambient trivial coefficients. -/
noncomputable def trivialF2QuotientEquivFixedPoints :
    (trivialF2 (G ⧸ N)).V ≃+ FixedPoints.addSubgroup N (trivialF2 G).V where
  toFun x := ⟨(trivialF2Equiv G).symm (trivialF2Equiv (G ⧸ N) x), by
    rw [FixedPoints.mem_addSubgroup]
    intro n
    simp only [Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]⟩
  invFun x := (trivialF2Equiv (G ⧸ N)).symm (trivialF2Equiv G x.1)
  left_inv x := by simp
  right_inv x := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    apply (trivialF2Equiv G).injective
    simp

/-- The coefficient equivalence does not change the underlying `ZMod 2` value. -/
@[simp]
theorem trivialF2Equiv_apply_trivialF2QuotientEquivFixedPoints
    (x : (trivialF2 (G ⧸ N)).V) :
    trivialF2Equiv G (trivialF2QuotientEquivFixedPoints N x : (trivialF2 G).V) =
      trivialF2Equiv (G ⧸ N) x := by
  simp [trivialF2QuotientEquivFixedPoints]

/-- The coefficient equivalence is equivariant for the quotient actions. -/
theorem trivialF2QuotientEquivFixedPoints_smul (q : G ⧸ N)
    (x : (trivialF2 (G ⧸ N)).V) :
    trivialF2QuotientEquivFixedPoints N (q • x) =
      q • trivialF2QuotientEquivFixedPoints N x := by
  apply Subtype.ext
  induction q using QuotientGroup.induction_on with
  | H g =>
    apply (trivialF2Equiv G).injective
    rw [coe_quotient_smul_fixedPoints_addSubgroup,
      coe_smul_fixedPoints_addSubgroup]
    simp

end Quotient

end TauCeti
