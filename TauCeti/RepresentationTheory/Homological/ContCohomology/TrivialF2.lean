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

The homomorphism and isomorphism maps follow the `cohomFpMap` and `cohomFpLinearEquiv`
construction in `TauCeti/RepresentationTheory/Homological/ContCohomology/TrivialFp.lean`,
with `ℤ` as the scalar ring used by the all-degree cup product.

For `G : Type u`, Mathlib's continuous-cohomology resolution requires the coefficient module to
live in `Type u`. The carrier of `trivialF2 G` is therefore `ULift.{u} (ZMod 2)`, not
`ZMod 2`. The action is trivial, and restriction to a subgroup is definitionally the corresponding
trivial coefficient object for that subgroup.

## Main definitions

* `TauCeti.trivialF2`: trivial `𝔽₂` coefficients over an arbitrary
  universe.
* `TauCeti.trivialF2ResMap`: restriction on continuous cohomology with trivial `𝔽₂`
  coefficients.
* `TauCeti.trivialF2Map`: pullback along any continuous group homomorphism with trivial
  `𝔽₂` coefficients, and `TauCeti.trivialF2Iso` for a topological group isomorphism.
* `TauCeti.trivialF2QuotientEquivFixedPoints`: trivial `𝔽₂` coefficients on a quotient `G ⧸ N`,
  identified with the `N`-fixed points of the ambient trivial `𝔽₂` coefficients.

## Main results

* `TauCeti.trivialF2_V`: the carrier is `ULift (ZMod 2)`.
* `TauCeti.trivialF2Equiv`: the additive equivalence that crosses the universe lift.
* `TauCeti.trivialF2_ρ_apply_apply`: every monoid element acts trivially.
* `TauCeti.trivialF2Pairing`: multiplication in `𝔽₂` as a biadditive pairing on the lifted
  carrier, with `TauCeti.trivialF2Pairing_smul_smul` its equivariance.
* `TauCeti.ofDiscreteModule_trivialF2`: the coefficient dictionary recovers `trivialF2`, with
  `TauCeti.eqToHom_ofDiscreteModule_trivialF2_apply` and
  `TauCeti.eqToHom_ofDiscreteModule_trivialF2_symm_apply` its carrier-level reading.
* `TauCeti.res_trivialF2`: restriction preserves the coefficient object on the nose.
* `TauCeti.trivialF2Map_subgroupSubtype`: the general pullback recovers subgroup restriction.
* `TauCeti.trivialF2Map_id`, `TauCeti.trivialF2Map_comp`: the functoriality laws.
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

/-- **The transported identity of `TauCeti.ofDiscreteModule_trivialF2` acts as the identity on
carriers**: `TauCeti.eqToHom (ofDiscreteModule_trivialF2 G)` is the morphism
`TauCeti.eqToIso (ofDiscreteModule_trivialF2 G)` read by `TauCeti.eqToIso.hom`, so it is the
identity on the carrier of `trivialF2 G`. -/
@[simp]
theorem eqToHom_ofDiscreteModule_trivialF2_apply (x : (trivialF2 G).V) :
    (CategoryTheory.eqToHom (ofDiscreteModule_trivialF2 G)) x = x := by
  rw [CategoryTheory.eqToHom]
  rfl

/-- **The transported inverse of `TauCeti.ofDiscreteModule_trivialF2` acts as the identity on
carriers**: `TauCeti.eqToHom (ofDiscreteModule_trivialF2 G).symm` is the inverse morphism
`TauCeti.eqToIso (ofDiscreteModule_trivialF2 G)` read by `TauCeti.eqToIso.inv`, so it too is the
identity on the carrier of `trivialF2 G`. -/
-- `TopRep.eqToHom_hom_apply` rewrites the left-hand side to a cast first.
theorem eqToHom_ofDiscreteModule_trivialF2_symm_apply (x : (trivialF2 G).V) :
    (CategoryTheory.eqToHom (ofDiscreteModule_trivialF2 G).symm) x = x := by
  rw [CategoryTheory.eqToHom]
  rfl

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

section Hom

open CategoryTheory

variable {G H J : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Pulling trivial `𝔽₂` coefficients back along a continuous group homomorphism gives the
trivial coefficient object on its source. -/
@[simp]
theorem res_trivialF2_hom (φ : H →ₜ* G) :
    TopRep.res (φ : H →* G) (trivialF2 G) = trivialF2 H :=
  res_trivial ℤ G (ULift.{u} (ZMod 2)) φ.toMonoidHom

/-- Contravariant continuous cohomology with trivial `𝔽₂` coefficients along a continuous
group homomorphism. -/
noncomputable def trivialF2Map (φ : H →ₜ* G) (n : ℕ) :
    continuousCohomology n (trivialF2 G) ⟶ continuousCohomology n (trivialF2 H) :=
  _root_.ContinuousCohomology.map φ (eqToHom (res_trivialF2_hom φ)) n

/-- The trivial-coefficient map is Mathlib's compatible-pair map with the canonical coefficient
identification. -/
theorem trivialF2Map_def (φ : H →ₜ* G) (n : ℕ) :
    trivialF2Map φ n =
      _root_.ContinuousCohomology.map φ (eqToHom (res_trivialF2_hom φ)) n :=
  (rfl)

/-- Pullback along a subgroup inclusion is the named restriction map. -/
@[simp]
theorem trivialF2Map_subgroupSubtype (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (n : ℕ) :
    trivialF2Map (ContinuousMonoidHom.subgroupSubtype S) n =
      trivialF2ResMap G S n := by
  have hsubtype :
      ((ContinuousMonoidHom.subgroupSubtype S : S →ₜ* G) : S →* G) = S.subtype := rfl
  have hcoeff :
      TopRep.res ((ContinuousMonoidHom.subgroupSubtype S : S →ₜ* G) : S →* G)
        (trivialF2 G) = trivialF2 S := by
    rw [hsubtype]
    exact res_trivialF2 G S
  have hmap : eqToHom
      (res_trivialF2_hom (ContinuousMonoidHom.subgroupSubtype S)) =
      𝟙 (trivialF2 S) := eqToHom_refl _ _
  have hres : eqToHom (congrArg (continuousCohomology n) (res_trivialF2 G S)) =
      𝟙 (continuousCohomology n (trivialF2 S)) := eqToHom_refl _ _
  have hcomparison :
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
        (𝟙 (trivialF2 S)) n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
        (𝟙 (TopRep.res (S.subtype : S →* G) (trivialF2 G))) n := by
    have hmaps : HEq (𝟙 (trivialF2 S))
        (𝟙 (TopRep.res (S.subtype : S →* G) (trivialF2 G))) := by
      rw [hsubtype] at hcoeff
      cases hcoeff
      rfl
    exact TauCeti.ContinuousCohomology.map_congr rfl hmaps n
  calc
    trivialF2Map (ContinuousMonoidHom.subgroupSubtype S) n =
        _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (trivialF2 S)) n := by
      rw [trivialF2Map_def, hmap]
    _ = _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (TopRep.res (S.subtype : S →* G) (trivialF2 G))) n ≫
          𝟙 (continuousCohomology n (trivialF2 S)) :=
      hcomparison.trans (Category.comp_id _).symm
    _ = trivialF2ResMap G S n := by
      rw [trivialF2ResMap_def, TauCeti.ContinuousCohomology.res_def, hres]

/-- The map induced by the identity group homomorphism is the identity. -/
@[simp]
theorem trivialF2Map_id (n : ℕ) :
    trivialF2Map (ContinuousMonoidHom.id G) n = 𝟙 _ := by
  have h : eqToHom (res_trivialF2_hom (ContinuousMonoidHom.id G)) =
      𝟙 (trivialF2 G) := eqToHom_refl _ _
  simpa only [trivialF2Map, h] using
    (_root_.ContinuousCohomology.map_id (trivialF2 G) n)

/-- Trivial-coefficient maps compose contravariantly. -/
@[simp]
theorem trivialF2Map_comp (φ : H →ₜ* G) (ψ : J →ₜ* H) (n : ℕ) :
    trivialF2Map (φ.comp ψ) n = trivialF2Map φ n ≫ trivialF2Map ψ n := by
  have hφ : eqToHom (res_trivialF2_hom φ) = 𝟙 (trivialF2 H) := eqToHom_refl _ _
  have hψ : eqToHom (res_trivialF2_hom ψ) = 𝟙 (trivialF2 J) := eqToHom_refl _ _
  have hcomp : eqToHom (res_trivialF2_hom (φ.comp ψ)) =
      𝟙 (trivialF2 J) := eqToHom_refl _ _
  unfold trivialF2Map
  rw [← _root_.ContinuousCohomology.map_comp]
  exact TauCeti.ContinuousCohomology.map_congr rfl
    (heq_of_eq (by simpa only [hφ, hψ, hcomp, Functor.map_id,
      Category.id_comp] :
        (TopRep.resFunctor (ψ : J →* H)).map (eqToHom (res_trivialF2_hom φ)) ≫
          eqToHom (res_trivialF2_hom ψ) =
            eqToHom (res_trivialF2_hom (φ.comp ψ))).symm) n

/-- A topological group isomorphism induces an equivalence on continuous cohomology with
trivial `𝔽₂` coefficients. The cohomology map runs along the inverse group isomorphism. -/
noncomputable def trivialF2Iso (e : G ≃ₜ* H) (n : ℕ) :
    continuousCohomology n (trivialF2 G) ≅ continuousCohomology n (trivialF2 H) := by
  let f : H →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom e.symm
  let g : G →ₜ* H := ContinuousMonoidHom.toContinuousMonoidHom e
  have hfg : f.comp g = ContinuousMonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  have hgf : g.comp f = ContinuousMonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  exact
    { hom := trivialF2Map f n
      inv := trivialF2Map g n
      hom_inv_id := by rw [← trivialF2Map_comp, hfg, trivialF2Map_id]
      inv_hom_id := by rw [← trivialF2Map_comp, hgf, trivialF2Map_id] }

/-- The forward cohomology transport is pullback along the inverse group isomorphism. -/
@[simp]
theorem trivialF2Iso_hom (e : G ≃ₜ* H) (n : ℕ) :
    (trivialF2Iso e n).hom =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom e.symm) n :=
  (rfl)

/-- The inverse cohomology transport is pullback along the group isomorphism. -/
@[simp]
theorem trivialF2Iso_inv (e : G ≃ₜ* H) (n : ℕ) :
    (trivialF2Iso e n).inv =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom e) n :=
  (rfl)

end Hom

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
