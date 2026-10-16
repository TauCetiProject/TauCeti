/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Continuous.TopRep.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees

/-!
# Shapiro's lemma for inflated induced representations

Let `G` be a profinite group, `V` an open normal subgroup, `C` a subgroup of the finite quotient
`G ⧸ V` and `U = π⁻¹(C)` its preimage in `G`, an open subgroup. A representation `B` of `C` inflates
to a smooth discrete representation of `U` (`comapInflation`), and the representation
`Ind_C^{G ⧸ V} B` of the finite quotient inflates to one of `G`. This file proves that

```text
Hⁿ(G, Inf Ind_C^{G ⧸ V} B) ≅ Hⁿ(U, Inf B)
```

in every degree (`indInflationShapiroIso`): the finite-index comparison identifies induction with
coinduction, inflation commutes with coinduction (`coindInflationIso`:
precomposition with `G → G ⧸ V` identifies the `C`-equivariant functions `G ⧸ V → B` with the
locally constant `U`-equivariant functions `G → B`), and continuous Shapiro's lemma
`shapiroIsoTopRep` computes the cohomology of the coinduced module. The comparison of induction
with coinduction is Amelia Livingston's `Rep.indCoindIso` in Mathlib.

For a local field `K` and a finite Galois extension `L/K` cut out by `V`, this is the step of the
dévissage of the local Euler characteristic that replaces an induced module `Ind_C^{Gal(L/K)} B` by
the module `B` over the fixed field of `C`.

## Main definitions

* `comapInflation`: the inflation of a representation of `C ≤ G ⧸ V` to the preimage of `C`.
* `comapInflationLinearEquiv`: the inflation has the underlying module of the representation.
* `coindInflationIso`: `Inf Coind_C^{G ⧸ V} B ≅ Coind_U^G Inf B`.
* `indInflationIso`: `Inf Ind_C^{G ⧸ V} B ≅ Coind_U^G Inf B`.
* `indInflationShapiroIso`: `Hⁿ(G, Inf Ind_C^{G ⧸ V} B) ≅ Hⁿ(U, Inf B)`.

## Implementation notes

Mathlib's `Rep.indCoindIso` requires the coefficient universe to contain that of the ring, and
`shapiroIsoTopRep` requires it to be the universe of the group, so for a ring `R : Type v` the
Shapiro isomorphism takes `G : Type (max u v)` and coefficients in `Type (max u v)`. In this file
the universe levels of `indInflationIso` and `indInflationShapiroIso` are given explicitly:
elaborating `max ?u ?v =?= max u v` otherwise times out. The inflation `comapInflation` only
needs `R` to be a ring; the comparison of inflation with coinduction needs it to be commutative,
as Mathlib's `Rep.coind` does.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.4), and the
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Inflation

variable {R : Type v} [Ring R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : OpenNormalSubgroup G) (C : Subgroup (G ⧸ V.toSubgroup))

/-- The inflation of a representation `B` of a subgroup `C` of the quotient `G ⧸ V` to the
preimage of `C` in `G`, with the discrete topology. It is smooth because `V` is open. Its
underlying module is identified with that of `B` by `comapInflationLinearEquiv`. -/
noncomputable def comapInflation (B : Rep.{w} R C) :
    SmoothDiscreteTopRep.{v, u, w} R (C.comap (QuotientGroup.mk' V.toSubgroup)) :=
  ⟨TopRep.res ((QuotientGroup.mk' V.toSubgroup).subgroupComap C) (discreteTopRep R C B),
    (isSmoothDiscrete_discreteTopRep R C B).res
      ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _)⟩

variable {V C} (B : Rep.{w} R C)

/-- The inflation is the discrete representation of `C` restricted along `π⁻¹(C) → C`. -/
theorem comapInflation_obj :
    (comapInflation V C B).obj =
      TopRep.res ((QuotientGroup.mk' V.toSubgroup).subgroupComap C) (discreteTopRep R C B) :=
  (rfl)

/-- Inflation does not change the underlying module: the identification of the underlying module
of the inflation with that of `B`. -/
noncomputable def comapInflationLinearEquiv : (comapInflation V C B).obj.V ≃ₗ[R] B.V :=
  LinearEquiv.refl R B.V

/-- An element of the preimage of `C` acts on the inflation through its image in `C`. -/
@[simp]
theorem comapInflationLinearEquiv_ρ_apply (x : C.comap (QuotientGroup.mk' V.toSubgroup))
    (b : (comapInflation V C B).obj.V) :
    comapInflationLinearEquiv B ((comapInflation V C B).obj.ρ x b) =
      B.ρ ((QuotientGroup.mk' V.toSubgroup).subgroupComap C x) (comapInflationLinearEquiv B b) :=
  (rfl)

/-- An element of the preimage of `C` acts on the inflation through its image in `C`, transported
along the inverse identification. -/
@[simp]
theorem comapInflation_ρ_comapInflationLinearEquiv_symm_apply
    (x : C.comap (QuotientGroup.mk' V.toSubgroup)) (b : B.V) :
    (comapInflation V C B).obj.ρ x ((comapInflationLinearEquiv B).symm b) =
      (comapInflationLinearEquiv B).symm
        (B.ρ ((QuotientGroup.mk' V.toSubgroup).subgroupComap C x) b) :=
  (rfl)

end Inflation

section Comparison

variable {R : Type v} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : OpenNormalSubgroup G} {C : Subgroup (G ⧸ V.toSubgroup)} (B : Rep.{w} R C)

/-- A function coinduced to `G` from the inflation of `B` is invariant under right translation by
`V`: `V` is normal, contained in the preimage of `C`, and acts trivially on `B`. -/
private theorem apply_mul_of_mem (F : DiscreteCoind G (C.comap (QuotientGroup.mk' V.toSubgroup))
      ((ofSmoothDiscrete R _).obj (comapInflation V C B)).V) (g : G) {x : G}
    (hx : x ∈ V.toSubgroup) : F (g * x) = F g := by
  have h1 : QuotientGroup.mk' V.toSubgroup (g * x * g⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.Normal.conj_mem inferInstance x hx g)
  have hgx : g * x * g⁻¹ ∈ C.comap (QuotientGroup.mk' V.toSubgroup) := by
    rw [Subgroup.mem_comap, h1]
    exact one_mem C
  have h := DiscreteCoind.apply_mul F ⟨_, hgx⟩ g
  rw [inv_mul_cancel_right] at h
  have h2 : (QuotientGroup.mk' V.toSubgroup).subgroupComap C ⟨_, hgx⟩ = 1 := Subtype.ext h1
  rw [h, ofSmoothDiscrete_obj_smul]
  apply (comapInflationLinearEquiv B).injective
  exact (comapInflationLinearEquiv_ρ_apply B _ (F g)).trans (by rw [h2, map_one]; rfl)

/-- Inflation commutes with coinduction: precomposition with the quotient map `G → G ⧸ V`
identifies `Coind_C^{G ⧸ V} B` with the locally constant functions `G → B` equivariant for the
preimage of `C`. -/
noncomputable def coindInflationEquiv :
    (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.coind C.subtype B)).V ≃ₗ[R]
      DiscreteCoind G (C.comap (QuotientGroup.mk' V.toSubgroup))
        ((ofSmoothDiscrete R _).obj (comapInflation V C B)).V where
  -- `QuotientGroup.mk` is multiplicative by definition, so equivariance in both directions is the
  -- defining law of the source on representatives.
  toFun f := DiscreteCoind.mk _ _ _ (fun g ↦ (comapInflationLinearEquiv B).symm (f.1 g))
    ((IsLocallyConstant.of_discrete f.1).comp_continuous QuotientGroup.continuous_mk)
    fun u g ↦ f.2 ((QuotientGroup.mk' V.toSubgroup).subgroupComap C u) g
  invFun F := ⟨fun q ↦ Quotient.liftOn' q (fun g ↦ comapInflationLinearEquiv B (F g))
      fun a b hab ↦ by
        rw [← mul_inv_cancel_left a b]
        exact congrArg _ (apply_mul_of_mem B F a (QuotientGroup.leftRel_apply.1 hab)).symm, by
    rintro ⟨c, hc⟩ q
    induction c using QuotientGroup.induction_on
    induction q using QuotientGroup.induction_on
    exact DiscreteCoind.apply_mul F ⟨_, hc⟩ _⟩
  left_inv f := by
    apply Subtype.ext
    funext q
    induction q using QuotientGroup.induction_on
    rfl
  right_inv F := DiscreteCoind.ext fun _ ↦ rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison precomposes a coinduced function with the quotient map. -/
@[simp]
theorem coindInflationEquiv_apply
    (f : (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.coind C.subtype B)).V) (g : G) :
    coindInflationEquiv B f g = (comapInflationLinearEquiv B).symm (f.1 g) :=
  (rfl)

/-- The inverse comparison descends a coinduced function along the quotient map. -/
@[simp]
theorem coindInflationEquiv_symm_apply_mk
    (F : DiscreteCoind G (C.comap (QuotientGroup.mk' V.toSubgroup))
      ((ofSmoothDiscrete R _).obj (comapInflation V C B)).V)
    (g : G) : ((coindInflationEquiv B).symm F).1 g = comapInflationLinearEquiv B (F g) :=
  (rfl)

variable [CompactSpace G]

/-- The inflation of a discrete representation of `G ⧸ V` is discrete. -/
local instance : DiscreteTopology (TopRep.res (QuotientGroup.mk' V.toSubgroup)
    (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.coind C.subtype B))).V :=
  inferInstanceAs (DiscreteTopology (discreteTopRep R _ (Rep.coind C.subtype B)).V)

/-- The inflation of `Coind_C^{G ⧸ V} B` to `G` is the coinduction to `G` of the inflation of `B`
to the preimage of `C`. -/
noncomputable def coindInflationIso :
    TopRep.res (QuotientGroup.mk' V.toSubgroup)
        (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.coind C.subtype B)) ≅
      (coindTopRep R G (C.comap (QuotientGroup.mk' V.toSubgroup))
        (comapInflation V C B)).obj :=
  eqToIso (ofDiscreteModule_eq_self _).symm ≪≫
    ofDiscreteModuleIso (coindInflationEquiv B) (fun _ _ ↦ DiscreteCoind.ext fun _ ↦ rfl) ≪≫
    eqToIso (toSmoothDiscrete_obj_obj R G (coindDiscreteRep R G
      (C.comap (QuotientGroup.mk' V.toSubgroup))
        ((ofSmoothDiscrete R _).obj (comapInflation V C B)))).symm

/-- The comparison acts on underlying functions as `coindInflationEquiv`, by precomposition with
the quotient map. -/
@[simp]
theorem coindInflationIso_hom_hom_apply
    (f : (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.coind C.subtype B)).V) :
    (coindInflationIso B).hom.hom f = coindInflationEquiv B f := by
  rw [coindInflationIso, Iso.trans_hom, Iso.trans_hom, ofDiscreteModuleIso_hom]
  rfl

/-- The inverse comparison acts on underlying functions as the inverse of `coindInflationEquiv`,
by descent along the quotient map. -/
@[simp]
theorem coindInflationIso_inv_hom_apply
    (F : DiscreteCoind G (C.comap (QuotientGroup.mk' V.toSubgroup))
      ((ofSmoothDiscrete R _).obj (comapInflation V C B)).V) :
    (coindInflationIso B).inv.hom F = (coindInflationEquiv B).symm F := by
  apply (coindInflationEquiv B).injective
  rw [← coindInflationIso_hom_hom_apply, LinearEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (coindInflationIso B).inv_hom_id F

open Classical in
/-- The inflation of `Ind_C^{G ⧸ V} B` to `G` is the coinduction to `G` of the inflation of `B` to
the preimage of `C`: Mathlib's finite-index comparison `Rep.indCoindIso` followed by
`coindInflationIso`. -/
noncomputable def indInflationIso (B : Rep.{max w v} R C) :
    TopRep.res (QuotientGroup.mk' V.toSubgroup)
        (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.ind C.subtype B)) ≅
      (coindTopRep R G (C.comap (QuotientGroup.mk' V.toSubgroup))
        (comapInflation V C B)).obj :=
  (TopRep.resFunctor (QuotientGroup.mk' V.toSubgroup)).mapIso
      ((discreteTopRepFunctor R (G ⧸ V.toSubgroup)).mapIso (Rep.indCoindIso B)) ≪≫
    coindInflationIso B

open Classical in
/-- The comparison `indInflationIso` is Mathlib's finite-index comparison, inflated, followed by
`coindInflationIso`. -/
theorem indInflationIso_hom (B : Rep.{max w v} R C) :
    (indInflationIso B).hom =
      (TopRep.resFunctor (QuotientGroup.mk' V.toSubgroup)).map
          ((discreteTopRepFunctor R (G ⧸ V.toSubgroup)).map (Rep.indCoindIso B).hom) ≫
        (coindInflationIso B).hom :=
  (rfl)

end Comparison

section Shapiro

variable {R : Type v} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type (max u v)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {V : OpenNormalSubgroup G} {C : Subgroup (G ⧸ V.toSubgroup)}
  (B : Rep.{max u v} R C)

/-- **Shapiro's lemma for inflated induced representations.** For an open normal subgroup `V` of
a profinite group `G`, a subgroup `C` of `G ⧸ V` and a representation `B` of `C`, the cohomology of
`G` with coefficients in the inflation of `Ind_C^{G ⧸ V} B` is the cohomology of the preimage of
`C` with coefficients in the inflation of `B`. -/
noncomputable def indInflationShapiroIso (n : ℕ) :
    continuousCohomology n (TopRep.res (QuotientGroup.mk' V.toSubgroup)
        (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.ind C.subtype B))) ≅
      continuousCohomology n (comapInflation V C B).obj :=
  (continuousCohomologyFunctor R G n).mapIso (indInflationIso.{max u v, v, u} B) ≪≫
    -- The preimage of `C` is open, hence closed, as `G ⧸ V` is discrete.
    shapiroIsoTopRep (C.comap (QuotientGroup.mk' V.toSubgroup))
      (Subgroup.isClosed_of_isOpen _
        ((isOpen_discrete (C : Set (G ⧸ V.toSubgroup))).preimage QuotientGroup.continuous_mk))
      (comapInflation V C B) n

/-- The Shapiro isomorphism for inflated induced representations is the coefficient map of
`indInflationIso` followed by the canonical Shapiro map: restriction to the preimage of `C` and
evaluation at `1`. -/
@[simp]
theorem indInflationShapiroIso_hom (n : ℕ) :
    (indInflationShapiroIso.{u, v} B n).hom =
      coeffMap (indInflationIso.{max u v, v, u} B).hom n ≫
        shapiroMapTopRep (C.comap (QuotientGroup.mk' V.toSubgroup)) (comapInflation V C B) n :=
  congrArg (coeffMap (indInflationIso.{max u v, v, u} B).hom n ≫ ·) (shapiroIsoTopRep_hom _ _ _ n)

/-- The inflation of `Ind_C^{G ⧸ V} B` to `G` and the inflation of `B` to the preimage of `C` have
cohomology groups of the same cardinality. -/
theorem natCard_continuousCohomology_ind_inflation (n : ℕ) :
    Nat.card (continuousCohomology n (TopRep.res (QuotientGroup.mk' V.toSubgroup)
        (discreteTopRep R (G ⧸ V.toSubgroup) (Rep.ind C.subtype B)))) =
      Nat.card (continuousCohomology n (comapInflation V C B).obj) :=
  Nat.card_congr (indInflationShapiroIso.{u, v} B n).toContinuousLinearEquiv.toEquiv

end Shapiro

end TauCeti.ContinuousCohomology
