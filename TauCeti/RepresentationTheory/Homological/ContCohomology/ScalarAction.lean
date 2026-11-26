/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.EqToHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# Scalar actions on the continuous cohomology of a discrete module

For a topological group `G` and a discrete `G`-module `M`, the cohomology `Hⁿ(G, M)` is Mathlib's
`continuousCohomology n (TauCeti.ofDiscreteModule ℤ G M)`, an object built from the abelian group
`M` alone. When `M` is moreover a module over a semiring `R` and the action of `G` commutes with
the scalars, each `r : R` gives a `G`-equivariant endomorphism `r • ·` of `M`, and `r` acts on
`Hⁿ(G, M)` through the coefficient map of that endomorphism. Additivity and functoriality of
coefficient maps (`TauCeti.ContinuousCohomology.continuousCohomologyFunctor_additive`) make this a
module structure, installed here as an instance on the `ℤ`-object itself.

For a discrete `X : TopRep R G` over a commutative ring `R`, the cohomology
`continuousCohomology n X` carries its own `R`-module structure, and
`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv` identifies it additively with the
cohomology of the carrier `X.V` as a discrete `ℤ`-module. That identification is `R`-linear for the
instance of this file (`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntLinearEquiv`), so
the two `R`-module structures are the same structure on the same group.

## Main definitions

* `TauCeti.ofDiscreteModuleSMulMap`: the endomorphism `r • ·` of `ofDiscreteModule ℤ G M`.
* `TauCeti.ContinuousCohomology.smulRingHom`: the action of `R` on `Hⁿ(G, M)` as a ring
  homomorphism into the additive endomorphisms.
* `TauCeti.ContinuousCohomology.instModuleOfDiscreteModule`: the `R`-module structure on
  `continuousCohomology n (ofDiscreteModule ℤ G M)`.
* `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntLinearEquiv`: the `R`-linear form of
  `ofDiscreteModuleRestrictScalarsIntEquiv`.

## Main results

* `TauCeti.ContinuousCohomology.smul_def`: a scalar acts as the coefficient map of `r • ·`.
* `TauCeti.ContinuousCohomology.coeffMap_smul`: the coefficient map of an `R`-linear equivariant
  map of discrete modules is `R`-linear.

## Implementation notes

The instance needs no topology on `R`: the endomorphism `r • ·` of a discrete module is
continuous whatever `R` is. A `TopRep R G` structure on `M`, which would need
`ContinuousSMul R M`, is only used to compare with Mathlib's `R`-linear cohomology.

At `R = ℤ` the instance differs from the `ℤ`-module structure of the `TopModuleCat ℤ` object
`continuousCohomology n (ofDiscreteModule ℤ G M)`: the two agree only propositionally, by
Mathlib's `int_smul_eq_zsmul` or `AddCommGroup.uniqueIntModule`. The instance therefore has low
priority, so that `ℤ`-scalar multiplication keeps resolving to the structure of the object.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

section SMulMap

variable {R : Type u} [Semiring R] {G : Type v} [Monoid G]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G R M]

variable (G M) in
/-- Multiplication by a scalar `r` on a discrete module `M`, as an endomorphism of
`ofDiscreteModule ℤ G M`; it is equivariant because the action of `G` commutes with the scalars. -/
def ofDiscreteModuleSMulMap (r : R) : ofDiscreteModule ℤ G M ⟶ ofDiscreteModule ℤ G M :=
  ofDiscreteModuleMap (DistribSMul.toAddMonoidHom M r).toIntLinearMap
    fun g m ↦ (smul_comm g r m).symm

/-- `ofDiscreteModuleSMulMap G M r` acts on the module as `r • ·`. -/
@[simp]
theorem ofDiscreteModuleSMulMap_hom_apply (r : R) (m : M) :
    (ofDiscreteModuleSMulMap G M r).hom m = r • m :=
  (rfl)

end SMulMap

namespace ContinuousCohomology

open _root_.ContinuousCohomology

universe w

section Module

variable {R : Type w} [Semiring R] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [SMulCommClass G R M]

variable (R G M) in
/-- The action of the scalars on `Hⁿ(G, M)`: the scalar `r` acts by the coefficient map of
`r • ·`, as a ring homomorphism into the additive endomorphisms. -/
noncomputable def smulRingHom (n : ℕ) :
    R →+* AddMonoid.End (continuousCohomology n (ofDiscreteModule ℤ G M)) where
  toFun r := AddMonoidHom.ofClass (coeffMap (ofDiscreteModuleSMulMap G M r) n).hom
  map_one' := by
    have h : ofDiscreteModuleSMulMap G M (1 : R) = 𝟙 _ :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ one_smul R (m : M))
    rw [h, coeffMap_id]
    rfl
  map_mul' r s := by
    have h : ofDiscreteModuleSMulMap G M (r * s) =
        ofDiscreteModuleSMulMap G M s ≫ ofDiscreteModuleSMulMap G M r :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ mul_smul r s (m : M))
    rw [h, coeffMap_comp]
    rfl
  map_zero' := by
    have h : ofDiscreteModuleSMulMap G M (0 : R) = 0 :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ zero_smul R (m : M))
    rw [h, ← continuousCohomologyFunctor_map, Functor.map_zero]
    rfl
  map_add' r s := by
    have h : ofDiscreteModuleSMulMap G M (r + s) =
        ofDiscreteModuleSMulMap G M r + ofDiscreteModuleSMulMap G M s :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ add_smul r s (m : M))
    rw [h, ← continuousCohomologyFunctor_map, Functor.map_add]
    rfl

/-- **`Hⁿ(G, M)` is an `R`-module** when the discrete coefficient module `M` is one and the action
of `G` commutes with the scalars: `r` acts by the coefficient map of `r • ·`. -/
noncomputable instance (priority := 100) instModuleOfDiscreteModule (n : ℕ) :
    Module R (continuousCohomology n (ofDiscreteModule ℤ G M)) :=
  Module.compHom _ (smulRingHom R G M n)

/-- A scalar acts on `Hⁿ(G, M)` as the coefficient map of `r • ·`. -/
theorem smul_def (n : ℕ) (r : R) (x : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    r • x = coeffMap (ofDiscreteModuleSMulMap G M r) n x :=
  (rfl)

/-- **Coefficient maps are `R`-linear.** The coefficient map of a `G`-equivariant `R`-linear map
of discrete modules commutes with the scalars. -/
theorem coeffMap_smul {N : Type v} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [DiscreteTopology N] [DistribMulAction G N] [SMulCommClass G R N] (f : M →ₗ[R] N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (n : ℕ) (r : R)
    (x : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    coeffMap (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap hf) n (r • x) =
      r • coeffMap (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap hf) n x := by
  have h : ofDiscreteModuleSMulMap G M r ≫ ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap hf =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap hf ≫ ofDiscreteModuleSMulMap G N r :=
    TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ f.map_smul r (m : M))
  rw [smul_def, smul_def, ← ConcreteCategory.comp_apply, ← coeffMap_comp, h, coeffMap_comp,
    ConcreteCategory.comp_apply]

end Module

end ContinuousCohomology

namespace ContCohomology

universe w

open TopRep _root_.ContinuousCohomology TauCeti.ContinuousCohomology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type w} [CommRing R] [TopologicalSpace R] {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep.{v} R G) [DiscreteTopology X.V] (n : ℕ)

/-- **The comparison of a discrete representation with its carrier is `R`-linear.** For a
discrete `X : TopRep R G` over a commutative ring, `ofDiscreteModuleRestrictScalarsIntEquiv`
carries the action of `R` on the cohomology of the carrier (`instModuleOfDiscreteModule`) to the
action of `R` on `continuousCohomology n X`. -/
theorem ofDiscreteModuleRestrictScalarsIntEquiv_smul (r : R)
    (a : continuousCohomology n (ofDiscreteModule ℤ G X.V)) :
    ofDiscreteModuleRestrictScalarsIntEquiv X n (r • a) =
      r • ofDiscreteModuleRestrictScalarsIntEquiv X n a := by
  -- Transport along an equality of coefficient objects carries the coefficient map of an
  -- endomorphism to that of the transported endomorphism.
  have hsq : ∀ {B : TopRep ℤ G} (h : ofDiscreteModule ℤ G X.V = B) (f : B ⟶ B),
      ofDiscreteModuleSMulMap G X.V r ≫ eqToHom h = eqToHom h ≫ f →
      eqToHom (congrArg (continuousCohomology n) h)
          (coeffMap (ofDiscreteModuleSMulMap G X.V r) n a) =
        coeffMap f n (eqToHom (congrArg (continuousCohomology n) h) a) := by
    rintro B rfl f hf
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf
    rw [hf]
    rfl
  -- The transported endomorphism of `r • ·` is the underlying additive map of `r • 𝟙 X`.
  have hX := ofDiscreteModule_eq_restrictScalarsInt_obj X
  have hf : ofDiscreteModuleSMulMap G X.V r ≫ eqToHom hX =
      eqToHom hX ≫ restrictScalarsInt.map (r • 𝟙 X) := by
    refine TopRep.hom_ext (DFunLike.ext _ _ fun x ↦ ?_)
    change (eqToHom hX).hom ((ofDiscreteModuleSMulMap G X.V r).hom x) =
      (restrictScalarsInt.map (r • 𝟙 X)).hom ((eqToHom hX).hom x)
    rw [TopRep.eqToHom_hom_apply, TopRep.eqToHom_hom_apply]
    refine (cast_eq _ _).trans
      ((ofDiscreteModuleSMulMap_hom_apply (G := G) (M := X.V) r x).trans ?_)
    refine Eq.symm ((restrictScalarsInt_map_hom_apply (r • 𝟙 X) _).trans ?_)
    refine (DFunLike.congr_fun (TopRep.hom_smul r (𝟙 X)) _).trans
      ((ContIntertwiningMap.smul_apply r (𝟙 X : X ⟶ X).hom _).trans
        (congrArg (r • ·) ((TopRep.id_apply X _).trans (cast_eq _ _))))
  rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply,
    ofDiscreteModuleRestrictScalarsIntEquiv_apply, smul_def, hsq _ _ hf,
    restrictScalarsIntEquiv_apply, restrictScalarsIntEquiv_apply,
    ← ConcreteCategory.comp_apply, coeffMap_comp_restrictScalarsIntIso_hom,
    ConcreteCategory.comp_apply]
  have hc : coeffMap (r • 𝟙 X) n = r • 𝟙 (continuousCohomology n X) :=
    ((continuousCohomologyFunctor R G n).map_smul r (𝟙 X)).trans
      (congrArg (r • ·) (coeffMap_id X n))
  rw [hc]
  rfl

/-- `ofDiscreteModuleRestrictScalarsIntEquiv` as an `R`-linear equivalence, for the action
`instModuleOfDiscreteModule` of `R` on the cohomology of the carrier. -/
noncomputable def ofDiscreteModuleRestrictScalarsIntLinearEquiv :
    continuousCohomology n (ofDiscreteModule ℤ G X.V) ≃ₗ[R] continuousCohomology n X :=
  { ofDiscreteModuleRestrictScalarsIntEquiv X n with
    map_smul' := ofDiscreteModuleRestrictScalarsIntEquiv_smul X n }

/-- `ofDiscreteModuleRestrictScalarsIntLinearEquiv` acts as
`ofDiscreteModuleRestrictScalarsIntEquiv`. -/
@[simp]
theorem ofDiscreteModuleRestrictScalarsIntLinearEquiv_apply
    (a : continuousCohomology n (ofDiscreteModule ℤ G X.V)) :
    ofDiscreteModuleRestrictScalarsIntLinearEquiv X n a =
      ofDiscreteModuleRestrictScalarsIntEquiv X n a :=
  (rfl)

/-- The underlying additive equivalence of `ofDiscreteModuleRestrictScalarsIntLinearEquiv` is
`ofDiscreteModuleRestrictScalarsIntEquiv`. -/
@[simp]
theorem ofDiscreteModuleRestrictScalarsIntLinearEquiv_toAddEquiv :
    (ofDiscreteModuleRestrictScalarsIntLinearEquiv X n).toAddEquiv =
      ofDiscreteModuleRestrictScalarsIntEquiv X n :=
  (rfl)

end ContCohomology

end TauCeti
