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
this identification carries one `R`-module structure to the other.

## Main definitions

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
## References

The design, in which the cohomology is defined once for abelian groups and the `R`-module
structure is supplied by instances where it exists, follows David Loeffler's advice in
[#Riemann-Hypothesis > Library design discrepancies between RH/Mathlib/TauCeti](https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780293).
It builds on the existing Tau Ceti files
`TauCeti.RepresentationTheory.Homological.ContCohomology.Additive` (additivity of coefficient maps)
and `TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars` (the additive
identification `ofDiscreteModuleRestrictScalarsIntEquiv`).
-/

public section

open CategoryTheory

namespace TauCeti

universe v

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
  -- Each field reduces to a statement about a morphism of `TopModuleCat`, then closes pointwise
  -- with `AddMonoidHom.ext` and the matching evaluation lemma (`id_apply`, `comp_apply`,
  -- `hom_zero_apply`, `hom_add`). These are applied with `exact` rather than `rw`/`simp`: the
  -- goal mixes the carrier of `continuousCohomology n _` with that of its `toModuleCat`, so a
  -- rewrite produces a goal that is not type-correct at reducible transparency.
  map_one' := by
    have h : ofDiscreteModuleSMulMap G M (1 : R) = 𝟙 _ :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦
        (ofDiscreteModuleSMulMap_hom_apply (G := G) (M := M) 1 m).trans (one_smul R (m : M)))
    rw [h, coeffMap_id]
    exact AddMonoidHom.ext fun x ↦ ConcreteCategory.id_apply x
  map_mul' r s := by
    have h : ofDiscreteModuleSMulMap G M (r * s) =
        ofDiscreteModuleSMulMap G M s ≫ ofDiscreteModuleSMulMap G M r :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ by
        have hA (t : R) (x : M) := ofDiscreteModuleSMulMap_hom_apply (G := G) (M := M) t x
        exact (hA (r * s) m).trans ((mul_smul r s (show M from m)).trans
          ((congrArg (fun x : M ↦ r • x) (hA s m).symm).trans (hA r _).symm)))
    rw [h, coeffMap_comp]
    exact AddMonoidHom.ext fun x ↦ ConcreteCategory.comp_apply
      (coeffMap (ofDiscreteModuleSMulMap G M s) n) (coeffMap (ofDiscreteModuleSMulMap G M r) n) x
  map_zero' := by
    have h : ofDiscreteModuleSMulMap G M (0 : R) = 0 :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦
        (ofDiscreteModuleSMulMap_hom_apply (G := G) (M := M) 0 m).trans (zero_smul R (m : M)))
    rw [h, ← continuousCohomologyFunctor_map, Functor.map_zero]
    exact AddMonoidHom.ext fun x ↦ TopModuleCat.hom_zero_apply (m := x)
  map_add' r s := by
    have h : ofDiscreteModuleSMulMap G M (r + s) =
        ofDiscreteModuleSMulMap G M r + ofDiscreteModuleSMulMap G M s :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ by
        have hA (t : R) (x : M) := ofDiscreteModuleSMulMap_hom_apply (G := G) (M := M) t x
        exact (hA (r + s) m).trans ((add_smul r s (show M from m)).trans
          (congrArg₂ (· + ·) (hA r m).symm (hA s m).symm)))
    rw [h, ← continuousCohomologyFunctor_map, Functor.map_add]
    exact AddMonoidHom.ext fun x ↦ (DFunLike.congr_fun (TopModuleCat.hom_add
      (φ₁ := (continuousCohomologyFunctor ℤ G n).map (ofDiscreteModuleSMulMap G M r))
      (φ₂ := (continuousCohomologyFunctor ℤ G n).map (ofDiscreteModuleSMulMap G M s))) x).trans
      (add_apply _ _ x)

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
    TopRep.hom_ext (DFunLike.ext _ _ fun m ↦
      (congrArg _ (ofDiscreteModuleSMulMap_hom_apply r m)).trans
        ((f.map_smul r (m : M)).trans (ofDiscreteModuleSMulMap_hom_apply (G := G) r (f m)).symm))
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
    simp only [eqToHom_refl, ConcreteCategory.id_apply]
  -- The transported endomorphism of `r • ·` is the underlying additive map of `r • 𝟙 X`.
  have hX := ofDiscreteModule_eq_restrictScalarsInt_obj X
  have hf : ofDiscreteModuleSMulMap G X.V r ≫ eqToHom hX =
      eqToHom hX ≫ restrictScalarsInt.map (r • 𝟙 X) := by
    refine TopRep.hom_ext (DFunLike.ext _ _ fun x ↦ ?_)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopRep.eqToHom_hom_apply,
      TopRep.eqToHom_hom_apply]
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
  -- the two sides live in the carriers of `restrictScalarsInt.obj (continuousCohomology n X)` and
  -- `continuousCohomology n X`, which agree only up to unfolding, so `rw` cannot see through
  exact (TopModuleCat.restrictScalarsInt_map_apply (r • 𝟙 (continuousCohomology n X)) _).trans
    ((DFunLike.congr_fun (TopModuleCat.hom_smul r (𝟙 _)) _).trans
      ((smul_apply (TopModuleCat.Hom.hom (𝟙 (continuousCohomology n X))) r _).trans
        (congrArg (r • ·) (ConcreteCategory.id_apply _))))

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
