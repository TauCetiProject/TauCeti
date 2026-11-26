/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# The de Rham homomorphism into singular cohomology

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners. Integration of closed forms over smooth singular simplices gives a map
`TauCeti.deRhamCohomology.integration` from de Rham cohomology to the cohomology of the smooth
singular cochains `Hom(C_*^∞(M; ℝ), ℝ)`. By the smoothing theorem, restriction of singular
cochains to smooth simplices induces an isomorphism `TauCeti.smoothSingularCohomologyIso` from
singular cohomology `Hᵏ(M; ℝ)` onto that smooth singular cohomology. Composing integration with its
inverse gives the **de Rham homomorphism**

`TauCeti.deRhamHom I M k : H^k_dR(M) →ₗ[ℝ] Hᵏ(M; ℝ)`

into ordinary singular cohomology with real coefficients. It is characterized by its restriction
to smooth simplices, which is integration (`TauCeti.homologyMap_cochainComplexMap_deRhamHom`), and
it is natural under pullback along smooth maps (`TauCeti.deRhamHom_map`).

Its values pair with singular homology through the Kronecker map
`TopCat.singularKronecker`: on the class of a smooth singular cycle `z`, the class `deRhamHom [φ]`
of a closed form `φ` evaluates to the integral `∫_z φ`
(`TauCeti.singularKronecker_deRhamHom_mk_apply`). Every class of `Hₖ(M; ℝ)` has such a
representative (the smoothing theorem again), so this computes the pairing of a de Rham class with
every real singular homology class. It is the comparison through which periods of closed forms on
singular homology classes, such as cross products and fundamental classes, are computed.

With coefficients in the divisible, hence injective, group `ℝ/ℤ`, the smoothing isomorphism
followed by the Kronecker pairing (`TauCeti.ChainComplex.kroneckerEquiv`) gives the universal
coefficient equivalence `Hᵏ(M; ℝ/ℤ) ≃ Hom(H_k(M; ℤ), ℝ/ℤ)` with smooth singular homology
(`TauCeti.singularCohomologyUnitAddCircleAddEquiv`).

## Main definitions

* `TauCeti.deRhamHom I M k`: the de Rham homomorphism `H^k_dR(M) →ₗ[ℝ] Hᵏ(M; ℝ)`.
* `TauCeti.singularCohomologyUnitAddCircleAddEquiv I M k`: the universal coefficient equivalence
  `Hᵏ(M; ℝ/ℤ) ≃+ Hom(H_k(M; ℤ), ℝ/ℤ)`.

## Main results

* `TauCeti.homologyMap_cochainComplexMap_deRhamHom`: restricted to smooth simplices, the de Rham
  homomorphism is integration.
* `TauCeti.deRhamHom_mk`: the image of the class of a closed form is the singular class
  corresponding to its integration cocycle.
* `TauCeti.deRhamHom_map`: naturality under smooth maps, `deRhamHom (f^* c) = f^* (deRhamHom c)`.
* `TauCeti.singularKronecker_deRhamHom_mk_apply`: the class of a closed form evaluates on the class
  of a smooth cycle to the integral of the form over the cycle.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (Theorem 18.7 and Proposition 18.13).
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

section UnitAddCircle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] (k : ℕ)

/-- The **universal coefficient theorem for `ℝ/ℤ`-coefficients** on a smooth manifold:
`Hᵏ(M; ℝ/ℤ) ≃ Hom(H_k(M; ℤ), ℝ/ℤ)`, with homology the smooth singular homology. It is the smoothing
isomorphism from singular cohomology to the cohomology of the smooth singular cochains, followed by
the Kronecker pairing, which is an equivalence because `ℝ/ℤ` is divisible, hence injective. -/
def singularCohomologyUnitAddCircleAddEquiv :
    (TopCat.of M).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle) k ≃+
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k →+
        UnitAddCircle) :=
  -- `ℝ/ℤ` is divisible, hence an injective `ℤ`-module.
  haveI := (Module.Baer.of_divisible UnitAddCircle).injective
  haveI := Module.injective_object_of_injective_module ℤ UnitAddCircle
  (smoothSingularCohomologyIso I M (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle)
      k).toLinearEquiv.toAddEquiv.trans <|
    (ChainComplex.kroneckerEquiv ℤ _ (ModuleCat.of ℤ UnitAddCircle) k).toAddEquiv.trans <|
      -- Mathlib's `addMonoidHomLequivInt` does not apply here: the homology carries the
      -- `ℤ`-module structure of `ModuleCat`, which is not definitionally the canonical one
      -- `AddCommGroup.toIntModule` that `addMonoidHomLequivInt` uses.
      ModuleCat.homAddEquiv.trans
        { toFun f := f.toAddMonoidHom
          invFun f :=
            { toFun := f
              map_add' := map_add f
              map_smul' n x := by
                simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul f ℤ ℤ n x }
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl }

/-- The universal coefficient equivalence evaluates a singular cohomology class on a smooth
singular homology class by the Kronecker pairing of its smooth singular representative. -/
theorem singularCohomologyUnitAddCircleAddEquiv_apply
    (x : (TopCat.of M).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle) k)
    (y : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k) :
    singularCohomologyUnitAddCircleAddEquiv I M k x y =
      (ChainComplex.kronecker ℤ _ (ModuleCat.of ℤ UnitAddCircle) k
        ((smoothSingularCohomologyIso I M (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle)
          k).hom x)).hom y := by
  have := (Module.Baer.of_divisible UnitAddCircle).injective
  have := Module.injective_object_of_injective_module ℤ UnitAddCircle
  simp only [singularCohomologyUnitAddCircleAddEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
  rw [ChainComplex.kroneckerEquiv_apply, Iso.toLinearEquiv_apply]
  -- What remains is the passage from a morphism of `ℤ`-modules to its underlying homomorphism,
  -- the hand-built last step of the equivalence, which holds by definition.
  rfl

end UnitAddCircle

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **The de Rham homomorphism** `H^k_dR(M) →ₗ[ℝ] Hᵏ(M; ℝ)` of a Hausdorff `σ`-compact smooth
manifold modelled on a finite-dimensional real model with corners: integration of closed forms over
smooth singular simplices, followed by the inverse of the smoothing isomorphism
`TauCeti.smoothSingularCohomologyIso` from singular cohomology to smooth singular cohomology. -/
def deRhamHom (k : ℕ) : deRhamCohomology I M k →ₗ[ℝ]
    (TopCat.of M).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) k :=
  (smoothSingularCohomologyIso I M (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) k).inv.hom ∘ₗ
    deRhamCohomology.integration I M k

/-- The de Rham homomorphism is integration followed by the inverse of the smoothing isomorphism. -/
theorem deRhamHom_apply (k : ℕ) (c : deRhamCohomology I M k) :
    deRhamHom I M k c =
      (smoothSingularCohomologyIso I M (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) k).inv
        (deRhamCohomology.integration I M k c) := (rfl)

/-- Restricted to smooth singular simplices, the de Rham homomorphism is integration. This
determines it, since this restriction is the isomorphism `TauCeti.smoothSingularCohomologyIso`. -/
@[simp]
theorem homologyMap_cochainComplexMap_deRhamHom (k : ℕ) (c : deRhamCohomology I M k) :
    HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
        (M := ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I M).ι) k (deRhamHom I M k c) =
      deRhamCohomology.integration I M k c := by
  rw [← smoothSingularCohomologyIso_hom, deRhamHom_apply, Iso.inv_hom_id_apply]

/-- The de Rham homomorphism sends the class of a closed form to the singular class whose
restriction to smooth simplices is the class of its integration cocycle. -/
@[simp]
theorem deRhamHom_mk (k : ℕ) (φ : closedForms I M k) :
    deRhamHom I M k (deRhamCohomology.mk I k φ) =
      (smoothSingularCohomologyIso I M (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) k).inv
        ((((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
          ℝ (ModuleCat.of ℝ ℝ)).homologyπ k (integrationCocycle I M k φ)) := by
  rw [deRhamHom_apply, deRhamCohomology.integration_mk]

variable {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N]
  [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]

variable {I M} in
/-- **Naturality of the de Rham homomorphism**: for a smooth map `f : M → N`, the de Rham
homomorphism of `M` applied to the pullback `f^* c` of a de Rham class is the singular pullback of
the de Rham homomorphism of `N` applied to `c`. -/
theorem deRhamHom_map {f : M → N} (hf : ContMDiff I J ∞ f) (k : ℕ)
    (c : deRhamCohomology J N k) :
    deRhamHom I M k (deRhamCohomology.map f hf k c) =
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) k (deRhamHom J N k c) := by
  rw [deRhamHom_apply, deRhamCohomology.integration_naturality, deRhamHom_apply]
  exact ConcreteCategory.congr_hom
    (smoothSingularCohomologyIso_inv_naturality (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) hf k)
    (deRhamCohomology.integration J N k c)

/-- **Periods of the de Rham homomorphism**: the singular class `deRhamHom [φ]` of a closed
form `φ` evaluates, under the Kronecker map, on the singular homology class of a smooth singular
cycle `z` to the integral `∫_z φ`. -/
theorem singularKronecker_deRhamHom_mk_apply (k : ℕ) (φ : closedForms I M k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).cycles k) :
    ((TopCat.of M).singularKronecker ℝ k (deRhamHom I M k (deRhamCohomology.mk I k φ))).hom
        ((smoothSingularHomologyIso I M (ModuleCat.of ℝ ℝ) k).hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex
            (ModuleCat.of ℝ ℝ)).homologyπ k z))) =
      (integrationCochain φ.val.val).hom
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).iCycles k z) := by
  -- Evaluate the naturality of the Kronecker map along the inclusion of smooth chains on the
  -- class of `z`.
  have h := ConcreteCategory.congr_hom (ChainComplex.kronecker_naturality
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℝ ℝ)) k
    (deRhamHom I M k (deRhamCohomology.mk I k φ)))
    ((((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).homologyπ k z))
  rw [ConcreteCategory.comp_apply] at h
  rw [TopCat.singularKronecker_def, smoothSingularHomologyIso_hom]
  -- The goal applies `ModuleCat.Hom.hom` where `h` applies `ConcreteCategory.hom`; the two
  -- coercions of a morphism of modules agree by definition.
  refine h.symm.trans ?_
  -- Restricted to smooth chains, the class is that of the integration cocycle.
  have hc := homologyMap_cochainComplexMap_deRhamHom I M k (deRhamCohomology.mk I k φ)
  rw [deRhamCohomology.integration_mk] at hc
  rw [hc, ChainComplex.kronecker_homologyπ_homologyπ, iCycles_integrationCocycle]

end TauCeti
