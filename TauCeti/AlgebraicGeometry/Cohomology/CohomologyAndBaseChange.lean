/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.RingTheory.Flat.IsBaseChange
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Cohomology and base change in degree zero on a two-affine cover

Let `X` be a scheme over a commutative ring `R`, covered by two affine opens `U` and `V` whose
intersection is affine, and let `M` be a quasi-coherent sheaf on `X`. For every ring map
`R → R'`, with base change `Y = X ×_R R'` and projection `g : Y ⟶ X`, this file proves that if
`H¹(X, M) = 0` and the sections `Γ(M, U ∩ V)` are flat over `R`, then the canonical map

`R' ⊗_R H⁰(X, M) ⟶ H⁰(Y, g^* M)`

is bijective. No flatness of `R → R'` is assumed. If moreover `Γ(M, U)` and `Γ(M, V)` are flat
over `R`, then `H⁰(X, M)` is a flat `R`-module
(`TauCeti.AlgebraicGeometry.flat_cohomology_zero_of_subsingleton_cohomology_one`), and the
vanishing of `H¹` itself persists after every base change
(`TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_pullback`). This is the degree-zero case
of cohomology and base change when the cohomology above it vanishes: for a family `X → Spec R`
with such a cover, coefficients with flat sections and vanishing `H¹` have a flat module of global
sections, whose formation commutes with every base change. Flatness of the sections over an open
`W` is stated for the `R`-module `((sectionsBasePresheafFunctor R).obj M).obj (op W)`, whose
carrier is `Γ(M, W)` with `R` acting through `Scheme.baseRingToStructurePresheaf`.

The proof uses the Mayer–Vietoris sequence of the cover. Since `H¹(X, M) = 0`, it gives a short
exact sequence of `R`-modules

`0 → H⁰(X, M) → Γ(M, U) × Γ(M, V) → Γ(M, U ∩ V) → 0`,

and over `Y` a left exact sequence `0 → H⁰(Y, g^* M) → Γ(g^* M, g⁻¹ U) × Γ(g^* M, g⁻¹ V) →
Γ(g^* M, g⁻¹ (U ∩ V))`. On affine opens, sections of `g^* M` are the base change of sections of
`M` (`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections`), with no flatness hypothesis.
Since `Γ(M, U ∩ V)` is flat, tensoring the first sequence with `R'` keeps it exact, and the five
lemma identifies `R' ⊗_R H⁰(X, M)` with `H⁰(Y, g^* M)`
(`IsBaseChange.of_left_exact_of_surjective`).

## Main results

* `TauCeti.AlgebraicGeometry.bijective_cohomologyBaseChange_zero_of_subsingleton_cohomology_one`:
  the base change map on `H⁰` is bijective along every ring map when `H¹(X, M) = 0` and
  `Γ(M, U ∩ V)` is flat.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.12.11 (cohomology and base change).
* D. Mumford, *Abelian Varieties*, Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

section BaseChange

variable {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

include H in
/-- **Cohomology and base change in degree zero.** Let `X` be a scheme over `R` covered by affine
opens `U` and `V` with affine intersection, let `M` be a quasi-coherent sheaf on `X` whose
sections over `U ∩ V` are a flat `R`-module, and let `Y = X ×_R R'` be the base change along any
ring map `R → R'`. If `H¹(X, M) = 0`, then the canonical map
`R' ⊗_R H⁰(X, M) ⟶ H⁰(Y, g^* M)`, `r' ⊗ x ↦ r' • g^* x`, is bijective.

No flatness of `R → R'` is assumed: flatness of the coefficients over `U ∩ V` and the vanishing of
`H¹` make the Mayer–Vietoris sequence computing `H⁰` stay exact after every base change. -/
theorem bijective_cohomologyBaseChange_zero_of_subsingleton_cohomology_one (M : X.Modules)
    [M.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤)
    [Module.Flat R (((sectionsBasePresheafFunctor R).obj M).obj (op (U ⊓ V)))]
    [Subsingleton (Cohomology M 1)] :
    Function.Bijective (cohomologyBaseChange H M 0) := by
  -- The actions of `R` on sections over `X`, and of `R'` and `R` on sections over `Y`.
  let : ∀ W : X.Opens, Algebra R Γ(X, W) := fun W ↦
    ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : ∀ W : X.Opens, Module R Γ(M, W) := fun W ↦ sectionsBaseModule R M W
  have : ∀ W : X.Opens, IsScalarTower R Γ(X, W) Γ(M, W) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  have : ∀ W : X.Opens, IsScalarTower R Γ(X, ⊤) Γ(M, W) := isScalarTower_sections R M
  have := isScalarTower_cohomology R X M 0
  let : ∀ W' : Y.Opens, Algebra R' Γ(Y, W') := fun W' ↦
    ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
  let : ∀ W' : Y.Opens, Module R' Γ((Scheme.Modules.pullback g).obj M, W') := fun W' ↦
    sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) W'
  have : ∀ W' : Y.Opens, IsScalarTower R' Γ(Y, W') Γ((Scheme.Modules.pullback g).obj M, W') :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  have : ∀ W' : Y.Opens, IsScalarTower R' Γ(Y, ⊤) Γ((Scheme.Modules.pullback g).obj M, W') :=
    isScalarTower_sections R' ((Scheme.Modules.pullback g).obj M)
  have := isScalarTower_cohomology R' Y ((Scheme.Modules.pullback g).obj M) 0
  let : ∀ W' : Y.Opens, Module R Γ((Scheme.Modules.pullback g).obj M, W') := fun _ ↦
    Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, W') :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R (Cohomology ((Scheme.Modules.pullback g).obj M) 0) :=
    Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (Cohomology ((Scheme.Modules.pullback g).obj M) 0) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat R Γ(M, U ⊓ V) :=
    ‹Module.Flat R (((sectionsBasePresheafFunctor R).obj M).obj (op (U ⊓ V)))›
  have hUV' : g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  -- The pullback map on `H⁰`, as an `R`-linear map; its scalar extension is the base change map.
  let h₁ : Cohomology M 0 →ₗ[R] Cohomology ((Scheme.Modules.pullback g).obj M) 0 :=
    ((cohomologyBaseChange H M 0).restrictScalars R).comp (TensorProduct.mk R R' _ 1)
  have h₁_apply (x : Cohomology M 0) : h₁ x = g.cohomologyPullback M 0 x := by
    simp [h₁]
  have hlift : h₁.liftBaseChange R' = cohomologyBaseChange H M 0 := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | tmul r' x => rw [LinearMap.liftBaseChange_tmul, h₁_apply, cohomologyBaseChange_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  -- The rows `0 → H⁰ → Γ(U) × Γ(V) → Γ(U ∩ V)` on `X` and on `Y`, and the vertical pullbacks.
  let σU := g.pullbackSectionsBaseLinear M U H.toCommSq
  let σV := g.pullbackSectionsBaseLinear M V H.toCommSq
  -- The preimage `g ⁻¹ᵁ (U ⊓ V)` is definitionally `g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V`, the overlap on which the
  -- Mayer–Vietoris difference over `Y` lands.
  let σUV : Γ(M, U ⊓ V) →ₗ[R] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) :=
    g.pullbackSectionsBaseLinear M (U ⊓ V) H.toCommSq
  have hσUV : IsBaseChange R' σUV := g.isBaseChange_pullbackSections M (U ⊓ V) H hInter
  have comm₁ : (σU.prodMap σV).comp (((mayerVietorisSectionsRestrictionLinear M U V).comp
        (cohomologyZeroLinearEquiv M).toLinearMap).restrictScalars R) =
      ((((mayerVietorisSectionsRestrictionLinear ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (g ⁻¹ᵁ V)).comp (cohomologyZeroLinearEquiv _).toLinearMap).restrictScalars
          R').restrictScalars R).comp h₁ := by
    refine LinearMap.ext fun x ↦ ?_
    -- Pullback lands in sections over `g ⁻¹ᵁ ⊤`, which is `⊤` by definition.
    have hx := mayerVietorisSectionsRestrictionLinear_apply ((Scheme.Modules.pullback g).obj M)
      (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) (g.pullbackSections M ⊤ (cohomologyZeroEquiv M x))
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      LinearMap.prodMap_apply, cohomologyZeroLinearEquiv_apply,
      mayerVietorisSectionsRestrictionLinear_apply, h₁_apply,
      g.cohomologyZeroEquiv_cohomologyPullback, σU, σV, g.pullbackSectionsBaseLinear_apply]
    refine Eq.trans ?_ hx.symm
    -- Pullback of sections commutes with the restrictions from `⊤` to `U` and to `V`.
    exact Prod.ext (g.pullbackSections_restrict M ⊤ U.leTop _).symm
      (g.pullbackSections_restrict M ⊤ V.leTop _).symm
  have comm₂ : σUV.comp ((mayerVietorisSectionsDifferenceLinear M U V).restrictScalars R) =
      (((mayerVietorisSectionsDifferenceLinear ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (g ⁻¹ᵁ V)).restrictScalars R').restrictScalars R).comp (σU.prodMap σV) :=
    LinearMap.ext fun ⟨s, t⟩ ↦
      (congrArg σUV (mayerVietorisSectionsDifferenceLinear_apply M U V s t)).trans <|
      (g.pullbackSectionsBaseLinear_apply M (U ⊓ V) H.toCommSq _).trans <|
      (g.pullbackSections_mayerVietorisSectionsDifference M U V s t).trans <|
      (congrArg (mayerVietorisSectionsDifference _ _ _)
        (Prod.ext (g.pullbackSectionsBaseLinear_apply M U H.toCommSq s).symm
          (g.pullbackSectionsBaseLinear_apply M V H.toCommSq t).symm)).trans
      (mayerVietorisSectionsDifferenceLinear_apply _ _ _ _ _).symm
  rw [← hlift]
  apply IsBaseChange.liftBaseChange_bijective
  exact IsBaseChange.of_left_exact_of_surjective R' comm₁ comm₂
    (IsBaseChange.prodMap (S := R') σU σV (g.isBaseChange_pullbackSections M U H hU)
      (g.isBaseChange_pullbackSections M V H hV))
    hσUV.liftBaseChange_injective
    (exact_mayerVietorisSectionsRestrictionLinear_comp_cohomologyZeroLinearEquiv M U V hUV)
    (mayerVietorisSectionsRestrictionLinear_comp_cohomologyZeroLinearEquiv_injective M U V hUV)
    (mayerVietorisSectionsDifferenceLinear_surjective M U V hUV)
    (exact_mayerVietorisSectionsRestrictionLinear_comp_cohomologyZeroLinearEquiv _ _ _ hUV')
    (mayerVietorisSectionsRestrictionLinear_comp_cohomologyZeroLinearEquiv_injective _ _ _ hUV')

end BaseChange

end TauCeti.AlgebraicGeometry
