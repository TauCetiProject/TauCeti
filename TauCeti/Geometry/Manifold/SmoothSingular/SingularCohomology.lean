/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.Geometry.Manifold.ContMDiff.Contraction
import TauCeti.Geometry.Manifold.Topology

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

The de Rham theorem asserts that `deRhamHom I M k` is bijective in every degree. This file proves
the cases on which a Mayer–Vietoris induction over open sets starts.

* **Degree zero.** A degree-zero de Rham class is a locally constant function
  (`TauCeti.deRhamCohomologyZeroEquiv`), and a degree-zero singular class is determined by its
  values at points (`TauCeti.singularCohomologyZeroEval`). The de Rham homomorphism preserves these
  values (`TauCeti.singularCohomologyZeroEval_deRhamHom`), because the integral of a function over
  a `0`-simplex is its value at the vertex. Since a manifold is locally path-connected, the
  functions constant on path components are the locally constant ones, so `deRhamHom I M 0` is
  bijective on every manifold (`TauCeti.bijective_deRhamHom_zero`).
* **The empty manifold.** Both sides vanish in every degree
  (`TauCeti.bijective_deRhamHom_of_isEmpty`).
* **Smoothly contractible manifolds.** If a smooth homotopy contracts `M` to a point, both sides
  vanish in positive degrees (`TauCeti.subsingleton_deRhamCohomology_of_contraction` and
  `TauCeti.isZero_singularCohomology_of_contractibleSpace`), so `deRhamHom I M k` is bijective in
  every degree (`TauCeti.bijective_deRhamHom_of_contraction`). This applies to every nonempty
  open subset of a chart domain whose image in the chart is star-convex
  (`TauCeti.bijective_deRhamHom_of_starConvex_image_extChartAt`), boundary and corners included.

## Main definitions

* `TauCeti.deRhamHom I M k`: the de Rham homomorphism `H^k_dR(M) →ₗ[ℝ] Hᵏ(M; ℝ)`.

## Main results

* `TauCeti.homologyMap_cochainComplexMap_deRhamHom`: restricted to smooth simplices, the de Rham
  homomorphism is integration.
* `TauCeti.deRhamHom_mk`: the image of the class of a closed form is the singular class
  corresponding to its integration cocycle.
* `TauCeti.deRhamHom_map`: naturality under smooth maps, `deRhamHom (f^* c) = f^* (deRhamHom c)`.
* `TauCeti.singularKronecker_deRhamHom_mk_apply`: the class of a closed form evaluates on the class
  of a smooth cycle to the integral of the form over the cycle.
* `TauCeti.singularCohomologyZeroEval_deRhamHom`: in degree zero, the de Rham homomorphism
  preserves values at points.
* `TauCeti.bijective_deRhamHom_zero`: the de Rham theorem in degree zero.
* `TauCeti.bijective_deRhamHom_of_isEmpty`, `TauCeti.bijective_deRhamHom_of_contraction`,
  `TauCeti.bijective_deRhamHom_of_starConvex_image_extChartAt`: the de Rham theorem on the empty
  manifold, on smoothly contractible manifolds and on star-convex chart domains.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (Theorem 18.7, Proposition 18.13 and the proof of Theorem 18.14).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Set
open scoped Manifold ContDiff

namespace TauCeti

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

/-- **The de Rham homomorphism preserves values in degree zero**: the singular class
`deRhamHom c` of a degree-zero de Rham class `c` takes at each point `x` the value at `x` of the
locally constant function representing `c`. -/
@[simp]
theorem singularCohomologyZeroEval_deRhamHom (c : deRhamCohomology I M 0) (x : M) :
    singularCohomologyZeroEval (X := TopCat.of M) x (deRhamHom I M 0 c) =
      deRhamCohomologyZeroEquiv I M c x := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I 0 c
  -- The value at `x` is the Kronecker pairing with the class of the smooth `0`-simplex at `x`.
  let σ := (SmoothSimplex.equiv₀ I M).symm x
  have hσ : TopCat.toSSetObj₀Equiv.symm x = (smoothSingularSubcomplex I M).ι.app _ σ :=
    (SmoothSimplex.coe_equiv₀_symm x).symm
  let z := ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).liftCycles
    ((smoothSingularSubcomplex I M : SSet).ιChainComplex σ) 0 (by simp) (by simp)
  have hx : (singularHomology₀Section (𝟙_ (ModuleCat ℝ)) (X := TopCat.of M) x).hom 1 =
      (smoothSingularHomologyIso I M (ModuleCat.of ℝ ℝ) 0).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).homologyπ 0).hom
          (z.hom 1)) := by
    rw [smoothSingularHomologyIso_hom, singularHomology₀Section_def, hσ,
      ← SSet.ιHomology₀_homologyMap, SSet.ιHomology₀_def]
    -- Both sides apply the same composite of morphisms; singular homology is by definition the
    -- homology of the singular simplicial set, and `𝟙_ (ModuleCat ℝ)` is `ModuleCat.of ℝ ℝ`.
    rfl
  have hz : (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).iCycles 0).hom
      (z.hom 1) = ((smoothSingularSubcomplex I M : SSet).ιChainComplex
        (R := ModuleCat.of ℝ ℝ) σ).hom 1 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.liftCycles_i]
  rw [singularCohomologyZeroEval_apply, ModuleCat.hom_comp, LinearMap.comp_apply, hx,
    singularKronecker_deRhamHom_mk_apply, hz, integrationCochain_ιChainComplex, one_smul,
    deRhamCohomologyZeroEquiv_mk, RoughForm.eq_ofFunction φ.val.val,
    SmoothSimplex.integral_ofFunction, SmoothSimplex.toContinuousMap_equiv₀_symm_apply,
    RoughForm.ofFunction_apply]

/-- **The de Rham theorem in degree zero**: on every Hausdorff `σ`-compact smooth manifold
modelled on a finite-dimensional real model with corners, the de Rham homomorphism
`H⁰_dR(M) → H⁰(M; ℝ)` is bijective. Both sides are the real functions on `M` that are constant on
path components. -/
theorem bijective_deRhamHom_zero : Function.Bijective (deRhamHom I M 0) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun u ↦ ?_⟩
  · refine (deRhamCohomologyZeroEquiv I M).map_eq_zero_iff.1 (LocallyConstant.ext fun x ↦ ?_)
    rw [← singularCohomologyZeroEval_deRhamHom, hc, map_zero, LocallyConstant.zero_apply]
  · -- The values of `u` are constant on path components, which are open in a manifold.
    have := I.locallyPathConnectedSpace_of_chartedSpace M
    have hu : IsLocallyConstant fun x ↦ singularCohomologyZeroEval (X := TopCat.of M) x u :=
      (IsLocallyConstant.iff_exists_open _).2 fun x ↦
        ⟨pathComponent x, IsOpen.pathComponent x, mem_pathComponent_self x,
          fun y hy ↦ (singularCohomologyZeroEval_eq_of_joined (mem_pathComponent_iff.1 hy) u).symm⟩
    refine ⟨(deRhamCohomologyZeroEquiv I M).symm ⟨_, hu⟩,
      singularCohomologyZero_ext fun x ↦ ?_⟩
    rw [singularCohomologyZeroEval_deRhamHom, LinearEquiv.apply_symm_apply,
      LocallyConstant.coe_mk]

/-- **The de Rham theorem on the empty manifold**: both de Rham and singular cohomology of the
empty manifold vanish, so the de Rham homomorphism is bijective in every degree. -/
theorem bijective_deRhamHom_of_isEmpty [IsEmpty M] (k : ℕ) :
    Function.Bijective (deRhamHom I M k) := by
  have := (deRhamCohomology.mk_surjective I (M := M) k).subsingleton
  have := ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_isEmpty
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (TopCat.of M) k)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The de Rham theorem on a smoothly contractible manifold**: if `F : M × [0, 1] → M` is a
smooth homotopy from the identity of `M` to the constant map at `c`, then the de Rham
homomorphism of `M` is bijective in every degree. In positive degrees both sides vanish; in
degree zero this is `TauCeti.bijective_deRhamHom_zero`. -/
theorem bijective_deRhamHom_of_contraction {F : M × Icc (0 : ℝ) 1 → M}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I ∞ F) {c : M} (hF₀ : ∀ x, F (x, 0) = x)
    (hF₁ : ∀ x, F (x, 1) = c) (k : ℕ) : Function.Bijective (deRhamHom I M k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact bijective_deRhamHom_zero I M
  have := subsingleton_deRhamCohomology_of_contraction hF hF₀ hF₁ hk
  -- `F` is a homotopy from the identity to a constant map, so `M` is contractible.
  have : ContractibleSpace (TopCat.of M) := (contractible_iff_id_nullhomotopic _).2
    ⟨c, ⟨{ toFun := fun p ↦ F (p.2, p.1)
           continuous_toFun := hF.continuous.comp continuous_swap
           map_zero_left := hF₀
           map_one_left := hF₁ }⟩⟩
  have := ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_contractibleSpace
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (TopCat.of M) hk)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

omit [SigmaCompactSpace M] in
/-- **The de Rham theorem on star-convex chart domains**: if an open subset `U` of `M` lies in the
domain of the extended chart at `x` and its image in the chart is star-convex about the image of a
point `c ∈ U`, then the de Rham homomorphism of `U` is bijective in every degree. The manifold may
have boundary or corners. -/
theorem bijective_deRhamHom_of_starConvex_image_extChartAt {x : M} {U : TopologicalSpace.Opens M}
    [SigmaCompactSpace U] (hU : (U : Set M) ⊆ (extChartAt I x).source) (c : U)
    (hc : StarConvex ℝ (extChartAt I x c) (extChartAt I x '' (U : Set M))) (k : ℕ) :
    Function.Bijective (deRhamHom I U k) := by
  obtain ⟨F, hF, hF₀, hF₁⟩ := exists_contMDiff_contraction_of_starConvex_image_extChartAt
    (n := ⊤) hU c hc
  exact bijective_deRhamHom_of_contraction I U (F := fun p ↦ F (p.2.val, p.1))
    (hF.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).prodMk contMDiff_fst))
    (fun z ↦ hF₀ z) (fun z ↦ hF₁ z) k

end TauCeti
