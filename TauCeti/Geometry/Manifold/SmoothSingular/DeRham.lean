/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.AlgebraicTopology.Cohomology.Basic

/-!
# Integration from de Rham forms to smooth singular cochains

Integration over smooth simplices defines a cochain map `deRhamIntegration` from the de Rham
complex to the dual of the smooth singular chain complex. Its induced map on cohomology is
`deRhamCohomology.integration`. Both maps are natural under smooth maps, and the class of a
closed form is sent to the class of its integration cochain.

The target here is **smooth** singular cohomology, not ordinary singular cohomology. No
smoothing theorem or comparison is assumed. The construction works on real `C²` manifolds
with corners, without finite-dimensionality or separation hypotheses. Stokes' theorem for
smooth singular chains supplies the cochain identity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Proposition 18.13.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- Integration of smooth forms, linear in the form. This is the degreewise component of the
integration map to smooth singular cochains. -/
def smoothFormIntegration (k : ℕ) :
    SmoothForm I M ℝ k →ₗ[ℝ]
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
        ℝ (ModuleCat.of ℝ ℝ)).X k where
  toFun φ := integrationCochain φ.1
  map_add' φ ψ := integrationCochain_add (φ.isSmoothForm.of_le (by simp))
    (ψ.isSmoothForm.of_le (by simp))
  map_smul' a φ := integrationCochain_smul a φ.1

/-- Integration of a smooth form is its integration cochain. -/
@[simp]
theorem smoothFormIntegration_apply (k : ℕ) (φ : SmoothForm I M ℝ k) :
    smoothFormIntegration I M k φ = integrationCochain φ.1 := (rfl)

/-- Integration of forms as a map from the de Rham complex to the dual of smooth singular
chains. Its commutation with differentials is Stokes' theorem. -/
def deRhamIntegration : deRhamComplex I M ⟶
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
      ℝ (ModuleCat.of ℝ ℝ) :=
  CochainComplex.ofHom
    (fun k ↦ (deRhamComplexXIso I k).hom ≫ ModuleCat.ofHom (smoothFormIntegration I M k))
    fun k ↦ by
      apply ModuleCat.hom_ext
      ext φ
      -- The objects of the Hom complex are morphism modules; expose their precomposition
      -- differential and the degreewise linear map to compare them with Stokes.
      change _ ≫ integrationCochain (((deRhamComplexXIso I k).hom φ).1) =
        smoothFormIntegration I M (k + 1)
          ((deRhamComplexXIso I (k + 1)).hom ((deRhamComplex I M).d k (k + 1) φ))
      rw [deRhamComplex_d_apply, Iso.inv_hom_id_apply, smoothFormIntegration_apply,
        mextDerivₗ_apply]
      exact d_comp_integrationCochain
        (((deRhamComplexXIso I k).hom φ).isSmoothForm.of_le (by simp))

/-- The degreewise integration map, evaluated on a form through the canonical identification
of the de Rham complex, is its integration cochain. -/
@[simp]
theorem deRhamIntegration_f_inv_apply (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (deRhamIntegration I M).f k ((deRhamComplexXIso I k).inv φ) =
      integrationCochain φ.1 := by
  -- CochainComplex.ofHom uses the supplied family as its components definitionally;
  -- expose that component and its composite of module morphisms before cancelling the iso.
  change smoothFormIntegration I M k
    ((deRhamComplexXIso I k).hom ((deRhamComplexXIso I k).inv φ)) = _
  rw [Iso.inv_hom_id_apply, smoothFormIntegration_apply]

/-- The constant function `1`, viewed as a zero-form, integrates to `1` on every smooth
zero-simplex. This fixes the normalization of the integration map in degree zero. -/
@[simp]
theorem deRhamIntegration_f_inv_apply_one (σ : SmoothSimplex I M 0) :
    ((deRhamIntegration I M).f 0 ((deRhamComplexXIso I 0).inv
      (SmoothForm.ofFunction (ContMDiffMap.const (I := I) (I' := 𝓘(ℝ, ℝ)) 1)))).hom
          (((smoothSingularSubcomplex I M : SSet).ιChainComplex
            (R := ModuleCat.of ℝ ℝ) σ).hom 1) = 1 := by
  rw [deRhamIntegration_f_inv_apply, integrationCochain_ιChainComplex,
    SmoothForm.coe_ofFunction, SmoothSimplex.integral_ofFunction]
  simp [ContMDiffMap.const]

variable {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- Integration commutes with pullback along a smooth map, on the level of complexes. -/
@[reassoc]
theorem deRhamIntegration_naturality {f : M → N} (hf : ContMDiff I J ∞ f) :
    deRhamComplex.map f hf ≫ deRhamIntegration I M =
      deRhamIntegration J N ≫ SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf) := by
  ext k : 2
  refine LinearMap.ext fun φ ↦ ?_
  obtain ⟨ψ, rfl⟩ := (deRhamComplexXIso J k).toLinearEquiv.symm.surjective φ
  -- Normalize the concrete morphism coercions before using the evaluation API. The dual
  -- complex stores cochains as morphisms, rather than as their underlying linear maps.
  change (deRhamIntegration I M).f k
      ((deRhamComplex.map f hf).f k ((deRhamComplexXIso J k).inv ψ)) =
    (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)).f k
      ((deRhamIntegration J N).f k ((deRhamComplexXIso J k).inv ψ))
  rw [deRhamComplex.map_f_inv_apply, deRhamIntegration_f_inv_apply,
    deRhamIntegration_f_inv_apply]
  exact (congrArg integrationCochain (SmoothForm.coe_mpullback f hf ψ)).trans
    ((integrationCochain_naturality hf ψ.1).symm.trans
      (SSet.cochainComplexMap_f_apply _ k _).symm)

/-- The integration cochain of a closed smooth form, bundled as a cocycle. -/
def integrationCocycle (k : ℕ) (φ : closedForms I M k) :
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
      ℝ (ModuleCat.of ℝ ℝ)).cycles k :=
  HomologicalComplex.moduleCatCyclesMk _ (integrationCochain φ.1.1) (k + 1)
    (CochainComplex.next ℕ k) (by
      exact (ChainComplex.linearYonedaObj_d_apply k (k + 1) _).trans
        (d_comp_integrationCochain_eq_zero
          (φ.1.isSmoothForm.of_le (by simp)) ((mem_closedForms I φ.1).mp φ.2)))

/-- The cochain underlying the integration cocycle is the integration cochain. -/
@[simp]
theorem iCycles_integrationCocycle (k : ℕ) (φ : closedForms I M k) :
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
      ℝ (ModuleCat.of ℝ ℝ)).iCycles k (integrationCocycle I M k φ) =
        integrationCochain φ.1.1 := by
  exact HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _

namespace deRhamCohomology

/-- The homomorphism from de Rham cohomology to smooth singular cohomology induced by integration.
This does not identify smooth singular cohomology with ordinary singular cohomology. -/
def integration (k : ℕ) : deRhamCohomology I M k →ₗ[ℝ]
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
      ℝ (ModuleCat.of ℝ ℝ)).homology k :=
  (HomologicalComplex.homologyMap (deRhamIntegration I M) k).hom

/-- The map on homology of the integration cochain map is the integration homomorphism. -/
theorem homologyMap_deRhamIntegration (k : ℕ) :
    HomologicalComplex.homologyMap (deRhamIntegration I M) k =
      ModuleCat.ofHom (integration I M k) := (rfl)

/-- The image of a closed form is the cohomology class of its integration cochain. -/
@[simp]
theorem integration_mk (k : ℕ) (φ : closedForms I M k) :
    integration I M k (mk I k φ) =
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
        ℝ (ModuleCat.of ℝ ℝ)).homologyπ k
          (integrationCocycle I M k φ) := by
  rw [integration, mk_eq_moduleCatHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  simp only [LinearMap.comp_apply, integrationCocycle]
  congr 2
  exact deRhamIntegration_f_inv_apply I M k φ.1

/-- The integration homomorphism is natural under smooth pullback. -/
theorem integration_naturality {f : M → N} (hf : ContMDiff I J ∞ f) (k : ℕ)
    (c : deRhamCohomology J N k) :
    integration I M k (map f hf k c) =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)) k
          (integration J N k c) := by
  have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g k)
    (deRhamIntegration_naturality I M hf)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    deRhamComplex.homologyMap_map] at h
  exact ConcreteCategory.congr_hom h c

end deRhamCohomology

end TauCeti
