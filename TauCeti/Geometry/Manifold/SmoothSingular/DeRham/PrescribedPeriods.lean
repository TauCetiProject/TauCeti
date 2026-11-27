/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Equiv
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
import Mathlib.Algebra.Category.Grp.Injective
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.IntegralComparison

/-!
# Closed forms with prescribed periods

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners. A closed `p`-form `φ` has periods `⟨[φ], c⟩` on the integral singular homology
classes `c ∈ H_p(M; ℤ)` (`TauCeti.closedFormHomologyPeriod`). This file proves de Rham's theorem in
the form of prescribed periods: **every homomorphism `H_p(M; ℤ) → ℝ` is the period map of a closed
`p`-form** (`TauCeti.exists_closedFormHomologyPeriod_eq`), in every degree. In degree one this is
`TauCeti.deRhamCohomology.homologyPeriod_surjective`, proved there through the universal cover.

**The proof.** By the smoothing theorem it suffices to prescribe the periods on the integral
smooth singular homology `H_p^∞(M; ℤ)` (`TauCeti.exists_smoothHomologyPeriodHom_eq`). Since `ℝ`
is divisible, hence an injective abelian group, a homomorphism `f : H_p^∞(M; ℤ) → ℝ` extends from
the cycles to an integral cochain `a` vanishing on boundaries. The real cochain `b` with the same
values on smooth simplices is a cocycle of `Hom(C_*^∞(M; ℝ), ℝ)`
(`TauCeti.exists_cocycle_iCycles_comp_eq`). By the de Rham theorem integration
is onto the cohomology of these cochains (`TauCeti.deRhamCohomology.bijective_integration`), so
the integration cochain of some closed form `φ` differs from `b` by a coboundary `d η`. Read back
on integral chains, the integration cochain of `φ` is `a` plus the coboundary of the integral
cochain with the values of `η`, which vanishes on cycles, so the periods of `φ` are `f`.

**Spanning periods.** Consequently the period maps of closed `p`-forms span the real vector space
of homomorphisms `H_p(M; ℤ) → ℝ` (`TauCeti.span_range_closedFormHomologyPeriod`). When `H_p(M; ℤ)`
is finitely generated, as for a compact manifold, this is the hypothesis under which finitely many
of these periods have injective real extension `ℝ ⊗ H_p(M; ℤ) → ℝⁿ`
(`TauCeti.exists_finset_liftBaseChange_pi_injective`), and under which bounds on all periods leave
only finitely many integral classes, torsion included (`TauCeti.finite_setOf_forall_abs_apply_le`).
This is the comparison behind Gromov's finiteness of the classes of pseudoholomorphic curves of
bounded area.

## Main results

* `TauCeti.exists_smoothHomologyPeriodHom_eq`: every homomorphism `H_p^∞(M; ℤ) → ℝ` is the period
  map of a closed form on integral smooth singular homology.
* `TauCeti.exists_closedFormHomologyPeriod_eq`: every homomorphism `H_p(M; ℤ) → ℝ` is the period
  map of a closed form.
* `TauCeti.span_range_closedFormHomologyPeriod`: the period maps of closed forms span the real
  homomorphisms `H_p(M; ℤ) → ℝ`.

## References

* G. de Rham, *Sur l'analysis situs des variétés à n dimensions*, J. Math. Pures Appl. 10
  (1931), 115–200.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18.
-/

public section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] {p : ℕ}

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
/-- If the integration cocycle of a closed form `φ` and a real cocycle `b` of the smooth singular
cochains have the same class, they differ by a coboundary `d ≫ η`. -/
private theorem exists_integrationCochain_sub_eq_d_comp (φ : closedForms I M p)
    {b : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X p ⟶
      ModuleCat.of ℝ ℝ}
    (hb : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d
      ((ComplexShape.up ℕ).next p) p ≫ b = 0)
    (hc : deRhamCohomology.integration I M p (deRhamCohomology.mk I p φ) =
      ChainComplex.homologyClassOfComp ℝ (ModuleCat.of ℝ ℝ) b hb (𝟙 _)) :
    ∃ η : ((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℝ ℝ)).X ((ComplexShape.up ℕ).prev p) ⟶ ModuleCat.of ℝ ℝ,
      integrationCochain (R := ℝ) (φ.val : RoughForm I M ℝ p) - b =
        ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d p
          ((ComplexShape.up ℕ).prev p) ≫ η := by
  let L := ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
    ℝ (ModuleCat.of ℝ ℝ)
  have hzero : L.homologyπ p (integrationCocycle I M p φ -
      ChainComplex.cocycleOfComp ℝ (ModuleCat.of ℝ ℝ) b hb (𝟙 _)) = 0 := by
    rw [map_sub, ← deRhamCohomology.integration_mk, hc, ChainComplex.homologyClassOfComp_eq b hb
      (𝟙 _) _ (ChainComplex.iCycles_cocycleOfComp b hb (𝟙 _)), sub_self]
  obtain ⟨η, hη⟩ := (L.moduleCat_homologyπ_eq_zero_iff rfl _).1 hzero
  -- Name `η` with its morphism type, so that composites with it can be rewritten.
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℝ ℝ)).X ((ComplexShape.up ℕ).prev p) ⟶ ModuleCat.of ℝ ℝ, η₀ = η := ⟨η, rfl⟩
  refine ⟨η₀, ?_⟩
  have := congrArg (L.iCycles p) hη
  rw [L.moduleCat_iCycles_toCycles_apply, map_sub, iCycles_integrationCocycle,
    ChainComplex.iCycles_cocycleOfComp, Category.comp_id,
    ChainComplex.linearYonedaObj_d_apply] at this
  rw [hη₀]
  exact this.symm

/-- **Closed forms with prescribed periods on smooth singular homology.** Every homomorphism
`g : H_p^∞(M; ℤ) → ℝ` from the integral smooth singular homology of `M` is the period map of a
closed `p`-form `φ`: `∫_z φ = g [z]` for every integral smooth singular cycle `z`. -/
theorem exists_smoothHomologyPeriodHom_eq
    (g : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology p →+ ℝ) :
    ∃ φ : closedForms I M p,
      (smoothHomologyPeriodHom (φ.val : RoughForm I M ℝ p)).toAddMonoidHom = g := by
  -- Work with `g` as a morphism of modules `f` out of the homology object.
  obtain ⟨f, hf⟩ : ∃ f : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).homology p ⟶ ModuleCat.of ℤ ℝ, ∀ x, f x = g x :=
    ⟨ModuleCat.ofHom
      { toFun := g
        map_add' := map_add g
        -- `g` is additive, so linear for any `ℤ`-module structures, which agree with `zsmul`.
        map_smul' := fun n x ↦ (congrArg g (int_smul_eq_zsmul _ n x)).trans
          ((map_zsmul g n x).trans (int_smul_eq_zsmul _ n (g x)).symm) }, fun _ ↦ rfl⟩
  have : Injective (ModuleCat.of ℤ ℝ) := by
    have := (Module.Baer.of_divisible ℝ).injective
    exact Module.injective_object_of_injective_module ℤ ℝ
  obtain ⟨b, hb, hbf⟩ :=
    exists_cocycle_iCycles_comp_eq ℝ (smoothSingularSubcomplex I M : SSet) ℝ p f
  -- By the de Rham theorem, the class of `b` is that of the integration cocycle of a form `φ`, so
  -- the integration cochain of `φ` differs from `b` by a coboundary `d ≫ η`.
  obtain ⟨c, hc⟩ := (deRhamCohomology.bijective_integration I M p).2
    (ChainComplex.homologyClassOfComp ℝ (ModuleCat.of ℝ ℝ) b hb (𝟙 _))
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I p c
  refine ⟨φ, ?_⟩
  obtain ⟨η, hη⟩ := exists_integrationCochain_sub_eq_d_comp φ hb hc
  -- Read on integral chains, the integration cochain of `φ` is that of `b` plus a coboundary.
  have hz := congrArg (fun x ↦
    (cochainValuesEquiv ℤ (ModuleCat.of ℤ ℝ) (smoothSingularSubcomplex I M : SSet) p).symm
      (cochainValuesEquiv ℝ (ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I M : SSet) p x)) hη
  simp only [map_sub, cochainValuesEquiv_symm_cochainValuesEquiv_integrationCochain] at hz
  rw [cochainValuesEquiv_symm_cochainValuesEquiv_d_comp] at hz
  -- On integral cycles the coboundary vanishes, and the values of `b` give `f`.
  refine HomologicalComplex.moduleCat_addMonoidHom_ext_homologyπ fun z ↦ ?_
  rw [LinearMap.toAddMonoidHom_coe, ← hf, smoothHomologyPeriodHom_homologyπ
    (φ.val.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp φ.property),
    eq_add_of_sub_eq hz]
  have h1 := ConcreteCategory.congr_hom hbf z
  have h0 : (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d p
      ((ComplexShape.up ℕ).prev p)).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles p).hom
          z) = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.iCycles_d,
      ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply, h0,
    map_zero, zero_add]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  exact h1

/-- **De Rham's theorem on periods.** On a Hausdorff `σ`-compact smooth manifold `M` modelled on a
finite-dimensional real model with corners, every homomorphism `g : H_p(M; ℤ) → ℝ` is the period
map of a closed `p`-form `φ`: `⟨[φ], c⟩ = g c` for every integral singular homology class `c`. -/
theorem exists_closedFormHomologyPeriod_eq
    (g : ((singularChains ℤ).obj (TopCat.of M)).homology p →+ ℝ) :
    ∃ φ : closedForms I M p, closedFormHomologyPeriod φ = g := by
  obtain ⟨φ, hφ⟩ := exists_smoothHomologyPeriodHom_eq (I := I) (M := M) (p := p)
    (g.comp (smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).hom.hom.toAddMonoidHom)
  refine ⟨φ, AddMonoidHom.ext fun c ↦ ?_⟩
  rw [closedFormHomologyPeriod_apply]
  exact (DFunLike.congr_fun hφ _).trans
    (congrArg g ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).inv_hom_id_apply c))

/-- The periods of closed `p`-forms span the real homomorphisms `H_p(M; ℤ) → ℝ`; indeed every such
homomorphism is a period map (`TauCeti.exists_closedFormHomologyPeriod_eq`). -/
theorem span_range_closedFormHomologyPeriod :
    Submodule.span ℝ (Set.range fun φ : closedForms I M p ↦ closedFormHomologyPeriod φ) = ⊤ :=
  Submodule.eq_top_iff'.2 fun g ↦ Submodule.subset_span (exists_closedFormHomologyPeriod_eq g)

end TauCeti
