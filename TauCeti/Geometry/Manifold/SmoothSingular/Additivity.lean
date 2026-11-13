/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

/-!
# Additivity of smooth singular chains over disjoint open sets

Let `s i` be pairwise disjoint open subsets of a manifold `M`. A smooth singular simplex of the
union `⨆ i, s i` has connected image, so it lies in exactly one `s i`. Read in `s i`, it is still
smooth, because smoothness into an open submanifold is smoothness into the ambient manifold
(`TauCeti.smoothSingularSubcomplex_preimage_inclusion`). Hence in each degree the smooth singular
simplices of the union are the disjoint union of those of the `s i`
(`TauCeti.smoothSingularSubcomplexMap_inclusion_app_bijective`), and the smooth singular
subcomplex of the union is the coproduct of the smooth singular subcomplexes of the `s i`, with
the maps induced by the inclusions as the cofan legs (`TauCeti.isColimitCofanSmoothSingularOpens`).

Since the simplicial chain complex functor preserves coproducts, the smooth singular chain
complex of the union is the coproduct of the smooth singular chain complexes of the `s i`
(`TauCeti.isColimitCofanSmoothSingularChainComplexOpens`), and when coproducts are exact in the
coefficient category, as for modules over a ring, so is smooth singular homology in every degree
(`TauCeti.isColimitCofanSmoothSingularHomologyOpens`). Ordinary singular chains and homology
decompose in the same way (`TauCeti.isColimitCofanSingularChainComplexOpens`), compatibly with
the inclusion of smooth chains into singular chains. So that inclusion is a quasi-isomorphism on
the union as soon as it is one on every `s i`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`). This is the input for
countable disjoint unions to a Mayer–Vietoris induction over open sets
(`TauCeti.mayerVietoris_induction`) comparing smooth and singular homology.

The index type lives in the universe of `M`, as for the additivity of singular chains; for the
induction it is `ℕ`, and `M` is a type in `Type`.

## Main results

* `TauCeti.smoothSingularSubcomplexMap_inclusion_app_bijective`: in each degree, the smooth
  singular simplices of `⨆ i, s i` are those of the `s i`.
* `TauCeti.isColimitCofanSmoothSingularOpens`: the smooth singular subcomplex of `⨆ i, s i` is the
  coproduct of those of the `s i`.
* `TauCeti.isColimitCofanSmoothSingularChainComplexOpens`,
  `TauCeti.isColimitCofanSmoothSingularHomologyOpens`: the same for smooth singular chains and,
  under exactness of coproducts, smooth singular homology.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`: if smooth chains include
  into singular chains by a quasi-isomorphism on every `s i`, they do so on `⨆ i, s i`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  disjoint-union step of the comparison of smooth and singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits Function Set TopologicalSpace TopCat
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type u} (s : ι → Opens M)

variable (I) in
/-- In each degree, the smooth singular simplices of a union of pairwise disjoint open sets `s i`
are exactly the smooth singular simplices of the members: such a simplex lies in a unique `s i`,
and it comes from a unique smooth singular simplex there. -/
theorem smoothSingularSubcomplexMap_inclusion_app_bijective (hs : Pairwise (Disjoint on s))
    (n : SimplexCategoryᵒᵖ) : Function.Bijective
      (fun p : Σ i, (smoothSingularSubcomplex I (s i) : SSet).obj n ↦
        (smoothSingularSubcomplexMap (Opens.inclusion (le_iSup s p.1))
          (contMDiff_inclusion _)).app n p.2) := by
  have hcont := toSSet_map_inclusion_app_bijective n s hs
  refine ⟨?_, fun τ ↦ ?_⟩
  · rintro ⟨i, σ⟩ ⟨j, σ'⟩ h
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 (hcont.1 (a₁ := ⟨i, σ.1⟩) (a₂ := ⟨j, σ'.1⟩)
      ((coe_smoothSingularSubcomplexMap_app _ σ).symm.trans
        ((congrArg Subtype.val h).trans (coe_smoothSingularSubcomplexMap_app _ σ'))))
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (eq_of_heq h')))
  · obtain ⟨⟨i, σ⟩, hσ⟩ := hcont.2 τ.1
    dsimp only at hσ
    have hσs : σ ∈ (smoothSingularSubcomplex I (s i)).obj n :=
      (smoothSingularSubcomplex_preimage_inclusion (le_iSup s i)).le n (by
        rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage, hσ]
        exact τ.2)
    exact ⟨⟨i, ⟨σ, hσs⟩⟩, Subtype.ext ((coe_smoothSingularSubcomplexMap_app _ _).trans hσ)⟩

variable (I) in
/-- The smooth singular subcomplex of a union of pairwise disjoint open sets `s i` is the
coproduct of the smooth singular subcomplexes of the `s i`, with the maps induced by the
inclusions as the cofan legs. -/
def isColimitCofanSmoothSingularOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk (smoothSingularSubcomplex I ↥(⨆ i, s i) : SSet)
      (fun i ↦ smoothSingularSubcomplexMap (Opens.inclusion (le_iSup s i))
        (contMDiff_inclusion _)) :
      Cofan fun i ↦ (smoothSingularSubcomplex I (s i) : SSet)) :=
  evaluationJointlyReflectsColimits _ fun n ↦ (isColimitMapCoconeCofanMkEquiv _ _ _).symm
    ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2
      (smoothSingularSubcomplexMap_inclusion_app_bijective I s hs n)).some

section Chains

variable (C : Type v) [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] (R : C)

variable (I) in
/-- **Additivity of smooth singular chains over disjoint open sets.** The smooth singular chain
complex of a union of pairwise disjoint open sets `s i`, with coefficients in `R`, is the coproduct
of the smooth singular chain complexes of the `s i`, with the maps induced by the inclusions as
the cofan legs. -/
def isColimitCofanSmoothSingularChainComplexOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk ((smoothSingularSubcomplex I ↥(⨆ i, s i) : SSet).chainComplex R)
      (fun i ↦ SSet.chainComplexMap (smoothSingularSubcomplexMap (Opens.inclusion (le_iSup s i))
        (contMDiff_inclusion _)) R) :
      Cofan fun i ↦ (smoothSingularSubcomplex I (s i) : SSet).chainComplex R) :=
  isColimitCofanMkObjOfIsColimit ((SSet.chainComplexFunctor C).obj R) _ _
    (isColimitCofanSmoothSingularOpens I s hs)

end Chains

section Homology

variable (C : Type v) [Category.{w} C] [HasCoproducts.{u} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ι) C] (R : C) (k : ℕ)

variable (I) in
/-- **Additivity of smooth singular homology over disjoint open sets.** If coproducts indexed by
`ι` are exact in `C`, then in every degree the smooth singular homology of a union of pairwise
disjoint open sets `s i`, with coefficients in `R`, is the coproduct of the smooth singular
homologies of the `s i`, with the maps induced by the inclusions as the cofan legs. -/
def isColimitCofanSmoothSingularHomologyOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk ((smoothSingularSubcomplex I ↥(⨆ i, s i) : SSet).homology R k)
      (fun i ↦ SSet.homologyMap (smoothSingularSubcomplexMap (Opens.inclusion (le_iSup s i))
        (contMDiff_inclusion _)) R k) :
      Cofan fun i ↦ (smoothSingularSubcomplex I (s i) : SSet).homology R k) :=
  isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor C _ k) _ _
    (isColimitCofanSmoothSingularChainComplexOpens I s C R hs)

/-- **The disjoint-union step of the smoothing theorem.** If coproducts indexed by `ι` are exact
in `C` and, for every member of a family of pairwise disjoint open sets `s i`, the inclusion of
smooth singular chains into singular chains with coefficients in `R` is a quasi-isomorphism, then
so is the inclusion for the union `⨆ i, s i`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup (hs : Pairwise (Disjoint on s))
    (h : ∀ i, QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I (s i)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(⨆ i, s i)).ι R) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hc₁ := isColimitCofanSmoothSingularHomologyOpens I s C R k hs
  have hc₂ := isColimitCofanSingularHomologyOpens s C R k hs
  let e := hc₁.coconePointsIsoOfNatIso hc₂
    (Discrete.natIso fun i ↦ asIso (SSet.homologyMap (smoothSingularSubcomplex I (s i.as)).ι R k))
  have he : e.hom = SSet.homologyMap (smoothSingularSubcomplex I ↥(⨆ i, s i)).ι R k := by
    refine hc₁.hom_ext fun ⟨i⟩ ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp only [Cofan.mk_ι_app, Discrete.natIso_hom_app, asIso_hom]
    rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]
  have he' : IsIso e.hom := inferInstance
  rw [he] at he'
  exact he'

end Homology

end TauCeti
