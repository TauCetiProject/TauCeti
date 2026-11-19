/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Geometry.Manifold.SmoothSingular.Contractible
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MayerVietoris
import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

/-!
# The smoothing theorem

Let `M` be a smooth manifold, over any real model with corners `I`, which is Hausdorff, locally
compact and second countable, for instance a Hausdorff σ-compact manifold over a
finite-dimensional model. This file proves the **smoothing theorem**: the inclusion of the complex
of smooth singular chains of `M` into the complex of singular chains is a quasi-isomorphism, with
coefficients in any object `R` of an abelian category with coproducts (indexed by types in the
universe of `M`), in which countable coproducts are exact, such as a module category
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`). So smooth singular homology is
singular homology (`TauCeti.smoothSingularHomologyIso`), naturally in smooth maps
(`TauCeti.smoothSingularHomologyIso_hom_naturality`). This is the input for reading integrals of
closed forms over smooth cycles on singular homology classes, such as the symplectic area of a
class in `H₂(M; ℤ)`, which is the integral of the symplectic form over a smooth representative.

The proof is the Mayer–Vietoris induction over convex chart domains
(`TauCeti.mayerVietoris_induction_extChartAt`) of the property that the inclusion is a
quasi-isomorphism on an open set. The induction steps for the union of two open sets and for
countable disjoint unions are `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup` and
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`. The base case is a convex chart
domain `U`: the extended chart at `x` maps `U` onto a convex set, so the straight-line contraction
in the chart contracts `U` smoothly, and the inclusion is a chain homotopy equivalence on `U`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex_extChartAt`). The
induction proves the property for the open set `⊤`, which is diffeomorphic to `M`
(`Diffeomorph.ofTop`). A
diffeomorphism induces isomorphisms of smooth singular subcomplexes
(`Diffeomorph.smoothSingularSubcomplexIso`) and of singular simplicial sets compatible with the
inclusions, so the property is invariant under diffeomorphisms
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph`).

Boundary and corners are allowed: no smoothing of individual singular simplices relative to their
faces is used, only contractions, subdivision and Mayer–Vietoris. The disjoint-union step is
indexed by types in the universe of `M`, so it is applied to countable families indexed by
`ULift ℕ`.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: the smoothing theorem.
* `TauCeti.smoothSingularHomologyIso`: smooth singular homology is singular homology.
* `TauCeti.smoothSingularHomologyIso_hom_naturality`,
  `TauCeti.smoothSingularHomologyIso_inv_naturality`: the isomorphism is natural in smooth maps.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph`: the smoothing
  theorem is invariant under diffeomorphisms.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 (the smoothing
  theorem) and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits Set TopologicalSpace Convexity
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

/-! ### Invariance under diffeomorphisms -/

section Diffeomorph

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {M N : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] [CategoryWithHomology C]
  (R : C)

/-- **The smoothing theorem is invariant under diffeomorphisms.** If `M` and `N` are
diffeomorphic, the inclusion of smooth singular chains into singular chains is a
quasi-isomorphism on `M` exactly when it is one on `N`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph
    (Φ : Diffeomorph I J M N ∞) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) := by
  let F := (SSet.chainComplexFunctor C).obj R
  refine quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (F.mapIso Φ.smoothSingularSubcomplexIso)
    (F.mapIso (TopCat.toSSet.mapIso (TopCat.isoOfHomeo Φ.toHomeomorph))) ?_)
  -- The square commutes before applying the chain functor.
  simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Functor.mapIso_hom,
    Diffeomorph.smoothSingularSubcomplexIso_hom]
  rw [← F.map_comp, ← F.map_comp, smoothSingularSubcomplexMap_ι]
  -- The map of topological spaces underlying `TopCat.isoOfHomeo` is `Φ` by definition.
  rfl

end Diffeomorph

/-! ### The smoothing theorem -/

section Smoothing

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] [SecondCountableTopology M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

variable (I M) in
/-- **The smoothing theorem.** On a Hausdorff, locally compact, second countable smooth manifold
`M`, over any real model with corners, the inclusion of smooth singular chains into singular
chains, with coefficients in an object `R` of an abelian category with coproducts (indexed by
types in the universe of `M`), in which countable coproducts are exact, such as a module
category, is a quasi-isomorphism. The hypotheses on `M` hold for a Hausdorff σ-compact manifold
over a finite-dimensional model (`Manifold.locallyCompact_of_finiteDimensional`,
`ChartedSpace.secondCountable_of_sigmaCompact`). -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have key : ∀ U : Opens M, QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
    refine mayerVietoris_induction_extChartAt I _ ?_ ?_ ?_ ?_
    · have : IsEmpty (⊥ : Opens M) := ⟨fun y ↦ y.2⟩
      exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty R
    · intro x K U _ hK hKt hU ⟨y₀, hy₀⟩
      have himage : extChartAt I x '' U = K ∩ range I := hU ▸ extChartAt_image_eq_inter_range hKt
      have hstar : StarConvex ℝ (extChartAt I x y₀) (extChartAt I x '' U) := by
        rw [himage]
        exact (hK.inter I.convex_range).starConvex (himage ▸ mem_image_of_mem _ hy₀)
      exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex_extChartAt R
        (hU.trans_subset inter_subset_left) hstar
    · exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup I R
    · intro s hs h
      -- The disjoint-union step is indexed by a type in the universe of `M`.
      have := HasExactColimitsOfShape.of_domain_equivalence (C := C)
        (Discrete.equivalence Equiv.ulift.{u}.symm : Discrete ℕ ≌ _)
      rw [← (Equiv.ulift.{u} (α := ℕ)).iSup_comp (g := s)]
      exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup (s ∘ ULift.down) C R
        (fun i j hij ↦ hs _ _ (ULift.down_injective.ne hij)) fun i ↦ h i.down
  exact (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph R
    (Diffeomorph.ofTop (I := I) (⊤ : Opens M) rfl)).1 (key ⊤)

variable (I M) in
/-- **Smooth singular homology is singular homology.** The inclusion of smooth singular chains
into singular chains induces an isomorphism on homology in every degree, with coefficients in an
object `R` of an abelian category with coproducts (indexed by types in the universe of `M`), in
which countable coproducts are exact, such as a module category. -/
def smoothSingularHomologyIso (n : ℕ) :
    (smoothSingularSubcomplex I M : SSet).homology R n ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology R n :=
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R
  asIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)

/-- The identification of smooth singular homology with singular homology is the map induced by the
inclusion of smooth singular chains. -/
@[simp]
theorem smoothSingularHomologyIso_hom (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n :=
  (rfl)

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]

/-- The identification of smooth singular homology with singular homology is natural in smooth
maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_hom_naturality {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
        (smoothSingularHomologyIso J N R n).hom =
      (smoothSingularHomologyIso I M R n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n := by
  simp only [smoothSingularHomologyIso_hom, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]

/-- The inverse identification of singular homology with smooth singular homology is natural in
smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_inv_naturality {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (smoothSingularHomologyIso J N R n).inv =
      (smoothSingularHomologyIso I M R n).inv ≫
        SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n := by
  rw [Iso.comp_inv_eq, Category.assoc, smoothSingularHomologyIso_hom_naturality,
    Iso.inv_hom_id_assoc]

end Smoothing

end TauCeti
