/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-!
# Excisive couples with homologically equivalent open neighbourhoods

Two subsets `A` and `B` of a space `X` form an *excisive couple* when the chains `C(A) + C(B)` of
the singular simplices lying in `A` or in `B`, the chains of the small singular subcomplex
`X.smallSingularSubcomplex ![A, B]`, include into the singular chains of `X` by a
quasi-isomorphism. The small-chain theorem says this when `A` and `B` are open and cover `X`
(`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι`), and the Mayer–Vietoris sequence
then holds for `A` and `B`.

Subsets which are not open often have open neighbourhoods `U ⊇ A` and `V ⊇ B` covering `X` such
that `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` induce isomorphisms on singular homology: subcomplexes
of a CW complex are deformation retracts of such neighbourhoods. Then `A` and `B` are excisive
as well (`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds`). The Mayer–Vietoris
short exact sequences of the two couples form a map of short exact sequences, which is a
quasi-isomorphism on the first two terms, hence on the third: the chains `C(A) + C(B)` include
into `C(U) + C(V)` by a quasi-isomorphism, and `C(U) + C(V)` includes into the chains of `X` by
the small-chain theorem.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds`: subsets with open
  neighbourhoods covering `X` whose inclusions, and that of their intersections, are
  quasi-isomorphisms on singular chains form an excisive couple.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, the
  Mayer–Vietoris sequence for deformation retracts of open neighbourhoods.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 4, Section 6, excisive couples.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}}

/-- **Subsets with homologically equivalent open neighbourhoods form an excisive couple.** Let
`A ⊆ U` and `B ⊆ V` be subsets of `X` with `U` and `V` open and covering `X`, such that the
inclusions `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` are quasi-isomorphisms on singular chains with
coefficients in `R`. Then the chains of the singular simplices lying in `A` or in `B` include into
the singular chains of `X` by a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds {A B U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hA : QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hAU))) R))
    (hB : QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hBV))) R))
    (hAB : QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_inter hAU hBV)))) R)) :
    QuasiIso (SSet.chainComplexMap (X.smallSingularSubcomplex ![A, B]).ι R) := by
  have hf : ∀ i, Set.MapsTo (𝟙 X) (![A, B] i) (![U, V] (id i)) :=
    Fin.forall_fin_two.2 ⟨fun _ hx ↦ hAU hx, fun _ hx ↦ hBV hx⟩
  -- The maps of singular simplicial sets from the square of `A` and `B` to that of `U` and `V`.
  let φ₁ := TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_inter hAU hBV)))
  let φ₂ := TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hAU))
  let φ₃ := TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hBV))
  let φ₄ := X.smallSingularSubcomplexMap ![A, B] ![U, V] (𝟙 X) id hf
  have hφ₄ :
      φ₄ ≫ (X.smallSingularSubcomplex ![U, V]).ι = (X.smallSingularSubcomplex ![A, B]).ι := by
    rw [TopCat.smallSingularSubcomplexMap_ι, CategoryTheory.Functor.map_id, Category.comp_id]
  have ht : TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := B)))) ≫ φ₂ =
      φ₁ ≫ TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))) := by
    -- Both composites are the inclusion `A ∩ B ⊆ U`.
    simp only [φ₁, φ₂, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.inclusion_comp_inclusion]
  have hl : TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := A)))) ≫ φ₃ =
      φ₁ ≫ TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U)))) := by
    -- Both composites are the inclusion `A ∩ B ⊆ V`.
    simp only [φ₁, φ₃, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.inclusion_comp_inclusion]
  have hr : TopCat.toSmallSingularSubcomplex ![A, B] (Matrix.cons_val_zero A ![B]).superset ≫ φ₄ =
      φ₂ ≫ TopCat.toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset :=
    TopCat.toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ _ _ hf _ _
      fun _ hx ↦ hAU hx
  have hb : TopCat.toSmallSingularSubcomplex ![A, B]
        ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset ≫ φ₄ =
      φ₃ ≫ TopCat.toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset :=
    TopCat.toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ _ _ hf _ _
      fun _ hx ↦ hBV hx
  -- The map of Mayer–Vietoris short exact sequences is a quasi-isomorphism on the first two
  -- terms, hence on the third.
  let sqAB := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex A B
  let sqUV := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex U V
  let ψ := SSet.mayerVietorisShortComplexMap R sqAB sqUV ht hl hr hb
  have h₂ : QuasiIso ψ.τ₂ := by
    rw [SSet.mayerVietorisShortComplexMap_τ₂]
    exact HomologicalComplex.quasiIso_biprod_map _ _
  have h₃ : QuasiIso ψ.τ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (SSet.shortExact_mayerVietorisShortComplex R sqAB)
    (SSet.shortExact_mayerVietorisShortComplex R sqUV)
    (by rwa [SSet.mayerVietorisShortComplexMap_τ₁]) h₂
  rw [SSet.mayerVietorisShortComplexMap_τ₃] at h₃
  -- Compose with the small-chain theorem for the open cover by `U` and `V`.
  have hUV' := quasiIso_chainComplexMap_smallSingularSubcomplex_ι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV)
  have hcomp : SSet.chainComplexMap (X.smallSingularSubcomplex ![A, B]).ι R =
      SSet.chainComplexMap φ₄ R ≫ SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R := by
    rw [← hφ₄]
    exact CategoryTheory.Functor.map_comp _ _ _
  rw [hcomp]
  exact quasiIso_comp (hφ := h₃) (hφ' := hUV') _ _

end TauCeti
