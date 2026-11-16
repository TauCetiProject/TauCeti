/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.AlgebraicTopology.SimplicialSet.Subcomplex
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# The Mayer–Vietoris step of the comparison of smooth and singular chains

Let `U` and `V` be open subsets of a manifold `M`. If smooth singular chains include into singular
chains by a quasi-isomorphism on `U`, on `V` and on `U ⊓ V`, then they do so on `U ⊔ V`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). Together with the
disjoint-union step `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`, this is
the inductive step of the comparison of smooth with continuous singular homology by a
Mayer–Vietoris induction over open sets (`TauCeti.mayerVietoris_induction`).

The proof takes place in the singular simplicial set of `W = U ⊔ V`. There the singular simplices
of `U`, of `V` and of `U ⊓ V` are the subcomplexes of simplices with image in the corresponding
subset, and they form a bicartesian square with the subcomplex of simplices subordinate to the
cover of `W` by `U` and `V` (`TopCat.bicartSq_range_toSSet_map_inclusion`). A singular simplex of
the open set `U` is smooth exactly when it is smooth in `W`
(`TauCeti.smoothSingularSubcomplex_preimage_inclusion`), so the hypothesis on `U` is the statement
that the smooth simplices of `W` lying in `U` include into all simplices of `W` lying in `U` by a
quasi-isomorphism (`SSet.Subcomplex.morphismProperty_ι_preimage_iff`).
Comparing the Mayer–Vietoris sequences of these two bicartesian squares gives the same for the
simplices subordinate to the cover (`SSet.quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq`), and
the small-chain theorems for singular chains
(`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι`) and for smooth singular chains
(`TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`) remove the restriction to
the cover.

No hypothesis on the manifold beyond its charted space structure is needed, and the coefficients
are an arbitrary object of an abelian category with coproducts.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the inclusion of smooth
  singular chains into singular chains is a quasi-isomorphism on `U ⊔ V` if it is one on `U`, on
  `V` and on `U ⊓ V`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  Mayer–Vietoris step of the comparison of smooth and singular homology).
* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u


namespace TauCeti

open TopologicalSpace
open SSet.Subcomplex (range homOfLE_ι)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

variable {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- For open sets `U ≤ V`, smooth singular chains include into singular chains of `U` by a
quasi-isomorphism exactly when, in the singular simplicial set of `V`, the smooth simplices with
image in `U` include into all simplices with image in `U` by a quasi-isomorphism. -/
private lemma quasiIso_smoothSingularSubcomplex_ι_iff {U V : Opens M} (h : U ≤ V) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) ↔
      QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right :
        smoothSingularSubcomplex I V ⊓ range (TopCat.toSSet.map
          (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩)) ≤ _)) R) := by
  have := SSet.Subcomplex.morphismProperty_ι_preimage_iff
    (TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩))
    (smoothSingularSubcomplex I V)
    ((HomologicalComplex.quasiIso C _).inverseImage ((SSet.chainComplexFunctor C).obj R))
  rw [smoothSingularSubcomplex_preimage_inclusion, MorphismProperty.inverseImage_iff,
    MorphismProperty.inverseImage_iff, HomologicalComplex.mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff] at this
  -- `SSet.chainComplexMap f R` is an abbreviation for `((SSet.chainComplexFunctor C).obj R).map f`.
  exact this

variable {U V : Opens M}

/-- **The Mayer–Vietoris step of the comparison of smooth and singular chains.** For open subsets
`U` and `V` of a manifold, if the inclusion of smooth singular chains into singular chains with
coefficients in `R` is a quasi-isomorphism on `U`, on `V` and on `U ⊓ V`, then it is a
quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  let cover : Fin 2 → Set (TopCat.of ↥(U ⊔ V)) := ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}]
  have hcover : ∀ i, IsOpen (cover i) :=
    (continuous_subtype_val.isOpen_preimage _ U.isOpen).vecCons
      (continuous_subtype_val.isOpen_preimage _ V.isOpen)
  have hcover' : ⋃ i, cover i = Set.univ := (Set.iUnion_vecCons_pair _ _).trans
    (Set.eq_univ_of_forall fun x ↦ Opens.mem_sup.1 x.2)
  let Q := (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex cover
  rw [quasiIso_smoothSingularSubcomplex_ι_iff R (le_sup_left : U ≤ U ⊔ V)] at hU
  rw [quasiIso_smoothSingularSubcomplex_ι_iff R (le_sup_right : V ≤ U ⊔ V)] at hV
  rw [quasiIso_smoothSingularSubcomplex_ι_iff R
    (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V)] at hUV
  -- Comparing the Mayer–Vietoris sequences of the smooth and the singular simplices.
  have hSQ := SSet.quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq R
    (TopCat.bicartSq_range_toSSet_map_inclusion U V) hUV hU hV
  -- The small-chain theorem for singular and for smooth singular chains.
  have hQ := quasiIso_chainComplexMap_smallSingularSubcomplex_ι R cover hcover hcover'
  have hS := quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R S cover hcover
    hcover'
  -- Both composites are the inclusion of the small smooth singular simplices.
  have hcomp : SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ Q ≤ S)) R ≫
      SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : S ⊓ Q ≤ Q)) R ≫
        SSet.chainComplexMap Q.ι R := by
    rw [← Functor.map_comp, ← Functor.map_comp, homOfLE_ι, homOfLE_ι]
  have : QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ Q ≤ S)) R ≫
      SSet.chainComplexMap S.ι R) := by
    rw [hcomp]
    exact quasiIso_comp (hφ := hSQ) (hφ' := hQ) _ _
  exact quasiIso_of_comp_left
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ Q ≤ S)) R) _

end TauCeti
