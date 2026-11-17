/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.Data.Set.Lattice
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision
public import TauCeti.Topology.Sets.FinTwo

/-!
# The Mayer–Vietoris step of the comparison of smooth and singular chains

Let `U` and `V` be open subsets of a manifold `M`. This file proves that if smooth singular chains
include into singular chains by a quasi-isomorphism on `U`, on `V` and on `U ∩ V`, then they do so
on `U ∪ V` (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). For the property
`P(O)` of an open set `O` that this inclusion is a quasi-isomorphism on `O`, this is the step
`P(U), P(V), P(U ∩ V) ⟹ P(U ∪ V)` of the Mayer–Vietoris induction over open sets
(`TauCeti.mayerVietoris_induction`), whose step for countable disjoint unions is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`. That induction compares smooth
with singular chains on a manifold.

Write `W = U ∪ V`. Inside the singular simplicial set of `W`, the singular simplices of `U`, of
`V` and of `U ∩ V` are the simplices lying in these sets, and by
`TauCeti.range_smoothSingularSubcomplex_ι_comp_toSSet_map_inclusion` the smooth singular simplices
of an open subset `O ⊆ W` are the smooth singular simplices of `W` lying in `O`. So the smooth and
the singular simplices lying in `U`, in `V`, in `U ∩ V` and in `U` or in `V` form two bicartesian
squares of subcomplexes, and the inclusion of the first square into the second is a map of
pushout squares. The Mayer–Vietoris short exact sequences of chain complexes of the two squares
(`SSet.shortExact_mayerVietorisShortComplex`) form a map of short exact sequences. By hypothesis
it is a quasi-isomorphism on the first two terms, so it is one on the third
(`HomologicalComplex.HomologySequence.quasiIso_τ₃`): the smooth chains subordinate to the cover
`{U, V}` include into the singular chains subordinate to it by a quasi-isomorphism. Both include
into all chains of their kind by quasi-isomorphisms, by the small-chain theorems for smooth chains
(`TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`, the smooth simplices
forming an affinely stable subcomplex) and for singular chains
(`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι`). Hence the inclusion of smooth
chains of `W` into its singular chains is a quasi-isomorphism.

The coefficients are an arbitrary object of an abelian category with coproducts. The space `M`
need only be a charted space: no separation, countability or finite-dimensionality assumption is
used, and the model may have boundary or corners.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the Mayer–Vietoris step of the
  comparison of smooth and singular chains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  Mayer–Vietoris step of the comparison of smooth and singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace SSet.Subcomplex

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- The map of singular simplicial sets induced by the inclusion of open sets `U ≤ W`. -/
private abbrev toSSetInclusion {U W : Opens M} (h : U ≤ W) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ TopCat.toSSet.obj (TopCat.of W) :=
  TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩)

/-- A singular simplex of `W` comes from the open subset `U ≤ W` exactly when it lies in `U`. -/
private lemma mem_range_toSSetInclusion_iff {U W : Opens M} (h : U ≤ W) (k : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of W)).obj k) :
    σ ∈ (SSet.Subcomplex.range (toSSetInclusion h)).obj k ↔
      Set.range ((TopCat.of W).toSSetObjEquiv k σ) ⊆ {x : W | (x : M) ∈ U} := by
  have hr : Set.range (Opens.inclusion h) = {x : W | (x : M) ∈ U} := Set.range_inclusion _
  rw [← hr]
  exact (Opens.isOpenEmbedding_of_le h).isInducing.mem_range_toSSet_map_app_iff
    (f := TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩) k σ

/-- The singular simplices of `W` lying in `U` and in `V` are those lying in `U ⊓ V`. -/
private lemma range_toSSetInclusion_inf {U V W : Opens M} (hU : U ≤ W) (hV : V ≤ W) :
    SSet.Subcomplex.range (toSSetInclusion hU) ⊓ SSet.Subcomplex.range (toSSetInclusion hV) =
      SSet.Subcomplex.range (toSSetInclusion (inf_le_left.trans hU : U ⊓ V ≤ W)) := by
  ext k σ
  -- The meet of subcomplexes is computed pointwise.
  change σ ∈ (SSet.Subcomplex.range (toSSetInclusion hU)).obj k ∧
      σ ∈ (SSet.Subcomplex.range (toSSetInclusion hV)).obj k ↔ _
  simp only [mem_range_toSSetInclusion_iff, ← Set.subset_inter_iff]
  rfl

/-- The singular simplices of `U ⊔ V` lying in `U` or in `V` are its small singular simplices for
the cover by `U` and `V`. -/
private lemma range_toSSetInclusion_sup (U V : Opens M) :
    SSet.Subcomplex.range (toSSetInclusion (le_sup_left : U ≤ U ⊔ V)) ⊔
        SSet.Subcomplex.range (toSSetInclusion (le_sup_right : V ≤ U ⊔ V)) =
      (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
        ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}] := by
  ext k σ
  -- The join of subcomplexes is computed pointwise.
  change σ ∈ (SSet.Subcomplex.range (toSSetInclusion (le_sup_left : U ≤ U ⊔ V))).obj k ∨
      σ ∈ (SSet.Subcomplex.range (toSSetInclusion (le_sup_right : V ≤ U ⊔ V))).obj k ↔ _
  simp only [mem_range_toSSetInclusion_iff, TopCat.mem_smallSingularSubcomplex_iff,
    Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

/-- For open sets `O ≤ W`, the inclusion of the smooth singular chains of `O` into its singular
chains is a quasi-isomorphism exactly when the inclusion of the chains of the smooth singular
simplices of `W` lying in `O` into the chains of all singular simplices of `W` lying in `O` is
one. -/
private lemma quasiIso_homOfLE_range_iff {O W : Opens M} (h : O ≤ W) :
    QuasiIso (SSet.chainComplexMap (homOfLE (Subfunctor.range_comp_le
      (smoothSingularSubcomplex I O).ι (toSSetInclusion h))) R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I O).ι R) := by
  have : Mono (TopCat.ofHom (⟨Opens.inclusion h, continuous_inclusion h⟩ : C(O, W))) :=
    (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)
  have : Mono (toSSetInclusion h) := Functor.map_mono _ _
  have hsq : toRange ((smoothSingularSubcomplex I O).ι ≫ toSSetInclusion h) ≫
        homOfLE (Subfunctor.range_comp_le (smoothSingularSubcomplex I O).ι (toSSetInclusion h)) =
      (smoothSingularSubcomplex I O).ι ≫ toRange (toSSetInclusion h) := by
    rw [← cancel_mono (SSet.Subcomplex.range (toSSetInclusion h)).ι]
    simp
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (((SSet.chainComplexFunctor C).obj R).mapArrow.mapIso
      (Arrow.isoMk (f := Arrow.mk (smoothSingularSubcomplex I O).ι)
        (g := Arrow.mk (homOfLE (Subfunctor.range_comp_le (smoothSingularSubcomplex I O).ι
          (toSSetInclusion h))))
        (asIso (toRange ((smoothSingularSubcomplex I O).ι ≫ toSSetInclusion h)))
        (asIso (toRange (toSSetInclusion h))) hsq))).symm

/-- The Mayer–Vietoris part of the proof: under the hypotheses of the Mayer–Vietoris step, the
chains of the smooth singular simplices of `U ⊔ V` lying in `U` or in `V` include into the chains of
all its singular simplices lying in `U` or in `V` by a quasi-isomorphism. -/
private lemma quasiIso_homOfLE_inf_smallSingularSubcomplex (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (homOfLE (inf_le_right :
      smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
        ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}] ≤ _)) R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  have hU' : U ≤ U ⊔ V := le_sup_left
  have hV' : V ≤ U ⊔ V := le_sup_right
  have hUV' : U ⊓ V ≤ U ⊔ V := inf_le_left.trans le_sup_left
  -- The singular simplices of `U ⊔ V` lying in `U ⊓ V`, in `U`, in `V`, and in `U` or in `V`.
  let B₁ := SSet.Subcomplex.range (toSSetInclusion hUV')
  let B₂ := SSet.Subcomplex.range (toSSetInclusion hU')
  let B₃ := SSet.Subcomplex.range (toSSetInclusion hV')
  let B₄ := (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}]
  -- The smooth ones among them.
  let A₁ :=
    SSet.Subcomplex.range ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫ toSSetInclusion hUV')
  let A₂ := SSet.Subcomplex.range ((smoothSingularSubcomplex I U).ι ≫ toSSetInclusion hU')
  let A₃ := SSet.Subcomplex.range ((smoothSingularSubcomplex I V).ι ≫ toSSetInclusion hV')
  have hA₁ : A₁ = S ⊓ B₁ := range_smoothSingularSubcomplex_ι_comp_toSSet_map_inclusion hUV'
  have hA₂ : A₂ = S ⊓ B₂ := range_smoothSingularSubcomplex_ι_comp_toSSet_map_inclusion hU'
  have hA₃ : A₃ = S ⊓ B₃ := range_smoothSingularSubcomplex_ι_comp_toSSet_map_inclusion hV'
  have sqB : SSet.Subcomplex.BicartSq B₁ B₂ B₃ B₄ :=
    ⟨range_toSSetInclusion_sup U V, range_toSSetInclusion_inf hU' hV'⟩
  have sqA : SSet.Subcomplex.BicartSq A₁ A₂ A₃ (S ⊓ B₄) := by
    refine ⟨?_, ?_⟩
    · rw [hA₂, hA₃, ← sqB.sup_eq]
      ext k σ
      -- Joins and meets of subcomplexes are computed pointwise.
      change (σ ∈ S.obj k ∧ σ ∈ B₂.obj k) ∨ (σ ∈ S.obj k ∧ σ ∈ B₃.obj k) ↔
        σ ∈ S.obj k ∧ (σ ∈ B₂.obj k ∨ σ ∈ B₃.obj k)
      exact and_or_left.symm
    · rw [hA₁, hA₂, hA₃, ← sqB.inf_eq]
      exact (inf_inf_distrib_left _ _ _).symm
  have h₁₁ : A₁ ≤ B₁ := hA₁ ▸ inf_le_right
  have h₂₂ : A₂ ≤ B₂ := hA₂ ▸ inf_le_right
  have h₃₃ : A₃ ≤ B₃ := hA₃ ▸ inf_le_right
  -- The map of Mayer–Vietoris short exact sequences is a quasi-isomorphism on the first two
  -- terms, by hypothesis, hence on the third.
  have h₁ := (quasiIso_homOfLE_range_iff R hUV').2 hUV
  have := (quasiIso_homOfLE_range_iff R hU').2 hU
  have := (quasiIso_homOfLE_range_iff R hV').2 hV
  have h₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (SSet.mayerVietorisShortComplexMap R sqA.isPushout sqB.isPushout
      (φ₁ := homOfLE h₁₁) (φ₂ := homOfLE h₂₂) (φ₃ := homOfLE h₃₃)
      (φ₄ := homOfLE (inf_le_right : S ⊓ B₄ ≤ B₄))
      (by rw [homOfLE_comp, homOfLE_comp]) (by rw [homOfLE_comp, homOfLE_comp])
      (by rw [homOfLE_comp, homOfLE_comp]) (by rw [homOfLE_comp, homOfLE_comp]))
    (SSet.shortExact_mayerVietorisShortComplex R sqA.isPushout)
    (SSet.shortExact_mayerVietorisShortComplex R sqB.isPushout)
    (by rw [SSet.mayerVietorisShortComplexMap_τ₁]; exact h₁)
    (by
      rw [SSet.mayerVietorisShortComplexMap_τ₂]
      exact HomologicalComplex.quasiIso_biprod_map _ _)
  rwa [SSet.mayerVietorisShortComplexMap_τ₃] at h₃

/-- **The Mayer–Vietoris step of the comparison of smooth and singular chains.** For open subsets
`U` and `V` of a manifold `M`, if the inclusions of smooth singular chains into singular chains
with coefficients in `R` are quasi-isomorphisms on `U`, on `V` and on `U ⊓ V`, then so is the
inclusion on `U ⊔ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  let A : Fin 2 → Set (TopCat.of ↥(U ⊔ V)) := ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}]
  let B := (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex A
  have hA : ∀ i, IsOpen (A i) := (continuous_subtype_val.isOpen_preimage _ U.isOpen).vecCons
    (continuous_subtype_val.isOpen_preimage _ V.isOpen)
  have hAcov : ⋃ i, A i = Set.univ := by
    refine (Set.iUnion_vecCons_pair _ _).trans (Set.eq_univ_of_forall fun x ↦ ?_)
    exact (Opens.mem_sup.1 x.2).imp id id
  -- The smooth chains subordinate to the cover by `U` and `V` include into all smooth chains and
  -- into the singular chains subordinate to the cover by quasi-isomorphisms, and the latter
  -- include into all singular chains by a quasi-isomorphism, by the small-chain theorems.
  have h₁ := quasiIso_homOfLE_inf_smallSingularSubcomplex R U V hU hV hUV
  have hS : QuasiIso (SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ B ≤ S)) R) :=
    quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R S A hA hAcov
  have hB : QuasiIso (SSet.chainComplexMap B.ι R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplex_ι R A hA hAcov
  have hcomp : SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ B ≤ S)) R ≫
        SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap (homOfLE (inf_le_right : S ⊓ B ≤ B)) R ≫
        SSet.chainComplexMap B.ι R := by
    rw [← Functor.map_comp, ← Functor.map_comp, homOfLE_ι, homOfLE_ι]
  have : QuasiIso (SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ B ≤ S)) R ≫
      SSet.chainComplexMap S.ι R) := by
    rw [hcomp]
    exact quasiIso_comp (hφ := h₁) (hφ' := hB) _ _
  exact quasiIso_of_comp_left (SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ B ≤ S)) R) _

end TauCeti
