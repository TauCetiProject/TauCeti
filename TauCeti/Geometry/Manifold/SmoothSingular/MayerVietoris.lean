/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.CategoryTheory.Subfunctor.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision
public import TauCeti.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# The Mayer–Vietoris step of the comparison of smooth and singular chains

Let `M` be a manifold and let `U` and `V` be open subsets. This file proves that if the inclusion
of smooth singular chains into singular chains is a quasi-isomorphism on `U`, on `V` and on
`U ∩ V`, then it is one on `U ∪ V`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). This is the binary-union
hypothesis of Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`) for the comparison of
smooth with singular homology; the disjoint-union hypothesis is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`.

Write `W = U ∪ V` and `S` for the smooth singular simplices of `W`. Inside the singular simplicial
set of `W`, the simplices lying in `U ∩ V`, in `U` and in `V` and the simplices lying in `U` or in
`V` form a bicartesian square of subcomplexes (`TopCat.bicartSq_range_toSSet_map_inclusion`), and
intersecting it with `S` gives the bicartesian square of the corresponding smooth simplices
(`Lattice.BicartSq.inf_left`). Its corners are the smooth simplices of `U ∩ V`, of
`U` and of `V`: a singular simplex of `W` lying in `U` is smooth exactly when it is smooth as a
simplex of `U` (`TauCeti.range_smoothSingularSubcomplexMap_inclusion_ι`). The inclusion of the
smooth square into the singular square is a map of Mayer–Vietoris short exact sequences of chain
complexes. By hypothesis it is a quasi-isomorphism on the first two terms
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE`), hence on the third,
the chains of simplices lying in `U` or in `V`. The small-chain theorems, for singular chains and
for the affinely stable subcomplex `S`, identify the homology of those chains with the singular and
the smooth singular homology of `W`
(`TauCeti.quasiIso_chainComplexMap_ι_iff_homOfLE_inf_smallSingularSubcomplex`), which gives the
conclusion.

No `IsManifold` hypothesis on `M`, Hausdorff property or finite-dimensionality is used.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE`: for open sets
  `U ≤ W`, the inclusion of smooth into singular chains of `U` is a quasi-isomorphism exactly when
  that of the smooth simplices of `W` lying in `U` into all singular simplices of `W` lying in `U`
  is.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the Mayer–Vietoris step of the
  comparison of smooth and singular chains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  Mayer–Vietoris step of the comparison of smooth and singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

section Inclusion

variable {U W : Opens M} (h : U ≤ W)

variable {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
  [CategoryWithHomology C] (R : C)

variable (I) in
/-- For open sets `U ≤ W` of `M`, the inclusion of smooth singular chains into singular chains of
`U` is a quasi-isomorphism exactly when the inclusion of the chains of the smooth singular
simplices of `W` lying in `U` into the chains of all singular simplices of `W` lying in `U` is
one. The two inclusions are isomorphic as arrows. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) ↔
      QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right :
        smoothSingularSubcomplex I W ⊓ SSet.Subcomplex.range
            (TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩)) ≤
          SSet.Subcomplex.range
            (TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩))))
        R) := by
  set f := TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩)
  have : Mono (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩) :=
    (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)
  have : Mono f := Functor.map_mono _ _
  have : Mono (smoothSingularSubcomplexMap (Opens.inclusion h) (contMDiff_inclusion h) ≫
      (smoothSingularSubcomplex I W).ι) := by
    rw [smoothSingularSubcomplexMap_ι]
    exact mono_comp _ _
  let e₁ := asIso (SSet.Subcomplex.toRange (smoothSingularSubcomplexMap (Opens.inclusion h)
    (contMDiff_inclusion h) ≫ (smoothSingularSubcomplex I W).ι)) ≪≫
      SSet.Subcomplex.eqToIso (range_smoothSingularSubcomplexMap_inclusion_ι h)
  let e₂ := asIso (SSet.Subcomplex.toRange f)
  have hcomm : e₁.hom ≫ SSet.Subcomplex.homOfLE inf_le_right =
      (smoothSingularSubcomplex I U).ι ≫ e₂.hom := by
    rw [← cancel_mono (SSet.Subcomplex.range f).ι]
    simp [e₁, e₂, f]
  have hchain : SSet.chainComplexMap e₁.hom R ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_right) R =
      SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R ≫ SSet.chainComplexMap e₂.hom R := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomm]
  rw [← quasiIso_iff_comp_right _ (SSet.chainComplexMap e₂.hom R), ← hchain,
    quasiIso_iff_comp_left]

end Inclusion

section MayerVietoris

variable (I) {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- **The Mayer–Vietoris step of the comparison of smooth and singular chains.** If the inclusion
of smooth singular chains into singular chains, with coefficients in `R`, is a quasi-isomorphism on
the open sets `U`, `V` and `U ∩ V` of `M`, then it is a quasi-isomorphism on `U ∪ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  have sq₂ := TopCat.bicartSq_range_toSSet_map_inclusion U V
  -- Intersecting the square of singular simplices with `S` gives the square of smooth simplices.
  have sq₁ : SSet.Subcomplex.BicartSq _ _ _ _ := sq₂.inf_left S
  have hc {A B C D : (TopCat.toSSet.obj (TopCat.of ↥(U ⊔ V))).Subcomplex} (h₁ : A ≤ B)
      (h₂ : B ≤ D) (h₃ : A ≤ C) (h₄ : C ≤ D) :
      SSet.Subcomplex.homOfLE h₁ ≫ SSet.Subcomplex.homOfLE h₂ =
        SSet.Subcomplex.homOfLE h₃ ≫ SSet.Subcomplex.homOfLE h₄ := by
    simp only [SSet.Subcomplex.homOfLE_comp]
  -- The inclusion of the smooth square into the singular square is a map of Mayer–Vietoris short
  -- exact sequences, a quasi-isomorphism on the first two terms by hypothesis.
  have h₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (SSet.mayerVietorisShortComplexMap R sq₁.isPushout sq₂.isPushout
      (φ₁ := SSet.Subcomplex.homOfLE inf_le_right) (φ₂ := SSet.Subcomplex.homOfLE inf_le_right)
      (φ₃ := SSet.Subcomplex.homOfLE inf_le_right) (φ₄ := SSet.Subcomplex.homOfLE inf_le_right)
      (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _))
    (SSet.shortExact_mayerVietorisShortComplex R sq₁.isPushout)
    (SSet.shortExact_mayerVietorisShortComplex R sq₂.isPushout)
    (by
      rw [SSet.mayerVietorisShortComplexMap_τ₁]
      exact (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I _ R).1 hUV)
    (by
      rw [SSet.mayerVietorisShortComplexMap_τ₂]
      have := (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I
        (le_sup_left : U ≤ U ⊔ V) R).1 hU
      have := (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I
        (le_sup_right : V ≤ U ⊔ V) R).1 hV
      exact HomologicalComplex.quasiIso_biprod_map _ _)
  rw [SSet.mayerVietorisShortComplexMap_τ₃] at h₃
  -- By the small-chain theorems, this is the conclusion.
  have hcov : ⋃ i, ![{x : ↥(U ⊔ V) | (x : M) ∈ U}, {x | (x : M) ∈ V}] i = Set.univ := by
    rw [Set.iUnion_vecCons_pair]
    exact Set.eq_univ_of_forall fun x ↦ Opens.mem_sup.1 x.2
  exact (quasiIso_chainComplexMap_ι_iff_homOfLE_inf_smallSingularSubcomplex R S _
    (IsOpen.vecCons (U.isOpen.preimage continuous_subtype_val)
      (V.isOpen.preimage continuous_subtype_val)) hcov).2 h₃

end MayerVietoris

end TauCeti
