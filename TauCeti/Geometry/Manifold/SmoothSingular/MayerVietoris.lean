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
public import TauCeti.AlgebraicTopology.Singular.Subspace
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# The Mayer–Vietoris step comparing smooth and singular chains

Let `U` and `V` be open subsets of a manifold `M`. If smooth singular chains include into singular
chains by a quasi-isomorphism on `U`, on `V` and on `U ∩ V`, then they do so on `U ∪ V`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). This is the union step of a
Mayer–Vietoris induction over open sets (`TauCeti.mayerVietoris_induction`) comparing smooth
singular homology with singular homology; the disjoint-union step is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`.

The proof compares two Mayer–Vietoris short exact sequences. Write `W = U ∪ V`. In the singular
simplicial set of `W`, the singular simplices of `U ∩ V`, `U` and `V`, read in `W`, form a
bicartesian square of subcomplexes whose union is the subcomplex of simplices lying in `U` or in
`V`. The smooth singular simplices of `U ∩ V`, `U` and `V`, read in `W`, are the smooth singular
simplices of `W` lying in these sets
(`TauCeti.range_smoothSingularSubcomplexMap_inclusion_comp_ι`), so they form a bicartesian square
too, whose union is the subcomplex of smooth simplices lying in `U` or in `V`. The inclusion of
the smooth square into the singular one is a map of Mayer–Vietoris short exact sequences
(`SSet.mayerVietorisShortComplexMap`), a quasi-isomorphism on the first two terms by hypothesis,
hence on the third (`HomologicalComplex.HomologySequence.quasiIso_τ₃`). Finally, by the
small-chain theorem, for singular chains
(`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι`) and for smooth singular chains, an
affinely stable subcomplex (`TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`),
the chains of the simplices lying in `U` or in `V` compute the homology of `W` on both sides.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the Mayer–Vietoris step of
  the comparison of smooth and singular chains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- The map of singular simplicial sets induced by the inclusion of open sets `A ≤ B`. -/
private abbrev singularInclusion {A B : Opens M} (h : A ≤ B) :
    TopCat.toSSet.obj (TopCat.of A) ⟶ TopCat.toSSet.obj (TopCat.of B) :=
  TopCat.toSSet.map
    (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion (SetLike.coe_subset_coe.2 h)⟩)

variable (I) in
/-- The smooth singular simplices of an open set `A`, read as singular simplices of an open set
`B ≥ A`. -/
private abbrev smoothInclusion {A B : Opens M} (h : A ≤ B) :
    (smoothSingularSubcomplex I A : SSet) ⟶ TopCat.toSSet.obj (TopCat.of B) :=
  smoothSingularSubcomplexMap (I := I) (J := I) (Opens.inclusion h) (contMDiff_inclusion h) ≫
    (smoothSingularSubcomplex I B).ι

private instance {A B : Opens M} (h : A ≤ B) : Mono (singularInclusion h) :=
  have : Mono (TopCat.ofHom (⟨Opens.inclusion h,
      continuous_inclusion (SetLike.coe_subset_coe.2 h)⟩ : C(A, B))) :=
    (TopCat.mono_iff_injective _).2 (Set.inclusion_injective (SetLike.coe_subset_coe.2 h))
  Functor.map_mono _ _

private theorem smoothInclusion_eq {A B : Opens M} (h : A ≤ B) :
    smoothInclusion I h = (smoothSingularSubcomplex I A).ι ≫ singularInclusion h :=
  smoothSingularSubcomplexMap_ι _

private instance {A B : Opens M} (h : A ≤ B) : Mono (smoothInclusion I h) := by
  rw [smoothInclusion_eq]
  infer_instance

private theorem range_smoothInclusion_le {A B : Opens M} (h : A ≤ B) :
    SSet.Subcomplex.range (smoothInclusion I h) ≤ SSet.Subcomplex.range (singularInclusion h) := by
  rw [smoothInclusion_eq]
  exact Subfunctor.range_comp_le _ _

variable (I) in
/-- For open sets `A ≤ B`, smooth singular chains include into singular chains by a
quasi-isomorphism on `A` exactly when they do so for the simplices of `A` read in `B`. -/
private theorem quasiIso_chainComplexMap_ι_iff {A B : Opens M} (h : A ≤ B) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I A).ι R) ↔
      QuasiIso (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (range_smoothInclusion_le (I := I) h)) R) := by
  -- Reading simplices of `A` in `B` identifies both chain complexes of `A` with those of the
  -- ranges, compatibly with the inclusions.
  have hsq : SSet.Subcomplex.toRange (smoothInclusion I h) ≫
        SSet.Subcomplex.homOfLE (range_smoothInclusion_le (I := I) h) =
      (smoothSingularSubcomplex I A).ι ≫ SSet.Subcomplex.toRange (singularInclusion h) := by
    rw [← cancel_mono (SSet.Subcomplex.range (singularInclusion h)).ι, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, Category.assoc,
      SSet.Subcomplex.toRange_ι, smoothInclusion_eq]
  rw [← quasiIso_iff_comp_right _
      (SSet.chainComplexMap (SSet.Subcomplex.toRange (singularInclusion h)) R),
    ← Functor.map_comp, ← hsq, Functor.map_comp, quasiIso_iff_comp_left]

/-- The cover of `U ∪ V` by its intersections with `U` and with `V`. -/
private abbrev supCover (U V : Opens M) : Fin 2 → Set ↥(U ⊔ V) :=
  ![Subtype.val ⁻¹' (U : Set M), Subtype.val ⁻¹' (V : Set M)]

private theorem isOpen_supCover (U V : Opens M) : ∀ i, IsOpen (supCover U V i) :=
  Fin.forall_fin_two.2
    ⟨U.isOpen.preimage continuous_subtype_val, V.isOpen.preimage continuous_subtype_val⟩

private theorem iUnion_supCover (U V : Opens M) : ⋃ i, supCover U V i = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
  rcases (Opens.coe_sup U V ▸ x.2 : (x : M) ∈ (U : Set M) ∪ V) with hx | hx
  exacts [⟨0, hx⟩, ⟨1, hx⟩]

/-- The singular simplices of `U ∩ V`, `U` and `V`, read in `U ∪ V`, form a bicartesian square
whose union is the subcomplex of simplices lying in `U` or in `V`. -/
private theorem bicartSq_range_singularInclusion (U V : Opens M) :
    SSet.Subcomplex.BicartSq (SSet.Subcomplex.range (singularInclusion (inf_le_sup (a := U))))
      (SSet.Subcomplex.range (singularInclusion (le_sup_left (b := V))))
      (SSet.Subcomplex.range (singularInclusion (le_sup_right (a := U))))
      ((TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V)) where
  sup_eq := by
    ext n σ
    -- The supremum of subcomplexes is computed pointwise.
    change σ ∈ (SSet.Subcomplex.range _).obj n ∨ σ ∈ (SSet.Subcomplex.range _).obj n ↔ _
    rw [TopCat.mem_range_toSSet_map_inclusion_iff, TopCat.mem_range_toSSet_map_inclusion_iff,
      TopCat.mem_smallSingularSubcomplex_iff]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  inf_eq := by
    ext n σ
    -- The infimum of subcomplexes is computed pointwise.
    change σ ∈ (SSet.Subcomplex.range _).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n ↔ _
    rw [TopCat.mem_range_toSSet_map_inclusion_iff, TopCat.mem_range_toSSet_map_inclusion_iff,
      TopCat.mem_range_toSSet_map_inclusion_iff, ← Set.subset_inter_iff, ← Set.preimage_inter,
      Opens.coe_inf]

variable (I) in
/-- The smooth singular simplices of `U ∩ V`, `U` and `V`, read in `U ∪ V`, form a bicartesian
square whose union is the subcomplex of smooth simplices lying in `U` or in `V`. -/
private theorem bicartSq_range_smoothInclusion (U V : Opens M) :
    SSet.Subcomplex.BicartSq (SSet.Subcomplex.range (smoothInclusion I (inf_le_sup (a := U))))
      (SSet.Subcomplex.range (smoothInclusion I (le_sup_left (b := V))))
      (SSet.Subcomplex.range (smoothInclusion I (le_sup_right (a := U))))
      (smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
        (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V)) where
  sup_eq := by
    rw [range_smoothSingularSubcomplexMap_inclusion_comp_ι,
      range_smoothSingularSubcomplexMap_inclusion_comp_ι,
      ← (bicartSq_range_singularInclusion U V).sup_eq]
    ext n σ
    -- Infima and suprema of subcomplexes are computed pointwise.
    change (σ ∈ (smoothSingularSubcomplex I _).obj n ∧ _) ∨
        (σ ∈ (smoothSingularSubcomplex I _).obj n ∧ _) ↔
      σ ∈ (smoothSingularSubcomplex I _).obj n ∧ (_ ∨ _)
    exact and_or_left.symm
  inf_eq := by
    rw [range_smoothSingularSubcomplexMap_inclusion_comp_ι,
      range_smoothSingularSubcomplexMap_inclusion_comp_ι,
      range_smoothSingularSubcomplexMap_inclusion_comp_ι,
      ← (bicartSq_range_singularInclusion U V).inf_eq]
    exact (inf_inf_distrib_left _ _ _).symm

variable (I) in
/-- **The Mayer–Vietoris comparison.** If smooth singular chains include into singular chains by a
quasi-isomorphism on `U`, on `V` and on `U ∩ V`, then the smooth singular simplices of `U ∪ V`
lying in `U` or in `V` include into all singular simplices lying in `U` or in `V` by a
quasi-isomorphism on chains. -/
private theorem quasiIso_chainComplexMap_homOfLE_smoothSingularSubcomplex_inf (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right :
      smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
          (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V) ≤
        (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V))) R) := by
  have sqT := bicartSq_range_singularInclusion U V
  have sqS := bicartSq_range_smoothInclusion I U V
  -- The inclusion of the smooth square into the singular one is a map of Mayer–Vietoris short
  -- exact sequences, a quasi-isomorphism on the first two terms, hence on the third.
  let φ₁ := SSet.Subcomplex.homOfLE
    (range_smoothInclusion_le (I := I) (inf_le_sup (a := U) (b := V)))
  let φ₂ := SSet.Subcomplex.homOfLE
    (range_smoothInclusion_le (I := I) (le_sup_left (a := U) (b := V)))
  let φ₃ := SSet.Subcomplex.homOfLE
    (range_smoothInclusion_le (I := I) (le_sup_right (a := U) (b := V)))
  let φ₄ := SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
    (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V) ≤ _)
  have hτ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (SSet.mayerVietorisShortComplexMap R sqS.isPushout sqT.isPushout
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) (φ₄ := φ₄) rfl rfl rfl rfl)
    (SSet.shortExact_mayerVietorisShortComplex R sqS.isPushout)
    (SSet.shortExact_mayerVietorisShortComplex R sqT.isPushout)
  -- Spell out the three components of the map of short complexes.
  rw [SSet.mayerVietorisShortComplexMap_τ₁ R sqS.isPushout sqT.isPushout
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) (φ₄ := φ₄) rfl rfl rfl rfl,
    SSet.mayerVietorisShortComplexMap_τ₂ R sqS.isPushout sqT.isPushout
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) (φ₄ := φ₄) rfl rfl rfl rfl,
    SSet.mayerVietorisShortComplexMap_τ₃ R sqS.isPushout sqT.isPushout
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) (φ₄ := φ₄) rfl rfl rfl rfl] at hτ₃
  have hφ₂ : QuasiIso (SSet.chainComplexMap φ₂ R) := (quasiIso_chainComplexMap_ι_iff I R _).1 hU
  have hφ₃ : QuasiIso (SSet.chainComplexMap φ₃ R) := (quasiIso_chainComplexMap_ι_iff I R _).1 hV
  -- Instance search does not find these quasi-isomorphisms for the biproduct of chain complexes
  -- in the Mayer–Vietoris short complex, so they are passed explicitly.
  exact hτ₃ ((quasiIso_chainComplexMap_ι_iff I R _).1 hUV)
    (@HomologicalComplex.quasiIso_biprod_map _ _ _ _ _ _ _ _ _ _ _ _ _ hφ₂ hφ₃)

variable (I) in
/-- **The Mayer–Vietoris step of the smoothing theorem.** Let `U` and `V` be open subsets of a
manifold `M`. If the inclusion of smooth singular chains into singular chains with coefficients in
`R` is a quasi-isomorphism on `U`, on `V` and on `U ∩ V`, then it is one on `U ∪ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  let D := (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex (supCover U V)
  have hSD := quasiIso_chainComplexMap_homOfLE_smoothSingularSubcomplex_inf I R U V hU hV hUV
  -- By the small-chain theorem, the chains of the simplices lying in `U` or in `V` compute the
  -- homology of `U ∪ V`, on the singular side and on the smooth side.
  have hD : QuasiIso (SSet.chainComplexMap D.ι R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplex_ι (X := TopCat.of ↥(U ⊔ V)) (C := C) R
      (supCover U V) (isOpen_supCover U V) (iUnion_supCover U V)
  have hS := quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R S (supCover U V)
    (isOpen_supCover U V) (iUnion_supCover U V)
  have hcomp : SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ D ≤ S)) R ≫
        SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : S ⊓ D ≤ D)) R ≫
        SSet.chainComplexMap D.ι R := by
    rw [← Functor.map_comp, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.homOfLE_ι]
  have : QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ D ≤ S)) R ≫
      SSet.chainComplexMap S.ι R) := by
    rw [hcomp]
    infer_instance
  exact quasiIso_of_comp_left
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ D ≤ S)) R) _

end TauCeti
