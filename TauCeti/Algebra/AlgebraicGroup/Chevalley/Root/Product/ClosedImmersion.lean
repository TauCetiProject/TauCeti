/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product.Parameters
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Closed immersions from ordered root products

For any Chevalley datum and any duplicate-free list of roots positive for a common rational
degree, ordered multiplication of the root morphisms is a closed immersion over `ℤ`.
The order is arbitrary. In particular this applies to lists of positive roots and lists
of negative roots.

The polynomial parameter presentation identifies the pullbacks of ambient matrix entries
with the entries of the universal ordered product. Integral coordinate recovery shows that
these entries generate the parameter ring, so the pullback from `GL` is surjective.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The matrix of the ordered root product at the universal polynomial parameters. -/
def universalRootProduct (l : List (Fin t.numRoots)) :
    Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ) :=
  (l.map fun γ ↦
    ((D.rootSubgroupPoints γ _ (Multiplicative.ofAdd (t.universalRootParameter l γ)) :
      Matrix.GeneralLinearGroup (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) :
        Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ))).prod

/-- The universal matrix is the product of root matrices at the universal parameters. -/
theorem universalRootProduct_def (l : List (Fin t.numRoots)) :
    D.universalRootProduct l = (l.map fun γ ↦
      ((D.rootSubgroupPoints γ _ (Multiplicative.ofAdd (t.universalRootParameter l γ)) :
        Matrix.GeneralLinearGroup (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) :
          Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ))).prod :=
  (rfl)

/-- The entries of the universal ordered root product generate the entire polynomial
parameter ring over `ℤ`. There is one variable for each root occurring in the list. -/
theorem adjoin_universalRootProduct_eq_top
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ)) :
    Algebra.adjoin ℤ (Set.range fun rs : Fin D.dim × Fin D.dim ↦
      D.universalRootProduct l rs.1 rs.2) = ⊤ := by
  classical
  have hmem := D.parameters_mem_of_list_prod_rootSubgroupPoints_mem hl degree hdegree
    (Algebra.adjoin ℤ (Set.range fun rs : Fin D.dim × Fin D.dim ↦
      D.universalRootProduct l rs.1 rs.2)) (t.universalRootParameter l)
    (fun r s ↦ by
      rw [← universalRootProduct_def]
      exact Algebra.subset_adjoin (Set.mem_range_self (r, s)))
  apply top_unique
  rw [← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨⟨γ, hγ⟩, rfl⟩
  rw [← t.universalRootParameter_of_mem l hγ]
  exact hmem γ hγ

/-- The pullback of functions on `GL` along the universal ordered root product. -/
def rootProductCoordinateMap (l : List (Fin t.numRoots)) :
    GeneralLinear.coordinateHopfAlgebra ℤ D.dim →ₐ[ℤ] MvPolynomial {γ // γ ∈ l} ℤ :=
  ((GeneralLinear.groupSchemePointMulEquiv D.dim _).symm
    (t.rootProductParametersPoint l ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom)).ofConv

/-- Pulling back a generic matrix entry gives that entry of the universal root product. -/
theorem rootProductCoordinateMap_genericMatrix (l : List (Fin t.numRoots))
    (r s : Fin D.dim) :
    D.rootProductCoordinateMap l (GeneralLinear.genericMatrix ℤ D.dim r s) =
      D.universalRootProduct l r s := by
  classical
  have hp := congrArg (fun g : Matrix.GeneralLinearGroup (Fin D.dim)
      (MvPolynomial {γ // γ ∈ l} ℤ) ↦
        (g : Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) r s)
    (D.schemePointsMulEquiv_rootProduct l _ (t.rootProductParametersPoint l))
  rw [GeneralLinear.schemePointsMulEquiv_apply, ← GeneralLinear.genericMatrix_apply] at hp
  rw [rootProductCoordinateMap]
  refine hp.trans ?_
  have hval := map_list_prod (Units.coeHom
    (Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)))
    (l.attach.map fun γ ↦ (D.rootSubgroupPoints γ.val _
      (AdditiveGroup.schemePointsMulEquiv _
        (t.rootProductParametersPoint l ≫ Pi.π _ γ)) :
          Matrix.GeneralLinearGroup (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)))
  rw [Units.coeHom_apply] at hval
  refine (congrArg (fun m ↦ m r s) hval).trans ?_
  simp only [List.map_map, Function.comp_def, t.rootProductParametersPoint_coordinate]
  rw [universalRootProduct_def, ← List.attach_map_val (l := l)]
  apply congrArg (fun xs : List
    (Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) ↦ xs.prod r s)
  apply List.map_congr_left
  intro γ _
  simp only [t.universalRootParameter_of_mem l γ.property, Units.coeHom_apply]

/-- The ambient matrix-coordinate pullback for a positive-degree root list is surjective. -/
theorem rootProductCoordinateMap_surjective
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ)) :
    Function.Surjective (D.rootProductCoordinateMap l) := by
  apply (AlgHom.range_eq_top _).mp
  apply top_unique
  rw [← D.adjoin_universalRootProduct_eq_top hl degree hdegree]
  apply Algebra.adjoin_le
  rintro _ ⟨⟨r, s⟩, rfl⟩
  exact ⟨GeneralLinear.genericMatrix ℤ D.dim r s,
    D.rootProductCoordinateMap_genericMatrix l r s⟩

/-- The spectrum map of the matrix-coordinate pullback is the universal parameter point
followed by ordered multiplication and the embedding into `GL`. -/
theorem spec_map_rootProductCoordinateMap (l : List (Fin t.numRoots)) :
    Spec.map (CommRingCat.ofHom (D.rootProductCoordinateMap l).toRingHom) ≫
      eqToHom (GeneralLinear.groupScheme_X_left ℤ D.dim).symm =
      (t.rootProductParametersPoint l ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom).left := by
  let p := t.rootProductParametersPoint l ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom
  have h := GeneralLinear.groupSchemePointMulEquiv_apply_left D.dim
    (MvPolynomial {γ // γ ∈ l} ℤ) ((GeneralLinear.groupSchemePointMulEquiv D.dim _).symm p)
  have he := congrArg (fun z ↦ z.left)
    ((GeneralLinear.groupSchemePointMulEquiv D.dim _).apply_symm_apply p)
  simpa only [rootProductCoordinateMap] using! h.symm.trans he

/-- Ordered multiplication of distinct roots positive for a common rational degree is a
closed immersion into the group scheme of the Chevalley datum. -/
theorem isClosedImmersion_rootProduct_of_degree
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ)) :
    IsClosedImmersion (D.rootProduct l).left := by
  have hs : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (D.rootProductCoordinateMap l).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (D.rootProductCoordinateMap l).toRingHom)
      (D.rootProductCoordinateMap_surjective hl degree hdegree)
  have hp : IsClosedImmersion
      (t.rootProductParametersPoint l ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom).left := by
    rw [← D.spec_map_rootProductCoordinateMap]
    exact @IsClosedImmersion.comp _ _ _ _ _ hs inferInstance
  have hGL : IsClosedImmersion ((D.rootProduct l).left ≫ D.groupSchemeι.hom.hom.left) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (t.rootProductParametersPoint l).left]
    exact hp
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (D.rootProduct l).left D.groupSchemeι.hom.hom.left

/-- Ordered multiplication of distinct positive roots is a closed immersion over `ℤ`. -/
theorem isClosedImmersion_rootProduct_of_posRoots
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    IsClosedImmersion (D.rootProduct l).left :=
  D.isClosedImmersion_rootProduct_of_degree hl (t.weightDegree ht)
    fun γ hγ ↦ t.weightDegree_root_pos ht (hpos γ hγ)

/-- Ordered multiplication of distinct negative roots is a closed immersion over `ℤ`. -/
theorem isClosedImmersion_rootProduct_of_negRoots
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hneg : ∀ γ ∈ l, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    IsClosedImmersion (D.rootProduct l).left :=
  D.isClosedImmersion_rootProduct_of_degree hl (-(t.weightDegree ht))
    fun γ hγ ↦ neg_pos.mpr (t.weightDegree_root_neg ht (hneg γ hγ))

end

end TauCeti.DynkinType.ChevalleyDatum
