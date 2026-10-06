/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Induction.DimensionShift
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# Dimension shifting in Tate cohomology

For a finite group `G`, the connecting maps of the canonical sequences

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0` and
`0 ⟶ dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A ⟶ 0`

are isomorphisms in every integer Tate degree. The same is true after restriction to any finite
subgroup of `G`, even when `G` itself is infinite. These subgroupwise shifts allow a vanishing
condition in consecutive degrees to be moved to other degrees simultaneously on all subgroups,
as required in Tate's cohomological triviality and cup-product criteria.

The two sequences stay short exact after tensoring on the left with any representation `M`, and
the middle terms `M ⊗ Coind_⊥^G A` and `M ⊗ Ind_⊥^G A` still have vanishing Tate cohomology, so
their connecting maps are isomorphisms as well (`tensorDimensionShiftUpIso`,
`tensorDimensionShiftDownIso`). These tensored shifts take the target degree as a parameter, so
that a construction proceeding by recursion on the degree, such as the cup product in all
bidegrees, needs no transport along equalities of degrees between its recursive steps; the cup
product transports its result once, at the end, to the requested target degree.

The composites of two consecutive upward shifts, on the group (`dimensionShiftUpTwoIso`, from
degree `0` to degree `2`) and on a finite subgroup (`dimensionShiftUpTwoResIso`), present a
degree-two class as the double shift of a degree-zero class.

Each isomorphism below has Mathlib's connecting homomorphism `TateCohomology.δ` as its forward
map. Thus its naturality in a morphism of the short exact sequences is the existing theorem
`TateCohomology.δ_naturality`; no choices of abstract isomorphisms enter the construction.
The naturality statements here apply both to a shift and to its tensor with a fixed
representation, so they transport cup products along coefficient maps.

The unrestricted constructions adapt `δUpIsoTate` and `δDownIsoTate` from
`ClassFieldTheory/Cohomology/Functors/UpDown.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`. The restricted constructions use the vanishing of
restricted induced and coinduced representations proved in `TateCohomology.Coinduced`.
All four reuse Mathlib's `CategoryTheory.ShortComplex.ShortExact.δIso`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §3 (dimension shifting and Theorem 3.10).
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

section Fintype

variable [Fintype G] (n : ℤ)

-- Use the public presentations of the short exact sequences so the endpoints of the connecting
-- maps are visible without unfolding the opaque `dimensionShiftUpSES` and `dimensionShiftDownSES`.

/-- The upward dimension-shifting sequence identifies Tate cohomology of `dimensionShiftUp A`
in degree `n` with Tate cohomology of `A` in degree `n + 1`. -/
def dimensionShiftUpIso :
    tateCohomology (dimensionShiftUp A) n ≅ tateCohomology A (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A))
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A)).δIso
      n (n + 1) rfl (isZero_coindBot A.V n) (isZero_coindBot A.V (n + 1))

/-- The upward dimension shift is the connecting map of the coinduced short exact sequence. -/
@[simp]
theorem dimensionShiftUpIso_hom :
    (dimensionShiftUpIso A n).hom =
      _root_.TateCohomology.δ
        (S := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
          (coindBotUnit_comp_dimensionShiftUpπ A))
        (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A) n := (rfl)

/-- The downward dimension-shifting sequence identifies Tate cohomology of `A` in degree `n`
with Tate cohomology of `dimensionShiftDown A` in degree `n + 1`. -/
def dimensionShiftDownIso :
    tateCohomology A n ≅ tateCohomology (dimensionShiftDown A) (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
      (dimensionShiftDownι_comp_indBotCounit A))
    (by simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact A)).δIso
      n (n + 1) rfl (isZero_indBot A.V n) (isZero_indBot A.V (n + 1))

/-- The downward dimension shift is the connecting map of the induced short exact sequence. -/
@[simp]
theorem dimensionShiftDownIso_hom :
    (dimensionShiftDownIso A n).hom =
      _root_.TateCohomology.δ
        (S := ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
          (dimensionShiftDownι_comp_indBotCounit A))
        (by simpa only [dimensionShiftDownSES_def] using
          dimensionShiftDownSES_shortExact A) n := (rfl)

/-- Two upward dimension shifts identify degree-zero Tate cohomology of the twice-shifted
representation with degree-two Tate cohomology of the representation itself. -/
def dimensionShiftUpTwoIso :
    tateCohomology (dimensionShiftUp (dimensionShiftUp A)) 0 ≅ tateCohomology A 2 :=
  dimensionShiftUpIso (dimensionShiftUp A) 0 ≪≫ dimensionShiftUpIso A 1

/-- The double shift is the composite of the two upward dimension shifts. -/
@[simp]
theorem dimensionShiftUpTwoIso_hom :
    (dimensionShiftUpTwoIso A).hom =
      (dimensionShiftUpIso (dimensionShiftUp A) 0).hom ≫ (dimensionShiftUpIso A 1).hom := by
  rw [dimensionShiftUpTwoIso, Iso.trans_hom]

variable {A} in
/-- Upward dimension shifting commutes with a morphism of coefficient representations. -/
@[reassoc]
theorem dimensionShiftUpIso_hom_naturality {B : Rep k G} (f : A ⟶ B) :
    (tateCohomologyFunctor n).map (dimensionShiftUpMap f) ≫
        (dimensionShiftUpIso B n).hom =
      (dimensionShiftUpIso A n).hom ≫ (tateCohomologyFunctor (n + 1)).map f := by
  let φ := dimensionShiftUpSESMap f
  rw [dimensionShiftUpIso_hom, dimensionShiftUpIso_hom]
  simpa only [φ, dimensionShiftUpSESMap_τ₁, dimensionShiftUpSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A)
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact B) φ n).symm

variable {A} in
/-- The inverse upward shift commutes with a coefficient morphism. -/
@[reassoc]
theorem dimensionShiftUpIso_inv_naturality {B : Rep k G} (f : A ⟶ B) :
    (tateCohomologyFunctor (n + 1)).map f ≫ (dimensionShiftUpIso B n).inv =
      (dimensionShiftUpIso A n).inv ≫
        (tateCohomologyFunctor n).map (dimensionShiftUpMap f) := by
  rw [Iso.comp_inv_eq, Category.assoc, dimensionShiftUpIso_hom_naturality,
    Iso.inv_hom_id_assoc]

variable {A} in
/-- Downward dimension shifting commutes with a morphism of coefficient representations. -/
@[reassoc]
theorem dimensionShiftDownIso_hom_naturality {B : Rep k G} (f : A ⟶ B) :
    (tateCohomologyFunctor n).map f ≫ (dimensionShiftDownIso B n).hom =
      (dimensionShiftDownIso A n).hom ≫
        (tateCohomologyFunctor (n + 1)).map (dimensionShiftDownMap f) := by
  let φ := dimensionShiftDownSESMap f
  rw [dimensionShiftDownIso_hom, dimensionShiftDownIso_hom]
  simpa only [φ, dimensionShiftDownSESMap_τ₁, dimensionShiftDownSESMap_τ₃] using
    (_root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact A)
    (by simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact B) φ n).symm

variable {A} in
/-- The inverse downward shift commutes with a coefficient morphism. -/
@[reassoc]
theorem dimensionShiftDownIso_inv_naturality {B : Rep k G} (f : A ⟶ B) :
    (tateCohomologyFunctor (n + 1)).map (dimensionShiftDownMap f) ≫
        (dimensionShiftDownIso B n).inv =
      (dimensionShiftDownIso A n).inv ≫ (tateCohomologyFunctor n).map f := by
  rw [Iso.comp_inv_eq, Category.assoc, dimensionShiftDownIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- Vanishing in degree `n` of an upward shift is vanishing in degree `n + 1` of the original
module. -/
@[simp]
theorem isZero_dimensionShiftUp_iff :
    IsZero (tateCohomology (dimensionShiftUp A) n) ↔
      IsZero (tateCohomology A (n + 1)) :=
  (dimensionShiftUpIso A n).isZero_iff

/-- Vanishing in degree `n + 1` of a downward shift is vanishing in degree `n` of the original
module. -/
@[simp]
theorem isZero_dimensionShiftDown_iff :
    IsZero (tateCohomology (dimensionShiftDown A) (n + 1)) ↔
      IsZero (tateCohomology A n) :=
  (dimensionShiftDownIso A n).isZero_iff.symm

section Tensor

variable (M : Rep k G)

/-- Tensoring the upward dimension-shifting sequence of `A` on the left with `M` identifies Tate
cohomology of `M ⊗ dimensionShiftUp A` in degree `i` with Tate cohomology of `M ⊗ A` in degree
`j = i + 1`. -/
def tensorDimensionShiftUpIso (i j : ℤ) (hij : i + 1 = j) :
    tateCohomology (M ⊗ dimensionShiftUp A) i ≅ tateCohomology (M ⊗ A) j :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)).map (tensorLeft M))
    (by simpa only [dimensionShiftUpSES_def] using
      dimensionShiftUpSES_tensorLeft_shortExact A M)).δIso i j hij
        (isZero_tensor_coindBot A.V M i) (isZero_tensor_coindBot A.V M j)

/-- The tensored upward dimension shift is the connecting map of the tensored coinduced short
exact sequence. -/
@[simp]
theorem tensorDimensionShiftUpIso_hom (i j : ℤ) (hij : i + 1 = j) :
    (tensorDimensionShiftUpIso A M i j hij).hom =
      (_root_.TateCohomology.map_tateComplexFunctor_shortExact
        (S := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
          (coindBotUnit_comp_dimensionShiftUpπ A)).map (tensorLeft M))
        (by simpa only [dimensionShiftUpSES_def] using
          dimensionShiftUpSES_tensorLeft_shortExact A M)).δ i j hij := (rfl)

/-- Tensoring the downward dimension-shifting sequence of `A` on the left with `M` identifies Tate
cohomology of `M ⊗ A` in degree `i` with Tate cohomology of `M ⊗ dimensionShiftDown A` in degree
`j = i + 1`. -/
def tensorDimensionShiftDownIso (i j : ℤ) (hij : i + 1 = j) :
    tateCohomology (M ⊗ A) i ≅ tateCohomology (M ⊗ dimensionShiftDown A) j :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := (ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
      (dimensionShiftDownι_comp_indBotCounit A)).map (tensorLeft M))
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_tensorLeft_shortExact A M)).δIso i j hij
        (isZero_tensor_indBot A.V M i) (isZero_tensor_indBot A.V M j)

/-- The tensored downward dimension shift is the connecting map of the tensored induced short
exact sequence. -/
@[simp]
theorem tensorDimensionShiftDownIso_hom (i j : ℤ) (hij : i + 1 = j) :
    (tensorDimensionShiftDownIso A M i j hij).hom =
      (_root_.TateCohomology.map_tateComplexFunctor_shortExact
        (S := (ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
          (dimensionShiftDownι_comp_indBotCounit A)).map (tensorLeft M))
        (by simpa only [dimensionShiftDownSES_def] using
          dimensionShiftDownSES_tensorLeft_shortExact A M)).δ i j hij := (rfl)

variable {A} in
/-- The tensored upward dimension shift is natural in its shifting representation. -/
@[reassoc]
theorem tensorDimensionShiftUpIso_hom_naturality_right {B : Rep k G} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (M ◁ dimensionShiftUpMap f) ≫
        (tensorDimensionShiftUpIso B M i j hij).hom =
      (tensorDimensionShiftUpIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map (M ◁ f) := by
  let φ := dimensionShiftUpSESMap f
  have hφ₁ : ((tensorLeft M).mapShortComplex.map φ).τ₁ = M ◁ f := by
    rw [Functor.mapShortComplex_map_τ₁]
    simp [φ, dimensionShiftUpSESMap_τ₁, tensorLeft, curriedTensor]
  have hφ₃ : ((tensorLeft M).mapShortComplex.map φ).τ₃ =
      M ◁ dimensionShiftUpMap f := by
    rw [Functor.mapShortComplex_map_τ₃]
    simp [φ, dimensionShiftUpSESMap_τ₃, tensorLeft, curriedTensor]
  subst j
  rw [tensorDimensionShiftUpIso_hom, tensorDimensionShiftUpIso_hom]
  simpa only [hφ₁, hφ₃] using
    (_root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftUpSES_def, Functor.mapShortComplex_obj] using
      dimensionShiftUpSES_tensorLeft_shortExact A M)
    (by simpa only [dimensionShiftUpSES_def, Functor.mapShortComplex_obj] using
      dimensionShiftUpSES_tensorLeft_shortExact B M)
    ((tensorLeft M).mapShortComplex.map φ) i).symm

variable {A} in
/-- The inverse tensored upward shift is natural in its shifting representation. -/
@[reassoc]
theorem tensorDimensionShiftUpIso_inv_naturality_right {B : Rep k G} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (M ◁ f) ≫
        (tensorDimensionShiftUpIso B M i j hij).inv =
      (tensorDimensionShiftUpIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map (M ◁ dimensionShiftUpMap f) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    tensorDimensionShiftUpIso_hom_naturality_right, Iso.inv_hom_id_assoc]

variable {A} in
/-- The tensored downward dimension shift is natural in its shifting representation. -/
@[reassoc]
theorem tensorDimensionShiftDownIso_hom_naturality_right {B : Rep k G} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (M ◁ f) ≫
        (tensorDimensionShiftDownIso B M i j hij).hom =
      (tensorDimensionShiftDownIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map (M ◁ dimensionShiftDownMap f) := by
  let φ := dimensionShiftDownSESMap f
  have hφ₁ : ((tensorLeft M).mapShortComplex.map φ).τ₁ =
      M ◁ dimensionShiftDownMap f := by
    rw [Functor.mapShortComplex_map_τ₁]
    simp [φ, dimensionShiftDownSESMap_τ₁, tensorLeft, curriedTensor]
  have hφ₃ : ((tensorLeft M).mapShortComplex.map φ).τ₃ = M ◁ f := by
    rw [Functor.mapShortComplex_map_τ₃]
    simp [φ, dimensionShiftDownSESMap_τ₃, tensorLeft, curriedTensor]
  subst j
  rw [tensorDimensionShiftDownIso_hom, tensorDimensionShiftDownIso_hom]
  simpa only [hφ₁, hφ₃] using
    (_root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftDownSES_def, Functor.mapShortComplex_obj] using
      dimensionShiftDownSES_tensorLeft_shortExact A M)
    (by simpa only [dimensionShiftDownSES_def, Functor.mapShortComplex_obj] using
      dimensionShiftDownSES_tensorLeft_shortExact B M)
    ((tensorLeft M).mapShortComplex.map φ) i).symm

variable {A} in
/-- The inverse tensored downward shift is natural in its shifting representation. -/
@[reassoc]
theorem tensorDimensionShiftDownIso_inv_naturality_right {B : Rep k G} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (M ◁ dimensionShiftDownMap f) ≫
        (tensorDimensionShiftDownIso B M i j hij).inv =
      (tensorDimensionShiftDownIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map (M ◁ f) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    tensorDimensionShiftDownIso_hom_naturality_right, Iso.inv_hom_id_assoc]

variable {M} in
/-- The tensored upward dimension shift is natural in the tensoring representation. -/
@[reassoc]
theorem tensorDimensionShiftUpIso_hom_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (f ▷ dimensionShiftUp A) ≫
        (tensorDimensionShiftUpIso A M' i j hij).hom =
      (tensorDimensionShiftUpIso A M i j hij).hom ≫ (tateCohomologyFunctor j).map (f ▷ A) := by
  rw [tensorDimensionShiftUpIso_hom, tensorDimensionShiftUpIso_hom]
  exact (HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor k G).mapShortComplex.map
      ((ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A)).mapNatTrans ((curriedTensor (Rep k G)).map f)))
    _ _ i j hij).symm

variable {M} in
/-- The inverse tensored upward shift is natural in the tensoring representation. -/
@[reassoc]
theorem tensorDimensionShiftUpIso_inv_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (f ▷ A) ≫
        (tensorDimensionShiftUpIso A M' i j hij).inv =
      (tensorDimensionShiftUpIso A M i j hij).inv ≫
        (tateCohomologyFunctor i).map (f ▷ dimensionShiftUp A) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftUpIso_hom_naturality_left,
    Iso.inv_hom_id_assoc]

variable {M} in
/-- The tensored downward dimension shift is natural in the tensoring representation. -/
@[reassoc]
theorem tensorDimensionShiftDownIso_hom_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor i).map (f ▷ A) ≫ (tensorDimensionShiftDownIso A M' i j hij).hom =
      (tensorDimensionShiftDownIso A M i j hij).hom ≫
        (tateCohomologyFunctor j).map (f ▷ dimensionShiftDown A) := by
  rw [tensorDimensionShiftDownIso_hom, tensorDimensionShiftDownIso_hom]
  exact (HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor k G).mapShortComplex.map
      ((ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
        (dimensionShiftDownι_comp_indBotCounit A)).mapNatTrans ((curriedTensor (Rep k G)).map f)))
    _ _ i j hij).symm

variable {M} in
/-- The inverse of the tensored downward dimension shift is natural in the tensoring
representation. -/
@[reassoc]
theorem tensorDimensionShiftDownIso_inv_naturality_left {M' : Rep k G} (f : M ⟶ M') (i j : ℤ)
    (hij : i + 1 = j) :
    (tateCohomologyFunctor j).map (f ▷ dimensionShiftDown A) ≫
        (tensorDimensionShiftDownIso A M' i j hij).inv =
      (tensorDimensionShiftDownIso A M i j hij).inv ≫ (tateCohomologyFunctor i).map (f ▷ A) := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorDimensionShiftDownIso_hom_naturality_left,
    Iso.inv_hom_id_assoc]

end Tensor

end Fintype

section Restriction

variable (S : Subgroup G) [Fintype S] (n : ℤ)

/-- Upward dimension shifting after restriction to a finite subgroup. The shift is constructed
over `G`, so the same coefficient representation works for every finite subgroup. -/
def dimensionShiftUpResIso :
    tateCohomology (res S.subtype (dimensionShiftUp A)) n ≅
      tateCohomology (res S.subtype A) (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)).map (resFunctor S.subtype))
    (by simpa only [dimensionShiftUpSES_def] using
      dimensionShiftUpSES_res_shortExact A S.subtype)).δIso n (n + 1) rfl
        (isZero_res_coindBot S A.V n) (isZero_res_coindBot S A.V (n + 1))

/-- Restricted upward dimension shifting is the connecting map of the restricted sequence. -/
@[simp]
theorem dimensionShiftUpResIso_hom :
    (dimensionShiftUpResIso A S n).hom =
      _root_.TateCohomology.δ
        (S := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
          (coindBotUnit_comp_dimensionShiftUpπ A)).map (resFunctor S.subtype))
        (by simpa only [dimensionShiftUpSES_def] using
          dimensionShiftUpSES_res_shortExact A S.subtype) n := (rfl)

/-- Downward dimension shifting after restriction to a finite subgroup. The shift is constructed
over `G`, so the same coefficient representation works for every finite subgroup. -/
def dimensionShiftDownResIso :
    tateCohomology (res S.subtype A) n ≅
      tateCohomology (res S.subtype (dimensionShiftDown A)) (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (S := (ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
      (dimensionShiftDownι_comp_indBotCounit A)).map (resFunctor S.subtype))
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_res_shortExact A S.subtype)).δIso n (n + 1) rfl
        (isZero_res_indBot S A.V n) (isZero_res_indBot S A.V (n + 1))

/-- Restricted downward dimension shifting is the connecting map of the restricted sequence. -/
@[simp]
theorem dimensionShiftDownResIso_hom :
    (dimensionShiftDownResIso A S n).hom =
      _root_.TateCohomology.δ
        (S := (ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
          (dimensionShiftDownι_comp_indBotCounit A)).map (resFunctor S.subtype))
        (by simpa only [dimensionShiftDownSES_def] using
          dimensionShiftDownSES_res_shortExact A S.subtype) n := (rfl)

/-- Two upward dimension shifts after restriction to a finite subgroup identify Tate cohomology
of the twice-shifted representation in degree `n` with Tate cohomology of the representation
itself in degree `n + 1 + 1`. -/
def dimensionShiftUpTwoResIso :
    tateCohomology (res S.subtype (dimensionShiftUp (dimensionShiftUp A))) n ≅
      tateCohomology (res S.subtype A) (n + 1 + 1) :=
  dimensionShiftUpResIso (dimensionShiftUp A) S n ≪≫ dimensionShiftUpResIso A S (n + 1)

/-- The restricted double shift is the composite of the two restricted upward dimension shifts. -/
@[simp]
theorem dimensionShiftUpTwoResIso_hom :
    (dimensionShiftUpTwoResIso A S n).hom =
      (dimensionShiftUpResIso (dimensionShiftUp A) S n).hom ≫
        (dimensionShiftUpResIso A S (n + 1)).hom := by
  rw [dimensionShiftUpTwoResIso, Iso.trans_hom]

/-- Vanishing in degree `n` of an upward shift is vanishing in degree `n + 1` of the original
module, also on a finite subgroup. -/
@[simp]
theorem isZero_res_dimensionShiftUp_iff :
    IsZero (tateCohomology (res S.subtype (dimensionShiftUp A)) n) ↔
      IsZero (tateCohomology (res S.subtype A) (n + 1)) :=
  (dimensionShiftUpResIso A S n).isZero_iff

/-- Vanishing in degree `n + 1` of a downward shift is vanishing in degree `n` of the original
module, also on a finite subgroup. -/
@[simp]
theorem isZero_res_dimensionShiftDown_iff :
    IsZero (tateCohomology (res S.subtype (dimensionShiftDown A)) (n + 1)) ↔
      IsZero (tateCohomology (res S.subtype A) n) :=
  (dimensionShiftDownResIso A S n).isZero_iff.symm

end Restriction

end TauCeti.TateCohomology
