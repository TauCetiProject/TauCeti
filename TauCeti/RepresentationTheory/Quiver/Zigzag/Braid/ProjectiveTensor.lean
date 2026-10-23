/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Unit
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Factors
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Adjacent
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The terms of a zigzag braid complex applied to a vertex projective

Let `Z` be the zigzag algebra of a finite simple graph and `P_j = Z e_j` its graded vertex
projective. The braid complex `B_i = [U_i ⟶ Z]` has the vertex bimodule
`U_i = Z e_i ⊗_k e_i Z` in cohomological degree `-1` and the regular bimodule in degree `0`.
Tensoring over `Z` with `P_j` extracts the corner `e_i Z e_j` from the middle:

```text
U_i ⊗_Z P_j ≅ Z e_i ⊗_k e_i Z e_j.
```

The corner is spanned by `e_i` and the volume `x_i`, of internal degrees `0` and `2`, when
`j = i`; by the arrow from `j` to `i`, of internal degree `1`, when `j` is adjacent to `i`; and
it vanishes otherwise. Hence, with `M{d}_p = M_{p-d}`,

```text
U_i ⊗_Z P_i ≅ P_i ⊞ P_i{2},    U_i ⊗_Z P_j ≅ P_i{1} (j adjacent to i),
U_i ⊗_Z P_j = 0 (j ≠ i not adjacent to i),    Z ⊗_Z P_j ≅ P_j,
```

as graded left `Z`-modules. These are the terms of the image of `B_i` under `- ⊗_Z P_j`.
The calculation covers isolated vertices of the public componentwise algebra.

## Main definitions

* `TauCeti.zigzagBraidProjectiveTensorCornerEquiv`: the carrier identification
  `U_i ⊗_Z P_j ≃ e_i Z e_j ⊗_k Z e_i`.
* `TauCeti.zigzagBraidProjectiveTensorSelfIso`: `U_i ⊗_Z P_i ≅ P_i ⊞ P_i{2}`.
* `TauCeti.zigzagBraidProjectiveTensorAdjIso`: `U_i ⊗_Z P_j ≅ P_i{1}` for `j` adjacent to `i`.
* `TauCeti.zigzagBraidProjectiveUnitTensorIso`: `Z ⊗_Z P_j ≅ P_j`.

## Main results

* `TauCeti.isZero_zigzagBraidProjectiveTensor`: `U_i ⊗_Z P_j` vanishes when `j ≠ i` is not
  adjacent to `i`.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4.6.
* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, Section 2e.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "P" => zigzagAlgebraGradedProjective k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
local notation "T" => fun i j : V ↦ GradedModuleCat.bimoduleModuleTensorObj Γ Γ (U i) (P j)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- Restrict the enveloping action to the right factor, as in balanced tensor products. -/
private local instance projectiveTensorRightModule (i : V) : Module Zᵐᵒᵖ (U i) :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)

/-! ### The carrier identification -/

private theorem ridSymm_smul (j : V) (a : Z) (n : L j) :
    (TensorProduct.rid k (L j)).symm (a • n) = a • (TensorProduct.rid k (L j)).symm n := by
  simp [TensorProduct.smul_tmul']

/-- Extract the corner `e_i Z e_j` from the tensor product of the vertex bimodule `U_i` with the
vertex projective `P_j`, leaving the left ideal `Z e_i` as the other factor. -/
def zigzagBraidProjectiveTensorCornerEquiv (i j : V) :
    T i j ≃ₗ[k] cornerSubmodule k (e i) (e j) ⊗[k] L i :=
  (GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv Γ Γ (U i) (P j)).trans
    ((BalancedTensorProduct.congr (zigzagBraidBimoduleRightFactorsEquiv k G i)
      (TensorProduct.rid k (L j)).symm
      (zigzagBraidBimoduleRightFactorsEquiv_op_smul k G i) (ridSymm_smul k G j)).trans
    ((BalancedTensorProduct.outerFactors k Z (R i) (L j) (L i) k).trans
      (TensorProduct.congr (spanSingletonBalancedTensorProductEquivCorner k
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G j)) (TensorProduct.rid k (L i)))))

/-- On pure tensors, corner extraction multiplies the right ideal factor of `U_i` into `P_j`. -/
@[simp]
theorem zigzagBraidProjectiveTensorCornerEquiv_tmul (i j : V) (l : L i) (r : R i) (n : L j) :
    zigzagBraidProjectiveTensorCornerEquiv k G i j
      (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ (U i) (P j)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r)) n) =
    spanSingletonBalancedTensorProductEquivCorner k
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
      (BalancedTensorProduct.tmul k Z r n) ⊗ₜ[k] l := by
  simp only [zigzagBraidProjectiveTensorCornerEquiv, LinearEquiv.trans_apply]
  rw [GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv_tmul Γ Γ (U i) (P j)]
  rw [BalancedTensorProduct.congr_tmul]
  simp only [zigzagBraidBimoduleRightFactorsEquiv_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.comm_tmul, TensorProduct.rid_symm_apply, BalancedTensorProduct.outerFactors_tmul,
    TensorProduct.congr_tmul, TensorProduct.rid_tmul, one_smul]

/-- The inverse of corner extraction inserts the right generator `e_i` of the vertex bimodule and
reads the corner element in `P_j`. -/
@[simp]
theorem zigzagBraidProjectiveTensorCornerEquiv_symm_tmul (i j : V)
    (c : cornerSubmodule k (e i) (e j)) (l : L i) :
    (zigzagBraidProjectiveTensorCornerEquiv k G i j).symm (c ⊗ₜ[k] l) =
      GradedModuleCat.bimoduleModuleTensorTmul Γ Γ (U i) (P j)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ⟨c, mem_span_singleton_of_mem_cornerSubmodule
          (isIdempotentElem_zigzagAlgebraBasis_inl k G j) c.2⟩ := by
  apply (zigzagBraidProjectiveTensorCornerEquiv k G i j).injective
  rw [LinearEquiv.apply_symm_apply, zigzagBraidProjectiveTensorCornerEquiv_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_spanSingletonBalancedTensorProductEquivCorner_tmul, coe_spanSingletonGenerator, unop_op]
  exact (mul_eq_self_of_mem_cornerSubmodule
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i) c.2).symm

/-! ### Inserting shifted vertex projectives -/

/-- A corner element `c ∈ e_i Z e_j`, read in the vertex projective `P_j = Z e_j`. -/
private def cornerToProjective {i j : V} (c : cornerSubmodule k (e i) (e j)) : L j :=
  ⟨c, mem_span_singleton_of_mem_cornerSubmodule
    (isIdempotentElem_zigzagAlgebraBasis_inl k G j) c.2⟩

/-- Insert `P_i` into `U_i ⊗_Z P_j` along a corner element `c`: `z ↦ (z ⊗ e_i) ⊗ c`. -/
private def insertCorner {i j : V} (c : cornerSubmodule k (e i) (e j)) : P i →ₗ[Z] T i j :=
  (LinearMap.toSpanSingleton Z (T i j)
    (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ (U i) (P j)
      (zigzagBraidBimoduleVertexGenerator k G i)
      (cornerToProjective k G c))).comp (L i).subtype

/-- The insertion along `c` is the inverse corner extraction of `c ⊗ z`. -/
private theorem insertCorner_apply {i j : V} (c : cornerSubmodule k (e i) (e j)) (z : L i) :
    insertCorner k G c z = (zigzagBraidProjectiveTensorCornerEquiv k G i j).symm (c ⊗ₜ[k] z) := by
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  simp only [zigzagBraidProjectiveTensorCornerEquiv_symm_tmul, insertCorner,
    LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.subtype_apply,
    GradedModuleCat.smul_bimoduleModuleTensorTmul, zigzagBraidBimoduleVertexGenerator_def,
    zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul, smul_spanSingletonGenerator he,
    cornerToProjective]

/-- The insertion along a corner element of internal degree `d` is a graded map
`P_i{d} ⟶ U_i ⊗_Z P_j`. -/
private def insertCornerHom {i j : V} {d : ℤ} (c : cornerSubmodule k (e i) (e j))
    (hc : (c : Z) ∈ zigzagAlgebraIntegerGrade k G d) : (P i).shiftObj d ⟶ T i j :=
  GradedModuleCat.ofHom (insertCorner k G c) <| LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
    have hz' := (zigzagAlgebraGradedProjective k G i |>.mem_shiftObj_piece_iff d p z).mp hz
    have ht := GradedModuleCat.bimoduleModuleTensorTmul_mem Γ Γ (U i) (P j)
      (zigzagBraidBimoduleVertexGenerator_mem k G i)
      ((mem_zigzagAlgebraGradedProjective_piece_iff k G j d (x := cornerToProjective k G c)).2 hc)
    have hdeg : p - d + (0 + d) = p + 0 := by omega
    simpa only [insertCorner, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
      Submodule.subtype_apply, vadd_eq_add, hdeg] using
      SetLike.GradedSMul.smul_mem ((mem_zigzagAlgebraGradedProjective_piece_iff k G i _).1 hz') ht

private theorem insertCornerHom_apply {i j : V} {d : ℤ} (c : cornerSubmodule k (e i) (e j))
    (hc : (c : Z) ∈ zigzagAlgebraIntegerGrade k G d) (z : L i) :
    (insertCornerHom k G c hc).hom z =
      (zigzagBraidProjectiveTensorCornerEquiv k G i j).symm (c ⊗ₜ[k] z) :=
  insertCorner_apply k G c z

/-! ### The diagonal corner -/

private theorem vertexCorner_mem (i : V) :
    (((zigzagAlgebraSelfCornerEquiv k G i).symm (1, 0) : cornerSubmodule k (e i) (e i)) : Z) ∈
      zigzagAlgebraIntegerGrade k G 0 := by
  simpa using zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i

private theorem volumeCorner_mem (i : V) :
    (((zigzagAlgebraSelfCornerEquiv k G i).symm (0, 1) : cornerSubmodule k (e i) (e i)) : Z) ∈
      zigzagAlgebraIntegerGrade k G 2 := by
  simpa using (zigzagAlgebraIntegerGrade_ofNat k G 2).ge
    (zigzagAlgebraBasis_inr_inr_mem_grade_two k G i)

/-- Insert `P_i` along the vertex idempotent of the diagonal corner. -/
private def selfInl (i : V) : P i ⟶ T i i :=
  (GradedModuleCat.shiftFunctorZeroIso _).inv.app (P i) ≫
    insertCornerHom k G _ (vertexCorner_mem k G i)

/-- Insert `P_i{2}` along the volume of the diagonal corner. -/
private def selfInr (i : V) : (P i).shiftObj 2 ⟶ T i i :=
  insertCornerHom k G _ (volumeCorner_mem k G i)

/-- The diagonal corner coordinates identify `U_i ⊗_Z P_i` with two copies of `Z e_i`. -/
private def selfEquiv (i : V) : T i i ≃ₗ[k] L i × L i :=
  (zigzagBraidProjectiveTensorCornerEquiv k G i i).trans
    ((TensorProduct.congr (zigzagAlgebraSelfCornerEquiv k G i) (LinearEquiv.refl k _)).trans
      ((TensorProduct.prodLeft k k k k (L i)).trans
        ((TensorProduct.lid k (L i)).prodCongr (TensorProduct.lid k (L i)))))

private theorem selfEquiv_symm_tmul (i : V) (a b : k) (z : L i) :
    selfEquiv k G i ((zigzagBraidProjectiveTensorCornerEquiv k G i i).symm
      ((zigzagAlgebraSelfCornerEquiv k G i).symm (a, b) ⊗ₜ[k] z)) = (a • z, b • z) := by
  simp only [selfEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.prodLeft_tmul,
    LinearEquiv.prodCongr_apply, TensorProduct.lid_tmul]

private theorem selfEquiv_coprod (i : V) (x : (P i) × ((P i).shiftObj 2)) :
    selfEquiv k G i (LinearMap.coprod (selfInl k G i).hom (selfInr k G i).hom x) = (x.1, x.2) := by
  have hl : (selfInl k G i).hom x.1 = (zigzagBraidProjectiveTensorCornerEquiv k G i i).symm
      ((zigzagAlgebraSelfCornerEquiv k G i).symm (1, 0) ⊗ₜ[k] x.1) := by
    simp only [selfInl, GradedModuleCat.hom_comp, LinearMap.comp_apply,
      GradedModuleCat.hom_shiftFunctorZeroIso_inv_app, LinearMap.id_apply]
    exact insertCornerHom_apply k G _ _ _
  rw [LinearMap.coprod_apply, map_add, hl, selfInr, insertCornerHom_apply, selfEquiv_symm_tmul,
    selfEquiv_symm_tmul]
  simp

private instance isIso_selfDesc (i : V) : IsIso (biprod.desc (selfInl k G i) (selfInr k G i)) := by
  refine GradedModuleCat.isIso_biprod_desc_of_bijective _ _ ⟨fun x y hxy ↦ ?_, fun t ↦ ?_⟩
  · have := congrArg (selfEquiv k G i) hxy
    rw [selfEquiv_coprod, selfEquiv_coprod] at this
    exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)
  · refine ⟨((selfEquiv k G i t).1, (selfEquiv k G i t).2), ?_⟩
    apply (selfEquiv k G i).injective
    exact selfEquiv_coprod k G i _

/-- **`U_i ⊗_Z P_i ≅ P_i ⊞ P_i{2}`**: the diagonal corner `e_i Z e_i` is spanned by the vertex
idempotent, of internal degree `0`, and the volume, of internal degree `2`. -/
def zigzagBraidProjectiveTensorSelfIso (i : V) : T i i ≅ P i ⊞ (P i).shiftObj 2 :=
  (asIso (biprod.desc (selfInl k G i) (selfInr k G i))).symm

/-- The summand `P_i` of `U_i ⊗_Z P_i` is inserted along the vertex idempotent of the diagonal
corner. -/
@[simp]
theorem zigzagBraidProjectiveTensorSelfIso_inv_inl (i : V) (z : L i) :
    (zigzagBraidProjectiveTensorSelfIso k G i).inv.hom
        ((biprod.inl : _ ⟶ P i ⊞ (P i).shiftObj 2).hom z) =
      (zigzagBraidProjectiveTensorCornerEquiv k G i i).symm
        ((zigzagAlgebraSelfCornerEquiv k G i).symm (1, 0) ⊗ₜ[k] z) := by
  rw [← LinearMap.comp_apply, ← GradedModuleCat.hom_comp]
  simp only [zigzagBraidProjectiveTensorSelfIso, Iso.symm_inv, asIso_hom, biprod.inl_desc,
    selfInl, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.hom_shiftFunctorZeroIso_inv_app, LinearMap.id_apply]
  exact insertCornerHom_apply k G _ _ _

/-- The summand `P_i{2}` of `U_i ⊗_Z P_i` is inserted along the volume of the diagonal corner. -/
@[simp]
theorem zigzagBraidProjectiveTensorSelfIso_inv_inr (i : V) (z : L i) :
    (zigzagBraidProjectiveTensorSelfIso k G i).inv.hom
        ((biprod.inr : _ ⟶ P i ⊞ (P i).shiftObj 2).hom z) =
      (zigzagBraidProjectiveTensorCornerEquiv k G i i).symm
        ((zigzagAlgebraSelfCornerEquiv k G i).symm (0, 1) ⊗ₜ[k] z) := by
  rw [← LinearMap.comp_apply, ← GradedModuleCat.hom_comp]
  simp only [zigzagBraidProjectiveTensorSelfIso, Iso.symm_inv, asIso_hom, biprod.inr_desc, selfInr]
  exact insertCornerHom_apply k G _ _ _

/-! ### Adjacent corners -/

private theorem arrowCorner_mem {i j : V} (h : G.Adj j i) :
    (((zigzagAlgebraAdjacentCornerEquiv k G h).symm 1 : cornerSubmodule k (e i) (e j)) : Z) ∈
      zigzagAlgebraIntegerGrade k G 1 := by
  simpa using (zigzagAlgebraIntegerGrade_ofNat k G 1).ge
    (zigzagAlgebraBasis_inr_inl_mem_grade_one k G (⟨(j, i), h⟩ : G.Dart))

/-- Insert `P_i{1}` along the arrow spanning the adjacent corner. -/
private def adjInsert {i j : V} (h : G.Adj j i) : (P i).shiftObj 1 ⟶ T i j :=
  insertCornerHom k G _ (arrowCorner_mem k G h)

/-- The arrow coordinate identifies `U_i ⊗_Z P_j` with `Z e_i` for adjacent `j`. -/
private def adjEquiv {i j : V} (h : G.Adj j i) : T i j ≃ₗ[k] L i :=
  (zigzagBraidProjectiveTensorCornerEquiv k G i j).trans
    ((TensorProduct.congr (zigzagAlgebraAdjacentCornerEquiv k G h) (LinearEquiv.refl k _)).trans
      (TensorProduct.lid k (L i)))

private theorem adjEquiv_adjInsert {i j : V} (h : G.Adj j i) (z : (P i).shiftObj 1) :
    adjEquiv k G h ((adjInsert k G h).hom z) = z := by
  rw [adjInsert, insertCornerHom_apply]
  simp [adjEquiv]

private instance isIso_adjInsert {i j : V} (h : G.Adj j i) : IsIso (adjInsert k G h) := by
  refine (GradedModuleCat.isIso_iff_bijective _).2
    ⟨fun x y hxy ↦ ?_, fun t ↦ ⟨adjEquiv k G h t, ?_⟩⟩
  · have := congrArg (adjEquiv k G h) hxy
    rwa [adjEquiv_adjInsert, adjEquiv_adjInsert] at this
  · apply (adjEquiv k G h).injective
    exact adjEquiv_adjInsert k G h _

/-- **`U_i ⊗_Z P_j ≅ P_i{1}` for `j` adjacent to `i`**: the corner `e_i Z e_j` is spanned by the
arrow from `j` to `i`, of internal degree `1`. -/
def zigzagBraidProjectiveTensorAdjIso {i j : V} (h : G.Adj j i) : T i j ≅ (P i).shiftObj 1 :=
  (asIso (adjInsert k G h)).symm

/-- The inverse of the adjacent isomorphism inserts `P_i{1}` along the arrow from `j` to `i`. -/
@[simp]
theorem zigzagBraidProjectiveTensorAdjIso_inv_apply {i j : V} (h : G.Adj j i) (z : L i) :
    (zigzagBraidProjectiveTensorAdjIso k G h).inv.hom z =
      (zigzagBraidProjectiveTensorCornerEquiv k G i j).symm
        ((zigzagAlgebraAdjacentCornerEquiv k G h).symm 1 ⊗ₜ[k] z) :=
  insertCornerHom_apply k G _ (arrowCorner_mem k G h) z

/-! ### Vanishing corners and the regular bimodule -/

/-- **`U_i ⊗_Z P_j = 0` for `j ≠ i` not adjacent to `i`**: the corner `e_i Z e_j` vanishes. -/
theorem isZero_zigzagBraidProjectiveTensor {i j : V} (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    IsZero (T i j) := by
  have : Subsingleton (cornerSubmodule k (e i) (e j)) := by
    rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij hadj]
    infer_instance
  have := (zigzagBraidProjectiveTensorCornerEquiv k G i j).toEquiv.subsingleton
  exact (IsZero.iff_id_eq_zero _).mpr
    (GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _))

/-- **`Z ⊗_Z P_j ≅ P_j`**: the regular bimodule acts as the identity on the vertex projective. -/
def zigzagBraidProjectiveUnitTensorIso (j : V) :
    GradedModuleCat.bimoduleModuleTensorObj Γ Γ (zigzagGradedBimodule k G) (P j) ≅ P j :=
  ((GradedModuleCat.bimoduleModuleTensor Γ Γ).mapIso (zigzagGradedBimoduleUnitIso k G).symm).app
      (P j) ≪≫ GradedModuleCat.bimoduleModuleTensorLeftUnitor.{w} Γ (P j)

/-- The identification `Z ⊗_Z P_j ≅ P_j` is the action of `Z` on `P_j`. -/
@[simp]
theorem zigzagBraidProjectiveUnitTensorIso_hom_tmul (j : V) (x : zigzagGradedBimodule k G)
    (n : L j) :
    (zigzagBraidProjectiveUnitTensorIso k G j).hom.hom
        (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ (zigzagGradedBimodule k G) (P j) x n) =
      (Bimodule.of (AlgHom.id k Z)).symm x • n := by
  have h : (zigzagBraidProjectiveUnitTensorIso k G j).hom =
      GradedModuleCat.bimoduleModuleTensorMap Γ Γ (zigzagGradedBimoduleUnitIso k G).inv (𝟙 _) ≫
        (GradedModuleCat.bimoduleModuleTensorLeftUnitor.{w} Γ (P j)).hom := by
    simp only [zigzagBraidProjectiveUnitTensorIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, GradedModuleCat.bimoduleModuleTensor_map_app, eqToHom_refl,
      Category.id_comp, Category.comp_id, Iso.symm_hom]
  simp only [h, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleModuleTensorMap_tmul, GradedModuleCat.hom_id, LinearMap.id_apply,
    GradedModuleCat.bimoduleModuleTensorLeftUnitor_hom]
  rw [GradedModuleCat.bimoduleModuleTensorLeftUnitorHom_tmul.{w} Γ (P j),
    GradedModuleCat.bimoduleUnitEquiv_symm_apply.{w}, zigzagGradedBimoduleUnitIso_inv_apply]

end TauCeti
