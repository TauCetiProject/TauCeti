/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import TauCeti.KnotTheory.Khovanov.DisjointUnion
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube
public import TauCeti.KnotTheory.PDCode.Reidemeister.Circle
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.AdjoinCircle

/-!
# The Khovanov complex of a diagram with an adjoined circle

Adjoining a crossing-free circle `O` to a planar PD-code `D` tensors its unnormalized Khovanov
complex with the circle module `V = R·1 ⊕ R·X`, where `1` has quantum degree `1` and `X` has
quantum degree `-1`. In quantum degree `j` this is the splitting

`⟦D ⊔ O⟧ʲ ≅ ⟦D⟧ʲ⁻¹ ⊞ ⟦D⟧ʲ⁺¹`

(`TauCeti.PDCode.khovanovBracketAdjoinCircleIso`), the first summand carrying the label `1` on
the adjoined circle and the second the label `X`.

In every smoothing the circles of `D.adjoinCircle` are those of `D` and the adjoined one
(`TauCeti.PDCode.adjoinCircleResolvedCircleEquiv`), which meets no crossing. So every saddle of
`D.adjoinCircle` is the saddle of `D` tensored with the identity on the adjoined circle
(`TauCeti.PDCode.resolutionEdgeMap_adjoinCircle_tmulEquiv`). Hence inserting the adjoined circle
with a fixed label (`TauCeti.PDCode.adjoinCircleInsert`, from `TauCeti.Khovanov.insertCircle`) and
reading off the coefficient of a label on it (`TauCeti.PDCode.adjoinCircleDelete`, from
`TauCeti.Khovanov.deleteCircle`) commute with all saddles, and are maps of cubes of resolutions,
`TauCeti.PDCode.adjoinCircleCubeInsert` and `TauCeti.PDCode.adjoinCircleCubeDelete`.
For the label `1`, insertion is the birth of a circle; for the label `X`, deletion is its death.
These maps exhibit the cube of `D.adjoinCircle` as a biproduct of two shifted copies of the cube of
`D`, and totalization turns this into the splitting of complexes.

This is the algebra behind the first Reidemeister move: one of the two resolutions of the crossing
of a kink is `D` with an adjoined circle.

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `adjoinCircleInsert D R s b`, `adjoinCircleDelete D R s b`: inserting the adjoined circle with
  the label `b`, and reading off the coefficient of the label `b` on it, on the circle tensors of
  the smoothings `s` of `D` and of `D.adjoinCircle`.
* `adjoinCircleCubeInsert D hD R b hj`: inserting the adjoined circle labelled `b`, a map of cubes
  from the cube of `D` in quantum degree `j'` to that of `D.adjoinCircle` in quantum degree
  `j = j' ± 1`.
* `adjoinCircleCubeDelete D hD R b hj`: the coefficient of the label `b` on the adjoined circle,
  a map of cubes in the opposite direction.
* `khovanovBracketAdjoinCircleIso D hD R j`: the splitting `⟦D ⊔ O⟧ʲ ≅ ⟦D⟧ʲ⁻¹ ⊞ ⟦D⟧ʲ⁺¹`.

## Main results

* `resolutionEdgeMap_adjoinCircle_tmulEquiv`: the saddles of `D.adjoinCircle` are those of `D`,
  tensored with the identity on the adjoined circle.
* `resolutionEdgeMap_adjoinCircleInsert`, `adjoinCircleDelete_resolutionEdgeMap`: inserting and
  deleting the adjoined circle commute with the saddles.
* `adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete`,
  `adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete_of_ne`,
  `adjoinCircleCubeDelete_comp_adjoinCircleCubeInsert_add`: the biproduct relations.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §5.2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.5.
-/

public section

noncomputable section

open CategoryTheory Limits Finset PiTensorProduct DualNumber
open scoped TensorProduct

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n)

/-! ### Inserting and deleting the adjoined circle -/

section InsertDelete

variable (R : Type u) [CommSemiring R]

/-- Inserting the adjoined circle of `D.adjoinCircle` smoothed by `s`, labelled `b`: the circle
tensor of `D` smoothed by `s` maps to that of `D.adjoinCircle` by `x ↦ x ⊗ v_b`. -/
def adjoinCircleInsert (s : Fin n → Bool) (b : Bool) :
    Khovanov.CircleTensor R (D.ResolvedCircle s) →ₗ[R]
      Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s) :=
  (reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s)).symm.toLinearMap ∘ₗ
    Khovanov.insertCircle R b

/-- Inserting the adjoined circle is `TauCeti.Khovanov.insertCircle` through the identification
of the circles. -/
theorem adjoinCircleInsert_apply (s : Fin n → Bool) (b : Bool)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.adjoinCircleInsert R s b x =
      (reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s)).symm
        (Khovanov.insertCircle R b x) :=
  (rfl)

/-- Reading off the coefficient of the label `b` on the adjoined circle of `D.adjoinCircle`
smoothed by `s`, a map to the circle tensor of `D` smoothed by `s`. -/
def adjoinCircleDelete (s : Fin n → Bool) (b : Bool) :
    Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s) →ₗ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle s) :=
  Khovanov.deleteCircle R b ∘ₗ
    (reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s)).toLinearMap

/-- Deleting the adjoined circle is `TauCeti.Khovanov.deleteCircle` through the identification
of the circles. -/
theorem adjoinCircleDelete_apply (s : Fin n → Bool) (b : Bool)
    (z : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    D.adjoinCircleDelete R s b z =
      Khovanov.deleteCircle R b
        (reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s) z) :=
  (rfl)

/-- Deleting the adjoined circle just inserted with the label `b'` returns the tensor for the
label `b'` and gives zero for the other label. -/
@[simp]
theorem adjoinCircleDelete_adjoinCircleInsert (s : Fin n → Bool) (b b' : Bool)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.adjoinCircleDelete R s b (D.adjoinCircleInsert R s b' x) = if b' = b then x else 0 := by
  rw [adjoinCircleDelete_apply, adjoinCircleInsert_apply, LinearEquiv.apply_symm_apply,
    Khovanov.deleteCircle_insertCircle]

/-- Every tensor of `D.adjoinCircle` is the sum of its parts with the adjoined circle labelled
`1` and `X`. -/
theorem adjoinCircleInsert_adjoinCircleDelete_add_adjoinCircleInsert_adjoinCircleDelete
    (s : Fin n → Bool) (z : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    D.adjoinCircleInsert R s false (D.adjoinCircleDelete R s false z) +
      D.adjoinCircleInsert R s true (D.adjoinCircleDelete R s true z) = z := by
  rw [adjoinCircleInsert_apply, adjoinCircleInsert_apply, adjoinCircleDelete_apply,
    adjoinCircleDelete_apply, ← map_add,
    Khovanov.insertCircle_deleteCircle_add_insertCircle_deleteCircle,
    LinearEquiv.symm_apply_apply]

end InsertDelete

/-! ### Saddles of a code with an adjoined circle -/

section Saddle

variable {s t : Fin n → Bool} {c : Fin n} (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (R : Type u) [CommSemiring R]

/-- **The adjoined circle is untouched by every saddle.** Through the identification of the
circles of `D.adjoinCircle` with those of `D` and the adjoined circle, a saddle of
`D.adjoinCircle` acts as the saddle of `D` on the circles of `D` and as the identity on the
adjoined circle. -/
theorem resolutionEdgeMap_adjoinCircle_tmulEquiv
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) (y : Khovanov.CircleTensor R Unit) :
    reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv t)
        (D.adjoinCircle.resolutionEdgeMap hst hc h' R
          ((reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s)).symm
            (tmulEquiv R R[ε] (x ⊗ₜ y)))) =
      tmulEquiv R R[ε] (D.resolutionEdgeMap hst hc h R x ⊗ₜ y) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D.adjoinCircle.circlesAt s c) = 2 := by rwa [card_circlesAt_adjoinCircle]
    rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs,
      D.adjoinCircle.resolutionEdgeMap_eq_resolutionMergeMap hst hc h' R hs',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, resolutionMergeMap_def,
      resolutionMergeMap_def, reindex_fiberwiseMul (f' := Sum.map (D.saddleResolvedCircleMap hst
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs)) id) _ _
        (funext (D.adjoinCircleResolvedCircleEquiv_saddleResolvedCircleMap hst _ _)),
      LinearEquiv.apply_symm_apply, fiberwiseMul_sum_map, fiberwiseMul_id, AlgHom.id_apply]
  · have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
    have ht := h.resolve_left hs
    have ht' : #(D.adjoinCircle.circlesAt t c) = 2 := by rwa [card_circlesAt_adjoinCircle]
    rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      D.adjoinCircle.resolutionEdgeMap_eq_resolutionSplitMap hst hc h' R ht',
      resolutionSplitMap_def, resolutionSplitMap_def, Khovanov.reindex_fiberwiseSplit
        (f' := Sum.map (D.saddleResolvedCircleMap hts
          (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht)) id) _ _
        (funext (D.adjoinCircleResolvedCircleEquiv_saddleResolvedCircleMap hts _ _)),
      LinearEquiv.apply_symm_apply]
    have hsplit := Khovanov.fiberwiseSplit_sum_map (R := R)
      (D.saddleResolvedCircleMap hts
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht)) (id : Unit → Unit)
    rw [Khovanov.fiberwiseSplit_id] at hsplit
    simpa using LinearMap.congr_fun hsplit (x ⊗ₜ y)

/-- Inserting the adjoined circle with a fixed label commutes with the saddles. -/
theorem resolutionEdgeMap_adjoinCircleInsert
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (b : Bool) (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.adjoinCircle.resolutionEdgeMap hst hc h' R (D.adjoinCircleInsert R s b x) =
      D.adjoinCircleInsert R t b (D.resolutionEdgeMap hst hc h R x) := by
  rw [adjoinCircleInsert_apply, adjoinCircleInsert_apply, LinearEquiv.eq_symm_apply,
    Khovanov.insertCircle_apply, Khovanov.insertCircle_apply,
    D.resolutionEdgeMap_adjoinCircle_tmulEquiv hst hc R h h']

/-- Reading off the coefficient of a label on the adjoined circle commutes with the saddles. -/
theorem adjoinCircleDelete_resolutionEdgeMap
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (b : Bool) (z : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    D.adjoinCircleDelete R t b (D.adjoinCircle.resolutionEdgeMap hst hc h' R z) =
      D.resolutionEdgeMap hst hc h R (D.adjoinCircleDelete R s b z) := by
  rw [adjoinCircleDelete_apply, adjoinCircleDelete_apply]
  obtain ⟨w, rfl⟩ := ((tmulEquiv R R[ε]).trans
    (reindex R (fun _ ↦ R[ε]) (D.adjoinCircleResolvedCircleEquiv s)).symm).surjective z
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [D.resolutionEdgeMap_adjoinCircle_tmulEquiv hst hc R h h', Khovanov.deleteCircle_tmulEquiv,
      Khovanov.deleteCircle_tmulEquiv, map_smul]
  | add w w' hw hw' => simp only [map_add, hw, hw']

end Saddle

/-! ### Maps of cubes -/

section Cube

variable (hD : D.IsPlanar) (R : Type u) [CommRing R] {j j' : ℤ}

/-- Inserting the adjoined circle labelled `b` sends the vertex `S` of the degree-`j'` cube of `D`
into the vertex `S` of the degree-`j` cube of `D.adjoinCircle`, where `j = j' + 1` for the label
`1` and `j = j' - 1` for the label `X`. -/
private theorem adjoinCircleInsert_resolutionCubeι_mem_range (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n))
    (x : (D.resolutionCube hD R j').obj S) :
    D.adjoinCircleInsert R (cubeState S) b ((D.resolutionCubeι hD R j' S).hom x) ∈
      LinearMap.range
        (D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S).hom := by
  have hx : (D.resolutionCubeι hD R j' S).hom x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece (j' - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  rw [range_resolutionCubeι, adjoinCircleInsert_apply, reindex_symm]
  convert (Khovanov.isHomogeneous_reindex (R := R) _).map_mem
    ((Khovanov.isHomogeneous_insertCircle R b).map_mem hx) using 2
  omega

/-- Reading off the coefficient of the label `b` on the adjoined circle sends the vertex `S` of
the degree-`j` cube of `D.adjoinCircle` into the vertex `S` of the degree-`j'` cube of `D`. -/
private theorem adjoinCircleDelete_resolutionCubeι_mem_range (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n))
    (x : (D.adjoinCircle.resolutionCube (D.isPlanar_adjoinCircle_iff.2 hD) R j).obj S) :
    D.adjoinCircleDelete R (cubeState S) b
        ((D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S).hom x) ∈
      LinearMap.range (D.resolutionCubeι hD R j' S).hom := by
  have hx : (D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S).hom x ∈
      (Khovanov.circleQuantumGrading R (D.adjoinCircle.ResolvedCircle (cubeState S))).piece
        (j - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  rw [range_resolutionCubeι, adjoinCircleDelete_apply]
  convert (Khovanov.isHomogeneous_deleteCircle R b).map_mem
    ((Khovanov.isHomogeneous_reindex (R := R) _).map_mem hx) using 2
  omega

/-- The component on the vertex `S` of inserting the adjoined circle labelled `b`. -/
private def adjoinCircleCubeInsertApp (b : Bool) (hj : j = j' + bif b then -1 else 1)
    (S : Finset (Fin n)) :
    (D.resolutionCube hD R j').obj S ⟶
      (D.adjoinCircle.resolutionCube (D.isPlanar_adjoinCircle_iff.2 hD) R j).obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _ (D.adjoinCircle.resolutionCubeι_injective
      (D.isPlanar_adjoinCircle_iff.2 hD) R j S)).symm.toLinearMap ∘ₗ
      (D.adjoinCircleInsert R (cubeState S) b ∘ₗ (D.resolutionCubeι hD R j' S).hom).codRestrict _
        (D.adjoinCircleInsert_resolutionCubeι_mem_range hD R b hj S)

@[reassoc]
private theorem adjoinCircleCubeInsertApp_comp_resolutionCubeι (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n)) :
    D.adjoinCircleCubeInsertApp hD R b hj S ≫
        D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S =
      D.resolutionCubeι hD R j' S ≫ ModuleCat.ofHom (D.adjoinCircleInsert R (cubeState S) b) := by
  ext x
  simp [adjoinCircleCubeInsertApp]

/-- The component on the vertex `S` of reading off the coefficient of the label `b` on the
adjoined circle. -/
private def adjoinCircleCubeDeleteApp (b : Bool) (hj : j = j' + bif b then -1 else 1)
    (S : Finset (Fin n)) :
    (D.adjoinCircle.resolutionCube (D.isPlanar_adjoinCircle_iff.2 hD) R j).obj S ⟶
      (D.resolutionCube hD R j').obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _ (D.resolutionCubeι_injective hD R j' S)).symm.toLinearMap ∘ₗ
      (D.adjoinCircleDelete R (cubeState S) b ∘ₗ
        (D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S).hom).codRestrict
        _ (D.adjoinCircleDelete_resolutionCubeι_mem_range hD R b hj S)

@[reassoc]
private theorem adjoinCircleCubeDeleteApp_comp_resolutionCubeι (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n)) :
    D.adjoinCircleCubeDeleteApp hD R b hj S ≫ D.resolutionCubeι hD R j' S =
      D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S ≫
        ModuleCat.ofHom (D.adjoinCircleDelete R (cubeState S) b) := by
  ext x
  simp [adjoinCircleCubeDeleteApp]

/-- **Inserting the adjoined circle as a map of cubes.** On the vertex `S` it tensors with the
label `b` on the adjoined circle: for `b = false` it is the birth of the circle labelled `1`,
from the cube of `D` in quantum degree `j' = j - 1` to that of `D.adjoinCircle` in quantum degree
`j`, and for `b = true` it inserts the circle labelled `X`, with `j' = j + 1`. It is a map of
cubes because the adjoined circle is untouched by every saddle. -/
def adjoinCircleCubeInsert (b : Bool) (hj : j = j' + bif b then -1 else 1) :
    D.resolutionCube hD R j' ⟶
      D.adjoinCircle.resolutionCube (D.isPlanar_adjoinCircle_iff.2 hD) R j :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeInsertApp hD R b hj) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j
        (insert a S)), Category.assoc, Category.assoc,
      adjoinCircleCubeInsertApp_comp_resolutionCubeι,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD R j' ha,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι _ R j ha,
      adjoinCircleCubeInsertApp_comp_resolutionCubeι_assoc]
    ext x
    exact (D.resolutionEdgeMap_adjoinCircleInsert hst hc R _ _ b _).symm

/-- On the vertex `S`, inserting the adjoined circle tensors with the label `b` on it. -/
@[reassoc]
theorem adjoinCircleCubeInsert_app_comp_resolutionCubeι (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeInsert hD R b hj).app S ≫
        D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S =
      D.resolutionCubeι hD R j' S ≫ ModuleCat.ofHom (D.adjoinCircleInsert R (cubeState S) b) := by
  rw [adjoinCircleCubeInsert, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeInsertApp_comp_resolutionCubeι hD R b hj S

/-- **Deleting the adjoined circle as a map of cubes.** On the vertex `S` it reads off the
coefficient of the label `b` on the adjoined circle: for `b = true` it is the death of the
circle, from the cube of `D.adjoinCircle` in quantum degree `j` to that of `D` in quantum degree
`j' = j + 1`, and for `b = false` it reads off the coefficient of `1`, with `j' = j - 1`. -/
def adjoinCircleCubeDelete (b : Bool) (hj : j = j' + bif b then -1 else 1) :
    D.adjoinCircle.resolutionCube (D.isPlanar_adjoinCircle_iff.2 hD) R j ⟶
      D.resolutionCube hD R j' :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeDeleteApp hD R b hj) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.resolutionCubeι hD R j' (insert a S)), Category.assoc, Category.assoc,
      adjoinCircleCubeDeleteApp_comp_resolutionCubeι,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc _ R j ha,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j' ha,
      adjoinCircleCubeDeleteApp_comp_resolutionCubeι_assoc]
    ext x
    exact D.adjoinCircleDelete_resolutionEdgeMap hst hc R _ _ b _

/-- On the vertex `S`, deleting the adjoined circle reads off the coefficient of the label `b`
on it. -/
@[reassoc]
theorem adjoinCircleCubeDelete_app_comp_resolutionCubeι (b : Bool)
    (hj : j = j' + bif b then -1 else 1) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeDelete hD R b hj).app S ≫ D.resolutionCubeι hD R j' S =
      D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S ≫
        ModuleCat.ofHom (D.adjoinCircleDelete R (cubeState S) b) := by
  rw [adjoinCircleCubeDelete, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeDeleteApp_comp_resolutionCubeι hD R b hj S

/-- Deleting the adjoined circle just inserted with the same label is the identity. -/
@[reassoc (attr := simp)]
theorem adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete (b : Bool)
    (hj : j = j' + bif b then -1 else 1) :
    D.adjoinCircleCubeInsert hD R b hj ≫ D.adjoinCircleCubeDelete hD R b hj = 𝟙 _ := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.id_app, ← cancel_mono (D.resolutionCubeι hD R j' S),
    Category.assoc, adjoinCircleCubeDelete_app_comp_resolutionCubeι,
    adjoinCircleCubeInsert_app_comp_resolutionCubeι_assoc, Category.id_comp]
  ext x
  simp

/-- Reading off the other label on the adjoined circle just inserted gives zero. -/
@[reassoc (attr := simp)]
theorem adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete_of_ne {j'' : ℤ} {b b' : Bool}
    (hb : b ≠ b') (hj : j = j' + bif b then -1 else 1) (hj' : j = j'' + bif b' then -1 else 1) :
    D.adjoinCircleCubeInsert hD R b hj ≫ D.adjoinCircleCubeDelete hD R b' hj' = 0 := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.app_zero, ← cancel_mono (D.resolutionCubeι hD R j'' S),
    Category.assoc, adjoinCircleCubeDelete_app_comp_resolutionCubeι,
    adjoinCircleCubeInsert_app_comp_resolutionCubeι_assoc, zero_comp]
  ext x
  simp [hb]

/-- Every element of the cube of `D.adjoinCircle` is the sum of its parts with the adjoined
circle labelled `1` and `X`. -/
theorem adjoinCircleCubeDelete_comp_adjoinCircleCubeInsert_add {j₀ j₁ : ℤ} (h₀ : j = j₀ + 1)
    (h₁ : j = j₁ - 1) :
    D.adjoinCircleCubeDelete hD R false (j := j) (j' := j₀) (by simpa using h₀) ≫
        D.adjoinCircleCubeInsert hD R false (j := j) (j' := j₀) (by simpa using h₀) +
      D.adjoinCircleCubeDelete hD R true (j := j) (j' := j₁)
          (by simpa [← sub_eq_add_neg] using h₁) ≫
        D.adjoinCircleCubeInsert hD R true (j := j) (j' := j₁)
          (by simpa [← sub_eq_add_neg] using h₁) =
      𝟙 _ := by
  ext S : 2
  rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app,
    ← cancel_mono (D.adjoinCircle.resolutionCubeι (D.isPlanar_adjoinCircle_iff.2 hD) R j S),
    Preadditive.add_comp, Category.assoc, Category.assoc,
    adjoinCircleCubeInsert_app_comp_resolutionCubeι,
    adjoinCircleCubeInsert_app_comp_resolutionCubeι,
    adjoinCircleCubeDelete_app_comp_resolutionCubeι_assoc,
    adjoinCircleCubeDelete_app_comp_resolutionCubeι_assoc, Category.id_comp]
  ext x
  exact D.adjoinCircleInsert_adjoinCircleDelete_add_adjoinCircleInsert_adjoinCircleDelete R _ _

end Cube

/-! ### The splitting of the Khovanov complex -/

variable (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- **The Khovanov complex of a diagram with an adjoined circle** is two shifted copies of the
complex of the diagram: `⟦D ⊔ O⟧ʲ ≅ ⟦D⟧ʲ⁻¹ ⊞ ⟦D⟧ʲ⁺¹`, that is `⟦D ⊔ O⟧ ≅ ⟦D⟧ ⊗ V` with
`V = R·1 ⊕ R·X`. Its components are the cochain maps induced by reading off the coefficients of
the labels `1` and `X` on the adjoined circle, and its inverse inserts the adjoined circle with
these labels. -/
def khovanovBracketAdjoinCircleIso :
    D.adjoinCircle.khovanovBracket (D.isPlanar_adjoinCircle_iff.2 hD) R j ≅
      D.khovanovBracket hD R (j - 1) ⊞ D.khovanovBracket hD R (j + 1) :=
  eqToIso (D.adjoinCircle.khovanovBracket_apply _ R j) ≪≫
    { hom := biprod.lift
          (NatTrans.cubeComplexMap (D.adjoinCircleCubeDelete hD R false (j' := j - 1) (by simp)))
          (NatTrans.cubeComplexMap (D.adjoinCircleCubeDelete hD R true (j' := j + 1) (by simp)))
      inv := biprod.desc
          (NatTrans.cubeComplexMap (D.adjoinCircleCubeInsert hD R false (j' := j - 1) (by simp)))
          (NatTrans.cubeComplexMap (D.adjoinCircleCubeInsert hD R true (j' := j + 1) (by simp)))
      hom_inv_id := by
        rw [biprod.lift_desc, ← NatTrans.cubeComplexMap_comp, ← NatTrans.cubeComplexMap_comp,
          ← NatTrans.cubeComplexMap_add,
          D.adjoinCircleCubeDelete_comp_adjoinCircleCubeInsert_add hD R (j₀ := j - 1)
            (j₁ := j + 1) (by simp) (by simp), NatTrans.cubeComplexMap_id]
      inv_hom_id := by
        refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
          simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
            biprod.lift_fst, biprod.lift_snd, ← NatTrans.cubeComplexMap_comp, Category.comp_id,
            adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete, NatTrans.cubeComplexMap_id,
            biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd]
        all_goals
          rw [adjoinCircleCubeInsert_comp_adjoinCircleCubeDelete_of_ne _ _ _ (by decide)]
          exact (cubeComplexFunctor _ _).map_zero _ _ } ≪≫
    biprod.mapIso (eqToIso (D.khovanovBracket_apply hD R (j - 1)).symm)
      (eqToIso (D.khovanovBracket_apply hD R (j + 1)).symm)


/-- The first component of `TauCeti.PDCode.khovanovBracketAdjoinCircleIso` reads off the
coefficient of the label `1` on the adjoined circle. -/
@[reassoc (attr := simp)]
theorem khovanovBracketAdjoinCircleIso_hom_fst :
    (D.khovanovBracketAdjoinCircleIso hD R j).hom ≫ biprod.fst =
      eqToHom (D.adjoinCircle.khovanovBracket_apply _ R j) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeDelete hD R false (j' := j - 1) (by simp)) ≫
          eqToHom (D.khovanovBracket_apply hD R (j - 1)).symm := by
  simp [khovanovBracketAdjoinCircleIso]

/-- The second component of `TauCeti.PDCode.khovanovBracketAdjoinCircleIso` reads off the
coefficient of the label `X` on the adjoined circle. -/
@[reassoc (attr := simp)]
theorem khovanovBracketAdjoinCircleIso_hom_snd :
    (D.khovanovBracketAdjoinCircleIso hD R j).hom ≫ biprod.snd =
      eqToHom (D.adjoinCircle.khovanovBracket_apply _ R j) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeDelete hD R true (j' := j + 1) (by simp)) ≫
          eqToHom (D.khovanovBracket_apply hD R (j + 1)).symm := by
  simp [khovanovBracketAdjoinCircleIso]

/-- On the first summand, the inverse of `TauCeti.PDCode.khovanovBracketAdjoinCircleIso` inserts
the adjoined circle labelled `1`. -/
@[reassoc (attr := simp)]
theorem inl_khovanovBracketAdjoinCircleIso_inv :
    biprod.inl ≫ (D.khovanovBracketAdjoinCircleIso hD R j).inv =
      eqToHom (D.khovanovBracket_apply hD R (j - 1)) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeInsert hD R false (j' := j - 1) (by simp)) ≫
          eqToHom (D.adjoinCircle.khovanovBracket_apply _ R j).symm := by
  simp [khovanovBracketAdjoinCircleIso]

/-- On the second summand, the inverse of `TauCeti.PDCode.khovanovBracketAdjoinCircleIso` inserts
the adjoined circle labelled `X`. -/
@[reassoc (attr := simp)]
theorem inr_khovanovBracketAdjoinCircleIso_inv :
    biprod.inr ≫ (D.khovanovBracketAdjoinCircleIso hD R j).inv =
      eqToHom (D.khovanovBracket_apply hD R (j + 1)) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeInsert hD R true (j' := j + 1) (by simp)) ≫
          eqToHom (D.adjoinCircle.khovanovBracket_apply _ R j).symm := by
  simp [khovanovBracketAdjoinCircleIso]

end TauCeti.PDCode
