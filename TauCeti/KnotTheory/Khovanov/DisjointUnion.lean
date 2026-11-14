/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Split
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Transport

/-!
# Disjoint unions of circle tensors

The native `PiTensorProduct.tmulEquiv` identifies the tensor product of two circle tensors
with the tensor indexed by the disjoint union of their circles. Its enhanced-state coordinates
and Frobenius pairing factor over the two summands. Consequently splitting along a disjoint
union of circle correspondences acts independently on the two factors, as does multiplication.

For native PD-codes, `PDCode.disjointUnionCircleTensorEquiv` combines this identification with
the actual disjoint-union correspondence of resolved circles. Crossing-free labels follow that
correspondence, including their prescribed numbering in the disjoint union.

Adjoining a single circle `()` gives the insertion `insertCircle R b : x ↦ x ⊗ v_b` of that
circle with the label `b` (`v_false = 1`, `v_true = X`) and the deletion `deleteCircle R b`,
which reads off the coefficient of the label `b` on it. They satisfy the biproduct relations of
`CircleTensor R (σ ⊕ Unit) ≅ CircleTensor R σ ⊗ (R·1 ⊕ R·X)`, and shift the quantum degree by
`±1`. Inserting the label `1` is the birth `fiberwiseMul Sum.inl` and deleting the label `X` is
the death `fiberwiseSplit Sum.inl` (`TauCeti.Khovanov.insertCircle_false`,
`TauCeti.Khovanov.deleteCircle_true`).

The maps use the ordinary unsigned tensor product, as in M. Khovanov,
*A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
-/

public section

open PiTensorProduct DualNumber
open scoped TensorProduct

namespace TauCeti.Khovanov

section Semiring

variable {R : Type*} [CommSemiring R]
variable {σ τ σ' τ' : Type*}

section Finite

variable [Finite σ] [Finite τ]

/-- Joining two enhanced-state basis tensors joins their labellings on the disjoint union. -/
@[simp↓]
theorem tmulEquiv_circleBasis (l : σ → Bool) (k : τ → Bool) :
    tmulEquiv R R[ε] (circleBasis R σ l ⊗ₜ circleBasis R τ k) =
      circleBasis R (σ ⊕ τ) (Sum.elim l k) := by
  simp only [circleBasis_apply, tmulEquiv_apply]
  congr 1
  funext i
  cases i <;> rfl

/-- Coordinates of a disjoint-union tensor are the products of its two circle-tensor
coordinates. -/
@[simp]
theorem circleBasis_repr_tmulEquiv (x : CircleTensor R σ) (y : CircleTensor R τ)
    (l : σ ⊕ τ → Bool) :
    (circleBasis R (σ ⊕ τ)).repr (tmulEquiv R R[ε] (x ⊗ₜ y)) l =
      (circleBasis R σ).repr x (l ∘ Sum.inl) *
        (circleBasis R τ).repr y (l ∘ Sum.inr) := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite τ
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul, circleBasis_repr_tprod,
        Fintype.prod_sum_type, smul_eq_mul, mul_assoc, mul_left_comm]
    | add y z hy hz =>
      simp [TensorProduct.tmul_add, hy, hz, mul_add]
  | add x z hx hz =>
    simp [TensorProduct.add_tmul, hx, hz, add_mul]

end Finite

variable [Fintype σ] [Fintype τ] [Fintype σ'] [Fintype τ']

/-- The Frobenius pairing of a disjoint union is the product of the pairings on its two
summands. -/
@[simp]
theorem circleDuality_tmulEquiv (x u : CircleTensor R σ) (y v : CircleTensor R τ) :
    circleDuality R (σ ⊕ τ) (tmulEquiv R R[ε] (x ⊗ₜ y))
      (tmulEquiv R R[ε] (u ⊗ₜ v)) =
      circleDuality R σ x u * circleDuality R τ y v := by
  classical
  rw [← (circleBasis R σ).sum_repr u, ← (circleBasis R τ).sum_repr v]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_sum, map_smul,
    tmulEquiv_circleBasis, circleDuality_apply_circleBasis, circleBasis_repr_tmulEquiv,
    Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
  congr 1
  funext l
  congr 1
  funext k
  simp [Function.comp_def, mul_assoc, mul_left_comm, mul_comm]

/-- Splitting a disjoint union of circle correspondences is the tensor product of their split
maps. This retains every circle in both summands, including unaffected and isolated circles. -/
theorem fiberwiseSplit_sum_map [DecidableEq σ'] [DecidableEq τ']
    (f : σ → σ') (g : τ → τ') :
    (fiberwiseSplit (R := R) (Sum.map f g)).comp (tmulEquiv R R[ε]).toLinearMap =
      (tmulEquiv R R[ε]).toLinearMap.comp
        (TensorProduct.map (fiberwiseSplit f) (fiberwiseSplit g)) := by
  refine TensorProduct.ext (LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_)
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.map_tmul]
  apply (circleDuality R (σ ⊕ τ)).injective
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (tmulEquiv R R[ε]).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    rw [circleDuality_fiberwiseSplit, fiberwiseMul_sum_map,
      circleDuality_tmulEquiv, circleDuality_tmulEquiv,
      circleDuality_fiberwiseSplit, circleDuality_fiberwiseSplit]
  | add u v hu hv => simp only [map_add, hu, hv]

end Semiring

section Grading

variable (R : Type*) [CommRing R] (σ τ : Type*) [Fintype σ] [Fintype τ]

/-- The native disjoint-union tensor equivalence preserves the total quantum degree. -/
theorem isHomogeneous_tmulEquiv :
    TauCeti.LinearMap.IsHomogeneous (tmulEquiv R R[ε]).toLinearMap
      ((circleQuantumGrading R σ).tensorProduct (circleQuantumGrading R τ)).piece
      (circleQuantumGrading R (σ ⊕ τ)).piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro n z hz
  refine (circleQuantumGrading R σ).tensorProduct_piece_le (circleQuantumGrading R τ)
    (C := ((circleQuantumGrading R (σ ⊕ τ)).piece (n + 0)).comap
      (tmulEquiv R R[ε]).toLinearMap) (fun p x hx y hy ↦ ?_) hz
  rw [Submodule.mem_comap, LinearEquiv.coe_toLinearMap,
    mem_circleQuantumGrading_piece_iff]
  intro l hl
  rw [circleBasis_repr_tmulEquiv] at hl
  rw [mem_circleQuantumGrading_piece_iff] at hx hy
  have hx' := hx _ (left_ne_zero_of_mul hl)
  have hy' := hy _ (right_ne_zero_of_mul hl)
  have hdegree : labelingQuantumDegree (σ ⊕ τ) l =
      labelingQuantumDegree σ (l ∘ Sum.inl) + labelingQuantumDegree τ (l ∘ Sum.inr) := by
    simp [labelingQuantumDegree_def, Fintype.sum_sum_type]
  omega

/-- Separating a disjoint-union tensor preserves the total quantum degree. -/
theorem isHomogeneous_tmulEquiv_symm :
    TauCeti.LinearMap.IsHomogeneous (tmulEquiv R R[ε]).symm.toLinearMap
      (circleQuantumGrading R (σ ⊕ τ)).piece
      ((circleQuantumGrading R σ).tensorProduct (circleQuantumGrading R τ)).piece 0 :=
  (isHomogeneous_tmulEquiv R σ τ).linearEquiv_symm

end Grading

/-! ### Adjoining one circle -/

section AdjoinCircle

section Semiring

variable (R : Type*) [CommSemiring R] {σ : Type*}

/-- Adjoining one circle labelled `1` (for `b = false`) or `X` (for `b = true`) to a circle
tensor: `x ↦ x ⊗ v_b` through the disjoint-union tensor equivalence. For `b = false` this is
the unit, the birth of a circle. -/
noncomputable def insertCircle (b : Bool) : CircleTensor R σ →ₗ[R] CircleTensor R (σ ⊕ Unit) :=
  (tmulEquiv R R[ε]).toLinearMap ∘ₗ (TensorProduct.mk R _ _).flip (circleBasis R Unit fun _ ↦ b)

/-- Inserting a circle labelled `b` tensors with the basis vector `b` on the new circle. -/
theorem insertCircle_apply (b : Bool) (x : CircleTensor R σ) :
    insertCircle R b x = tmulEquiv R R[ε] (x ⊗ₜ circleBasis R Unit fun _ ↦ b) :=
  (rfl)

/-- Inserting a circle labelled `b` extends an enhanced state by the label `b`. -/
@[simp↓]
theorem insertCircle_circleBasis [Finite σ] (b : Bool) (l : σ → Bool) :
    insertCircle R b (circleBasis R σ l) = circleBasis R (σ ⊕ Unit) (Sum.elim l fun _ ↦ b) := by
  rw [insertCircle_apply, tmulEquiv_circleBasis]

/-- The coefficient of the label `b` on the adjoined circle `()`: `x ⊗ y ↦ y_b • x`. For
`b = true` this is the counit, the death of a circle. -/
noncomputable def deleteCircle (b : Bool) : CircleTensor R (σ ⊕ Unit) →ₗ[R] CircleTensor R σ :=
  (TensorProduct.rid R _).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id ((circleBasis R Unit).coord fun _ ↦ b) ∘ₗ
      (tmulEquiv R R[ε]).symm.toLinearMap

/-- Deleting the adjoined circle reads off the coefficient of the label `b` there. -/
@[simp]
theorem deleteCircle_tmulEquiv (b : Bool) (x : CircleTensor R σ) (y : CircleTensor R Unit) :
    deleteCircle R b (tmulEquiv R R[ε] (x ⊗ₜ y)) =
      (circleBasis R Unit).repr y (fun _ ↦ b) • x := by
  simp [deleteCircle]

/-- Deleting the adjoined circle keeps the enhanced states labelling it by `b`, restricted to
the other circles, and kills the others. -/
@[simp↓]
theorem deleteCircle_circleBasis [Finite σ] (b : Bool) (l : σ ⊕ Unit → Bool) :
    deleteCircle R b (circleBasis R (σ ⊕ Unit) l) =
      if l (.inr ()) = b then circleBasis R σ (l ∘ Sum.inl) else 0 := by
  have hb : (l ∘ Sum.inr = fun _ ↦ b) ↔ l (.inr ()) = b :=
    ⟨fun h ↦ congrFun h (), fun h ↦ funext fun _ ↦ h⟩
  conv_lhs => rw [← Sum.elim_comp_inl_inr l, ← tmulEquiv_circleBasis, deleteCircle_tmulEquiv,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [hb, ite_smul, one_smul, zero_smul]

/-- Deleting a circle inserted with the label `b'` returns the tensor for the label `b'` and
gives zero for the other label. -/
@[simp]
theorem deleteCircle_insertCircle (b b' : Bool) (x : CircleTensor R σ) :
    deleteCircle R b (insertCircle R b' x) = if b' = b then x else 0 := by
  rw [insertCircle_apply, deleteCircle_tmulEquiv, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : b' = b
  · simp [h]
  · have h' : (fun _ : Unit ↦ b') ≠ fun _ ↦ b := fun e ↦ h (congrFun e ())
    simp [h, h']

/-- A tensor on `σ ⊕ Unit` is the sum of its two parts with the adjoined circle labelled `1`
and `X`. -/
theorem insertCircle_deleteCircle_add_insertCircle_deleteCircle [Finite σ]
    (z : CircleTensor R (σ ⊕ Unit)) :
    insertCircle R false (deleteCircle R false z) + insertCircle R true (deleteCircle R true z) =
      z := by
  have h : insertCircle R false ∘ₗ deleteCircle R false +
      insertCircle R true ∘ₗ deleteCircle R true =
        (LinearMap.id : CircleTensor R (σ ⊕ Unit) →ₗ[R] _) := by
    refine (circleBasis R (σ ⊕ Unit)).ext fun l ↦ ?_
    have hl : Sum.elim (l ∘ Sum.inl) (fun _ ↦ l (.inr ())) = l := by
      ext (i | i) <;> rfl
    rw [← hl]
    generalize l (.inr ()) = b
    generalize l ∘ Sum.inl = k
    cases b <;> simp [-circleBasis_apply]
  exact LinearMap.congr_fun h z

/-- Inserting a circle labelled `1` is the birth of a circle: multiplication along the inclusion
`σ → σ ⊕ Unit`, whose fibre over the adjoined circle is empty. -/
theorem insertCircle_false [Fintype σ] [DecidableEq σ] :
    insertCircle R false =
      (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (Sum.inl : σ → σ ⊕ Unit)).toLinearMap := by
  refine (circleBasis R σ).ext fun l ↦ ?_
  rw [insertCircle_circleBasis, AlgHom.toLinearMap_apply, fiberwiseMul_circleBasis_eq_tprod,
    circleBasis_apply]
  congr 1
  funext C
  rcases C with i | u
  · cases h : l i <;> simp [h, Finset.filter_eq', Finset.filter_and]
  · simp

/-- Reading off the coefficient of `X` on the adjoined circle is the death of that circle: the
split map along the inclusion `σ → σ ⊕ Unit`, adjoint to its birth. -/
theorem deleteCircle_true [Fintype σ] [DecidableEq σ] :
    deleteCircle R true = fiberwiseSplit (R := R) (Sum.inl : σ → σ ⊕ Unit) := by
  refine LinearMap.ext fun z ↦ (circleDuality R σ).injective (LinearMap.ext fun y ↦ ?_)
  rw [circleDuality_fiberwiseSplit, ← AlgHom.toLinearMap_apply, ← insertCircle_false]
  obtain ⟨w, rfl⟩ := (tmulEquiv R R[ε]).surjective z
  induction w using TensorProduct.inductionOn with
  | tmul x v =>
    rw [deleteCircle_tmulEquiv, insertCircle_apply, circleDuality_tmulEquiv,
      circleDuality_apply_circleBasis, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
    simp only [Bool.not_false]
  | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']

end Semiring

section Grading

variable (R : Type*) [CommRing R] {σ : Type*} [Fintype σ]

/-- Inserting a circle labelled `1` raises the quantum degree by one, and inserting it labelled
`X` lowers it by one. -/
theorem isHomogeneous_insertCircle (b : Bool) :
    TauCeti.LinearMap.IsHomogeneous (insertCircle R (σ := σ) b)
      (circleQuantumGrading R σ).piece (circleQuantumGrading R (σ ⊕ Unit)).piece
      (bif b then -1 else 1) := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  have hb : circleBasis R Unit (fun _ ↦ b) ∈
      (circleQuantumGrading R Unit).piece (bif b then -1 else 1) := by
    convert circleBasis_mem_circleQuantumGrading_piece (R := R) fun _ : Unit ↦ b using 2
    simp [labelingQuantumDegree_def]
  rw [insertCircle_apply]
  simpa only [add_zero, LinearEquiv.coe_coe] using (isHomogeneous_tmulEquiv R σ Unit).map_mem
    (InternalGrading.tmul_mem_tensorProduct _ _ hx hb)

/-- Deleting a circle labelled `1` lowers the quantum degree by one, and deleting it labelled
`X` raises it by one. -/
theorem isHomogeneous_deleteCircle (b : Bool) :
    TauCeti.LinearMap.IsHomogeneous (deleteCircle R (σ := σ) b)
      (circleQuantumGrading R (σ ⊕ Unit)).piece (circleQuantumGrading R σ).piece
      (-bif b then -1 else 1) := by
  classical
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [mem_circleQuantumGrading_piece_iff] at hx
  rw [← (circleBasis R (σ ⊕ Unit)).sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  by_cases hl : (circleBasis R (σ ⊕ Unit)).repr x l = 0
  · simp [hl]
  rw [map_smul, deleteCircle_circleBasis]
  split_ifs with h
  · refine Submodule.smul_mem _ _ ?_
    have hdeg : labelingQuantumDegree (σ ⊕ Unit) l =
        labelingQuantumDegree σ (l ∘ Sum.inl) + bif b then -1 else 1 := by
      simp [labelingQuantumDegree_def, Fintype.sum_sum_type, h]
    convert circleBasis_mem_circleQuantumGrading_piece (R := R) (l ∘ Sum.inl) using 2
    rw [← hx l hl, hdeg]
    ring
  · simp

end Grading

end AdjoinCircle

end TauCeti.Khovanov

namespace TauCeti.PDCode

variable {n m : ℕ} (D : PDCode n) (E : PDCode m) (s : Fin (n + m) → Bool)
variable (R : Type*) [CommSemiring R]

/-- Circle tensors of an actual disjoint union split into the tensors of its two resolved
summands, using the native circle correspondence and the native indexed tensor equivalence. -/
noncomputable def disjointUnionCircleTensorEquiv :
    Khovanov.CircleTensor R ((D.disjointUnion E).ResolvedCircle s) ≃ₗ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle (s ∘ Fin.castAdd m)) ⊗[R]
        Khovanov.CircleTensor R (E.ResolvedCircle (s ∘ Fin.natAdd n)) :=
  (reindex R (fun _ ↦ R[ε]) (D.disjointUnionResolvedCircleEquiv E s)).trans
    (tmulEquiv R R[ε]).symm

-- Keep the bundled comparison as the simp normal form so its generic inverse laws still match.

/-- The disjoint-union comparison sends a pure tensor to the tensors on the two actual
resolved-circle summands. -/
theorem disjointUnionCircleTensorEquiv_tprod
    (x : (D.disjointUnion E).ResolvedCircle s → R[ε]) :
    D.disjointUnionCircleTensorEquiv E s R (tprod R x) =
      tprod R (fun C ↦ x ((D.disjointUnionResolvedCircleEquiv E s).symm (.inl C))) ⊗ₜ
        tprod R (fun C ↦ x ((D.disjointUnionResolvedCircleEquiv E s).symm (.inr C))) := by
  simp only [disjointUnionCircleTensorEquiv, LinearEquiv.trans_apply, reindex_tprod,
    tmulEquiv_symm_apply]

/-- The inverse comparison places the two pure tensors on their actual summand circles. -/
theorem disjointUnionCircleTensorEquiv_symm_tprod
    (x : D.ResolvedCircle (s ∘ Fin.castAdd m) → R[ε])
    (y : E.ResolvedCircle (s ∘ Fin.natAdd n) → R[ε]) :
    (D.disjointUnionCircleTensorEquiv E s R).symm (tprod R x ⊗ₜ tprod R y) =
      tprod R (fun C ↦ Sum.elim x y (D.disjointUnionResolvedCircleEquiv E s C)) := by
  rw [disjointUnionCircleTensorEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    tmulEquiv_apply]
  simp [reindex_tprod]

section Grading

variable (S : Type*) [CommRing S]

/-- The actual disjoint-union comparison preserves the total quantum degree. -/
theorem isHomogeneous_disjointUnionCircleTensorEquiv :
    TauCeti.LinearMap.IsHomogeneous (D.disjointUnionCircleTensorEquiv E s S).toLinearMap
      (Khovanov.circleQuantumGrading S ((D.disjointUnion E).ResolvedCircle s)).piece
      ((Khovanov.circleQuantumGrading S (D.ResolvedCircle (s ∘ Fin.castAdd m))).tensorProduct
        (Khovanov.circleQuantumGrading S (E.ResolvedCircle (s ∘ Fin.natAdd n)))).piece 0 := by
  exact (Khovanov.isHomogeneous_tmulEquiv_symm S _ _).comp
    (Khovanov.isHomogeneous_reindex (D.disjointUnionResolvedCircleEquiv E s))

/-- Reassembling the two actual resolved-circle tensors preserves the total quantum degree. -/
theorem isHomogeneous_disjointUnionCircleTensorEquiv_symm :
    TauCeti.LinearMap.IsHomogeneous (D.disjointUnionCircleTensorEquiv E s S).symm.toLinearMap
      ((Khovanov.circleQuantumGrading S (D.ResolvedCircle (s ∘ Fin.castAdd m))).tensorProduct
        (Khovanov.circleQuantumGrading S (E.ResolvedCircle (s ∘ Fin.natAdd n)))).piece
      (Khovanov.circleQuantumGrading S ((D.disjointUnion E).ResolvedCircle s)).piece 0 :=
  (D.isHomogeneous_disjointUnionCircleTensorEquiv E s S).linearEquiv_symm

end Grading

end TauCeti.PDCode
