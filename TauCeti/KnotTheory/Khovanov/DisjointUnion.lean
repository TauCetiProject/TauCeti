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
theorem tmulEquiv_circleBasis (l : σ → Bool) (k : τ → Bool) :
    tmulEquiv R R[ε] (circleBasis R σ l ⊗ₜ circleBasis R τ k) =
      circleBasis R (σ ⊕ τ) (Sum.elim l k) := by
  simp only [circleBasis_apply, tmulEquiv_apply]
  congr 1
  funext i
  cases i <;> rfl

/-- Coordinates of a disjoint-union tensor are the products of its two circle-tensor
coordinates. -/
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
