/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Equivariance
public import TauCeti.RepresentationTheory.Tensor.Pi.Basic
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Commutant

/-!
# The invariant-tensor bridge for the orthogonal group

Brauer's duality for the orthogonal group says that the commutant of `O(n)` on the tensor power
`(Rⁿ)^{⊗k}` is the image of the Brauer algebra `B_k(n)`. Its classical proof turns the statement
about endomorphisms into one about invariant tensors, the first fundamental theorem of invariant
theory for `O(n)`, and this file carries out that translation.

The dot product identifies `Rⁿ` with its dual, so an endomorphism of `(Rⁿ)^{⊗k}` is a tensor with
`2 * k` slots, indexed by the boundary points `Fin k ⊕ Fin k` of a Brauer diagram: the input slots
`Sum.inl i` and the output slots `Sum.inr j`. This is the linear equivalence
`TauCeti.boundaryTensorEquiv`, whose value on `f` has the entry `f_(v, u)` at the labelling
`Sum.elim u v`. Multiplying `f` by the tensor power of a matrix `A` on the left and of its transpose
on the right is acting by `A` on all `2 * k` slots. For an orthogonal `A` this is conjugation, so
`f` commutes with the orthogonal group exactly when its tensor is invariant under the diagonal
action.

A Brauer diagram `D` gives the **matching tensor** `t_D` of `TauCeti.BrauerDiagram.matchingTensor`:
the tensor product, over the arcs of `D`, of the copairing `∑ c, e_c ⊗ e_c` placed in the two slots
of the arc. Expanding the product, it is the sum of the monomial tensors whose labelling is constant
on the arcs of `D`. The equivalence sends the action of `D` to `t_D`. So the image of the Brauer
algebra corresponds to the span of the matching tensors, the commutant to the invariant tensors,
and Brauer's duality on `(Rⁿ)^{⊗k}` is equivalent to the statement that the matching tensors span
the invariants of `O(n)` in the `2 * k`-th tensor power
(`TauCeti.range_brauerActionOrth_eq_centralizer_iff`).

## Main definitions

* `TauCeti.boundaryTensorBasis`: the monomial basis of the tensor power indexed by the boundary
  points `Fin k ⊕ Fin k`.
* `TauCeti.boundaryTensorEquiv`: endomorphisms of `(Rⁿ)^{⊗k}` as tensors on the boundary points.
* `TauCeti.BrauerDiagram.matchingTensor`: the matching tensor of a Brauer diagram.

## Main results

* `TauCeti.boundaryTensorEquiv_eq_sum`: the tensor of `f` is `∑ u, e_u ⊗ f e_u`.
* `TauCeti.boundaryTensorEquiv_dualTensorHom`: the operator `x ↦ ⟨a, x⟩ w` has the tensor `a ⊗ w`,
  so the equivalence is the one induced by the dot product.
* `TauCeti.boundaryTensorEquiv_piTensorProductMap_comp_comp`: multiplying by the tensor powers of
  a matrix on the outputs and of its transpose on the inputs is the action on all the slots.
* `TauCeti.boundaryTensorEquiv_tensorPower_mul_mul`: for an element of the orthogonal group,
  conjugation is the action on all the slots.
* `TauCeti.boundaryTensorEquiv_mem_invariants_iff`: `f` lies in the commutant of the orthogonal
  group exactly when its tensor is invariant.
* `TauCeti.BrauerDiagram.reindex_matchingTensor`: permuting the slots permutes the matching tensors.
* `TauCeti.BrauerDiagram.piTensorProductMap_matchingTensor` and
  `TauCeti.BrauerDiagram.matchingTensor_mem_invariants`: the matching tensors are invariant.
* `TauCeti.boundaryTensorEquiv_brauerActionOrth_of`: a diagram acts through its matching tensor.
* `TauCeti.range_brauerActionOrth_eq_centralizer_iff`: **the bridge**, from Brauer's duality to the
  spanning of the invariant tensors by the matching tensors.
* `TauCeti.invariants_eq_span_matchingTensor_two`: over a field of characteristic zero, the matching
  tensors span the invariants on two strands.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §5.3.2 and §10.1.
* S. Doty and J. Hu, *Schur-Weyl duality for orthogonal groups*, Proc. London Math. Soc. 98 (2009),
  679-713.
-/

public section

open scoped Matrix TensorProduct

namespace TauCeti

universe u

section CommSemiring

variable (R : Type u) [CommSemiring R] (n k : ℕ)

/-- The monomial basis of the tensor power of `Rⁿ` with one slot for each boundary point of a Brauer
diagram on `k` strands: the basis vector at a labelling `ℓ` is the pure tensor whose factor at the
boundary point `x` is the `ℓ x`-th standard basis vector. -/
noncomputable def boundaryTensorBasis :
    Module.Basis (Fin k ⊕ Fin k → Fin n) R (⨂[R] _ : Fin k ⊕ Fin k, Fin n → R) :=
  Basis.piTensorProduct fun _ => Pi.basisFun R (Fin n)

@[simp]
theorem boundaryTensorBasis_apply (ℓ : Fin k ⊕ Fin k → Fin n) :
    boundaryTensorBasis R n k ℓ = PiTensorProduct.tprod R fun x => Pi.single (ℓ x) (1 : R) := by
  rw [boundaryTensorBasis, Basis.piTensorProduct_apply]
  simp

variable {R n k} in
/-- The coordinates of a pure tensor in the monomial basis are the products of the coordinates of
its factors. -/
theorem repr_boundaryTensorBasis_tprod (x : Fin k ⊕ Fin k → Fin n → R)
    (ℓ : Fin k ⊕ Fin k → Fin n) :
    (boundaryTensorBasis R n k).repr (PiTensorProduct.tprod R x) ℓ = ∏ s, x s (ℓ s) := by
  rw [boundaryTensorBasis, Basis.piTensorProduct_repr_tprod_apply]
  simp

variable {R n k} in
/-- The coordinates of the tensor product of two tensors, one on the input slots and one on the
output slots, are the products of their coordinates. -/
@[simp]
theorem repr_tmulEquiv_tmul (a x : ⨂[R] _ : Fin k, Fin n → R) (u v : Fin k → Fin n) :
    (boundaryTensorBasis R n k).repr (PiTensorProduct.tmulEquiv R (Fin n → R) (a ⊗ₜ[R] x))
        (Sum.elim u v) =
      (tensorPowerBasis R n k).repr a u * (tensorPowerBasis R n k).repr x v := by
  induction a using PiTensorProduct.induction_on with
  | add a₁ a₂ h₁ h₂ =>
    simp only [TensorProduct.add_tmul, map_add, Finsupp.add_apply, h₁, h₂, add_mul]
  | smul_tprod r a =>
    induction x using PiTensorProduct.induction_on with
    | add x₁ x₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, h₁, h₂, mul_add]
    | smul_tprod s x =>
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul,
        PiTensorProduct.tmulEquiv_apply, Finsupp.smul_apply, smul_eq_mul,
        repr_boundaryTensorBasis_tprod, tensorPowerBasis_def,
        Basis.piTensorProduct_repr_tprod_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.basisFun_repr]
      ring

/-- Two boundary tensors are equal when their coordinates agree at every labelling
`Sum.elim u v`. -/
private theorem boundaryTensor_ext {x y : ⨂[R] _ : Fin k ⊕ Fin k, Fin n → R}
    (h : ∀ u v, (boundaryTensorBasis R n k).repr x (Sum.elim u v) =
      (boundaryTensorBasis R n k).repr y (Sum.elim u v)) : x = y :=
  (boundaryTensorBasis R n k).ext_elem fun ℓ => by
    simpa only [Sum.elim_comp_inl_inr] using h (ℓ ∘ Sum.inl) (ℓ ∘ Sum.inr)

/-- **An endomorphism of `(Rⁿ)^{⊗k}` as a tensor with `2 * k` slots**, indexed by the boundary
points of a Brauer diagram. It is Mathlib's contraction `dualTensorHomEquivOfBasis` of
`Module.Dual R T ⊗[R] T` for `T = (Rⁿ)^{⊗k}`, followed by the identification of `T` with its dual
through the monomial basis and by the concatenation `PiTensorProduct.tmulEquiv` of the input slots
and the output slots. By `TauCeti.boundaryTensorEquiv_dualTensorHom` the identification of `T` with
its dual is the one induced by the dot product on `Rⁿ`. -/
noncomputable def boundaryTensorEquiv :
    Module.End R (⨂[R] _ : Fin k, Fin n → R) ≃ₗ[R] ⨂[R] _ : Fin k ⊕ Fin k, Fin n → R :=
  (dualTensorHomEquivOfBasis (tensorPowerBasis R n k)).symm.trans
    ((TensorProduct.congr (tensorPowerBasis R n k).toDualEquiv.symm (LinearEquiv.refl R _)).trans
      (PiTensorProduct.tmulEquiv R (Fin n → R)))

variable {R n k}

/-- The tensor of `f` is the sum over the monomial basis of the tensor products `e_u ⊗ f e_u` of the
inputs with their images. -/
theorem boundaryTensorEquiv_eq_sum (f : Module.End R (⨂[R] _ : Fin k, Fin n → R)) :
    boundaryTensorEquiv R n k f =
      ∑ u, PiTensorProduct.tmulEquiv R (Fin n → R)
        (tensorPowerBasis R n k u ⊗ₜ[R] f (tensorPowerBasis R n k u)) := by
  have hsymm : (dualTensorHomEquivOfBasis (tensorPowerBasis R n k)).symm f =
      ∑ u, (tensorPowerBasis R n k).toDual (tensorPowerBasis R n k u) ⊗ₜ[R]
        f (tensorPowerBasis R n k u) := by
    rw [LinearEquiv.symm_apply_eq, map_sum]
    refine LinearMap.ext fun x => ?_
    conv_lhs => rw [← (tensorPowerBasis R n k).sum_repr x, map_sum]
    rw [LinearMap.sum_apply]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [dualTensorHomEquivOfBasis_apply, dualTensorHom_apply, Module.Basis.toDual_apply_right,
      map_smul]
  rw [boundaryTensorEquiv, LinearEquiv.trans_apply, hsymm, LinearEquiv.trans_apply, map_sum,
    map_sum]
  refine Fintype.sum_congr _ _ fun u => ?_
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- The entries of the tensor of `f` are the entries of the matrix of `f`: the entry at the
labelling `Sum.elim u v`, with `u` on the input slots and `v` on the output slots, is the
coefficient of the basis tensor `e_v` in `f e_u`. -/
@[simp]
theorem repr_boundaryTensorEquiv (f : Module.End R (⨂[R] _ : Fin k, Fin n → R))
    (u v : Fin k → Fin n) :
    (boundaryTensorBasis R n k).repr (boundaryTensorEquiv R n k f) (Sum.elim u v) =
      LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k) f v u := by
  simp only [boundaryTensorEquiv_eq_sum, map_sum, Finsupp.finsetSum_apply, repr_tmulEquiv_tmul,
    Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, LinearMap.toMatrix_apply]

/-- The coordinates of a boundary tensor after applying a matrix in every slot. -/
private theorem repr_piTensorProductMap (A : Matrix (Fin n) (Fin n) R)
    (x : ⨂[R] _ : Fin k ⊕ Fin k, Fin n → R) (ℓ : Fin k ⊕ Fin k → Fin n) :
    (boundaryTensorBasis R n k).repr (PiTensorProduct.map (fun _ => A.mulVecLin) x) ℓ =
      ∑ m, (∏ s, A (ℓ s) (m s)) * (boundaryTensorBasis R n k).repr x m := by
  have h := LinearMap.toMatrix_mulVec_repr (boundaryTensorBasis R n k) (boundaryTensorBasis R n k)
    (PiTensorProduct.map fun _ : Fin k ⊕ Fin k => A.mulVecLin) x
  rw [boundaryTensorBasis, A.toMatrix_piTensorProductMap_mulVecLin] at h
  simpa only [boundaryTensorBasis, Matrix.mulVec, dotProduct, Matrix.kroneckerPower_apply] using
    (congrFun h ℓ).symm

/-- **Two-sided multiplication is the action on all the slots.** Composing `f` with the tensor power
of `A` on the outputs and of its transpose on the inputs applies `A` in all `2 * k` slots of the
tensor of `f`. The inputs carry the transpose because the input slots of the tensor are identified
with the dual through the dot product. For an orthogonal `A` this is conjugation
(`TauCeti.boundaryTensorEquiv_tensorPower_mul_mul`). -/
theorem boundaryTensorEquiv_piTensorProductMap_comp_comp (A : Matrix (Fin n) (Fin n) R)
    (f : Module.End R (⨂[R] _ : Fin k, Fin n → R)) :
    boundaryTensorEquiv R n k
        ((PiTensorProduct.map fun _ : Fin k => A.mulVecLin) ∘ₗ f ∘ₗ
          PiTensorProduct.map fun _ : Fin k => Aᵀ.mulVecLin) =
      PiTensorProduct.map (fun _ : Fin k ⊕ Fin k => A.mulVecLin) (boundaryTensorEquiv R n k f) := by
  refine boundaryTensor_ext R n k fun u v => ?_
  have hprod : ∀ u' v' : Fin k → Fin n,
      ∏ s, A (Sum.elim u v s) (Sum.elim u' v' s) =
        A.kroneckerPower (Fin k) v v' * A.kroneckerPower (Fin k) u u' := fun u' v' => by
    rw [Fintype.prod_sum_type, mul_comm]
    simp [Matrix.kroneckerPower_apply]
  have hsymm : ∀ p : (Fin k → Fin n) × (Fin k → Fin n),
      (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (Fin n)).symm p = Sum.elim p.1 p.2 := fun p =>
    funext fun x => by cases x <;> rfl
  rw [repr_piTensorProductMap, repr_boundaryTensorEquiv, LinearMap.toMatrix_comp _
      (tensorPowerBasis R n k), LinearMap.toMatrix_comp _ (tensorPowerBasis R n k),
    A.toMatrix_piTensorProductMap_tensorPowerBasis, Aᵀ.toMatrix_piTensorProductMap_tensorPowerBasis,
    ← Matrix.transpose_kroneckerPower, ← Matrix.mul_assoc,
    ← (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, hsymm, hprod,
    repr_boundaryTensorEquiv]
  exact Fintype.sum_congr _ _ fun u' => Fintype.sum_congr _ _ fun v' => by ring

namespace BrauerDiagram

variable (R n) in
/-- **The matching tensor of a Brauer diagram**: the tensor product, over the arcs of `D`, of the
copairing `∑ c, e_c ⊗ e_c` of the dot product placed in the two slots of the arc. Expanding the
product, it is the sum of the monomial tensors whose labelling is constant on the arcs of `D`
(`TauCeti.BrauerDiagram.matchingTensor_eq_sum_tprod` indexes this sum by the labels of the arcs). -/
noncomputable def matchingTensor (D : BrauerDiagram k) : ⨂[R] _ : Fin k ⊕ Fin k, Fin n → R :=
  ∑ m with D.IsConstantOnArcs m, boundaryTensorBasis R n k m

/-- The entry of a matching tensor at a labelling is `1` when the labelling is constant on the arcs
of the diagram, and `0` otherwise. -/
@[simp]
theorem repr_matchingTensor (D : BrauerDiagram k) (ℓ : Fin k ⊕ Fin k → Fin n) :
    (boundaryTensorBasis R n k).repr (D.matchingTensor R n) ℓ =
      if D.IsConstantOnArcs ℓ then 1 else 0 := by
  simp only [matchingTensor, map_sum, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The matching tensor as a product over the arcs.** A labelling constant on the arcs is a free
choice of one label per arc, so the matching tensor is the sum, over these choices, of the pure
tensors carrying at each slot the basis vector of the label of its arc. -/
theorem matchingTensor_eq_sum_tprod (D : BrauerDiagram k) :
    D.matchingTensor R n =
      ∑ g : {x // D.IsLowerEnd x} → Fin n, PiTensorProduct.tprod R fun x =>
        Pi.single ((D.isConstantOnArcsEquiv.symm g).1 x) (1 : R) := by
  rw [matchingTensor, Finset.sum_subtype (p := D.IsConstantOnArcs) _ (fun m => by simp),
    ← (D.isConstantOnArcsEquiv (ι := Fin n)).symm.sum_comp]
  exact Fintype.sum_congr _ _ fun g => boundaryTensorBasis_apply R n k _

/-- **Permuting the slots permutes the matching tensors.** Reindexing the matching tensor of `D` by
a permutation `π` of the slots gives the matching tensor of the diagram transported along `π`. -/
theorem reindex_matchingTensor (π : Equiv.Perm (Fin k ⊕ Fin k)) (D : BrauerDiagram k) :
    PiTensorProduct.reindex R (fun _ => Fin n → R) π (D.matchingTensor R n) =
      matchingTensor R n (PerfectMatching.congr π D) := by
  rw [matchingTensor, matchingTensor, map_sum]
  refine Finset.sum_equiv (π.arrowCongr (Equiv.refl _)) (fun m => ?_) fun m _ => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (isConstantOnArcs_congr_comp_symm_iff π D m).symm
  · simp [PiTensorProduct.reindex_tprod, Equiv.arrowCongr]

/-- Renaming the input and output slots by permutations `σ` and `τ` carries the matching tensor of
`D` to the matching tensor of the relabelled diagram. -/
theorem matchingTensor_relabel (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).matchingTensor R n =
      PiTensorProduct.reindex R (fun _ => Fin n → R) (Equiv.Perm.sumCongr σ τ)
        (D.matchingTensor R n) := by
  rw [relabel_def, reindex_matchingTensor]

/-- **The matching tensors are invariant.** A matrix `A` with `A * Aᵀ = 1`, acting in every slot,
fixes each matching tensor. -/
theorem piTensorProductMap_matchingTensor (D : BrauerDiagram k) {A : Matrix (Fin n) (Fin n) R}
    (hA : A * Aᵀ = 1) :
    PiTensorProduct.map (fun _ => A.mulVecLin) (D.matchingTensor R n) = D.matchingTensor R n := by
  refine (boundaryTensorBasis R n k).ext_elem fun ℓ => ?_
  rw [repr_piTensorProductMap, repr_matchingTensor, ← D.sum_isConstantOnArcs_prod_apply hA,
    Finset.sum_filter]
  exact Fintype.sum_congr _ _ fun m => by simp [repr_matchingTensor]

end BrauerDiagram

/-- **A Brauer diagram acts through its matching tensor.** The tensor of the operator by which `D`
acts on `(Rⁿ)^{⊗k}` is the matching tensor of `D`. -/
@[simp]
theorem boundaryTensorEquiv_brauerActionOrth_of (D : BrauerDiagram k) :
    boundaryTensorEquiv R n k (brauerActionOrth R n k (BrauerAlgebra.of D)) =
      D.matchingTensor R n := by
  refine boundaryTensor_ext R n k fun u v => ?_
  rw [repr_boundaryTensorEquiv, brauerActionOrth_of, LinearMap.toMatrix_toLin,
    BrauerDiagram.repr_matchingTensor, BrauerDiagram.orthogonalActionMatrix_apply]

variable (R n k) in
/-- **The image of the Brauer algebra is the span of the matching tensors.** Under
`TauCeti.boundaryTensorEquiv`, the operators by which the Brauer algebra acts correspond to the
combinations of matching tensors. -/
theorem map_range_brauerActionOrth :
    (Subalgebra.toSubmodule (brauerActionOrth R n k).range).map
        (boundaryTensorEquiv R n k).toLinearMap =
      Submodule.span R (Set.range fun D : BrauerDiagram k => D.matchingTensor R n) := by
  have hrange : (Subalgebra.toSubmodule (brauerActionOrth R n k).range) =
      LinearMap.range (brauerActionOrth R n k).toLinearMap := by
    ext x
    simp
  rw [hrange, ← LinearMap.range_comp, LinearMap.range_eq_map,
    ← (BrauerAlgebra.basis R (n : R) k).span_eq, Submodule.map_span, ← Set.range_comp]
  congr 2
  ext D
  simp [BrauerAlgebra.basis_apply]

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {n k : ℕ}

/-- **The tensor of a rank-one operator.** For a pure tensor `a` and a tensor `w`, the operator
`x ↦ ⟨a, x⟩ w`, where `⟨a, -⟩` is the product over the slots of the dot products with the factors of
`a`, has the tensor `a ⊗ w`. Since pure tensors span, this says that
`TauCeti.boundaryTensorEquiv` identifies `End T` with `Dual T ⊗ T`, the dual `Dual T` with the
tensor power of `Dual V`, and `Dual V` with `V` by the dot product
`TauCeti.stdOrthogonalRepToDual` in every input slot, for `V = Rⁿ` and `T = V^{⊗k}`. -/
theorem boundaryTensorEquiv_dualTensorHom (a : Fin k → Fin n → R) (w : ⨂[R] _ : Fin k, Fin n → R) :
    boundaryTensorEquiv R n k (dualTensorHom R _ _
        (PiTensorProduct.dualDistrib (PiTensorProduct.tprod R fun i =>
          stdOrthogonalRepToDual R n (a i)) ⊗ₜ[R] w)) =
      PiTensorProduct.tmulEquiv R (Fin n → R) (PiTensorProduct.tprod R a ⊗ₜ[R] w) := by
  have hdual : PiTensorProduct.dualDistrib (PiTensorProduct.tprod R fun i =>
      stdOrthogonalRepToDual R n (a i)) =
        (tensorPowerBasis R n k).toDualEquiv (PiTensorProduct.tprod R a) := by
    refine (tensorPowerBasis R n k).ext fun u => ?_
    rw [Module.Basis.toDualEquiv_apply, Module.Basis.toDual_apply_left, tensorPowerBasis_apply,
      PiTensorProduct.dualDistrib_apply, tensorPowerBasis_def,
      Basis.piTensorProduct_repr_tprod_apply]
    simp [stdOrthogonalRepToDual_apply]
  rw [boundaryTensorEquiv, LinearEquiv.trans_apply, ← dualTensorHomEquivOfBasis_apply
      (tensorPowerBasis R n k), LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, hdual, LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply]

/-- **Equivariance of the identification.** For `g` in the orthogonal group, conjugating `f` by the
action of `g` on `(Rⁿ)^{⊗k}` acts on the tensor of `f` by `g` in all `2 * k` slots. -/
theorem boundaryTensorEquiv_tensorPower_mul_mul (g : Matrix.orthogonalGroup (Fin n) R)
    (f : Module.End R (⨂[R] _ : Fin k, Fin n → R)) :
    boundaryTensorEquiv R n k
        ((stdOrthogonalRep R n).tensorPower k g * f * (stdOrthogonalRep R n).tensorPower k g⁻¹) =
      Representation.piTensorProduct (fun _ : Fin k ⊕ Fin k => stdOrthogonalRep R n) g
        (boundaryTensorEquiv R n k f) := by
  have hinv : ((g⁻¹ : Matrix.orthogonalGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (g : Matrix (Fin n) (Fin n) R)ᵀ :=
    left_inv_eq_right_inv (congrArg Subtype.val (inv_mul_cancel g))
      ((Matrix.mem_orthogonalGroup_iff (Fin n) R).mp g.2)
  simp only [Representation.piTensorProduct_apply, Representation.tensorPower_apply,
    stdOrthogonalRep_apply, hinv, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  exact boundaryTensorEquiv_piTensorProductMap_comp_comp _ f

/-- **The commutant is the invariant tensors.** An endomorphism of `(Rⁿ)^{⊗k}` commutes with the
orthogonal group exactly when its tensor is invariant under the diagonal action on the `2 * k`
slots. -/
theorem boundaryTensorEquiv_mem_invariants_iff (f : Module.End R (⨂[R] _ : Fin k, Fin n → R)) :
    boundaryTensorEquiv R n k f ∈
        (Representation.piTensorProduct fun _ : Fin k ⊕ Fin k => stdOrthogonalRep R n).invariants ↔
      f ∈ Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) := by
  set T := (stdOrthogonalRep R n).tensorPower k
  have hT : ∀ g, T g⁻¹ * T g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hT' : ∀ g, T g * T g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  rw [Representation.mem_invariants, Subalgebra.mem_centralizer_iff]
  refine ⟨fun h => ?_, fun h g => ?_⟩
  · rintro _ ⟨g, rfl⟩
    have hconj : T g * f * T g⁻¹ = f := (boundaryTensorEquiv R n k).injective <| by
      rw [boundaryTensorEquiv_tensorPower_mul_mul, h]
    calc T g * f = T g * f * (T g⁻¹ * T g) := by rw [hT, mul_one]
      _ = f * T g := by rw [← mul_assoc, hconj]
  · rw [← boundaryTensorEquiv_tensorPower_mul_mul, h _ ⟨g, rfl⟩, mul_assoc, hT', mul_one]

/-- **The matching tensors are invariant under the orthogonal group.** -/
theorem BrauerDiagram.matchingTensor_mem_invariants (D : BrauerDiagram k) :
    D.matchingTensor R n ∈
      (Representation.piTensorProduct fun _ : Fin k ⊕ Fin k => stdOrthogonalRep R n).invariants :=
  (Representation.mem_invariants _ _).mpr fun g => by
    simp only [Representation.piTensorProduct_apply, stdOrthogonalRep_apply]
    exact D.piTensorProductMap_matchingTensor ((Matrix.mem_orthogonalGroup_iff (Fin n) R).mp g.2)

variable (R n k) in
/-- **The commutant corresponds to the invariant tensors**, as submodules: the image under
`TauCeti.boundaryTensorEquiv` of the commutant of the orthogonal group on `(Rⁿ)^{⊗k}` is the space
of invariants of the diagonal action on the `2 * k` slots. -/
theorem map_centralizer_tensorPower :
    (Subalgebra.toSubmodule
        (Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)))).map
        (boundaryTensorEquiv R n k).toLinearMap =
      (Representation.piTensorProduct fun _ : Fin k ⊕ Fin k =>
        stdOrthogonalRep R n).invariants := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (boundaryTensorEquiv_mem_invariants_iff f).mpr hf
  · intro hx
    refine ⟨(boundaryTensorEquiv R n k).symm x, ?_, LinearEquiv.apply_symm_apply _ x⟩
    exact (boundaryTensorEquiv_mem_invariants_iff _).mp (by simpa using hx)

variable (R n k) in
/-- **The invariant-tensor bridge.** The image of the Brauer algebra `B_k(n)` is the whole commutant
of the orthogonal group on `(Rⁿ)^{⊗k}` if and only if the matching tensors span the invariants of
the orthogonal group in the tensor power with `2 * k` slots. -/
theorem range_brauerActionOrth_eq_centralizer_iff :
    (brauerActionOrth R n k).range =
        Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) ↔
      (Representation.piTensorProduct fun _ : Fin k ⊕ Fin k => stdOrthogonalRep R n).invariants =
        Submodule.span R (Set.range fun D : BrauerDiagram k => D.matchingTensor R n) := by
  rw [← map_centralizer_tensorPower, ← map_range_brauerActionOrth, eq_comm]
  refine ⟨fun h => by rw [h], fun h => Subalgebra.toSubmodule_injective ?_⟩
  exact Submodule.map_injective_of_injective (boundaryTensorEquiv R n k).injective h

/-- **The tensor theorem on two strands.** Over a field of characteristic zero, the invariants of
the orthogonal group in the fourth tensor power of the standard module are spanned by the three
matching tensors, by Brauer's duality on the tensor square. -/
theorem invariants_eq_span_matchingTensor_two (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    (Representation.piTensorProduct fun _ : Fin 2 ⊕ Fin 2 => stdOrthogonalRep K n).invariants =
      Submodule.span K (Set.range fun D : BrauerDiagram 2 => D.matchingTensor K n) :=
  (range_brauerActionOrth_eq_centralizer_iff K n 2).mp
    (range_brauerActionOrth_two_eq_centralizer K n)

end CommRing

end TauCeti
