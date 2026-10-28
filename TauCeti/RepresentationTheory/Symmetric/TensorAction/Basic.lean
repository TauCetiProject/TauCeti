/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.Matrix.KroneckerPower

/-!
# Permuting tensor factors

This file defines the symmetric-group action on a power of a module by permuting its tensor
factors. Mathlib's `Representation.asAlgebraHom` then extends the action linearly to the group
algebra, which is the action used by Young symmetrizers.

The construction is the first target in Layer 2 of the
[classical-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
and the first construction in Layer 8 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md).
It reuses `PiTensorProduct.reindex`; the convention is
`σ • (⨂ₜ i, m i) = ⨂ₜ i, m (σ⁻¹ i)`.

## Main definitions

* `PiTensorProduct.reindexRepresentation` is the permutation action for an arbitrary index type
  and module.
* `permTensorAction` specializes it to `(Fin n → R)^{⊗d}`.
* `permTensorActionAlgHom` is its `Representation.asAlgebraHom` extension to `R[S_d]`.
* `TauCeti.tensorPowerBasis` is the monomial basis of `(Rⁿ)^{⊗d}`, on which the action is a
  reindexing.

## Main results

* `TauCeti.finrank_tensorPower` is the dimension count `dim (Rⁿ)^{⊗d} = nᵈ` that the monomial
  basis supplies.
* `Matrix.piTensorProductMap_tensorPowerBasis` and
  `Matrix.toMatrix_piTensorProductMap_tensorPowerBasis`: in the monomial basis, a matrix `A` acting
  in every tensor factor has the Kronecker power `Matrix.kroneckerPower (Fin d) A` as its matrix.
* `PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom` transports the image of
  a group-algebra element along any equivalence of tensor-factor index types.
-/

public section

open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation group of `ι` on the `ι`-indexed tensor power,
acting by reindexing the tensor factors. -/
noncomputable def reindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) where
  toFun σ := (reindex R (fun _ : ι => M) σ).toLinearMap
  map_one' := by
    simpa only [Equiv.Perm.one_def, Module.End.one_eq_id,
      LinearEquiv.refl_toLinearMap] using
      congrArg LinearEquiv.toLinearMap
        (reindex_refl (R := R) (s := fun _ : ι => M))
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap]
    simpa only [Equiv.Perm.mul_def] using
      (reindex_reindex (R := R) (s := fun _ : ι => M) τ σ x).symm

/-- The permutation representation acts by `PiTensorProduct.reindex`. -/
@[simp]
theorem reindexRepresentation_apply (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ = (reindex R (fun _ : ι => M) σ).toLinearMap :=
  (rfl)

/-- Permuting factors commutes with applying the same linear map in every tensor factor. -/
theorem commute_reindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (reindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, reindexRepresentation_apply,
    LinearEquiv.coe_toLinearMap] using
    (map_reindex (f := fun _ : ι => f) σ x).symm

/-- Every element of the group algebra commutes with applying the same linear map in every
tensor factor. -/
theorem commute_reindexRepresentation_asAlgebraHom_map
    (a : MonoidAlgebra R (Equiv.Perm ι)) (f : M →ₗ[R] M) :
    Commute ((reindexRepresentation R M ι).asAlgebraHom a) (map fun _ : ι => f) := by
  induction a using MonoidAlgebra.induction_on with
  | of σ =>
    simpa only [Representation.asAlgebraHom_of] using commute_reindexRepresentation_map R M ι σ f
  | add a b ha hb => simpa only [map_add] using ha.add_left hb
  | smul r a ha => simpa only [map_smul] using ha.smul_left r

/-- The group-algebra action on a pure tensor is the corresponding finite linear combination
of reindexed pure tensors. -/
theorem reindexRepresentation_asAlgebraHom_apply_tprod
    (a : MonoidAlgebra R (Equiv.Perm ι)) (m : ι → M) :
    (reindexRepresentation R M ι).asAlgebraHom a (tprod R m) =
      a.coeff.sum fun σ r => r • tprod R (fun i => m (σ.symm i)) := by
  classical
  simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]

/-- Relabeling tensor factors along an equivalence transports the image of a group-algebra
element onto the image of its transport to the permutation group of the new index type. -/
theorem map_reindex_range_reindexRepresentation_asAlgebraHom {κ : Type*} (e : ι ≃ κ)
    (a : MonoidAlgebra R (Equiv.Perm ι)) :
    (LinearMap.range ((reindexRepresentation R M ι).asAlgebraHom a)).map
        (reindex R (fun _ => M) e : (⨂[R] _ : ι, M) →ₗ[R] (⨂[R] _ : κ, M)) =
      LinearMap.range ((reindexRepresentation R M κ).asAlgebraHom
        (MonoidAlgebra.domCongr R R e.permCongrHom a)) := by
  have h :
      (reindex R (fun _ => M) e).toLinearMap ∘ₗ
          (reindexRepresentation R M ι).asAlgebraHom a =
        (reindexRepresentation R M κ).asAlgebraHom
            (MonoidAlgebra.domCongr R R e.permCongrHom a) ∘ₗ
          (reindex R (fun _ => M) e).toLinearMap := by
    induction a using MonoidAlgebra.induction_on with
    | of σ =>
      ext f
      simp [MonoidAlgebra.of_apply, Equiv.permCongrHom_coe, Equiv.permCongr_def,
        ← Equiv.trans_assoc]
    | add a b ha hb => simp [ha, hb, LinearMap.comp_add, LinearMap.add_comp]
    | smul r a ha => simp [ha, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [← LinearMap.range_comp, h]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)

end PiTensorProduct

namespace TauCeti

variable (R : Type u) (n d : ℕ)
variable [CommSemiring R]

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` by permutation of tensor factors. -/
noncomputable def permTensorAction :
    Representation R (Equiv.Perm (Fin d)) (⨂[R] _ : Fin d, Fin n → R) :=
  PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d)

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` is the reindexing representation for the
index type `Fin d`. -/
theorem permTensorAction_def :
    permTensorAction R n d = PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) :=
  (rfl)

/-- A permutation acts on `(Fin n → R)^{⊗d}` by `PiTensorProduct.reindex`. -/
@[simp]
theorem permTensorAction_apply (σ : Equiv.Perm (Fin d)) :
    permTensorAction R n d σ =
      (PiTensorProduct.reindex R (fun _ : Fin d => Fin n → R) σ).toLinearMap :=
  (rfl)

/-- The group-algebra action of `R[S_d]` on `(Fin n → R)^{⊗d}` induced by factor
permutations. -/
noncomputable def permTensorActionAlgHom :
    MonoidAlgebra R (Equiv.Perm (Fin d)) →ₐ[R]
      Module.End R (⨂[R] _ : Fin d, Fin n → R) :=
  (permTensorAction R n d).asAlgebraHom

/-- The group-algebra action of `R[S_d]` is the linear extension of `permTensorAction`. -/
theorem permTensorActionAlgHom_def :
    permTensorActionAlgHom R n d = (permTensorAction R n d).asAlgebraHom :=
  (rfl)

/-- A single permutation, viewed in the group algebra, acts by `permTensorAction`. -/
theorem permTensorActionAlgHom_of (σ : Equiv.Perm (Fin d)) :
    permTensorActionAlgHom R n d (MonoidAlgebra.of R (Equiv.Perm (Fin d)) σ) =
      permTensorAction R n d σ := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_of]

/-- The group-algebra action of `a ∈ R[S_d]` is the coefficient-weighted sum of the permutation
actions. -/
theorem permTensorActionAlgHom_eq_sum (a : MonoidAlgebra R (Equiv.Perm (Fin d))) :
    permTensorActionAlgHom R n d a = ∑ σ, a.coeff σ • permTensorAction R n d σ := by
  simp [permTensorActionAlgHom_def, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype]

/-- The group-algebra action on a pure tensor of `(Fin n → R)^{⊗d}` is the corresponding finite
linear combination of reindexed pure tensors. -/
@[simp]
theorem permTensorActionAlgHom_apply_tprod (a : MonoidAlgebra R (Equiv.Perm (Fin d)))
    (m : Fin d → (Fin n → R)) :
    permTensorActionAlgHom R n d a (PiTensorProduct.tprod R m) =
      a.coeff.sum fun σ r => r • PiTensorProduct.tprod R fun i => m (σ.symm i) := by
  rw [permTensorActionAlgHom_def, permTensorAction_def]
  exact PiTensorProduct.reindexRepresentation_asAlgebraHom_apply_tprod R (Fin n → R) (Fin d) a m

/-- Relabeling the tensor factors along `finCongr h`, for `h : m = d`, transports the image of
`a ∈ R[S_m]` onto the image of its transport to `R[S_d]`. -/
theorem map_reindex_range_permTensorAction_asAlgebraHom {m : ℕ} (h : m = d)
    (a : MonoidAlgebra R (Equiv.Perm (Fin m))) :
    (LinearMap.range ((permTensorAction R n m).asAlgebraHom a)).map
        (PiTensorProduct.reindex R (fun _ => Fin n → R) (finCongr h) :
          (⨂[R] _ : Fin m, Fin n → R) →ₗ[R] (⨂[R] _ : Fin d, Fin n → R)) =
      LinearMap.range ((permTensorAction R n d).asAlgebraHom
        (MonoidAlgebra.domCongr R R (finCongr h).permCongrHom a)) := by
  simpa only [permTensorAction_def] using
    PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom R (Fin n → R) (Fin m)
      (finCongr h) a

/-- The monomial basis of `(Rⁿ)^{⊗d}`: the basis vector at `f : Fin d → Fin n` is the pure tensor
whose `i`-th factor is the `f i`-th standard basis vector of `Rⁿ`. -/
noncomputable def tensorPowerBasis :
    Module.Basis (Fin d → Fin n) R (⨂[R] _ : Fin d, Fin n → R) :=
  Basis.piTensorProduct fun _ => Pi.basisFun R (Fin n)

/-- The monomial basis is the tensor product of the standard bases.  The definition is not
exposed, so this is its defining equation, used to compare it with the `Basis.piTensorProduct`
spelling of the weight theory. -/
theorem tensorPowerBasis_def :
    tensorPowerBasis R n d = Basis.piTensorProduct fun _ : Fin d => Pi.basisFun R (Fin n) :=
  (rfl)

@[simp]
theorem tensorPowerBasis_apply (f : Fin d → Fin n) :
    tensorPowerBasis R n d f = PiTensorProduct.tprod R fun i => Pi.single (f i) (1 : R) := by
  classical
  rw [tensorPowerBasis, Basis.piTensorProduct_apply]
  simp

/-- **The dimension of `(Rⁿ)^{⊗d}` is `nᵈ`**, read off the monomial basis
`TauCeti.tensorPowerBasis`, whose index type is `Fin d → Fin n`. -/
theorem finrank_tensorPower [StrongRankCondition R] :
    Module.finrank R (⨂[R] _ : Fin d, Fin n → R) = n ^ d := by
  rw [Module.finrank_eq_card_basis (tensorPowerBasis R n d), Fintype.card_fun]
  simp

/-- **A matrix acting diagonally on the monomial basis of `(Rⁿ)^{⊗d}`.** Applying `A` in every
tensor factor sends the basis tensor `e_u` to `∑ v, (∏ i, A (v i) (u i)) • e_v`, so its matrix in
the monomial basis is the Kronecker power of `A`. -/
theorem _root_.Matrix.piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R] {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (u : Fin d → Fin n) :
    PiTensorProduct.map (fun _ : Fin d => A.mulVecLin) (tensorPowerBasis R n d u) =
      ∑ v, A.kroneckerPower (Fin d) v u • tensorPowerBasis R n d v := by
  have hcol : ∀ i, A.mulVecLin (Pi.single (u i) (1 : R)) =
      ∑ c, A c (u i) • Pi.single c (1 : R) := fun i => by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ← (Pi.basisFun R (Fin n)).sum_repr
      (A.col (u i))]
    simp [Matrix.col_apply]
  simp only [tensorPowerBasis_apply, PiTensorProduct.map_tprod, hcol,
    MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  simp

/-- **The matrix of `A^{⊗d}` in the monomial basis is the Kronecker power of `A`.** The matrix of
`A` acting in every tensor factor of `(Rⁿ)^{⊗d}`, in the basis `TauCeti.tensorPowerBasis`, is
`Matrix.kroneckerPower (Fin d) A`. -/
theorem _root_.Matrix.toMatrix_piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R]
    {n d : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.toMatrix (tensorPowerBasis R n d) (tensorPowerBasis R n d)
        (PiTensorProduct.map fun _ : Fin d => A.mulVecLin) =
      A.kroneckerPower (Fin d) := by
  ext v u
  rw [LinearMap.toMatrix_apply, A.piTensorProductMap_tensorPowerBasis u, map_sum]
  simp [Finsupp.single_apply, -tensorPowerBasis_apply]

-- These two derived normal forms remain explicit rewrite lemmas: `simpNF` detects each as already
-- provable from the underlying tensor-action rules, so adding them to the simp set is redundant.
/-- A permutation acts on the monomial basis of `(Rⁿ)^{⊗d}` by precomposing the index function
with its inverse. -/
theorem permTensorAction_tensorPowerBasis (σ : Equiv.Perm (Fin d)) (f : Fin d → Fin n) :
    permTensorAction R n d σ (tensorPowerBasis R n d f) =
      tensorPowerBasis R n d fun i => f (σ.symm i) := by
  simp

/-- A group-algebra basis element acts on a monomial basis vector by precomposition and
scaling. -/
theorem permTensorActionAlgHom_single_tensorPowerBasis (ρ : Equiv.Perm (Fin d)) (r : R)
    (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d (MonoidAlgebra.single ρ r) (tensorPowerBasis R n d f) =
      r • tensorPowerBasis R n d fun i => f (ρ.symm i) := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    permTensorAction_tensorPowerBasis]

/-- The group-algebra action on a monomial basis vector is the coefficient-weighted sum of the
precomposed monomial basis vectors. -/
theorem permTensorActionAlgHom_apply_tensorPowerBasis
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d a (tensorPowerBasis R n d f) =
      ∑ σ ∈ a.coeff.support,
        a.coeff σ • tensorPowerBasis R n d fun i => f (σ.symm i) := by
  rw [tensorPowerBasis_apply, permTensorActionAlgHom_apply_tprod, Finsupp.sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [tensorPowerBasis_apply]

end TauCeti
