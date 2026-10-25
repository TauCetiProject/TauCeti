/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.TensorProduct
public import TauCeti.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal

/-!
# Tensor induction of tensor products

Tensor induction takes tensor products to tensor products. For representations `ρ` and `τ` of a
subgroup `U ≤ G` of finite index and a transversal `s`,

```text
Ind⊗_U^G (ρ ⊗ τ) ≃ Ind⊗_U^G ρ ⊗ Ind⊗_U^G τ,     ⨂ₜ (mₓ ⊗ₜ nₓ) ↦ (⨂ₜ mₓ) ⊗ₜ (⨂ₜ nₓ),
```

as representations of `G`. The underlying linear equivalence is
`PiTensorProduct.tensorDistribEquiv`. It is equivariant already for the wreath product
`(ι → D) ⋊ Perm ι` acting on tensor powers, since that action applies a linear map in every
factor and then permutes the factors; tensor induction is its restriction along the monomial
homomorphism.

The equivalence is natural in both representations, so that tensor induction of a pairing
`ρ ⊗ τ → υ` gives a pairing `Ind⊗ ρ ⊗ Ind⊗ τ → Ind⊗ υ`. It carries the diagonal tensor of
`x ⊗ₜ y` to the tensor product of the diagonal tensors of `x` and `y`. These are the
representative-level inputs for the multiplicativity of Evens' norm map
`N(x ⌣ y) = N(x) ⌣ N(y)`, where the cup product is induced by such a pairing.

## Main definitions

* `Representation.wreathTensorTprodEquiv`: the wreath tensor power of `ρ ⊗ τ` is the tensor
  product of the wreath tensor powers.
* `Subgroup.tensorInducedTprodEquiv`: tensor induction of `ρ ⊗ τ` is the tensor product of the
  tensor inductions.

## Main results

* `Subgroup.tensorInducedTprodEquiv_naturality`: naturality in both representations.
* `Representation.tensorInducedTprodEquiv_tensorInducedDiagonal`: the diagonal of `x ⊗ₜ y` is
  sent to the tensor product of the diagonals.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–6.
-/

public section

open scoped TensorProduct

universe u v w x y z

namespace Representation

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] {N : Type y} [AddCommMonoid N] [Module R N]

/-- The wreath tensor power of a tensor product of representations is the tensor product of the
wreath tensor powers. The index type must be finite. -/
noncomputable def wreathTensorTprodEquiv (ρ : Representation R D M) (τ : Representation R D N)
    (ι : Type x) [Finite ι] :
    ((ρ.tprod τ).wreathTensor ι).Equiv ((ρ.wreathTensor ι).tprod (τ.wreathTensor ι)) :=
  Representation.Equiv.mk (PiTensorProduct.tensorDistribEquiv R (fun _ : ι ↦ M) fun _ ↦ N)
    fun a ↦ by
      apply PiTensorProduct.ext_tprod_tmul
      intro m n
      simp [Representation.tprod_apply]

/-- On pure tensors of tensor products, the wreath comparison separates the two components. -/
@[simp]
theorem wreathTensorTprodEquiv_apply_tprod (ρ : Representation R D M)
    (τ : Representation R D N) (ι : Type x) [Finite ι] (m : ι → M) (n : ι → N) :
    ρ.wreathTensorTprodEquiv τ ι (PiTensorProduct.tprod R fun i ↦ m i ⊗ₜ n i) =
      PiTensorProduct.tprod R m ⊗ₜ PiTensorProduct.tprod R n :=
  PiTensorProduct.tensorDistribEquiv_tprod m n

end Representation

namespace Subgroup

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G] {U : Subgroup G}
  {M : Type w} [AddCommMonoid M] [Module R M] {N : Type y} [AddCommMonoid N] [Module R N]

/-- **Tensor induction takes tensor products to tensor products.** For a subgroup of finite
index, tensor induction of `ρ ⊗ τ` along a transversal is the tensor product of the tensor
inductions of `ρ` and `τ` along the same transversal. -/
noncomputable def tensorInducedTprodEquiv (s : U.LeftTransversal) [Finite (G ⧸ U)]
    (ρ : Representation R U M) (τ : Representation R U N) :
    (U.tensorInducedRepresentation s (ρ.tprod τ)).Equiv
      ((U.tensorInducedRepresentation s ρ).tprod (U.tensorInducedRepresentation s τ)) :=
  Representation.Equiv.mk
    (PiTensorProduct.tensorDistribEquiv R (fun _ : G ⧸ U ↦ M) fun _ ↦ N) fun g ↦ by
      -- Tensor induction is the wreath tensor action pulled back along the monomial
      -- homomorphism, so the wreath-product equivariance applies at `U.monomialHom s g`.
      rw [Representation.tprod_apply,
        LinearMap.ext (U.tensorInducedRepresentation_apply s (ρ.tprod τ) g),
        LinearMap.ext (U.tensorInducedRepresentation_apply s ρ g),
        LinearMap.ext (U.tensorInducedRepresentation_apply s τ g)]
      exact (ρ.wreathTensorTprodEquiv τ (G ⧸ U)).isIntertwining' (U.monomialHom s g)

/-- On pure tensors of tensor products, the comparison separates the two components. -/
@[simp]
theorem tensorInducedTprodEquiv_apply_tprod (s : U.LeftTransversal) [Finite (G ⧸ U)]
    (ρ : Representation R U M) (τ : Representation R U N) (m : G ⧸ U → M) (n : G ⧸ U → N) :
    U.tensorInducedTprodEquiv s ρ τ (PiTensorProduct.tprod R fun x ↦ m x ⊗ₜ n x) =
      PiTensorProduct.tprod R m ⊗ₜ PiTensorProduct.tprod R n :=
  PiTensorProduct.tensorDistribEquiv_tprod m n

/-- The inverse comparison pairs up the factors of two pure tensors. -/
@[simp]
theorem tensorInducedTprodEquiv_symm_apply_tmul (s : U.LeftTransversal) [Finite (G ⧸ U)]
    (ρ : Representation R U M) (τ : Representation R U N) (m : G ⧸ U → M) (n : G ⧸ U → N) :
    (U.tensorInducedTprodEquiv s ρ τ).symm
        (PiTensorProduct.tprod R m ⊗ₜ PiTensorProduct.tprod R n) =
      PiTensorProduct.tprod R fun x ↦ m x ⊗ₜ n x :=
  PiTensorProduct.tensorDistribEquiv_symm_tmul m n

/-- The comparison is natural in both representations: tensor induction of a tensor product of
intertwining maps corresponds to the tensor product of their tensor inductions. -/
theorem tensorInducedTprodEquiv_naturality (s : U.LeftTransversal) [Finite (G ⧸ U)]
    {M' : Type z} [AddCommMonoid M'] [Module R M'] {N' : Type x} [AddCommMonoid N']
    [Module R N'] {ρ : Representation R U M} {τ : Representation R U N}
    {ρ' : Representation R U M'} {τ' : Representation R U N'}
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') :
    (U.tensorInducedTprodEquiv s ρ' τ').toIntertwiningMap.comp ((f.tensor g).tensorInduced s) =
      ((f.tensorInduced s).tensor (g.tensorInduced s)).comp
        (U.tensorInducedTprodEquiv s ρ τ).toIntertwiningMap := by
  apply Representation.IntertwiningMap.ext
  apply PiTensorProduct.ext_tprod_tmul
  intro m n
  simp

end Subgroup

namespace Representation

variable {R : Type u} [CommRing R] {G : Type v} [Group G] {U : Subgroup G}
  {M : Type w} [AddCommGroup M] [Module R M] {N : Type y} [AddCommGroup N] [Module R N]

/-- The comparison for tensor products sends the diagonal tensor of `x ⊗ₜ y` to the tensor
product of the diagonal tensors of `x` and `y`. On representatives, this is the multiplicativity
of the diagonal construction underlying Evens' norm map. -/
theorem tensorInducedTprodEquiv_tensorInducedDiagonal (s : U.LeftTransversal)
    [Finite (G ⧸ U)] (ρ : Representation R U M) (τ : Representation R U N)
    (x : ρ.invariants) (y : τ.invariants) :
    U.tensorInducedTprodEquiv s ρ τ
        ((ρ.tprod τ).tensorInducedDiagonal s
          ⟨_, tmul_mem_invariants_tprod x.property y.property⟩) =
      (ρ.tensorInducedDiagonal s x : ⨂[R] _ : G ⧸ U, M) ⊗ₜ
        (τ.tensorInducedDiagonal s y : ⨂[R] _ : G ⧸ U, N) := by
  simp only [coe_tensorInducedDiagonal]
  exact Subgroup.tensorInducedTprodEquiv_apply_tprod s ρ τ (fun _ ↦ x) (fun _ ↦ y)

end Representation
