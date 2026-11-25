/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Coproduct tensors and finitely supported functions

Tensoring a module of finitely supported functions `ι →₀ M` over a bialgebra distributes over
the index type, compatibly with the coproduct action. In particular a coproduct tensor product
with a free module `ι →₀ H` is a direct sum of copies of the tensor product with `H`. This is
the step that reduces statements about tensor products with arbitrary projective modules to
the regular module.

The underlying equivalences are Mathlib's `TensorProduct.finsuppLeft` and
`TensorProduct.finsuppRight`. The inverse comparisons are sums of tensor products of the
insertions `Finsupp.lsingle`, which makes them `H`-linear. The finite-product analogues are
`TauCeti.BialgebraModule.piLeft` and `TauCeti.BialgebraModule.piRight`.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.BialgebraModule

variable (R H : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H]
variable (ι : Type*)
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module H N] [IsScalarTower R H N]

/-- Coproduct tensor products distribute over finitely supported functions in their left
factor. -/
def finsuppLeft : Tensor R H (ι →₀ M) N ≃ₗ[H] ι →₀ Tensor R H M N :=
  (LinearEquiv.ofBijective
    (Finsupp.lsum ℕ fun i => tensorMap R H (Finsupp.lsingle i) LinearMap.id)
    (by
      classical
      let e := (Finsupp.mapRange.linearEquiv (tensorEquiv R H M N)).trans
        ((TensorProduct.finsuppLeft R R M N ι).symm.trans (tensorEquiv R H (ι →₀ M) N).symm)
      convert e.bijective using 1
      ext x
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single i x =>
        induction x using Tensor.inductionOn with
        | htmul m n =>
          simp [e, TensorProduct.finsuppLeft_symm_apply_single]
        | hadd x y hx hy => simp only [Finsupp.single_add, map_add, hx, hy])).symm

/-- The inverse left comparison inserts a tensor into the corresponding coordinate of the
left factor. -/
@[simp] theorem finsuppLeft_symm_single (i : ι) (x : Tensor R H M N) :
    (finsuppLeft R H ι M N).symm (Finsupp.single i x) =
      tensorMap R H (Finsupp.lsingle i) LinearMap.id x := by
  simp [finsuppLeft]

/-- The left comparison evaluates pure tensors coordinatewise. -/
@[simp] theorem finsuppLeft_tmul (f : ι →₀ M) (n : N) (i : ι) :
    finsuppLeft R H ι M N (tmul R H f n) i = tmul R H (f i) n := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, hf, hg]
  | single j m =>
    have hs : tmul R H (Finsupp.single j m) n =
        (finsuppLeft R H ι M N).symm (Finsupp.single j (tmul R H m n)) := by simp
    rw [hs, LinearEquiv.apply_symm_apply]
    by_cases hji : j = i <;> simp [hji]

/-- Each coordinate of `finsuppLeft` is the tensor product of the corresponding evaluation
with the identity. -/
theorem finsuppLeft_apply (x : Tensor R H (ι →₀ M) N) (i : ι) :
    finsuppLeft R H ι M N x i = tensorMap R H (Finsupp.lapply i) LinearMap.id x := by
  induction x using Tensor.inductionOn with
  | htmul f n => simp
  | hadd x y hx hy => simp [hx, hy]

/-- The left comparison sends a pure tensor of a single to a single. -/
@[simp] theorem finsuppLeft_single_tmul (i : ι) (m : M) (n : N) :
    finsuppLeft R H ι M N (tmul R H (Finsupp.single i m) n) = Finsupp.single i (tmul R H m n) :=
  (LinearEquiv.eq_symm_apply _).mp (by simp)

/-- Coproduct tensor products distribute over finitely supported functions in their right
factor. -/
def finsuppRight : Tensor R H N (ι →₀ M) ≃ₗ[H] ι →₀ Tensor R H N M :=
  (LinearEquiv.ofBijective
    (Finsupp.lsum ℕ fun i => tensorMap R H LinearMap.id (Finsupp.lsingle i))
    (by
      classical
      let e := (Finsupp.mapRange.linearEquiv (tensorEquiv R H N M)).trans
        ((TensorProduct.finsuppRight R R N M ι).symm.trans (tensorEquiv R H N (ι →₀ M)).symm)
      convert e.bijective using 1
      ext x
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single i x =>
        induction x using Tensor.inductionOn with
        | htmul n m =>
          simp [e, TensorProduct.finsuppRight_symm_apply_single]
        | hadd x y hx hy => simp only [Finsupp.single_add, map_add, hx, hy])).symm

/-- The inverse right comparison inserts a tensor into the corresponding coordinate of the
right factor. -/
@[simp] theorem finsuppRight_symm_single (i : ι) (x : Tensor R H N M) :
    (finsuppRight R H ι M N).symm (Finsupp.single i x) =
      tensorMap R H LinearMap.id (Finsupp.lsingle i) x := by
  simp [finsuppRight]

/-- The right comparison evaluates pure tensors coordinatewise. -/
@[simp] theorem finsuppRight_tmul (n : N) (f : ι →₀ M) (i : ι) :
    finsuppRight R H ι M N (tmul R H n f) i = tmul R H n (f i) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, hf, hg]
  | single j m =>
    have hs : tmul R H n (Finsupp.single j m) =
        (finsuppRight R H ι M N).symm (Finsupp.single j (tmul R H n m)) := by simp
    rw [hs, LinearEquiv.apply_symm_apply]
    by_cases hji : j = i <;> simp [hji]

/-- Each coordinate of `finsuppRight` is the tensor product of the identity with the
corresponding evaluation. -/
theorem finsuppRight_apply (x : Tensor R H N (ι →₀ M)) (i : ι) :
    finsuppRight R H ι M N x i = tensorMap R H LinearMap.id (Finsupp.lapply i) x := by
  induction x using Tensor.inductionOn with
  | htmul n f => simp
  | hadd x y hx hy => simp [hx, hy]

/-- The right comparison sends a pure tensor with a single to a single. -/
@[simp] theorem finsuppRight_tmul_single (i : ι) (n : N) (m : M) :
    finsuppRight R H ι M N (tmul R H n (Finsupp.single i m)) = Finsupp.single i (tmul R H n m) :=
  (LinearEquiv.eq_symm_apply _).mp (by simp)

end TauCeti.BialgebraModule
