/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.LTensor
public import TauCeti.LowDimTopology.Bordered.TypeA.Basic
public import TauCeti.LowDimTopology.Bordered.TypeDD

/-!
# The box tensor product of a type `A` module with a type `DD` structure

A bordered three-manifold `Y₂` with two boundary components has a type `DD` bimodule over the
algebras `A` and `B` of its two boundary surfaces; gluing a bordered manifold `Y₁` with type `A`
module `M` over `A` along the first boundary gives a bordered manifold whose type `D` structure
over `B` is the box tensor product `M ⊠ N`. With `N` written as a type `D` structure over `A ⊗ B`
(`TauCeti.TypeDDStructure`), with generators `Y` and coefficient matrix `δ`, its structure map is

`δ¹(m ⊗ y) = ∑ₖ ∑_{y = y₀ → ⋯ → yₖ} b₁ ⋯ bₖ ⊗ m_{k+1}(m, a₁, …, aₖ) ⊗ yₖ`

along the paths of generators, where `δ yᵢ₋₁ yᵢ = aᵢ ⊗ bᵢ`: the type `A` operations of `M` consume
the `A` parts of the coefficients, and the `B` parts are multiplied in order.

This file realizes `M ⊠ N` through the differential `B`-module it induces, `B ⊗ (M ⊠ N)`, with
differential `∂ (b₀ ⊗ x) = d_B b₀ ⊗ x + b₀ δ¹(x)`; for a type `D` structure written in a basis this
module determines the structure (`TauCeti.LowDimTopology.Bordered.InducedModule`). Its elements
are the row vectors `φ : Y → B ⊗ M`, standing for `∑ y, φ y ⊗ y`, and its differential is the type
`A` box tensor differential of the `A∞` module `B ⊗ M` over `A ⊗ B`
(`TauCeti.UngradedAInfinityRightModule.lTensor`) with `N`:
`N.typeABoxDifferential (Mm.lTensor hB)`. On `b₀ ⊗ m ⊗ y` it is `b₀` times the formula above, plus
`d_B b₀ ⊗ m ⊗ y`. The sum is finite when `M` or `N` is bounded. Writing `M ⊠ N` itself as a type
`D` structure over `B` in a basis needs a basis of `M` adapted to the idempotents, and is not done
here.

* **The Leibniz rule.** The differential satisfies
  `∂ (b • φ) = b • ∂ φ + d_B b • φ` for the left action of `B`
  (`TauCeti.TypeDStructure.typeABoxDifferential_lTensor_smul`, with its two bounded forms
  `TauCeti.TypeDStructure.typeABoxDifferential_lTensor_smul_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxDifferential_lTensor_smul_of_act_eq_zero`), since the
  operations of `B ⊗ M` are `B`-linear except for the Leibniz rule of `m₁`.
* **It squares to zero** when `N` is bounded, by
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_isBounded` applied to
  `B ⊗ M`, and when `M` is bounded
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_lTensor_of_act_eq_zero`),
  since `B ⊗ M` is then bounded as well.

Together, the Leibniz rule and `∂ ∘ ∂ = 0` make `B ⊗ (M ⊠ N)` a differential `B`-module whenever
`M` or `N` is bounded.

When `M` is strictly unital, so is `B ⊗ M` for the idempotents `ιA s ⊗ ιB t` of the type `DD`
structure (`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.lTensor`). If moreover the
differential `d ⊗ 1 + 1 ⊗ d_B` vanishes on these idempotents, for instance when `dA (ιA s) = 0`
and `dB (ιB t) = 0`, the results of `TauCeti.LowDimTopology.Bordered.TypeA.Basic` about
`TauCeti.TypeDStructure.typeABoxTensor` restrict the differential to the box tensor product over
the idempotents, the row vectors with `m₂(φ y, ιA s ⊗ ιB t) = φ y` at every generator `y` over
`(s, t)`.

## Main results

* `TauCeti.TypeDStructure.typeABoxDifferential_lTensor_smul`: the Leibniz rule for the left action
  of `B`.
* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_lTensor_of_act_eq_zero`: the
  differential squares to zero when `M` is bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.3
  (box tensor products of modules with bimodules) and §2.2 (type `DD` structures as type `D`
  structures over a tensor product of algebras).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.4 (the box tensor product, equation (2.29)).
-/

public section

open scoped TensorProduct
open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A B M : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [AddCommGroup M] [Module R M] [CharP R 2] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S T : Type*}
  {ιA : S → A} {ιB : T → B} {Y : Type*} [Fintype Y] [DecidableEq Y]
  (hB : IsUngradedDGAlgebra dB) (Mm : UngradedAInfinityRightModule dA M)
  (N : TypeDDStructure dA dB ιA ιB Y)

/-- **The box tensor differential with a type `DD` structure satisfies the Leibniz rule** for the
left action of `B`. When the
operations of the matrix module of `B ⊗ M` vanish along `δ` from some arity on, the box tensor
differential of `B ⊗ M` with `N` satisfies the Leibniz rule `∂ (b • φ) = b • ∂ φ + d_B b • φ` for
the left action of `B` on the factor `B`. -/
theorem typeABoxDifferential_lTensor_smul {K : ℕ}
    (hK : ∀ n, K ≤ n → ((Mm.lTensor hB).matrixAct Y n fun _ => N.coeff) = 0) (b : B)
    (φ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (b • φ) =
      b • N.typeABoxDifferential (Mm.lTensor hB) φ + dB b • φ := by
  have hK' : ∀ n, K + 1 ≤ n → ((Mm.lTensor hB).matrixAct Y n fun _ => N.coeff) = 0 :=
    fun n hn => hK n (by omega)
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, N.typeABoxDifferential_apply_eq_sum _ hK',
    UngradedAInfinityRightModule.lTensor_act_smul, smul_sum, smul_ite, smul_zero]
  -- Each operation is `B`-linear; `m₁` adds `d_B b • φ (x 0)`, which survives on the paths of
  -- length zero, the constant paths at `z`.
  simp only [ite_add_zero, sum_add_distrib, add_right_inj]
  rw [sum_eq_single_of_mem 0 (mem_range.2 (Nat.succ_pos K)) fun n _ hn => by
    simp [hn]]
  simp only [ite_true]
  -- A path of length zero ending at `z` is the constant path at `z`.
  have hconst : ∀ x : Fin 1 → Y, x (Fin.last 0) = z → x = fun _ => z := fun x h =>
    funext fun i => by rw [Subsingleton.elim i (Fin.last 0), h]
  rw [Fintype.sum_eq_single (fun _ => z) fun x hx => ite_eq_right fun h => (hx (hconst x h)).elim]
  exact ite_eq_left rfl

/-- **The box tensor differential with a bounded type `DD` structure satisfies the Leibniz rule**
for the left action of `B`: `∂ (b • φ) = b • ∂ φ + d_B b • φ`. -/
theorem typeABoxDifferential_lTensor_smul_of_isBounded (hN : N.IsBounded) (b : B)
    (φ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (b • φ) =
      b • N.typeABoxDifferential (Mm.lTensor hB) φ + dB b • φ := by
  obtain ⟨K, hK⟩ := hN.exists_matrixAct_eq_zero
  exact N.typeABoxDifferential_lTensor_smul hB Mm (hK (Mm.lTensor hB)) b φ

/-- **The box tensor differential of a bounded type `A` module with a type `DD` structure
satisfies the Leibniz rule** for the left action of `B`: if the operations `m_{n+1}` of `M` vanish
for `n ≥ K`, then `∂ (b • φ) = b • ∂ φ + d_B b • φ`. -/
theorem typeABoxDifferential_lTensor_smul_of_act_eq_zero {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (b : B) (φ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (b • φ) =
      b • N.typeABoxDifferential (Mm.lTensor hB) φ + dB b • φ :=
  N.typeABoxDifferential_lTensor_smul hB Mm (K := K + 1) (fun n hn => by
    rw [(Mm.lTensor hB).matrixAct_eq_zero_of_act_eq_zero Y
      (Mm.lTensor_act_eq_zero hB (by omega) (hK n (by omega))), _root_.zero_apply]) b φ

/-- **The box tensor differential of a bounded type `A` module with a type `DD` structure squares
to zero.** If the operations `m_{n+1}` of `M` vanish for `n ≥ K`, then so do those of `B ⊗ M` for
`n ≥ K + 1`, and `∂ ∘ ∂ = 0` on the row vectors `Y → B ⊗ M`. -/
theorem typeABoxDifferential_typeABoxDifferential_lTensor_of_act_eq_zero {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (N.typeABoxDifferential (Mm.lTensor hB) φ) = 0 :=
  N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero (Mm.lTensor hB) (K := K + 1)
    (fun n hn => Mm.lTensor_act_eq_zero hB (by omega) (hK n (by omega))) φ

end TypeDStructure

end TauCeti
