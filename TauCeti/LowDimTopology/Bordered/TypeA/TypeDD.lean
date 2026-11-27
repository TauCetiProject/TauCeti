/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.LTensor
public import TauCeti.LowDimTopology.Bordered.InducedModule
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
`d_B b₀ ⊗ m ⊗ y`. The sum is finite when `M` or `N` is bounded.

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

**`M ⊠ N` as a type `D` structure over `B`.** Writing `M ⊠ N` itself in a basis needs a basis
`(e_x)` of `M` adapted to the idempotents: `m₂(e_x, ιA s)` is `e_x` when `σ x = s` and `0`
otherwise. The tensor product over the idempotents of `A` is then spanned by the `e_x ⊗ y` with
`σ x` the `A`-idempotent of `y` (`TauCeti.TypeDStructure.boxGenerators`), each carrying the
`B`-idempotent of `y`. A function `φ` on these generators, standing for `∑ φ (x, y) ⊗ e_x ⊗ y` in
`B ⊗ (M ⊠ N)`, has the row vector `y ↦ ∑ x, φ (x, y) ⊗ e_x` (`TauCeti.TypeDStructure.toBoxRow`),
and a row vector has its coordinates in the `B`-basis `1 ⊗ e_x` of `B ⊗ M`
(`TauCeti.TypeDStructure.ofBoxRow`). These are inverse `B`-linear identifications of the induced
module of the generators with `B ⊗ (M ⊗_{I_A} N)`: the coordinate of `e_x` at `y` of a row vector
fixed by the idempotents vanishes unless `σ x` is the `A`-idempotent of `y`, and is fixed by right
multiplication by the `B`-idempotent of `y`. Transporting the box tensor differential of `B ⊗ M`
with `N`, a Leibniz differential of square zero, along them gives a type `D` structure over `B`
(`TauCeti.TypeDStructure.ofInducedDifferential`): this is `M ⊠ N`
(`TauCeti.TypeDStructure.typeABoxTypeD`). It requires `M` strictly unital, the idempotents of `A`
and `B` cycles, those of `B` idempotent, and `M` or `N` bounded.

## Main definitions

* `TauCeti.TypeDStructure.boxGenerators`: the generators `e_x ⊗ y` of `M ⊠ N` in a basis of `M`
  adapted to the idempotents.
* `TauCeti.TypeDStructure.toBoxRow`, `TauCeti.TypeDStructure.ofBoxRow`: the identification of
  functions on these generators with row vectors of `B ⊗ M`.
* `TauCeti.TypeDStructure.typeABoxTypeD`: the type `D` structure `M ⊠ N` over `B`.

## Main results

* `TauCeti.TypeDStructure.typeABoxDifferential_lTensor_smul`: the Leibniz rule for the left action
  of `B`.
* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_lTensor_of_act_eq_zero`: the
  differential squares to zero when `M` is bounded.
* `TauCeti.TypeDStructure.toBoxRow_ofBoxRow`, `TauCeti.TypeDStructure.ofBoxRow_toBoxRow`: the row
  vectors fixed by the idempotents are those of functions on the generators.
* `TauCeti.TypeDStructure.typeABoxTypeD_coeff`: the coefficients of `M ⊠ N`.
* `TauCeti.TypeDStructure.toBoxRow_boxDifferential_typeABoxTypeD`: the box tensor differential of
  `M ⊠ N` is that of `B ⊗ M` with `N`.
* `TauCeti.TypeDStructure.eq_typeABoxTypeD_iff`: `M ⊠ N` is the only type `D` structure with these
  generators and idempotents whose box tensor differential is that of `B ⊗ M` with `N`.

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

section LTensor

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

end LTensor

/-! ### `M ⊠ N` as a type `D` structure in a basis -/

section Basis

variable {R A B M : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [AddCommGroup M] [Module R M] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S T : Type*}
  {ιA : S → A} {ιB : T → B} {Y : Type*} [Fintype Y] (N : TypeDDStructure dA dB ιA ιB Y)
  {X : Type*} (σ : X → S)

/-- The **generators of `M ⊠ N`** for a basis `(e_x)` of `M` whose element `e_x` lies in the
summand of the idempotent `ιA (σ x)`: the pairs `(x, y)` such that `σ x` is the `A`-idempotent of
`y`, standing for `e_x ⊗ y`. The other pairs vanish in the tensor product over the idempotents. -/
abbrev boxGenerators : Type _ :=
  {p : X × Y // σ p.1 = (N.idem p.2).1}

variable (bM : Module.Basis X R M)

/-- The **coordinates of a row vector of `B ⊗ M` on the generators of `M ⊠ N`**: the coefficient
of `e_x` in the entry at `y`, for every generator `(x, y)`. -/
noncomputable def ofBoxRow : (Y → B ⊗[R] M) →ₗ[B] N.boxGenerators σ → B :=
  LinearMap.pi fun p => (Algebra.TensorProduct.basis B bM).coord p.val.1 ∘ₗ LinearMap.proj p.val.2

/-- The coordinate of a row vector at the generator `(x, y)` is the coefficient of `e_x` in its
entry at `y`. -/
@[simp]
theorem ofBoxRow_apply (ψ : Y → B ⊗[R] M) (p : N.boxGenerators σ) :
    N.ofBoxRow σ bM ψ p = (Algebra.TensorProduct.basis B bM).repr (ψ p.val.2) p.val.1 :=
  (rfl)

variable [DecidableEq S]

/-- **Coordinates of `m₂(m, ιA s)` in a basis adapted to the idempotents.** If `m₂(e_x, ιA s)` is
`e_x` when `σ x = s` and `0` otherwise, then `m₂(·, ιA s)` keeps the coordinates of `m` at the
`x` with `σ x = s` and kills the others. -/
private theorem repr_act_one_apply {Mm : UngradedAInfinityRightModule dA M} {σ : X → S}
    {bM : Module.Basis X R M}
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0) (s : S)
    (m : M) (x : X) :
    bM.repr (Mm.act 1 (fun _ => ιA s) m) x = if σ x = s then bM.repr m x else 0 := by
  have h : bM.coord x ∘ₗ Mm.act 1 (fun _ => ιA s) = if σ x = s then bM.coord x else 0 := by
    refine bM.ext fun i => ?_
    rw [LinearMap.comp_apply, hbM]
    by_cases hi : i = x
    · subst hi
      split_ifs <;> simp
    · split_ifs <;> simp [hi]
  simpa [apply_ite (fun f : M →ₗ[R] R => f m)] using congrArg (fun f : M →ₗ[R] R => f m) h

variable [Fintype X]

/-- The **row vector of `B ⊗ M` of a function on the generators of `M ⊠ N`**: `φ` stands for
`∑ φ (x, y) ⊗ e_x ⊗ y`, and its row vector is `y ↦ ∑ x, φ (x, y) ⊗ e_x`, with `φ (x, y)` read as
`0` when `(x, y)` is not a generator. -/
noncomputable def toBoxRow : (N.boxGenerators σ → B) →ₗ[B] Y → B ⊗[R] M :=
  LinearMap.pi fun y => (Algebra.TensorProduct.basis B bM).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi fun x => if h : σ x = (N.idem y).1 then LinearMap.proj ⟨(x, y), h⟩ else 0

variable {N σ bM}

/-- The coefficient of `e_x` in the entry at `y` of the row vector of `φ` is `φ (x, y)`, or `0`
when `(x, y)` is not a generator. -/
@[simp]
theorem repr_toBoxRow_apply (φ : N.boxGenerators σ → B) (y : Y) (x : X) :
    (Algebra.TensorProduct.basis B bM).repr (N.toBoxRow σ bM φ y) x =
      if h : σ x = (N.idem y).1 then φ ⟨(x, y), h⟩ else 0 := by
  rw [← Module.Basis.equivFun_apply]
  simp only [toBoxRow, LinearMap.pi_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  split_ifs <;> simp [*]

/-- The entry at `y` of the row vector of `φ` is `∑ x, φ (x, y) ⊗ e_x`. -/
theorem toBoxRow_apply (φ : N.boxGenerators σ → B) (y : Y) :
    N.toBoxRow σ bM φ y =
      ∑ x, (if h : σ x = (N.idem y).1 then φ ⟨(x, y), h⟩ else 0) ⊗ₜ[R] bM x := by
  simp only [toBoxRow, LinearMap.pi_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Module.Basis.equivFun_symm_apply,
    Algebra.TensorProduct.basis_repr_symm_apply']
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- A function on the generators of `M ⊠ N` is recovered from the coordinates of its row vector. -/
@[simp]
theorem ofBoxRow_toBoxRow (φ : N.boxGenerators σ → B) :
    N.ofBoxRow σ bM (N.toBoxRow σ bM φ) = φ := by
  funext p
  rw [ofBoxRow_apply, repr_toBoxRow_apply]
  simp [p.property]


variable [DecidableEq X] [DecidableEq Y]

/-- The row vector of the generator `c ⊗ e_x ⊗ y` of `B ⊗ (M ⊠ N)` is `c ⊗ e_x` at `y`. -/
@[simp]
theorem toBoxRow_single (p : N.boxGenerators σ) (c : B) :
    N.toBoxRow σ bM (Pi.single p c) = Pi.single p.val.2 (c ⊗ₜ[R] bM p.val.1) := by
  funext y
  refine (Algebra.TensorProduct.basis B bM).ext_elem_iff.2 fun x => ?_
  rw [repr_toBoxRow_apply]
  obtain ⟨⟨x₀, y₀⟩, h₀⟩ := p
  by_cases hy : y = y₀
  · subst hy
    by_cases hx : x = x₀
    · subst hx
      simp [h₀]
    · simp [hx]
  · simp [hy]

end Basis

section BasisLTensor

variable {R A B M : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [AddCommGroup M] [Module R M] [CharP R 2] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S T : Type*}
  {ιA : S → A} {ιB : T → B} {Y : Type*} [Fintype Y] {N : TypeDDStructure dA dB ιA ιB Y}
  [DecidableEq S] {X : Type*} {σ : X → S} {bM : Module.Basis X R M}
  (hB : IsUngradedDGAlgebra dB) {Mm : UngradedAInfinityRightModule dA M}

include hB in
/-- **Coordinates of `m₂(·, ιA s ⊗ ιB t)` on `B ⊗ M`** in the `B`-basis `1 ⊗ e_x` of a basis
adapted to the idempotents: the coordinates at the `x` with `σ x = s` are multiplied on the right
by `ιB t`, and the others vanish. -/
private theorem repr_lTensor_act_one
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0) (s : S)
    (t : T) (v : B ⊗[R] M) (x : X) :
    (Algebra.TensorProduct.basis B bM).repr
        ((Mm.lTensor hB).act 1 (fun _ => ιA s ⊗ₜ[R] ιB t) v) x =
      if σ x = s then (Algebra.TensorProduct.basis B bM).repr v x * ιB t else 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul b₀ m =>
    have h := Mm.lTensor_act_tmul_tmul hB 1 (fun _ => ιA s) (fun _ => ιB t) b₀ m
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      one_ne_zero, ↓reduceIte, add_zero] at h
    rw [h]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul, repr_act_one_apply hbM]
    split_ifs
    · rw [mul_assoc, mul_assoc, Algebra.commutes]
    · simp
  | add v w hv hw =>
    simp only [map_add, Finsupp.add_apply, hv, hw]
    split_ifs
    · rw [add_mul]
    · rw [add_zero]

include hB in
/-- The coordinates of a row vector of `B ⊗ (M ⊗_{I_A} N)`, for a basis of `M` adapted to the
idempotents: the coordinate of `e_x` at `y` vanishes unless `σ x` is the `A`-idempotent of `y`, and
is fixed by right multiplication by its `B`-idempotent. -/
private theorem repr_apply_of_mem_typeABoxTensor
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0)
    {ψ : Y → B ⊗[R] M} (hψ : ψ ∈ N.typeABoxTensor (Mm.lTensor hB)) (y : Y) (x : X) :
    (Algebra.TensorProduct.basis B bM).repr (ψ y) x =
      if σ x = (N.idem y).1 then (Algebra.TensorProduct.basis B bM).repr (ψ y) x *
        ιB (N.idem y).2 else 0 := by
  conv_lhs => rw [← mem_typeABoxTensor_iff.1 hψ y]
  exact repr_lTensor_act_one hB hbM _ _ _ _

include hB in
/-- The coordinates of a row vector of `B ⊗ (M ⊗_{I_A} N)` on the generators of `M ⊠ N` are fixed
by right multiplication by their `B`-idempotents. -/
theorem ofBoxRow_mul_idem
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0)
    {ψ : Y → B ⊗[R] M} (hψ : ψ ∈ N.typeABoxTensor (Mm.lTensor hB)) (p : N.boxGenerators σ) :
    N.ofBoxRow σ bM ψ p * ιB (N.idem p.val.2).2 = N.ofBoxRow σ bM ψ p := by
  have h := repr_apply_of_mem_typeABoxTensor hB hbM hψ p.val.2 p.val.1
  simp only [p.property, ↓reduceIte] at h
  rw [ofBoxRow_apply]
  exact h.symm

variable [Fintype X]

include hB in
/-- **`toBoxRow` inverts `ofBoxRow` on `B ⊗ (M ⊗_{I_A} N)`**: a row vector of `B ⊗ M` fixed by the
idempotents is recovered from its coordinates on the generators of `M ⊠ N`, for a basis of `M`
adapted to the idempotents. -/
theorem toBoxRow_ofBoxRow
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0)
    {ψ : Y → B ⊗[R] M} (hψ : ψ ∈ N.typeABoxTensor (Mm.lTensor hB)) :
    N.toBoxRow σ bM (N.ofBoxRow σ bM ψ) = ψ := by
  funext y
  refine (Algebra.TensorProduct.basis B bM).ext_elem_iff.2 fun x => ?_
  rw [repr_toBoxRow_apply]
  split_ifs with h
  · rfl
  · rw [repr_apply_of_mem_typeABoxTensor hB hbM hψ y x]
    simp [h]

include hB in
/-- **`toBoxRow` lands in `B ⊗ (M ⊗_{I_A} N)`**: the row vector of a function on the generators of
`M ⊠ N` fixed by right multiplication by their `B`-idempotents is fixed by the idempotents
`ιA s ⊗ ιB t` of `N`, for a basis of `M` adapted to the idempotents. -/
theorem toBoxRow_mem_typeABoxTensor
    (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0)
    {φ : N.boxGenerators σ → B} (hφ : ∀ p, φ p * ιB (N.idem p.val.2).2 = φ p) :
    N.toBoxRow σ bM φ ∈ N.typeABoxTensor (Mm.lTensor hB) :=
  mem_typeABoxTensor_iff.2 fun y => (Algebra.TensorProduct.basis B bM).ext_elem_iff.2 fun x => by
    rw [repr_lTensor_act_one hB hbM, repr_toBoxRow_apply]
    split_ifs with h
    · exact hφ ⟨(x, y), h⟩
    · rfl


variable [DecidableEq Y]

omit [DecidableEq S] in
include hB in
/-- The box tensor differential of `B ⊗ M` with `N` satisfies the Leibniz rule for the left action
of `B` when `M` or `N` is bounded. -/
private theorem typeABoxDifferential_lTensor_smul_of_or
    (hbd : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → Mm.act n = 0) (b : B) (ψ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (b • ψ) =
      b • N.typeABoxDifferential (Mm.lTensor hB) ψ + dB b • ψ := by
  rcases hbd with hN | ⟨K, hK⟩
  · exact N.typeABoxDifferential_lTensor_smul_of_isBounded hB Mm hN b ψ
  · exact N.typeABoxDifferential_lTensor_smul_of_act_eq_zero hB Mm hK b ψ

omit [DecidableEq S] in
include hB in
/-- The box tensor differential of `B ⊗ M` with `N` squares to zero when `M` or `N` is bounded. -/
private theorem typeABoxDifferential_typeABoxDifferential_lTensor_of_or
    (hbd : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → Mm.act n = 0) (ψ : Y → B ⊗[R] M) :
    N.typeABoxDifferential (Mm.lTensor hB) (N.typeABoxDifferential (Mm.lTensor hB) ψ) = 0 := by
  rcases hbd with hN | ⟨K, hK⟩
  · exact N.typeABoxDifferential_typeABoxDifferential_of_isBounded (Mm.lTensor hB) hN ψ
  · exact N.typeABoxDifferential_typeABoxDifferential_lTensor_of_act_eq_zero hB Mm hK ψ

variable (hMm : Mm.IsStrictlyUnital ιA) (hbd : N.IsBounded ∨ ∃ K, ∀ n, K ≤ n → Mm.act n = 0)
  (hιA : ∀ s, dA (ιA s) = 0) (hidemB : ∀ t, IsIdempotentElem (ιB t)) (hιB : ∀ t, dB (ιB t) = 0)
  (hbM : ∀ x s, Mm.act 1 (fun _ => ιA s) (bM x) = if σ x = s then bM x else 0)

include hB hMm hιA hιB hbM in
/-- The box tensor differential of `B ⊗ M` with `N` maps row vectors of functions on the
generators of `M ⊠ N` fixed by their `B`-idempotents into `B ⊗ (M ⊗_{I_A} N)`. -/
private theorem typeABoxDifferential_toBoxRow_mem_typeABoxTensor
    {φ : N.boxGenerators σ → B} (hφ : ∀ p, φ p * ιB (N.idem p.val.2).2 = φ p) :
    N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ) ∈
      N.typeABoxTensor (Mm.lTensor hB) :=
  typeABoxDifferential_mem_typeABoxTensor (UngradedAInfinityRightModule.IsStrictlyUnital.lTensor
    Mm hB hMm) (fun st => by simp [ungradedTensorDifferential_tmul, hιA, hιB])
    (toBoxRow_mem_typeABoxTensor hB hbM hφ)

omit [CharP R 2] [DecidableEq Y] in
/-- A function on the generators of `M ⊠ N` in the induced module of their `B`-idempotents is fixed
by them on the right. -/
private theorem mul_idem_of_mem_inducedModule_ofIdem {φ : N.boxGenerators σ → B}
    (hφ : φ ∈ (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule)
    (p : N.boxGenerators σ) : φ p * ιB (N.idem p.val.2).2 = φ p := by
  simpa only [ofIdem_idem] using mem_inducedModule_iff.1 hφ p

include hMm hιA hιB hbM in
/-- The differential of the induced module of `M ⊠ N`, transported from the box tensor
differential of `B ⊗ M` with `N` on `B ⊗ (M ⊗_{I_A} N)` through the coordinates in the basis. -/
private noncomputable def boxInducedDifferential :
    (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule →ₗ[R]
      (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule where
  toFun φ := ⟨N.ofBoxRow σ bM (N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ)),
    mem_inducedModule_iff.2 fun p => by
      simpa only [ofIdem_idem] using ofBoxRow_mul_idem hB hbM
        (typeABoxDifferential_toBoxRow_mem_typeABoxTensor hB hMm hιA hιB hbM
          (mul_idem_of_mem_inducedModule_ofIdem φ.property)) p⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' r φ := Subtype.ext (by simp)

private theorem coe_boxInducedDifferential_apply
    (φ : (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule) :
    (boxInducedDifferential hB hMm hιA hιB hbM φ : N.boxGenerators σ → B) =
      N.ofBoxRow σ bM (N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ)) :=
  (rfl)

/-- The row vector of the transported differential is the box tensor differential of `B ⊗ M` with
`N` applied to the row vector. -/
private theorem toBoxRow_coe_boxInducedDifferential
    (φ : (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule) :
    N.toBoxRow σ bM (boxInducedDifferential hB hMm hιA hιB hbM φ) =
      N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ) := by
  rw [coe_boxInducedDifferential_apply, toBoxRow_ofBoxRow hB hbM
    (typeABoxDifferential_toBoxRow_mem_typeABoxTensor hB hMm hιA hιB hbM
      (mul_idem_of_mem_inducedModule_ofIdem φ.property))]

include hbd in
private theorem boxInducedDifferential_smul (b : B)
    (φ : (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule) :
    boxInducedDifferential hB hMm hιA hιB hbM (b • φ) =
      dB b • φ + b • boxInducedDifferential hB hMm hιA hιB hbM φ := by
  refine Subtype.ext ?_
  simp only [coe_boxInducedDifferential_apply, SetLike.val_smul, Submodule.coe_add, map_smul,
    typeABoxDifferential_lTensor_smul_of_or hB hbd, map_add, ofBoxRow_toBoxRow]
  exact add_comm _ _

include hbd in
private theorem boxInducedDifferential_boxInducedDifferential
    (φ : (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).inducedModule) :
    boxInducedDifferential hB hMm hιA hιB hbM (boxInducedDifferential hB hMm hιA hιB hbM φ) = 0 :=
  Subtype.ext (by
    rw [coe_boxInducedDifferential_apply, toBoxRow_coe_boxInducedDifferential,
      typeABoxDifferential_typeABoxDifferential_lTensor_of_or hB hbd, map_zero,
      ZeroMemClass.coe_zero])

variable [DecidableEq X]

variable (N) in
/-- **The box tensor product `M ⊠ N` of a type `A` module with a type `DD` structure, as a type `D`
structure over `B`.** Let `M` be a strictly unital `A∞` module over `A` with a basis `(e_x)` adapted
to the idempotents, `m₂(e_x, ιA s) = e_x` if `σ x = s` and `0` otherwise, and let `M` or `N` be
bounded. Its generators are the pairs `e_x ⊗ y` with `σ x` the `A`-idempotent of `y`
(`TauCeti.TypeDStructure.boxGenerators`), with the `B`-idempotent of `y`, and its structure map is

`δ¹(e_x ⊗ y) = ∑ₖ ∑_{y = y₀ → ⋯ → yₖ} b₁ ⋯ bₖ ⊗ m_{k+1}(e_x, a₁, …, aₖ) ⊗ yₖ`

along the paths of generators of `N` with coefficients `aᵢ ⊗ bᵢ`, the elements
`m_{k+1}(e_x, a₁, …, aₖ)` being expanded in the basis
(`TauCeti.TypeDStructure.typeABoxTypeD_coeff`).
It is the type `D` structure whose induced module is `B ⊗ (M ⊗_{I_A} N)` with the box tensor
differential of the `A∞` module `B ⊗ M` over `A ⊗ B` with `N`
(`TauCeti.TypeDStructure.toBoxRow_boxDifferential_typeABoxTypeD`), and the only one with these
idempotents (`TauCeti.TypeDStructure.eq_typeABoxTypeD_iff`). -/
noncomputable def typeABoxTypeD : TypeDStructure dB ιB (N.boxGenerators σ) :=
  (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).ofInducedDifferential hB hidemB
    hιB (boxInducedDifferential hB hMm hιA hιB hbM)
    (boxInducedDifferential_smul hB hMm hbd hιA hιB hbM)
    (boxInducedDifferential_boxInducedDifferential hB hMm hbd hιA hιB hbM)

/-- The generator `e_x ⊗ y` of `M ⊠ N` carries the `B`-idempotent of `y`. -/
@[simp]
theorem typeABoxTypeD_idem (p : N.boxGenerators σ) :
    (N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM).idem p = (N.idem p.val.2).2 := by
  rw [typeABoxTypeD, ofInducedDifferential_idem, ofIdem_idem]

/-- **The coefficients of `M ⊠ N`.** The coefficient of `e_{x'} ⊗ y'` in `δ¹(e_x ⊗ y)` is the
coefficient of `e_{x'}` at `y'` in the box tensor differential of `B ⊗ M` with `N` applied to the
row vector `ιB t ⊗ e_x` at `y`, where `t` is the `B`-idempotent of `y`. -/
theorem typeABoxTypeD_coeff (p q : N.boxGenerators σ) :
    (N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM).coeff p q =
      (Algebra.TensorProduct.basis B bM).repr (N.typeABoxDifferential (Mm.lTensor hB)
        (Pi.single p.val.2 (ιB (N.idem p.val.2).2 ⊗ₜ[R] bM p.val.1)) q.val.2) q.val.1 := by
  rw [typeABoxTypeD, ofInducedDifferential_coeff, coe_boxInducedDifferential_apply,
    coe_generator, ofIdem_idem, toBoxRow_single, ofBoxRow_apply]

/-- **The coefficients of `M ⊠ N` as sums over paths.** When the operations
`m_{n+1}(·, δ, …, δ)` of `B ⊗ M` along the coefficients of `N` vanish for `n ≥ K`, for instance
when `M` or `N` is bounded, the coefficient of `e_{x'} ⊗ y'` in `δ¹(e_x ⊗ y)` is the sum, over the
paths `y = y₀ → ⋯ → yₙ = y'` of generators of `N` of length `n < K`, of the coefficients of
`e_{x'}` in `m_{n+1}(ιB t ⊗ e_x, δ y₀ y₁, …, δ yₙ₋₁ yₙ)`. -/
theorem typeABoxTypeD_coeff_eq_sum {K : ℕ}
    (hK : ∀ n, K ≤ n → ((Mm.lTensor hB).matrixAct Y n fun _ => N.coeff) = 0)
    (p q : N.boxGenerators σ) :
    (N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM).coeff p q =
      ∑ n ∈ Finset.range K, ∑ y : Fin (n + 1) → Y,
        if y 0 = p.val.2 ∧ y (Fin.last n) = q.val.2 then
          (Algebra.TensorProduct.basis B bM).repr ((Mm.lTensor hB).act n
            (fun l => N.coeff (y l.castSucc) (y l.succ))
            (ιB (N.idem p.val.2).2 ⊗ₜ[R] bM p.val.1)) q.val.1
        else 0 := by
  rw [typeABoxTypeD_coeff, N.typeABoxDifferential_apply_eq_sum _ hK]
  simp only [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h₀ : y 0 = p.val.2
  · by_cases hn : y (Fin.last n) = q.val.2 <;> simp [h₀, hn]
  · simp [h₀]

/-- **The box tensor differential of `M ⊠ N` is that of `B ⊗ M` with `N`.** Under the
identification `φ ↦ (y ↦ ∑ x, φ (x, y) ⊗ e_x)` of the induced module `B ⊗ (M ⊠ N)` with
`B ⊗ (M ⊗_{I_A} N)` (`TauCeti.TypeDStructure.toBoxRow`), the box tensor differential of the type
`D` structure `M ⊠ N` is the box tensor differential of the `A∞` module `B ⊗ M` over `A ⊗ B`
with the type `D` structure `N`. -/
theorem toBoxRow_boxDifferential_typeABoxTypeD {φ : N.boxGenerators σ → B}
    (hφ : φ ∈ (N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM).inducedModule) :
    N.toBoxRow σ bM ((N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM).boxDifferential dB φ) =
      N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ) := by
  rw [typeABoxTypeD, inducedModule_ofInducedDifferential] at hφ
  rw [typeABoxTypeD, boxDifferential_ofInducedDifferential_of_mem _ _ _ _ _ _ hφ,
    toBoxRow_coe_boxInducedDifferential]

/-- **`M ⊠ N` is the only type `D` structure on its generators with their `B`-idempotents whose box
tensor differential is that of `B ⊗ M` with `N`**, under the identification
`TauCeti.TypeDStructure.toBoxRow`. -/
theorem eq_typeABoxTypeD_iff {N' : TypeDStructure dB ιB (N.boxGenerators σ)} :
    N' = N.typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM ↔
      (∀ p, N'.idem p = (N.idem p.val.2).2) ∧ ∀ φ ∈ N'.inducedModule,
        N.toBoxRow σ bM (N'.boxDifferential dB φ) =
          N.typeABoxDifferential (Mm.lTensor hB) (N.toBoxRow σ bM φ) := by
  refine ⟨?_, fun ⟨hidem, hD⟩ => ?_⟩
  · rintro rfl
    exact ⟨typeABoxTypeD_idem hB hMm hbd hιA hidemB hιB hbM,
      fun φ hφ => toBoxRow_boxDifferential_typeABoxTypeD hB hMm hbd hιA hidemB hιB hbM hφ⟩
  rw [typeABoxTypeD, eq_ofInducedDifferential_iff]
  have hidem' : N'.idem = (ofIdem dB ιB fun p : N.boxGenerators σ => (N.idem p.val.2).2).idem := by
    rw [ofIdem_idem]
    exact funext hidem
  refine ⟨hidem', fun φ => ?_⟩
  have hφ : (φ : N.boxGenerators σ → B) ∈ N'.inducedModule :=
    mem_inducedModule_iff.2 fun p => by rw [hidem']; exact mem_inducedModule_iff.1 φ.property p
  rw [← ofBoxRow_toBoxRow (N := N) (σ := σ) (bM := bM)
    (N'.boxDifferential dB (φ : N.boxGenerators σ → B)), hD _ hφ,
    coe_boxInducedDifferential_apply]

end BasisLTensor

end TypeDStructure

end TauCeti
