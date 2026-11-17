/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded
public import TauCeti.LinearAlgebra.Multilinear.ContractNth
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.Algebra.BigOperators.Ring.List
import TauCeti.LinearAlgebra.Multilinear.TensorProduct

/-!
# Extending an `A∞` module over `A` to an `A∞` module over `A ⊗ B`

Let `M` be an ungraded `A∞` right module over the differential algebra `(A, d)`, and `(B, d_B)` a
second ungraded differential algebra, over a ring of characteristic two. Then `B ⊗ M` is an
ungraded `A∞` right module over the tensor product algebra `A ⊗ B` with the differential
`d ⊗ 1 + 1 ⊗ d_B` (`TauCeti.UngradedAInfinityRightModule.lTensor`), whose operations are

`m_{n+1}(b₀ ⊗ m, a₁ ⊗ b₁, …, aₙ ⊗ bₙ) = b₀ b₁ ⋯ bₙ ⊗ m_{n+1}(m, a₁, …, aₙ)` for `n ≥ 1`, and

`m₁(b₀ ⊗ m) = b₀ ⊗ m₁(m) + d_B b₀ ⊗ m`

(`TauCeti.UngradedAInfinityRightModule.lTensor_act_tmul_tmul`). As an `R`-module, `B ⊗ M` is
`M ⊗_A (A ⊗ B)`, the module obtained from `M` by extending scalars along `a ↦ a ⊗ 1`, and
`m₂(·, a ⊗ 1)` is the extended action of `A`. Its operations commute
with left multiplication on the factor `B`, except that `m₁` satisfies the Leibniz rule for `d_B`
(`TauCeti.UngradedAInfinityRightModule.lTensor_act_smul`).

A type `DD` bimodule `N` over `A` and `B` is a type `D` structure over `A ⊗ B`, and its box tensor
product with `B ⊗ M` realizes the differential `B`-module `B ⊗ (M ⊠ N)` induced by the type `D`
structure `M ⊠ N` over `B`; see `TauCeti.LowDimTopology.Bordered.TypeA.TypeDD`.

**The relations.** On pure tensors the `A∞` relation of `B ⊗ M` of length `n` is `b₀ b₁ ⋯ bₙ`
tensored with the relation of `M`, plus three terms carrying `d_B`, each tensored with
`m_{n+1}(m, a₁, …, aₙ)`: `d_B (b₀ b₁ ⋯ bₙ)` and `d_B b₀ · b₁ ⋯ bₙ` from the composite terms with
`m₁` outermost and innermost, and `b₀ · d_B (b₁ ⋯ bₙ)` from the differential terms. By the
Leibniz rule they add up to twice `d_B (b₀ ⋯ bₙ)`, which vanishes in characteristic two. The
relation is multilinear in the algebra inputs: `TauCeti.ungradedStasheffCompMultilinear`,
`TauCeti.ungradedStasheffDiffMultilinear` and `TauCeti.ungradedStasheffMulMultilinear` package its
three kinds of terms as multilinear maps. So it suffices to check it on pure tensors
(`MultilinearMap.ext_tmul`). The operations themselves are built with `MultilinearMap.tensorMap`
from the operations of `M` and the ordered product of `B`.

The analogous construction for `ℤ`-graded `A∞` algebras, with Koszul signs, is
`TauCeti.AInfinityAlgebra.tensorDGAlgebra`.

Boundedness and strict unitality pass from `M` to `B ⊗ M`
(`TauCeti.UngradedAInfinityRightModule.lTensor_act_eq_zero`,
`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.lTensor`), the units of `A ⊗ B` being the
pure tensors of units.

## Main definitions

* `TauCeti.ungradedStasheffCompMultilinear`, `TauCeti.ungradedStasheffDiffMultilinear`,
  `TauCeti.ungradedStasheffMulMultilinear`: the terms of the `A∞` relations as multilinear maps
  in the algebra inputs.
* `TauCeti.UngradedAInfinityRightModule.lTensor`: the `A∞` module `B ⊗ M` over `A ⊗ B`.

## Main results

* `TauCeti.UngradedAInfinityRightModule.lTensor_act_tmul_tmul`: the operations on pure tensors.
* `TauCeti.UngradedAInfinityRightModule.lTensor_act_smul`: the operations are `B`-linear, up to the
  Leibniz rule of `m₁`.
* `TauCeti.UngradedAInfinityRightModule.lTensor_act_eq_zero`: `B ⊗ M` is bounded when `M` is.
* `TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.lTensor`: `B ⊗ M` is strictly unital
  when `M` is.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2
  (`A∞` modules over `𝔽₂`, and type `DD` structures as type `D` structures over a tensor product
  of algebras).
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. **3**
  (2001), 1–35, Section 4 (`A∞` modules).
-/

public section

open scoped TensorProduct
open Function

namespace TauCeti

/-! ### The relations as multilinear maps -/

section StasheffMultilinear

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  (act : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M))
  (d : A →ₗ[R] A)

/-- The **composite terms** of the `A∞` relation of length `n`,
`∑_{i + j = n} m_{j+1}(m_{i+1}(·, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`, as a multilinear map in the algebra
inputs (`TauCeti.ungradedStasheffCompMultilinear_apply`). -/
noncomputable def ungradedStasheffCompMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M) :=
  ∑ k : Fin (n + 1), ((TensorProduct.lift (LinearMap.llcomp R M M M).flip).compMultilinearMap
      ((act k).domCoprod (act (n - k)))).domDomCongr
      (finSumFinEquiv.trans (finCongr (by omega)))

@[simp]
theorem ungradedStasheffCompMultilinear_apply (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffCompMultilinear act n a m = ungradedStasheffComp act n a m := by
  simp only [ungradedStasheffCompMultilinear, _root_.sum_apply, LinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domCoprod_apply, TensorProduct.lift.tmul, LinearMap.flip_apply,
    ungradedStasheffComp_def]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- The **differential terms** of the `A∞` relation of length `n`,
`∑_l m_{n+1}(·, a₁, …, d aₗ, …, aₙ)`, as a multilinear map in the algebra inputs
(`TauCeti.ungradedStasheffDiffMultilinear_apply`). -/
noncomputable def ungradedStasheffDiffMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M) :=
  ∑ l : Fin n, (act n).compLinearMap (update (fun _ => LinearMap.id) l d)

@[simp]
theorem ungradedStasheffDiffMultilinear_apply (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffDiffMultilinear act d n a m = ungradedStasheffDiff act d n a m := by
  simp only [ungradedStasheffDiffMultilinear, _root_.sum_apply, LinearMap.sum_apply,
    MultilinearMap.compLinearMap_apply, ungradedStasheffDiff_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  funext i
  by_cases h : i = l
  · subst h; simp
  · simp [h]

/-- The **product terms** of the `A∞` relation of length `n`,
`∑_l m_n(·, a₁, …, aₗ aₗ₊₁, …, aₙ)`, as a multilinear map in the algebra inputs
(`TauCeti.ungradedStasheffMulMultilinear_apply`). -/
noncomputable def ungradedStasheffMulMultilinear : (n : ℕ) →
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)
  | 0 => 0
  | n + 1 => ∑ l : Fin n, (act n).compContractNth l

@[simp]
theorem ungradedStasheffMulMultilinear_apply (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffMulMultilinear act n a m = ungradedStasheffMul act n a m := by
  cases n with
  | zero => simp [ungradedStasheffMulMultilinear]
  | succ n =>
    simp [ungradedStasheffMulMultilinear, ungradedStasheffMul_succ, _root_.sum_apply,
      LinearMap.sum_apply]

end StasheffMultilinear

/-! ### The module `B ⊗ M` over `A ⊗ B` -/

namespace UngradedAInfinityRightModule

variable {R A M B : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Ring B] [Algebra R B]

private noncomputable def lTensorEval : (M →ₗ[R] M) ⊗[R] B →ₗ[R] (B ⊗[R] M →ₗ[R] B ⊗[R] M) :=
  TensorProduct.lift
    ((TensorProduct.mapBilinear (RingHom.id R) B M B M).flip.compl₂ (LinearMap.mul R B).flip)

private theorem lTensorEval_tmul_tmul (φ : M →ₗ[R] M) (b b₀ : B) (m : M) :
    lTensorEval (φ ⊗ₜ[R] b) (b₀ ⊗ₜ[R] m) = (b₀ * b) ⊗ₜ[R] φ m := by
  simp [lTensorEval]


variable {d : A →ₗ[R] A} (Mm : UngradedAInfinityRightModule d M) (dB : B →ₗ[R] B)

/-- The evaluation map is `B`-linear for left multiplication on the factor `B`. -/
private theorem lTensorEval_smul (z : (M →ₗ[R] M) ⊗[R] B) (b : B) (y : B ⊗[R] M) :
    lTensorEval z (b • y) = b • lTensorEval z y := by
  induction z using TensorProduct.inductionOn with
  | tmul φ c =>
    induction y using TensorProduct.inductionOn with
    | tmul b₀ m => simp [TensorProduct.smul_tmul', lTensorEval_tmul_tmul, mul_assoc]
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]

/-- `d_B ⊗ 1` satisfies the Leibniz rule for left multiplication on the factor `B`. -/
private theorem rTensor_smul {dB : B →ₗ[R] B} (hB : IsUngradedDGAlgebra dB) (b : B)
    (y : B ⊗[R] M) : dB.rTensor M (b • y) = dB b • y + b • dB.rTensor M y := by
  induction y using TensorProduct.inductionOn with
  | tmul b₀ m => simp [TensorProduct.smul_tmul', hB.map_mul, TensorProduct.add_tmul]
  | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']; abel

private noncomputable def lTensorAct : (n : ℕ) →
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A ⊗[R] B) (B ⊗[R] M →ₗ[R] B ⊗[R] M)
  | 0 => lTensorEval.compMultilinearMap
      ((Mm.act 0).tensorMap (MultilinearMap.mkPiAlgebraFin R 0 B)) +
      MultilinearMap.constOfIsEmpty (RingHom.id R) _ (dB.rTensor M)
  | n + 1 => lTensorEval.compMultilinearMap
      ((Mm.act (n + 1)).tensorMap (MultilinearMap.mkPiAlgebraFin R (n + 1) B))

private theorem lTensorAct_tmul_tmul (n : ℕ) (a : Fin n → A) (b : Fin n → B) (b₀ : B) (m : M) :
    Mm.lTensorAct dB n (fun i => a i ⊗ₜ[R] b i) (b₀ ⊗ₜ[R] m) =
      (b₀ * (List.ofFn b).prod) ⊗ₜ[R] Mm.act n a m + if n = 0 then dB b₀ ⊗ₜ[R] m else 0 := by
  cases n with
  | zero =>
    simp [lTensorAct, lTensorEval_tmul_tmul, MultilinearMap.mkPiAlgebraFin_apply]
  | succ n =>
    simp [lTensorAct, lTensorEval_tmul_tmul, MultilinearMap.mkPiAlgebraFin_apply]

private theorem act_congr {j j' : ℕ} (h : j = j') {a : Fin j → A} {a' : Fin j' → A}
    (ha : ∀ l, a l = a' (Fin.cast h l)) : Mm.act j a = Mm.act j' a' := by
  subst h
  exact congrArg (Mm.act j) (funext ha)

private theorem prod_ofFn_eq_one {j : ℕ} (hj : j = 0) (f : Fin j → B) : (List.ofFn f).prod = 1 := by
  subst hj
  simp

variable {dB}

private theorem lTensorAct_comp_tmul (hB : IsUngradedDGAlgebra dB) {n : ℕ} (k : Fin (n + 1))
    (a : Fin n → A) (b : Fin n → B) (b₀ : B) (m : M) :
    Mm.lTensorAct dB (n - k) (fun l => a ⟨k + l, by omega⟩ ⊗ₜ[R] b ⟨k + l, by omega⟩)
        (Mm.lTensorAct dB k (fun l => a ⟨l, by omega⟩ ⊗ₜ[R] b ⟨l, by omega⟩) (b₀ ⊗ₜ[R] m)) =
      (b₀ * (List.ofFn b).prod) ⊗ₜ[R]
          Mm.act (n - k) (fun l => a ⟨k + l, by omega⟩) (Mm.act k (fun l => a ⟨l, by omega⟩) m) +
        (if (k : ℕ) = n then dB (b₀ * (List.ofFn b).prod) ⊗ₜ[R] Mm.act n a m else 0) +
        (if (k : ℕ) = 0 then (dB b₀ * (List.ofFn b).prod) ⊗ₜ[R] Mm.act n a m else 0) := by
  have hk := k.isLt
  have hπ := List.prod_ofFn_mul_prod_ofFn (Nat.lt_succ_iff.mp hk) b
  rw [lTensorAct_tmul_tmul, map_add, lTensorAct_tmul_tmul, mul_assoc, hπ]
  by_cases h0 : (k : ℕ) = 0
  · rw [ite_eq_left h0, lTensorAct_tmul_tmul, hB.map_map, TensorProduct.zero_tmul, ite_self,
      add_zero, ite_eq_left h0]
    have ht : (List.ofFn fun l : Fin (n - k) => b ⟨k + l, by omega⟩).prod = (List.ofFn b).prod := by
      rw [← hπ, prod_ofFn_eq_one h0, one_mul]
    have hat : Mm.act (n - k) (fun l => a ⟨k + l, by omega⟩) = Mm.act n a :=
      Mm.act_congr (by omega) fun l => congrArg a (Fin.ext (by simp [h0]))
    rw [ht, hat]
    by_cases hn : (k : ℕ) = n
    · rw [ite_eq_left (by omega), ite_eq_left hn]
      have hah : Mm.act k (fun l => a ⟨l, by omega⟩) = Mm.act n a :=
        Mm.act_congr hn fun l => rfl
      rw [hah, prod_ofFn_eq_one h0, prod_ofFn_eq_one (show n = 0 by omega) b, mul_one]
    · rw [ite_eq_right (by omega), ite_eq_right hn, add_zero]
  · rw [ite_eq_right h0, map_zero, add_zero, ite_eq_right h0, add_zero]
    by_cases hn : (k : ℕ) = n
    · rw [ite_eq_left (by omega), ite_eq_left hn]
      have hah : Mm.act k (fun l => a ⟨l, by omega⟩) = Mm.act n a :=
        Mm.act_congr hn fun l => rfl
      have hh : (List.ofFn fun l : Fin k => b ⟨l, by omega⟩).prod = (List.ofFn b).prod := by
        rw [← hπ, prod_ofFn_eq_one (by omega) (fun l : Fin (n - k) => b ⟨k + l, by omega⟩),
          mul_one]
      rw [hah, hh]
    · rw [ite_eq_right (by omega), ite_eq_right hn, add_zero]

private theorem update_tmul {n : ℕ} (a : Fin n → A) (b : Fin n → B) (l : Fin n) (x : A) (y : B) :
    update (fun i => a i ⊗ₜ[R] b i) l (x ⊗ₜ[R] y) =
      fun i => update a l x i ⊗ₜ[R] update b l y i := by
  funext i
  by_cases h : i = l
  · subst h; simp
  · simp [h]

private theorem contractNth_tmul {n : ℕ} (a : Fin (n + 1) → A) (b : Fin (n + 1) → B) (l : Fin n) :
    Fin.contractNth l.castSucc (· * ·) (fun i => a i ⊗ₜ[R] b i) =
      fun i =>
        Fin.contractNth l.castSucc (· * ·) a i ⊗ₜ[R] Fin.contractNth l.castSucc (· * ·) b i := by
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem stasheffDiff_lTensorAct_tmul (hB : IsUngradedDGAlgebra dB) (n : ℕ) (a : Fin n → A)
    (b : Fin n → B) (b₀ : B) (m : M) :
    ungradedStasheffDiff (Mm.lTensorAct dB) (ungradedTensorDifferential d dB) n
        (fun i => a i ⊗ₜ[R] b i) (b₀ ⊗ₜ[R] m) =
      (b₀ * (List.ofFn b).prod) ⊗ₜ[R] ungradedStasheffDiff Mm.act d n a m +
        (b₀ * dB (List.ofFn b).prod) ⊗ₜ[R] Mm.act n a m := by
  rw [ungradedStasheffDiff_def, ungradedStasheffDiff_def, TensorProduct.tmul_sum,
    map_prod_ofFn_of_leibniz dB hB.map_mul, Finset.mul_sum, TensorProduct.sum_tmul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp l.pos
  rw [ungradedTensorDifferential_tmul, MultilinearMap.map_update_add, LinearMap.add_apply,
    update_tmul, update_tmul, lTensorAct_tmul_tmul, lTensorAct_tmul_tmul, ite_eq_right hn,
    add_zero, add_zero, update_eq_self, update_eq_self]

private theorem stasheffMul_lTensorAct_tmul (n : ℕ) (a : Fin n → A) (b : Fin n → B) (b₀ : B)
    (m : M) :
    ungradedStasheffMul (Mm.lTensorAct dB) n (fun i => a i ⊗ₜ[R] b i) (b₀ ⊗ₜ[R] m) =
      (b₀ * (List.ofFn b).prod) ⊗ₜ[R] ungradedStasheffMul Mm.act n a m := by
  cases n with
  | zero => simp
  | succ n =>
    rw [ungradedStasheffMul_succ, ungradedStasheffMul_succ, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp l.pos
    rw [contractNth_tmul, lTensorAct_tmul_tmul, ite_eq_right hn, add_zero,
      List.prod_ofFn_contractNth]

private theorem sum_ite_val_eq_last {N : Type*} [AddCommMonoid N] (n : ℕ) (y : N) :
    ∑ k : Fin (n + 1), (if (k : ℕ) = n then y else 0) = y := by
  have h (k : Fin (n + 1)) : (if (k : ℕ) = n then y else 0) = if k = Fin.last n then y else 0 := by
    simp [Fin.ext_iff]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem sum_ite_val_eq_zero {N : Type*} [AddCommMonoid N] (n : ℕ) (y : N) :
    ∑ k : Fin (n + 1), (if (k : ℕ) = 0 then y else 0) = y := by
  have h (k : Fin (n + 1)) : (if (k : ℕ) = 0 then y else 0) = if k = 0 then y else 0 := by
    exact if_congr Fin.val_eq_zero_iff rfl rfl
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem lTensorAct_stasheff [CharP R 2] (hB : IsUngradedDGAlgebra dB) (n : ℕ)
    (x : Fin n → A ⊗[R] B) (y : B ⊗[R] M) :
    ungradedStasheffComp (Mm.lTensorAct dB) n x y +
        ungradedStasheffDiff (Mm.lTensorAct dB) (ungradedTensorDifferential d dB) n x y +
        ungradedStasheffMul (Mm.lTensorAct dB) n x y = 0 := by
  rw [← ungradedStasheffCompMultilinear_apply, ← ungradedStasheffDiffMultilinear_apply,
    ← ungradedStasheffMulMultilinear_apply, ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← _root_.add_apply, ← _root_.add_apply]
  suffices h : ungradedStasheffCompMultilinear (Mm.lTensorAct dB) n +
      ungradedStasheffDiffMultilinear (Mm.lTensorAct dB) (ungradedTensorDifferential d dB) n +
      ungradedStasheffMulMultilinear (Mm.lTensorAct dB) n = 0 by
    simp [h]
  refine MultilinearMap.ext_tmul (R := R) (ι := Fin n) (A := A) (B := B)
    (N := B ⊗[R] M →ₗ[R] B ⊗[R] M) fun a b => ?_
  refine TensorProduct.ext' fun b₀ m => ?_
  simp only [_root_.add_apply, LinearMap.add_apply, _root_.zero_apply,
    LinearMap.zero_apply, ungradedStasheffCompMultilinear_apply,
    ungradedStasheffDiffMultilinear_apply, ungradedStasheffMulMultilinear_apply,
    ungradedStasheffComp_def, ungradedStasheffDiff_def]
  -- The composite terms.
  rw [Finset.sum_congr rfl fun k _ => Mm.lTensorAct_comp_tmul hB k a b b₀ m,
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_val_eq_last, sum_ite_val_eq_zero,
    ← TensorProduct.tmul_sum, ← ungradedStasheffDiff_def, stasheffDiff_lTensorAct_tmul Mm hB,
    stasheffMul_lTensorAct_tmul]
  have h := Mm.stasheff n a m
  rw [ungradedStasheffComp_def] at h
  have hL := hB.map_mul b₀ (List.ofFn b).prod
  set X := Mm.act n a m
  set c := b₀ * (List.ofFn b).prod
  calc _ = c ⊗ₜ[R] ((∑ k : Fin (n + 1), Mm.act (n - k) (fun l => a ⟨k + l, by omega⟩)
          (Mm.act k (fun l => a ⟨l, by omega⟩) m)) + ungradedStasheffDiff Mm.act d n a m +
          ungradedStasheffMul Mm.act n a m) +
        (dB c ⊗ₜ[R] X + dB c ⊗ₜ[R] X) := by
          rw [hL, TensorProduct.tmul_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
          abel
    _ = 0 := by rw [h, TensorProduct.tmul_zero, zero_add, add_self_eq_zero_of_charTwo R]


variable [CharP R 2]

/-- The **`A∞` module `B ⊗ M` over `A ⊗ B`** of an `A∞` module `M` over `A` and a differential
algebra `(B, d_B)`, over a ring of characteristic two: the operations are
`m_{n+1}(b₀ ⊗ m, a₁ ⊗ b₁, …, aₙ ⊗ bₙ) = b₀ b₁ ⋯ bₙ ⊗ m_{n+1}(m, a₁, …, aₙ)`, plus `d_B b₀ ⊗ m`
for `n = 0` (`TauCeti.UngradedAInfinityRightModule.lTensor_act_tmul_tmul`). -/
noncomputable def lTensor (hB : IsUngradedDGAlgebra dB) :
    UngradedAInfinityRightModule (ungradedTensorDifferential d dB) (B ⊗[R] M) where
  act := Mm.lTensorAct dB
  stasheff := Mm.lTensorAct_stasheff hB

variable (hB : IsUngradedDGAlgebra dB)

private theorem lTensor_act : (Mm.lTensor hB).act = Mm.lTensorAct dB :=
  (rfl)

/-- **The operations of `B ⊗ M` on pure tensors**:
`m_{n+1}(b₀ ⊗ m, a₁ ⊗ b₁, …, aₙ ⊗ bₙ) = b₀ b₁ ⋯ bₙ ⊗ m_{n+1}(m, a₁, …, aₙ)`, plus `d_B b₀ ⊗ m`
when `n = 0`. -/
@[simp]
theorem lTensor_act_tmul_tmul (n : ℕ) (a : Fin n → A) (b : Fin n → B) (b₀ : B) (m : M) :
    (Mm.lTensor hB).act n (fun i => a i ⊗ₜ[R] b i) (b₀ ⊗ₜ[R] m) =
      (b₀ * (List.ofFn b).prod) ⊗ₜ[R] Mm.act n a m + if n = 0 then dB b₀ ⊗ₜ[R] m else 0 := by
  rw [lTensor_act, lTensorAct_tmul_tmul]

/-- **The operations of `B ⊗ M` are `B`-linear**, for left multiplication on the factor `B`,
except that `m₁` satisfies the Leibniz rule `m₁(b • y) = b • m₁ y + d_B b • y`. -/
theorem lTensor_act_smul (n : ℕ) (x : Fin n → A ⊗[R] B) (b : B) (y : B ⊗[R] M) :
    (Mm.lTensor hB).act n x (b • y) =
      b • (Mm.lTensor hB).act n x y + if n = 0 then dB b • y else 0 := by
  rw [lTensor_act]
  cases n with
  | zero =>
    simp only [lTensorAct, _root_.add_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.constOfIsEmpty_apply, Function.const_apply, LinearMap.add_apply,
      lTensorEval_smul, rTensor_smul hB, smul_add, ite_true]
    abel
  | succ n =>
    simp only [lTensorAct, LinearMap.compMultilinearMap_apply, lTensorEval_smul,
      Nat.succ_ne_zero, ite_false, add_zero]

/-- **`B ⊗ M` is bounded when `M` is**: its operation `m_{n+1}`, `n ≥ 1`, vanishes when that of
`M` does. -/
theorem lTensor_act_eq_zero {n : ℕ} (hn : n ≠ 0) (h : Mm.act n = 0) :
    (Mm.lTensor hB).act n = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [lTensor_act, lTensorAct, h, MultilinearMap.tensorMap_zero_left,
    LinearMap.compMultilinearMap_zero]

/-- **`B ⊗ M` is strictly unital when `M` is**: if the operations `m_{n+1}`, `n ≥ 2`, of `M`
vanish on every input `ι s`, those of `B ⊗ M` vanish on every input `ι s ⊗ ι_B t`. -/
theorem IsStrictlyUnital.lTensor {S T : Type*} {ι : S → A} {ιB : T → B}
    (hMm : Mm.IsStrictlyUnital ι) :
    (Mm.lTensor hB).IsStrictlyUnital fun st : S × T => ι st.1 ⊗ₜ[R] ιB st.2 := by
  refine (Mm.lTensor hB).isStrictlyUnital_iff.2 fun n hn a i st hai => ?_
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [lTensor_act, lTensorAct, LinearMap.compMultilinearMap_apply,
    MultilinearMap.tensorMap_apply_eq_zero _ (fun a' ha' => hMm.act_eq_zero hn ha') hai,
    map_zero]

end UngradedAInfinityRightModule

end TauCeti
