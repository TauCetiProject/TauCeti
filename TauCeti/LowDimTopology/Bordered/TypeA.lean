/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded
public import TauCeti.LowDimTopology.Bordered.TypeD

/-!
# The box tensor product of a type `A` module with a type `D` structure

In bordered Heegaard Floer homology, the Floer complex of a closed three-manifold cut along a
surface `F` into two pieces is homotopy equivalent to the box tensor product `M ⊠ N` of a type `A`
module `M` over the algebra `A` of `F` with a type `D` structure `N` over `A`. A type `A` module
is an `A∞` right module (`TauCeti.UngradedAInfinityRightModule`) and, unlike the differential
modules of `TauCeti.LowDimTopology.Bordered.TypeD`, may carry higher operations `m_{k+1}` for
`k ≥ 2`. The box tensor differential is then

`∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))`,

where `δ^k : N → A^{⊗ k} ⊗ N` is the `k`-fold iterate of the structure map of `N`. In a basis of
generators `X` of `N` with coefficient matrix `δ`, `δ^k x` is the sum over the paths
`x = x₀ → x₁ → ⋯ → x_k` of `δ x₀ x₁ ⊗ ⋯ ⊗ δ xₖ₋₁ xₖ ⊗ xₖ`, so the box tensor differential is the
twist (`TauCeti.UngradedAInfinityRightModule.twistedDifferential`) of the module of row vectors
over the matrix algebra (`TauCeti.UngradedAInfinityRightModule.matrix`) by the Maurer–Cartan
element `δ` (`TauCeti.TypeDStructure.typeABoxDifferential`). This differential is defined on all
row vectors `X → M`; its restriction to the submodule `TauCeti.TypeDStructure.boxTensor` of
`M ⊗ N` over the idempotents, which needs strict unitality of `M`, is not established here.

The sum over `k` is infinite in general, and the box tensor product is only defined under a
boundedness hypothesis. Two are treated here, over a ring of characteristic two; under either one
the differential squares to zero.

* The module `M` is bounded: its operations `m_{k+1}` vanish for `k ≥ K`
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero`).
* The type `D` structure is bounded (`TauCeti.TypeDStructure.IsBounded`): its iterates `δ^k`
  (`TauCeti.TypeDStructure.iteratedCoeff`) vanish for `k ≥ K`
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_isBounded`).
  The derivative of a coefficient is the product of two coefficients, so the terms of the `A∞`
  relations along the paths of `N` are images of the iterates and vanish with them. This holds in
  particular when the generators carry a height which strictly increases along every nonzero
  coefficient: the paths of nonzero coefficients then have bounded length
  (`TauCeti.TypeDStructure.isBounded_of_lt`,
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_lt`).

A finite set of generators alone does not bound the sum: a coefficient `δ x x ≠ 0` gives paths of
every length. For a differential module, viewed as an `A∞` module with `m_{k+1} = 0` for `k ≥ 2`,
the differential is the box tensor differential `∂ φ = dM φ + φ ⬝ δ` of
`TauCeti.TypeDStructure.boxDifferential`
(`TauCeti.TypeDStructure.typeABoxDifferential_toUngradedAInfinityRightModule`).

## Main definitions

* `TauCeti.TypeDStructure.typeABoxDifferential`: the box tensor differential of an `A∞` module
  with a type `D` structure, on row vectors.

## Main results

* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_isBounded`:
  the differential squares to zero when the module, respectively the type `D` structure, is
  bounded; `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_lt` is the case
  of a height on the generators.
* `TauCeti.TypeDStructure.typeABoxDifferential_apply_eq_sum`: the differential as a finite sum
  over paths of generators; under either boundedness hypothesis, see
  `TauCeti.TypeDStructure.typeABoxDifferential_apply_eq_sum_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxDifferential_apply_eq_sum_of_lt`.
* `TauCeti.TypeDStructure.typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff`: the differential
  is `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))`, with the iterates of the structure map. Its
  variant `typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff_of_iteratedCoeff_eq_zero` (in the
  same namespace) assumes the iterates `δ^k` vanish for `k ≥ K`.
* `TauCeti.TypeDStructure.typeABoxDifferential_toUngradedAInfinityRightModule`: for a differential
  module it is the box tensor differential `TauCeti.TypeDStructure.boxDifferential`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (boundedness of `A∞` modules and type `D` structures, and the box tensor product,
  equation (2.29)).
-/

public section

open Finset MulOpposite

namespace TauCeti

namespace TypeDStructure

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

/-- The **box tensor differential** of an `A∞` right module `M` with a type `D` structure `N`, on
all row vectors `φ : X → M`: `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))`. It is the twist of the
matrix module of `M` by the coefficient matrix of `N`. The sum is finite when `M` or `N` is
bounded; otherwise this is `0` by the convention of
`TauCeti.UngradedAInfinityRightModule.twistedDifferential`. -/
noncomputable def typeABoxDifferential (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) : (X → M) →ₗ[R] X → M :=
  (Mm.matrix X).twistedDifferential N.coeff

theorem typeABoxDifferential_def (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) :
    N.typeABoxDifferential Mm = (Mm.matrix X).twistedDifferential N.coeff :=
  (rfl)

/-- **The box tensor differential as a sum over paths.** When the operations
`m_{n+1}(·, δ, …, δ)` of the matrix module vanish for `n ≥ K`, the `z`-component of `∂ φ` is the
sum, over the paths `x₀ → ⋯ → xₙ = z` of length `n < K`, of
`m_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
theorem typeABoxDifferential_apply_eq_sum (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → (Mm.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxDifferential Mm φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then Mm.act n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [typeABoxDifferential_def, UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (by simpa only [UngradedAInfinityRightModule.matrix_act] using hK)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    UngradedAInfinityRightModule.matrixAct_apply]

/-- **The box tensor differential of a bounded module as a sum over paths.** If the operations
`m_{n+1}` of `M` vanish for `n ≥ K`, the `z`-component of `∂ φ` is the sum, over the paths
`x₀ → ⋯ → xₙ = z` of length `n < K`, of `m_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
theorem typeABoxDifferential_apply_eq_sum_of_act_eq_zero (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (φ : X → M) (z : X) :
    N.typeABoxDifferential Mm φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then Mm.act n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 :=
  N.typeABoxDifferential_apply_eq_sum Mm (fun n hn => by
    rw [Mm.matrixAct_eq_zero_of_act_eq_zero X (hK n hn), zero_apply]) φ z

/-- **The box tensor differential with a bounded type `D` structure as a sum over paths.** If a
height `h` on the generators strictly increases along every nonzero coefficient of `N`, the
`z`-component of `∂ φ` is the sum, over the paths `x₀ → ⋯ → xₙ = z` of length `n` at most the
largest height, of `m_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
theorem typeABoxDifferential_apply_eq_sum_of_lt (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) (z : X) :
    N.typeABoxDifferential Mm φ z = ∑ n ∈ range (univ.sup h + 1), ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then Mm.act n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 :=
  N.typeABoxDifferential_apply_eq_sum Mm
    (fun _ hn => Mm.matrixAct_eq_zero_of_lt X h hn fun _ => hh) φ z

/-- **The box tensor differential of a bounded module squares to zero.** If the operations
`m_{k+1}` of `M` vanish for `k ≥ K`, then `∂ ∘ ∂ = 0` on the row vectors `X → M`, over a ring of
characteristic two. -/
theorem typeABoxDifferential_typeABoxDifferential_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : X → M) :
    N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 :=
  (Mm.matrix X).twistedDifferential_twistedDifferential N.map_coeff_add_coeff_mul_coeff
    (Set.mem_univ _) (Set.mem_univ _) (K := K) (fun n hn F _ => by
      rw [UngradedAInfinityRightModule.matrix_act, Mm.matrixAct_eq_zero_of_act_eq_zero X (hK n hn),
        zero_apply]) φ

/-! ### Bounded type `D` structures -/

/-- The operations of the matrix module along the coefficient matrix of `N`, with linear maps `L`
applied to the coefficients, evaluate the operations of `M` on the iterates `δⁿ` of `N`. -/
theorem matrixAct_map_coeff_apply (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) (n : ℕ) (L : Fin n → A →ₗ[R] A) (φ : X → M) (z : X) :
    Mm.matrixAct X n (fun l => N.coeff.map (L l)) φ z =
      ∑ x, PiTensorProduct.lift ((Mm.act n).compLinearMap L) (N.iteratedCoeff n x z) (φ x) := by
  rw [Mm.matrixAct_apply, ← Finset.sum_filter]
  convert (N.sum_lift_iteratedCoeff n (fun x => (LinearMap.applyₗ (φ x)).compMultilinearMap
    ((Mm.act n).compLinearMap L)) z).symm using 2 with x
  · simp
  · simp

/-- If the iterate `δⁿ` of `N` vanishes, so does the operation `m_{n+1}` of the matrix module on
every tuple of copies of the coefficient matrix of `N` and of its derivative. -/
theorem matrixAct_eq_zero_of_iteratedCoeff_eq_zero (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) {n : ℕ} (hn : ∀ x z, N.iteratedCoeff n x z = 0)
    {F : Fin n → Matrix X X A} (hF : ∀ l, F l = N.coeff ∨ F l = N.coeff.map d) :
    Mm.matrixAct X n F = 0 := by
  classical
  have hL : F = fun l => N.coeff.map ⇑(if F l = N.coeff then LinearMap.id else d) := by
    funext l
    split_ifs with h
    · rw [h]
      simp
    · exact (hF l).resolve_left h
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [hL, matrixAct_map_coeff_apply]
  simp [hn]

/-- **The box tensor differential in terms of the iterates of `N`.** When the operations
`m_{n+1}(·, δ, …, δ)` of the matrix module vanish for `n ≥ K`, the box tensor differential is
`∂ (m ⊗ x) = ∑_{n < K} (m_{n+1} ⊗ 1) (m ⊗ δⁿ (x))`. -/
theorem typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → (Mm.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxDifferential Mm φ z =
      ∑ n ∈ range K, ∑ x, PiTensorProduct.lift (Mm.act n) (N.iteratedCoeff n x z) (φ x) := by
  rw [typeABoxDifferential_def, UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (by simpa only [UngradedAInfinityRightModule.matrix_act] using hK)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act]
  refine Finset.sum_congr rfl fun n _ => ?_
  simpa [MultilinearMap.compLinearMap_id] using
    N.matrixAct_map_coeff_apply Mm n (fun _ => LinearMap.id) φ z

/-- **The box tensor differential of a bounded type `D` structure in terms of its iterates.** If
the iterates `δⁿ` of `N` vanish for `n ≥ K`, the box tensor differential is
`∂ (m ⊗ x) = ∑_{n < K} (m_{n+1} ⊗ 1) (m ⊗ δⁿ (x))`. -/
theorem typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff_of_iteratedCoeff_eq_zero
    (N : TypeDStructure d ι X) (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) (φ : X → M) (z : X) :
    N.typeABoxDifferential Mm φ z =
      ∑ n ∈ range K, ∑ x, PiTensorProduct.lift (Mm.act n) (N.iteratedCoeff n x z) (φ x) :=
  N.typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff Mm (fun n hn =>
    N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero Mm (hK n hn) fun _ => Or.inl rfl) φ z

/-- **The box tensor differential with a bounded type `D` structure squares to zero.** If the
iterates `δⁿ` of `N` vanish for all large `n`, then `∂ ∘ ∂ = 0` on the row vectors `X → M`, over a
ring of characteristic two, whatever the operations of `M`. -/
theorem typeABoxDifferential_typeABoxDifferential_of_isBounded [CharP R 2]
    (N : TypeDStructure d ι X) (Mm : UngradedAInfinityRightModule d M) (hN : N.IsBounded)
    (φ : X → M) : N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  -- In characteristic two `δ * δ = d δ`, and `m_{n+1}` vanishes along `δ` and `d δ` for `n ≥ K`.
  exact (Mm.matrix X).twistedDifferential_twistedDifferential N.map_coeff_add_coeff_mul_coeff
    (U := {N.coeff, N.coeff.map d}) (Or.inl rfl) (Or.inr N.map_coeff_eq_coeff_mul_coeff.symm)
    (K := K) (fun n hn F hF => by
      rw [UngradedAInfinityRightModule.matrix_act]
      exact N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero Mm (hK n hn) hF) φ

/-- **The box tensor differential with a bounded type `D` structure squares to zero.** If a
height `h` on the generators strictly increases along every nonzero coefficient of `N`, then
`∂ ∘ ∂ = 0` on the row vectors `X → M`, over a ring of characteristic two, whatever the operations
of `M`. -/
theorem typeABoxDifferential_typeABoxDifferential_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) :
    N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 :=
  N.typeABoxDifferential_typeABoxDifferential_of_isBounded Mm (N.isBounded_of_lt h hh) φ

/-- **The box tensor product with a differential module.** For a differential right module,
viewed as an `A∞` module, the box tensor differential is `∂ φ = dM φ + φ ⬝ δ`, the differential
`TauCeti.TypeDStructure.boxDifferential`. -/
theorem typeABoxDifferential_toUngradedAInfinityRightModule [CharP R 2] [Module Aᵐᵒᵖ M]
    [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (N : TypeDStructure d ι X) :
    N.typeABoxDifferential hM.toUngradedAInfinityRightModule = N.boxDifferential dM := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [typeABoxDifferential_apply_eq_sum_of_act_eq_zero (K := 2) _ _ fun n hn => ?_]
  · simp only [sum_range_succ, range_zero, sum_empty, zero_add, boxDifferential_apply,
      Pi.add_apply, IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_zero,
      IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one]
    rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp, ← (piFinTwoEquiv fun _ => X).symm.sum_comp,
      Fintype.sum_prod_type]
    simp [continuationMap_apply (R := R) (M := M) N.coeff]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact hM.toUngradedAInfinityRightModule_act_add_two n

end TypeDStructure

end TauCeti
