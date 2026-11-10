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

**Functoriality in the type `D` structure.** A morphism `F` from `N` to `N'`, a matrix of
coefficients, induces the map `T_F = id_M ⊠ F` from `M ⊠ N` to `M ⊠ N'`
(`TauCeti.TypeDStructure.typeABoxMap`): the `y`-component of `T_F φ` is the sum, over the paths
`x₀ → ⋯ → xᵢ` in `X` and `y₀ → ⋯ → yⱼ = y` in `X'`, of

`m_{i+j+2}(φ x₀, δ x₀ x₁, …, δ xᵢ₋₁ xᵢ, F xᵢ y₀, δ' y₀ y₁, …, δ' yⱼ₋₁ yⱼ)`.

 It is the off-diagonal component of the box tensor
differential of the block upper-triangular matrix `C = fromBlocks δ F 0 δ'` on the generators
`X ⊕ X'`: a path of generators from `X` to `X'` along `C` crosses from `X` to `X'` exactly once,
through an entry of `F`. The matrix `C` is a Maurer–Cartan element only when `F` is a cycle; in
general its curvature `d C + C * C` is `fromBlocks 0 (∂F) 0 0`, where `∂F` is the differential of
morphisms, and the square of the twisted differential inserts this curvature once
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential_eq_sum`). Reading
off the off-diagonal component gives, under either boundedness hypothesis,

`∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}`.

So a homomorphism of type `D` structures (`∂F = 0`) induces a chain map, and homotopic
homomorphisms (`∂H = F + G`) induce chain homotopic maps, with homotopy `T_H`. For a differential
module `T_F` is the action `φ ↦ φ ⬝ F` of `TauCeti.LowDimTopology.Bordered.TypeD`. That composites
and identity morphisms induce, up to homotopy, composites and identities is not established here;
the identity needs a strictly unital module.

## Main definitions

* `TauCeti.TypeDStructure.typeABoxDifferential`: the box tensor differential of an `A∞` module
  with a type `D` structure, on row vectors.
* `TauCeti.TypeDStructure.typeABoxMap`: the map of box tensor products induced by a morphism of
  type `D` structures.

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
* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_lt`: `∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}`
  when the module, respectively the type `D` structures, are bounded.
* `TauCeti.TypeDStructure.typeABoxMap_apply_eq_sum`: the induced map as a finite sum over paths
  with exactly one step through `F`; under either boundedness hypothesis, see
  `TauCeti.TypeDStructure.typeABoxMap_apply_eq_sum_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxMap_apply_eq_sum_of_lt`.
* In `TauCeti.TypeDStructure`,
  `typeABoxDifferential_typeABoxMap_of_morphismDifferential_eq_zero_of_act_eq_zero`,
  `typeABoxMap_add_typeABoxMap_of_act_eq_zero` and their `_of_lt` versions: homomorphisms induce
  chain maps, and homotopic homomorphisms induce homotopic chain maps.
* `TauCeti.TypeDStructure.typeABoxMap_toUngradedAInfinityRightModule`: for a differential module,
  `T_F` is the action of `F` on row vectors.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (boundedness of `A∞` modules and type `D` structures, and the box tensor product,
  equation (2.29), with its functoriality in morphisms of type `D` structures).
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

/-! ### Maps induced by morphisms of type `D` structures -/

section Morphism

variable {X' : Type*} [Fintype X'] [DecidableEq X']

/-- The **map induced on box tensor products** by a morphism `F` from `N` to `N'`: on row vectors,
`φ ↦ ∑_{i, j} m_{i+j+2}(φ, δ, …, δ, F, δ', …, δ')`, with `i` copies of the coefficient matrix `δ`
of `N` and `j` copies of the coefficient matrix `δ'` of `N'`, evaluated along the paths of
generators.
It is the `X'`-component of the box tensor differential, restricted to row vectors supported on
`X`, of the block upper-triangular matrix `fromBlocks δ F 0 δ'` on `X ⊕ X'`; when `F` is a cycle,
`∂F = 0`, this is the coefficient matrix of the mapping cone of `F`. As for
`TauCeti.TypeDStructure.typeABoxDifferential`, the sum is finite when `M`, or `N` and `N'`, are
bounded; the construction is `0` by convention whenever the operations along
`fromBlocks δ F 0 δ'` do not vanish from some arity on. -/
noncomputable def typeABoxMap (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A) : (X → M) →ₗ[R] X' → M :=
  LinearMap.funLeft R M Sum.inr ∘ₗ
    (Mm.matrix (X ⊕ X')).twistedDifferential (Matrix.fromBlocks N.coeff F 0 N'.coeff) ∘ₗ
    (LinearEquiv.sumArrowLequivProdArrow X X' R M).symm.toLinearMap ∘ₗ
    LinearMap.inl R (X → M) (X' → M)

theorem typeABoxMap_apply (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A) (φ : X → M) (z : X') :
    typeABoxMap N N' Mm F φ z =
      (Mm.matrix (X ⊕ X')).twistedDifferential (Matrix.fromBlocks N.coeff F 0 N'.coeff)
        (Sum.elim φ 0) (Sum.inr z) := by
  have h : (LinearEquiv.sumArrowLequivProdArrow X X' R M).symm (φ, 0) = Sum.elim φ 0 := by
    funext a
    cases a <;> simp
  simp [typeABoxMap, LinearMap.funLeft_apply, h]

/-- **The zero morphism induces the zero map.** -/
@[simp]
theorem typeABoxMap_zero (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) : typeABoxMap N N' Mm 0 = 0 := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [typeABoxMap_apply, UngradedAInfinityRightModule.twistedDifferential_def]
  set g : ℕ → (X ⊕ X' → M) →ₗ[R] X ⊕ X' → M :=
    fun n => (Mm.matrix (X ⊕ X')).act n fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff
  -- Every operation along the block-diagonal matrix keeps `X` and `X'` apart.
  have hg (n : ℕ) : g n (Sum.elim φ 0) (Sum.inr z) = 0 := by
    have h := Mm.sum_matrixAct_update_fromBlocks_apply_inr (n := n) N.coeff N'.coeff 0 0 φ z
    simp only [Matrix.fromBlocks_zero, MultilinearMap.map_update_zero, LinearMap.zero_apply,
      Pi.zero_apply, sum_const_zero] at h
    simp [g, ← h]
  let ev : ((X ⊕ X' → M) →ₗ[R] X ⊕ X' → M) →+ M :=
    { toFun := fun T => T (Sum.elim φ 0) (Sum.inr z)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  -- The goal is the evaluation `ev` of the `finsum`; `ev` commutes with it when it is finite.
  have hev (T : (X ⊕ X' → M) →ₗ[R] X ⊕ X' → M) : T (Sum.elim φ 0) (Sum.inr z) = ev T := rfl
  rw [hev, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hfin : (Function.support g).Finite
  · rw [map_finsum ev hfin]
    exact finsum_eq_zero_of_forall_eq_zero hg
  · rw [finsum_of_infinite_support hfin, map_zero]

/-- **The induced map as a sum over paths.** When the operations of the matrix module of
`X ⊕ X'` along `fromBlocks δ F 0 δ'` vanish from arity `K` on, the `z`-component of `T_F φ` is the
sum, over the paths `x₀ → ⋯ → xₙ = z` in `X ⊕ X'` of length `n < K` and the slots `l < n`, of
`m_{n+1}(φ x₀, …)` with the entry of `F` at step `l` and the entries of `δ` or `δ'` at the other
steps. Such a term vanishes unless the path stays in `X` up to step `l`, crosses to `X'` there and
stays in `X'` afterwards: the terms are the `m_{i+j+2}(φ x₀, δ…, F xᵢ y₀, δ'…)` with `i = l`. -/
theorem typeABoxMap_apply_eq_sum (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A) {K : ℕ}
    (hK : ∀ n, K ≤ n →
      (Mm.matrixAct (X ⊕ X') n fun _ => Matrix.fromBlocks N.coeff F 0 N'.coeff) = 0)
    (φ : X → M) (z : X') :
    typeABoxMap N N' Mm F φ z = ∑ n ∈ range K, ∑ l : Fin n, ∑ x : Fin (n + 1) → X ⊕ X',
      if x (Fin.last n) = Sum.inr z then
        Mm.act n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
          (Matrix.fromBlocks 0 F 0 0) t (x t.castSucc) (x t.succ)) (Sum.elim φ 0 (x 0))
      else 0 := by
  rw [typeABoxMap_apply, UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (by simpa only [UngradedAInfinityRightModule.matrix_act] using hK)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    ← Mm.sum_matrixAct_update_fromBlocks_apply_inr N.coeff N'.coeff 0 F,
    UngradedAInfinityRightModule.matrixAct_apply]

/-- **The induced map of a bounded module as a sum over paths.** If the operations `m_{n+1}` of
`M` vanish for `n ≥ K`, `T_F φ` is the sum of `TauCeti.TypeDStructure.typeABoxMap_apply_eq_sum`
over the paths of length `n < K`. -/
theorem typeABoxMap_apply_eq_sum_of_act_eq_zero (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A)
    {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : X → M) (z : X') :
    typeABoxMap N N' Mm F φ z = ∑ n ∈ range K, ∑ l : Fin n, ∑ x : Fin (n + 1) → X ⊕ X',
      if x (Fin.last n) = Sum.inr z then
        Mm.act n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
          (Matrix.fromBlocks 0 F 0 0) t (x t.castSucc) (x t.succ)) (Sum.elim φ 0 (x 0))
      else 0 :=
  typeABoxMap_apply_eq_sum N N' Mm F (fun n hn => by
    rw [Mm.matrixAct_eq_zero_of_act_eq_zero _ (hK n hn), zero_apply]) φ z

section Core

variable {U : Set (Matrix (X ⊕ X') (X ⊕ X') A)} {K : ℕ}

/-- The hypotheses shared by the two boundedness conditions: the operations of the matrix module
of `X ⊕ X'` vanish from arity `K` on along matrices of a set `U` closed under the entrywise
differential and containing the block upper-triangular matrices `fromBlocks δ G 0 δ'` and the
off-diagonal blocks `fromBlocks 0 G 0 0`. -/
private structure Bound (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (U : Set (Matrix (X ⊕ X') (X ⊕ X') A)) (K : ℕ) :
    Prop where
  act_eq_zero : ∀ n, K ≤ n → ∀ u : Fin n → Matrix (X ⊕ X') (X ⊕ X') A, (∀ l, u l ∈ U) →
    Mm.matrixAct (X ⊕ X') n u = 0
  fromBlocks_mem : ∀ G : Matrix X X' A, Matrix.fromBlocks N.coeff G 0 N'.coeff ∈ U
  fromBlocks_zero_mem : ∀ G : Matrix X X' A, Matrix.fromBlocks 0 G 0 0 ∈ U
  map_mem : ∀ P ∈ U, P.map d ∈ U

variable {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'}
  {Mm : UngradedAInfinityRightModule d M}

private theorem Bound.act_fromBlocks (hB : Bound N N' Mm U K) (G : Matrix X X' A) :
    ∀ n, K ≤ n → ((Mm.matrix (X ⊕ X')).act n fun _ => Matrix.fromBlocks N.coeff G 0 N'.coeff) = 0 :=
  fun n hn => by
    rw [UngradedAInfinityRightModule.matrix_act]
    exact hB.act_eq_zero n hn _ fun _ => hB.fromBlocks_mem G

private theorem Bound.act_coeff (hB : Bound N N' Mm U K) :
    ∀ n, K ≤ n → ((Mm.matrix X).act n fun _ => N.coeff) = 0 := by
  intro n hn
  refine LinearMap.ext fun φ => funext fun z => ?_
  have h := Mm.matrixAct_apply_inl (n := n) (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff)
    (fun _ _ _ => by simp) (Sum.elim φ 0) z
  simp only [Matrix.toBlocks_fromBlocks₁₁, Sum.elim_comp_inl] at h
  rw [UngradedAInfinityRightModule.matrix_act, ← h, hB.act_eq_zero n hn _
    fun _ => hB.fromBlocks_mem 0]
  simp

private theorem Bound.act_coeff' (hB : Bound N N' Mm U K) :
    ∀ n, K ≤ n → ((Mm.matrix X').act n fun _ => N'.coeff) = 0 := by
  intro n hn
  refine LinearMap.ext fun ψ => funext fun z => ?_
  have h := Mm.matrixAct_sumElim_zero_apply_inr (n := n)
    (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) (fun _ _ _ => by simp) ψ z
  simp only [Matrix.toBlocks_fromBlocks₂₂] at h
  rw [UngradedAInfinityRightModule.matrix_act, ← h, hB.act_eq_zero n hn _
    fun _ => hB.fromBlocks_mem 0]
  simp

/-- The `X`-components of the box tensor differential of `fromBlocks δ G 0 δ'` are the box tensor
differential of `N` on the `X`-components. -/
private theorem Bound.twistedDifferential_apply_inl (hB : Bound N N' Mm U K) (G : Matrix X X' A)
    (ψ : X ⊕ X' → M) (z : X) :
    (Mm.matrix (X ⊕ X')).twistedDifferential (Matrix.fromBlocks N.coeff G 0 N'.coeff) ψ
      (Sum.inl z) = N.typeABoxDifferential Mm (ψ ∘ Sum.inl) z := by
  rw [typeABoxDifferential_def, UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (hB.act_fromBlocks G), UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    hB.act_coeff]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act]
  refine sum_congr rfl fun n _ => ?_
  rw [Mm.matrixAct_apply_inl _ (fun _ _ _ => by simp)]
  simp only [Matrix.toBlocks_fromBlocks₁₁]

/-- The `X'`-components of the box tensor differential of `fromBlocks δ G 0 δ'` are the induced map
of `G` on the `X`-components plus the box tensor differential of `N'` on the `X'`-components. -/
private theorem Bound.twistedDifferential_apply_inr (hB : Bound N N' Mm U K) (G : Matrix X X' A)
    (a : X → M) (b : X' → M) (z : X') :
    (Mm.matrix (X ⊕ X')).twistedDifferential (Matrix.fromBlocks N.coeff G 0 N'.coeff)
      (Sum.elim a b) (Sum.inr z) =
      typeABoxMap N N' Mm G a z + N'.typeABoxDifferential Mm b z := by
  have hab : Sum.elim a b = Sum.elim a (0 : X' → M) + Sum.elim (0 : X → M) b := by
    funext w
    cases w <;> simp
  rw [hab, map_add, Pi.add_apply, ← typeABoxMap_apply, typeABoxDifferential_def,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ (hB.act_fromBlocks G),
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ hB.act_coeff']
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act]
  refine congrArg _ (sum_congr rfl fun n _ => ?_)
  rw [Mm.matrixAct_sumElim_zero_apply_inr _ (fun _ _ _ => by simp)]
  simp only [Matrix.toBlocks_fromBlocks₂₂]

/-- The induced map of `G` as a sum of insertions of the off-diagonal block `fromBlocks 0 G 0 0`
into the block upper-triangular matrix `fromBlocks δ F 0 δ'`, for any `F`. -/
private theorem Bound.typeABoxMap_apply_eq_sum (hB : Bound N N' Mm U K) (F G : Matrix X X' A)
    (φ : X → M) (z : X') :
    typeABoxMap N N' Mm G φ z = ∑ n ∈ range K, ∑ l : Fin n, Mm.matrixAct (X ⊕ X') n
      (Function.update (fun _ => Matrix.fromBlocks N.coeff F 0 N'.coeff) l
        (Matrix.fromBlocks 0 G 0 0)) (Sum.elim φ 0) (Sum.inr z) := by
  rw [typeABoxMap_apply, UngradedAInfinityRightModule.twistedDifferential_eq_sum _
    (hB.act_fromBlocks G)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    Mm.sum_matrixAct_update_fromBlocks_apply_inr]

private theorem Bound.typeABoxMap_add (hB : Bound N N' Mm U K) (F G : Matrix X X' A) :
    typeABoxMap N N' Mm (F + G) = typeABoxMap N N' Mm F + typeABoxMap N N' Mm G := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  have hE : Matrix.fromBlocks (0 : Matrix X X A) (F + G) (0 : Matrix X' X A) (0 : Matrix X' X' A) =
      Matrix.fromBlocks 0 F 0 0 + Matrix.fromBlocks 0 G 0 0 := by
    simp [Matrix.fromBlocks_add]
  simp only [LinearMap.add_apply, Pi.add_apply, hB.typeABoxMap_apply_eq_sum 0, hE,
    MultilinearMap.map_update_add, LinearMap.add_apply, Pi.add_apply, sum_add_distrib]

/-- The core of `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_act_eq_zero` and
`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_lt`. -/
private theorem Bound.typeABoxDifferential_typeABoxMap [CharP R 2] (hB : Bound N N' Mm U K)
    (F : Matrix X X' A) (φ : X → M) :
    N'.typeABoxDifferential Mm (typeABoxMap N N' Mm F φ) +
        typeABoxMap N N' Mm F (N.typeABoxDifferential Mm φ) =
      typeABoxMap N N' Mm (morphismDifferential N N' F) φ := by
  funext z
  set C := Matrix.fromBlocks N.coeff F 0 N'.coeff
  have hcurv := map_fromBlocks_add_fromBlocks_mul_fromBlocks N N' F
  -- The square of the box tensor differential of `C` inserts its curvature `fromBlocks 0 ∂F 0 0`.
  have hsq := (Mm.matrix (X ⊕ X')).twistedDifferential_twistedDifferential_eq_sum
    (β := C) (U := U) (K := K) (hB.fromBlocks_mem F)
    (by rw [LinearMap.mapMatrix_apply]; exact hB.map_mem _ (hB.fromBlocks_mem F))
    (by rw [LinearMap.mapMatrix_apply, hcurv]; exact hB.fromBlocks_zero_mem _)
    (fun n hn u hu => by
      rw [UngradedAInfinityRightModule.matrix_act]; exact hB.act_eq_zero n hn u hu)
    (Sum.elim φ 0)
  rw [LinearMap.mapMatrix_apply, hcurv] at hsq
  -- On row vectors supported on `X`, the box tensor differential of `C` is `(∂ φ, T_F φ)`.
  have h₁ : (Mm.matrix (X ⊕ X')).twistedDifferential C (Sum.elim φ 0) =
      Sum.elim (N.typeABoxDifferential Mm φ) (typeABoxMap N N' Mm F φ) := by
    funext w
    rcases w with a | b
    · rw [hB.twistedDifferential_apply_inl, Sum.elim_comp_inl, Sum.elim_inl]
    · rw [hB.twistedDifferential_apply_inr, map_zero, Pi.zero_apply, add_zero, Sum.elim_inr]
  have h := congrFun hsq (Sum.inr z)
  rw [h₁, hB.twistedDifferential_apply_inr] at h
  simp only [Finset.sum_apply, UngradedAInfinityRightModule.matrix_act] at h
  rw [Pi.add_apply, add_comm, h, hB.typeABoxMap_apply_eq_sum F]

/-- The operations of a bounded module vanish from arity `K` on along all matrices. -/
private theorem bound_of_act_eq_zero (hK : ∀ n, K ≤ n → Mm.act n = 0) :
    Bound N N' Mm Set.univ K where
  act_eq_zero n hn _ _ := by rw [Mm.matrixAct_eq_zero_of_act_eq_zero _ (hK n hn), zero_apply]
  fromBlocks_mem _ := trivial
  fromBlocks_zero_mem _ := trivial
  map_mem _ _ := trivial

end Core

/-- **The induced maps of a bounded module.** Over a ring of characteristic two, if the operations
`m_{k+1}` of `M` vanish for `k ≥ K`, the map `T_F` induced by any matrix `F` from `N` to `N'`
satisfies `∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}`, where `∂` and `∂'` are the box tensor differentials and
`∂F` is the differential of morphisms. So a homomorphism of type `D` structures induces a chain map
(`typeABoxDifferential_typeABoxMap_of_morphismDifferential_eq_zero_of_act_eq_zero`), and
homotopic homomorphisms induce homotopic chain maps
(`TauCeti.TypeDStructure.typeABoxMap_add_typeABoxMap_of_act_eq_zero`). -/
theorem typeABoxDifferential_typeABoxMap_of_act_eq_zero [CharP R 2] (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (F : Matrix X X' A) (φ : X → M) :
    N'.typeABoxDifferential Mm (typeABoxMap N N' Mm F φ) +
        typeABoxMap N N' Mm F (N.typeABoxDifferential Mm φ) =
      typeABoxMap N N' Mm (morphismDifferential N N' F) φ :=
  (bound_of_act_eq_zero hK).typeABoxDifferential_typeABoxMap F φ

/-- **Additivity of the induced maps of a bounded module.** -/
theorem typeABoxMap_add_of_act_eq_zero (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (F G : Matrix X X' A) :
    typeABoxMap N N' Mm (F + G) = typeABoxMap N N' Mm F + typeABoxMap N N' Mm G :=
  (bound_of_act_eq_zero hK).typeABoxMap_add F G

/-- **A homomorphism of type `D` structures induces a chain map of box tensor products with a
bounded module.** If `∂F = 0`, then `∂' ∘ T_F = T_F ∘ ∂`. -/
theorem typeABoxDifferential_typeABoxMap_of_morphismDifferential_eq_zero_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M)
    {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0) {F : Matrix X X' A}
    (hF : morphismDifferential N N' F = 0) (φ : X → M) :
    N'.typeABoxDifferential Mm (typeABoxMap N N' Mm F φ) =
      typeABoxMap N N' Mm F (N.typeABoxDifferential Mm φ) :=
  (add_eq_zero_iff_eq_of_charTwo R).mp <| by
    rw [typeABoxDifferential_typeABoxMap_of_act_eq_zero N N' Mm hK, hF, typeABoxMap_zero,
      LinearMap.zero_apply]

/-- **Homotopic homomorphisms induce homotopic chain maps of box tensor products with a bounded
module.** If `∂H = F + G`, then `T_F + T_G = ∂' ∘ T_H + T_H ∘ ∂`. -/
theorem typeABoxMap_add_typeABoxMap_of_act_eq_zero [CharP R 2] (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) {F G H : Matrix X X' A}
    (hH : morphismDifferential N N' H = F + G) (φ : X → M) :
    typeABoxMap N N' Mm F φ + typeABoxMap N N' Mm G φ =
      N'.typeABoxDifferential Mm (typeABoxMap N N' Mm H φ) +
        typeABoxMap N N' Mm H (N.typeABoxDifferential Mm φ) := by
  rw [typeABoxDifferential_typeABoxMap_of_act_eq_zero N N' Mm hK, hH,
    typeABoxMap_add_of_act_eq_zero N N' Mm hK, LinearMap.add_apply]

/-- The height on `X ⊕ X'` of two heights on `X` and `X'`, that of `X'` shifted above that of
`X`. -/
private def sumHeight (h : X → ℕ) (h' : X' → ℕ) : X ⊕ X' → ℕ :=
  Sum.elim h fun y => univ.sup h + 1 + h' y

/-- The block upper-triangular matrices increase `sumHeight h h'` when `δ` and `δ'` increase `h`
and `h'`. -/
private theorem bound_of_lt {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'}
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) :
    Bound N N' Mm {P | ∀ a b, P a b ≠ 0 → sumHeight h h' a < sumHeight h h' b}
      (univ.sup h + univ.sup h' + 2) where
  act_eq_zero n hn u hu := by
    have hsup : univ.sup (sumHeight h h') ≤ univ.sup h + univ.sup h' + 1 :=
      Finset.sup_le fun a _ => by
        rcases a with x | y
        · have := le_sup (f := h) (mem_univ x)
          simp only [sumHeight, Sum.elim_inl]
          omega
        · have := le_sup (f := h') (mem_univ y)
          simp only [sumHeight, Sum.elim_inr]
          omega
    exact Mm.matrixAct_eq_zero_of_lt _ _ (by omega) fun l => hu l
  fromBlocks_mem G a b hab := by
    have hle (x : X) : h x ≤ univ.sup h := le_sup (f := h) (mem_univ x)
    rcases a with x | x <;> rcases b with y | y <;>
      simp only [sumHeight, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at hab ⊢
    · exact hh x y hab
    · have := hle x; omega
    · simp at hab
    · have := hh' x y hab; omega
  fromBlocks_zero_mem G a b hab := by
    have hle (x : X) : h x ≤ univ.sup h := le_sup (f := h) (mem_univ x)
    rcases a with x | x <;> rcases b with y | y <;> simp at hab
    simp only [sumHeight, Sum.elim_inl, Sum.elim_inr]
    have := hle x; omega
  map_mem P hP a b hab := hP a b fun h0 => hab (by simp [h0])

/-- **The induced maps with bounded type `D` structures.** Over a ring of characteristic two, if
heights on the generators of `N` and of `N'` strictly increase along their nonzero coefficients,
the map `T_F` induced by any matrix `F` from `N` to `N'` satisfies
`∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}`, whatever the operations of `M`. -/
theorem typeABoxDifferential_typeABoxMap_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) (φ : X → M) :
    N'.typeABoxDifferential Mm (typeABoxMap N N' Mm F φ) +
        typeABoxMap N N' Mm F (N.typeABoxDifferential Mm φ) =
      typeABoxMap N N' Mm (morphismDifferential N N' F) φ :=
  (bound_of_lt Mm h hh h' hh').typeABoxDifferential_typeABoxMap F φ

/-- **The induced map with bounded type `D` structures as a sum over paths.** If heights on the
generators of `N` and of `N'` strictly increase along their nonzero coefficients, `T_F φ` is the
sum of `TauCeti.TypeDStructure.typeABoxMap_apply_eq_sum` over the paths of length `n` at most
the sum of the largest heights plus one, whatever the operations of `M`. -/
theorem typeABoxMap_apply_eq_sum_of_lt (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) (φ : X → M)
    (z : X') :
    typeABoxMap N N' Mm F φ z =
      ∑ n ∈ range (univ.sup h + univ.sup h' + 2), ∑ l : Fin n, ∑ x : Fin (n + 1) → X ⊕ X',
        if x (Fin.last n) = Sum.inr z then
          Mm.act n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t (x t.castSucc) (x t.succ)) (Sum.elim φ 0 (x 0))
        else 0 :=
  have hB := bound_of_lt Mm h hh h' hh'
  typeABoxMap_apply_eq_sum N N' Mm F (fun n hn => hB.act_eq_zero n hn _ fun _ =>
    hB.fromBlocks_mem F) φ z

/-- **Additivity of the induced maps with bounded type `D` structures.** -/
theorem typeABoxMap_add_of_lt (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F G : Matrix X X' A) :
    typeABoxMap N N' Mm (F + G) = typeABoxMap N N' Mm F + typeABoxMap N N' Mm G :=
  (bound_of_lt Mm h hh h' hh').typeABoxMap_add F G

/-- **A homomorphism of bounded type `D` structures induces a chain map of box tensor products.**
If `∂F = 0`, then `∂' ∘ T_F = T_F ∘ ∂`. -/
theorem typeABoxDifferential_typeABoxMap_of_morphismDifferential_eq_zero_of_lt [CharP R 2]
    (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M)
    (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F : Matrix X X' A}
    (hF : morphismDifferential N N' F = 0) (φ : X → M) :
    N'.typeABoxDifferential Mm (typeABoxMap N N' Mm F φ) =
      typeABoxMap N N' Mm F (N.typeABoxDifferential Mm φ) :=
  (add_eq_zero_iff_eq_of_charTwo R).mp <| by
    rw [typeABoxDifferential_typeABoxMap_of_lt N N' Mm h hh h' hh', hF, typeABoxMap_zero,
      LinearMap.zero_apply]

/-- **Homotopic homomorphisms of bounded type `D` structures induce homotopic chain maps of box
tensor products.** If `∂H = F + G`, then `T_F + T_G = ∂' ∘ T_H + T_H ∘ ∂`. -/
theorem typeABoxMap_add_typeABoxMap_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F G H : Matrix X X' A}
    (hH : morphismDifferential N N' H = F + G) (φ : X → M) :
    typeABoxMap N N' Mm F φ + typeABoxMap N N' Mm G φ =
      N'.typeABoxDifferential Mm (typeABoxMap N N' Mm H φ) +
        typeABoxMap N N' Mm H (N.typeABoxDifferential Mm φ) := by
  rw [typeABoxDifferential_typeABoxMap_of_lt N N' Mm h hh h' hh', hH,
    typeABoxMap_add_of_lt N N' Mm h hh h' hh', LinearMap.add_apply]

/-- **The induced map of a differential module.** For a differential right module, viewed as an
`A∞` module, the map induced by `F` is `φ ↦ φ ⬝ F`, the action `TauCeti.continuationMap` of `F` on
the box tensor products of `TauCeti.TypeDStructure.boxDifferential`. -/
theorem typeABoxMap_toUngradedAInfinityRightModule [CharP R 2] [Module Aᵐᵒᵖ M]
    [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (F : Matrix X X' A) :
    typeABoxMap N N' hM.toUngradedAInfinityRightModule F = continuationMap R M F := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  have hB : Bound N N' hM.toUngradedAInfinityRightModule Set.univ 2 :=
    bound_of_act_eq_zero fun n hn => by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact hM.toUngradedAInfinityRightModule_act_add_two n
  rw [hB.typeABoxMap_apply_eq_sum 0]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Finset.univ_eq_empty,
    Fin.sum_univ_one, Function.update_eq_const_of_subsingleton]
  rw [UngradedAInfinityRightModule.matrixAct_apply, ← (piFinTwoEquiv fun _ => X ⊕ X').symm.sum_comp,
    Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp [continuationMap_apply (R := R) (M := M) F,
    IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one]

end Morphism

end TypeDStructure

end TauCeti
