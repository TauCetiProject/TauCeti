/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Ungraded
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
row vectors `X → M`; it preserves the submodule `M ⊗ N` over the idempotents when `M` is strictly
unital (see below).

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
module `T_F` is the action `φ ↦ φ ⬝ F` of `TauCeti.LowDimTopology.Bordered.TypeD`.

**Composites.** For homomorphisms `F` from `N` to `N'` and `G` from `N'` to `N''`, the map of the
composite morphism `F * G` agrees with `T_G ∘ T_F` up to homotopy:
`T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂`, with `K = TauCeti.TypeDStructure.typeABoxCompHomotopy` the
sum of `m_{i+j+k+3}(φ, δ…, F, δ'…, G, δ''…)` along the paths that step through `F` and then
through `G`. This is the chain map identity for the morphism `fromCols F 0` from `N` into the
mapping cone `TauCeti.TypeDStructure.cone` of `G`, read on its `N''`-components: the
differential of `fromCols F 0` is `fromCols 0 (F * G)`, the `N'`-components of its induced map are
`T_F`, and the `N''`-components of the differential of the cone see these through `T_G`.

**Strictly unital modules.** The type `A` modules of bordered Floer theory are strictly unital
(`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital`): their operations `m_{k+1}`, `k ≥ 2`,
vanish when an input is an idempotent `ι s`. The box tensor product over the idempotents is then
the submodule `M ⊗ N` of row vectors with `m₂(φ x, ι (idem x)) = φ x`
(`TauCeti.TypeDStructure.typeABoxTensor`), the analogue of `TauCeti.TypeDStructure.boxTensor` for
differential modules. When the idempotents are cycles, the box tensor differential, the maps
induced by morphisms and the homotopies between composites preserve it, by the corresponding
property of the twisted differentials of the matrix module
(`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_matrix_twistedDifferential_apply`).
The identity morphism induces `φ ↦ (z ↦ m₂(φ z, ι (idem z)))`, since every longer path through
the identity block puts an idempotent into a higher operation, so it induces the identity of
`M ⊗ N`. Together with the composite homotopy this gives **homotopy invariance**: if `F` and `G`
are homomorphisms with `∂H = F * G + id`, then `T_G ∘ T_F + id = ∂ L + L ∂` on `M ⊗ N` with
`L = K + T_H`, so homotopy equivalent type `D` structures have homotopy equivalent box tensor
products.

**Morphisms of `A∞` modules.** A morphism `f` of `A∞` modules from `M` to `M'`
(`TauCeti.UngradedAInfinityRightModuleHom`) induces the map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` on box tensor products
(`TauCeti.TypeDStructure.typeABoxMapOfHom`). It is the off-diagonal component of the box tensor
differential of the mapping cone of `f` (`TauCeti.UngradedAInfinityRightModuleHom.cone`), which is
block triangular with diagonal blocks the box tensor differentials of `M` and `M'`; since that
differential squares to zero, `∂' ∘ T_f = T_f ∘ ∂` under either boundedness hypothesis. For a
bounded type `D` structure, the identity morphism induces the identity. For any type `D` structure,
an `A`-linear chain map `g` of differential modules induces `φ ↦ g ∘ φ`.

## Main definitions

* `TauCeti.TypeDStructure.typeABoxDifferential`: the box tensor differential of an `A∞` module
  with a type `D` structure, on row vectors.
* `TauCeti.TypeDStructure.typeABoxMap`: the map of box tensor products induced by a morphism of
  type `D` structures.
* `TauCeti.TypeDStructure.typeABoxCompHomotopy`: the homotopy between the composite of two induced
  maps and the map induced by the composite morphism.
* `TauCeti.TypeDStructure.typeABoxTensor`: the box tensor product `M ⊗ N` over the idempotents.
* `TauCeti.TypeDStructure.typeABoxTensorDifferential`: the box tensor differential restricted to
  `M ⊗ N`.
* `TauCeti.TypeDStructure.typeABoxMapOfHom`: the map of box tensor products induced by a morphism
  of `A∞` modules.

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
* `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt`: composites of
  homomorphisms induce composites of the induced chain maps up to homotopy,
  `T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂`, when the module, respectively the type `D` structures,
  are bounded.
* `TauCeti.TypeDStructure.typeABoxDifferential_mem_typeABoxTensor`,
  `TauCeti.TypeDStructure.typeABoxMap_mem_typeABoxTensor` and
  `TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_typeABoxTensor`: for a strictly unital module,
  the differential preserves `M ⊗ N`, and the induced maps and the composite homotopies take
  values in it.
* `TauCeti.TypeDStructure.typeABoxMap_idMorphism_of_act_eq_zero`,
  `TauCeti.TypeDStructure.typeABoxMap_idMorphism_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxMap_idMorphism_of_lt`: the identity morphism induces the
  identity of `M ⊗ N`.
* `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_of_lt`: homotopy invariance of `M ⊗ N` in
  the type `D` structure.
* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMapOfHom_of_isBounded`,
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMapOfHom_of_lt` and
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMapOfHom_of_act_eq_zero`: morphisms of `A∞`
  modules induce chain maps, `∂' ∘ T_f = T_f ∘ ∂`, when the type `D` structure, respectively the
  modules and the morphism, are bounded.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_apply_eq_sum`: the induced map as a finite sum over
  paths of generators.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_id_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxMapOfHom_toUngradedAInfinityRightModuleHom`: for a bounded type
  `D` structure, the identity induces the identity; for any type `D` structure, a chain map `g` of
  differential modules induces `φ ↦ g ∘ φ`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (strictly unital `A∞` modules, boundedness of `A∞` modules and type `D` structures,
  and the box tensor product, equation (2.29), with its functoriality in morphisms of type `D`
  structures and its invariance under homotopy equivalence).
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

/-! ### Composites of induced maps -/

section Composition

variable {X'' : Type*} [Fintype X''] [DecidableEq X'']

/-- The **homotopy between a composite of induced maps and the map of the composite**. For
matrices `F` from `N` to `N'` and `G` from `N'` to `N''`, it sends a row vector `φ` on `X` to the
sum of `m_{i+j+k+3}(φ, δ, …, δ, F, δ', …, δ', G, δ'', …, δ'')` along the paths of generators that
step through an entry of `F` once and then through an entry of `G` once. It is the `X''`-component
of the box tensor differential of the block upper-triangular matrix on `X ⊕ (X' ⊕ X'')` with
diagonal blocks `δ`, `δ'`, `δ''` and off-diagonal blocks `F` and `G`, restricted to row vectors
supported on `X`; when `G` is a homomorphism, it is the `X''`-component of the map induced by `F`
into the mapping cone of `G`
(`TauCeti.TypeDStructure.typeABoxCompHomotopy_apply_eq_typeABoxMap`). As for
`TauCeti.TypeDStructure.typeABoxMap`, the sum is finite when `M`, or `N`, `N'` and `N''`, are
bounded, and the construction is `0` by convention otherwise. -/
noncomputable def typeABoxCompHomotopy (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (N'' : TypeDStructure d ι X'') (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A)
    (G : Matrix X' X'' A) : (X → M) →ₗ[R] X'' → M :=
  LinearMap.funLeft R M (Sum.inr ∘ Sum.inr) ∘ₗ
    (Mm.matrix (X ⊕ (X' ⊕ X''))).twistedDifferential
      (Matrix.fromBlocks N.coeff (Matrix.fromCols F 0) 0
        (Matrix.fromBlocks N'.coeff G 0 N''.coeff)) ∘ₗ
    (LinearEquiv.sumArrowLequivProdArrow X (X' ⊕ X'') R M).symm.toLinearMap ∘ₗ
    LinearMap.inl R (X → M) (X' ⊕ X'' → M)

theorem typeABoxCompHomotopy_apply (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X')
    (N'' : TypeDStructure d ι X'') (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A)
    (G : Matrix X' X'' A) (φ : X → M) (z : X'') :
    typeABoxCompHomotopy N N' N'' Mm F G φ z =
      (Mm.matrix (X ⊕ (X' ⊕ X''))).twistedDifferential
        (Matrix.fromBlocks N.coeff (Matrix.fromCols F 0) 0
          (Matrix.fromBlocks N'.coeff G 0 N''.coeff)) (Sum.elim φ 0) (Sum.inr (Sum.inr z)) := by
  have h : (LinearEquiv.sumArrowLequivProdArrow X (X' ⊕ X'') R M).symm (φ, 0) = Sum.elim φ 0 := by
    funext a
    cases a <;> simp
  simp [typeABoxCompHomotopy, LinearMap.funLeft_apply, h]

/-- When `G` is a homomorphism, the homotopy `typeABoxCompHomotopy N N' N'' Mm F G` is the
`X''`-component of the map induced by the morphism `fromCols F 0` from `N` into the mapping cone of
`G`. -/
theorem typeABoxCompHomotopy_apply_eq_typeABoxMap (N : TypeDStructure d ι X)
    {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''}
    (Mm : UngradedAInfinityRightModule d M) (F : Matrix X X' A) {G : Matrix X' X'' A}
    (hG : G ∈ morphisms N' N'') (hG' : morphismDifferential N' N'' G = 0) (φ : X → M) (z : X'') :
    typeABoxCompHomotopy N N' N'' Mm F G φ z =
      typeABoxMap N (cone N' N'' G hG hG') Mm (Matrix.fromCols F 0) φ (Sum.inr z) := by
  rw [typeABoxCompHomotopy_apply, typeABoxMap_apply, cone_coeff]

section Core

variable {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''}
  {Mm : UngradedAInfinityRightModule d M} {G : Matrix X' X'' A} {hG : G ∈ morphisms N' N''}
  {hG' : morphismDifferential N' N'' G = 0} {K : ℕ}

private theorem Bound.mono {U : Set (Matrix (X ⊕ X') (X ⊕ X') A)} {K' : ℕ}
    (hB : Bound N N' Mm U K) (hK : K ≤ K') : Bound N N' Mm U K' :=
  { hB with act_eq_zero := fun n hn => hB.act_eq_zero n (hK.trans hn) }

/-- The `N'`-components of the map induced by `fromCols F H` into the mapping cone of `G` are the
map induced by `F`: a path ending in `X'` never visits `X''`. -/
private theorem typeABoxMap_cone_fromCols_apply_inl
    {U : Set (Matrix (X ⊕ (X' ⊕ X'')) (X ⊕ (X' ⊕ X'')) A)}
    {U₁ : Set (Matrix (X ⊕ X') (X ⊕ X') A)} (hB : Bound N (cone N' N'' G hG hG') Mm U K)
    (hB₁ : Bound N N' Mm U₁ K) (F : Matrix X X' A) (H : Matrix X X'' A) (φ : X → M) (y : X') :
    typeABoxMap N (cone N' N'' G hG hG') Mm (Matrix.fromCols F H) φ (Sum.inl y) =
      typeABoxMap N N' Mm F φ y := by
  rw [typeABoxMap_apply, typeABoxMap_apply,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _
      (hB.act_fromBlocks (Matrix.fromCols F H)),
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ (hB₁.act_fromBlocks F)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act]
  refine sum_congr rfl fun n _ => ?_
  have h := Mm.matrixAct_apply_of_injective (n := n) (e := Sum.map id Sum.inl)
    (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩)
    (fun _ => Matrix.fromBlocks N.coeff (Matrix.fromCols F H) 0 (cone N' N'' G hG hG').coeff)
    (fun _ => Matrix.fromBlocks N.coeff F 0 N'.coeff)
    (fun _ a b => by rcases a with a | a <;> rcases b with b | b <;> simp)
    (fun _ a b ha => by
      rcases a with a | a | a
      · exact absurd ⟨Sum.inl a, rfl⟩ ha
      · exact absurd ⟨Sum.inr a, rfl⟩ ha
      · rcases b with b | b <;> simp)
    (Sum.elim φ 0) (Sum.inr y)
  rw [Sum.elim_comp_map, Function.comp_id, Pi.zero_comp] at h
  exact h

/-- The `N''`-components of the map induced by `fromCols 0 H` into the mapping cone of `G` are the
map induced by `H`: a path starting in `X` never visits `X'`. -/
private theorem typeABoxMap_cone_fromCols_zero_apply_inr
    {U : Set (Matrix (X ⊕ (X' ⊕ X'')) (X ⊕ (X' ⊕ X'')) A)}
    {U₂ : Set (Matrix (X ⊕ X'') (X ⊕ X'') A)} (hB : Bound N (cone N' N'' G hG hG') Mm U K)
    (hB₂ : Bound N N'' Mm U₂ K) (H : Matrix X X'' A) (φ : X → M) (z : X'') :
    typeABoxMap N (cone N' N'' G hG hG') Mm (Matrix.fromCols 0 H) φ (Sum.inr z) =
      typeABoxMap N N'' Mm H φ z := by
  rw [typeABoxMap_apply, typeABoxMap_apply,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _
      (hB.act_fromBlocks (Matrix.fromCols 0 H)),
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _ (hB₂.act_fromBlocks H)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act]
  refine sum_congr rfl fun n _ => ?_
  have h := Mm.matrixAct_apply_of_injective_of_forall_notMem_range (n := n)
    (e := Sum.map id Sum.inr) (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩)
    (fun _ => Matrix.fromBlocks N.coeff (Matrix.fromCols 0 H) 0 (cone N' N'' G hG hG').coeff)
    (fun _ => Matrix.fromBlocks N.coeff H 0 N''.coeff)
    (fun _ a b => by rcases a with a | a <;> rcases b with b | b <;> simp)
    (fun _ a b hb => by
      rcases b with b | b | b
      · exact absurd ⟨Sum.inl b, rfl⟩ hb
      · rcases a with a | a <;> simp
      · exact absurd ⟨Sum.inr b, rfl⟩ hb)
    (φ := Sum.elim φ 0) (fun a ha => by
      rcases a with a | a | a
      · exact absurd ⟨Sum.inl a, rfl⟩ ha
      · rfl
      · exact absurd ⟨Sum.inr a, rfl⟩ ha) (Sum.inr z)
  rw [Sum.elim_comp_map, Function.comp_id, Pi.zero_comp] at h
  exact h

/-- The core of `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero`
and `TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt`: the
`X''`-components of the chain map identity for the map induced by `fromCols F 0` into the mapping
cone of `G`. -/
private theorem typeABoxMap_typeABoxMap_add_typeABoxMap_mul [CharP R 2]
    {U : Set (Matrix (X ⊕ (X' ⊕ X'')) (X ⊕ (X' ⊕ X'')) A)}
    {U₁ : Set (Matrix (X ⊕ X') (X ⊕ X') A)} {U₂ : Set (Matrix (X ⊕ X'') (X ⊕ X'') A)}
    {U₃ : Set (Matrix (X' ⊕ X'') (X' ⊕ X'') A)} (hB : Bound N (cone N' N'' G hG hG') Mm U K)
    (hB₁ : Bound N N' Mm U₁ K) (hB₂ : Bound N N'' Mm U₂ K) (hB₃ : Bound N' N'' Mm U₃ K)
    {F : Matrix X X' A} (hF : morphismDifferential N N' F = 0) (φ : X → M) :
    typeABoxMap N' N'' Mm G (typeABoxMap N N' Mm F φ) + typeABoxMap N N'' Mm (F * G) φ =
      N''.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N'' Mm F G φ) +
        typeABoxCompHomotopy N N' N'' Mm F G (N.typeABoxDifferential Mm φ) := by
  funext z
  set T := typeABoxMap N (cone N' N'' G hG hG') Mm (Matrix.fromCols F 0)
  -- The chain map identity for `T`, whose source is a cycle up to the composite `F * G`.
  have key := congrFun (hB.typeABoxDifferential_typeABoxMap (Matrix.fromCols F 0) φ) (Sum.inr z)
  rw [morphismDifferential_cone_fromCols, hF, map_zero, add_zero,
    typeABoxMap_cone_fromCols_zero_apply_inr hB hB₂] at key
  -- On the mapping cone, the `N''`-components of the differential see the `N'`-components of `T φ`
  -- through `G`, and these are the map induced by `F`.
  have hT : T φ = Sum.elim (typeABoxMap N N' Mm F φ) (typeABoxCompHomotopy N N' N'' Mm F G φ) := by
    funext w
    rcases w with y | y
    · exact typeABoxMap_cone_fromCols_apply_inl hB hB₁ F 0 φ y
    · exact (typeABoxCompHomotopy_apply_eq_typeABoxMap N Mm F hG hG' φ y).symm
  rw [Pi.add_apply, hT, typeABoxDifferential_def, cone_coeff, hB₃.twistedDifferential_apply_inr,
    ← typeABoxCompHomotopy_apply_eq_typeABoxMap N Mm F hG hG'] at key
  rw [Pi.add_apply, Pi.add_apply, ← key]
  calc _ = (typeABoxMap N' N'' Mm G (typeABoxMap N N' Mm F φ) z +
        typeABoxMap N' N'' Mm G (typeABoxMap N N' Mm F φ) z) +
        (N''.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N'' Mm F G φ) z +
          typeABoxCompHomotopy N N' N'' Mm F G (N.typeABoxDifferential Mm φ) z) := by abel
    _ = _ := by rw [add_self_eq_zero_of_charTwo R, zero_add]

end Core

/-- **Composites of homomorphisms induce composites of chain maps up to homotopy, for a bounded
module.** Over a ring of characteristic two, let the operations `m_{k+1}` of `M` vanish for
`k ≥ K`, and let `F` from `N` to `N'` and `G` from `N'` to `N''` be homomorphisms of type `D`
structures. Then the map `T_{F G}` of box tensor products induced by the composite morphism
`F * G` and the composite `T_G ∘ T_F` of the induced maps are chain homotopic, with homotopy
`TauCeti.TypeDStructure.typeABoxCompHomotopy`:
`T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂`. -/
theorem typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X') (N'' : TypeDStructure d ι X'')
    (Mm : UngradedAInfinityRightModule d M) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    {F : Matrix X X' A} {G : Matrix X' X'' A} (hF : morphismDifferential N N' F = 0)
    (hG : G ∈ morphisms N' N'') (hG' : morphismDifferential N' N'' G = 0) (φ : X → M) :
    typeABoxMap N' N'' Mm G (typeABoxMap N N' Mm F φ) + typeABoxMap N N'' Mm (F * G) φ =
      N''.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N'' Mm F G φ) +
        typeABoxCompHomotopy N N' N'' Mm F G (N.typeABoxDifferential Mm φ) :=
  typeABoxMap_typeABoxMap_add_typeABoxMap_mul (hG := hG) (hG' := hG')
    (bound_of_act_eq_zero hK) (bound_of_act_eq_zero hK) (bound_of_act_eq_zero hK)
    (bound_of_act_eq_zero hK) hF φ

/-- **Composites of homomorphisms of bounded type `D` structures induce composites of chain maps
up to homotopy.** Over a ring of characteristic two, let heights on the generators of `N`, `N'` and
`N''` strictly increase along their nonzero coefficients, and let `F` from `N` to `N'` and `G` from
`N'` to `N''` be homomorphisms of type `D` structures. Then, whatever the operations of `M`,
`T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂` with the homotopy
`K = TauCeti.TypeDStructure.typeABoxCompHomotopy`. -/
theorem typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (N' : TypeDStructure d ι X') (N'' : TypeDStructure d ι X'')
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (h'' : X'' → ℕ)
    (hh'' : ∀ x y, N''.coeff x y ≠ 0 → h'' x < h'' y) {F : Matrix X X' A} {G : Matrix X' X'' A}
    (hF : morphismDifferential N N' F = 0) (hG : G ∈ morphisms N' N'')
    (hG' : morphismDifferential N' N'' G = 0) (φ : X → M) :
    typeABoxMap N' N'' Mm G (typeABoxMap N N' Mm F φ) + typeABoxMap N N'' Mm (F * G) φ =
      N''.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N'' Mm F G φ) +
        typeABoxCompHomotopy N N' N'' Mm F G (N.typeABoxDifferential Mm φ) := by
  -- The mapping cone of `G` is bounded by the height of `X''` shifted above that of `X'`.
  have hB₃ := bound_of_lt Mm h' hh' h'' hh''
  have hB := bound_of_lt (N' := cone N' N'' G hG hG') Mm h hh (sumHeight h' h'')
    (fun a b hab => hB₃.fromBlocks_mem G a b (by rwa [cone_coeff] at hab))
  have hB₁ := bound_of_lt (N' := N') Mm h hh h' hh'
  have hB₂ := bound_of_lt (N' := N'') Mm h hh h'' hh''
  -- Bring the four bounds to a common arity.
  set K := (univ.sup h + univ.sup (sumHeight h' h'') + 2) + (univ.sup h + univ.sup h' + 2) +
    (univ.sup h + univ.sup h'' + 2) + (univ.sup h' + univ.sup h'' + 2)
  exact typeABoxMap_typeABoxMap_add_typeABoxMap_mul (hB.mono (K' := K) (by omega))
    (hB₁.mono (K' := K) (by omega)) (hB₂.mono (K' := K) (by omega))
    (hB₃.mono (K' := K) (by omega)) hF φ

end Composition

/-! ### Strictly unital modules -/

section StrictUnit

variable {X' X'' : Type*} [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']

omit [DecidableEq X] in
variable (N : TypeDStructure d ι X) (Mm : UngradedAInfinityRightModule d M) in
/-- The **box tensor product** `M ⊠ N = M ⊗ N` over the idempotents of a type `A` module `M` with
a type `D` structure `N`, as the submodule of row vectors `φ : X → M`, standing for
`∑ x, φ x ⊗ x`, with `m₂(φ x, ι (idem x)) = φ x`. For a strictly unital module this is preserved
by the box tensor differential (`TauCeti.TypeDStructure.typeABoxDifferential_mem_typeABoxTensor`)
and by the maps induced by morphisms
(`TauCeti.TypeDStructure.typeABoxMap_mem_typeABoxTensor`); for a differential module it is
`TauCeti.TypeDStructure.boxTensor`
(`TauCeti.TypeDStructure.typeABoxTensor_toUngradedAInfinityRightModule`). -/
def typeABoxTensor : Submodule R (X → M) where
  carrier := {φ | ∀ x, Mm.act 1 (fun _ => ι (N.idem x)) (φ x) = φ x}
  add_mem' {φ ψ} hφ hψ x := by simp [hφ x, hψ x]
  zero_mem' := by simp
  smul_mem' r φ hφ x := by simp [hφ x]

omit [DecidableEq X] in
@[simp]
theorem mem_typeABoxTensor_iff {N : TypeDStructure d ι X} {Mm : UngradedAInfinityRightModule d M}
    {φ : X → M} : φ ∈ N.typeABoxTensor Mm ↔ ∀ x, Mm.act 1 (fun _ => ι (N.idem x)) (φ x) = φ x :=
  Iff.rfl

omit [DecidableEq X] in
/-- For a differential module, viewed as an `A∞` module, the box tensor product over the
idempotents is `TauCeti.TypeDStructure.boxTensor`. -/
theorem typeABoxTensor_toUngradedAInfinityRightModule [CharP R 2] [Module Aᵐᵒᵖ M]
    [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (N : TypeDStructure d ι X) :
    N.typeABoxTensor hM.toUngradedAInfinityRightModule = N.boxTensor M := by
  ext φ
  simp

variable {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''}
  {Mm : UngradedAInfinityRightModule d M}

/-- `M ⊗ N` is the submodule of row vectors fixed by the operation `m₂(·, I)` of the matrix
module along the identity morphism `I`. -/
theorem mem_typeABoxTensor_iff_matrixAct {φ : X → M} :
    φ ∈ N.typeABoxTensor Mm ↔ Mm.matrixAct X 1 (fun _ => N.idMorphism) φ = φ := by
  simp only [mem_typeABoxTensor_iff, funext_iff, idMorphism_def,
    UngradedAInfinityRightModule.matrixAct_one_diagonal_apply]

/-- **The box tensor differential preserves `M ⊗ N`** when `M` is strictly unital and the
idempotents are cycles, over a ring of characteristic two. -/
theorem typeABoxDifferential_mem_typeABoxTensor [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hι : ∀ s, d (ι s) = 0) {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) :
    N.typeABoxDifferential Mm φ ∈ N.typeABoxTensor Mm := fun z => by
  rw [typeABoxDifferential_def]
  exact hMm.act_one_matrix_twistedDifferential_apply X (hι _) (fun y => N.coeff_mul_idem y z)
    (hφ z)

variable (N) in
/-- The box tensor differential restricted to `M ⊗ N`, for a strictly unital module `M` whose
idempotents are cycles, over a ring of characteristic two. -/
noncomputable def typeABoxTensorDifferential [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hι : ∀ s, d (ι s) = 0) : N.typeABoxTensor Mm →ₗ[R] N.typeABoxTensor Mm :=
  (N.typeABoxDifferential Mm).restrict fun _ hφ =>
    typeABoxDifferential_mem_typeABoxTensor hMm hι hφ

@[simp]
theorem coe_typeABoxTensorDifferential_apply [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hι : ∀ s, d (ι s) = 0) (φ : N.typeABoxTensor Mm) :
    (N.typeABoxTensorDifferential hMm hι φ : X → M) = N.typeABoxDifferential Mm φ :=
  (rfl)

/-- The box tensor differential of a bounded module squares to zero on `M ⊗ N`. -/
theorem typeABoxTensorDifferential_typeABoxTensorDifferential_of_act_eq_zero [CharP R 2]
    (hMm : Mm.IsStrictlyUnital ι) (hι : ∀ s, d (ι s) = 0) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : N.typeABoxTensor Mm) :
    N.typeABoxTensorDifferential hMm hι (N.typeABoxTensorDifferential hMm hι φ) = 0 :=
  Subtype.ext (N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero Mm hK φ)

/-- The box tensor differential with a bounded type `D` structure squares to zero on `M ⊗ N`. -/
theorem typeABoxTensorDifferential_typeABoxTensorDifferential_of_isBounded [CharP R 2]
    (hMm : Mm.IsStrictlyUnital ι) (hι : ∀ s, d (ι s) = 0) (hN : N.IsBounded)
    (φ : N.typeABoxTensor Mm) :
    N.typeABoxTensorDifferential hMm hι (N.typeABoxTensorDifferential hMm hι φ) = 0 :=
  Subtype.ext (N.typeABoxDifferential_typeABoxDifferential_of_isBounded Mm hN φ)

/-- **A morphism induces a map into the box tensor product over the idempotents** when `M` is
strictly unital and the idempotents are cycles, over a ring of characteristic two: `T_F` takes
values in `M ⊗ N'`, since the idempotent of `z` is a right unit for the column `z` of
`fromBlocks δ F 0 δ'`. -/
theorem typeABoxMap_mem_typeABoxTensor [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hι : ∀ s, d (ι s) = 0) {F : Matrix X X' A} (hF : F ∈ morphisms N N') (φ : X → M) :
    typeABoxMap N N' Mm F φ ∈ N'.typeABoxTensor Mm := fun z => by
  rw [typeABoxMap_apply]
  refine hMm.act_one_matrix_twistedDifferential_apply (X ⊕ X') (hι _) ?_ (map_zero _)
  rintro (x | x)
  exacts [(mem_morphisms_iff.mp hF x z).2, N'.coeff_mul_idem x z]

/-- **The homotopy between composites takes values in the box tensor product over the
idempotents** when `M` is strictly unital and the idempotents are cycles, over a ring of
characteristic two: for a matrix `F` and a morphism `G` from `N'` to `N''`,
`TauCeti.TypeDStructure.typeABoxCompHomotopy` takes values in `M ⊗ N''`, since the idempotent of
`z` is a right unit for the column `z` of its block upper-triangular matrix. -/
theorem typeABoxCompHomotopy_mem_typeABoxTensor [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hι : ∀ s, d (ι s) = 0) (F : Matrix X X' A) {G : Matrix X' X'' A}
    (hG : G ∈ morphisms N' N'') (φ : X → M) :
    typeABoxCompHomotopy N N' N'' Mm F G φ ∈ N''.typeABoxTensor Mm := fun z => by
  rw [typeABoxCompHomotopy_apply]
  refine hMm.act_one_matrix_twistedDifferential_apply (X ⊕ (X' ⊕ X'')) (hι _) ?_ (map_zero _)
  rintro (_ | x | x)
  exacts [zero_mul _, (mem_morphisms_iff.mp hG x z).2, N''.coeff_mul_idem x z]

/-- The operations of arity at least three of the matrix module of `X ⊕ X` vanish when one input
is the off-diagonal block `fromBlocks 0 I 0 0`, for a strictly unital module: along every path its
entry is zero or an idempotent. -/
private theorem matrixAct_update_fromBlocks_zero_idMorphism (hMm : Mm.IsStrictlyUnital ι)
    {n : ℕ} (hn : 2 ≤ n) (l : Fin n) :
    Mm.matrixAct (X ⊕ X) n (Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N.coeff) l
      (Matrix.fromBlocks 0 N.idMorphism 0 0)) = 0 := by
  refine LinearMap.ext fun ψ => funext fun z => ?_
  rw [UngradedAInfinityRightModule.matrixAct_apply, LinearMap.zero_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs
  · rcases ha : x l.castSucc with a | a <;> rcases hb : x l.succ with b | b
    · rw [(Mm.act n).map_coord_zero l (by simp [ha, hb]), LinearMap.zero_apply]
    · by_cases hab : a = b
      · subst hab
        rw [hMm.act_eq_zero hn (i := l) (s := N.idem a) (by simp [ha, hb]),
          LinearMap.zero_apply]
      · rw [(Mm.act n).map_coord_zero l (by simp [ha, hb, hab]), LinearMap.zero_apply]
    · rw [(Mm.act n).map_coord_zero l (by simp [ha, hb]), LinearMap.zero_apply]
    · rw [(Mm.act n).map_coord_zero l (by simp [ha, hb]), LinearMap.zero_apply]
  · rfl

/-- The operations of arity at least three of the matrix module of `X ⊕ X` along
`fromBlocks δ I 0 δ` vanish when those of the matrix module of `X` along `δ` do, for a strictly
unital module: the paths that stay on one side are paths along `δ`, and the others step through
the identity morphism. -/
private theorem matrixAct_fromBlocks_idMorphism_eq_zero (hMm : Mm.IsStrictlyUnital ι) {n : ℕ}
    (hn : 2 ≤ n) (hδ : (Mm.matrixAct X n fun _ => N.coeff) = 0) :
    (Mm.matrixAct (X ⊕ X) n fun _ => Matrix.fromBlocks N.coeff N.idMorphism 0 N.coeff) = 0 := by
  refine LinearMap.ext fun ψ => funext fun w => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, ψ = Sum.elim a b :=
    ⟨ψ ∘ Sum.inl, ψ ∘ Sum.inr, (Sum.elim_comp_inl_inr ψ).symm⟩
  rcases w with z | z
  · rw [Mm.matrixAct_apply_inl _ (fun _ _ _ => by simp)]
    simp only [Matrix.toBlocks_fromBlocks₁₁, hδ, LinearMap.zero_apply, Pi.zero_apply]
  · have hab : Sum.elim a b = Sum.elim a (0 : X → M) + Sum.elim (0 : X → M) b := by
      funext w
      cases w <;> simp
    rw [hab, map_add, Pi.add_apply, Mm.matrixAct_sumElim_zero_apply_inr _ (fun _ _ _ => by simp),
      ← Mm.sum_matrixAct_update_fromBlocks_apply_inr N.coeff N.coeff 0 N.idMorphism]
    simp only [Matrix.toBlocks_fromBlocks₂₂, hδ, matrixAct_update_fromBlocks_zero_idMorphism hMm hn,
      LinearMap.zero_apply, Pi.zero_apply, Finset.sum_const_zero, add_zero]

/-- **The identity morphism induces the action of the idempotents**, for a strictly unital module
whose matrix module operations along `δ` vanish from some arity on: `T_{id} φ` has `z`-component
`m₂(φ z, ι (idem z))`. Every path of length at least two steps through an idempotent or a zero
entry of the identity morphism, and the paths of length one are the single steps `z → z`. -/
theorem typeABoxMap_idMorphism_apply (hMm : Mm.IsStrictlyUnital ι) {K : ℕ}
    (hK : ∀ n, K ≤ n → (Mm.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    typeABoxMap N N Mm N.idMorphism φ z = Mm.act 1 (fun _ => ι (N.idem z)) (φ z) := by
  have hupd : Function.update (fun _ : Fin 1 => Matrix.fromBlocks N.coeff 0 0 N.coeff) 0
      (Matrix.fromBlocks 0 N.idMorphism 0 0) = fun _ => Matrix.fromBlocks 0 N.idMorphism 0 0 :=
    funext fun l => by rw [Fin.fin_one_eq_zero l, Function.update_self]
  rw [typeABoxMap_apply, UngradedAInfinityRightModule.twistedDifferential_eq_sum (K := K + 2) _
    fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act]
      exact matrixAct_fromBlocks_idMorphism_eq_zero hMm (by omega) (hK n (by omega))]
  simp only [LinearMap.sum_apply, Finset.sum_apply, UngradedAInfinityRightModule.matrix_act,
    ← Mm.sum_matrixAct_update_fromBlocks_apply_inr N.coeff N.coeff 0 N.idMorphism]
  rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ K + 2 by omega),
    Finset.sum_eq_zero (s := Finset.Ico 2 (K + 2)) fun n hn => Finset.sum_eq_zero fun l _ => by
      rw [matrixAct_update_fromBlocks_zero_idMorphism hMm (Finset.mem_Ico.mp hn).1,
        LinearMap.zero_apply, Pi.zero_apply], add_zero]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Finset.univ_eq_empty,
    zero_add, Fin.sum_univ_one, hupd, UngradedAInfinityRightModule.matrixAct_one_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero]
  rw [← UngradedAInfinityRightModule.matrixAct_one_apply, idMorphism_def,
    UngradedAInfinityRightModule.matrixAct_one_diagonal_apply]

/-- **The identity morphism induces the action of the idempotents**, for a strictly unital
bounded module: `T_{id} φ` has `z`-component `m₂(φ z, ι (idem z))`. -/
theorem typeABoxMap_idMorphism_apply_of_act_eq_zero (hMm : Mm.IsStrictlyUnital ι) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : X → M) (z : X) :
    typeABoxMap N N Mm N.idMorphism φ z = Mm.act 1 (fun _ => ι (N.idem z)) (φ z) :=
  typeABoxMap_idMorphism_apply hMm (fun n hn => by
    rw [Mm.matrixAct_eq_zero_of_act_eq_zero _ (hK n hn), zero_apply]) φ z

/-- **The identity morphism of a bounded type `D` structure induces the action of the
idempotents**, for a strictly unital module: `T_{id} φ` has `z`-component
`m₂(φ z, ι (idem z))`. -/
theorem typeABoxMap_idMorphism_apply_of_isBounded (hMm : Mm.IsStrictlyUnital ι)
    (hN : N.IsBounded) (φ : X → M) (z : X) :
    typeABoxMap N N Mm N.idMorphism φ z = Mm.act 1 (fun _ => ι (N.idem z)) (φ z) := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  exact typeABoxMap_idMorphism_apply hMm (K := K) (fun n hn =>
    N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero Mm (hK n hn) fun _ => Or.inl rfl) φ z

/-- **The identity morphism of a type `D` structure with heights induces the action of the
idempotents**, for a strictly unital module: `T_{id} φ` has `z`-component
`m₂(φ z, ι (idem z))`. -/
theorem typeABoxMap_idMorphism_apply_of_lt (hMm : Mm.IsStrictlyUnital ι) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) (z : X) :
    typeABoxMap N N Mm N.idMorphism φ z = Mm.act 1 (fun _ => ι (N.idem z)) (φ z) :=
  typeABoxMap_idMorphism_apply_of_isBounded hMm (N.isBounded_of_lt h hh) φ z

/-- **The identity morphism induces the identity of `M ⊗ N`**, for a strictly unital module whose
matrix module operations along `δ` vanish from some arity on. -/
theorem typeABoxMap_idMorphism (hMm : Mm.IsStrictlyUnital ι) {K : ℕ}
    (hK : ∀ n, K ≤ n → (Mm.matrixAct X n fun _ => N.coeff) = 0) {φ : X → M}
    (hφ : φ ∈ N.typeABoxTensor Mm) : typeABoxMap N N Mm N.idMorphism φ = φ :=
  funext fun z => (typeABoxMap_idMorphism_apply hMm hK φ z).trans (hφ z)

/-- **The identity morphism induces the identity of `M ⊗ N`**, for a strictly unital bounded
module. -/
theorem typeABoxMap_idMorphism_of_act_eq_zero (hMm : Mm.IsStrictlyUnital ι) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) :
    typeABoxMap N N Mm N.idMorphism φ = φ :=
  funext fun z => (typeABoxMap_idMorphism_apply_of_act_eq_zero hMm hK φ z).trans (hφ z)

/-- **The identity morphism of a bounded type `D` structure induces the identity of `M ⊗ N`**, for
a strictly unital module. -/
theorem typeABoxMap_idMorphism_of_isBounded (hMm : Mm.IsStrictlyUnital ι) (hN : N.IsBounded)
    {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) : typeABoxMap N N Mm N.idMorphism φ = φ :=
  funext fun z => (typeABoxMap_idMorphism_apply_of_isBounded hMm hN φ z).trans (hφ z)

/-- **The identity morphism of a type `D` structure with heights induces the identity of
`M ⊗ N`**, for a strictly unital module. -/
theorem typeABoxMap_idMorphism_of_lt (hMm : Mm.IsStrictlyUnital ι) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) :
    typeABoxMap N N Mm N.idMorphism φ = φ :=
  typeABoxMap_idMorphism_of_isBounded hMm (N.isBounded_of_lt h hh) hφ

/-- **Homotopy invariance of the box tensor product with a bounded module.** Over a ring of
characteristic two, let `M` be strictly unital with operations `m_{k+1}` vanishing for `k ≥ K`.
Let `F` from `N` to `N'` and `G` from `N'` to `N` be homomorphisms of type `D` structures whose
composite `F * G` is homotopic to the identity, `∂H = F * G + id`. Then on `M ⊗ N`,
`T_G ∘ T_F + id = ∂ L + L ∂` with `L = K + T_H`, where `K` is
`TauCeti.TypeDStructure.typeABoxCompHomotopy`. When the idempotents are cycles and `H` is a
morphism, `L` takes values in `M ⊗ N`
(`TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_typeABoxTensor` and
`TauCeti.TypeDStructure.typeABoxMap_mem_typeABoxTensor`), so with the symmetric statement for
`G * F` a homotopy equivalence of type `D` structures induces a homotopy equivalence of box tensor
products over the idempotents. -/
theorem typeABoxMap_typeABoxMap_add_of_act_eq_zero [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0) {F : Matrix X X' A} {G : Matrix X' X A}
    {H : Matrix X X A} (hF : morphismDifferential N N' F = 0) (hG : G ∈ morphisms N' N)
    (hG' : morphismDifferential N' N G = 0)
    (hH : morphismDifferential N N H = F * G + N.idMorphism) {φ : X → M}
    (hφ : φ ∈ N.typeABoxTensor Mm) :
    typeABoxMap N' N Mm G (typeABoxMap N N' Mm F φ) + φ =
      N.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N Mm F G φ + typeABoxMap N N Mm H φ) +
        (typeABoxCompHomotopy N N' N Mm F G (N.typeABoxDifferential Mm φ) +
          typeABoxMap N N Mm H (N.typeABoxDifferential Mm φ)) := by
  have h₂ := typeABoxMap_add_typeABoxMap_of_act_eq_zero N N Mm hK hH φ
  rw [typeABoxMap_idMorphism_of_act_eq_zero hMm hK hφ] at h₂
  -- Add `T_G ∘ T_F + T_{F G} = ∂ K + K ∂` and `T_{F G} + id = ∂ T_H + T_H ∂`.
  exact add_eq_map_add_add_of_charTwo R _
    (typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero N N' N Mm hK hF hG hG' φ) h₂

/-- **Homotopy invariance of the box tensor product of bounded type `D` structures.** Over a ring
of characteristic two, let `M` be strictly unital, and let heights on the generators of `N` and
`N'` strictly increase along their nonzero coefficients. Let `F` from `N` to `N'` and `G` from `N'`
to `N` be homomorphisms of type `D` structures with `∂H = F * G + id`. Then on `M ⊗ N`,
`T_G ∘ T_F + id = ∂ L + L ∂` with `L = K + T_H`, where `K` is
`TauCeti.TypeDStructure.typeABoxCompHomotopy`; see
`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_of_act_eq_zero`. -/
theorem typeABoxMap_typeABoxMap_add_of_lt [CharP R 2] (hMm : Mm.IsStrictlyUnital ι) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F : Matrix X X' A} {G : Matrix X' X A}
    {H : Matrix X X A} (hF : morphismDifferential N N' F = 0) (hG : G ∈ morphisms N' N)
    (hG' : morphismDifferential N' N G = 0)
    (hH : morphismDifferential N N H = F * G + N.idMorphism) {φ : X → M}
    (hφ : φ ∈ N.typeABoxTensor Mm) :
    typeABoxMap N' N Mm G (typeABoxMap N N' Mm F φ) + φ =
      N.typeABoxDifferential Mm (typeABoxCompHomotopy N N' N Mm F G φ + typeABoxMap N N Mm H φ) +
        (typeABoxCompHomotopy N N' N Mm F G (N.typeABoxDifferential Mm φ) +
          typeABoxMap N N Mm H (N.typeABoxDifferential Mm φ)) := by
  have h₂ := typeABoxMap_add_typeABoxMap_of_lt N N Mm h hh h hh hH φ
  rw [typeABoxMap_idMorphism_of_lt hMm h hh hφ] at h₂
  -- Add `T_G ∘ T_F + T_{F G} = ∂ K + K ∂` and `T_{F G} + id = ∂ T_H + T_H ∂`.
  exact add_eq_map_add_add_of_charTwo R _
    (typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt N N' N Mm h hh h' hh' h hh hF hG hG' φ) h₂

end StrictUnit

end Morphism

/-! ### Maps induced by morphisms of `A∞` modules -/

section ModuleHom

variable {M' : Type*} [AddCommGroup M'] [Module R M'] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'}

/-- The **map induced on box tensor products** by a morphism `f` of `A∞` modules from `M` to `M'`:
on row vectors, `φ ↦ ∑_k (f_{k+1} ⊗ 1) (φ ⊗ δ^k)`, the sum over the paths of generators
`x₀ → ⋯ → xₙ = z` of `f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`
(`TauCeti.TypeDStructure.typeABoxMapOfHom_apply_eq_sum`). It is the `M'`-component of the box
tensor differential of the mapping cone of `f`, restricted to row vectors with values in `M`. As
for `TauCeti.TypeDStructure.typeABoxDifferential`, the sum is finite when `N`, or `M`, `M'` and
`f`, are bounded; the construction is `0` by convention whenever the operations of the matrix
module of the mapping cone of `f` along the coefficient matrix `δ` of `N` do not vanish from
some arity on. -/
noncomputable def typeABoxMapOfHom (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') : (X → M) →ₗ[R] X → M' :=
  (LinearMap.snd R M M').compLeft X ∘ₗ N.typeABoxDifferential f.cone ∘ₗ
    (LinearMap.inl R M M').compLeft X

theorem typeABoxMapOfHom_apply (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (φ : X → M) (z : X) :
    N.typeABoxMapOfHom f φ z = (N.typeABoxDifferential f.cone (fun x => (φ x, 0)) z).2 :=
  (rfl)

/-- **The induced map as a sum over paths.** When the operations `m_{n+1}(·, δ, …, δ)` of the
matrix module of the mapping cone of `f` vanish for `n ≥ K`, the `z`-component of `T_f φ` is the
sum, over the paths `x₀ → ⋯ → xₙ = z` of length `n < K`, of `f_{n+1}(φ x₀, δ x₀ x₁, …)`. -/
theorem typeABoxMapOfHom_apply_eq_sum (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxMapOfHom f φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then f.map n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [typeABoxMapOfHom_apply, typeABoxDifferential_apply_eq_sum _ _ hK, Prod.snd_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Prod.snd_sum]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- **The box tensor differential of the mapping cone.** When the operations
`m_{n+1}(·, δ, …, δ)` of the matrix module of the mapping cone of `f` vanish for `n ≥ K`, its box
tensor differential is block triangular: on `ψ : X → M × M'` it is `∂ ψ₁` on the first components,
and `∂' ψ₂ + T_f ψ₁` on the second. -/
theorem typeABoxDifferential_cone_apply (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) (ψ : X → M × M') (z : X) :
    N.typeABoxDifferential f.cone ψ z =
      (N.typeABoxDifferential Mm (fun x => (ψ x).1) z,
        N.typeABoxDifferential Mm' (fun x => (ψ x).2) z +
          N.typeABoxMapOfHom f (fun x => (ψ x).1) z) := by
  -- The operations of the matrix modules of `M` and `M'` are components of those of the cone.
  have hKM : ∀ n, K ≤ n → (Mm.matrixAct X n fun _ => N.coeff) = 0 := fun n hn =>
    LinearMap.ext fun φ => funext fun z => by
      simpa [UngradedAInfinityRightModuleHom.matrixAct_cone_apply] using congrArg (fun χ => (χ z).1)
        (LinearMap.congr_fun (hK n hn) fun x => ((φ x, 0) : M × M'))
  have hKM' : ∀ n, K ≤ n → (Mm'.matrixAct X n fun _ => N.coeff) = 0 := fun n hn =>
    LinearMap.ext fun φ => funext fun z => by
      simpa [UngradedAInfinityRightModuleHom.matrixAct_cone_apply] using congrArg (fun χ => (χ z).2)
        (LinearMap.congr_fun (hK n hn) fun x => ((0, φ x) : M × M'))
  rw [typeABoxDifferential_apply_eq_sum _ _ hK, typeABoxDifferential_apply_eq_sum _ _ hKM,
    typeABoxDifferential_apply_eq_sum _ _ hKM', typeABoxMapOfHom_apply_eq_sum _ _ hK]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [Prod.fst_sum]
    exact sum_congr rfl fun x _ => by split_ifs <;> simp
  · rw [Prod.snd_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [Prod.snd_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- The chain map identity from the vanishing of the operations of the matrix module of the cone
and the square-zero box tensor differential of the cone. -/
private theorem typeABoxDifferential_typeABoxMapOfHom_of_bound [CharP R 2]
    (N : TypeDStructure d ι X) (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0)
    (h : ∀ ψ, N.typeABoxDifferential f.cone (N.typeABoxDifferential f.cone ψ) = 0) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxMapOfHom f φ) =
      N.typeABoxMapOfHom f (N.typeABoxDifferential Mm φ) := by
  funext z
  have hz := congrArg (fun χ => (χ z).2) (h fun x => (φ x, 0))
  simp only [typeABoxDifferential_cone_apply N f hK, Pi.zero_apply, Prod.snd_zero] at hz
  simp only [← Pi.zero_def, map_zero, Pi.zero_apply, zero_add] at hz
  exact (add_eq_zero_iff_eq_of_charTwo R).mp hz

/-- **Morphisms induce chain maps, for a bounded type `D` structure.** Over a ring of
characteristic two, if the iterates `δⁿ` of `N` vanish for all large `n`, the map `T_f` induced by
a morphism `f` of `A∞` modules commutes with the box tensor differentials:
`∂' ∘ T_f = T_f ∘ ∂`, whatever the operations of the modules. -/
theorem typeABoxDifferential_typeABoxMapOfHom_of_isBounded [CharP R 2] (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (hN : N.IsBounded) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxMapOfHom f φ) =
      N.typeABoxMapOfHom f (N.typeABoxDifferential Mm φ) := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  exact N.typeABoxDifferential_typeABoxMapOfHom_of_bound f (K := K)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero f.cone (hK n hn) fun _ => Or.inl rfl)
    (N.typeABoxDifferential_typeABoxDifferential_of_isBounded f.cone hN) φ

/-- **Morphisms induce chain maps, for a type `D` structure with a height.** Over a ring of
characteristic two, if a height on the generators strictly increases along every nonzero
coefficient of `N`, then `∂' ∘ T_f = T_f ∘ ∂`. -/
theorem typeABoxDifferential_typeABoxMapOfHom_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxMapOfHom f φ) =
      N.typeABoxMapOfHom f (N.typeABoxDifferential Mm φ) :=
  N.typeABoxDifferential_typeABoxMapOfHom_of_isBounded f (N.isBounded_of_lt h hh) φ

/-- **Morphisms of bounded modules induce chain maps.** Over a ring of characteristic two, if the
operations of `M` and `M'` and the components of `f` vanish from arity `K` on, then
`∂' ∘ T_f = T_f ∘ ∂`, whatever the type `D` structure. -/
theorem typeABoxDifferential_typeABoxMapOfHom_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hM : ∀ n, K ≤ n → Mm.act n = 0) (hM' : ∀ n, K ≤ n → Mm'.act n = 0)
    (hf : ∀ n, K ≤ n → f.map n = 0) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxMapOfHom f φ) =
      N.typeABoxMapOfHom f (N.typeABoxDifferential Mm φ) := by
  have hcone (n : ℕ) (hn : K ≤ n) : f.cone.act n = 0 :=
    f.cone_act_eq_zero (hM n hn) (hM' n hn) (hf n hn)
  exact N.typeABoxDifferential_typeABoxMapOfHom_of_bound f (K := K)
    (fun n hn => by rw [f.cone.matrixAct_eq_zero_of_act_eq_zero X (hcone n hn), zero_apply])
    (N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero f.cone hcone) φ

/-- **A morphism without higher components acts componentwise.** If `f_{n+1} = 0` for `n ≥ 1`, the
induced map is `φ ↦ f₁ ∘ φ`, when the operations `m_{n+1}(·, δ, …, δ)` of the matrix module of the
mapping cone vanish for `n ≥ K`. -/
theorem typeABoxMapOfHom_apply_eq_map_zero (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (hf : ∀ n, f.map (n + 1) = 0) {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxMapOfHom f φ z = f.map 0 ![] (φ z) := by
  rw [typeABoxMapOfHom_apply_eq_sum (K := K + 1) _ _ fun n hn => hK n (by omega), sum_range_succ',
    sum_eq_zero fun n _ => by simp [hf], zero_add, ← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
  simp [Subsingleton.elim (fun _ : Fin 0 => _) ![]]

/-- **The identity morphism induces the identity**, for a bounded type `D` structure. -/
theorem typeABoxMapOfHom_id_of_isBounded [CharP R 2] (N : TypeDStructure d ι X)
    (hN : N.IsBounded) : N.typeABoxMapOfHom (UngradedAInfinityRightModuleHom.id Mm) =
      LinearMap.id := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [N.typeABoxMapOfHom_apply_eq_map_zero _ UngradedAInfinityRightModuleHom.id_map_add_one
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)]
  simp

/-- **The map induced by a chain map of differential modules.** For an `A`-linear map `g` of
differential right modules commuting with the differentials, viewed as a morphism of `A∞` modules,
the induced map on box tensor products is `φ ↦ g ∘ φ`, for every type `D` structure. -/
theorem typeABoxMapOfHom_toUngradedAInfinityRightModuleHom [CharP R 2] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M'] {dM : M →ₗ[R] M}
    {dM' : M' →ₗ[R] M'} (hM : IsUngradedDGRightModule d dM) (hM' : IsUngradedDGRightModule d dM')
    (N : TypeDStructure d ι X) (g : M →ₗ[Aᵐᵒᵖ] M') (hg : ∀ m, g (dM m) = dM' (g m))
    (φ : X → M) :
    N.typeABoxMapOfHom (hM.toUngradedAInfinityRightModuleHom hM' g hg) φ = fun x => g (φ x) := by
  funext z
  rw [N.typeABoxMapOfHom_apply_eq_map_zero _
    (IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom_map_add_one hM hM' g hg) (K := 2)
    fun n hn => ?_]
  · simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [UngradedAInfinityRightModule.matrixAct_eq_zero_of_act_eq_zero _ X
      (UngradedAInfinityRightModuleHom.cone_act_eq_zero _
        (hM.toUngradedAInfinityRightModule_act_add_two n)
        (hM'.toUngradedAInfinityRightModule_act_add_two n)
        (IsUngradedDGRightModule.toUngradedAInfinityRightModuleHom_map_add_one hM hM' g hg
          (n + 1))), zero_apply]

end ModuleHom

end TypeDStructure

end TauCeti
