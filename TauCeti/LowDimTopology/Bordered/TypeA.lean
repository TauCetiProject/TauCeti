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
element `δ` (`TauCeti.TypeDStructure.typeABoxDifferential`).

The sum over `k` is infinite in general, and the box tensor product is only defined under a
boundedness hypothesis. Two are treated here, over a ring of characteristic two; under either one
the differential squares to zero.

* The module `M` is bounded: its operations `m_{k+1}` vanish for `k ≥ K`
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero`).
* The type `D` structure is bounded, in the strong form that the generators carry a height which
  strictly increases along every nonzero coefficient. The paths of nonzero coefficients then have
  bounded length, so `δ^k = 0` for large `k`
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_lt`).

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
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxDifferential_of_lt`: the differential
  squares to zero when the module, respectively the type `D` structure, is bounded.
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
row vectors `φ : X → M`: `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))`. It is the twist of the
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

omit [DecidableEq X] in
/-- The structure equation of a type `D` structure says that its coefficient matrix is a
Maurer–Cartan element of the matrix algebra with the entrywise differential. -/
theorem mapMatrix_coeff_add_coeff_mul_coeff (N : TypeDStructure d ι X) :
    (d.mapMatrix : Matrix X X A →ₗ[R] Matrix X X A) N.coeff + N.coeff * N.coeff = 0 := by
  rw [LinearMap.mapMatrix_apply]
  exact N.map_coeff_add_coeff_mul_coeff

/-- **The box tensor differential of a bounded module squares to zero.** If the operations
`m_{k+1}` of `M` vanish for `k ≥ K`, then `∂ ∘ ∂ = 0` on `M ⊠ N`, over a ring of characteristic
two. -/
theorem typeABoxDifferential_typeABoxDifferential_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) (Mm : UngradedAInfinityRightModule d M) {K : ℕ}
    (hK : ∀ n, K ≤ n → Mm.act n = 0) (φ : X → M) :
    N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 := by
  refine (Mm.matrix X).twistedDifferential_twistedDifferential
    N.mapMatrix_coeff_add_coeff_mul_coeff (Set.mem_univ _) (Set.mem_univ _)
    (K := K) (fun n hn F _ => ?_) φ
  refine LinearMap.ext fun ψ => funext fun z => ?_
  simp [Mm.matrixAct_apply, hK n hn]

omit [Fintype X] [DecidableEq X] in
/-- Along a path whose height increases at every step, the height of the end point is at least
the length of the path. -/
private theorem le_height_last {n : ℕ} (h : X → ℕ) (x : Fin (n + 1) → X)
    (hx : ∀ l : Fin n, h (x l.castSucc) < h (x l.succ)) : n ≤ h (x (Fin.last n)) := by
  have key : ∀ k (hk : k ≤ n), k ≤ h (x ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro hk
      have := hx ⟨k, by omega⟩
      have := ih (by omega)
      simp only [Fin.castSucc_mk, Fin.succ_mk] at *
      omega
  exact key n le_rfl

/-- **The box tensor differential with a bounded type `D` structure squares to zero.** If a
height `h` on the generators strictly increases along every nonzero coefficient of `N`, then
`∂ ∘ ∂ = 0` on `M ⊠ N`, over a ring of characteristic two, whatever the operations of `M`. -/
theorem typeABoxDifferential_typeABoxDifferential_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) :
    N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 := by
  set U : Set (Matrix X X A) := {F | ∀ x y, F x y ≠ 0 → h x < h y}
  have hU : N.coeff * N.coeff ∈ U := fun x y hxy => by
    obtain ⟨w, -, hw⟩ := exists_ne_zero_of_sum_ne_zero hxy
    exact (hh x w (left_ne_zero_of_mul hw)).trans (hh w y (right_ne_zero_of_mul hw))
  refine (Mm.matrix X).twistedDifferential_twistedDifferential
    N.mapMatrix_coeff_add_coeff_mul_coeff hh hU (K := univ.sup h + 1)
    (fun n hn F hF => ?_) φ
  refine LinearMap.ext fun ψ => funext fun z => ?_
  simp only [UngradedAInfinityRightModule.matrix_act, Mm.matrixAct_apply, LinearMap.zero_apply,
    Pi.zero_apply]
  refine sum_eq_zero fun x _ => ?_
  -- Some coefficient along the path `x` vanishes, since the height cannot increase `n` times.
  obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
    by_contra hne
    push Not at hne
    have := le_height_last h x fun l => hF l _ _ (hne l)
    have := le_sup (f := h) (mem_univ (x (Fin.last n)))
    omega
  rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply, ite_self]

/-- **The box tensor product with a differential module.** For a differential right module,
viewed as an `A∞` module, the box tensor differential is `∂ φ = dM φ + φ ⬝ δ`, the differential
`TauCeti.TypeDStructure.boxDifferential`. -/
theorem typeABoxDifferential_toUngradedAInfinityRightModule [CharP R 2] [Module Aᵐᵒᵖ M]
    [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (N : TypeDStructure d ι X) :
    N.typeABoxDifferential hM.toUngradedAInfinityRightModule = N.boxDifferential dM := by
  rw [typeABoxDifferential_def, UngradedAInfinityRightModule.twistedDifferential_eq_sum (K := 2)]
  · refine LinearMap.ext fun φ => funext fun z => ?_
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, LinearMap.add_apply,
      Pi.add_apply, UngradedAInfinityRightModule.matrix_act,
      UngradedAInfinityRightModule.matrixAct_apply, boxDifferential_apply,
      IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_zero,
      IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one]
    rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp, ← (piFinTwoEquiv fun _ => X).symm.sum_comp,
      Fintype.sum_prod_type]
    simp [Fin.last, continuationMap_apply (R := R) (M := M) N.coeff]
  · intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine LinearMap.ext fun ψ => funext fun z => ?_
    simp [UngradedAInfinityRightModule.matrixAct_apply]

end TypeDStructure

end TauCeti
