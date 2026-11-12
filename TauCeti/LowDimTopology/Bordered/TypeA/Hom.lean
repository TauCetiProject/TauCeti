/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Ungraded
public import TauCeti.LowDimTopology.Bordered.TypeA

/-!
# Maps of box tensor products induced by morphisms of type `A` modules

This file continues `TauCeti.LowDimTopology.Bordered.TypeA`, where the box tensor differential
`TauCeti.TypeDStructure.typeABoxDifferential` of an `A∞` right module with a type `D` structure is
defined.

A morphism `f` of `A∞` modules from `M` to `M'`
(`TauCeti.UngradedAInfinityRightModuleHom`) induces the map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` on box tensor products
(`TauCeti.TypeDStructure.typeABoxMapOfHom`). It is the off-diagonal component of the box tensor
differential of the mapping cone of `f` (`TauCeti.UngradedAInfinityRightModuleHom.cone`), which is
block triangular with diagonal blocks the box tensor differentials of `M` and `M'`; since that
differential squares to zero, `∂' ∘ T_f = T_f ∘ ∂` under either boundedness hypothesis. For a
bounded type `D` structure, the identity morphism induces the identity. For any type `D` structure,
an `A`-linear chain map `g` of differential modules induces `φ ↦ g ∘ φ`.

## Main definitions

* `TauCeti.TypeDStructure.typeABoxMapOfHom`: the map of box tensor products induced by a morphism
  of `A∞` modules.

## Main results

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
  Chapter 2 (morphisms of `A∞` modules and the box tensor product).
-/

public section

open Finset MulOpposite

namespace TauCeti

namespace TypeDStructure

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

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
