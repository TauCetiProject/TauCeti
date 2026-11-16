/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA.Basic

/-!
# Homotopic morphisms of type `A` modules induce homotopic maps of box tensor products

A morphism `f` of `A∞` modules from `M` to `M'` induces the chain map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` of box tensor products with a type `D` structure
`N` (`TauCeti.TypeDStructure.typeABoxMapOfHom`). This file shows that homotopic morphisms induce
chain homotopic maps. A homotopy `H` between morphisms `f` and `g`
(`TauCeti.UngradedAInfinityRightModuleHom.Homotopy`), with components `h_{k+1}`, induces the map
`T_H (m ⊗ x) = ∑_k (h_{k+1} ⊗ 1) (m ⊗ δ^k (x))` (`TauCeti.TypeDStructure.typeABoxHomotopy`), and

`T_f + T_g = ∂' ∘ T_H + T_H ∘ ∂`

over a ring of characteristic two, where `∂` and `∂'` are the box tensor differentials, when the
type `D` structure is bounded or the modules, the morphisms and the homotopy are.

The proof reads the homotopy as the morphism `(id, h)` from `M` into the mapping cone of `f + g`
(`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`). Its induced map is `φ ↦ (φ, T_H φ)`,
and the box tensor differential of the cone is block triangular, with off-diagonal block
`T_{f+g} = T_f + T_g`. The `M'`-component of the chain map identity of `(id, h)` is then the
homotopy identity above.

## Main definitions

* `TauCeti.TypeDStructure.typeABoxHomotopy`: the map of box tensor products induced by a
  homotopy of morphisms of `A∞` modules.

## Main results

* `TauCeti.TypeDStructure.typeABoxMapOfHom_add_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxMapOfHom_add_of_act_eq_zero`: the induced maps are additive in
  the morphism, `T_{f+g} = T_f + T_g`.
* `TauCeti.TypeDStructure.typeABoxHomotopy_apply_eq_sum`: the induced homotopy as a finite sum
  over paths of generators.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_act_eq_zero`: homotopic
  morphisms induce homotopic chain maps, `T_f + T_g = ∂' ∘ T_H + T_H ∘ ∂`, when the type `D`
  structure, respectively the modules, the morphisms and the homotopy, are bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (homotopies of morphisms of `A∞` modules over `𝔽₂`, and the functoriality of the box
  tensor product, equation (2.29), in the type `A` module).
-/

public section

open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A M M' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*}
  [Fintype X] [DecidableEq X] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'}

/-! ### Additivity in the morphism -/

/-- The induced map of a sum of morphisms is the sum of the induced maps, when the operations of
the matrix modules of the three mapping cones along `δ` vanish from a common arity on. -/
private theorem typeABoxMapOfHom_add_of_bound (N : TypeDStructure d ι X)
    (f g : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hf : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hg : ∀ n, K ≤ n → (g.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hfg : ∀ n, K ≤ n → ((f + g).cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom (f + g) = N.typeABoxMapOfHom f + N.typeABoxMapOfHom g := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [LinearMap.add_apply, Pi.add_apply, typeABoxMapOfHom_apply_eq_sum N _ hfg,
    typeABoxMapOfHom_apply_eq_sum N _ hf, typeABoxMapOfHom_apply_eq_sum N _ hg,
    ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- **The induced maps are additive in the morphism, for a bounded type `D` structure:**
`T_{f+g} = T_f + T_g`. -/
theorem typeABoxMapOfHom_add_of_isBounded (N : TypeDStructure d ι X) (hN : N.IsBounded)
    (f g : UngradedAInfinityRightModuleHom Mm Mm') :
    N.typeABoxMapOfHom (f + g) = N.typeABoxMapOfHom f + N.typeABoxMapOfHom g := by
  obtain ⟨K, hK⟩ := hN.exists_matrixAct_eq_zero
  exact typeABoxMapOfHom_add_of_bound N f g (K := K) (hK _) (hK _) (hK _)

/-- **The induced maps are additive in the morphism, for bounded modules and morphisms:**
`T_{f+g} = T_f + T_g` when the operations of `M` and `M'` and the components of `f` and `g`
vanish from arity `K` on. -/
theorem typeABoxMapOfHom_add_of_act_eq_zero (N : TypeDStructure d ι X)
    (f g : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0)
    (hM' : ∀ n, K ≤ n → Mm'.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) :
    N.typeABoxMapOfHom (f + g) = N.typeABoxMapOfHom f + N.typeABoxMapOfHom g :=
  typeABoxMapOfHom_add_of_bound N f g (N.cone_matrixAct_eq_zero_of_act_eq_zero hM hM' hf)
    (N.cone_matrixAct_eq_zero_of_act_eq_zero hM hM' hg)
    (N.cone_matrixAct_eq_zero_of_act_eq_zero hM hM' fun n hn => by
      rw [UngradedAInfinityRightModuleHom.add_map, hf n hn, hg n hn, add_zero])

/-! ### The induced homotopy -/

section Homotopy

variable [CharP R 2] {f g : UngradedAInfinityRightModuleHom Mm Mm'}

/-- The **homotopy induced on box tensor products** by a homotopy `H` between morphisms `f` and
`g` of `A∞` modules: on row vectors, `φ ↦ ∑_k (h_{k+1} ⊗ 1) (φ ⊗ δ^k)`, the sum over the paths of
generators `x₀ → ⋯ → xₙ = z` of `h_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`
(`TauCeti.TypeDStructure.typeABoxHomotopy_apply_eq_sum`). It is the `M'`-component of the map
induced by the morphism `(id, h)` from `M` into the mapping cone of `f + g`
(`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`). As for
`TauCeti.TypeDStructure.typeABoxMapOfHom`, the sum is finite when `N`, or the modules, the
morphisms and the homotopy, are bounded, and the construction is `0` by convention otherwise. -/
noncomputable def typeABoxHomotopy (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) : (X → M) →ₗ[R] X → M' :=
  (LinearMap.snd R M M').compLeft X ∘ₗ N.typeABoxMapOfHom H.toConeHom

theorem typeABoxHomotopy_apply (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) (φ : X → M) (z : X) :
    N.typeABoxHomotopy H φ z = (N.typeABoxMapOfHom H.toConeHom φ z).2 :=
  (rfl)

/-- **The induced homotopy as a sum over paths.** When the operations `m_{n+1}(·, δ, …, δ)` of the
matrix module of the mapping cone of `(id, h)` vanish for `n ≥ K`, the `z`-component of `T_H φ` is
the sum, over the paths `x₀ → ⋯ → xₙ = z` of length `n < K`, of `h_{n+1}(φ x₀, δ x₀ x₁, …)`. -/
theorem typeABoxHomotopy_apply_eq_sum (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) {K : ℕ}
    (hK : ∀ n, K ≤ n → (H.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M)
    (z : X) :
    N.typeABoxHomotopy H φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then H.map n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [typeABoxHomotopy_apply, typeABoxMapOfHom_apply_eq_sum _ _ hK, Prod.snd_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Prod.snd_sum]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- The first component of the map induced by `(id, h)` is the identity. -/
private theorem fst_typeABoxMapOfHom_toConeHom (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) {K : ℕ}
    (hK : ∀ n, K ≤ n → (H.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M)
    (z : X) : (N.typeABoxMapOfHom H.toConeHom φ z).1 = φ z := by
  rw [typeABoxMapOfHom_apply_eq_sum (K := K + 1) _ _ fun n hn => hK n (by omega)]
  simp only [Prod.fst_sum, apply_ite Prod.fst, Prod.fst_zero,
    UngradedAInfinityRightModuleHom.Homotopy.toConeHom_map_apply]
  -- Only the paths of length zero contribute, since `id_{n+1} = 0` for `n ≥ 1`.
  rw [sum_eq_single 0 (fun n _ hn => by
    simp [UngradedAInfinityRightModuleHom.id_map_eq_zero hn]) (by simp)]
  simp [← (Equiv.funUnique (Fin 1) X).symm.sum_comp]

/-- The homotopy identity from the chain map identity of `(id, h)`, the additivity of the
induced maps and the vanishing of the operations of the matrix modules of the cones. -/
private theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) {K : ℕ}
    (hfg : ∀ n, K ≤ n → ((f + g).cone.matrixAct X n fun _ => N.coeff) = 0)
    (hH : ∀ n, K ≤ n → (H.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hchain : ∀ φ, N.typeABoxDifferential (f + g).cone (N.typeABoxMapOfHom H.toConeHom φ) =
      N.typeABoxMapOfHom H.toConeHom (N.typeABoxDifferential Mm φ))
    (hadd : N.typeABoxMapOfHom (f + g) = N.typeABoxMapOfHom f + N.typeABoxMapOfHom g)
    (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxHomotopy H φ) +
        N.typeABoxHomotopy H (N.typeABoxDifferential Mm φ) := by
  funext z
  -- The `M'`-component of `∂_cone ∘ T_(id, h) = T_(id, h) ∘ ∂` at `z`.
  have hz := congrArg (fun χ => (χ z).2) (hchain φ)
  have h₁ : (fun x => (N.typeABoxMapOfHom H.toConeHom φ x).1) = φ :=
    funext (fst_typeABoxMapOfHom_toConeHom N H hH φ)
  simp only [typeABoxDifferential_cone_apply N (f + g) hfg, h₁, hadd, LinearMap.add_apply,
    Pi.add_apply, ← typeABoxHomotopy_apply] at hz
  rw [Pi.add_apply, Pi.add_apply, ← hz, ← add_assoc, add_self_eq_zero_of_charTwo R, zero_add]

/-- **Homotopic morphisms induce homotopic chain maps, for a bounded type `D` structure.** Over a
ring of characteristic two, if the iterates `δⁿ` of `N` vanish for all large `n`, a homotopy `H`
between morphisms `f` and `g` of `A∞` modules gives `T_f + T_g = ∂' ∘ T_H + T_H ∘ ∂`, whatever
the operations of the modules. -/
theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded (N : TypeDStructure d ι X)
    (hN : N.IsBounded) (H : UngradedAInfinityRightModuleHom.Homotopy f g) (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxHomotopy H φ) +
        N.typeABoxHomotopy H (N.typeABoxDifferential Mm φ) := by
  obtain ⟨K, hK⟩ := hN.exists_matrixAct_eq_zero
  exact typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound N H (K := K) (hK _) (hK _)
    (N.typeABoxDifferential_typeABoxMapOfHom_of_isBounded H.toConeHom hN)
    (N.typeABoxMapOfHom_add_of_isBounded hN f g) φ

/-- **Homotopic morphisms of bounded modules induce homotopic chain maps.** Over a ring of
characteristic two, if the operations of `M` and `M'`, the components of `f` and `g` and those of
the homotopy `H` vanish from arity `K` on, then `T_f + T_g = ∂' ∘ T_H + T_H ∘ ∂`, whatever the type
`D` structure. -/
theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_act_eq_zero (N : TypeDStructure d ι X)
    (H : UngradedAInfinityRightModuleHom.Homotopy f g) {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0)
    (hM' : ∀ n, K ≤ n → Mm'.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) (hH : ∀ n, K ≤ n → H.map n = 0) (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxHomotopy H φ) +
        N.typeABoxHomotopy H (N.typeABoxDifferential Mm φ) := by
  have hfg (n : ℕ) (hn : K ≤ n) : (f + g).map n = 0 := by
    rw [UngradedAInfinityRightModuleHom.add_map, hf n hn, hg n hn, add_zero]
  have hcone (n : ℕ) (hn : K ≤ n) : (f + g).cone.act n = 0 :=
    (f + g).cone_act_eq_zero (hM n hn) (hM' n hn) (hfg n hn)
  -- The component `id_{n+1}` of `(id, h)` vanishes only for `n ≥ 1`, so the bound is `K + 1`.
  have hΦ (n : ℕ) (hn : K + 1 ≤ n) : H.toConeHom.map n = 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_of_lt hn)
    ext a m <;> simp [hH (n + 1) (by omega)]
  have hM₁ (n : ℕ) (hn : K + 1 ≤ n) : Mm.act n = 0 := hM n (by omega)
  have hcone₁ (n : ℕ) (hn : K + 1 ≤ n) : (f + g).cone.act n = 0 := hcone n (by omega)
  exact typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound N H (K := K + 1)
    (fun n hn => N.cone_matrixAct_eq_zero_of_act_eq_zero hM hM' hfg n (by omega))
    (N.cone_matrixAct_eq_zero_of_act_eq_zero hM₁ hcone₁ hΦ)
    (N.typeABoxDifferential_typeABoxMapOfHom_of_act_eq_zero H.toConeHom hM₁ hcone₁ hΦ)
    (N.typeABoxMapOfHom_add_of_act_eq_zero f g hM hM' hf hg) φ

end Homotopy

end TypeDStructure

end TauCeti
