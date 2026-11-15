/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA

/-!
# Homotopic morphisms of type `A` modules induce homotopic box tensor maps

A morphism `f` of `A∞` modules from `M` to `M'` induces a chain map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` of box tensor products with a type `D`
structure `N` (`TauCeti.TypeDStructure.typeABoxMapOfHom`). This file shows that a homotopy `h`
between morphisms `f` and `g` (`TauCeti.UngradedAInfinityRightModuleHom.Homotopy`) induces, by
the same formula, a chain homotopy between `T_f` and `T_g`: over a ring of characteristic two,

`T_f + T_g = ∂' ∘ T_h + T_h ∘ ∂`,

where the `z`-component of `T_h φ` is the sum, over the paths `x₀ → ⋯ → xₙ = z` of generators,
of `h_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`
(`TauCeti.TypeDStructure.typeABoxMapOfHomotopy_apply_eq_sum`). This is the half of the homotopy
invariance of the box tensor product that concerns the type `A` side; invariance under homotopies
of type `D` structures is in `TauCeti.LowDimTopology.Bordered.TypeA`.

The proof reuses the chain map property of induced maps. The homotopy `h` is a morphism `Φ` from
`M` to the mapping cone of `f + g`, with components `m ↦ (id_{n+1}(m, a…), h_{n+1}(m, a…))`
(`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.toConeHom`), and `T_h` is the second component
of `T_Φ`. Its first component is the identity, and the box tensor differential of the cone is
block triangular, `(ψ₁, ψ₂) ↦ (∂ ψ₁, ∂' ψ₂ + T_{f+g} ψ₁)`. So the second component of the chain map
identity `∂_cone ∘ T_Φ = T_Φ ∘ ∂` reads `∂' (T_h φ) + T_{f+g} φ = T_h (∂ φ)`, and
`T_{f+g} = T_f + T_g`.

As for the induced maps, the sums are finite under a boundedness hypothesis: the type `D` structure
is bounded (`TauCeti.TypeDStructure.IsBounded`), for instance by a height on its generators, or
the modules, the morphisms and the homotopy have no components from some arity on.

## Main definitions

* `TauCeti.TypeDStructure.typeABoxMapOfHomotopy`: the map of box tensor products induced by a
  homotopy of `A∞` module morphisms.

## Main results

* `TauCeti.TypeDStructure.typeABoxMapOfHomotopy_apply_eq_sum`: the induced map as a finite sum over
  paths of generators, for a bounded type `D` structure.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_add_of_isBounded`: `T_{f+g} = T_f + T_g`.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded`,
  `TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_lt` and
  `TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_act_eq_zero`: homotopic
  morphisms induce chain homotopic maps, `T_f + T_g = ∂' ∘ T_h + T_h ∘ ∂`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (homotopies of `A∞` module morphisms over `𝔽₂`, and the box tensor product, equation
  (2.29), with its invariance under homotopy equivalence).
-/

public section

open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A M M' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X]
  [DecidableEq X] {Mm : UngradedAInfinityRightModule d M} {Mm' : UngradedAInfinityRightModule d M'}
  {f g : UngradedAInfinityRightModuleHom Mm Mm'}

/-! ### Sums of morphisms -/

/-- The induced map of a sum of morphisms is the sum of the induced maps, when the operations
`m_{n+1}(·, δ, …, δ)` of the matrix modules of the three mapping cones vanish for `n ≥ K`. -/
private theorem typeABoxMapOfHom_add_apply_of_bound (N : TypeDStructure d ι X) {K : ℕ}
    (hf : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hg : ∀ n, K ≤ n → (g.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hfg : ∀ n, K ≤ n → ((f + g).cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxMapOfHom (f + g) φ z = N.typeABoxMapOfHom f φ z + N.typeABoxMapOfHom g φ z := by
  rw [typeABoxMapOfHom_apply_eq_sum _ _ hfg, typeABoxMapOfHom_apply_eq_sum _ _ hf,
    typeABoxMapOfHom_apply_eq_sum _ _ hg, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- **The induced map is additive in the morphism**, for a bounded type `D` structure:
`T_{f+g} = T_f + T_g`. -/
theorem typeABoxMapOfHom_add_of_isBounded (N : TypeDStructure d ι X) (hN : N.IsBounded) :
    N.typeABoxMapOfHom (f + g) = N.typeABoxMapOfHom f + N.typeABoxMapOfHom g := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  refine LinearMap.ext fun φ => funext fun z => ?_
  exact N.typeABoxMapOfHom_add_apply_of_bound (K := K)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl) φ z

/-! ### The map induced by a homotopy -/

/-- The **map induced on box tensor products** by a homotopy `h` from `f` to `g`: on row vectors,
`φ ↦ ∑_k (h_{k+1} ⊗ 1) (φ ⊗ δ^k)`, the sum over the paths of generators `x₀ → ⋯ → xₙ = z` of
`h_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`
(`TauCeti.TypeDStructure.typeABoxMapOfHomotopy_apply_eq_sum`). It is the `M'`-component of the
map induced by the morphism `h.toConeHom` from `M` to the mapping cone of `f + g`. As for
`TauCeti.TypeDStructure.typeABoxMapOfHom`, the sum is finite when `N`, or the modules, morphisms
and homotopy, are bounded, and the construction is `0` by convention otherwise. -/
noncomputable def typeABoxMapOfHomotopy [CharP R 2] (N : TypeDStructure d ι X)
    (h : f.Homotopy g) : (X → M) →ₗ[R] X → M' :=
  (LinearMap.snd R M M').compLeft X ∘ₗ N.typeABoxMapOfHom h.toConeHom

theorem typeABoxMapOfHomotopy_apply [CharP R 2] (N : TypeDStructure d ι X) (h : f.Homotopy g)
    (φ : X → M) (z : X) :
    N.typeABoxMapOfHomotopy h φ z = (N.typeABoxMapOfHom h.toConeHom φ z).2 :=
  (rfl)

/-- The bound on the operations of the matrix module of the mapping cone of `h.toConeHom` given by
a bound on the iterates of `N`. -/
private theorem matrixAct_cone_toConeHom_eq_zero [CharP R 2] (N : TypeDStructure d ι X)
    (h : f.Homotopy g) {K : ℕ} (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) (n : ℕ)
    (hn : K ≤ n) : (h.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0 :=
  N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl

/-- **The map induced by a homotopy as a sum over paths.** If the iterates `δⁿ` of `N` vanish for
`n ≥ K`, the `z`-component of `T_h φ` is the sum, over the paths `x₀ → ⋯ → xₙ = z` of length
`n < K`, of `h_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
theorem typeABoxMapOfHomotopy_apply_eq_sum [CharP R 2] (N : TypeDStructure d ι X)
    (h : f.Homotopy g) {K : ℕ} (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) (φ : X → M)
    (z : X) :
    N.typeABoxMapOfHomotopy h φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then h.map n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [typeABoxMapOfHomotopy_apply,
    typeABoxMapOfHom_apply_eq_sum _ _ (N.matrixAct_cone_toConeHom_eq_zero h hK), Prod.snd_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Prod.snd_sum]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- The first component of the map induced by `h.toConeHom` is the identity, since that of
`h.toConeHom` is the identity morphism, when the operations `m_{n+1}(·, δ, …, δ)` of the matrix
module of its mapping cone vanish for `n ≥ K`. -/
private theorem fst_typeABoxMapOfHom_toConeHom [CharP R 2] (N : TypeDStructure d ι X)
    (h : f.Homotopy g) {K : ℕ}
    (hK : ∀ n, K ≤ n → (h.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0) (φ : X → M)
    (z : X) : (N.typeABoxMapOfHom h.toConeHom φ z).1 = φ z := by
  rw [typeABoxMapOfHom_apply_eq_sum (K := K + 1) _ _ fun n hn => hK n (by omega), sum_range_succ',
    Prod.fst_add, Prod.fst_sum,
    sum_eq_zero fun n _ => by simp [Prod.fst_sum, apply_ite Prod.fst], zero_add, Prod.fst_sum,
    ← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
  simp [apply_ite Prod.fst]

/-- **Homotopic morphisms induce homotopic maps**, from the bounds needed to read the chain map
identity of `h.toConeHom` and the additivity of the induced maps. -/
private theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound [CharP R 2]
    (N : TypeDStructure d ι X) (h : f.Homotopy g) {K : ℕ}
    (hΦ : ∀ n, K ≤ n → (h.toConeHom.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hfg : ∀ n, K ≤ n → ((f + g).cone.matrixAct X n fun _ => N.coeff) = 0)
    (hchain : ∀ φ, N.typeABoxDifferential (f + g).cone (N.typeABoxMapOfHom h.toConeHom φ) =
      N.typeABoxMapOfHom h.toConeHom (N.typeABoxDifferential Mm φ))
    (hadd : ∀ φ, N.typeABoxMapOfHom (f + g) φ = N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ)
    (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxMapOfHomotopy h φ) +
        N.typeABoxMapOfHomotopy h (N.typeABoxDifferential Mm φ) := by
  -- The second component of the chain map identity of `h.toConeHom`:
  -- `∂' (T_h φ) + T_{f+g} φ = T_h (∂ φ)`.
  have e : N.typeABoxDifferential Mm' (N.typeABoxMapOfHomotopy h φ) +
      N.typeABoxMapOfHom (f + g) φ = N.typeABoxMapOfHomotopy h (N.typeABoxDifferential Mm φ) := by
    funext z
    have hz := congrArg (fun χ => (χ z).2) (hchain φ)
    simp only [typeABoxDifferential_cone_apply N (f + g) hfg,
      N.fst_typeABoxMapOfHom_toConeHom h hΦ] at hz
    have e₂ : (fun x => (N.typeABoxMapOfHom h.toConeHom φ x).2) = N.typeABoxMapOfHomotopy h φ :=
      funext fun x => (typeABoxMapOfHomotopy_apply N h φ x).symm
    rw [e₂] at hz
    rw [Pi.add_apply, typeABoxMapOfHomotopy_apply]
    exact hz
  rw [← e, ← hadd, ← add_assoc, add_self_eq_zero_of_charTwo R, zero_add]

/-- **Homotopic morphisms induce homotopic maps, for a bounded type `D` structure.** Over a ring of
characteristic two, if the iterates `δⁿ` of `N` vanish for all large `n`, a homotopy `h` from `f`
to `g` gives `T_f + T_g = ∂' ∘ T_h + T_h ∘ ∂`, whatever the operations of the modules. -/
theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded [CharP R 2] (N : TypeDStructure d ι X)
    (hN : N.IsBounded) (h : f.Homotopy g) (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxMapOfHomotopy h φ) +
        N.typeABoxMapOfHomotopy h (N.typeABoxDifferential Mm φ) := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  exact N.typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound h (K := K)
    (N.matrixAct_cone_toConeHom_eq_zero h hK)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)
    (N.typeABoxDifferential_typeABoxMapOfHom_of_isBounded h.toConeHom hN)
    (fun φ => by rw [N.typeABoxMapOfHom_add_of_isBounded hN, LinearMap.add_apply]) φ

/-- **Homotopic morphisms induce homotopic maps, for a type `D` structure with a height.** Over a
ring of characteristic two, if a height on the generators strictly increases along every nonzero
coefficient of `N`, a homotopy `h` from `f` to `g` gives `T_f + T_g = ∂' ∘ T_h + T_h ∘ ∂`. -/
theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (ht : X → ℕ) (hht : ∀ x y, N.coeff x y ≠ 0 → ht x < ht y) (h : f.Homotopy g) (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxMapOfHomotopy h φ) +
        N.typeABoxMapOfHomotopy h (N.typeABoxDifferential Mm φ) :=
  N.typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded (N.isBounded_of_lt ht hht) h φ

/-- **Homotopic morphisms of bounded modules induce homotopic maps.** Over a ring of
characteristic two, if the operations of `M` and `M'` and the components of `f`, `g` and of a
homotopy `h` from `f` to `g` vanish from arity `K` on, then `T_f + T_g = ∂' ∘ T_h + T_h ∘ ∂`,
whatever the type `D` structure. -/
theorem typeABoxMapOfHom_add_typeABoxMapOfHom_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0)
    (hM' : ∀ n, K ≤ n → Mm'.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) (h : f.Homotopy g) (hh : ∀ n, K ≤ n → h.map n = 0)
    (φ : X → M) :
    N.typeABoxMapOfHom f φ + N.typeABoxMapOfHom g φ =
      N.typeABoxDifferential Mm' (N.typeABoxMapOfHomotopy h φ) +
        N.typeABoxMapOfHomotopy h (N.typeABoxDifferential Mm φ) := by
  -- From arity `K + 1` on, the identity part of `h.toConeHom` vanishes too.
  have hfg (n : ℕ) (hn : K ≤ n) : (f + g).map n = 0 := by
    rw [UngradedAInfinityRightModuleHom.add_map, Pi.add_apply, hf n hn, hg n hn, add_zero]
  have hcone (n : ℕ) (hn : K ≤ n) : (f + g).cone.act n = 0 :=
    (f + g).cone_act_eq_zero (hM n hn) (hM' n hn) (hfg n hn)
  have hΦ (n : ℕ) (hn : K + 1 ≤ n) : h.toConeHom.map n = 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ n by omega)
    refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
    simp [hh (n + 1) (by omega)]
  have hΦcone (n : ℕ) (hn : K + 1 ≤ n) : h.toConeHom.cone.act n = 0 :=
    h.toConeHom.cone_act_eq_zero (hM n (by omega)) (hcone n (by omega)) (hΦ n hn)
  have hfcone (n : ℕ) (hn : K ≤ n) : f.cone.act n = 0 :=
    f.cone_act_eq_zero (hM n hn) (hM' n hn) (hf n hn)
  have hgcone (n : ℕ) (hn : K ≤ n) : g.cone.act n = 0 :=
    g.cone_act_eq_zero (hM n hn) (hM' n hn) (hg n hn)
  exact N.typeABoxMapOfHom_add_typeABoxMapOfHom_of_bound h (K := K + 1)
    (fun n hn => by
      rw [h.toConeHom.cone.matrixAct_eq_zero_of_act_eq_zero X (hΦcone n hn), zero_apply])
    (fun n hn => by
      rw [(f + g).cone.matrixAct_eq_zero_of_act_eq_zero X (hcone n (by omega)), zero_apply])
    (N.typeABoxDifferential_typeABoxMapOfHom_of_act_eq_zero h.toConeHom
      (fun n hn => hM n (by omega)) (fun n hn => hcone n (by omega)) hΦ)
    (fun φ => funext fun z => N.typeABoxMapOfHom_add_apply_of_bound (K := K)
      (fun n hn => by rw [f.cone.matrixAct_eq_zero_of_act_eq_zero X (hfcone n hn), zero_apply])
      (fun n hn => by rw [g.cone.matrixAct_eq_zero_of_act_eq_zero X (hgcone n hn), zero_apply])
      (fun n hn => by
        rw [(f + g).cone.matrixAct_eq_zero_of_act_eq_zero X (hcone n hn), zero_apply]) φ z) φ

end TypeDStructure

end TauCeti
