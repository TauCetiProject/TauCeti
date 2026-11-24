/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.LinearAlgebra.Multilinear.CompSplit

/-!
# Composites of morphisms of type `A` modules on box tensor products

A morphism `f` of `A∞` modules from `M` to `M'` induces the map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` from `M ⊠ N` to `M' ⊠ N`, for a type `D`
structure `N` (`TauCeti.TypeDStructure.typeABoxMapOfHom`). This file shows that the map of a
composite is the composite of the maps: `T_{g ∘ f} = T_g ∘ T_f`, for the composite
`TauCeti.UngradedAInfinityRightModuleHom.comp` of morphisms of `A∞` modules, when the type `D`
structure is bounded or the modules and the morphisms are.

On row vectors `φ : X → M`, `T_f φ` is the sum over `n` of the maps `P^f_n` whose `z`-component
is the sum, over the paths of generators `x₀ → ⋯ → xₙ = z`, of `f_{n+1}(φ x₀, δ x₀ x₁, …)`. A
path of length `n` from `x₀` to `z` is a path of length `k` followed by a path of length `n - k`,
and the component `(g ∘ f)_{n+1}` is the sum over `k` of `g_{n-k+1}` after `f_{k+1}`, so
`P^{g ∘ f}_n = ∑_{k ≤ n} P^g_{n-k} ∘ P^f_k`. Summing over `n` gives `T_{g ∘ f} = T_g ∘ T_f`, as
for the square of a twisted differential
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential_eq_sum`).

Together with the identity `T_{id} = id`
(`TauCeti.TypeDStructure.typeABoxMapOfHom_id_of_isBounded`), this makes `M ↦ M ⊠ N` functorial in
morphisms of type `A` modules, for a bounded type `D` structure: morphisms `f : M → M'` and
`g : M' → M` induce maps whose composites `T_g ∘ T_f` and `T_f ∘ T_g` are the maps of `g ∘ f` and
`f ∘ g`. This reduces the invariance of the box tensor product under homotopy equivalences of type
`A` modules to the fact that homotopic morphisms induce homotopic maps.

## Main results

* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_isBounded`: `T_{g ∘ f} = T_g ∘ T_f` for a
  bounded type `D` structure.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_lt`: the same for a type `D` structure whose
  coefficients increase a height on its generators.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_act_eq_zero`: the same when the operations of
  the modules and the components of the morphisms vanish from some arity on.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (morphisms of `A∞` modules over `𝔽₂`, their composition, and the box tensor product
  with its functoriality).
-/

public section

open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A M M' M'' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M''] {d : A →ₗ[R] A} {S : Type*}
  {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'} {Mm'' : UngradedAInfinityRightModule d M''}

/-- The part of `T_f` along the paths of length `n`: the `M'`-component of the operation
`m_{n+1}(·, δ, …, δ)` of the matrix module of the mapping cone of `f`, on row vectors with values
in `M`. -/
private noncomputable def pathMap (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) : (X → M) →ₗ[R] X → M' :=
  (LinearMap.snd R M M').compLeft X ∘ₗ (f.cone.matrixAct X n fun _ => N.coeff) ∘ₗ
    (LinearMap.inl R M M').compLeft X

/-- The `z`-component of `P^f_n φ` is the sum over the paths `x₀ → ⋯ → xₙ = z` of
`f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
private theorem pathMap_apply (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) (φ : X → M) (z : X) :
    pathMap N f n φ z = ∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
      f.map n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0)) else 0 :=
  UngradedAInfinityRightModuleHom.snd_matrixAct_cone_apply_inl f X n _ φ z

/-- When the operations of the matrix module of the mapping cone of `f` along `δ` vanish from
arity `K` on, `T_f` is the sum of the `P^f_n` for `n < K`. -/
private theorem typeABoxMapOfHom_eq_sum_pathMap (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom f = ∑ n ∈ range K, pathMap N f n := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [typeABoxMapOfHom_apply_eq_sum N f hK φ z, LinearMap.sum_apply, Finset.sum_apply]
  exact sum_congr rfl fun n _ => (pathMap_apply N f n φ z).symm

/-- **The paths of a composite.** `P^{g ∘ f}_n = ∑_{k ≤ n} P^g_{n-k} ∘ P^f_k`: a path of length
`n` is a path of length `k` followed by one of length `n - k`. -/
private theorem pathMap_comp [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    (n : ℕ) (φ : X → M) (z : X) :
    pathMap N (g.comp f) n φ z =
      ∑ k ∈ range (n + 1), pathMap N g (n - k) (pathMap N f k φ) z := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => pathMap N g (n - k) (pathMap N f k φ) z)]
  -- Expand both path sums, then concatenate the two paths.
  have hk (k : Fin (n + 1)) : pathMap N g (n - k) (pathMap N f k φ) z =
      ∑ w : Fin (n + 1) → X, if w (Fin.last n) = z then
        g.map (n - k)
          (fun l => N.coeff (w ⟨k + l, Nat.lt_succ_of_lt (Nat.add_lt_of_lt_sub' l.isLt)⟩)
            (w ⟨k + l + 1, Nat.succ_lt_succ (Nat.add_lt_of_lt_sub' l.isLt)⟩))
          (f.map k (fun l => N.coeff (w ⟨l, l.isLt.trans k.isLt⟩)
            (w ⟨l + 1, (Nat.succ_lt_succ l.isLt).trans_le k.isLt⟩)) (φ (w 0)))
      else 0 := by
    simp only [pathMap_apply]
    exact MultilinearMap.sum_ite_apply_sum_ite_eq_sum (by omega) (g.map (n - k)) (f.map k)
      (fun _ => N.coeff) (fun _ => N.coeff) φ z
  rw [sum_congr rfl fun k _ => hk k, sum_comm, pathMap_apply]
  refine sum_congr rfl fun w _ => ?_
  rw [UngradedAInfinityRightModuleHom.comp_map_apply]
  split_ifs
  · refine sum_congr rfl fun k _ => ?_
    simp only [Fin.castSucc_mk, Fin.succ_mk]
  · simp

/-- The map of a composite is the composite of the maps, when the operations of the matrix
modules of the mapping cones of `f`, `g` and `g ∘ f` along `δ` vanish from arity `K` on. -/
private theorem typeABoxMapOfHom_comp_of_bound [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    {K : ℕ} (hf : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hg : ∀ n, K ≤ n → (g.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hgf : ∀ n, K ≤ n → ((g.comp f).cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  have hPf (i : ℕ) (hi : K ≤ i) : pathMap N f i = 0 := by simp [pathMap, hf i hi]
  have hPg (j : ℕ) (hj : K ≤ j) : pathMap N g j = 0 := by simp [pathMap, hg j hj]
  have hPgf (n : ℕ) (hn : K ≤ n) : pathMap N (g.comp f) n = 0 := by simp [pathMap, hgf n hn]
  refine LinearMap.ext fun φ => funext fun z => ?_
  -- `G i j` is the part of `T_g ∘ T_f` along the paths of lengths `i` for `f` and `j` for `g`.
  set G : ℕ → ℕ → M'' := fun i j => pathMap N g j (pathMap N f i φ) z with hG
  have hGi (i j : ℕ) (hi : K ≤ i) : G i j = 0 := by simp [hG, hPf i hi]
  have hGj (i j : ℕ) (hj : K ≤ j) : G i j = 0 := by simp [hG, hPg j hj]
  rw [typeABoxMapOfHom_eq_sum_pathMap N (g.comp f) hgf, LinearMap.comp_apply,
    typeABoxMapOfHom_eq_sum_pathMap N f hf, typeABoxMapOfHom_eq_sum_pathMap N g hg]
  simp only [LinearMap.sum_apply, map_sum, Finset.sum_apply]
  calc ∑ n ∈ range K, pathMap N (g.comp f) n φ z
      = ∑ n ∈ range (K + K), ∑ ij ∈ antidiagonal n, G ij.1 ij.2 := by
        rw [sum_subset (f := fun n => pathMap N (g.comp f) n φ z)
          (range_subset_range.mpr (Nat.le_add_right K K)) fun n _ hn => by
            rw [hPgf n (by simpa using hn), LinearMap.zero_apply, Pi.zero_apply]]
        exact sum_congr rfl fun n _ => (pathMap_comp N g f n φ z).trans
          (Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => G ij.1 ij.2) n).symm
    _ = ∑ i ∈ range K, ∑ j ∈ range K, G i j :=
        sum_range_add_antidiagonal_of_support K K (fun ij => G ij.1 ij.2) fun i j h =>
          h.elim (hGi i j) (hGj i j)

/-- **The map of a composite is the composite of the maps**, for a bounded type `D` structure.
Over a ring of characteristic two, if the iterates `δⁿ` of `N` vanish for all large `n`, then
`T_{g ∘ f} = T_g ∘ T_f` for morphisms `f` from `M` to `M'` and `g` from `M'` to `M''` of `A∞`
modules, whatever their operations. -/
theorem typeABoxMapOfHom_comp_of_isBounded [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    (hN : N.IsBounded) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  exact N.typeABoxMapOfHom_comp_of_bound g f
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n hn) fun _ => Or.inl rfl)

/-- **The map of a composite is the composite of the maps**, for a type `D` structure with a
height. Over a ring of characteristic two, if a height on the generators strictly increases
along every nonzero coefficient of `N`, then `T_{g ∘ f} = T_g ∘ T_f`. -/
theorem typeABoxMapOfHom_comp_of_lt [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f :=
  N.typeABoxMapOfHom_comp_of_isBounded g f (N.isBounded_of_lt h hh)

/-- **The map of a composite of bounded morphisms is the composite of the maps.** Over a ring of
characteristic two, if the operations of `M`, `M'` and `M''` and the components of `f` and `g`
vanish from arity `K` on, then `T_{g ∘ f} = T_g ∘ T_f`, whatever the type `D` structure. -/
theorem typeABoxMapOfHom_comp_of_act_eq_zero [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0) (hM' : ∀ n, K ≤ n → Mm'.act n = 0)
    (hM'' : ∀ n, K ≤ n → Mm''.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  -- All the operations involved vanish from arity `K + K` on.
  refine N.typeABoxMapOfHom_comp_of_bound g f (K := K + K) (fun n hn => ?_) (fun n hn => ?_)
    fun n hn => ?_
  · rw [UngradedAInfinityRightModule.matrixAct_eq_zero_of_act_eq_zero _ X
      (f.cone_act_eq_zero (hM n (by omega)) (hM' n (by omega)) (hf n (by omega))), zero_apply]
  · rw [UngradedAInfinityRightModule.matrixAct_eq_zero_of_act_eq_zero _ X
      (g.cone_act_eq_zero (hM' n (by omega)) (hM'' n (by omega)) (hg n (by omega))), zero_apply]
  · rw [UngradedAInfinityRightModule.matrixAct_eq_zero_of_act_eq_zero _ X
      ((g.comp f).cone_act_eq_zero (hM n (by omega)) (hM'' n (by omega))
        (g.comp_map_eq_zero f hf hg hn)), zero_apply]

end TypeDStructure

end TauCeti
