/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA
import TauCeti.Algebra.BigOperators.Fin

/-!
# The box tensor product is functorial in the type `A` module

A morphism `f` of `A∞` modules from `M` to `M'` induces the map
`T_f = f ⊠ id_N : M ⊠ N → M' ⊠ N` of box tensor products with a type `D` structure `N`
(`TauCeti.TypeDStructure.typeABoxMapOfHom`), the sum over the paths `x₀ → ⋯ → xₙ = z` of
generators of `f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. This file shows that the composite morphism
`g ∘ f` (`TauCeti.UngradedAInfinityRightModuleHom.comp`) induces the composite map:

`T_{g ∘ f} = T_g ∘ T_f`,

under each of the boundedness hypotheses for which the induced maps are chain maps. Together with
`TauCeti.TypeDStructure.typeABoxMapOfHom_id_of_isBounded`, this makes `M ↦ M ⊠ N` a functor, so
that the box tensor product carries an isomorphism of type `A` modules to an isomorphism of
complexes.

A path of length `n` from `x₀` to `z` splits at each of its vertices `xₖ` into a path of length
`k` followed by one of length `n - k`, and the component `(g ∘ f)_{n+1}` is the sum over these
splittings of `g_{n-k+1}(f_{k+1}(…), …)`. So the path sums of length `n` of `g ∘ f` are the sums,
over `i + j = n`, of the path sums of length `j` of `g` applied to those of length `i` of `f`. The
path sums of `f` vanish from length `K` on when the type `D` structure is bounded, and so do those
of `g` and of `g ∘ f`; the double sum of the composite map, over pairs `i, j < K`, then agrees with
the sum over `i + j < K` defining the map of the composite.

## Main results

* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_isBounded`: `T_{g ∘ f} = T_g ∘ T_f` for a bounded
  type `D` structure.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_lt`: the same along a height on the generators
  that strictly increases along every nonzero coefficient.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_comp_of_act_eq_zero`: the same when the operations of
  the modules and the components of the morphisms vanish from some arity on.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (composition of morphisms of `A∞` modules) and §2.4 (functoriality of the box tensor
  product).
-/

public section

open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A M M' M'' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M''] {d : A →ₗ[R] A} {S : Type*}
  {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X] {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'} {Mm'' : UngradedAInfinityRightModule d M''}

/-- The contribution of the paths of length `n` to the map induced by `f`: on row vectors, the sum
over the paths `x₀ → ⋯ → xₙ = z` of `f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
private noncomputable def pathMap (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) : (X → M) →ₗ[R] X → M' :=
  (LinearMap.snd R M M').compLeft X ∘ₗ f.cone.matrixAct X n (fun _ => N.coeff) ∘ₗ
    (LinearMap.inl R M M').compLeft X

private theorem pathMap_apply (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') (n : ℕ) (φ : X → M) (z : X) :
    pathMap N f n φ z = ∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
      f.map n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0)) else 0 := by
  have h0 : (fun _ : X => (0 : M')) = 0 := rfl
  simp [pathMap, UngradedAInfinityRightModuleHom.matrixAct_cone_apply, h0]

private theorem pathMap_eq_zero (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {n : ℕ}
    (h : (f.cone.matrixAct X n fun _ => N.coeff) = 0) : pathMap N f n = 0 := by
  simp [pathMap, h]

private theorem typeABoxMapOfHom_eq_sum_pathMap (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom f = ∑ n ∈ range K, pathMap N f n := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [N.typeABoxMapOfHom_apply_eq_sum f hK, LinearMap.sum_apply, Finset.sum_apply]
  simp only [pathMap_apply]

/-- **Concatenating paths.** The path sum of length `j` of `g` applied to that of length `i` of `f`
is the sum over the paths `w₀ → ⋯ → wᵢ₊ⱼ = z` of
`g_{j+1}(f_{i+1}(φ w₀, δ w₀ w₁, …), δ wᵢ wᵢ₊₁, …)`. -/
private theorem pathMap_pathMap_apply (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    {i j n : ℕ} (h : i + j = n) (φ : X → M) (z : X) :
    pathMap N g j (pathMap N f i φ) z = ∑ w : Fin (n + 1) → X,
      if w (Fin.last n) = z then
        g.map j (fun l => N.coeff (w ⟨i + l, by have := l.isLt; omega⟩)
          (w ⟨i + l + 1, by have := l.isLt; omega⟩))
          (f.map i (fun l => N.coeff (w ⟨l, by have := l.isLt; omega⟩)
            (w ⟨l + 1, by have := l.isLt; omega⟩)) (φ (w 0)))
      else 0 := by
  have hy (y : Fin (j + 1) → X) :
      (if y (Fin.last j) = z then g.map j (fun l => N.coeff (y l.castSucc) (y l.succ))
        (pathMap N f i φ (y 0)) else 0) =
      ∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
        (if y (Fin.last j) = z then g.map j (fun l => N.coeff (y l.castSucc) (y l.succ))
          (f.map i (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))) else 0) else 0 := by
    split_ifs with hyz
    · simp only [pathMap_apply, map_sum]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    · simp
  rw [pathMap_apply, sum_congr rfl fun y _ => hy y, sum_comm,
    Fin.sum_sum_ite_apply_last_eq_apply_zero h]
  refine sum_congr rfl fun w _ => ?_
  have hlast : w ⟨i + (Fin.last j : ℕ), by simp; omega⟩ = w (Fin.last n) :=
    congrArg w (Fin.ext (by simp [h]))
  have hzero : w ⟨((0 : Fin (i + 1)) : ℕ), by simp⟩ = w 0 := congrArg w (Fin.ext (by simp))
  simp only [hlast, hzero, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]

/-- The path sum of length `n` of `g ∘ f` is the sum, over `i + j = n`, of the path sums of length
`j` of `g` applied to those of length `i` of `f`. -/
private theorem pathMap_comp_apply [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    (n : ℕ) (φ : X → M) (z : X) :
    pathMap N (g.comp f) n φ z =
      ∑ k ∈ range (n + 1), pathMap N g (n - k) (pathMap N f k φ) z := by
  rw [pathMap_apply, ← Fin.sum_univ_eq_sum_range (fun k => pathMap N g (n - k) (pathMap N f k φ) z)]
  symm
  refine (sum_congr rfl fun (k : Fin (n + 1)) _ => pathMap_pathMap_apply N g f
    (show (k : ℕ) + (n - k) = n by have := k.isLt; omega) φ z).trans ?_
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  split_ifs
  · simp [UngradedAInfinityRightModuleHom.comp_map_apply]
  · simp

/-- `T_{g ∘ f} = T_g ∘ T_f` when the path sums of `f` and `g` vanish from length `K` on and those
of `g ∘ f` from length `2 K` on. -/
private theorem typeABoxMapOfHom_comp_of_bound [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    {K : ℕ} (hf : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hg : ∀ n, K ≤ n → (g.cone.matrixAct X n fun _ => N.coeff) = 0)
    (hgf : ∀ n, 2 * K ≤ n → ((g.comp f).cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [typeABoxMapOfHom_eq_sum_pathMap N (g.comp f) hgf, LinearMap.comp_apply,
    typeABoxMapOfHom_eq_sum_pathMap N g hg, typeABoxMapOfHom_eq_sum_pathMap N f hf]
  simp only [LinearMap.sum_apply, Finset.sum_apply, map_sum, pathMap_comp_apply]
  -- Regroup the sum over `i + j < 2 K` as a sum over `i < 2 K` and `j < 2 K - i`; the terms with
  -- `i ≥ K` or `j ≥ K` vanish.
  rw [sum_range_diag_flip (2 * K) fun i j => pathMap N g j (pathMap N f i φ) z,
    ← sum_range_add_sum_Ico _ (show K ≤ 2 * K by omega),
    sum_eq_zero (s := Ico K (2 * K)) fun i hi => sum_eq_zero fun j _ => by
      simp [pathMap_eq_zero N f (hf i (by simp at hi; omega))], add_zero]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [← sum_range_add_sum_Ico _ (show K ≤ 2 * K - i by omega),
    sum_eq_zero (s := Ico K (2 * K - i)) fun j hj => by
      simp [pathMap_eq_zero N g (hg j (by simp at hj; omega))], add_zero]

/-- **The box tensor product is functorial in the type `A` module**, for a bounded type `D`
structure: over a ring of characteristic two, the map induced by a composite of morphisms of `A∞`
modules is the composite of the induced maps, `T_{g ∘ f} = T_g ∘ T_f`. -/
theorem typeABoxMapOfHom_comp_of_isBounded [CharP R 2] (N : TypeDStructure d ι X)
    (hN : N.IsBounded) (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  -- The iterates of `N` vanish from length `K` on, so do the path sums of every morphism.
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  exact N.typeABoxMapOfHom_comp_of_bound g f (K := K)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero f.cone (hK n hn) fun _ => Or.inl rfl)
    (fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero g.cone (hK n hn) fun _ => Or.inl rfl)
    fun n hn => N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero (g.comp f).cone (hK n (by omega))
      fun _ => Or.inl rfl

/-- **The box tensor product is functorial in the type `A` module**, for a type `D` structure with
a height: if a height on the generators strictly increases along every nonzero coefficient of `N`,
then `T_{g ∘ f} = T_g ∘ T_f`. -/
theorem typeABoxMapOfHom_comp_of_lt [CharP R 2] (N : TypeDStructure d ι X) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (g : UngradedAInfinityRightModuleHom Mm' Mm'')
    (f : UngradedAInfinityRightModuleHom Mm Mm') :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f :=
  N.typeABoxMapOfHom_comp_of_isBounded (N.isBounded_of_lt h hh) g f

/-- **The box tensor product is functorial in bounded type `A` modules**: if the operations of `M`,
`M'` and `M''` and the components of `f` and `g` vanish from arity `K` on, then
`T_{g ∘ f} = T_g ∘ T_f`, whatever the type `D` structure. -/
theorem typeABoxMapOfHom_comp_of_act_eq_zero [CharP R 2] (N : TypeDStructure d ι X)
    (g : UngradedAInfinityRightModuleHom Mm' Mm'') (f : UngradedAInfinityRightModuleHom Mm Mm')
    {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0) (hM' : ∀ n, K ≤ n → Mm'.act n = 0)
    (hM'' : ∀ n, K ≤ n → Mm''.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) :
    N.typeABoxMapOfHom (g.comp f) = N.typeABoxMapOfHom g ∘ₗ N.typeABoxMapOfHom f := by
  -- The components of `g ∘ f` vanish from arity `2 K` on: each term has `f_{i+1}` with `i ≥ K` or
  -- `g_{j+1}` with `j ≥ K`.
  have hgf (n : ℕ) (hn : 2 * K ≤ n) : (g.comp f).map n = 0 := by
    refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
    rw [UngradedAInfinityRightModuleHom.comp_map_apply]
    refine sum_eq_zero fun k _ => ?_
    by_cases hk : K ≤ (k : ℕ)
    · simp [hf k hk]
    · simp [hg (n - k) (by omega)]
  refine N.typeABoxMapOfHom_comp_of_bound g f (K := K) (fun n hn => ?_) (fun n hn => ?_)
    fun n hn => ?_
  · rw [f.cone.matrixAct_eq_zero_of_act_eq_zero X
      (f.cone_act_eq_zero (hM n hn) (hM' n hn) (hf n hn)), zero_apply]
  · rw [g.cone.matrixAct_eq_zero_of_act_eq_zero X
      (g.cone_act_eq_zero (hM' n hn) (hM'' n hn) (hg n hn)), zero_apply]
  · rw [(g.comp f).cone.matrixAct_eq_zero_of_act_eq_zero X ((g.comp f).cone_act_eq_zero
      (hM n (by omega)) (hM'' n (by omega)) (hgf n hn)), zero_apply]

end TypeDStructure

end TauCeti
