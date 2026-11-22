/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Range
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# The rank of a symmetric matrix bordered by a column and its transpose

Let `S` be a symmetric `n × n` matrix over a field `K`, let `v : n → K` and `a : K`, and let
`B = [[S, v], [vᵀ, a]]` be the symmetric matrix on `n ⊕ Unit` obtained by bordering `S` with the
column `v`, the row `vᵀ` and the corner `a`. The rank of `B` is determined as follows.

* If `v = S x` lies in the column range of `S`, then `rank B = rank S` when `a = x ⬝ᵥ S x`, and
  `rank B = rank S + 1` otherwise. The shear `(y, t) ↦ (y + t x, t)` identifies the kernel of `B`
  with `ker S × {t | (a - x ⬝ᵥ S x) t = 0}`.
* If `v` is not in the column range of `S`, then `rank B = rank S + 2` for every corner `a`: the
  kernel of `B` is the hyperplane of `ker S` cut out by `y ↦ v ⬝ᵥ y`, which is a nonzero
  functional on `ker S` because a vector lies in the range of a symmetric matrix exactly when it is
  orthogonal to its kernel.

The diagonal entry `a` is unrestricted and no division by two occurs, so these hold in every
characteristic, including for alternating matrices in characteristic two. They are the border step
of MacWilliams's count of symmetric matrices of each rank over a finite field.

## Main results

* `Matrix.IsSymm.mem_range_mulVecLin_iff`: `v` is in the range of a symmetric `S` if and only if
  `v ⬝ᵥ z = 0` for every `z` in the kernel of `S`.
* `Matrix.fromBlocks_replicateCol_replicateRow_mulVec`: the action of a bordered matrix.
* `Matrix.IsSymm.rank_fromBlocks_mulVec`: the rank of the border by a column `S x` in the range.
* `Matrix.IsSymm.rank_fromBlocks_of_notMem_range`: the rank of the border by a column outside the
  range.

## References

* R. P. Stanley, *Spanning trees and a conjecture of Kontsevich*, Ann. Comb. 2 (1998), 351–363,
  §4, First proof (J. MacWilliams), equations (4.2)–(4.3).
-/

public section

namespace Matrix

/-- The action of the matrix obtained by bordering `S` with the column `v`, the row `v` and the
corner `a`: it sends `w` to `(S y + t v, v ⬝ᵥ y + a t)`, where `y` and `t` are the restrictions of
`w` to `n` and to the extra index. -/
theorem fromBlocks_replicateCol_replicateRow_mulVec {R n : Type*} [CommSemiring R] [Fintype n]
    (S : Matrix n n R) (v : n → R) (a : R) (w : n ⊕ Unit → R) :
    fromBlocks S (replicateCol Unit v) (replicateRow Unit v) (of fun _ _ => a) *ᵥ w =
      Sum.elim (S *ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) • v)
        (fun _ => v ⬝ᵥ (w ∘ Sum.inl) + a * w (Sum.inr ())) := by
  ext (i | i) <;> simp [mulVec, dotProduct, mul_comm]

variable {K n : Type*} [Field K] [Fintype n] {S : Matrix n n K}

/-- A vector lies in the range of a symmetric matrix over a field if and only if it is orthogonal,
for the dot product, to the kernel. -/
theorem IsSymm.mem_range_mulVecLin_iff (hS : S.IsSymm) (v : n → K) :
    v ∈ LinearMap.range S.mulVecLin ↔ ∀ z ∈ LinearMap.ker S.mulVecLin, v ⬝ᵥ z = 0 := by
  simp_rw [mem_range_mulVecLin_iff_forall_vecMul_eq_zero, LinearMap.mem_ker, mulVecLin_apply,
    ← mulVec_transpose, hS.eq, dotProduct_comm v]

/-- Rank-nullity for a matrix on `n ⊕ Unit`. -/
private theorem rank_add_finrank_ker_sum_unit (B : Matrix (n ⊕ Unit) (n ⊕ Unit) K) :
    B.rank + Module.finrank K (LinearMap.ker B.mulVecLin) = Fintype.card n + 1 := by
  have h := B.rank_le_card_width
  rw [finrank_ker_mulVecLin, Fintype.card_sum, Fintype.card_unit] at *
  omega

/-- **Bordering a symmetric matrix by a column in its range.** If `S` is symmetric, bordering it by
the column `S x`, its transpose and the corner `a` keeps the rank when `a = x ⬝ᵥ S x` and raises it
by one otherwise. -/
theorem IsSymm.rank_fromBlocks_mulVec [DecidableEq K] (hS : S.IsSymm) (x : n → K) (a : K) :
    (Matrix.fromBlocks S (replicateCol Unit (S *ᵥ x)) (replicateRow Unit (S *ᵥ x))
      (of fun _ _ => a)).rank = S.rank + if a = x ⬝ᵥ S *ᵥ x then 0 else 1 := by
  set B := Matrix.fromBlocks S (replicateCol Unit (S *ᵥ x)) (replicateRow Unit (S *ᵥ x))
    (of fun _ _ => a)
  set c := a - x ⬝ᵥ S *ᵥ x
  -- The shear `(y, t) ↦ (y + t x, t)` carries `ker B` onto `ker S × {t | c t = 0}`.
  let Φ : (n ⊕ Unit → K) ≃ₗ[K] (n → K) × K :=
    { toFun w := (w ∘ Sum.inl + w (Sum.inr ()) • x, w (Sum.inr ()))
      invFun p := Sum.elim (p.1 - p.2 • x) fun _ => p.2
      map_add' w w' := by ext <;> simp [add_smul]; abel
      map_smul' r w := by ext <;> simp [smul_smul]
      left_inv w := by ext (i | i) <;> simp
      right_inv p := by ext <;> simp }
  have hmap : (LinearMap.ker B.mulVecLin).map (Φ : (n ⊕ Unit → K) →ₗ[K] (n → K) × K) =
      (LinearMap.ker S.mulVecLin).prod (LinearMap.ker (c • LinearMap.id)) := by
    ext ⟨y, t⟩
    rw [Submodule.mem_map_equiv, Submodule.mem_prod, LinearMap.mem_ker, LinearMap.mem_ker,
      LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply,
      fromBlocks_replicateCol_replicateRow_mulVec]
    simp only [Φ, LinearEquiv.coe_symm_mk', Sum.elim_comp_inl, Sum.elim_inr]
    rw [mulVec_sub, mulVec_smul, sub_add_cancel, ← Sum.elim_zero_zero, Sum.elim_eq_iff]
    refine and_congr_right fun hy => ?_
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm, ← hS.dotProduct_mulVec_comm, hy,
      dotProduct_zero, funext_iff]
    simp only [Pi.zero_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, c,
      dotProduct_comm x]
    exact ⟨fun h => by linear_combination h (), fun h _ => by linear_combination h⟩
  have hker := (Φ.ofSubmodules _ _ hmap).finrank_eq
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_ker_mulVecLin S] at hker
  have hc : Module.finrank K (LinearMap.ker (c • LinearMap.id : K →ₗ[K] K)) =
      if a = x ⬝ᵥ S *ᵥ x then 1 else 0 := by
    split_ifs with h
    · rw [show c = 0 from sub_eq_zero.mpr h, zero_smul, LinearMap.ker_zero, finrank_top,
        Module.finrank_self]
    · rw [LinearMap.ker_smul _ _ (sub_ne_zero.mpr h), LinearMap.ker_id, finrank_bot]
  have h1 := rank_add_finrank_ker_sum_unit B
  have h2 := S.rank_le_card_width
  rw [hc] at hker
  split_ifs at hker ⊢ <;> omega

/-- **Bordering a symmetric matrix by a column outside its range.** If `S` is symmetric and `v` is
not in its range, bordering `S` by the column `v`, its transpose and any corner raises the rank by
two. -/
theorem IsSymm.rank_fromBlocks_of_notMem_range (hS : S.IsSymm) {v : n → K}
    (hv : v ∉ LinearMap.range S.mulVecLin) (a : K) :
    (Matrix.fromBlocks S (replicateCol Unit v) (replicateRow Unit v) (of fun _ _ => a)).rank =
      S.rank + 2 := by
  classical
  set B := Matrix.fromBlocks S (replicateCol Unit v) (replicateRow Unit v) (of fun _ _ => a)
  set φ := dotProductEquiv K n v
  let Φ := (LinearEquiv.sumArrowLequivProdArrow n Unit K K).trans
    ((LinearEquiv.refl K (n → K)).prodCongr (LinearEquiv.funUnique Unit K K))
  -- A kernel vector of `B` has vanishing last coordinate, since `v` is not in the range of `S`.
  have hmap : (LinearMap.ker B.mulVecLin).map (Φ : (n ⊕ Unit → K) →ₗ[K] (n → K) × K) =
      (LinearMap.ker S.mulVecLin ⊓ LinearMap.ker φ).prod ⊥ := by
    ext ⟨y, t⟩
    have hΦ : Φ.symm (y, t) = Sum.elim y fun _ => t := by ext (i | i) <;> rfl
    rw [Submodule.mem_map_equiv, hΦ, Submodule.mem_prod, LinearMap.mem_ker, mulVecLin_apply,
      fromBlocks_replicateCol_replicateRow_mulVec, Sum.elim_comp_inl, Sum.elim_inr,
      ← Sum.elim_zero_zero, Sum.elim_eq_iff, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_bot, dotProductEquiv_apply_apply]
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨⟨h₁, h₂⟩, ht⟩ => ?_⟩
    · obtain rfl : t = 0 := by
        by_contra ht
        refine hv ⟨-t⁻¹ • y, ?_⟩
        rw [mulVecLin_apply, mulVec_smul, eq_add_neg_of_add_eq h₁]
        simp [smul_smul, ht]
      simpa using And.intro h₁ (congrFun h₂ ())
    · subst ht
      exact ⟨by simpa using h₁, funext fun _ => by simpa using h₂⟩
  -- The dot product with `v` is a nonzero functional on `ker S`, so it cuts out a hyperplane.
  obtain ⟨z, hz, hvz⟩ : ∃ z ∈ LinearMap.ker S.mulVecLin, v ⬝ᵥ z ≠ 0 := by
    by_contra! h
    exact hv ((hS.mem_range_mulVecLin_iff v).mpr h)
  have hψ : φ ∘ₗ (LinearMap.ker S.mulVecLin).subtype ≠ 0 :=
    fun h => hvz (by simpa [φ] using LinearMap.congr_fun h ⟨z, hz⟩)
  have hcodim := Module.Dual.finrank_ker_add_one_of_ne_zero hψ
  rw [LinearMap.ker_comp, ← top_inf_eq (Submodule.comap _ _),
    ← Submodule.comap_subtype_self (LinearMap.ker S.mulVecLin), ← Submodule.comap_inf,
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hcodim
  have hker := (Φ.ofSubmodules _ _ hmap).finrank_eq
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_bot, add_zero] at hker
  have h1 := rank_add_finrank_ker_sum_unit B
  have h2 := finrank_ker_mulVecLin S
  have h3 := S.rank_le_card_width
  omega

end Matrix
