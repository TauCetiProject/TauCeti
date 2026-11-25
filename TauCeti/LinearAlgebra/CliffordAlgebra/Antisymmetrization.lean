/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.ExteriorAlgebra.CliffordAction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The Chevalley quantization map is antisymmetrization

When `2` is invertible, Mathlib's `CliffordAlgebra.equivExterior Q` identifies the Clifford algebra
of `Q` with the exterior algebra as modules. Its inverse is the *quantization map*
`σ : ⋀ M → CliffordAlgebra Q` of Chevalley. This file proves that the quantization map is
antisymmetrization: for vectors `v₀, …, vₖ₋₁`,

`k! • σ(v₀ ∧ ⋯ ∧ vₖ₋₁) = ∑_{π ∈ Sₖ} sign π • v_{π 0} ⋯ v_{π (k-1)}`,

with the products on the right taken in the Clifford algebra. When `k!` is invertible this is the
normalized formula `σ(v₀ ∧ ⋯ ∧ vₖ₋₁) = (1/k!) ∑_π sign π • v_{π 0} ⋯ v_{π (k-1)}`.

The cases of low degree are recorded beside the corresponding equations for `equivExterior`: the
quantization map fixes scalars (`CliffordAlgebra.equivExterior_symm_algebraMap`) and vectors
(`CliffordAlgebra.equivExterior_symm_ι`), and sends `x ∧ y` to `½ (x y - y x) = x y - B(x, y)`
for the bilinear form `B = QuadraticMap.associated Q` with `B(x, x) = Q x`
(`CliffordAlgebra.equivExterior_symm_ι_mul_ι`). So `σ(x ∧ x) = 0` while `x x = Q x`, and the
quantization map is not multiplicative as soon as `Q x ≠ 0` for some `x`.

This is the form of the quantization map `⋀ 𝔤 → C(𝔤)` used in Kostant's description of the
Clifford algebra of a semisimple Lie algebra, where the quantizations of invariant exterior forms
generate the invariant Clifford elements.

## Main results

* `CliffordAlgebra.equivExterior_sum_sign_smul_prod`: `equivExterior Q` sends the antisymmetrized
  Clifford product of `k` vectors to `k!` times their exterior product.
* `CliffordAlgebra.factorial_smul_equivExterior_symm_ιMulti`: the same statement for the
  quantization map `(equivExterior Q).symm`.
* `CliffordAlgebra.equivExterior_symm_ιMulti`: the normalized antisymmetrization formula, when
  `k!` is invertible.

## Implementation notes

The proof never expands `equivExterior Q` on a product of `k` generators completely. A vector `m`
acts on the exterior algebra, through `CliffordAlgebra.exteriorAction`, by `ω ↦ m ∧ ω - B'(m) ⌋ ω`
with `B' = QuadraticMap.associated (-Q)`, and `equivExterior Q` intertwines it with left
multiplication. So the difference between the image of the Clifford product `v₀ ⋯ vₖ₋₁` and the
exterior product `v₀ ∧ ⋯ ∧ vₖ₋₁` is the action of `v₀` on the same difference for `v₁, …, vₖ₋₁`,
minus the contraction of `v₁ ∧ ⋯ ∧ vₖ₋₁` against `B'(v₀, ·)`. Expanding the signed sum over `Sₖ`
along the vector placed first (`TauCeti.sum_sign_smul_comp_eq_sum_cons_removeNth`) shows by
induction that the first part has vanishing signed sum, and the contraction has vanishing signed
sum because `B'` is symmetric
(`TauCeti.ExteriorAlgebra.sum_sign_smul_contractLeft_ιMulti_tail_eq_zero`). The signed sum of the
exterior products themselves is the alternatization of the alternating map `ExteriorAlgebra.ιMulti`,
which is `k!` times that map (`AlternatingMap.coe_alternatization`).

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* E. Meinrenken, *Clifford Algebras in Lie Theory*, Ergebnisse der Mathematik 58 (2013), §2.2.
* B. Kostant, *Clifford algebra analogue of the Hopf–Koszul–Samelson theorem, the ρ-decomposition
  C(𝔤) = End V_ρ ⊗ C(P), and the 𝔤-module structure of ⋀𝔤*, Adv. Math. 125 (1997).
-/

public section

open Equiv

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The difference between `equivExterior Q` of the Clifford product of `k` vectors and their
exterior product has vanishing signed sum over the permutations of the vectors. -/
private theorem sum_sign_smul_equivExterior_prod_sub_ιMulti (k : ℕ) (v : Fin k → M) :
    ∑ σ : Perm (Fin k), Perm.sign σ • (equivExterior Q (List.ofFn fun i ↦ ι Q ((v ∘ σ) i)).prod -
      ExteriorAlgebra.ιMulti R k (v ∘ σ)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- peel off the first vector: the difference in `k + 1` vectors is the action of the first
    -- vector on the difference in the last `k`, minus a contraction
    have hD (w : Fin (k + 1) → M) :
        equivExterior Q (List.ofFn fun i ↦ ι Q (w i)).prod - ExteriorAlgebra.ιMulti R (k + 1) w =
          exteriorAction Q (ι Q (w 0))
            (equivExterior Q (List.ofFn fun i ↦ ι Q (Fin.tail w i)).prod -
              ExteriorAlgebra.ιMulti R k (Fin.tail w)) -
          contractLeft (Q := (0 : QuadraticForm R M)) (QuadraticMap.associated (-Q) (w 0))
            (ExteriorAlgebra.ιMulti R k (Fin.tail w)) := by
      -- `Matrix.vecTail` and `Fin.tail` are both `fun i ↦ w i.succ` by definition
      have htail : Matrix.vecTail w = Fin.tail w := (rfl)
      have hprod : (List.ofFn fun i ↦ ι Q (w i)).prod =
          ι Q (w 0) * (List.ofFn fun i ↦ ι Q (Fin.tail w i)).prod := by
        rw [List.ofFn_succ, List.prod_cons, Fin.tail_def]
      rw [hprod, ← exteriorAction_equivExterior, ExteriorAlgebra.ιMulti_succ_apply, htail, map_sub,
        exteriorAction_ι Q (w 0) (ExteriorAlgebra.ιMulti R k (Fin.tail w))]
      abel
    simp_rw [hD, smul_sub, Finset.sum_sub_distrib]
    rw [TauCeti.ExteriorAlgebra.sum_sign_smul_contractLeft_ιMulti_tail_eq_zero _
      (QuadraticMap.associated_isSymm R (-Q)) k v, sub_zero,
      TauCeti.sum_sign_smul_comp_eq_sum_cons_removeNth (fun u ↦ exteriorAction Q (ι Q (u 0))
        (equivExterior Q (List.ofFn fun i ↦ ι Q (Fin.tail u i)).prod -
          ExteriorAlgebra.ιMulti R k (Fin.tail u)))]
    -- after moving `v j` to the front, the remaining vectors are permuted by `Sₖ`
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [Fin.cons_zero, Fin.tail_cons, ← map_zsmul_unit, ← map_sum, ih, map_zero,
      smul_zero]

/-- **`equivExterior Q` sends the antisymmetrized Clifford product of `k` vectors to `k!` times
their exterior product.** -/
theorem equivExterior_sum_sign_smul_prod (k : ℕ) (v : Fin k → M) :
    equivExterior Q (∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod) =
      k.factorial • ExteriorAlgebra.ιMulti R k v := by
  -- the signed sum of the exterior products is the alternatization of `ExteriorAlgebra.ιMulti`
  have halt := DFunLike.congr_fun (AlternatingMap.coe_alternatization (ExteriorAlgebra.ιMulti R k
    (M := M))) v
  rw [MultilinearMap.alternatization_apply, Fintype.card_fin] at halt
  simp only [MultilinearMap.domDomCongr_apply, AlternatingMap.coe_multilinearMap,
    smul_apply] at halt
  have h := sum_sign_smul_equivExterior_prod_sub_ιMulti Q k v
  rw [← halt, ← sub_eq_zero, map_sum, ← Finset.sum_sub_distrib]
  simpa only [map_zsmul_unit, smul_sub, Function.comp_def] using h

/-- **The quantization map is antisymmetrization**, multiplied through by `k!`: the inverse of
`equivExterior Q` sends `k!` times the exterior product of `k` vectors to the alternating sum of
their Clifford products in all orders. -/
theorem factorial_smul_equivExterior_symm_ιMulti (k : ℕ) (v : Fin k → M) :
    k.factorial • (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v) =
      ∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod := by
  rw [← map_nsmul, ← equivExterior_sum_sign_smul_prod, LinearEquiv.symm_apply_apply]

/-- **The normalized antisymmetrization formula for the quantization map**: when `k!` is
invertible, the inverse of `equivExterior Q` sends `v₀ ∧ ⋯ ∧ vₖ₋₁` to
`(1/k!) ∑_π sign π • v_{π 0} ⋯ v_{π (k-1)}`. -/
theorem equivExterior_symm_ιMulti (k : ℕ) [Invertible (k.factorial : R)] (v : Fin k → M) :
    (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v) =
      ⅟(k.factorial : R) •
        ∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod := by
  rw [← factorial_smul_equivExterior_symm_ιMulti, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]

end CliffordAlgebra
