/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Lie.ExteriorPower
import TauCeti.LinearAlgebra.Alternating.Alternatization
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation

/-!
# The Chevalley quantization map is antisymmetrization

When `2` is invertible, Mathlib's `CliffordAlgebra.equivExterior Q` identifies the Clifford algebra
of `Q` with the exterior algebra as modules. Its inverse is the *quantization map*
`⋀ M → CliffordAlgebra Q` of Chevalley. This file proves that the quantization map is
antisymmetrization: for vectors `v₀, …, vₖ₋₁`,

`k! • (equivExterior Q).symm (v₀ ∧ ⋯ ∧ vₖ₋₁) = ∑_{σ ∈ Sₖ} sign σ • v_{σ 0} ⋯ v_{σ (k-1)}`,

with the products on the right taken in the Clifford algebra. When `k!` is invertible this is the
normalized formula `σ(v₀ ∧ ⋯ ∧ vₖ₋₁) = (1/k!) ∑_σ sign σ • v_{σ 0} ⋯ v_{σ (k-1)}`. In degrees `0`
and `1` it says that the quantization map fixes scalars and vectors, and in degree `2` it is
`σ(x ∧ y) = ½ (x y - y x) = x y - B(x, y)` for the bilinear form `B = QuadraticMap.associated Q`
with `B(x, x) = Q x`.

The quantization map is also equivariant. A linear map of the Clifford algebra that obeys the
Leibniz rule and sends each vector `m` to `A m` (for instance the commutator with the quadratic lift
of a skew-adjoint `A`) acts on the quantization of `v₀ ∧ ⋯ ∧ vₖ₋₁` as the quantization of the
derivation `∑ⱼ v₀ ∧ ⋯ ∧ A vⱼ ∧ ⋯ ∧ vₖ₋₁`. So the quantization map intertwines such a map with any
Leibniz map of the exterior algebra extending `A`, and with `exteriorPower.lieMap k A` on
`⋀[R]^k M`.
For the adjoint representation of a Lie algebra with an invariant form, this is the equivariance
of the quantization map `⋀ 𝔤 → C(𝔤)` that carries invariant exterior forms to invariant Clifford
elements, as in Kostant's description of the Clifford algebra of a semisimple Lie algebra.

## Main results

* `CliffordAlgebra.equivExterior_sum_sign_smul_prod`: `equivExterior Q` sends the antisymmetrized
  Clifford product of `k` vectors to `k!` times their exterior product.
* `CliffordAlgebra.factorial_smul_equivExterior_symm_ιMulti`: the same statement for the
  quantization map `(equivExterior Q).symm`.
* `CliffordAlgebra.equivExterior_symm_ιMulti`: the normalized antisymmetrization formula, when
  `k!` is invertible.
* `CliffordAlgebra.equivExterior_symm_algebraMap`, `CliffordAlgebra.equivExterior_symm_ι` and
  `CliffordAlgebra.equivExterior_symm_ι_mul_ι`: the cases of degree `0`, `1` and `2`.
* `CliffordAlgebra.equivExterior_symm_ι_mul`: the quantization map on a left exterior factor,
  `σ(m ∧ x) = m σ(x) - σ(B(m, ·) ⌋ x)`.
* `CliffordAlgebra.map_equivExterior_symm_ιMulti` and
  `CliffordAlgebra.lie_equivExterior_symm_ιMulti`: equivariance for Leibniz maps and for
  commutators that preserve the vectors, on pure wedges.
* `CliffordAlgebra.map_equivExterior_symm` and `CliffordAlgebra.lie_equivExterior_symm`: the same
  equivariance on arbitrary elements of the exterior algebra, against a Leibniz map extending `A`.
* `CliffordAlgebra.map_equivExterior_symm_exteriorPower` and
  `CliffordAlgebra.lie_equivExterior_symm_exteriorPower`: the same equivariance on `⋀[R]^k M`,
  against `exteriorPower.lieMap k A`.

## Implementation notes

The proof never expands `equivExterior Q` on a product of `k` generators completely. By the
recursion `CliffordAlgebra.equivExterior_ι_mul`, the image of the product `v₀ ⋯ vₖ₋₁` is the
exterior product `v₀ ∧ ⋯ ∧ vₖ₋₁` plus a function of `v` that is a sum of functions each invariant
under a transposition of two of the vectors; each such function comes from a correction term
`B(vᵢ, vⱼ) • ⋯`, which is symmetric in `vᵢ` and `vⱼ` because `B` is. The alternating sum over
`Sₖ` kills every function invariant under a transposition, and multiplies the exterior product by
`k!`. Equivariance is proved by induction on the degree from `equivExterior_symm_ι_mul`, which needs
no invertibility of `k!`; the correction terms match because the Leibniz map makes `A`
skew-adjoint for `B`. It extends from pure wedges to `⋀ M` and to `⋀[R]^k M` because pure wedges
span them.

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

section TranspositionInvariant

variable {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- The span of the functions of `k` vectors that are invariant under some transposition of two
of their arguments. The alternating sum over `Sₖ` vanishes on it. -/
private def transpositionInvariantSpan (R M N : Type*) [CommRing R] [AddCommGroup N] [Module R N]
    (k : ℕ) : Submodule R ((Fin k → M) → N) :=
  Submodule.span R {F | ∃ i j : Fin k, i ≠ j ∧ ∀ v, F (v ∘ swap i j) = F v}

omit [AddCommGroup M] [Module R M] in
/-- The alternating sum over `Sₖ` of a function in `transpositionInvariantSpan` vanishes, by
`Equiv.Perm.sum_sign_smul_comp_eq_zero` on each spanning function. -/
private theorem sum_sign_smul_eq_zero {k : ℕ} {F : (Fin k → M) → N}
    (hF : F ∈ transpositionInvariantSpan R M N k) (v : Fin k → M) :
    ∑ σ : Perm (Fin k), Perm.sign σ • F (v ∘ σ) = 0 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i, j, hij, hF⟩ := hF
    exact Perm.sum_sign_smul_comp_eq_zero hij hF v
  | zero => simp
  | add F G _ _ hF hG => simp [Finset.sum_add_distrib, hF, hG]
  | smul r F _ hF =>
    calc ∑ σ : Perm (Fin k), Perm.sign σ • (r • F) (v ∘ σ)
        = r • ∑ σ : Perm (Fin k), Perm.sign σ • F (v ∘ σ) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun σ _ ↦ smul_comm _ _ _
      _ = 0 := by rw [hF, smul_zero]

/-- Feeding the first vector and a function of the remaining ones into a bilinear map preserves
`transpositionInvariantSpan`: invariance under `swap i j` becomes invariance under
`swap i.succ j.succ`. -/
private theorem bilin_tail_mem (G : M →ₗ[R] N →ₗ[R] N') {k : ℕ} {F : (Fin k → M) → N}
    (hF : F ∈ transpositionInvariantSpan R M N k) :
    (fun v : Fin (k + 1) → M ↦ G (v 0) (F (Fin.tail v))) ∈
      transpositionInvariantSpan R M N' (k + 1) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i, j, hij, hF⟩ := hF
    refine Submodule.subset_span ⟨i.succ, j.succ, (Fin.succ_injective _).ne hij, fun v ↦ ?_⟩
    have h0 : (v ∘ swap i.succ j.succ) 0 = v 0 := by
      rw [Function.comp_apply,
        swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
    have ht : Fin.tail (v ∘ swap i.succ j.succ) = Fin.tail v ∘ swap i j := by
      ext l
      simp [Fin.tail, (Fin.succ_injective _).swap_apply]
    simp only [h0, ht, hF]
  | zero =>
    convert (transpositionInvariantSpan R M N' (k + 1)).zero_mem using 1
    funext v
    simp
  | add F₁ F₂ _ _ h₁ h₂ =>
    convert add_mem h₁ h₂ using 1
    ext v
    simp
  | smul r F _ h =>
    convert Submodule.smul_mem _ r h using 1
    ext v
    simp

/-- Contracting the exterior product of the remaining vectors against the first, along a
symmetric bilinear form, lands in `transpositionInvariantSpan`: by
`TauCeti.ExteriorAlgebra.contractLeft_ιMulti` it is a sum of terms `± B(v₀, vᵢ₊₁) • ⋯`, each
invariant under `swap 0 i.succ`. -/
private theorem contractLeft_ιMulti_tail_mem (B : M →ₗ[R] Module.Dual R M)
    (hB : ∀ a b, B a b = B b a) (k : ℕ) :
    (fun v : Fin (k + 1) → M ↦ contractLeft (Q := (0 : QuadraticForm R M)) (B (v 0))
      (ExteriorAlgebra.ιMulti R k (Fin.tail v))) ∈
      transpositionInvariantSpan R M (ExteriorAlgebra R M) (k + 1) := by
  cases k with
  | zero =>
    convert (transpositionInvariantSpan R M (ExteriorAlgebra R M) 1).zero_mem using 1
    funext v
    simp
  | succ n =>
    have hsum : (fun v : Fin (n + 2) → M ↦ contractLeft (Q := (0 : QuadraticForm R M)) (B (v 0))
        (ExteriorAlgebra.ιMulti R (n + 1) (Fin.tail v))) =
        ∑ i : Fin (n + 1), fun v : Fin (n + 2) → M ↦ ((-1 : R) ^ (i : ℕ) * B (v 0) (v i.succ)) •
          ExteriorAlgebra.ιMulti R n (i.removeNth (Fin.tail v)) := by
      ext v
      rw [TauCeti.ExteriorAlgebra.contractLeft_ιMulti, Finset.sum_apply]
      rfl
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span
      ⟨0, i.succ, (Fin.succ_ne_zero i).symm, fun v ↦ ?_⟩
    have hrem : i.removeNth (Fin.tail (v ∘ swap 0 i.succ)) = i.removeNth (Fin.tail v) := by
      ext l
      have hl0 : (i.succAbove l).succ ≠ 0 := Fin.succ_ne_zero _
      have hli : (i.succAbove l).succ ≠ i.succ :=
        (Fin.succ_injective _).ne (Fin.succAbove_ne i l)
      simp [Fin.removeNth, Fin.tail, swap_apply_of_ne_of_ne hl0 hli]
    simp only [hrem, Function.comp_apply, swap_apply_left, swap_apply_right, hB (v i.succ)]

end TranspositionInvariant

variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- `equivExterior Q` sends the Clifford product of `k` vectors to their exterior product, up to a
function of the vectors in `transpositionInvariantSpan`. -/
private theorem equivExterior_prod_sub_ιMulti_mem (k : ℕ) :
    (fun v : Fin k → M ↦ equivExterior Q (List.ofFn fun i ↦ ι Q (v i)).prod -
      ExteriorAlgebra.ιMulti R k v) ∈
      transpositionInvariantSpan R M (ExteriorAlgebra R M) k := by
  induction k with
  | zero =>
    convert (transpositionInvariantSpan R M (ExteriorAlgebra R M) 0).zero_mem using 1
    funext v
    simp
  | succ k ih =>
    set B := QuadraticMap.associated (-Q)
    have hB : ∀ a b, B a b = B b a := QuadraticMap.associated_isSymm R (-Q)
    set s := fun v : Fin k → M ↦ equivExterior Q (List.ofFn fun i ↦ ι Q (v i)).prod -
      ExteriorAlgebra.ιMulti R k v
    have hmul := bilin_tail_mem (LinearMap.mul R (ExteriorAlgebra R M) ∘ₗ ExteriorAlgebra.ι R) ih
    have hcon := bilin_tail_mem
      (contractLeft (Q := (0 : QuadraticForm R M)) ∘ₗ B) ih
    have hι := contractLeft_ιMulti_tail_mem B hB k
    convert sub_mem (sub_mem hmul hcon) hι using 1
    ext v
    have hs : equivExterior Q (List.ofFn fun i ↦ ι Q (Fin.tail v i)).prod =
        s (Fin.tail v) + ExteriorAlgebra.ιMulti R k (Fin.tail v) := by
      simp [s]
    simp only [List.ofFn_succ, List.prod_cons, equivExterior_ι_mul,
      ExteriorAlgebra.ιMulti_succ_apply,
      Pi.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply']
    -- `List.ofFn_succ` and `ιMulti_succ_apply` write the tail as `v ∘ Fin.succ` and
    -- `Matrix.vecTail v`, both by definition `Fin.tail v`
    rw [show (fun i : Fin k ↦ ι Q (v i.succ)) = fun i ↦ ι Q (Fin.tail v i) from rfl, hs,
      show Matrix.vecTail v = Fin.tail v from rfl]
    simp only [mul_add, map_add]
    abel

/-- **`equivExterior Q` sends the antisymmetrized Clifford product of `k` vectors to `k!` times
their exterior product.** -/
theorem equivExterior_sum_sign_smul_prod (k : ℕ) (v : Fin k → M) :
    equivExterior Q (∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod) =
      k.factorial • ExteriorAlgebra.ιMulti R k v := by
  have h := sum_sign_smul_eq_zero (equivExterior_prod_sub_ιMulti_mem Q k) v
  simp only [Function.comp_apply, smul_sub, Finset.sum_sub_distrib, sub_eq_zero,
    AlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [map_sum, ← h]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- **The quantization map is antisymmetrization**, multiplied through by `k!`: the inverse of
`equivExterior Q` sends `k!` times the exterior product of `k` vectors to the alternating sum of
their Clifford products in all orders. -/
theorem factorial_smul_equivExterior_symm_ιMulti (k : ℕ) (v : Fin k → M) :
    k.factorial • (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v) =
      ∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod := by
  rw [← map_nsmul, ← equivExterior_sum_sign_smul_prod, LinearEquiv.symm_apply_apply]

/-- **The normalized antisymmetrization formula for the quantization map**: when `k!` is
invertible, the inverse of `equivExterior Q` sends `v₀ ∧ ⋯ ∧ vₖ₋₁` to
`(1/k!) ∑_σ sign σ • v_{σ 0} ⋯ v_{σ (k-1)}`. -/
theorem equivExterior_symm_ιMulti (k : ℕ) [Invertible (k.factorial : R)] (v : Fin k → M) :
    (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v) =
      ⅟(k.factorial : R) •
        ∑ σ : Perm (Fin k), Perm.sign σ • (List.ofFn fun i ↦ ι Q (v (σ i))).prod := by
  rw [← factorial_smul_equivExterior_symm_ιMulti, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]

/-- **The quantization map in degree two**: the inverse of `equivExterior Q` sends `x ∧ y` to
`x y - B(x, y)`, where `B = QuadraticMap.associated Q` is the bilinear form with `B(x, x) = Q x`. -/
theorem equivExterior_symm_ι_mul_ι (x y : M) :
    (equivExterior Q).symm (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) =
      ι Q x * ι Q y - algebraMap R (CliffordAlgebra Q) (QuadraticMap.associated Q x y) := by
  rw [equivExterior, changeFormEquiv_symm, changeFormEquiv_apply, changeForm_ι_mul_ι]
  simp

/-- **The quantization map in degree zero** fixes scalars. -/
theorem equivExterior_symm_algebraMap (r : R) :
    (equivExterior Q).symm (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap R (CliffordAlgebra Q) r := by
  rw [LinearEquiv.symm_apply_eq, equivExterior_algebraMap]

/-- **The quantization map in degree one** fixes vectors. -/
theorem equivExterior_symm_ι (m : M) :
    (equivExterior Q).symm (ExteriorAlgebra.ι R m) = ι Q m := by
  rw [LinearEquiv.symm_apply_eq, equivExterior_ι]

/-- **The quantization map on a left exterior factor**: `σ(m ∧ x) = m σ(x) - σ(B(m, ·) ⌋ x)`, where
`B = QuadraticMap.associated Q`. -/
theorem equivExterior_symm_ι_mul (m : M) (x : ExteriorAlgebra R M) :
    (equivExterior Q).symm (ExteriorAlgebra.ι R m * x) =
      ι Q m * (equivExterior Q).symm x -
        (equivExterior Q).symm (contractLeft (QuadraticMap.associated Q m) x) := by
  rw [LinearEquiv.symm_apply_eq, map_sub, equivExterior_ι_mul]
  simp only [LinearEquiv.apply_symm_apply, map_neg, LinearMap.neg_apply]
  abel

section Equivariance

variable {Q} {A : M →ₗ[R] M} {D : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q}

/-- A Leibniz map of the Clifford algebra sending each vector `m` to `A m` makes `A` skew-adjoint
for `QuadraticMap.associated Q`: it kills scalars, and so the scalar
`ι Q m * ι Q m' + ι Q m' * ι Q m`. -/
private theorem associated_map_add_associated_map (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hι : ∀ m, D (ι Q m) = ι Q (A m)) (m m' : M) :
    QuadraticMap.associated Q (A m) m' + QuadraticMap.associated Q m (A m') = 0 := by
  have h1 : D 1 = 0 := by simpa using hD 1 1
  have h : D (ι Q m * ι Q m' + ι Q m' * ι Q m) =
      D (algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q m m')) := by
    rw [ι_mul_ι_add_swap]
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero, map_add, hD, hD, hι, hι] at h
  have h' : algebraMap R (CliffordAlgebra Q)
      (QuadraticMap.polar Q (A m) m' + QuadraticMap.polar Q m (A m')) = 0 := by
    rw [map_add, ← ι_mul_ι_add_swap, ← ι_mul_ι_add_swap, ← h]
    abel
  rw [← map_zero (algebraMap R (CliffordAlgebra Q)), (algebraMap_injective Q).eq_iff] at h'
  simp only [QuadraticMap.polar] at h'
  simp only [QuadraticMap.associated_apply, ← smul_add]
  rw [h', smul_zero]

/-- The quantization of `v₀ ∧ ω` is `v₀ σ(ω) - σ(B(v₀, ·) ⌋ ω)`, with the contraction expanded
over the factors of `ω` by `TauCeti.ExteriorAlgebra.contractLeft_ιMulti`. -/
private theorem equivExterior_symm_ιMulti_add_two {n : ℕ} (w : Fin (n + 2) → M) :
    (equivExterior Q).symm (ExteriorAlgebra.ιMulti R (n + 2) w) =
      ι Q (w 0) * (equivExterior Q).symm (ExteriorAlgebra.ιMulti R (n + 1) (Fin.tail w)) -
        ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * QuadraticMap.associated Q (w 0) (Fin.tail w i)) •
          (equivExterior Q).symm (ExteriorAlgebra.ιMulti R n (i.removeNth (Fin.tail w))) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, equivExterior_symm_ι_mul,
    TauCeti.ExteriorAlgebra.contractLeft_ιMulti, map_sum]
  simp only [map_smul]
  -- `ιMulti_succ_apply` writes the tail as `Matrix.vecTail w`, by definition `Fin.tail w`
  rfl

/-- **The quantization map is equivariant for derivations**: if a linear map `D` of the Clifford
algebra obeys the Leibniz rule and sends each vector `m` to `A m`, then `D` applied to the
quantization of `v₀ ∧ ⋯ ∧ vₖ₋₁` is the quantization of `∑ⱼ v₀ ∧ ⋯ ∧ A vⱼ ∧ ⋯ ∧ vₖ₋₁`, the
derivation of the exterior algebra extending `A`. -/
theorem map_equivExterior_symm_ιMulti (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hι : ∀ m, D (ι Q m) = ι Q (A m)) (k : ℕ) (v : Fin k → M) :
    D ((equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v)) =
      ∑ j, (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k (Function.update v j (A (v j)))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  match k, ih, v with
  | 0, _, v =>
    simpa using hD 1 1
  | 1, _, v =>
    simp [hι]
  | n + 2, ih, v =>
    have hrec := equivExterior_symm_ιMulti_add_two (Q := Q) (n := n)
    set B := QuadraticMap.associated Q
    have ih₁ : D ((equivExterior Q).symm (ExteriorAlgebra.ιMulti R (n + 1) (Fin.tail v))) =
        ∑ j, (equivExterior Q).symm (ExteriorAlgebra.ιMulti R (n + 1)
          (Function.update (Fin.tail v) j (A (v j.succ)))) :=
      ih (n + 1) (by omega) (Fin.tail v)
    have ih₀ := ih n (by omega)
    have hskew (i : Fin (n + 1)) : B (A (v 0)) (Fin.tail v i) = -B (v 0) (A (Fin.tail v i)) :=
      eq_neg_of_add_eq_zero_left (associated_map_add_associated_map hD hι _ _)
    have h0 (j : Fin (n + 1)) (x : M) : Function.update v j.succ x 0 = v 0 :=
      Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
    -- the correction terms in which `A` acts on a later vector `vⱼ₊₁`: those with `j = i` cancel
    -- the correction terms in which `A` acts on `v₀`, by skewness, and the others are the
    -- derivation of the contracted terms
    have hcorr : ∑ j : Fin (n + 1), ∑ i : Fin (n + 1),
        ((-1 : R) ^ (i : ℕ) * B (v 0) (Function.update (Fin.tail v) j (A (v j.succ)) i)) •
          (equivExterior Q).symm (ExteriorAlgebra.ιMulti R n
            (i.removeNth (Function.update (Fin.tail v) j (A (v j.succ))))) =
        ∑ i : Fin (n + 1), (((-1 : R) ^ (i : ℕ) * B (v 0) (A (Fin.tail v i))) •
            (equivExterior Q).symm (ExteriorAlgebra.ιMulti R n (i.removeNth (Fin.tail v))) +
          ((-1 : R) ^ (i : ℕ) * B (v 0) (Fin.tail v i)) •
            ∑ l, (equivExterior Q).symm (ExteriorAlgebra.ιMulti R n (Function.update
              (i.removeNth (Fin.tail v)) l (A (i.removeNth (Fin.tail v) l))))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Fin.sum_univ_succAbove _ i, Finset.smul_sum]
      simp [Fin.tail, Fin.removeNth]
    rw [hrec]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [hrec, map_sub, hD, hι, map_sum, map_smul, ih₁, ih₀, Function.update_self,
      Fin.tail_update_zero, Fin.tail_update_succ, h0, hskew, Finset.sum_sub_distrib,
      Finset.mul_sum, hcorr, Finset.sum_add_distrib, mul_neg, neg_smul, Finset.sum_neg_distrib]
    abel

omit [Invertible (2 : R)] in
/-- The commutator with `c` as the linear map `mulLeft c - mulRight c`. -/
private theorem lie_eq_mulLeft_sub_mulRight (c x : CliffordAlgebra Q) :
    ⁅c, x⁆ = (LinearMap.mulLeft R c - LinearMap.mulRight R c) x := by
  rw [Ring.lie_def]
  rfl

omit [Invertible (2 : R)] in
/-- The commutator with `c` obeys the Leibniz rule. -/
private theorem mulLeft_sub_mulRight_mul (c x y : CliffordAlgebra Q) :
    (LinearMap.mulLeft R c - LinearMap.mulRight R c) (x * y) =
      (LinearMap.mulLeft R c - LinearMap.mulRight R c) x * y +
        x * (LinearMap.mulLeft R c - LinearMap.mulRight R c) y := by
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_sub,
    sub_mul, mul_assoc]
  abel

/-- **The quantization map is equivariant for commutators**: if the commutator with `c` sends each
vector `m` to `A m`, then the commutator of `c` with the quantization of `v₀ ∧ ⋯ ∧ vₖ₋₁` is the
quantization of `∑ⱼ v₀ ∧ ⋯ ∧ A vⱼ ∧ ⋯ ∧ vₖ₋₁`. This applies to the quadratic lift of an orthogonal
Lie algebra, and so to the adjoint representation of a Lie algebra with an invariant form. -/
theorem lie_equivExterior_symm_ιMulti {c : CliffordAlgebra Q} (hc : ∀ m, ⁅c, ι Q m⁆ = ι Q (A m))
    (k : ℕ) (v : Fin k → M) :
    ⁅c, (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k v)⁆ =
      ∑ j, (equivExterior Q).symm (ExteriorAlgebra.ιMulti R k (Function.update v j (A (v j)))) := by
  rw [lie_eq_mulLeft_sub_mulRight]
  exact map_equivExterior_symm_ιMulti (mulLeft_sub_mulRight_mul c)
    (fun m ↦ by rw [← lie_eq_mulLeft_sub_mulRight, hc]) k v

/-- **The quantization map intertwines derivations**: if a linear map `D` of the Clifford algebra
and a linear map `d` of the exterior algebra both obey the Leibniz rule and send each vector `m` to
`A m`, then `D ∘ σ = σ ∘ d` for the quantization map `σ = (equivExterior Q).symm`. -/
theorem map_equivExterior_symm (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hι : ∀ m, D (ι Q m) = ι Q (A m)) {d : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M}
    (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (hdι : ∀ m, d (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (A m)) (x : ExteriorAlgebra R M) :
    D ((equivExterior Q).symm x) = (equivExterior Q).symm (d x) := by
  have h : D ∘ₗ (equivExterior Q).symm.toLinearMap = (equivExterior Q).symm.toLinearMap ∘ₗ d :=
    LinearMap.ext_on_range (ExteriorAlgebra.ιMulti_span R M) fun ⟨k, v⟩ ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_equivExterior_symm_ιMulti hD hι,
        ExteriorAlgebra.map_ιMulti_of_leibniz hd hdι, map_sum]
  exact LinearMap.congr_fun h x

/-- **The quantization map intertwines commutators with derivations**: if the commutator with `c`
sends each vector `m` to `A m`, and a linear map `d` of the exterior algebra obeys the Leibniz rule
and sends each vector `m` to `A m`, then `⁅c, σ x⁆ = σ (d x)` for the quantization map
`σ = (equivExterior Q).symm`. -/
theorem lie_equivExterior_symm {c : CliffordAlgebra Q} (hc : ∀ m, ⁅c, ι Q m⁆ = ι Q (A m))
    {d : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M} (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (hdι : ∀ m, d (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (A m)) (x : ExteriorAlgebra R M) :
    ⁅c, (equivExterior Q).symm x⁆ = (equivExterior Q).symm (d x) := by
  rw [lie_eq_mulLeft_sub_mulRight]
  exact map_equivExterior_symm (mulLeft_sub_mulRight_mul c)
    (fun m ↦ by rw [← lie_eq_mulLeft_sub_mulRight, hc]) hd hdι x

/-- **The quantization map is equivariant on exterior powers**: if a linear map `D` of the
Clifford algebra obeys the Leibniz rule and sends each vector `m` to `A m`, then on `⋀[R]^k M` it
intertwines `D` with the action `exteriorPower.lieMap k A` of `A`. -/
theorem map_equivExterior_symm_exteriorPower (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hι : ∀ m, D (ι Q m) = ι Q (A m)) {k : ℕ} (x : ⋀[R]^k M) :
    D ((equivExterior Q).symm x) = (equivExterior Q).symm (exteriorPower.lieMap k A x) := by
  have h : D ∘ₗ (equivExterior Q).symm.toLinearMap ∘ₗ (⋀[R]^k M).subtype =
      (equivExterior Q).symm.toLinearMap ∘ₗ (⋀[R]^k M).subtype ∘ₗ exteriorPower.lieMap k A :=
    LinearMap.ext_on_range (exteriorPower.ιMulti_span R k M) fun v ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
        exteriorPower.ιMulti_apply_coe, map_equivExterior_symm_ιMulti hD hι,
        exteriorPower.lieMap_apply_ιMulti, map_sum]
  exact LinearMap.congr_fun h x

/-- **The quantization map is equivariant for commutators on exterior powers**: if the commutator
with `c` sends each vector `m` to `A m`, then on `⋀[R]^k M` the commutator with `c` corresponds to
the action `exteriorPower.lieMap k A` of `A`. -/
theorem lie_equivExterior_symm_exteriorPower {c : CliffordAlgebra Q}
    (hc : ∀ m, ⁅c, ι Q m⁆ = ι Q (A m)) {k : ℕ} (x : ⋀[R]^k M) :
    ⁅c, (equivExterior Q).symm x⁆ = (equivExterior Q).symm (exteriorPower.lieMap k A x) := by
  rw [lie_eq_mulLeft_sub_mulRight]
  exact map_equivExterior_symm_exteriorPower (mulLeft_sub_mulRight_mul c)
    (fun m ↦ by rw [← lie_eq_mulLeft_sub_mulRight, hc]) x

end Equivariance

end CliffordAlgebra
