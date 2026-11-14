/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Polynomial
public import TauCeti.Algebra.TypeAHeckeAlgebra.TraceRadical
public import TauCeti.KnotTheory.Jimbo.StrandInclusion

import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The Turaev–Jimbo weighted trace on the type-A Hecke algebra

Turaev's diagonal enhancement `TauCeti.KnotTheory.jimboEnhancement` commutes with every operator in
the `N`-colour Jimbo representation `TauCeti.TypeAHeckeAlgebra.jimbo (Fin N) q` on the q-tensor
space `(Fin n → Fin N) →₀ R`. Taking the `R`-linear trace against this enhancement defines a linear
functional `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace N q n` on the finite type-A Hecke algebra
on `n` strands, over an arbitrary commutative ring `R` and with no invertibility assumption on the
quantum dimension `δ_N = ∑ a : Fin N, jimboWeight q a` or on `q - q⁻¹`.

Composed with `TauCeti.TypeAHeckeAlgebra.braidHom`, this algebra functional recovers the braid-group
functional `TauCeti.KnotTheory.jimboWeightedTrace` (`jimboWeightedTrace_braidHom`). Beyond the image
of the braid group, it satisfies the full Hecke-algebra Markov laws: it is tracial, adding an
uncrossed strand multiplies it by `δ_N`, multiplying by the positive crossing `T (Fin.last n)`
multiplies it by `q ^ N`, and multiplying by `(T (Fin.last n))⁻¹` multiplies it by `q⁻¹ ^ N`.

Consequently, on `n + 1` strands `jimboWeightedTrace N q (n + 1)` unconditionally equals `δ_N`
times the degree-`n` homogenized Ocneanu trace at `(q ^ N, δ_N)`
(`jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace`), even when `δ_N` is zero or a zero divisor.
Whenever `c * δ_N = 1`, rescaling by `c ^ n` identifies the tower with the Ocneanu trace at Markov
parameter `c * q ^ N` (`mul_pow_jimboWeightedTrace_eq_ocneanuTrace`), and the kernel of the
`N`-colour Jimbo representation is contained in the finite trace radical of that Ocneanu trace
(`ker_jimbo_le_finiteRadical_ocneanuTrace`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace`: the `N`-colour Turaev–Jimbo weighted trace on
  `TauCeti.TypeAHeckeAlgebra R q n`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_mapDomain_snoc`: intertwining of `jimbo` with
  `strandIncl` and appending a fixed colour.
* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`: Turaev's enhancement commutes with
  the entire Hecke-algebra action.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last`, and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last`: uncrossed-strand
  and positive/negative crossing contractions on the Hecke algebra.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace`: unconditional
  factorization through `homogenizedOcneanuTrace` over any commutative ring.
* `TauCeti.TypeAHeckeAlgebra.mul_pow_jimboWeightedTrace_eq_ocneanuTrace` and
  `TauCeti.TypeAHeckeAlgebra.ker_jimbo_le_finiteRadical_ocneanuTrace`: normalized comparison with
  `ocneanuTrace` and inclusion of the Jimbo representation kernel in the finite trace radical.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Finsupp Function
open scoped BigOperators

namespace TauCeti.TypeAHeckeAlgebra

section Intertwining

variable {R : Type*} [CommRing R] (ι : Type*) [LinearOrder ι] (q : Rˣ) {n : ℕ}

/-- A map of type-A Hecke algebras and a linear map of word spaces which intertwine the Jimbo
representations on every generator intertwine them on every element. -/
theorem jimbo_comp_eq_of_forall_T {m : ℕ}
    (f : TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra R q m)
    (L : ((Fin n → ι) →₀ R) →ₗ[R] (Fin m → ι) →₀ R)
    (h : ∀ i, (jimbo ι q (f (T q i))).comp L = L.comp (jimbo ι q (T q i)))
    (x : TypeAHeckeAlgebra R q n) :
    (jimbo ι q (f x)).comp L = L.comp (jimbo ι q x) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact h i
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact LinearMap.ext fun v ↦ by simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]

/-- The action of a Hecke-algebra element after adding an uncrossed last strand is its original
action with the last colour held fixed. -/
@[simp]
theorem jimbo_strandIncl_mapDomain_snoc (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.snoc w a : Fin (n + 1) → ι))
  suffices h : (jimbo ι q (strandIncl R q n x)).comp L = L.comp (jimbo ι q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine jimbo_comp_eq_of_forall_T ι q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).castSucc := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).castSucc := Fin.ext (by simp)
  rw [strandIncl_T, jimbo_T, jimbo_T, hj, hk]
  exact KnotTheory.jimboGenerator_comp_lmapDomain_snoc q _ _ a

/-- Adding an uncrossed last strand preserves matrix coefficients within each block of words with a
fixed last colour and gives zero between blocks with different last colours. -/
theorem jimbo_strandIncl_single_snoc_apply_snoc (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) 1) (Fin.snoc u d) =
      if a = d then jimbo ι q x (single w 1) u else 0 := by
  classical
  have h := jimbo_strandIncl_mapDomain_snoc ι q x a (single w 1)
  rw [mapDomain_single] at h
  rw [h]
  by_cases had : a = d
  · subst d
    simp only [↓reduceIte]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · simp only [had, ↓reduceIte]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply had
    simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z (Fin.last n)) hv

end Intertwining

section WeightedTrace

variable {R : Type*} [CommRing R]

/-- Turaev's tensor-power enhancement commutes with every element of the Hecke algebra in the
`N`-colour Jimbo representation. -/
theorem commute_jimboEnhancement_jimbo (N : ℕ) (q : Rˣ) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    Commute (KnotTheory.jimboEnhancement (N := N) q) (jimbo (Fin N) q x) := by
  have hx : jimbo (Fin N) q x ∈
      Algebra.adjoin R (Set.range (jimbo (Fin N) q ∘ T (n := n) q)) := by
    rw [Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_T]
    exact ⟨x, trivial, rfl⟩
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
  rintro _ ⟨i, rfl⟩
  simpa only [Function.comp_apply, jimbo_T] using
    KnotTheory.jimboEnhancement_commute_generator (N := N) q
      (BraidGroup.strand i) (BraidGroup.strandSucc i)

/-- **The Turaev–Jimbo weighted trace** on the finite type-A Hecke algebra on `n` strands with `N`
colours: `x ↦ tr (ρ_N(x) * μ^{⊗ n})`. Defined over any commutative ring with no division by the
quantum dimension or by `q - q⁻¹`. -/
noncomputable def jimboWeightedTrace (N : ℕ) (q : Rˣ) (n : ℕ) : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R) ∘ₗ
    LinearMap.mulRight R (KnotTheory.jimboEnhancement q) ∘ₗ (jimbo (Fin N) q).toLinearMap

/-- Unfold `jimboWeightedTrace` to the linear trace against `jimboEnhancement`. -/
theorem jimboWeightedTrace_apply (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q) :=
  (rfl)

/-- On the image of a braid under `braidHom`, the algebra weighted trace agrees with the braid
weighted trace `TauCeti.KnotTheory.jimboWeightedTrace`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (N : ℕ) (q : Rˣ) {n : ℕ} (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b : TypeAHeckeAlgebra R q n) =
      KnotTheory.jimboWeightedTrace (N := N) q b := by
  simp [jimboWeightedTrace_apply, KnotTheory.jimboWeightedTrace_def]

/-- The Turaev–Jimbo weighted trace is tracial on `TypeAHeckeAlgebra R q n`. -/
theorem jimboWeightedTrace_mul_comm (N : ℕ) (q : Rˣ) {n : ℕ} (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  rw [jimboWeightedTrace_apply, jimboWeightedTrace_apply,
    map_mul (jimbo (Fin N) q) x y, map_mul (jimbo (Fin N) q) y x, mul_assoc,
    ← (commute_jimboEnhancement_jimbo N q y).eq, ← mul_assoc, LinearMap.trace_mul_comm, mul_assoc]

/-- Expansion of `jimboWeightedTrace` in the canonical word basis. -/
theorem jimboWeightedTrace_eq_sum (N : ℕ) (q : Rˣ) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      ∑ w : Fin n → Fin N,
        jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    mul_apply_eq_comp, Finsupp.coe_basisSingleOne, KnotTheory.jimboEnhancement_single_one, map_smul]
  simp [mul_comm]

/-- On `1`, the `N`-colour weighted trace on `n` strands is the `n`-th power of the quantum
dimension. -/
@[simp]
theorem jimboWeightedTrace_one (N : ℕ) (q : Rˣ) (n : ℕ) :
    jimboWeightedTrace N q n 1 = (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  rw [← Units.val_one, ← map_one (braidHom R q n), jimboWeightedTrace_braidHom,
    KnotTheory.jimboWeightedTrace_one]

/-- On a scalar `r`, the `N`-colour weighted trace on `n` strands is `r` times the `n`-th power of
the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_algebraMap (N : ℕ) (q : Rˣ) (n : ℕ) (r : R) :
    jimboWeightedTrace N q n (algebraMap R _ r) =
      r * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, jimboWeightedTrace_one, smul_eq_mul]

/-- Adding an uncrossed strand multiplies `jimboWeightedTrace` by the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_strandIncl (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_single_snoc_apply_snoc, ↓reduceIte]
  have hweight (w : Fin n → Fin N) (a : Fin N) :
      (∏ i : Fin (n + 1), KnotTheory.jimboWeight q ((Fin.snoc w a : Fin (n + 1) → Fin N) i)) =
        (∏ i, KnotTheory.jimboWeight q (w i)) * KnotTheory.jimboWeight q a := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp only [hweight]
  rw [jimboWeightedTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ ↦ by ring

private theorem jimbo_strandIncl_mul_T_last_diagonal (N : ℕ) (q : Rˣ) {n : ℕ}
    (x : TypeAHeckeAlgebra R q (n + 1)) (w : Fin (n + 1) → Fin N) (c : Fin N) :
    jimbo (Fin N) q (strandIncl R q (n + 1) x * T q (Fin.last n))
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      jimbo (Fin N) q x (single w 1) w *
        (KnotTheory.jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
          ![w (Fin.last n), c] := by
  classical
  have hj : BraidGroup.strand (Fin.last n : Fin (n + 2 - 1)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n : Fin (n + 2 - 1)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
      Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
    rw [Equiv.comp_swap_eq_update]
    simp [← Fin.snoc_update, Fin.update_snoc_last]
  have hswap₂ : (![w (Fin.last n), c] : Fin 2 → Fin N) ∘ Equiv.swap 0 1 =
      ![c, w (Fin.last n)] := by
    ext i
    fin_cases i <;> simp
  have hpair : (![c, w (Fin.last n)] : Fin 2 → Fin N) = ![w (Fin.last n), c] ↔
      w (Fin.last n) = c := by
    simp [funext_iff, Fin.forall_fin_two, eq_comm]
  simp only [map_mul, mul_apply_eq_comp, jimbo_T, hj, hk,
    KnotTheory.jimboGenerator_single_one, Fin.snoc_castSucc, Fin.snoc_last,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, hswap, hswap₂,
      jimbo_strandIncl_single_snoc_apply_snoc, single_apply, hpair, mul_zero]
  · simp only [h, ↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      jimbo_strandIncl_single_snoc_apply_snoc, single_eq_same, mul_one, mul_comm]
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, hswap, hswap₂, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, zero_add, mul_one, mul_comm]

/-- Multiplying an included `(n + 1)`-strand element by the positive crossing `T (Fin.last n)`
multiplies `jimboWeightedTrace` by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_mul_T_last_diagonal]
  have hweight (w : Fin (n + 1) → Fin N) (c : Fin N) :
      (∏ i : Fin (n + 2), KnotTheory.jimboWeight q ((Fin.snoc w c : Fin (n + 2) → Fin N) i)) =
        (∏ i, KnotTheory.jimboWeight q (w i)) * KnotTheory.jimboWeight q c := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp only [hweight]
  rw [Finset.sum_comm, jimboWeightedTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  calc
    _ = (jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i)) *
        (∑ c : Fin N,
          (KnotTheory.jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
            ![w (Fin.last n), c] * KnotTheory.jimboWeight q c) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ ↦ by ring
    _ = _ := by rw [KnotTheory.sum_jimboGenerator_coeff_mul_weight, ite_eq_left rfl]; ring

/-- Two-sided Markov contraction for `jimboWeightedTrace` across the last generator. -/
theorem jimboWeightedTrace_strandIncl_mul_T_last_mul (N : ℕ) (q : Rˣ) (n : ℕ)
    (x y : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * T q (Fin.last n) * strandIncl R q (n + 1) y) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) (y * x) := by
  rw [jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
    jimboWeightedTrace_strandIncl_mul_T_last]

/-- Multiplying an included `(n + 1)`-strand element by `(T (Fin.last n))⁻¹` multiplies
`jimboWeightedTrace` by `q⁻¹ ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹) =
      ↑(q⁻¹ ^ N) * jimboWeightedTrace N q (n + 1) x := by
  rw [val_inv_unitT, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul,
    smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last, jimboWeightedTrace_strandIncl]
  have hs := KnotTheory.jimboWeight_sum (N := N) q
  linear_combination -jimboWeightedTrace N q (n + 1) x * hs

/-- On two strands, the positive generator `T 0` has weighted trace `q ^ N * δ_N`. -/
@[simp]
theorem jimboWeightedTrace_T_two (N : ℕ) (q : Rˣ) :
    jimboWeightedTrace N q 2 (T q (0 : Fin (2 - 1))) =
      ↑(q ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa using jimboWeightedTrace_braidHom N q (BraidGroup.sigma (0 : Fin (2 - 1)))

/-- On two strands, the inverse generator `(T 0)⁻¹` has weighted trace `q⁻¹ ^ N * δ_N`. -/
theorem jimboWeightedTrace_val_inv_unitT_two (N : ℕ) (q : Rˣ) :
    jimboWeightedTrace N q 2 ↑(unitT q (0 : Fin (2 - 1)))⁻¹ =
      ↑(q⁻¹ ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa [← Units.val_inv_eq_inv_val] using
    jimboWeightedTrace_braidHom N q ((BraidGroup.sigma (0 : Fin (2 - 1)))⁻¹)

/-- **Universal comparison of the Jimbo weighted trace with the homogenized Ocneanu trace.** Over
every commutative ring `R`, for every `N : ℕ`, `q : Rˣ`, `n : ℕ`, and `x` in the `(n + 1)`-strand
Hecke algebra, `jimboWeightedTrace` equals the quantum dimension `δ_N` times the degree-`n`
homogenized Ocneanu trace at `(q ^ N, δ_N)`. No invertibility assumption is needed. -/
theorem jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 1) x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) *
        InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace R q ↑(q ^ N)
          (∑ a : Fin N, KnotTheory.jimboWeight q a) n (toInfinite R q (n + 1) x) := by
  have h := eq_homogenizedOcneanuTrace_toInfinite
    (w := (↑(q ^ N) : R)) (δ := ∑ a : Fin N, KnotTheory.jimboWeight q a)
    (fun m ↦ jimboWeightedTrace N q (m + 1))
    (fun m y ↦ jimboWeightedTrace_strandIncl N q (m + 1) y)
    (fun m y z ↦ jimboWeightedTrace_mul_comm N q y z)
    (fun m y ↦ jimboWeightedTrace_strandIncl_mul_T_last N q m y)
    n x
  simpa only [jimboWeightedTrace_one, zero_add, pow_one] using h

/-- **Normalized comparison with the Ocneanu trace.** When `c` is an inverse to the quantum
dimension `δ_N`, rescaling `jimboWeightedTrace N q n` by `c ^ n` identifies the finite tower with
the Ocneanu trace at Markov parameter `c * q ^ N`. -/
theorem mul_pow_jimboWeightedTrace_eq_ocneanuTrace {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace N q n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  refine eq_ocneanuTrace_toInfinite
    (fun m ↦ c ^ m • jimboWeightedTrace N q m)
    (by simp)
    (fun m y ↦ ?_)
    (fun m x₁ x₂ ↦ by simp [jimboWeightedTrace_mul_comm])
    (fun m y ↦ ?_)
    n x
  · simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl]
    calc c ^ (m + 1) * (jimboWeightedTrace N q m y * ∑ a : Fin N, KnotTheory.jimboWeight q a)
        = c ^ m * jimboWeightedTrace N q m y * (c * ∑ a : Fin N, KnotTheory.jimboWeight q a) := by
          ring
      _ = c ^ m * jimboWeightedTrace N q m y := by rw [hc, mul_one]
  · simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last]
    ring

/-- Unrescaled form of `mul_pow_jimboWeightedTrace_eq_ocneanuTrace`: when `c * δ_N = 1`, the
`N`-colour weighted trace on `n` strands equals `δ_N ^ n` times the Ocneanu trace at `c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  rw [← mul_pow_jimboWeightedTrace_eq_ocneanuTrace hc, ← mul_assoc, ← mul_pow, mul_comm _ c, hc,
    one_pow, one_mul]

/-- Over a field where the quantum dimension `δ_N` is nonzero, dividing `jimboWeightedTrace` by
`δ_N ^ n` gives the Ocneanu trace at `q ^ N / δ_N`. -/
theorem jimboWeightedTrace_div_pow_eq_ocneanuTrace {K : Type*} [Field K] {N : ℕ} {q : Kˣ}
    (hδ : (∑ a : Fin N, KnotTheory.jimboWeight q a) ≠ 0) (n : ℕ)
    (x : TypeAHeckeAlgebra K q n) :
    jimboWeightedTrace N q n x / (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace K q
        (↑(q ^ N) / ∑ a : Fin N, KnotTheory.jimboWeight q a) (toInfinite K q n x) := by
  have hc : (∑ a : Fin N, KnotTheory.jimboWeight q a)⁻¹ *
      ∑ a : Fin N, KnotTheory.jimboWeight q a = 1 := inv_mul_cancel₀ hδ
  rw [div_eq_inv_mul, ← inv_pow, mul_pow_jimboWeightedTrace_eq_ocneanuTrace hc, inv_mul_eq_div]

/-- With `N = 1` colour, the weighted trace on `n` strands is the index character `T i ↦ q`. -/
@[simp]
theorem jimboWeightedTrace_one_color (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace 1 q n x =
      InfiniteTypeAHeckeAlgebra.indexCharacter R q (toInfinite R q n x) := by
  have hc : (1 : R) * ∑ a : Fin 1, KnotTheory.jimboWeight q a = 1 := by
    simp [KnotTheory.jimboWeight_def]
  have h := mul_pow_jimboWeightedTrace_eq_ocneanuTrace hc n x
  simpa only [one_pow, one_mul, pow_one, InfiniteTypeAHeckeAlgebra.ocneanuTrace_eq_indexCharacter,
    AlgHom.toLinearMap_apply] using h

/-- With `N = 0` colours on `n + 1` strands, the q-tensor space is zero and the weighted trace
vanishes identically. -/
@[simp]
theorem jimboWeightedTrace_zero_color_succ (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace 0 q (n + 1) x = 0 := by
  simp [jimboWeightedTrace_eq_sum]

/-- **Kernel inclusion in the finite Ocneanu trace radical.** When `c` is an inverse to the
`N`-colour quantum dimension `δ_N`, every element of `TypeAHeckeAlgebra R q n` annihilating the
`N`-colour q-tensor space lies in the finite trace radical of the Ocneanu trace at `c * q ^ N`. -/
theorem ker_jimbo_le_finiteRadical_ocneanuTrace {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (n : ℕ) :
    RingHom.ker (jimbo (Fin N) q (n := n)) ≤
      InfiniteTypeAHeckeAlgebra.finiteRadical
        (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace (R := R) (q := q)
          (c * ↑(q ^ N))).map_mul_comm n := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [InfiniteTypeAHeckeAlgebra.mem_finiteRadical]
  intro y
  rw [← mul_pow_jimboWeightedTrace_eq_ocneanuTrace hc, jimboWeightedTrace_apply,
    map_mul (jimbo (Fin N) q) x y, hx, zero_mul, zero_mul, map_zero, mul_zero]

end WeightedTrace

end TauCeti.TypeAHeckeAlgebra
