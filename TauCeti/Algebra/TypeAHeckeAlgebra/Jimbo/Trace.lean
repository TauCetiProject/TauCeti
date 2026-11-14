/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Jimbo.StrandInclusion
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Turaev's weighted trace on the finite type-A Hecke algebra

For `N` colours and a unit parameter `q : Rˣ`, Turaev's diagonal enhancement
`TauCeti.KnotTheory.jimboEnhancement q` commutes with the Jimbo representation
`TauCeti.TypeAHeckeAlgebra.jimbo (Fin N) q` of the finite type-A Hecke algebra on `n` strands. The
resulting weighted trace

`x ↦ tr (jimbo (Fin N) q x * jimboEnhancement q)`

(`TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace N q n`) is an `R`-linear trace on
`TypeAHeckeAlgebra R q n` over any commutative ring `R`, defined without dividing by the quantum
dimension `∑ a : Fin N, jimboWeight q a` or by `q - q⁻¹`. Composed with `braidHom`, it recovers the
weighted braid trace `TauCeti.KnotTheory.jimboWeightedTrace`.

This finite-colour trace on each `TypeAHeckeAlgebra R q n` is a separate object from the algebraic
Ocneanu trace on the full Hecke tower. Adding an uncrossed last strand along `strandIncl` holds the
last colour of each word fixed, so it multiplies the weighted trace by the quantum dimension. In a
positive or negative Markov stabilization `strandIncl x * T (Fin.last n)` or
`strandIncl x * (T (Fin.last n))⁻¹`, only the colour-preserving diagonal of the last crossing
contributes, and the weighted partial traces multiply the trace by `q ^ N` and `(q⁻¹) ^ N`.

When the quantum dimension admits an inverse `c` in `R`, normalizing `jimboWeightedTrace N q n` by
`c ^ n` produces a compatible Markov tower of traces with parameter `c * q ^ N`, which agrees with
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace` restricted along `toInfinite`
(`TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace`: the `N`-colour Turaev–Jimbo weighted trace on
  `TypeAHeckeAlgebra R q n`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_mapDomain_snoc`: `strandIncl` acts in the Jimbo
  representation with the last colour held fixed.
* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`: Turaev's enhancement commutes with
  the Jimbo action of the Hecke algebra.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last` and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last`: uncrossed-strand
  and positive/negative Markov stabilization formulas on the Hecke tower.
* `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace`: normalizing by an inverse of
  the quantum dimension identifies the finite-colour trace with the Ocneanu trace.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*,
  Lett. Math. Phys. 11 (1986), 247–252.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.

The strand-inclusion and stabilization calculations lift those for braids in
`TauCeti.KnotTheory.Jimbo.StrandInclusion` and `TauCeti.KnotTheory.Jimbo.Stabilization`.
-/

public section

open Function Finsupp
open scoped BigOperators

namespace TauCeti.TypeAHeckeAlgebra

section StrandInclusion

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] {n : ℕ}

/-- A Hecke algebra map and a linear map of word spaces intertwining the Jimbo representations on
every generator intertwine them everywhere. -/
private theorem jimbo_comp_eq_of_forall_T {m : ℕ} (q : Rˣ)
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

/-- Adding an uncrossed last strand via `strandIncl` acts in the Jimbo representation on any
number of strands with the last colour held fixed. -/
@[simp]
theorem jimbo_strandIncl_mapDomain_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.snoc w a : Fin (n + 1) → ι))
  suffices h : (jimbo ι q (strandIncl R q n x)).comp L = L.comp (jimbo ι q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine jimbo_comp_eq_of_forall_T q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).castSucc := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).castSucc := Fin.ext (by simp)
  rw [strandIncl_T, jimbo_T, jimbo_T, hj, hk]
  exact KnotTheory.jimboGenerator_comp_lmapDomain_snoc q _ _ a

/-- Basis-vector form of compatibility of `jimbo` with `strandIncl`. -/
@[simp]
theorem jimbo_strandIncl_single_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) (a : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) =
      mapDomain (fun u ↦ Fin.snoc u a) (jimbo ι q x (single w c)) := by
  simpa only [mapDomain_single] using jimbo_strandIncl_mapDomain_snoc q x a (single w c)

/-- Under `strandIncl`, the Jimbo action preserves matrix coefficients on each fixed-last-colour
block and has zero coefficients between blocks with different last colours. -/
theorem jimbo_strandIncl_single_snoc_apply_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) (Fin.snoc u d) =
      if a = d then jimbo ι q x (single w c) u else 0 := by
  classical
  rw [jimbo_strandIncl_single_snoc]
  by_cases had : a = d
  · subst d
    simp only [↓reduceIte]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · simp only [had, ↓reduceIte]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply had
    simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z (Fin.last n)) hv

end StrandInclusion

section CommRing

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- Turaev's tensor-power enhancement commutes with every element of the finite Hecke algebra in
the Jimbo representation. -/
theorem commute_jimboEnhancement_jimbo (N : ℕ) (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
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

/-- Turaev's `N`-colour weighted trace `x ↦ tr (jimbo (Fin N) q x * jimboEnhancement q)` on the
finite type-A Hecke algebra on `n` strands. No invertibility of the quantum dimension or of
`q - q⁻¹` is assumed. -/
noncomputable def jimboWeightedTrace (N : ℕ) (q : Rˣ) (n : ℕ) : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R) ∘ₗ
    LinearMap.mulRight R (KnotTheory.jimboEnhancement q) ∘ₗ (jimbo (Fin N) q).toLinearMap

/-- Defining formula for `jimboWeightedTrace`. -/
theorem jimboWeightedTrace_apply (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q) :=
  (rfl)

/-- The weighted braid trace factors through `jimboWeightedTrace` along `braidHom`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (N : ℕ) (q : Rˣ) (n : ℕ) (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b) = KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [jimboWeightedTrace_apply, jimbo_braidHom, KnotTheory.jimboWeightedTrace_def]

/-- The `N`-colour Jimbo weighted trace is tracial on `TypeAHeckeAlgebra R q n`. -/
theorem jimboWeightedTrace_mul_comm (N : ℕ) (q : Rˣ) (n : ℕ) (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  rw [jimboWeightedTrace_apply, jimboWeightedTrace_apply, map_mul (jimbo (Fin N) q) x y,
    map_mul (jimbo (Fin N) q) y x, mul_assoc,
    ← (commute_jimboEnhancement_jimbo N q y).eq, ← mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc]

/-- Diagonal-sum expansion of `jimboWeightedTrace` in the canonical word basis. -/
theorem jimboWeightedTrace_eq_sum (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      ∑ w : Fin n → Fin N,
        jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, mul_apply_eq_comp,
    Finsupp.coe_basisSingleOne, KnotTheory.jimboEnhancement_single_one, map_smul]
  simp [mul_comm]

/-- On `1`, `jimboWeightedTrace` is the `n`-th power of the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_one (N : ℕ) (q : Rˣ) (n : ℕ) :
    jimboWeightedTrace N q n 1 = (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  simpa using jimboWeightedTrace_braidHom N q n 1

/-- Value of `jimboWeightedTrace` on scalars. -/
@[simp]
theorem jimboWeightedTrace_algebraMap (N : ℕ) (q : Rˣ) (n : ℕ) (r : R) :
    jimboWeightedTrace N q n (algebraMap R _ r) =
      r * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, jimboWeightedTrace_one, smul_eq_mul]

/-- At `q = 1`, the enhancement is the identity, so the weighted trace is the ordinary trace of
the permutation action on words. -/
@[simp]
theorem jimboWeightedTrace_one_parameter (N n : ℕ) (x : TypeAHeckeAlgebra R (1 : Rˣ) n) :
    jimboWeightedTrace N (1 : Rˣ) n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R) (jimbo (Fin N) (1 : Rˣ) x) := by
  simp [jimboWeightedTrace_apply]

/-- Adding an uncrossed last strand multiplies `jimboWeightedTrace` by the quantum dimension, on
any number of strands (including zero). -/
@[simp]
theorem jimboWeightedTrace_strandIncl (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_single_snoc_apply_snoc, ↓reduceIte, Fin.prod_univ_castSucc (n := n),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [jimboWeightedTrace_eq_sum, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- In the diagonal coefficient of `strandIncl x * T (Fin.last n)` on `Fin.snoc w c`, only the
colour-preserving two-strand entry of the last crossing survives. -/
private theorem jimbo_strandIncl_mul_T_last_single_snoc_apply (q : Rˣ)
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
  simp only [map_mul, mul_apply_eq_comp, jimbo_T, hj, hk, KnotTheory.jimboGenerator_single_one,
    Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpair : (![c, w (Fin.last n)] : Fin 2 → Fin N) = ![w (Fin.last n), c] ↔
      w (Fin.last n) = c := by
    simp [funext_iff, Fin.forall_fin_two, eq_comm]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, hswap, hswap₂,
      jimbo_strandIncl_single_snoc_apply_snoc, single_apply, hpair, mul_zero]
  · simp only [h, ↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      jimbo_strandIncl_single_snoc_apply_snoc, single_eq_same, mul_one, mul_comm]
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, hswap, hswap₂, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, zero_add, mul_one, mul_comm]

/-- **Positive Markov rule for `jimboWeightedTrace`.** Appending a strand and multiplying by the
last Hecke generator multiplies the `N`-colour weighted trace by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_mul_T_last_single_snoc_apply, Fin.prod_univ_castSucc (n := n + 1),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm, jimboWeightedTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  calc
    _ = (jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i)) *
        ∑ c : Fin N,
          (KnotTheory.jimboGenerator q (0 : Fin 2) 1 (single ![w (Fin.last n), c] 1))
            ![w (Fin.last n), c] * KnotTheory.jimboWeight q c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      ring
    _ = _ := by
      rw [KnotTheory.sum_jimboGenerator_coeff_mul_weight, ite_eq_left_iff.2 (fun h ↦ (h rfl).elim)]
      ring

/-- Two-sided Markov reduction: `strandIncl x * T (Fin.last n) * strandIncl y` has weighted trace
`q ^ N` times that of `y * x`. -/
theorem jimboWeightedTrace_strandIncl_mul_T_last_mul (N : ℕ) (q : Rˣ) (n : ℕ)
    (x y : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * T q (Fin.last n) * strandIncl R q (n + 1) y) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) (y * x) := by
  rw [jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
    jimboWeightedTrace_strandIncl_mul_T_last]

/-- **Negative Markov rule for `jimboWeightedTrace`.** Appending a strand and multiplying by the
inverse of the last Hecke generator multiplies the `N`-colour weighted trace by `(q⁻¹) ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace N q (n + 1) x := by
  rw [val_inv_unitT, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul,
    jimboWeightedTrace_strandIncl_mul_T_last, jimboWeightedTrace_strandIncl, smul_eq_mul]
  have hs := KnotTheory.jimboWeight_sum (N := N) q
  linear_combination -jimboWeightedTrace N q (n + 1) x * hs

/-- On two strands, the single positive Hecke generator has weighted trace `q ^ N` times the
quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_T_two (N : ℕ) (q : Rˣ) :
    jimboWeightedTrace N q 2 (T q 0) = ↑(q ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa using jimboWeightedTrace_braidHom N q 2 (BraidGroup.sigma (0 : Fin (2 - 1)))

/-- On two strands, the inverse of the Hecke generator has weighted trace `(q⁻¹) ^ N` times the
quantum dimension. -/
theorem jimboWeightedTrace_val_inv_unitT_two (N : ℕ) (q : Rˣ) :
    jimboWeightedTrace N q 2 ↑(unitT (n := 2) q 0)⁻¹ =
      ↑((q⁻¹) ^ N) * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  simpa [map_inv] using
    jimboWeightedTrace_braidHom N q 2 ((BraidGroup.sigma (0 : Fin (2 - 1)))⁻¹)

/-- **Comparison with the Ocneanu trace.** When `c` is an inverse to the quantum dimension
`∑ a : Fin N, jimboWeight q a`, normalizing `jimboWeightedTrace N q n` by `c ^ n` yields the
Ocneanu trace with parameter `c * q ^ N` along `toInfinite`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace N q n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  have h := eq_ocneanuTrace_toInfinite (z := c * ↑(q ^ N))
    (fun m ↦ (c ^ m) • jimboWeightedTrace N q m) (by simp)
    (fun m y ↦ by
      simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl]
      calc
        c ^ (m + 1) * (jimboWeightedTrace N q m y * ∑ a : Fin N, KnotTheory.jimboWeight q a) =
            c ^ m * jimboWeightedTrace N q m y *
              (c * ∑ a : Fin N, KnotTheory.jimboWeight q a) := by ring
        _ = c ^ m * jimboWeightedTrace N q m y := by rw [hc, mul_one])
    (fun m y₁ y₂ ↦ by simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_mul_comm])
    (fun m y ↦ by
      simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last]
      ring)
    n x
  simpa only [LinearMap.smul_apply, smul_eq_mul] using h

/-- Unnormalized form of the comparison with `ocneanuTrace`: when `c` inverts the quantum
dimension, `jimboWeightedTrace` is the `n`-th power of the quantum dimension times the Ocneanu
trace with parameter `c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  rw [← mul_jimboWeightedTrace_eq_ocneanuTrace hc, ← mul_assoc, ← mul_pow, mul_comm _ c, hc,
    one_pow, one_mul]

end CommRing

section Field

variable {K : Type*} [Field K] {N n : ℕ}

/-- Over a field where the quantum dimension is nonzero, dividing `jimboWeightedTrace` by the
`n`-th power of the quantum dimension gives the Ocneanu trace at `q ^ N / [N]_q`. -/
theorem jimboWeightedTrace_div_pow_eq_ocneanuTrace (q : Kˣ)
    (hδ : ∑ a : Fin N, KnotTheory.jimboWeight q a ≠ 0) (x : TypeAHeckeAlgebra K q n) :
    jimboWeightedTrace N q n x / (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace K q
        (↑(q ^ N) / ∑ a : Fin N, KnotTheory.jimboWeight q a) (toInfinite K q n x) := by
  have hc : (∑ a : Fin N, KnotTheory.jimboWeight q a)⁻¹ *
      ∑ a : Fin N, KnotTheory.jimboWeight q a = 1 := inv_mul_cancel₀ hδ
  simpa only [div_eq_inv_mul, inv_pow] using mul_jimboWeightedTrace_eq_ocneanuTrace hc x

/-- Over a field where the quantum dimension is nonzero, `jimboWeightedTrace` equals the `n`-th
power of the quantum dimension times the Ocneanu trace at `q ^ N / [N]_q`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace_div (q : Kˣ)
    (hδ : ∑ a : Fin N, KnotTheory.jimboWeight q a ≠ 0) (x : TypeAHeckeAlgebra K q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace K q
          (↑(q ^ N) / ∑ a : Fin N, KnotTheory.jimboWeight q a) (toInfinite K q n x) := by
  rw [← jimboWeightedTrace_div_pow_eq_ocneanuTrace q hδ, mul_div_cancel₀ _ (pow_ne_zero n hδ)]

end Field

end TauCeti.TypeAHeckeAlgebra
