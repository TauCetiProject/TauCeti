/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Polynomial
public import TauCeti.Algebra.TypeAHeckeAlgebra.TraceRadical
public import TauCeti.KnotTheory.Jimbo.Trace

import Mathlib.Tactic.LinearCombination
import TauCeti.KnotTheory.Jimbo.Stabilization

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

* `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_lmapDomain_snoc`,
  `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_single_snoc`, and
  `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_single_snoc_apply_snoc`: appending a fixed colour
  intertwines `jimbo` along `strandIncl` for all strand counts `n`.
* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`: Turaev's enhancement commutes with
  the entire Hecke-algebra action.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last`, and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last`: uncrossed-strand
  and positive/negative crossing contractions on the Hecke algebra.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_T` and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_val_inv_unitT`: the weighted traces of the
  generators and their inverses.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace`: unconditional
  factorization through `homogenizedOcneanuTrace` over any commutative ring.
* `TauCeti.TypeAHeckeAlgebra.mul_pow_jimboWeightedTrace_eq_ocneanuTrace` and
  `TauCeti.TypeAHeckeAlgebra.ker_jimbo_le_finiteRadical_ocneanuTrace`: normalized comparison with
  `ocneanuTrace` and inclusion of the Jimbo representation kernel in the finite trace radical.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_braidHom_eq_mul_jimboWeightedTrace` and
  `TauCeti.KnotTheory.jimboWeightedTrace_eq_pow_mul_ocneanuTrace_braidHom`: the normalized
  comparison on braids.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Finsupp
open scoped BigOperators

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R]

section Intertwining

variable (ι : Type*) [LinearOrder ι] (q : Rˣ) {n : ℕ}

/-- Appending a fixed colour to every word intertwines the Jimbo representation of the Hecke
algebra along the tower inclusion `strandIncl`. -/
@[simp↓]
theorem jimbo_strandIncl_lmapDomain_snoc (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (lmapDomain R R (fun w ↦ Fin.snoc w a) v) =
      lmapDomain R R (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  rcases n with _ | m
  · obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (Nat.zero_le 1) x
    simp [Algebra.algebraMap_eq_smul_one]
  · let L : TypeAHeckeAlgebra R q (m + 1) →ₗ[R] (Fin (m + 2) → ι) →₀ R :=
      LinearMap.applyₗ (lmapDomain R R (fun w ↦ Fin.snoc w a) v) ∘ₗ
        (jimbo ι q (n := m + 2)).toLinearMap ∘ₗ (strandIncl R q (m + 1)).toLinearMap
    let M : TypeAHeckeAlgebra R q (m + 1) →ₗ[R] (Fin (m + 2) → ι) →₀ R :=
      lmapDomain R R (fun w ↦ Fin.snoc w a) ∘ₗ
        LinearMap.applyₗ v ∘ₗ (jimbo ι q (n := m + 1)).toLinearMap
    have hLM : L = M := LinearMap.ext_on_range span_range_braidHom fun b ↦ by
      simp only [L, M, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply,
        ← braidHom_strandIncl, jimbo_braidHom, KnotTheory.jimbo_strandIncl_lmapDomain_snoc]
    exact LinearMap.congr_fun hLM x

/-- Basis-vector form of the strand-inclusion intertwining identity for `jimbo`. -/
@[simp]
theorem jimbo_strandIncl_single_snoc (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) (a : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) =
      mapDomain (fun u ↦ Fin.snoc u a) (jimbo ι q x (single w c)) := by
  simpa only [lmapDomain_apply, mapDomain_single] using
    jimbo_strandIncl_lmapDomain_snoc ι q x a (single w c)

/-- Inclusion preserves coefficients on each fixed-last-colour block and has zero coefficients
between blocks with different last colours. -/
@[simp↓]
theorem jimbo_strandIncl_single_snoc_apply_snoc (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) (Fin.snoc u d) =
      if a = d then jimbo ι q x (single w c) u else 0 := by
  classical
  rw [jimbo_strandIncl_single_snoc]
  by_cases h : a = d
  · subst d
    simp only [ite_true]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · rw [ite_eq_right h]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply h
    simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z (Fin.last n)) hv

end Intertwining

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

/-- At `q = 1`, the enhancement is the identity, so the weighted trace is the ordinary trace of
the permutation action on words. -/
@[simp]
theorem jimboWeightedTrace_one_parameter (N n : ℕ) (x : TypeAHeckeAlgebra R (1 : Rˣ) n) :
    jimboWeightedTrace N (1 : Rˣ) n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R) (jimbo (Fin N) (1 : Rˣ) x) := by
  simp [jimboWeightedTrace_apply]

/-- Adding an uncrossed strand multiplies `jimboWeightedTrace` by the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_strandIncl (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  cases n with
  | zero =>
    obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (Nat.zero_le 1) x
    simp
  | succ n =>
    let f : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
      jimboWeightedTrace N q (n + 2) ∘ₗ (strandIncl R q (n + 1)).toLinearMap
    let g : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
      (∑ a : Fin N, KnotTheory.jimboWeight q a) • jimboWeightedTrace N q (n + 1)
    have hfg : f = g :=
      LinearMap.ext_on_range (span_range_braidHom (R := R) (q := q)) fun b ↦ by
        simp [f, g, ← braidHom_strandIncl, mul_comm]
    simpa [f, g, mul_comm] using LinearMap.congr_fun hfg x

/-- Multiplying an included `(n + 1)`-strand element by the positive crossing `T (Fin.last n)`
multiplies `jimboWeightedTrace` by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  let f : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    jimboWeightedTrace N q (n + 2) ∘ₗ LinearMap.mulRight R (T q (Fin.last n)) ∘ₗ
      (strandIncl R q (n + 1)).toLinearMap
  let g : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    (↑(q ^ N) : R) • jimboWeightedTrace N q (n + 1)
  have hfg : f = g :=
    LinearMap.ext_on_range (span_range_braidHom (R := R) (q := q)) fun b ↦ by
      have hmul :
          strandIncl R q (n + 1) (braidHom R q (n + 1) b) * T q (Fin.last n) =
            (braidHom R q (n + 2) (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) :
              TypeAHeckeAlgebra R q (n + 2)) := by
        simp
      simp only [f, g, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
        LinearMap.smul_apply, smul_eq_mul, hmul, jimboWeightedTrace_braidHom,
        KnotTheory.jimboWeightedTrace_stabilize]
  exact LinearMap.congr_fun hfg x

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

/-- Every generator `T q i` on `n` strands has weighted trace `q ^ N * δ_N ^ (n - 1)`. -/
@[simp]
theorem jimboWeightedTrace_T (N : ℕ) (q : Rˣ) (n : ℕ) (i : Fin (n - 1)) :
    jimboWeightedTrace N q n (T q i) =
      ↑(q ^ N) * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ (n - 1) := by
  induction n with
  | zero => exact i.elim0
  | succ m ih =>
    rcases m with _ | k
    · exact i.elim0
    · refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [map_one, one_mul, jimboWeightedTrace_one, Nat.add_sub_cancel] using
          jimboWeightedTrace_strandIncl_mul_T_last N q k (1 : TypeAHeckeAlgebra R q (k + 1))
      · rw [← strandIncl_T_castSucc, jimboWeightedTrace_strandIncl, ih j]
        simp [pow_succ, mul_assoc]

/-- Every inverse generator `(T q i)⁻¹` on `n` strands has weighted trace
`q⁻¹ ^ N * δ_N ^ (n - 1)`. -/
@[simp↓]
theorem jimboWeightedTrace_val_inv_unitT (N : ℕ) (q : Rˣ) (n : ℕ) (i : Fin (n - 1)) :
    jimboWeightedTrace N q n (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) =
      ↑(q⁻¹ ^ N) * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ (n - 1) := by
  rcases n with _ | m
  · exact i.elim0
  · rw [val_inv_unitT, map_sub, jimboWeightedTrace_T, jimboWeightedTrace_algebraMap,
      Nat.add_sub_cancel, pow_succ', ← mul_assoc, KnotTheory.jimboWeight_sum]
    ring

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

/-- Over a field where the quantum dimension is nonzero, `jimboWeightedTrace` equals the `n`-th
power of the quantum dimension times the Ocneanu trace at `q ^ N / δ_N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace_div {K : Type*} [Field K] {N : ℕ} {q : Kˣ}
    (hδ : (∑ a : Fin N, KnotTheory.jimboWeight q a) ≠ 0) (n : ℕ)
    (x : TypeAHeckeAlgebra K q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace K q
          (↑(q ^ N) / ∑ a : Fin N, KnotTheory.jimboWeight q a) (toInfinite K q n x) := by
  rw [← jimboWeightedTrace_div_pow_eq_ocneanuTrace hδ n x, mul_div_cancel₀ _ (pow_ne_zero n hδ)]

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

end TauCeti.TypeAHeckeAlgebra

namespace TauCeti.InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}

/-- On the image of a braid on `n` strands in the infinite Hecke algebra, the Ocneanu trace at
`c * q ^ N` is `c ^ n` times Turaev's weighted Jimbo braid trace. -/
theorem ocneanuTrace_braidHom_eq_mul_jimboWeightedTrace
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) {n : ℕ} (b : BraidGroup n) :
    ocneanuTrace R q (c * ↑(q ^ N)) (braidHom R q n b) =
      c ^ n * KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.mul_pow_jimboWeightedTrace_eq_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimboWeightedTrace_braidHom]

end TauCeti.InfiniteTypeAHeckeAlgebra

namespace TauCeti.KnotTheory

open InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}

/-- On a braid on `n` strands, Turaev's weighted Jimbo trace is the `n`-th power of the quantum
dimension times the Ocneanu trace at `c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace_braidHom
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) {n : ℕ} (b : BraidGroup n) :
    jimboWeightedTrace (N := N) q b =
      (∑ a : Fin N, jimboWeight q a) ^ n *
        ocneanuTrace R q (c * ↑(q ^ N)) (InfiniteTypeAHeckeAlgebra.braidHom R q n b) := by
  rw [← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.jimboWeightedTrace_eq_pow_mul_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimboWeightedTrace_braidHom]

end TauCeti.KnotTheory
