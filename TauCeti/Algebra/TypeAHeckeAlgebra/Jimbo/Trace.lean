/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Jimbo.StrandInclusion
import Mathlib.Tactic.LinearCombination

/-!
# The weighted Jimbo trace on the type-A Hecke algebra and its Ocneanu comparison

On the `n`-strand q-tensor space `(Fin n → Fin N) →₀ R`, Turaev's diagonal enhancement
`TauCeti.KnotTheory.jimboEnhancement q` commutes with every operator in the Jimbo representation
`TauCeti.TypeAHeckeAlgebra.jimbo (Fin N) q`. Weighting the representation trace by this operator
defines a linear functional `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace N q n` on the finite
type-A Hecke algebra, over any commutative ring `R` and at any unit parameter `q : Rˣ` (including
`q = ±1`, with no division by `q - q⁻¹` or by the quantum dimension). Composed with the braid
homomorphism `braidHom`, it recovers the weighted braid trace
`TauCeti.KnotTheory.jimboWeightedTrace`.

This finite-colour weighted trace is kept separate from the universal algebraic Ocneanu trace
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace` on the infinite Hecke tower: on `1` it takes the
value `[N]_q ^ n`, where `[N]_q = ∑ a : Fin N, jimboWeight q a` is the quantum dimension, and
adding an uncrossed strand multiplies it by `[N]_q`. Using the intertwining of `strandIncl` with
fixed-last-colour word inclusion together with Turaev's positive and negative two-strand weighted
partial traces (`sum_jimboGenerator_coeff_mul_weight` and `sum_jimboUnit_inv_coeff_mul_weight`), we
prove both last-strand Markov stabilization laws on arbitrary Hecke algebra elements: multiplying
`strandIncl x` by the last generator `T (Fin.last n)` multiplies the trace by `q ^ N`, while
multiplying by `(unitT (Fin.last n))⁻¹` multiplies it by `(q⁻¹) ^ N`.

Comparing the resulting finite Markov tower with `ocneanuTrace` yields two forms of the
identification along `toInfinite`:
* Without inverting `[N]_q`, whenever `z * [N]_q = q ^ N`,
  `jimboWeightedTrace N q n x = [N]_q ^ n * ocneanuTrace R q z (toInfinite R q n x)`.
* Whenever `c * [N]_q = 1`, rescaling by `c ^ n` identifies the finite-colour trace directly with
  `ocneanuTrace R q (c * q ^ N)` on every `n`-strand Hecke element and on every `n`-strand braid.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace`: Turaev's `N`-colour weighted trace as an
  `R`-linear functional on `TypeAHeckeAlgebra R q n`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo` and
  `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_mapDomain_snoc`: commutation with the enhancement and
  intertwining with `strandIncl`.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last`, and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last`: uncrossed-strand
  and positive/negative Markov stabilization rules on arbitrary Hecke elements.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_pow_mul_ocneanuTrace_of_mul_eq` and
  `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite`: comparison with
  the universal Ocneanu trace.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Section 5.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

section Representation

variable (ι) [LinearOrder ι] (q : Rˣ)

/-- In the Jimbo representation, the inverse of the generator `T i` acts by the inverse of the
adjacent crossing unit `jimboUnit q i`. -/
theorem jimbo_val_inv_unitT (i : Fin (n - 1)) :
    jimbo ι q (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) =
      (↑(KnotTheory.jimboUnit (ι := ι) q i)⁻¹ : Module.End R ((Fin n → ι) →₀ R)) := by
  have h := jimbo_braidHom ι q ((BraidGroup.sigma i)⁻¹ : BraidGroup n)
  simpa only [map_inv, braidHom_sigma, KnotTheory.jimbo_sigma] using h

/-- A homomorphism of Hecke algebras and a linear map of word spaces which intertwine the Jimbo
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

/-- The Jimbo action of an element after adding an uncrossed last strand is its original action
with the last colour held fixed. -/
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
  rw [strandIncl_T, jimbo_T, jimbo_T, hj, hk, KnotTheory.jimboGenerator_comp_lmapDomain_snoc]

/-- Adding an uncrossed last strand preserves matrix coefficients within each fixed-last-colour
block and has zero coefficients between blocks with distinct last colours. -/
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

end Representation

section Trace

/-- Turaev's tensor-power enhancement commutes with every element in the `N`-colour Jimbo
representation of the type-A Hecke algebra. -/
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

/-- Turaev's `N`-colour weighted trace `x ↦ tr (ρ(x) * μ^{⊗ n})` on the type-A Hecke algebra on `n`
strands, as an `R`-linear map. -/
noncomputable def jimboWeightedTrace (N : ℕ) (q : Rˣ) (n : ℕ) :
    TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R) ∘ₗ
    LinearMap.mulRight R (KnotTheory.jimboEnhancement q) ∘ₗ
      (jimbo (Fin N) q).toLinearMap

/-- Evaluation of `jimboWeightedTrace` as the operator trace weighted by `jimboEnhancement`. -/
theorem jimboWeightedTrace_apply (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q) := (rfl)

/-- On the image of a braid in the Hecke algebra, `jimboWeightedTrace` agrees with the native
weighted braid trace `KnotTheory.jimboWeightedTrace`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (N : ℕ) (q : Rˣ) (n : ℕ) (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b) =
      KnotTheory.jimboWeightedTrace (N := N) q b := by
  simp [jimboWeightedTrace_apply, KnotTheory.jimboWeightedTrace_def]

/-- The `N`-colour weighted Jimbo trace on the Hecke algebra is tracial. -/
theorem jimboWeightedTrace_mul_comm (N : ℕ) (q : Rˣ) (n : ℕ)
    (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  rw [jimboWeightedTrace_apply, jimboWeightedTrace_apply, map_mul (jimbo (Fin N) q) x y,
    map_mul (jimbo (Fin N) q) y x, mul_assoc,
    ← (commute_jimboEnhancement_jimbo N q y).eq, ← mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc]

/-- In the canonical word basis, `jimboWeightedTrace` is the sum of diagonal matrix coefficients
weighted by the product of their letter weights. -/
theorem jimboWeightedTrace_eq_sum (N : ℕ) (q : Rˣ) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      ∑ w : Fin n → Fin N,
        jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, mul_apply_eq_comp,
    Finsupp.coe_basisSingleOne, KnotTheory.jimboEnhancement_single_one, map_smul]
  simp [mul_comm]

/-- The weighted Jimbo trace of `1` on `n` strands is the `n`-th power of the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_one (N : ℕ) (q : Rˣ) (n : ℕ) :
    jimboWeightedTrace N q n 1 = (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  simpa using jimboWeightedTrace_braidHom N q n 1

/-- Adding an uncrossed last strand multiplies `jimboWeightedTrace` by the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_strandIncl (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_single_snoc_apply_snoc, ite_true, Fin.prod_univ_castSucc (n := n),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [jimboWeightedTrace_eq_sum, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

private theorem jimbo_strandIncl_mul_T_last_single_snoc_apply {N : ℕ} (q : Rˣ)
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
  simp only [map_mul, mul_apply_eq_comp, jimbo_T, hj, hk, KnotTheory.jimboGenerator_single_one,
    Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, hswap, hswap₂,
      jimbo_strandIncl_single_snoc_apply_snoc, single_apply, hpair, mul_zero]
  · simp only [h, ↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      jimbo_strandIncl_single_snoc_apply_snoc, single_eq_same, mul_one, mul_comm]
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, hswap, hswap₂, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jimbo_strandIncl_single_snoc_apply_snoc,
      single_apply, hpair, zero_add, mul_one, mul_comm]

private theorem jimbo_strandIncl_mul_val_inv_unitT_last_single_snoc_apply {N : ℕ} (q : Rˣ)
    (x : TypeAHeckeAlgebra R q (n + 1)) (w : Fin (n + 1) → Fin N) (c : Fin N) :
    jimbo (n := n + 2) (Fin N) q
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹)
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      jimbo (Fin N) q x (single w 1) w *
        (((KnotTheory.jimboUnit q (0 : Fin (2 - 1)))⁻¹ :
          (Module.End R ((Fin 2 → Fin N) →₀ R))ˣ) : Module.End R ((Fin 2 → Fin N) →₀ R))
          (single ![w (Fin.last n), c] 1) ![w (Fin.last n), c] := by
  have hdiag := jimbo_strandIncl_mul_T_last_single_snoc_apply q x w c
  have h0 : BraidGroup.strand (0 : Fin (2 - 1)) = 0 := Fin.ext (by simp)
  have h1 : BraidGroup.strandSucc (0 : Fin (2 - 1)) = 1 := Fin.ext (by simp)
  rw [map_mul, mul_apply_eq_comp, jimbo_T] at hdiag
  rw [map_mul, mul_apply_eq_comp, jimbo_val_inv_unitT, KnotTheory.jimboUnit_inv_val,
    KnotTheory.jimboUnit_inv_val, h0, h1]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, single_eq_same, hdiag,
    jimbo_strandIncl_single_snoc_apply_snoc, ↓reduceIte]
  ring

/-- **Positive Markov stabilization for `jimboWeightedTrace`.** Multiplying an element included from
the first `n + 1` strands by the last generator `T (Fin.last n)` multiplies the `N`-colour weighted
trace by `q ^ N`. -/
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
      rw [KnotTheory.sum_jimboGenerator_coeff_mul_weight, ite_eq_left rfl]
      ring

/-- **Negative Markov stabilization for `jimboWeightedTrace`.** Multiplying an element included from
the first `n + 1` strands by the inverse of the last generator `(unitT (Fin.last n))⁻¹` multiplies
the `N`-colour weighted trace by `(q⁻¹) ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace N q (n + 1) x := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_mul_val_inv_unitT_last_single_snoc_apply, Fin.prod_univ_castSucc (n := n + 1),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm, jimboWeightedTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  calc
    _ = (jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i)) *
          ∑ c : Fin N,
            (((KnotTheory.jimboUnit q (0 : Fin (2 - 1)))⁻¹ :
              (Module.End R ((Fin 2 → Fin N) →₀ R))ˣ) : Module.End R ((Fin 2 → Fin N) →₀ R))
              (single ![w (Fin.last n), c] 1) ![w (Fin.last n), c] *
              KnotTheory.jimboWeight q c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      ring
    _ = _ := by
      rw [KnotTheory.sum_jimboUnit_inv_coeff_mul_weight, ite_eq_left rfl]
      ring

/-- Every standard generator `T i` on `n` strands has `N`-colour weighted trace
`q ^ N * [N]_q ^ (n - 1)`. -/
@[simp]
theorem jimboWeightedTrace_T (N : ℕ) (q : Rˣ) (i : Fin (n - 1)) :
    jimboWeightedTrace N q n (T q i) =
      ↑(q ^ N) * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ (n - 1) := by
  obtain _ | _ | m := n
  · exact i.elim0
  · exact i.elim0
  · induction m with
    | zero =>
      fin_cases i
      simpa using jimboWeightedTrace_strandIncl_mul_T_last N q 0 1
    | succ m ih =>
      obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · rw [← strandIncl_T_castSucc (n := m + 1), jimboWeightedTrace_strandIncl, ih j]
        simp [pow_succ, mul_assoc]
      · simpa using jimboWeightedTrace_strandIncl_mul_T_last N q (m + 1) 1

/-- Every inverse generator `(unitT i)⁻¹` on `n` strands has `N`-colour weighted trace
`(q⁻¹) ^ N * [N]_q ^ (n - 1)`. -/
theorem jimboWeightedTrace_val_inv_unitT (N : ℕ) (q : Rˣ) (i : Fin (n - 1)) :
    jimboWeightedTrace N q n ↑(unitT q i)⁻¹ =
      ↑((q⁻¹) ^ N) * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ (n - 1) := by
  obtain _ | _ | m := n
  · exact i.elim0
  · exact i.elim0
  · induction m with
    | zero =>
      fin_cases i
      simpa using jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last N q 0 1
    | succ m ih =>
      obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · have hinv : (↑(unitT (n := m + 3) q j.castSucc)⁻¹ : TypeAHeckeAlgebra R q (m + 3)) =
            strandIncl R q (m + 2) ↑(unitT (n := m + 2) q j)⁻¹ := by
          simp only [val_inv_unitT, map_sub, AlgHom.commutes, strandIncl_T_castSucc]
        rw [hinv, jimboWeightedTrace_strandIncl, ih j]
        simp [pow_succ, mul_assoc]
      · simpa using jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last N q (m + 1) 1

/-! ### Comparison with the universal Ocneanu trace -/

/-- **Uninverted Ocneanu comparison for `jimboWeightedTrace`.** Whenever `z` satisfies
`z * [N]_q = q ^ N`, the `N`-colour weighted Jimbo trace on `n` strands equals `[N]_q ^ n` times
the Ocneanu trace with parameter `z` along `toInfinite`. No invertibility of `[N]_q` or of
`q - q⁻¹` is assumed. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace_of_mul_eq {N : ℕ} {q : Rˣ} {z : R}
    (hz : z * ∑ a : Fin N, KnotTheory.jimboWeight q a = ↑(q ^ N))
    (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) := by
  set δ : R := ∑ a : Fin N, KnotTheory.jimboWeight q a
  have hτ := InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace (q := q) z
  have hmem (m : ℕ) (y : TypeAHeckeAlgebra R q m) :
      toInfinite R q m y ∈ InfiniteTypeAHeckeAlgebra.stage R q m := by
    rw [← range_toInfinite]
    exact ⟨y, rfl⟩
  have hle (m : ℕ) (hm : m ≤ 1) (y : TypeAHeckeAlgebra R q m) :
      jimboWeightedTrace N q m y =
        δ ^ m * InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q m y) := by
    obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one hm y
    rw [AlgHom.commutes, hτ.map_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul,
      jimboWeightedTrace_one, smul_eq_mul]
    ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain hn | ⟨n, rfl⟩ : n ≤ 1 ∨ ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    exacts [.inl (by omega), .inl le_rfl, .inr ⟨m, rfl⟩]
  · exact hle n hn x
  let M : TypeAHeckeAlgebra R q (n + 2) →ₗ[R] R :=
    δ ^ (n + 2) • (InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z ∘ₗ
      (toInfinite R q (n + 2)).toLinearMap)
  let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
    (LinearMap.eqLocus (jimboWeightedTrace N q (n + 2)) M).map
      (toInfinite R q (n + 2)).toLinearMap
  have hsub (y : InfiniteTypeAHeckeAlgebra R q)
      (hy : y ∈ InfiniteTypeAHeckeAlgebra.stage R q (n + 1)) :
      ∃ y' : TypeAHeckeAlgebra R q (n + 1), toInfinite R q (n + 1) y' = y := by
    rw [← range_toInfinite] at hy
    exact hy
  have hP : Subalgebra.toSubmodule (InfiniteTypeAHeckeAlgebra.stage R q (n + 2)) ≤ P := by
    refine InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two_le_iff.2
      ⟨fun y hy ↦ ?_, fun a ha b hb ↦ ?_⟩
    · obtain ⟨y', rfl⟩ := hsub y hy
      refine ⟨strandIncl R q (n + 1) y', LinearMap.mem_eqLocus.2 ?_, toInfinite_strandIncl y'⟩
      simp only [M, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        smul_eq_mul, jimboWeightedTrace_strandIncl, toInfinite_strandIncl, ih (n + 1) (by omega)]
      ring
    · obtain ⟨a', rfl⟩ := hsub a ha
      obtain ⟨b', rfl⟩ := hsub b hb
      have hT : toInfinite R q (n + 2) (T q (Fin.last n)) =
          InfiniteTypeAHeckeAlgebra.T q n := by simp
      refine ⟨strandIncl R q (n + 1) a' * T q (Fin.last n) * strandIncl R q (n + 1) b',
        LinearMap.mem_eqLocus.2 ?_, by simp [hT]⟩
      simp only [M, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        smul_eq_mul, map_mul, toInfinite_strandIncl, hT]
      rw [jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
        jimboWeightedTrace_strandIncl_mul_T_last, ih (n + 1) (by omega),
        hτ.map_mul_T_mul (hmem _ a') (hmem _ b'), ← map_mul]
      linear_combination δ ^ (n + 1) *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q (n + 1) (b' * a')) * hz.symm
  obtain ⟨y, hy, hyx⟩ := hP (hmem _ x)
  rw [← toInfinite_injective R q (n + 2) hyx]
  exact hy

/-- **The rescaled `N`-colour weighted Jimbo trace is the Ocneanu trace.** When `c * [N]_q = 1`,
multiplying `jimboWeightedTrace N q n` by `c ^ n` produces the restriction of `ocneanuTrace` with
parameter `c * q ^ N` along `toInfinite`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace N q n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  refine eq_ocneanuTrace_toInfinite (fun m ↦ c ^ m • jimboWeightedTrace N q m)
    (by simp) (fun m y ↦ ?_) (fun m y₁ y₂ ↦ ?_) (fun m y ↦ ?_) n x
  · simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl]
    linear_combination c ^ m * jimboWeightedTrace N q m y * hc
  · simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_mul_comm]
  · simp only [LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last]
    ring

/-- When `c * [N]_q = 1`, the `N`-colour weighted Jimbo trace on `n` strands is `[N]_q ^ n` times
the Ocneanu trace with parameter `c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace_toInfinite {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) :=
  jimboWeightedTrace_eq_pow_mul_ocneanuTrace_of_mul_eq
    (by linear_combination (↑(q ^ N) : R) * hc) n x

/-- On any `n`-strand braid, rescaling `KnotTheory.jimboWeightedTrace` by `c ^ n` where
`c * [N]_q = 1` recovers the Ocneanu trace of its universal Hecke image at `z = c * q ^ N`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace_braidHom {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) (b : BraidGroup n) :
    c ^ n * KnotTheory.jimboWeightedTrace (N := N) q b =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N))
        (InfiniteTypeAHeckeAlgebra.braidHom R q n b) := by
  simpa using mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite hc
    (braidHom R q n b : TypeAHeckeAlgebra R q n)

end Trace

end TauCeti.TypeAHeckeAlgebra
