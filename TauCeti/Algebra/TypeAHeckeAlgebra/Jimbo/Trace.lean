/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Jimbo.Stabilization
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
adding an uncrossed strand multiplies it by `[N]_q`. Because the images of `n`-strand braids span
`TypeAHeckeAlgebra R q n`, the braid-level strand-inclusion and positive/negative Markov
stabilization identities lift to arbitrary Hecke algebra elements: multiplying `strandIncl x` by
the last generator `T (Fin.last n)` multiplies the trace by `q ^ N`, while multiplying by
`(unitT (Fin.last n))⁻¹` multiplies it by `(q⁻¹) ^ N`.

Whenever `[N]_q` has an inverse `c` (`c * [N]_q = 1`), rescaling `jimboWeightedTrace N q n` by
`c ^ n` produces a normalized finite Markov tower and therefore agrees with
`ocneanuTrace R q (c * q ^ N)` along `toInfinite` (and on every `n`-strand braid), with no
invertibility assumption on `q - q⁻¹`.

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
* `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_pow_mul_ocneanuTrace_toInfinite`, and
  `TauCeti.KnotTheory.mul_jimboWeightedTrace_eq_ocneanuTrace_braidHom`: comparison with the
  universal Ocneanu trace when `[N]_q` is invertible.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Section 5.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* The Hecke representation intertwining, weighted-trace, and stabilization arguments follow
  `TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic` and
  `TauCeti.KnotTheory.Jimbo.Stabilization`.
-/

public section

open Function Finsupp

namespace TauCeti

namespace TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

section Representation

variable (ι) [LinearOrder ι] (q : Rˣ)

/-- The Jimbo action of an element after adding an uncrossed last strand is its original action
with the last colour held fixed. -/
@[simp]
theorem jimbo_strandIncl_mapDomain_snoc (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.snoc w a : Fin (n + 1) → ι))
  suffices h : ((jimbo ι q).comp (strandIncl R q n) x).comp L = L.comp (jimbo ι q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine comp_eq_of_forall_T (jimbo ι q) ((jimbo ι q).comp (strandIncl R q n)) L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).castSucc := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).castSucc := Fin.ext (by simp)
  rw [AlgHom.comp_apply, strandIncl_T, jimbo_T, jimbo_T, hj, hk,
    KnotTheory.jimboGenerator_comp_lmapDomain_snoc]

end Representation

section Trace

/-- Turaev's tensor-power enhancement commutes with every element in the `N`-colour Jimbo
representation of the type-A Hecke algebra. -/
theorem commute_jimboEnhancement_jimbo (N : ℕ) (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
    Commute (KnotTheory.jimboEnhancement (N := N) q) (jimbo (Fin N) q x) :=
  commute_of_forall_T (jimbo (Fin N) q)
    (fun i ↦ by
      simpa only [jimbo_T] using KnotTheory.jimboEnhancement_commute_generator (N := N) q
        (BraidGroup.strand i) (BraidGroup.strandSucc i))
    x

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
  set g : TypeAHeckeAlgebra R q n →ₗ[R] R :=
    ∑ w : Fin n → Fin N,
      LinearMap.mulRight R (∏ i, KnotTheory.jimboWeight q (w i)) ∘ₗ
        Finsupp.lapply w ∘ₗ LinearMap.applyₗ (single w (1 : R)) ∘ₗ (jimbo (Fin N) q).toLinearMap
  have hfg : jimboWeightedTrace N q n = g :=
    LinearMap.ext_on_range span_range_braidHom fun b ↦ by
      simp [g, KnotTheory.jimboWeightedTrace_eq_sum, mul_comm]
  simpa [g, mul_comm] using LinearMap.congr_fun hfg x

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
  cases n with
  | zero =>
    obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (Nat.zero_le 1) x
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul,
      map_smul, jimboWeightedTrace_one, jimboWeightedTrace_one, pow_zero, pow_one, smul_eq_mul,
      smul_eq_mul, mul_one]
  | succ m =>
    have hfg : jimboWeightedTrace N q (m + 2) ∘ₗ (strandIncl R q (m + 1)).toLinearMap =
        LinearMap.mulRight R (∑ a : Fin N, KnotTheory.jimboWeight q a) ∘ₗ
          jimboWeightedTrace N q (m + 1) :=
      LinearMap.ext_on_range span_range_braidHom fun b ↦ by
        simp [← braidHom_strandIncl, mul_comm]
    simpa [mul_comm] using LinearMap.congr_fun hfg x

/-- **Positive Markov stabilization for `jimboWeightedTrace`.** Multiplying an element included from
the first `n + 1` strands by the last generator `T (Fin.last n)` multiplies the `N`-colour weighted
trace by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  have hfg : jimboWeightedTrace N q (n + 2) ∘ₗ
      LinearMap.mulRight R (T (n := n + 2) q (Fin.last n)) ∘ₗ
        (strandIncl R q (n + 1)).toLinearMap =
          (↑(q ^ N) : R) • jimboWeightedTrace N q (n + 1) :=
    LinearMap.ext_on_range span_range_braidHom fun b ↦ by
      have hb : strandIncl R q (n + 1) (braidHom R q (n + 1) b) *
          T (n := n + 2) q (Fin.last n) =
            braidHom R q (n + 2) (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) := by
        simp
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hb, jimboWeightedTrace_braidHom, KnotTheory.jimboWeightedTrace_stabilize,
        jimboWeightedTrace_braidHom]
  simpa using LinearMap.congr_fun hfg x

/-- **Negative Markov stabilization for `jimboWeightedTrace`.** Multiplying an element included from
the first `n + 1` strands by the inverse of the last generator `(unitT (Fin.last n))⁻¹` multiplies
the `N`-colour weighted trace by `(q⁻¹) ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_val_inv_unitT_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x * ↑(unitT (n := n + 2) q (Fin.last n))⁻¹) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace N q (n + 1) x := by
  have hfg : jimboWeightedTrace N q (n + 2) ∘ₗ
      LinearMap.mulRight R ↑(unitT (n := n + 2) q (Fin.last n))⁻¹ ∘ₗ
        (strandIncl R q (n + 1)).toLinearMap =
          (↑((q⁻¹) ^ N) : R) • jimboWeightedTrace N q (n + 1) :=
    LinearMap.ext_on_range span_range_braidHom fun b ↦ by
      have hb : strandIncl R q (n + 1) (braidHom R q (n + 1) b) *
          ↑(unitT (n := n + 2) q (Fin.last n))⁻¹ =
            braidHom R q (n + 2)
              (BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹) := by
        simp only [map_mul, map_inv, Units.val_mul, braidHom_strandIncl, braidHom_sigma]
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hb, jimboWeightedTrace_braidHom, KnotTheory.jimboWeightedTrace_stabilizeInv,
        jimboWeightedTrace_braidHom]
  simpa using LinearMap.congr_fun hfg x

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
  obtain _ | m := n
  · exact i.elim0
  · rw [val_inv_unitT, map_sub, Algebra.algebraMap_eq_smul_one, map_smul, jimboWeightedTrace_T,
      jimboWeightedTrace_one, smul_eq_mul]
    have hs := KnotTheory.jimboWeight_sum (N := N) q
    simp only [Nat.add_sub_cancel, pow_succ']
    linear_combination -(∑ a : Fin N, KnotTheory.jimboWeight q a) ^ m * hs

/-! ### Comparison with the universal Ocneanu trace -/

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
        InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  rw [← mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite hc, ← mul_assoc, ← mul_pow,
    mul_comm _ c, hc, one_pow, one_mul]

end Trace

end TypeAHeckeAlgebra

namespace KnotTheory

/-- On any `n`-strand braid, rescaling `KnotTheory.jimboWeightedTrace` by `c ^ n` where
`c * [N]_q = 1` recovers the Ocneanu trace of its universal Hecke image at `z = c * q ^ N`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace_braidHom {R : Type*} [CommRing R] {N n : ℕ}
    {q : Rˣ} {c : R} (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (b : BraidGroup n) :
    c ^ n * jimboWeightedTrace (N := N) q b =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * ↑(q ^ N))
        (InfiniteTypeAHeckeAlgebra.braidHom R q n b) := by
  simpa using TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace_toInfinite hc
    (TypeAHeckeAlgebra.braidHom R q n b : TypeAHeckeAlgebra R q n)

end KnotTheory

end TauCeti
