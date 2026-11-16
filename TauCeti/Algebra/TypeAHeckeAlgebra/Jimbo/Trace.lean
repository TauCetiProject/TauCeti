/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Jimbo.Stabilization

/-!
# Turaev's weighted trace on the Jimbo representation of the Hecke algebra

The Jimbo representation `TauCeti.TypeAHeckeAlgebra.jimbo` carries the type-A Hecke algebra on
`n` strands to endomorphisms of the q-tensor space `(Fin n → Fin N) →₀ R`. Composing it with
right multiplication by Turaev's tensor-power enhancement `TauCeti.KnotTheory.jimboEnhancement q`
and Mathlib's module trace defines an `R`-linear functional
`TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace N q n` on `TypeAHeckeAlgebra R q n`.

Because the images of the braids span `TypeAHeckeAlgebra R q n` as an `R`-module
(`TauCeti.TypeAHeckeAlgebra.span_range_braidHom`), the intertwining, commutation, uncrossed-strand,
and Markov-stabilization identities for the braid representation in
`TauCeti.KnotTheory.Jimbo.StrandInclusion` and `TauCeti.KnotTheory.Jimbo.Stabilization` extend
by linearity to the full Hecke algebra:

* adding an uncrossed strand multiplies `jimboWeightedTrace N q n` by the quantum dimension
  `∑ a : Fin N, jimboWeight q a`;
* multiplying an included element by the last generator `T q (Fin.last n)` multiplies the weighted
  trace by `q ^ N`, and multiplying by its inverse multiplies the weighted trace by `(q⁻¹) ^ N`.

No division by `q - q⁻¹` or by the quantum dimension enters these identities, so they hold over
every commutative ring `R`, for every unit `q` (including `q = ±1`), and for every number of
colours `N` (including `N = 0`).

When the quantum dimension admits an inverse `c` in `R` (`c * ∑ a : Fin N, jimboWeight q a = 1`),
rescaling `jimboWeightedTrace N q n` by `c ^ n` produces a normalized Markov tower on the finite
Hecke algebras with Markov parameter `z = c * q ^ N`. By uniqueness of the Ocneanu trace
(`TauCeti.TypeAHeckeAlgebra.eq_ocneanuTrace_toInfinite`), this rescaled finite-colour trace agrees
with `InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * q ^ N)` restricted along `toInfinite`.
The universal Ocneanu trace on the full Hecke tower and the finite-colour weighted Jimbo trace
remain distinct objects: `ocneanuTrace` is defined for an arbitrary parameter `z : R`, whereas the
`N`-colour representation has a kernel in high strand counts and realizes the specialization
`z = c * q ^ N`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace`: Turaev's `R`-linear weighted trace on
  `TypeAHeckeAlgebra R q n` in the `N`-colour Jimbo representation.

## Main results

* `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_lmapDomain_snoc`,
  `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_single_snoc`, and
  `TauCeti.TypeAHeckeAlgebra.jimbo_strandIncl_single_snoc_apply_snoc`: appending a fixed colour
  intertwines `jimbo` along `strandIncl` for all strand counts `n`.
* `TauCeti.TypeAHeckeAlgebra.commute_jimboEnhancement_jimbo`: Turaev's enhancement commutes with
  the Hecke action on the q-tensor space.
* `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_T_last`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_strandIncl_mul_inv_unitT_last`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_T`, and
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_val_inv_unitT`: the uncrossed-strand,
  positive/negative stabilization, and generator evaluation laws on the Hecke algebra.
* `TauCeti.TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace`,
  `TauCeti.TypeAHeckeAlgebra.jimboWeightedTrace_eq_pow_mul_ocneanuTrace`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_braidHom_eq_mul_jimboWeightedTrace`, and
  `TauCeti.KnotTheory.jimboWeightedTrace_eq_pow_mul_ocneanuTrace_braidHom`: comparison with the
  Ocneanu trace at parameter `c * q ^ N` when `c` inverts the quantum dimension.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Sections 4–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

open Finsupp
open scoped BigOperators

namespace TauCeti

namespace TypeAHeckeAlgebra

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

section WeightedTrace

variable (N : ℕ) (q : Rˣ) (n : ℕ)

/-- Turaev's tensor-power enhancement commutes with every element of the Hecke algebra in the
`N`-colour Jimbo representation. -/
theorem commute_jimboEnhancement_jimbo {N n : ℕ} (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
    Commute (KnotTheory.jimboEnhancement (N := N) q) (jimbo (Fin N) q x) := by
  have hx : jimbo (Fin N) q x ∈ (jimbo (Fin N) q (n := n)).range := ⟨x, rfl⟩
  rw [← Algebra.map_top, ← adjoin_range_T, AlgHom.map_adjoin, ← Set.range_comp] at hx
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
  rintro _ ⟨i, rfl⟩
  simpa only [Function.comp_apply, jimbo_T] using
    KnotTheory.jimboEnhancement_commute_generator (N := N) q
      (BraidGroup.strand i) (BraidGroup.strandSucc i)

/-- **Turaev's weighted trace on the type-A Hecke algebra**: the `R`-linear functional
`x ↦ tr (jimbo (Fin N) q x * jimboEnhancement q)` on `TypeAHeckeAlgebra R q n`. -/
noncomputable def jimboWeightedTrace : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  (LinearMap.trace R ((Fin n → Fin N) →₀ R)).comp
    (LinearMap.mulRight R (KnotTheory.jimboEnhancement q) ∘ₗ (jimbo (Fin N) q (n := n)).toLinearMap)

/-- The defining formula for the weighted Jimbo trace on the Hecke algebra. -/
theorem jimboWeightedTrace_apply (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q) := (rfl)

/-- On the image of a braid, the Hecke weighted trace recovers `KnotTheory.jimboWeightedTrace`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b) =
      KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [jimboWeightedTrace_apply, jimbo_braidHom, KnotTheory.jimboWeightedTrace_def]

/-- The weighted trace of an element of the Hecke algebra is the sum of its diagonal matrix
coefficients in the word basis weighted by the products of colour weights. -/
theorem jimboWeightedTrace_eq_sum (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      ∑ w : Fin n → Fin N,
        jimbo (Fin N) q x (single w 1) w * ∏ i, KnotTheory.jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    mul_apply_eq_comp, Finsupp.coe_basisSingleOne, KnotTheory.jimboEnhancement_single_one,
    map_smul]
  simp [mul_comm]

/-- The weighted trace of `1` on `n` strands is the `n`-th power of the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_one :
    jimboWeightedTrace N q n 1 = (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  simpa using jimboWeightedTrace_braidHom N q n (1 : BraidGroup n)

/-- The weighted trace scales scalars by the `n`-th power of the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_algebraMap (r : R) :
    jimboWeightedTrace N q n (algebraMap R _ r) =
      r * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, jimboWeightedTrace_one, smul_eq_mul]

/-- The weighted Jimbo trace is tracial (`φ (x * y) = φ (y * x)`) on the Hecke algebra. -/
theorem jimboWeightedTrace_mul_comm {N n : ℕ} (q : Rˣ) (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  simp only [jimboWeightedTrace_apply, map_mul]
  rw [mul_assoc, ← (commute_jimboEnhancement_jimbo q y).eq, ← mul_assoc, LinearMap.trace_mul_cycle]

/-- **Adding an uncrossed strand multiplies the Hecke weighted trace by the quantum dimension.** -/
@[simp]
theorem jimboWeightedTrace_strandIncl (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q (n + 1) (strandIncl R q n x) =
      jimboWeightedTrace N q n x * ∑ a : Fin N, KnotTheory.jimboWeight q a := by
  rcases n with _ | m
  · obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (Nat.zero_le 1) x
    simp
  · have h := LinearMap.ext_on_range
      (span_range_braidHom (R := R) (q := q) (n := m + 1))
      (f := (jimboWeightedTrace N q (m + 2)).comp (strandIncl R q (m + 1)).toLinearMap)
      (g := LinearMap.mulRight R (∑ a : Fin N, KnotTheory.jimboWeight q a) ∘ₗ
        jimboWeightedTrace N q (m + 1))
      fun b ↦ by
        simp [← braidHom_strandIncl]
    exact LinearMap.congr_fun h x

/-- **Positive Markov stabilization on the Hecke algebra**: multiplying an element of the
`(n + 1)`-strand stage by the last generator `T q (Fin.last n)` multiplies the weighted trace
by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  let L : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    (jimboWeightedTrace N q (n + 2)).comp
      (LinearMap.mulRight R (T (n := n + 2) q (Fin.last n)) ∘ₗ (strandIncl R q (n + 1)).toLinearMap)
  let M : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    ↑(q ^ N) • jimboWeightedTrace N q (n + 1)
  have hLM : L = M := LinearMap.ext_on_range span_range_braidHom fun b ↦ by
    have hprod :
        strandIncl R q (n + 1) (braidHom R q (n + 1) b : TypeAHeckeAlgebra R q (n + 1)) *
            T (n := n + 2) q (Fin.last n) =
          braidHom R q (n + 2) (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) := by
      rw [map_mul, Units.val_mul, braidHom_strandIncl, braidHom_sigma, val_unitT]
    simp only [L, M, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      LinearMap.smul_apply, Units.smul_def, smul_eq_mul, hprod, jimboWeightedTrace_braidHom,
      KnotTheory.jimboWeightedTrace_stabilize]
  exact LinearMap.congr_fun hLM x

/-- **Negative Markov stabilization on the Hecke algebra**: multiplying an element of the
`(n + 1)`-strand stage by the inverse of the last generator multiplies the weighted trace by
`(q⁻¹) ^ N`. -/
theorem jimboWeightedTrace_strandIncl_mul_inv_unitT_last (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2)
        (strandIncl R q (n + 1) x *
          (↑(unitT (n := n + 2) q (Fin.last n))⁻¹ : TypeAHeckeAlgebra R q (n + 2))) =
      ↑((q⁻¹) ^ N) * jimboWeightedTrace N q (n + 1) x := by
  let L : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    (jimboWeightedTrace N q (n + 2)).comp
      (LinearMap.mulRight R
        (↑(unitT (n := n + 2) q (Fin.last n))⁻¹ : TypeAHeckeAlgebra R q (n + 2)) ∘ₗ
          (strandIncl R q (n + 1)).toLinearMap)
  let M : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    ↑((q⁻¹) ^ N) • jimboWeightedTrace N q (n + 1)
  have hLM : L = M := LinearMap.ext_on_range span_range_braidHom fun b ↦ by
    have hprod :
        strandIncl R q (n + 1) (braidHom R q (n + 1) b : TypeAHeckeAlgebra R q (n + 1)) *
            (↑(unitT (n := n + 2) q (Fin.last n))⁻¹ : TypeAHeckeAlgebra R q (n + 2)) =
          braidHom R q (n + 2) (BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹) := by
      rw [map_mul, map_inv, Units.val_mul, braidHom_strandIncl, braidHom_sigma]
    simp only [L, M, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      LinearMap.smul_apply, Units.smul_def, smul_eq_mul, hprod, jimboWeightedTrace_braidHom,
      KnotTheory.jimboWeightedTrace_stabilizeInv]
  exact LinearMap.congr_fun hLM x

/-- Every generator `T q i` on `n` strands has weighted trace `q ^ N * [N]_q ^ (n - 1)`. -/
@[simp]
theorem jimboWeightedTrace_T (i : Fin (n - 1)) :
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

/-- Every inverse generator `↑(unitT q i)⁻¹` on `n` strands has weighted trace
`(q⁻¹) ^ N * [N]_q ^ (n - 1)`. -/
theorem jimboWeightedTrace_val_inv_unitT (i : Fin (n - 1)) :
    jimboWeightedTrace N q n (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) =
      ↑((q⁻¹) ^ N) * (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ (n - 1) := by
  rcases n with _ | m
  · exact i.elim0
  · rw [val_inv_unitT, map_sub, jimboWeightedTrace_T, jimboWeightedTrace_algebraMap,
      Nat.add_sub_cancel, pow_succ', ← mul_assoc, KnotTheory.jimboWeight_sum]
    ring

end WeightedTrace

section OcneanuComparison

open InfiniteTypeAHeckeAlgebra

variable {N : ℕ} {q : Rˣ} {c : R}

/-- **Comparison of the finite-colour weighted Jimbo trace with the Ocneanu trace.** Whenever `c`
inverts the quantum dimension `∑ a : Fin N, jimboWeight q a` in `R`, multiplying the `N`-colour
weighted Jimbo trace on `n` strands by `c ^ n` recovers the Ocneanu trace with parameter
`c * q ^ N`. No invertibility of `q - q⁻¹` is assumed, so this also holds at `q = ±1` whenever
`±N` is invertible in `R`. -/
theorem mul_jimboWeightedTrace_eq_ocneanuTrace
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    c ^ n * jimboWeightedTrace N q n x =
      ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  let φ : ∀ m, TypeAHeckeAlgebra R q m →ₗ[R] R := fun m ↦ (c ^ m) • jimboWeightedTrace N q m
  refine eq_ocneanuTrace_toInfinite φ (by simp [φ]) (fun m y ↦ ?_) (fun m x y ↦ ?_)
    (fun m y ↦ ?_) n x
  · simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl, pow_succ]
    calc
      c ^ m * c * (jimboWeightedTrace N q m y * ∑ a : Fin N, KnotTheory.jimboWeight q a) =
          (c * ∑ a : Fin N, KnotTheory.jimboWeight q a) *
            (c ^ m * jimboWeightedTrace N q m y) := by ring
      _ = c ^ m * jimboWeightedTrace N q m y := by rw [hc, one_mul]
  · simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_mul_comm]
  · simp only [φ, LinearMap.smul_apply, smul_eq_mul, jimboWeightedTrace_strandIncl_mul_T_last,
      pow_succ]
    ring

/-- Unrescaled form of `mul_jimboWeightedTrace_eq_ocneanuTrace`: the `N`-colour weighted Jimbo
trace on `n` strands is the `n`-th power of the quantum dimension times the Ocneanu trace at
parameter `c * q ^ N`. -/
theorem jimboWeightedTrace_eq_pow_mul_ocneanuTrace
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      (∑ a : Fin N, KnotTheory.jimboWeight q a) ^ n *
        ocneanuTrace R q (c * ↑(q ^ N)) (toInfinite R q n x) := by
  rw [← mul_jimboWeightedTrace_eq_ocneanuTrace hc x, ← mul_assoc, ← mul_pow, mul_comm _ c, hc,
    one_pow, one_mul]

end OcneanuComparison

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}

/-- On the image of a braid on `n` strands in the infinite Hecke algebra, the Ocneanu trace at
`c * q ^ N` is `c ^ n` times Turaev's weighted Jimbo braid trace. -/
theorem ocneanuTrace_braidHom_eq_mul_jimboWeightedTrace
    (hc : c * ∑ a : Fin N, KnotTheory.jimboWeight q a = 1) {n : ℕ} (b : BraidGroup n) :
    ocneanuTrace R q (c * ↑(q ^ N)) (braidHom R q n b) =
      c ^ n * KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [← TypeAHeckeAlgebra.toInfinite_braidHom,
    ← TypeAHeckeAlgebra.mul_jimboWeightedTrace_eq_ocneanuTrace hc,
    TypeAHeckeAlgebra.jimboWeightedTrace_braidHom]

end InfiniteTypeAHeckeAlgebra

namespace KnotTheory

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

end KnotTheory

end TauCeti
