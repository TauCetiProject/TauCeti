/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import TauCeti.Algebra.TypeAHeckeAlgebra.BaseChange
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Basic

/-!
# Polynomiality and homogenization of the Ocneanu trace

For every element `x` of the infinite type-A Hecke algebra `TauCeti.InfiniteTypeAHeckeAlgebra R q`,
the Ocneanu trace `ocneanuTrace R q z x` depends polynomially on its Markov parameter `z`. Base
changing to the polynomial ring `R[X]` and evaluating at the indeterminate `Polynomial.X` defines
the linear map `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPoly`. Because the Ocneanu trace commutes
with change of coefficients (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_map`), evaluating
`ocneanuPoly R q x` at any element `s` of any `R`-algebra recovers the Ocneanu trace with
parameter `s` (`TauCeti.InfiniteTypeAHeckeAlgebra.aeval_ocneanuPoly`).

On the stage `stage R q (n + 1)` of the first `n + 1` strands, `ocneanuPoly R q x` has degree at
most `n` (`TauCeti.InfiniteTypeAHeckeAlgebra.natDegree_ocneanuPoly_le`): only `n` generators are
available to introduce new strands. Homogenizing `ocneanuPoly R q x` in degree `n` and evaluating
at `(w, δ)` therefore defines a regular two-parameter functional
`TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace R q w δ n` on the stage `n + 1`, with no
invertibility assumption on the loop factor `δ` or on `q - q⁻¹`. Adding an uncrossed strand
multiplies it by `δ`, multiplying by the positive crossing `T n` multiplies it by `w`, and
multiplying by `(T n)⁻¹` multiplies it by `w - (q - q⁻¹) * δ`.

Conversely, any tracial family on the positive-strand finite Hecke algebras satisfying these
uncrossed-strand and positive-crossing rules equals its one-strand value multiplied by
`homogenizedOcneanuTrace` (`TauCeti.TypeAHeckeAlgebra.eq_homogenizedOcneanuTrace_toInfinite`).
When `c * δ = 1`, rescaling by `c ^ n` recovers the Ocneanu trace at `z = c * w`
(`TauCeti.InfiniteTypeAHeckeAlgebra.mul_pow_homogenizedOcneanuTrace_eq_ocneanuTrace`).

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPoly`: the Ocneanu trace with indeterminate Markov
  parameter, valued in `R[X]`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace`: the degree-`n` homogenized Ocneanu
  trace at `(w, δ)`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_map`: naturality of the Ocneanu trace under
  coefficient change.
* `TauCeti.InfiniteTypeAHeckeAlgebra.aeval_ocneanuPoly` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.eval_ocneanuPoly`: specializing `ocneanuPoly` recovers
  `ocneanuTrace`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.natDegree_ocneanuPoly_le`: elements on `n + 1` strands have
  `z`-degree at most `n`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace_succ_of_mem_stage`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace_mul_T`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.homogenizedOcneanuTrace_mul_val_inv_unitT`: uncrossed-strand
  and positive/negative crossing rules for the homogenized trace.
* `TauCeti.TypeAHeckeAlgebra.eq_homogenizedOcneanuTrace_toInfinite`: uniqueness of two-parameter
  finite Markov towers.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5 (Theorem 5.1).
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Chapter 4 (Theorem 4.19).
-/

public section

open scoped Polynomial

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

/-- **Naturality of the Ocneanu trace.** Changing coefficients along an `R`-algebra `S` carries
the Ocneanu trace with parameter `z` to the Ocneanu trace with parameter `algebraMap R S z`. -/
theorem ocneanuTrace_map {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace S q' (algebraMap R S z) (map h x) =
      algebraMap R S (ocneanuTrace R q z x) := by
  let f : InfiniteTypeAHeckeAlgebra R q →ₗ[R] S :=
    (ocneanuTrace S q' (algebraMap R S z)).restrictScalars R ∘ₗ (map h).toLinearMap
  let g : InfiniteTypeAHeckeAlgebra R q →ₗ[R] S :=
    Algebra.linearMap R S ∘ₗ ocneanuTrace R q z
  have hτR := isMarkovTrace_ocneanuTrace (R := R) (q := q) z
  have hτS := isMarkovTrace_ocneanuTrace (R := S) (q := q') (algebraMap R S z)
  refine LinearMap.mem_eqLocus.1 <| Submodule.eq_top_iff'.1
    (eq_top_of_algebraMap_mem_of_mul_T_mul_mem (P := LinearMap.eqLocus f g)
      (fun r ↦ LinearMap.mem_eqLocus.2 ?_)
      (fun n ih a ha b hb ↦ LinearMap.mem_eqLocus.2 ?_)) x
  · simp only [f, g, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.linearMap_apply,
      IsScalarTower.algebraMap_apply R S (InfiniteTypeAHeckeAlgebra S q'),
      hτR.map_algebraMap, hτS.map_algebraMap]
  · have hab : f (b * a) = g (b * a) :=
      LinearMap.mem_eqLocus.1 (ih ((Subalgebra.mem_toSubmodule _).2 (mul_mem hb ha)))
    simp only [f, g, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, Algebra.linearMap_apply] at hab ⊢
    rw [_root_.map_mul (map h), _root_.map_mul (map h), map_T,
      hτS.map_mul_T_mul (map_mem_stage h ha) (map_mem_stage h hb),
      ← _root_.map_mul (map h), hab, hτR.map_mul_T_mul ha hb, ← _root_.map_mul (algebraMap R S)]

section OcneanuPoly

variable (R q) in
/-- **The Ocneanu polynomial** of an element of the infinite type-A Hecke algebra: the Ocneanu
trace over `R[X]` at the indeterminate Markov parameter `Polynomial.X`. Evaluating at `s` in any
`R`-algebra recovers the Ocneanu trace with parameter `s`
(`TauCeti.InfiniteTypeAHeckeAlgebra.aeval_ocneanuPoly`). -/
noncomputable def ocneanuPoly : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R[X] :=
  (ocneanuTrace R[X] (Units.map (algebraMap R R[X]).toMonoidHom q) Polynomial.X).restrictScalars
    R ∘ₗ (map (Units.coe_map (algebraMap R R[X]).toMonoidHom q).symm).toLinearMap

/-- Unfold `ocneanuPoly` to the Ocneanu trace over `R[X]` at `Polynomial.X`. -/
theorem ocneanuPoly_apply (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuPoly R q x =
      ocneanuTrace R[X] (Units.map (algebraMap R R[X]).toMonoidHom q) Polynomial.X
        (map (Units.coe_map (algebraMap R R[X]).toMonoidHom q).symm x) :=
  (rfl)

/-- Evaluating `ocneanuPoly` at `s` in any `R`-algebra `S` gives the Ocneanu trace with parameter
`s` on the base-changed algebra. -/
theorem aeval_ocneanuPoly {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (s : S) (x : InfiniteTypeAHeckeAlgebra R q) :
    Polynomial.aeval s (ocneanuPoly R q x) = ocneanuTrace S q' s (map h x) := by
  let _ : Algebra R[X] S := (Polynomial.aeval s).toRingHom.toAlgebra
  have halg (p : R[X]) : algebraMap R[X] S p = Polynomial.aeval s p := rfl
  have _ : IsScalarTower R R[X] S := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [halg, Polynomial.algebraMap_eq, Polynomial.aeval_C]
  have hq : algebraMap R[X] S (Units.map (algebraMap R R[X]).toMonoidHom q : R[X]) = q' := by
    simp [halg, h]
  have hX : algebraMap R[X] S (Polynomial.X : R[X]) = s := by
    rw [halg, Polynomial.aeval_X]
  have hm := (ocneanuTrace_map (R := R[X]) (S := S) hq Polynomial.X
    (map (Units.coe_map (algebraMap R R[X]).toMonoidHom q).symm x)).symm
  rwa [halg, hX, map_map] at hm

/-- Evaluating `ocneanuPoly` at `z : R` recovers the Ocneanu trace with parameter `z`. -/
@[simp]
theorem eval_ocneanuPoly (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    (ocneanuPoly R q x).eval z = ocneanuTrace R q z x := by
  simpa [Polynomial.aeval_def] using aeval_ocneanuPoly (S := R) (q' := q) rfl z x

/-- Mapping the coefficients of `ocneanuPoly` along an `R`-algebra `S` gives `ocneanuPoly` after
coefficient change. -/
theorem map_ocneanuPoly {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (x : InfiniteTypeAHeckeAlgebra R q) :
    (ocneanuPoly R q x).map (algebraMap R S) = ocneanuPoly S q' (map h x) := by
  have heq : (ocneanuPoly R q x).map (algebraMap R S) =
      Polynomial.aeval (Polynomial.X : S[X]) (ocneanuPoly R q x) := by
    rw [Polynomial.aeval_def, Polynomial.map]
    congr 1
  rw [heq, aeval_ocneanuPoly (S := S[X])
    (q' := Units.map (algebraMap S S[X]).toMonoidHom q')
    (by rw [IsScalarTower.algebraMap_apply R S S[X], h]; exact (Units.coe_map _ q').symm),
    ocneanuPoly_apply, map_map]

/-- The Ocneanu polynomial of `1` is `1`. -/
@[simp]
theorem ocneanuPoly_one : ocneanuPoly R q 1 = 1 := by
  rw [ocneanuPoly_apply, map_one, (isMarkovTrace_ocneanuTrace _).map_one]

/-- The Ocneanu polynomial of a scalar `r` is the constant polynomial `C r`. -/
@[simp]
theorem ocneanuPoly_algebraMap (r : R) :
    ocneanuPoly R q (algebraMap R _ r) = Polynomial.C r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ocneanuPoly_one, ← Algebra.algebraMap_eq_smul_one,
    Polynomial.algebraMap_eq]

/-- The Ocneanu polynomial is tracial. -/
theorem ocneanuPoly_mul_comm (x y : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuPoly R q (x * y) = ocneanuPoly R q (y * x) := by
  rw [ocneanuPoly_apply, ocneanuPoly_apply, _root_.map_mul (map _), _root_.map_mul (map _),
    (isMarkovTrace_ocneanuTrace _).map_mul_comm]

/-- Multiplying an element of the stage `n + 1` by `T n` multiplies its Ocneanu polynomial by
`Polynomial.X`. -/
theorem ocneanuPoly_mul_T {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) :
    ocneanuPoly R q (x * T q n) = Polynomial.X * ocneanuPoly R q x := by
  rw [ocneanuPoly_apply, ocneanuPoly_apply, _root_.map_mul (map _), map_T]
  exact (isMarkovTrace_ocneanuTrace _).map_mul_T (map_mem_stage _ hx)

/-- For `a` and `b` in the stage `n + 1`, `ocneanuPoly (a * T n * b) = X * ocneanuPoly (b * a)`. -/
theorem ocneanuPoly_mul_T_mul {n : ℕ} {a b : InfiniteTypeAHeckeAlgebra R q}
    (ha : a ∈ stage R q (n + 1)) (hb : b ∈ stage R q (n + 1)) :
    ocneanuPoly R q (a * T q n * b) = Polynomial.X * ocneanuPoly R q (b * a) := by
  rw [ocneanuPoly_mul_comm, ← mul_assoc, ocneanuPoly_mul_T (mul_mem hb ha)]

/-- Multiplying an element of the stage `n + 1` by `(T n)⁻¹` multiplies its Ocneanu polynomial by
`X - C (q - q⁻¹)`. -/
theorem ocneanuPoly_mul_val_inv_unitT {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) :
    ocneanuPoly R q (x * ↑(unitT q n)⁻¹) =
      (Polynomial.X - Polynomial.C ((q : R) - ↑q⁻¹)) * ocneanuPoly R q x := by
  rw [val_inv_unitT, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul,
    ocneanuPoly_mul_T hx, ← Polynomial.C_mul', ← sub_mul]

/-- Every generator `T i` has Ocneanu polynomial `X`. -/
@[simp]
theorem ocneanuPoly_T (i : ℕ) : ocneanuPoly R q (T q i) = Polynomial.X := by
  simpa only [one_mul, ocneanuPoly_one, mul_one] using
    ocneanuPoly_mul_T (one_mem (stage R q (i + 1)))

/-- The inverse of every generator has Ocneanu polynomial `X - C (q - q⁻¹)`. -/
theorem ocneanuPoly_val_inv_unitT (i : ℕ) :
    ocneanuPoly R q ↑(unitT q i)⁻¹ = Polynomial.X - Polynomial.C ((q : R) - ↑q⁻¹) := by
  simpa only [one_mul, ocneanuPoly_one, mul_one] using
    ocneanuPoly_mul_val_inv_unitT (one_mem (stage R q (i + 1)))

/-- The Ocneanu polynomial is multiplicative on disjoint blocks of strands. -/
theorem ocneanuPoly_mul_shift {a : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q a) (y : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuPoly R q (x * shift R q a y) = ocneanuPoly R q x * ocneanuPoly R q y := by
  rw [ocneanuPoly_apply, ocneanuPoly_apply, ocneanuPoly_apply, _root_.map_mul (map _), map_shift]
  exact (isMarkovTrace_ocneanuTrace _).map_mul_shift (map_mem_stage _ hx) _

/-- **Degree bound for the Ocneanu polynomial.** An element in the stage of the first `n + 1`
strands has Ocneanu polynomial of degree at most `n`. -/
theorem natDegree_ocneanuPoly_le {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) : (ocneanuPoly R q x).natDegree ≤ n := by
  induction n generalizing x with
  | zero =>
    rw [stage_eq_bot_of_le_one le_rfl, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [ocneanuPoly_algebraMap, Polynomial.natDegree_C]
  | succ n ih =>
    let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
      { carrier := {y | (ocneanuPoly R q y).natDegree ≤ n + 1}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb ↦ by
          dsimp at ha hb ⊢
          rw [map_add]
          exact (Polynomial.natDegree_add_le _ _).trans (max_le ha hb)
        smul_mem' := fun r _ ha ↦ by
          dsimp at ha ⊢
          rw [map_smul]
          exact (Polynomial.natDegree_smul_le r _).trans ha }
    have hP : Subalgebra.toSubmodule (stage R q (n + 2)) ≤ P := by
      refine toSubmodule_stage_add_two_le_iff.2 ⟨fun y hy ↦ (ih hy).trans n.le_succ,
        fun a ha b hb ↦ ?_⟩
      change (ocneanuPoly R q (a * T q n * b)).natDegree ≤ n + 1
      rw [ocneanuPoly_mul_T_mul ha hb, Nat.add_comm n 1]
      exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add Polynomial.natDegree_X_le (ih (mul_mem hb ha)))
    exact hP hx

end OcneanuPoly

section Homogenized

variable (R q) in
/-- **The two-parameter homogenized Ocneanu trace** in degree `n`: homogenize `ocneanuPoly R q x`
to a binary form of degree `n` and evaluate at `(w, δ)`. On the stage of the first `n + 1` strands,
`δ` is the uncrossed-strand factor and `w` is the positive-crossing contraction factor. -/
noncomputable def homogenizedOcneanuTrace (w δ : R) (n : ℕ) :
    InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
  (MvPolynomial.aeval ![w, δ]).toLinearMap ∘ₗ Polynomial.homogenizeLM n ∘ₗ ocneanuPoly R q

/-- Unfold `homogenizedOcneanuTrace` to evaluation of `(ocneanuPoly R q x).homogenize n` at
`![w, δ]`. -/
theorem homogenizedOcneanuTrace_apply (w δ : R) (n : ℕ) (x : InfiniteTypeAHeckeAlgebra R q) :
    homogenizedOcneanuTrace R q w δ n x =
      MvPolynomial.eval ![w, δ] ((ocneanuPoly R q x).homogenize n) :=
  (rfl)

/-- On `1`, the degree-`n` homogenized Ocneanu trace is `δ ^ n`. -/
@[simp]
theorem homogenizedOcneanuTrace_one (w δ : R) (n : ℕ) :
    homogenizedOcneanuTrace R q w δ n 1 = δ ^ n := by
  simp [homogenizedOcneanuTrace_apply]

/-- On a scalar `r`, the degree-`n` homogenized Ocneanu trace is `r * δ ^ n`. -/
@[simp]
theorem homogenizedOcneanuTrace_algebraMap (w δ : R) (n : ℕ) (r : R) :
    homogenizedOcneanuTrace R q w δ n (algebraMap R _ r) = r * δ ^ n := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, homogenizedOcneanuTrace_one, smul_eq_mul]

/-- The homogenized Ocneanu trace is tracial. -/
theorem homogenizedOcneanuTrace_mul_comm (w δ : R) (n : ℕ) (x y : InfiniteTypeAHeckeAlgebra R q) :
    homogenizedOcneanuTrace R q w δ n (x * y) = homogenizedOcneanuTrace R q w δ n (y * x) := by
  rw [homogenizedOcneanuTrace_apply, homogenizedOcneanuTrace_apply, ocneanuPoly_mul_comm]

/-- Naturality of the homogenized Ocneanu trace under coefficient change. -/
theorem map_homogenizedOcneanuTrace {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (w δ : R) (n : ℕ) (x : InfiniteTypeAHeckeAlgebra R q) :
    algebraMap R S (homogenizedOcneanuTrace R q w δ n x) =
      homogenizedOcneanuTrace S q' (algebraMap R S w) (algebraMap R S δ) n (map h x) := by
  have hpt : (⇑(algebraMap R S) ∘ ![w, δ]) = ![algebraMap R S w, algebraMap R S δ] := by
    ext i
    fin_cases i <;> simp
  rw [homogenizedOcneanuTrace_apply, homogenizedOcneanuTrace_apply, MvPolynomial.map_eval, hpt,
    ← Polynomial.homogenize_map, map_ocneanuPoly h]

/-- Raising the homogenization degree by one on an element of `stage R q (n + 1)` multiplies the
homogenized Ocneanu trace by the loop factor `δ`. -/
theorem homogenizedOcneanuTrace_succ_of_mem_stage (w δ : R) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    homogenizedOcneanuTrace R q w δ (n + 1) x = homogenizedOcneanuTrace R q w δ n x * δ := by
  have hm := Polynomial.homogenize_mul (ocneanuPoly R q x) 1 (natDegree_ocneanuPoly_le hx)
    (by simp : (1 : R[X]).natDegree ≤ 1)
  rw [mul_one, Polynomial.homogenize_one, pow_one] at hm
  simp [homogenizedOcneanuTrace_apply, hm]

/-- Multiplying an element of `stage R q (n + 1)` by the positive crossing `T n` multiplies the
homogenized Ocneanu trace by `w`. -/
theorem homogenizedOcneanuTrace_mul_T (w δ : R) {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) :
    homogenizedOcneanuTrace R q w δ (n + 1) (x * T q n) =
      w * homogenizedOcneanuTrace R q w δ n x := by
  have hm := Polynomial.homogenize_mul (Polynomial.X : R[X]) (ocneanuPoly R q x)
    Polynomial.natDegree_X_le (natDegree_ocneanuPoly_le hx)
  rw [Nat.add_comm 1 n, Polynomial.homogenize_X one_ne_zero] at hm
  simp [homogenizedOcneanuTrace_apply, ocneanuPoly_mul_T hx, hm]

/-- For `a` and `b` in `stage R q (n + 1)`, multiplying by the new crossing `T n` between `a` and
`b` contracts to `w` times the homogenized trace of `b * a`. -/
theorem homogenizedOcneanuTrace_mul_T_mul (w δ : R) {n : ℕ}
    {a b : InfiniteTypeAHeckeAlgebra R q} (ha : a ∈ stage R q (n + 1))
    (hb : b ∈ stage R q (n + 1)) :
    homogenizedOcneanuTrace R q w δ (n + 1) (a * T q n * b) =
      w * homogenizedOcneanuTrace R q w δ n (b * a) := by
  rw [homogenizedOcneanuTrace_mul_comm, ← mul_assoc,
    homogenizedOcneanuTrace_mul_T w δ (mul_mem hb ha)]

/-- Multiplying an element of `stage R q (n + 1)` by `(T n)⁻¹` multiplies the homogenized Ocneanu
trace by `w - (q - q⁻¹) * δ`. -/
theorem homogenizedOcneanuTrace_mul_val_inv_unitT (w δ : R) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    homogenizedOcneanuTrace R q w δ (n + 1) (x * ↑(unitT q n)⁻¹) =
      (w - ((q : R) - ↑q⁻¹) * δ) * homogenizedOcneanuTrace R q w δ n x := by
  have hm := Polynomial.homogenize_mul (Polynomial.X - Polynomial.C ((q : R) - ↑q⁻¹))
    (ocneanuPoly R q x) (Polynomial.natDegree_X_sub_C_le _) (natDegree_ocneanuPoly_le hx)
  rw [Nat.add_comm 1 n, Polynomial.homogenize_sub, Polynomial.homogenize_X one_ne_zero,
    Polynomial.homogenize_C] at hm
  rw [homogenizedOcneanuTrace_apply, ocneanuPoly_mul_val_inv_unitT hx, hm]
  simp [homogenizedOcneanuTrace_apply]

/-- When `w = δ * z`, the degree-`n` homogenized Ocneanu trace on `stage R q (n + 1)` is `δ ^ n`
times the Ocneanu trace with parameter `z`. -/
theorem homogenizedOcneanuTrace_const_mul (z δ : R) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    homogenizedOcneanuTrace R q (δ * z) δ n x = δ ^ n * ocneanuTrace R q z x := by
  have hsmul : (![δ * z, δ] : Fin 2 → R) = δ • ![z, 1] := by
    ext i
    fin_cases i <;> simp
  rw [homogenizedOcneanuTrace_apply, hsmul,
    (Polynomial.isHomogeneous_homogenize _).eval_smul, ← MvPolynomial.aeval_eq_eval,
    Polynomial.aeval_homogenize_of_eq_one (natDegree_ocneanuPoly_le hx) _ (by simp),
    Matrix.cons_val_zero, aeval_ocneanuPoly rfl, map_id, AlgHom.id_apply]

/-- When `c * δ = 1`, rescaling the degree-`n` homogenized Ocneanu trace on `stage R q (n + 1)` by
`c ^ n` recovers the Ocneanu trace with parameter `c * w`. -/
theorem mul_pow_homogenizedOcneanuTrace_eq_ocneanuTrace {c w δ : R} (hc : c * δ = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    c ^ n * homogenizedOcneanuTrace R q w δ n x = ocneanuTrace R q (c * w) x := by
  have hsmul : c • (![w, δ] : Fin 2 → R) = ![c * w, 1] := by
    ext i
    fin_cases i <;> simp [hc]
  rw [homogenizedOcneanuTrace_apply, ← (Polynomial.isHomogeneous_homogenize _).eval_smul, hsmul,
    ← MvPolynomial.aeval_eq_eval,
    Polynomial.aeval_homogenize_of_eq_one (natDegree_ocneanuPoly_le hx) _ (by simp),
    Matrix.cons_val_zero, aeval_ocneanuPoly rfl, map_id, AlgHom.id_apply]

end Homogenized

end InfiniteTypeAHeckeAlgebra

namespace TypeAHeckeAlgebra

open InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

/-- Naturality of the Ocneanu trace on the finite type-A Hecke algebras along an `R`-algebra `S`. -/
theorem ocneanuTrace_toInfinite_map {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (h : algebraMap R S q = q') (z : R) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    ocneanuTrace S q' (algebraMap R S z) (toInfinite S q' n (map n h x)) =
      algebraMap R S (ocneanuTrace R q z (toInfinite R q n x)) := by
  rw [toInfinite_map, ocneanuTrace_map]

/-- **Two-parameter finite Markov towers factor through the homogenized Ocneanu trace.** Let
`ψ n` be a family of `R`-linear functionals on `TypeAHeckeAlgebra R q (n + 1)` which is tracial at
each level, multiplied by `δ` under `strandIncl`, and multiplied by `w` when multiplied by the last
generator `T (Fin.last n)`. Then `ψ n` equals `ψ 0 1` times the degree-`n` homogenized Ocneanu
trace at `(w, δ)`, with no invertibility assumption on `δ` or `q - q⁻¹`. -/
theorem eq_homogenizedOcneanuTrace_toInfinite {w δ : R}
    (ψ : ∀ n, TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R)
    (h_incl : ∀ n x, ψ (n + 1) (strandIncl R q (n + 1) x) = ψ n x * δ)
    (h_comm : ∀ n x y, ψ n (x * y) = ψ n (y * x))
    (h_markov : ∀ n x, ψ (n + 1) (strandIncl R q (n + 1) x * T q (Fin.last n)) = w * ψ n x)
    (n : ℕ) (x : TypeAHeckeAlgebra R q (n + 1)) :
    ψ n x = ψ 0 1 * homogenizedOcneanuTrace R q w δ n (toInfinite R q (n + 1) x) := by
  have hmem (m : ℕ) (y : TypeAHeckeAlgebra R q m) : toInfinite R q m y ∈ stage R q m := by
    rw [← range_toInfinite]
    exact ⟨y, rfl⟩
  induction n with
  | zero =>
    obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one le_rfl x
    rw [AlgHom.commutes, homogenizedOcneanuTrace_algebraMap, pow_zero, mul_one,
      Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
  | succ n ih =>
    let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
      (LinearMap.eqLocus (ψ (n + 1))
        ((ψ 0 1 • homogenizedOcneanuTrace R q w δ (n + 1)).comp
          (toInfinite R q (n + 2)).toLinearMap)).map (toInfinite R q (n + 2)).toLinearMap
    have hsub (y : InfiniteTypeAHeckeAlgebra R q) (hy : y ∈ stage R q (n + 1)) :
        ∃ y' : TypeAHeckeAlgebra R q (n + 1), toInfinite R q (n + 1) y' = y := by
      rw [← range_toInfinite] at hy
      exact hy
    have hP : Subalgebra.toSubmodule (stage R q (n + 2)) ≤ P := by
      refine toSubmodule_stage_add_two_le_iff.2 ⟨fun y hy ↦ ?_, fun a ha b hb ↦ ?_⟩
      · obtain ⟨y', rfl⟩ := hsub y hy
        refine ⟨strandIncl R q (n + 1) y', LinearMap.mem_eqLocus.2 ?_, toInfinite_strandIncl y'⟩
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
          smul_eq_mul, h_incl, toInfinite_strandIncl, ih y',
          homogenizedOcneanuTrace_succ_of_mem_stage w δ (hmem (n + 1) y'), mul_assoc]
      · obtain ⟨a', rfl⟩ := hsub a ha
        obtain ⟨b', rfl⟩ := hsub b hb
        have hT : toInfinite R q (n + 2) (T q (Fin.last n)) = InfiniteTypeAHeckeAlgebra.T q n := by
          simp
        refine ⟨strandIncl R q (n + 1) a' * T q (Fin.last n) * strandIncl R q (n + 1) b',
          LinearMap.mem_eqLocus.2 ?_, by simp [hT]⟩
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
          smul_eq_mul, map_mul, toInfinite_strandIncl, hT]
        rw [h_comm, ← mul_assoc, ← map_mul, h_markov, ih (b' * a'),
          homogenizedOcneanuTrace_mul_T_mul w δ (hmem _ a') (hmem _ b'), map_mul, mul_left_comm]
    obtain ⟨y, hy, hyx⟩ := hP (hmem _ x)
    rw [← toInfinite_injective R q (n + 2) hyx]
    exact LinearMap.mem_eqLocus.1 hy

end TypeAHeckeAlgebra

end TauCeti
