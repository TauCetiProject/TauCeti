/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Jimbo.Trace
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
import TauCeti.KnotTheory.Jimbo.Stabilization
import Mathlib.Tactic.LinearCombination

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
Ocneanu trace on the full Hecke tower. Conjugating by order reversal on the alphabet and twisting
by `TypeAHeckeAlgebra.negEquiv` identifies `jimbo` and `jimboWeightedTrace` with the all-positive
atomic model in `TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic`, supplying strand-inclusion
compatibility, commutativity with the enhancement, traciality, and the uncrossed-strand rule.
Positive Markov stabilization extends `TauCeti.KnotTheory.jimboWeightedTrace_stabilize` linearly
along `TypeAHeckeAlgebra.span_range_braidHom`, and negative stabilization follows from the
quadratic relation and `KnotTheory.jimboWeight_sum`.

When the quantum dimension admits an inverse `c` in `R`, normalizing `jimboWeightedTrace N q n` by
`c ^ n` produces a compatible Markov tower of traces with parameter `c * q ^ N`, which agrees with
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace` restricted along `toInfinite`
(`TauCeti.TypeAHeckeAlgebra.pow_mul_jimboWeightedTrace_eq_ocneanuTrace`).

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
* `TauCeti.TypeAHeckeAlgebra.pow_mul_jimboWeightedTrace_eq_ocneanuTrace`: normalizing by an inverse
  of the quantum dimension identifies the finite-colour trace with the Ocneanu trace.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*,
  Lett. Math. Phys. 11 (1986), 247–252.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.

The strand-inclusion and trace properties are transported from the atomic model in
`TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic`, and the stabilization law extends
`TauCeti.KnotTheory.jimboWeightedTrace_stabilize` linearly along `span_range_braidHom`.
-/

public section

open Function Finsupp
open scoped BigOperators

namespace TauCeti.TypeAHeckeAlgebra

section StrandInclusion

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

/-- Relabelling words by reversing the order of the alphabet. -/
private noncomputable abbrev dualWordEquiv (R : Type*) [CommRing R] (ι : Type*) (n : ℕ) :
    ((Fin n → ι) →₀ R) ≃ₗ[R] ((Fin n → ιᵒᵈ) →₀ R) :=
  Finsupp.domLCongr (Equiv.arrowCongr (Equiv.refl (Fin n)) OrderDual.toDual)

private theorem dualWordEquiv_single (w : Fin n → ι) (c : R) :
    dualWordEquiv R ι n (single w c) = single (OrderDual.toDual ∘ w) c := by
  rw [dualWordEquiv, domLCongr_single]
  refine congrArg (single · c) (funext fun i ↦ ?_)
  simp

private theorem dualWordEquiv_symm_single (w : Fin n → ιᵒᵈ) (c : R) :
    (dualWordEquiv R ι n).symm (single w c) = single (OrderDual.ofDual ∘ w) c := by
  rw [LinearEquiv.symm_apply_eq, dualWordEquiv_single]
  refine congrArg (single · c) (funext fun i ↦ ?_)
  simp

private theorem dualWordEquiv_apply_comp (v : (Fin n → ι) →₀ R) (u : Fin n → ι) :
    dualWordEquiv R ι n v (OrderDual.toDual ∘ u) = v u := by
  have hu : Equiv.arrowCongr (Equiv.refl (Fin n)) OrderDual.toDual u = OrderDual.toDual ∘ u := by
    ext i
    simp
  rw [← hu, dualWordEquiv, domLCongr_apply, domCongr_apply, equivMapDomain_apply,
    Equiv.symm_apply_apply]

private theorem dualWordEquiv_mapDomain_snoc (a : ι) (v : (Fin n → ι) →₀ R) :
    dualWordEquiv R ι (n + 1) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w (OrderDual.toDual a)) (dualWordEquiv R ι n v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ hv₁ hv₂ => simp only [mapDomain_add, map_add, hv₁, hv₂]
  | single w c =>
    rw [mapDomain_single, dualWordEquiv_single, dualWordEquiv_single, mapDomain_single]
    refine congrArg (single · c) (funext fun i ↦ ?_)
    refine Fin.lastCases ?_ ?_ i <;> simp

private theorem negEquiv_strandIncl (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
    negEquiv R q (n + 1) (strandIncl R q n x) = strandIncl R (-q) n (negEquiv R q n x) := by
  have h : (negEquiv R q (n + 1)).toAlgHom.comp (strandIncl R q n) =
      (strandIncl R (-q) n).comp (negEquiv R q n).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

variable [LinearOrder ι]

/-- Twisting by `negEquiv` and reversing the order of the alphabet identifies `jimbo` with the
all-positive `signedChecked` representation at `-q`. -/
private theorem signedChecked_negEquiv (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
    signedChecked (fun _ : ιᵒᵈ ↦ True) (-q) (negEquiv R q n x) =
      (dualWordEquiv R ι n).conjAlgEquiv R (jimbo ι q x) := by
  have hcomp :
      (signedChecked (fun _ : ιᵒᵈ ↦ True) (-q)).comp (negEquiv R q n).toAlgHom =
        ((dualWordEquiv R ι n).conjAlgEquiv R).toAlgHom.comp (jimbo ι q) := by
    refine hom_ext fun i ↦ ?_
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, negEquiv_T, map_neg, signedChecked_T,
      jimbo_T]
    have hgen := signedCheckedR_eq_jimboGenerator (R := R) (ι := ιᵒᵈ) (n := n)
      (pos := fun _ ↦ True) (s := -q) (fun _ ↦ trivial)
      (BraidGroup.strand i) (BraidGroup.strandSucc i)
    rw [hgen, map_smul, smul_smul, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.symm_conj_apply]
    simp only [Units.val_neg, inv_neg, neg_mul, neg_neg, Units.inv_mul]
    rw [OrderDual.instLinearOrder.dual_dual ι]
    ext w : 2
    simp only [LinearMap.neg_apply, LinearMap.smul_apply, neg_smul, one_smul, neg_neg,
      LinearMap.comp_apply, lsingle_apply, LinearEquiv.coe_coe,
      Finsupp.domLCongr_symm, Finsupp.domLCongr_single, dualWordEquiv]
    -- `OrderDual` is a type synonym (`ιᵒᵈᵒᵈ = ι` definitionally, with `toDual`/`ofDual`
    -- definitionally `Equiv.refl`), so `domLCongr` for `ιᵒᵈ ≃ ιᵒᵈᵒᵈ` is definitionally
    -- `(dualWordEquiv R ι n).symm`.
    rfl
  exact AlgHom.congr_fun hcomp x

private theorem dualWordEquiv_jimbo (q : Rˣ) (x : TypeAHeckeAlgebra R q n)
    (v : (Fin n → ι) →₀ R) :
    dualWordEquiv R ι n (jimbo ι q x v) =
      signedChecked (fun _ : ιᵒᵈ ↦ True) (-q) (negEquiv R q n x) (dualWordEquiv R ι n v) := by
  have h := LinearMap.congr_fun (signedChecked_negEquiv q x) (dualWordEquiv R ι n v)
  rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- Adding an uncrossed last strand via `strandIncl` acts in the Jimbo representation on any
number of strands with the last colour held fixed. -/
@[simp]
theorem jimbo_strandIncl_mapDomain_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    jimbo ι q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (jimbo ι q x v) := by
  apply (dualWordEquiv R ι (n + 1)).injective
  rw [dualWordEquiv_jimbo, negEquiv_strandIncl, dualWordEquiv_mapDomain_snoc,
    signedChecked_strandIncl_mapDomain_snoc, ← dualWordEquiv_jimbo, ← dualWordEquiv_mapDomain_snoc]

/-- Basis-vector form of compatibility of `jimbo` with `strandIncl`. -/
@[simp]
theorem jimbo_strandIncl_single_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) (a : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) =
      mapDomain (fun u ↦ Fin.snoc u a) (jimbo ι q x (single w c)) := by
  simpa only [mapDomain_single] using jimbo_strandIncl_mapDomain_snoc q x a (single w c)

/-- Under `strandIncl`, the Jimbo action preserves matrix coefficients on each fixed-last-colour
block and has zero coefficients between blocks with different last colours. -/
@[simp↓]
theorem jimbo_strandIncl_single_snoc_apply_snoc (q : Rˣ) (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) (c : R) :
    jimbo ι q (strandIncl R q n x) (single (Fin.snoc w a) c) (Fin.snoc u d) =
      if a = d then jimbo ι q x (single w c) u else 0 := by
  have hcoeff {m : ℕ} (y : TypeAHeckeAlgebra R q m) (w' u' : Fin m → ι) :
      jimbo ι q y (single w' 1) u' =
        signedChecked (fun _ : ιᵒᵈ ↦ True) (-q) (negEquiv R q m y)
          (single (OrderDual.toDual ∘ w') 1) (OrderDual.toDual ∘ u') := by
    rw [← dualWordEquiv_apply_comp, dualWordEquiv_jimbo, dualWordEquiv_single]
  have hsnoc (v : Fin n → ι) (b : ι) :
      OrderDual.toDual ∘ Fin.snoc v b = Fin.snoc (OrderDual.toDual ∘ v) (OrderDual.toDual b) := by
    ext i
    refine Fin.lastCases ?_ ?_ i <;> simp
  have h1 (m : ℕ) (v : Fin m → ι) : single v c = c • single v 1 := by simp
  rw [h1 (n + 1), h1 n, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply,
    hcoeff, hcoeff, negEquiv_strandIncl, hsnoc, hsnoc,
    signedChecked_strandIncl_single_snoc_apply_snoc]
  simp

end StrandInclusion

section CommRing

variable {R : Type*} [CommRing R] {N n : ℕ}

private theorem dualWordEquiv_conj_jimboEnhancement (q : Rˣ) :
    (dualWordEquiv R (Fin N) n).conjAlgEquiv R (KnotTheory.jimboEnhancement q) =
      productDensity (KnotTheory.jimboWeight q ∘ OrderDual.ofDual) := by
  ext w : 2
  rw [LinearMap.comp_apply, lsingle_apply, LinearMap.comp_apply, lsingle_apply,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, dualWordEquiv_symm_single,
    KnotTheory.jimboEnhancement_single_one, map_smul, dualWordEquiv_single,
    productDensity_single_one]
  refine congrArg ((∏ i, KnotTheory.jimboWeight q (OrderDual.ofDual (w i))) • single · 1)
    (funext fun i ↦ ?_)
  simp

/-- Turaev's tensor-power enhancement commutes with every element of the finite Hecke algebra in
the Jimbo representation. -/
theorem commute_jimboEnhancement_jimbo (N : ℕ) (q : Rˣ) (x : TypeAHeckeAlgebra R q n) :
    Commute (KnotTheory.jimboEnhancement (N := N) q) (jimbo (Fin N) q x) := by
  have h := commute_productDensity_signedChecked (fun _ : (Fin N)ᵒᵈ ↦ True) (-q)
    (KnotTheory.jimboWeight q ∘ OrderDual.ofDual) (negEquiv R q n x)
  rw [← dualWordEquiv_conj_jimboEnhancement, signedChecked_negEquiv] at h
  have h' := h.map ((dualWordEquiv R (Fin N) n).conjAlgEquiv R).symm
  simpa using h'

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

/-- Under `negEquiv` and alphabet reversal, `jimboWeightedTrace` coincides with `atomicTrace`. -/
private theorem jimboWeightedTrace_eq_atomicTrace (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n x =
      atomicTrace (fun _ : (Fin N)ᵒᵈ ↦ True) (-q)
        (KnotTheory.jimboWeight q ∘ OrderDual.ofDual) n (negEquiv R q n x) := by
  rw [jimboWeightedTrace_apply, atomicTrace_apply, signedChecked_negEquiv,
    ← dualWordEquiv_conj_jimboEnhancement, ← map_mul, LinearEquiv.conjAlgEquiv_apply]
  exact (LinearMap.trace_conj' (jimbo (Fin N) q x * KnotTheory.jimboEnhancement q)
    (dualWordEquiv R (Fin N) n)).symm

/-- The weighted braid trace factors through `jimboWeightedTrace` along `braidHom`. -/
@[simp]
theorem jimboWeightedTrace_braidHom (N : ℕ) (q : Rˣ) (n : ℕ) (b : BraidGroup n) :
    jimboWeightedTrace N q n (braidHom R q n b) = KnotTheory.jimboWeightedTrace (N := N) q b := by
  rw [jimboWeightedTrace_apply, jimbo_braidHom, KnotTheory.jimboWeightedTrace_def]

/-- The `N`-colour Jimbo weighted trace is tracial on `TypeAHeckeAlgebra R q n`. -/
theorem jimboWeightedTrace_mul_comm (N : ℕ) (q : Rˣ) (n : ℕ) (x y : TypeAHeckeAlgebra R q n) :
    jimboWeightedTrace N q n (x * y) = jimboWeightedTrace N q n (y * x) := by
  rw [jimboWeightedTrace_eq_atomicTrace, jimboWeightedTrace_eq_atomicTrace,
    _root_.map_mul (negEquiv R q n), _root_.map_mul (negEquiv R q n), atomicTrace_mul_comm]

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
  rw [jimboWeightedTrace_eq_atomicTrace, negEquiv_strandIncl, atomicTrace_strandIncl,
    ← jimboWeightedTrace_eq_atomicTrace]
  exact congrArg (jimboWeightedTrace N q n x * ·)
    (Fintype.sum_equiv OrderDual.ofDual _ _ fun _ ↦ rfl)

/-- **Positive Markov rule for `jimboWeightedTrace`.** Appending a strand and multiplying by the
last Hecke generator multiplies the `N`-colour weighted trace by `q ^ N`. -/
@[simp]
theorem jimboWeightedTrace_strandIncl_mul_T_last (N : ℕ) (q : Rˣ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    jimboWeightedTrace N q (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      ↑(q ^ N) * jimboWeightedTrace N q (n + 1) x := by
  let L₁ : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    jimboWeightedTrace N q (n + 2) ∘ₗ LinearMap.mulRight R (T q (Fin.last n)) ∘ₗ
      (strandIncl R q (n + 1)).toLinearMap
  let L₂ : TypeAHeckeAlgebra R q (n + 1) →ₗ[R] R :=
    (↑(q ^ N) : R) • jimboWeightedTrace N q (n + 1)
  have h : L₁ = L₂ :=
    LinearMap.ext_on_range (span_range_braidHom (R := R) (q := q) (n := n + 1)) fun b ↦ by
      simp only [L₁, L₂, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [← braidHom_strandIncl, ← val_unitT, ← braidHom_sigma, ← Units.val_mul, ← map_mul,
        jimboWeightedTrace_braidHom, jimboWeightedTrace_braidHom,
        KnotTheory.jimboWeightedTrace_stabilize]
  simpa [L₁, L₂] using LinearMap.congr_fun h x

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

/-- **Comparison with the Ocneanu trace.** When `c` is an inverse to the quantum dimension
`∑ a : Fin N, jimboWeight q a`, normalizing `jimboWeightedTrace N q n` by `c ^ n` yields the
Ocneanu trace with parameter `c * q ^ N` along `toInfinite`. -/
theorem pow_mul_jimboWeightedTrace_eq_ocneanuTrace {c : R}
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
  rw [← pow_mul_jimboWeightedTrace_eq_ocneanuTrace hc, ← mul_assoc, ← mul_pow, mul_comm _ c, hc,
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
  simpa only [div_eq_inv_mul, inv_pow] using pow_mul_jimboWeightedTrace_eq_ocneanuTrace hc x

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
