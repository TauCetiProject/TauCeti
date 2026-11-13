/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.TemperleyLieb.EvenClifford.Basic
public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.TemperleyLieb.Trace.Star
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.RepresentationTheory.Spin.OddStructure
import TauCeti.RepresentationTheory.Spin.Structure

/-!
# Trace radical, quotient isomorphism, and block structure at `δ = √2`

The coordinate inclusions `cliffordIncl m : Cl_m → Cl_{m+1}` along `Fin.snoc · 0` preserve the
analytic adjoint and the scalar trace `cliffordScalarCoefficient`, intertwine `strandIncl` with
`evenCliffordIncl`, and satisfy the Markov relation
`s_{k+2}(J_{k+1}(a) p_k) = s_{k+1}(a) / 2`. By uniqueness of the Markov trace,
`markovTrace q hq x = (√2)^m * s_m(evenCliffordModel m x)`, and faithfulness of `s_m(a† a)`
shows `ker (evenCliffordModel m)` equals the Markov trace radical.

This yields the quotient algebra isomorphism `quotientEquivEvenClifford m q hq` from the Jones
quotient onto `EvenClifford m` (Theorem 5.4 and Proposition 5.5 of Iohara–Lehrer–Zhang),
together with its complex dimension `2 ^ (m - 1)` for `m ≥ 1` and odd/even matrix block
decompositions.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordIncl`, `TauCeti.TemperleyLieb.evenCliffordIncl`: the
  coordinate inclusions along `Fin.snoc · 0`.
* `TauCeti.TemperleyLieb.quotientEquivEvenClifford`: the trace-radical quotient isomorphism onto
  `EvenClifford m`.

## Main results

* `TauCeti.TemperleyLieb.cliffordScalarCoefficient_cliffordIncl_mul_projection`: the Markov
  relation `s_{k+2}(J_{k+1}(a) p_k) = s_{k+1}(a) / 2`.
* `TauCeti.TemperleyLieb.markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient`: the Markov
  trace formula `T_m(x) = (√2)^m s_m(F_m x)`.
* `TauCeti.TemperleyLieb.exists_evenCliffordModel`: existence of the comparison map with generator
  values, surjectivity, trace formula, and kernel equal to the trace radical.
* `TauCeti.TemperleyLieb.finrank_quotient_evenClifford`: the trace-radical quotient has complex
  dimension `2 ^ (m - 1)` for `m ≥ 1`.
* `TauCeti.TemperleyLieb.nonempty_evenClifford_algEquiv_matrix_of_odd` and
  `TauCeti.TemperleyLieb.nonempty_evenClifford_algEquiv_matrix_prod_of_even`: odd/even matrix
  block decompositions of `EvenClifford m`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* K. Iohara, G. I. Lehrer, and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1903.00520, Section 5.3 (Theorem 5.4 and Proposition 5.5).
-/

public section

noncomputable section

open scoped ComplexConjugate ComplexOrder
open CliffordAlgebra Module

namespace TauCeti.TemperleyLieb

section TowerAndTrace

private lemma two_inv_mul_sqrt_two_sq :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private noncomputable def snocZeroLinear (m : ℕ) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

private noncomputable def snocZeroIsometry (m : ℕ) :
    cliffordForm m →qᵢ cliffordForm (m + 1) where
  toLinearMap := snocZeroLinear m
  map_app' x := by
    simp [snocZeroLinear, cliffordForm_apply, Fin.sum_univ_castSucc]

private theorem snocZeroIsometry_apply (m : ℕ) (x : Fin m → ℂ) :
    snocZeroIsometry m x = Fin.snoc x 0 :=
  (rfl)

/-- The coordinate inclusion `J_m : Cl_m → Cl_{m+1}` sending `c_j ↦ c_j` for `j < m`. -/
def cliffordIncl (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1)) :=
  CliffordAlgebra.map (snocZeroIsometry m)

@[simp]
theorem cliffordIncl_majorana (m : ℕ) (j : Fin m) :
    cliffordIncl m (majorana m j) = majorana (m + 1) j.castSucc := by
  rw [cliffordIncl, majorana_def, majorana_def, map_apply_ι]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [snocZeroIsometry_apply, Fin.snoc_last]
    simp [(Fin.castSucc_ne_last j).symm]
  · rw [snocZeroIsometry_apply, Fin.snoc_castSucc]
    simp [Pi.single_apply]

theorem cliffordIncl_mem_even (m : ℕ) {a : CliffordAlgebra (cliffordForm m)}
    (ha : a ∈ EvenClifford m) : cliffordIncl m a ∈ EvenClifford (m + 1) :=
  map_mem_even (snocZeroIsometry m) ha

/-- The coordinate inclusion `EvenClifford m →ₐ[ℂ] EvenClifford (m + 1)`. -/
def evenCliffordIncl (m : ℕ) : EvenClifford m →ₐ[ℂ] EvenClifford (m + 1) where
  toFun a := ⟨cliffordIncl m a, cliffordIncl_mem_even m a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' z := Subtype.ext ((cliffordIncl m).commutes z)

@[simp]
theorem coe_evenCliffordIncl (m : ℕ) (a : EvenClifford m) :
    (evenCliffordIncl m a : CliffordAlgebra (cliffordForm (m + 1))) = cliffordIncl m a :=
  (rfl)

@[simp]
theorem cliffordIncl_adjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (cliffordAdjoint m a) = cliffordAdjoint (m + 1) (cliffordIncl m a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap z => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hι : cliffordIncl m (cliffordAdjoint m (ι (cliffordForm m) v)) =
        cliffordAdjoint (m + 1) (cliffordIncl m (ι (cliffordForm m) v)) := by
      have hv : v = ∑ j : Fin m, v j • Pi.single j 1 := by
        ext i; simp [Pi.single_apply]
      rw [hv]
      simp only [map_sum, map_smulₛₗ]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1
      have hm1 : cliffordIncl m (cliffordAdjoint m (majorana m j)) =
          majorana (m + 1) j.castSucc := by
        rw [cliffordAdjoint_majorana, cliffordIncl_majorana]
      have hm2 : cliffordAdjoint (m + 1) (cliffordIncl m (majorana m j)) =
          majorana (m + 1) j.castSucc := by
        rw [cliffordIncl_majorana, cliffordAdjoint_majorana]
      rw [← majorana_def]
      exact hm1.trans hm2.symm
    simp only [cliffordAdjoint_mul, map_mul, hι, hx]

/-- The coordinate inclusion preserves the scalar coefficient `s`. -/
@[simp]
theorem cliffordScalarCoefficient_cliffordIncl (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordScalarCoefficient (m + 1) (cliffordIncl m a) = cliffordScalarCoefficient m a := by
  rw [cliffordScalarCoefficient_eq_scalarTrace, cliffordScalarCoefficient_eq_scalarTrace]
  let f : CliffordAlgebra (cliffordForm m) →ₗ[ℂ] ℂ :=
    (scalarTrace (cliffordForm (m + 1))).comp (cliffordIncl m).toLinearMap
  have hf_mul (x y : CliffordAlgebra (cliffordForm m)) : f (x * y) = f (y * x) := by
    simp [f, map_mul, scalarTrace_mul_comm]
  have hf_inv (x : CliffordAlgebra (cliffordForm m)) : f (involute x) = f x := by
    have hinvol : cliffordIncl m (involute x) = involute (cliffordIncl m x) := by
      induction x using CliffordAlgebra.induction with
      | algebraMap z => simp
      | ι v => simp [cliffordIncl]
      | add x y hx hy => simp [hx, hy]
      | mul x y hx hy => simp [hx, hy]
    simp only [f, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hinvol, scalarTrace_involute]
  have hl : (List.ofFn (Pi.basisFun ℂ (Fin m))).Pairwise (cliffordForm m).IsOrtho := by
    refine List.pairwise_ofFn.mpr fun i j hij ↦ ?_
    simp only [QuadraticMap.isOrtho_def, cliffordForm_apply, Pi.add_apply,
      Pi.basisFun_apply, Pi.single_apply]
    have hij' : i ≠ j := Fin.ne_of_lt hij
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hij', hij'.symm]
  have hspan : Submodule.span ℂ {x | x ∈ List.ofFn (Pi.basisFun ℂ (Fin m))} = ⊤ := by
    have hset : {x | x ∈ List.ofFn (Pi.basisFun ℂ (Fin m))} =
        Set.range (Pi.basisFun ℂ (Fin m)) := by
      ext x; simp
    rw [hset, (Pi.basisFun ℂ (Fin m)).span_eq]
  have heq := eq_smul_scalarTrace hl hspan f hf_mul hf_inv
  have h1 : f 1 = 1 := by simp [f]
  simpa [f, h1] using LinearMap.congr_fun heq a

theorem cliffordIncl_injective (m : ℕ) : Function.Injective (cliffordIncl m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← cliffordScalarCoefficient_adjoint_mul_self_eq_zero_iff m a,
    ← cliffordScalarCoefficient_cliffordIncl m, map_mul, cliffordIncl_adjoint, ha, mul_zero,
    cliffordScalarCoefficient_eq_scalarTrace, map_zero]

@[simp]
theorem evenCliffordModel_strandIncl (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (m + 1)) :
    evenCliffordModel (m + 2) (strandIncl x) =
      evenCliffordIncl (m + 1) (evenCliffordModel (m + 1) x) := by
  have h : (evenCliffordModel (m + 2)).comp strandIncl =
      (evenCliffordIncl (m + 1)).comp (evenCliffordModel (m + 1)) := by
    apply TemperleyLieb.hom_ext
    intro j
    ext1
    rw [AlgHom.comp_apply, AlgHom.comp_apply, strandIncl_e, evenCliffordModel_e,
      coe_evenCliffordIncl, evenCliffordModel_e, cliffordProjection_def, cliffordProjection_def,
      map_smul, map_smul, map_add, map_one, map_smul, map_mul, cliffordIncl_majorana,
      cliffordIncl_majorana]
    simp
  exact AlgHom.congr_fun h x

private noncomputable def flipLastIso (m : ℕ) :
    (cliffordForm (m + 1)).IsometryEquiv (cliffordForm (m + 1)) where
  toFun v := Function.update v (Fin.last m) (-v (Fin.last m))
  invFun v := Function.update v (Fin.last m) (-v (Fin.last m))
  left_inv v := by ext i; by_cases hi : i = Fin.last m <;> simp [hi]
  right_inv v := by ext i; by_cases hi : i = Fin.last m <;> simp [hi]
  map_add' v w := by ext i; by_cases hi : i = Fin.last m <;> simp [hi]; ring
  map_smul' c v := by ext i; by_cases hi : i = Fin.last m <;> simp [hi]
  map_app' v := by
    simp only [cliffordForm_apply, Fin.sum_univ_castSucc, Function.update_self,
      neg_mul, mul_neg, neg_neg]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Fin.castSucc_ne_last]

private theorem flipLastIso_toIsometry_apply (m : ℕ) (v : Fin (m + 1) → ℂ) :
    (flipLastIso m).toIsometry v = Function.update v (Fin.last m) (-v (Fin.last m)) :=
  (rfl)

private noncomputable def flipLastEquiv (m : ℕ) :
    CliffordAlgebra (cliffordForm (m + 1)) ≃ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1)) :=
  equivOfIsometry (flipLastIso m)

private theorem flipLastEquiv_cliffordIncl (k : ℕ)
    (a : CliffordAlgebra (cliffordForm (k + 1))) :
    flipLastEquiv (k + 1) (cliffordIncl (k + 1) a) = cliffordIncl (k + 1) a := by
  have hcomp : (flipLastEquiv (k + 1)).toAlgHom.comp (cliffordIncl (k + 1)) =
      cliffordIncl (k + 1) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, flipLastEquiv, cliffordIncl,
      equivOfIsometry_apply, map_apply_ι]
    congr 1
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [flipLastIso_toIsometry_apply, snocZeroIsometry_apply]
      simp
    · rw [flipLastIso_toIsometry_apply, snocZeroIsometry_apply]
      simp [Fin.castSucc_ne_last]
  exact AlgHom.congr_fun hcomp a

private theorem flipLastEquiv_majorana_of_ne_last (k : ℕ) {i : Fin (k + 2)}
    (hi : i ≠ Fin.last (k + 1)) :
    flipLastEquiv (k + 1) (majorana (k + 2) i) = majorana (k + 2) i := by
  simp only [flipLastEquiv, majorana_def, equivOfIsometry_apply, map_apply_ι]
  congr 1
  ext r
  rw [flipLastIso_toIsometry_apply]
  by_cases hr : r = Fin.last (k + 1)
  · simp only [hr, Function.update_self, Pi.single_apply]
    split_ifs with h
    · exact absurd h.symm hi
    · simp
  · simp [hr]

private theorem flipLastEquiv_majorana_last (k : ℕ) :
    flipLastEquiv (k + 1) (majorana (k + 2) (Fin.last (k + 1))) =
      -(majorana (k + 2) (Fin.last (k + 1))) := by
  simp only [flipLastEquiv, majorana_def, equivOfIsometry_apply, map_apply_ι, ← map_neg]
  congr 1
  ext r
  rw [flipLastIso_toIsometry_apply]
  by_cases hr : r = Fin.last (k + 1)
  · simp [hr]
  · simp only [Function.update_of_ne hr, Pi.neg_apply, Pi.single_apply]
    split_ifs with h
    · exact absurd h hr
    · simp

/-- **The Markov relation on the Clifford tower**: for `k : ℕ` and `a ∈ Cl_{k+1}`,
`s_{k+2}(J_{k+1}(a) p_k) = s_{k+1}(a) / 2`. -/
theorem cliffordScalarCoefficient_cliffordIncl_mul_projection (k : ℕ)
    (a : CliffordAlgebra (cliffordForm (k + 1))) :
    cliffordScalarCoefficient (k + 2)
        (cliffordIncl (k + 1) a * cliffordProjection (k + 2) (Fin.last k)) =
      (2 : ℂ)⁻¹ * cliffordScalarCoefficient (k + 1) a := by
  let σ := flipLastEquiv (k + 1)
  have hσ_c_prev : σ (majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val, by omega⟩) =
      majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val, by omega⟩ :=
    flipLastEquiv_majorana_of_ne_last k (by simp [Fin.ext_iff])
  have hσ_c_last : σ (majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val + 1, by omega⟩) =
      -(majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val + 1, by omega⟩) := by
    have hidx : (⟨(Fin.last k : Fin (k + 2 - 1)).val + 1, by omega⟩ : Fin (k + 2)) =
        Fin.last (k + 1) := by simp [Fin.ext_iff]
    rw [hidx]
    exact flipLastEquiv_majorana_last k
  have hzero : cliffordScalarCoefficient (k + 2) (cliffordIncl (k + 1) a *
      (majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val, by omega⟩ *
       majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val + 1, by omega⟩)) = 0 := by
    set term := cliffordIncl (k + 1) a *
      (majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val, by omega⟩ *
       majorana (k + 2) ⟨(Fin.last k : Fin (k + 2 - 1)).val + 1, by omega⟩)
    have hneg : σ term = -term := by
      simp only [term, σ, map_mul, flipLastEquiv_cliffordIncl, hσ_c_prev, hσ_c_last, mul_neg]
    have htr : cliffordScalarCoefficient (k + 2) term =
        -cliffordScalarCoefficient (k + 2) term := by
      calc
        cliffordScalarCoefficient (k + 2) term
            = scalarTrace (cliffordForm (k + 2)) term :=
              cliffordScalarCoefficient_eq_scalarTrace _ _
        _ = scalarTrace (cliffordForm (k + 2)) (σ term) :=
            (scalarTrace_eq_of_algEquiv σ term).symm
        _ = -scalarTrace (cliffordForm (k + 2)) term := by rw [hneg, map_neg]
        _ = -cliffordScalarCoefficient (k + 2) term := by
            rw [cliffordScalarCoefficient_eq_scalarTrace]
    have h2 : (2 : ℂ) * cliffordScalarCoefficient (k + 2) term = 0 := by
      linear_combination htr
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  simp only [cliffordProjection_def, Algebra.mul_smul_comm, mul_add, mul_one,
    cliffordScalarCoefficient_smul, cliffordScalarCoefficient_add,
    cliffordScalarCoefficient_cliffordIncl, hzero, mul_zero, add_zero]

/-- **The Markov trace identity at `δ = √2`**: for every `q : ℂˣ` with `√2 = -(q + q⁻¹)`,
`markovTrace q hq x = (√2)^m * cliffordScalarCoefficient m (evenCliffordModel m x)`. -/
theorem markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 2 : ℂ) ^ m * cliffordScalarCoefficient m (evenCliffordModel m x) := by
  let tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n →ₗ[ℂ] ℂ := fun n ↦
    (Real.sqrt 2 : ℂ) ^ n •
      ((scalarTrace (cliffordForm n)).comp
        (CliffordAlgebra.even (cliffordForm n)).val.toLinearMap).comp
        (evenCliffordModel n).toLinearMap
  have htr_apply (n : ℕ) (y : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n) :
      tr n y = (Real.sqrt 2 : ℂ) ^ n * cliffordScalarCoefficient n (evenCliffordModel n y) := by
    simp [tr, cliffordScalarCoefficient_eq_scalarTrace]
  have hmarkov : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr := by
    constructor
    · intro n
      simp [htr_apply]
    · intro n a b
      simp [htr_apply, map_mul, cliffordScalarCoefficient_mul_comm]
    · intro n a
      simp only [htr_apply, evenCliffordModel_strandIncl, coe_evenCliffordIncl,
        cliffordScalarCoefficient_cliffordIncl, pow_succ']
      ring
    · intro n a
      simp only [htr_apply, map_mul, evenCliffordModel_strandIncl, Subalgebra.coe_mul,
        coe_evenCliffordIncl, evenCliffordModel_e, Algebra.mul_smul_comm,
        cliffordScalarCoefficient_smul]
      rw [cliffordScalarCoefficient_cliffordIncl_mul_projection n (evenCliffordModel (n + 1) a)]
      calc
        (Real.sqrt 2 : ℂ) ^ (n + 2) *
            ((Real.sqrt 2 : ℂ) * ((2 : ℂ)⁻¹ * cliffordScalarCoefficient (n + 1)
              (evenCliffordModel (n + 1) a)))
            = (Real.sqrt 2 : ℂ) ^ (n + 1) *
                ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) *
                cliffordScalarCoefficient (n + 1) (evenCliffordModel (n + 1) a) := by
              rw [pow_succ]; ring
        _ = (Real.sqrt 2 : ℂ) ^ (n + 1) *
              cliffordScalarCoefficient (n + 1) (evenCliffordModel (n + 1) a) := by
            rw [two_inv_mul_sqrt_two_sq, mul_one]
  have huniq := (isMarkovTrace_markovTrace q hq).unique hmarkov
  simpa [htr_apply] using LinearMap.congr_fun (congrFun huniq m) x

/-- The kernel of `evenCliffordModel m` is the Markov trace radical
`R_m = {x | ∀ y, T_m(x y) = 0}`. -/
theorem evenCliffordModel_eq_zero_iff (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    evenCliffordModel m x = 0 ↔ ∀ y, markovTrace q hq (x * y) = 0 := by
  constructor
  · intro hx y
    rw [markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient m q hq (x * y),
      map_mul, hx, zero_mul, ZeroMemClass.coe_zero,
      cliffordScalarCoefficient_eq_scalarTrace, map_zero, mul_zero]
  · intro hx
    have hmul := hx (star x)
    rw [markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient m q hq (x * star x),
      map_mul, evenCliffordModel_star, Subalgebra.coe_mul, coe_evenCliffordAdjoint] at hmul
    have hpow : ((Real.sqrt 2 : ℂ) ^ m) ≠ 0 := by
      refine pow_ne_zero _ ?_
      exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
    have hs : cliffordScalarCoefficient m
        ((evenCliffordModel m x : CliffordAlgebra (cliffordForm m)) *
          cliffordAdjoint m (evenCliffordModel m x)) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hpow
    rw [cliffordScalarCoefficient_mul_comm] at hs
    exact Subtype.ext ((cliffordScalarCoefficient_adjoint_mul_self_eq_zero_iff m _).mp hs)

/-- **The Jones quotient at `δ = √2` is the even Clifford algebra** (Jones;
Iohara–Lehrer–Zhang, Theorem 5.4 and Proposition 5.5): for any unit `q : ℂˣ` with
`√2 = -(q + q⁻¹)`, there is a surjective algebra map
`F : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m` sending `e j` to `√2 p_j`,
intertwining the Markov trace with `(√2)^m s_m`, and with kernel equal to the trace radical
`{x | ∀ y, markovTrace q hq (x * y) = 0}`. -/
theorem exists_evenCliffordModel (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] EvenClifford m,
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 2 : ℂ) j) : CliffordAlgebra (cliffordForm m)) =
          (Real.sqrt 2 : ℂ) • cliffordProjection m j) ∧
      Function.Surjective F ∧
      (∀ x, markovTrace q hq x =
        (Real.sqrt 2 : ℂ) ^ m * cliffordScalarCoefficient m (F x)) ∧
      (∀ x, F x = 0 ↔ ∀ y, markovTrace q hq (x * y) = 0) :=
  ⟨evenCliffordModel m, evenCliffordModel_e m, evenCliffordModel_surjective m,
    markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient m q hq,
    evenCliffordModel_eq_zero_iff m q hq⟩

/-- The Markov trace radical on `TemperleyLieb ℂ (√2 : ℂ) m` equals
`ker (evenCliffordModel m)`. -/
theorem traceRadical_eq_ker_evenCliffordModel (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq) =
      RingHom.ker (evenCliffordModel m) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  exact (evenCliffordModel_eq_zero_iff m q hq x).symm

/-- The Markov trace radical on `TemperleyLieb ℂ (√2 : ℂ) m` is star-stable. -/
theorem star_mem_traceRadical_markovTrace_iff (m : ℕ)
    (q : ℂˣ) (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    {x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m} :
    star x ∈ (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq) ↔
      x ∈ (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq) :=
  (markovTrace q hq).star_mem_traceRadical_iff (markovTrace_mul_comm q hq) (markovTrace_star q hq)

/-- **The Jones quotient at `δ = √2` is isomorphic as an algebra to `EvenClifford m`.** -/
def quotientEquivEvenClifford (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸
        (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq)) ≃ₐ[ℂ]
      EvenClifford m :=
  (Ideal.quotientEquivAlgOfEq ℂ (traceRadical_eq_ker_evenCliffordModel m q hq)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evenCliffordModel_surjective m))

@[simp]
theorem quotientEquivEvenClifford_mk (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    quotientEquivEvenClifford m q hq (Ideal.Quotient.mk _ x) = evenCliffordModel m x := by
  simp [quotientEquivEvenClifford, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

theorem quotientEquivEvenClifford_star (m : ℕ)
    (q : ℂˣ) (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    quotientEquivEvenClifford m q hq (Ideal.Quotient.mk _ (star x)) =
      evenCliffordAdjoint m (quotientEquivEvenClifford m q hq (Ideal.Quotient.mk _ x)) := by
  simp [quotientEquivEvenClifford_mk, evenCliffordModel_star]

theorem quotientTrace_eq_quotientEquivEvenClifford (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸
      (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq)) :
    (markovTrace q hq (n := m)).quotientTrace (markovTrace_mul_comm q hq) x =
      (Real.sqrt 2 : ℂ) ^ m *
        cliffordScalarCoefficient m (quotientEquivEvenClifford m q hq x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [LinearMap.quotientTrace_mk,
    markovTrace_eq_sqrt_two_pow_mul_cliffordScalarCoefficient m q hq]

@[simp]
theorem quotientEquivEvenClifford_quotientStrandIncl (m : ℕ) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (m + 1) ⧸
      (markovTrace q hq (n := m + 1)).traceRadical (markovTrace_mul_comm q hq)) :
    quotientEquivEvenClifford (m + 2) q hq
        ((isMarkovTrace_markovTrace q hq).quotientStrandIncl m x) =
      evenCliffordIncl (m + 1) (quotientEquivEvenClifford (m + 1) q hq x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [IsMarkovTrace.quotientStrandIncl_mk, quotientEquivEvenClifford_mk,
    evenCliffordModel_strandIncl]

/-- For `m ≥ 1`, `EvenClifford m` has complex dimension `2 ^ (m - 1)`. -/
theorem finrank_evenClifford {m : ℕ} (hm : 1 ≤ m) :
    finrank ℂ (EvenClifford m) = 2 ^ (m - 1) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [CliffordAlgebra.finrank_even (cliffordForm m), finrank_fin_fun]

/-- For `m ≥ 1`, the Jones quotient of `TemperleyLieb ℂ (√2 : ℂ) m` has dimension
`2 ^ (m - 1)`. -/
theorem finrank_quotient_evenClifford {m : ℕ} (hm : 1 ≤ m) (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    finrank ℂ (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸
        (markovTrace q hq (n := m)).traceRadical (markovTrace_mul_comm q hq)) =
      2 ^ (m - 1) := by
  rw [(quotientEquivEvenClifford m q hq).toLinearEquiv.finrank_eq, finrank_evenClifford hm]

/-- For odd `m = 2 * l + 1`, `EvenClifford m` is isomorphic to the matrix algebra `M_{2^l}(ℂ)`. -/
theorem nonempty_evenClifford_algEquiv_matrix_of_odd (l : ℕ) :
    Nonempty (EvenClifford (2 * l + 1) ≃ₐ[ℂ] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) ℂ) :=
  CliffordAlgebra.nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one
    (cliffordForm_nondegenerate (2 * l + 1)) (by simp)

/-- For even `m = 2 * l` with `l ≥ 1`, `EvenClifford m` is isomorphic to
`M_{2^(l-1)}(ℂ) × M_{2^(l-1)}(ℂ)`. -/
theorem nonempty_evenClifford_algEquiv_matrix_prod_of_even {l : ℕ} (hl : 1 ≤ l) :
    Nonempty (EvenClifford (2 * l) ≃ₐ[ℂ]
      Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) ℂ ×
        Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) ℂ) := by
  let P := SpinPolarizationData.ofNondegenerate (cliffordForm (2 * l))
    (cliffordForm_nondegenerate (2 * l))
  have hV : finrank ℂ (Fin (2 * l) → ℂ) = 2 * l := by simp
  have hW : P.W ≠ ⊥ := by
    intro hbot
    have h0 := P.finrank_W_eq_of_finrank_eq_two_mul hV
    rw [hbot, finrank_bot] at h0
    omega
  exact ⟨P.evenCliffordEquivProdMatrix hW hV⟩

end TowerAndTrace

end TauCeti.TemperleyLieb

end
