/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.EvenClifford.Basic
public import TauCeti.KnotTheory.TemperleyLieb
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even

/-!
# Braid units and finiteness of the Clifford braid image at `δ = √2`

In `EvenClifford m`, the braid generators `g_j = -(1 + c_j c_{j+1}) / √2` are unitary with
respect to the positive-form analytic adjoint `cliffordAdjoint`, satisfy `g_j ^ 2 = c_j c_{j+1}`,
`g_j ^ 4 = -1`, `g_j ^ 8 = 1`, and the Artin braid relations, yielding a group homomorphism
`evenCliffordBraidRep m : BraidGroup m →* (EvenClifford m)ˣ`.

Under the comparison map `evenCliffordModel m`, the Kauffman-bracket braid generators
`TemperleyLieb.jonesUnit a j` at `a ^ 2 = -u⁻¹` (with `u ^ 2 = i` and `u + u⁻¹ = √2`) map to
scalar multiples `(-a / u) • g_j`. Conjugation by `g_j` permutes the signed Majorana generators
`±c_k` with central kernel `{±1}`, proving that `evenCliffordBraidRep m` has finite image.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordBraidGenerator`,
  `TauCeti.TemperleyLieb.evenCliffordBraidUnit`: the unitary braid generators
  `g_j = -(1 + c_j c_{j+1}) / √2` and their promotion to `(EvenClifford m)ˣ`.
* `TauCeti.TemperleyLieb.evenCliffordBraidRep`: the braid-group representation
  `BraidGroup m →* (EvenClifford m)ˣ`.

## Main results

* `TauCeti.TemperleyLieb.cliffordBraidGenerator_pow_eight`: `g_j ^ 8 = 1`.
* `TauCeti.TemperleyLieb.evenCliffordModel_jonesUnit`: comparison with `TemperleyLieb.jonesUnit`.
* `TauCeti.TemperleyLieb.evenCliffordBraidUnit_conj_majorana`: conjugation action on `c_k`.
* `TauCeti.TemperleyLieb.evenCliffordBraidSubgroup_finite` and
  `TauCeti.TemperleyLieb.finite_range_evenCliffordBraidRep`: finiteness of the Clifford braid
  subgroup and of the image of `BraidGroup m`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* K. Iohara, G. I. Lehrer, and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1903.00520, Section 5.3.
-/

public section

noncomputable section

open scoped ComplexConjugate
open CliffordAlgebra

namespace TauCeti.TemperleyLieb

section BraidUnits

private lemma two_inv_mul_sqrt_two_sq :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private lemma sqrt_two_inv_sq :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Clifford braid generators `g_j = -(1 + d_j) / √2` in `EvenClifford m`, with
`d_j = c_j c_{j+1}`. -/
def cliffordBraidGenerator (m : ℕ) (j : Fin (m - 1)) : CliffordAlgebra (cliffordForm m) :=
  (-(Real.sqrt 2 : ℂ)⁻¹) •
    (1 + majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩)

theorem cliffordBraidGenerator_mem_even (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j ∈ EvenClifford m := by
  unfold cliffordBraidGenerator
  exact Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (Subalgebra.one_mem _) (majorana_mul_succ_mem_even m j)) _

private theorem cliffordAdjoint_cliffordBraidGenerator (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordBraidGenerator m j) =
      (-(Real.sqrt 2 : ℂ)⁻¹) •
        (1 - majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) := by
  rw [cliffordBraidGenerator, map_smulₛₗ, map_add, cliffordAdjoint_one,
    cliffordAdjoint_majorana_mul_succ]
  simp [Complex.conj_ofReal, sub_eq_add_neg]

/-- `g_j† * g_j = 1`, where `g_j† = cliffordAdjoint m g_j = -(1 - d_j) / √2`. -/
@[simp]
theorem cliffordBraidGenerator_adjoint_mul_self (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordBraidGenerator m j) * cliffordBraidGenerator m j = 1 := by
  set d := majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩
  have hd2 : d * d = -1 := by simpa [sq] using majorana_mul_succ_sq m j
  have hadj := cliffordAdjoint_cliffordBraidGenerator m j
  rw [hadj, cliffordBraidGenerator, smul_mul_smul_comm]
  have hsq : -(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    simpa using sqrt_two_inv_sq
  have hprod : (1 - d) * (1 + d) = (2 : ℂ) • 1 := by
    calc
      (1 - d) * (1 + d) = 1 - d * d := by noncomm_ring
      _ = (2 : ℂ) • 1 := by rw [hd2, sub_neg_eq_add, two_smul]
  rw [hsq, hprod, smul_smul]
  norm_num

/-- `g_j * g_j† = 1`. -/
@[simp]
theorem cliffordBraidGenerator_mul_adjoint (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j * cliffordAdjoint m (cliffordBraidGenerator m j) = 1 := by
  set d := majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩
  have hd2 : d * d = -1 := by simpa [sq] using majorana_mul_succ_sq m j
  have hadj := cliffordAdjoint_cliffordBraidGenerator m j
  rw [hadj, cliffordBraidGenerator, smul_mul_smul_comm]
  have hsq : -(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    simpa using sqrt_two_inv_sq
  have hprod : (1 + d) * (1 - d) = (2 : ℂ) • 1 := by
    calc
      (1 + d) * (1 - d) = 1 - d * d := by noncomm_ring
      _ = (2 : ℂ) • 1 := by rw [hd2, sub_neg_eq_add, two_smul]
  rw [hsq, hprod, smul_smul]
  norm_num

/-- `g_j ^ 2 = d_j = c_j c_{j+1}`. -/
@[simp]
theorem cliffordBraidGenerator_sq (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j ^ 2 =
      majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩ := by
  set d := majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩
  have hd2 : d * d = -1 := by simpa [sq] using majorana_mul_succ_sq m j
  rw [sq, cliffordBraidGenerator, smul_mul_smul_comm]
  have hsq : -(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    simpa using sqrt_two_inv_sq
  have hprod : (1 + d) * (1 + d) = (2 : ℂ) • d := by
    calc
      (1 + d) * (1 + d) = 1 + d * d + (2 : ℂ) • d := by rw [two_smul]; noncomm_ring
      _ = (2 : ℂ) • d := by rw [hd2, add_neg_cancel, zero_add]
  rw [hsq, hprod, smul_smul]
  norm_num

/-- `g_j ^ 4 = -1`. -/
@[simp]
theorem cliffordBraidGenerator_pow_four (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j ^ 4 = -1 := by
  calc
    cliffordBraidGenerator m j ^ 4 = (cliffordBraidGenerator m j ^ 2) ^ 2 := by noncomm_ring
    _ = -1 := by rw [cliffordBraidGenerator_sq, majorana_mul_succ_sq]

/-- `g_j ^ 8 = 1`. -/
@[simp]
theorem cliffordBraidGenerator_pow_eight (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j ^ 8 = 1 := by
  calc
    cliffordBraidGenerator m j ^ 8 = (cliffordBraidGenerator m j ^ 4) ^ 2 := by noncomm_ring
    _ = 1 := by rw [cliffordBraidGenerator_pow_four, neg_one_sq]

/-- The braid generators promoted to units of `EvenClifford m`. -/
def evenCliffordBraidUnit (m : ℕ) (j : Fin (m - 1)) : (EvenClifford m)ˣ where
  val := ⟨cliffordBraidGenerator m j, cliffordBraidGenerator_mem_even m j⟩
  inv := evenCliffordAdjoint m ⟨cliffordBraidGenerator m j, cliffordBraidGenerator_mem_even m j⟩
  val_inv := Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_evenCliffordAdjoint, cliffordBraidGenerator_mul_adjoint,
      OneMemClass.coe_one])
  inv_val := Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_evenCliffordAdjoint, cliffordBraidGenerator_adjoint_mul_self,
      OneMemClass.coe_one])

@[simp]
theorem evenCliffordBraidUnit_val (m : ℕ) (j : Fin (m - 1)) :
    ((evenCliffordBraidUnit m j : EvenClifford m) : CliffordAlgebra (cliffordForm m)) =
      cliffordBraidGenerator m j :=
  (rfl)

@[simp]
theorem evenCliffordBraidUnit_inv_val (m : ℕ) (j : Fin (m - 1)) :
    ((((evenCliffordBraidUnit m j)⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
        CliffordAlgebra (cliffordForm m)) =
      cliffordAdjoint m (cliffordBraidGenerator m j) :=
  coe_evenCliffordAdjoint m ⟨cliffordBraidGenerator m j, cliffordBraidGenerator_mem_even m j⟩

theorem evenCliffordBraidUnit_comm (m : ℕ) {i j : Fin (m - 1)}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    evenCliffordBraidUnit m i * evenCliffordBraidUnit m j =
      evenCliffordBraidUnit m j * evenCliffordBraidUnit m i := by
  apply Units.ext
  ext1
  have hc := majorana_mul_succ_comm_of_dist m hij
  set di := majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩
  set dj := majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩
  have hsum : (1 + di) * (1 + dj) = (1 + dj) * (1 + di) := by
    calc
      (1 + di) * (1 + dj) = 1 + di + dj + di * dj := by noncomm_ring
      _ = 1 + dj + di + dj * di := by rw [hc.eq]; abel
      _ = (1 + dj) * (1 + di) := by noncomm_ring
  simp only [Units.val_mul, Subalgebra.coe_mul, evenCliffordBraidUnit_val, cliffordBraidGenerator,
    smul_mul_smul_comm]
  exact congrArg ((-(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹) • ·) hsum

theorem evenCliffordBraidUnit_braid (m : ℕ) {i j : Fin (m - 1)}
    (hij : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    evenCliffordBraidUnit m i * evenCliffordBraidUnit m j * evenCliffordBraidUnit m i =
      evenCliffordBraidUnit m j * evenCliffordBraidUnit m i * evenCliffordBraidUnit m j := by
  apply Units.ext
  ext1
  set di := majorana m ⟨i.val, by omega⟩ * majorana m ⟨i.val + 1, by omega⟩
  set dj := majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩
  have hdi2 : di * di = -1 := by simpa [sq] using majorana_mul_succ_sq m i
  have hdj2 : dj * dj = -1 := by simpa [sq] using majorana_mul_succ_sq m j
  have hantic : di * dj = -(dj * di) := hij.elim
    (fun h ↦ majorana_mul_succ_anticomm_of_adj m h)
    (fun h ↦ by rw [majorana_mul_succ_anticomm_of_adj m h, neg_neg])
  have hantic' : dj * di = -(di * dj) := by rw [hantic, neg_neg]
  have htriple (x y : CliffordAlgebra (cliffordForm m)) (hx2 : x * x = -1)
      (hxy : x * y = -(y * x)) :
      (1 + x) * (1 + y) * (1 + x) = (2 : ℂ) • (x + y) := by
    have hxyx : x * y * x = y := by
      calc
        x * y * x = -(y * x) * x := by rw [hxy]
        _ = -(y * (x * x)) := by simp [mul_assoc]
        _ = y := by rw [hx2, mul_neg, mul_one, neg_neg]
    calc
      (1 + x) * (1 + y) * (1 + x)
          = 1 + x * x + (x + x) + (y + x * y * x) + (x * y + y * x) := by noncomm_ring
      _ = (2 : ℂ) • (x + y) := by
        rw [hxyx, hx2, hxy, two_smul]
        abel
  simp only [Units.val_mul, Subalgebra.coe_mul, evenCliffordBraidUnit_val, cliffordBraidGenerator,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [htriple di dj hdi2 hantic, htriple dj di hdj2 hantic', add_comm dj di]

/-- The unitary representation of `BraidGroup m` into `(EvenClifford m)ˣ`
sending `σ_j ↦ g_j`. -/
def evenCliffordBraidRep (m : ℕ) : BraidGroup m →* (EvenClifford m)ˣ :=
  BraidGroup.lift (evenCliffordBraidUnit m)
    (fun h ↦ evenCliffordBraidUnit_comm m h)
    (fun h ↦ evenCliffordBraidUnit_braid m h)

@[simp]
theorem evenCliffordBraidRep_sigma (m : ℕ) (j : Fin (m - 1)) :
    evenCliffordBraidRep m (BraidGroup.sigma j) = evenCliffordBraidUnit m j :=
  BraidGroup.lift_sigma _ _ _ j

/-- Comparison with `TemperleyLieb.jones`: for units `u, a : ℂˣ` with `u ^ 2 = i`,
`u + u⁻¹ = √2`, and `a ^ 2 = -u⁻¹`, `evenCliffordModel m` maps `jonesUnit a j` to
`(-a / u) • g_j`. -/
theorem evenCliffordModel_jonesUnit (m : ℕ) {u a : ℂˣ}
    (hu2 : (u : ℂ) ^ 2 = Complex.I)
    (hu : (u : ℂ) + ((u⁻¹ : ℂˣ) : ℂ) = (Real.sqrt 2 : ℂ))
    (ha : (a : ℂ) ^ 2 = -((u⁻¹ : ℂˣ) : ℂ)) (j : Fin (m - 1)) :
    (evenCliffordModel m
        (cast (congrArg (fun δ ↦ TemperleyLieb ℂ δ m)
          (by
            rw [jonesDelta_def, ha]
            have ha_inv : ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = -(u : ℂ) := by
              have hprod : (a : ℂ) ^ 2 * ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = 1 := by
                rw [← mul_pow]; simp
              rw [ha] at hprod
              have h2 : (-((u⁻¹ : ℂˣ) : ℂ)) * (-(u : ℂ)) = 1 := by simp
              exact mul_left_cancel₀ (neg_ne_zero.mpr (Units.ne_zero _)) (hprod.trans h2.symm)
            rw [ha_inv]
            simpa [neg_add] using hu))
          (jonesUnit a j : TemperleyLieb ℂ (jonesDelta a) m)) :
        CliffordAlgebra (cliffordForm m)) =
      (-((a : ℂ) / (u : ℂ))) • cliffordBraidGenerator m j := by
  have ha_inv : ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = -(u : ℂ) := by
    have hprod : (a : ℂ) ^ 2 * ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← mul_pow]; simp
    rw [ha] at hprod
    have h2 : (-((u⁻¹ : ℂˣ) : ℂ)) * (-(u : ℂ)) = 1 := by simp
    exact mul_left_cancel₀ (neg_ne_zero.mpr (Units.ne_zero _)) (hprod.trans h2.symm)
  have hdelta : jonesDelta a = (Real.sqrt 2 : ℂ) := by
    rw [jonesDelta_def, ha, ha_inv]
    simpa [neg_add] using hu
  have hval_gen : ∀ (δ : ℂ) (hδ : δ = jonesDelta a),
      (cast (congrArg (fun d ↦ TemperleyLieb ℂ d m) hδ.symm)
        (jonesUnit a j : TemperleyLieb ℂ (jonesDelta a) m)) =
        (a : ℂ) • 1 + ((a⁻¹ : ℂˣ) : ℂ) • e δ j := by
    rintro _ rfl
    simp [jonesUnit_val, crossing_def]
  have hval := hval_gen (Real.sqrt 2 : ℂ) hdelta.symm
  rw [hval, map_add, map_smul, map_smul, map_one, Subalgebra.coe_add, Subalgebra.coe_smul,
    Subalgebra.coe_smul, OneMemClass.coe_one, evenCliffordModel_e, cliffordProjection_def,
    cliffordBraidGenerator]
  have hainv : ((a⁻¹ : ℂˣ) : ℂ) = -(a : ℂ) * (u : ℂ) := by
    calc
      ((a⁻¹ : ℂˣ) : ℂ)
          = ((a⁻¹ : ℂˣ) : ℂ) * ((a : ℂ) * ((a⁻¹ : ℂˣ) : ℂ)) := by simp
      _ = ((a⁻¹ : ℂˣ) : ℂ) ^ 2 * (a : ℂ) := by ring
      _ = -(u : ℂ) * (a : ℂ) := by rw [ha_inv]
      _ = -(a : ℂ) * (u : ℂ) := by ring
  have hc1 : (a : ℂ) + ((a⁻¹ : ℂˣ) : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) =
      -((a : ℂ) / (u : ℂ)) * -(Real.sqrt 2 : ℂ)⁻¹ := by
    rw [hainv]
    have hmul_eq :
        (1 - (u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹)) * ((u : ℂ) * Real.sqrt 2) =
          1 := by
      have hu' : (u : ℂ) + (u : ℂ)⁻¹ = Real.sqrt 2 := by simpa using hu
      have h2 : (u : ℂ) ^ 2 + 1 = (Real.sqrt 2 : ℂ) * (u : ℂ) := by
        calc
          (u : ℂ) ^ 2 + 1 = (u : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) := by
            rw [mul_add, sq, mul_inv_cancel₀ (Units.ne_zero u)]
          _ = (Real.sqrt 2 : ℂ) * (u : ℂ) := by rw [hu']; ring
      calc
        (1 - (u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹)) * ((u : ℂ) * Real.sqrt 2)
            = (u : ℂ) * Real.sqrt 2 -
                (u : ℂ) ^ 2 * ((Real.sqrt 2 : ℂ) * Real.sqrt 2 * (2 : ℂ)⁻¹) := by ring
        _ = (u : ℂ) * Real.sqrt 2 - (u : ℂ) ^ 2 := by rw [two_inv_mul_sqrt_two_sq, mul_one]
        _ = 1 := by linear_combination -h2
    have hdiv : 1 - (u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) =
        ((u : ℂ) * Real.sqrt 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul_eq
    calc
      (a : ℂ) + (-(a : ℂ) * (u : ℂ)) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹)
          = (a : ℂ) * (1 - (u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹)) := by ring
      _ = (a : ℂ) * ((u : ℂ) * Real.sqrt 2)⁻¹ := by rw [hdiv]
      _ = -((a : ℂ) / (u : ℂ)) * -(Real.sqrt 2 : ℂ)⁻¹ := by
        rw [mul_inv]; ring
  have hc2 : ((a⁻¹ : ℂˣ) : ℂ) * ((Real.sqrt 2 : ℂ) * ((2 : ℂ)⁻¹ * Complex.I)) =
      -((a : ℂ) / (u : ℂ)) * -(Real.sqrt 2 : ℂ)⁻¹ := by
    rw [hainv]
    have hkey : -((u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) * Complex.I) *
        ((u : ℂ) * Real.sqrt 2) = 1 := by
      calc
        -((u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) * Complex.I) *
            ((u : ℂ) * Real.sqrt 2)
            = -((u : ℂ) ^ 2 * Complex.I) *
                ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) := by ring
        _ = -(Complex.I * Complex.I) * 1 := by rw [hu2, two_inv_mul_sqrt_two_sq]
        _ = 1 := by simp
    have hdiv := eq_inv_of_mul_eq_one_left hkey
    calc
      (-(a : ℂ) * (u : ℂ)) * ((Real.sqrt 2 : ℂ) * ((2 : ℂ)⁻¹ * Complex.I))
          = (a : ℂ) *
              (-((u : ℂ) * ((Real.sqrt 2 : ℂ) * (2 : ℂ)⁻¹) * Complex.I)) := by ring
      _ = (a : ℂ) * ((u : ℂ) * Real.sqrt 2)⁻¹ := by rw [hdiv]
      _ = -((a : ℂ) / (u : ℂ)) * -(Real.sqrt 2 : ℂ)⁻¹ := by rw [mul_inv]; ring
  simp only [smul_add, smul_smul]
  rw [← add_assoc, ← add_smul, hc1, hc2]

section ConjugationAction

private theorem g_mul_majorana_left (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j * majorana m ⟨j.val, by omega⟩ *
        cliffordAdjoint m (cliffordBraidGenerator m j) =
      -majorana m ⟨j.val + 1, by omega⟩ := by
  set c0 := majorana m ⟨j.val, by omega⟩
  set c1 := majorana m ⟨j.val + 1, by omega⟩
  set d := c0 * c1
  have hne : (⟨j.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by simp [Fin.ext_iff]
  have hdc0 : d * c0 = -c1 := by
    calc
      (c0 * c1) * c0 = c0 * (c1 * c0) := mul_assoc _ _ _
      _ = c0 * (-(c0 * c1)) := by rw [majorana_mul_comm_neg m hne.symm]
      _ = -(c0 * c0 * c1) := by simp [mul_assoc]
      _ = -c1 := by rw [majorana_mul_self, one_mul]
  have hc0d : c0 * d = c1 := by
    calc
      c0 * (c0 * c1) = c0 * c0 * c1 := (mul_assoc _ _ _).symm
      _ = c1 := by rw [majorana_mul_self, one_mul]
  have hc1d : c1 * d = -c0 := by
    calc
      c1 * (c0 * c1) = (c1 * c0) * c1 := (mul_assoc _ _ _).symm
      _ = (-(c0 * c1)) * c1 := by rw [majorana_mul_comm_neg m hne.symm]
      _ = -(c0 * (c1 * c1)) := by simp [mul_assoc]
      _ = -c0 := by rw [majorana_mul_self, mul_one]
  have hadj := cliffordAdjoint_cliffordBraidGenerator m j
  rw [hadj, cliffordBraidGenerator, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_smul]
  have hsq : -(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    simpa using sqrt_two_inv_sq
  have hprod : (1 + d) * c0 * (1 - d) = -(2 : ℂ) • c1 := by
    calc
      (1 + d) * c0 * (1 - d) = (c0 + d * c0) * (1 - d) := by rw [add_mul, one_mul]
      _ = (c0 - c1) * (1 - d) := by rw [hdc0, ← sub_eq_add_neg]
      _ = c0 - c0 * d - c1 + c1 * d := by noncomm_ring
      _ = c0 - c1 - c1 + (-c0) := by rw [hc0d, hc1d]
      _ = -(2 : ℂ) • c1 := by rw [neg_smul, two_smul]; abel
  rw [hsq, hprod, smul_smul]
  norm_num

private theorem g_mul_majorana_right (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidGenerator m j * majorana m ⟨j.val + 1, by omega⟩ *
        cliffordAdjoint m (cliffordBraidGenerator m j) =
      majorana m ⟨j.val, by omega⟩ := by
  set c0 := majorana m ⟨j.val, by omega⟩
  set c1 := majorana m ⟨j.val + 1, by omega⟩
  set d := c0 * c1
  have hne : (⟨j.val, by omega⟩ : Fin m) ≠ ⟨j.val + 1, by omega⟩ := by simp [Fin.ext_iff]
  have hdc1 : d * c1 = c0 := by
    calc
      (c0 * c1) * c1 = c0 * (c1 * c1) := mul_assoc _ _ _
      _ = c0 := by rw [majorana_mul_self, mul_one]
  have hc0d : c0 * d = c1 := by
    calc
      c0 * (c0 * c1) = c0 * c0 * c1 := (mul_assoc _ _ _).symm
      _ = c1 := by rw [majorana_mul_self, one_mul]
  have hc1d : c1 * d = -c0 := by
    calc
      c1 * (c0 * c1) = (c1 * c0) * c1 := (mul_assoc _ _ _).symm
      _ = (-(c0 * c1)) * c1 := by rw [majorana_mul_comm_neg m hne.symm]
      _ = -(c0 * (c1 * c1)) := by simp [mul_assoc]
      _ = -c0 := by rw [majorana_mul_self, mul_one]
  have hadj := cliffordAdjoint_cliffordBraidGenerator m j
  rw [hadj, cliffordBraidGenerator, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_smul]
  have hsq : -(Real.sqrt 2 : ℂ)⁻¹ * -(Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    simpa using sqrt_two_inv_sq
  have hprod : (1 + d) * c1 * (1 - d) = (2 : ℂ) • c0 := by
    calc
      (1 + d) * c1 * (1 - d) = (c1 + d * c1) * (1 - d) := by rw [add_mul, one_mul]
      _ = (c1 + c0) * (1 - d) := by rw [hdc1]
      _ = c1 - c1 * d + c0 - c0 * d := by noncomm_ring
      _ = c1 - (-c0) + c0 - c1 := by rw [hc1d, hc0d]
      _ = (2 : ℂ) • c0 := by rw [two_smul]; abel
  rw [hsq, hprod, smul_smul]
  norm_num

private theorem g_mul_majorana_other (m : ℕ) (j : Fin (m - 1)) {k : Fin m}
    (hk0 : k.val ≠ j.val) (hk1 : k.val ≠ j.val + 1) :
    cliffordBraidGenerator m j * majorana m k *
        cliffordAdjoint m (cliffordBraidGenerator m j) =
      majorana m k := by
  have hne0 : (⟨j.val, by omega⟩ : Fin m) ≠ k := Fin.ne_of_val_ne hk0.symm
  have hne1 : (⟨j.val + 1, by omega⟩ : Fin m) ≠ k := Fin.ne_of_val_ne hk1.symm
  have hcomm : Commute (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩)
      (majorana m k) := by
    rw [commute_iff_eq]
    calc
      (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) * majorana m k
          = majorana m ⟨j.val, by omega⟩ *
              (majorana m ⟨j.val + 1, by omega⟩ * majorana m k) := mul_assoc _ _ _
      _ = majorana m ⟨j.val, by omega⟩ *
            (-(majorana m k * majorana m ⟨j.val + 1, by omega⟩)) := by
            rw [majorana_mul_comm_neg m hne1]
      _ = -((majorana m ⟨j.val, by omega⟩ * majorana m k) *
            majorana m ⟨j.val + 1, by omega⟩) := by
            simp [mul_assoc]
      _ = -((-(majorana m k * majorana m ⟨j.val, by omega⟩)) *
            majorana m ⟨j.val + 1, by omega⟩) := by
            rw [majorana_mul_comm_neg m hne0]
      _ = majorana m k *
            (majorana m ⟨j.val, by omega⟩ * majorana m ⟨j.val + 1, by omega⟩) := by
            simp [mul_assoc]
  have hcomm_g : Commute (cliffordBraidGenerator m j) (majorana m k) :=
    ((Commute.one_left _).add_left hcomm).smul_left _
  rw [hcomm_g.eq, mul_assoc, cliffordBraidGenerator_mul_adjoint, mul_one]

/-- Conjugation by `g_j` sends `c_j ↦ -c_{j+1}`, `c_{j+1} ↦ c_j`, and fixes all other `c_k`. -/
theorem evenCliffordBraidUnit_conj_majorana (m : ℕ) (j : Fin (m - 1)) (k : Fin m) :
    ((evenCliffordBraidUnit m j : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        majorana m k *
        ((((evenCliffordBraidUnit m j)⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
          CliffordAlgebra (cliffordForm m)) =
      if k.val = j.val then -majorana m ⟨j.val + 1, by omega⟩
      else if k.val = j.val + 1 then majorana m ⟨j.val, by omega⟩
      else majorana m k := by
  simp only [evenCliffordBraidUnit_val, evenCliffordBraidUnit_inv_val]
  split_ifs with h0 h1
  · have hk : k = ⟨j.val, by omega⟩ := Fin.ext h0
    rw [hk]
    exact g_mul_majorana_left m j
  · have hk : k = ⟨j.val + 1, by omega⟩ := Fin.ext h1
    rw [hk]
    exact g_mul_majorana_right m j
  · exact g_mul_majorana_other m j h0 h1

private def signedMajorana (m : ℕ) (p : Bool × Fin m) : CliffordAlgebra (cliffordForm m) :=
  if p.1 then -majorana m p.2 else majorana m p.2

private theorem signedMajorana_injective (m : ℕ) : Function.Injective (signedMajorana m) := by
  intro ⟨s1, k1⟩ ⟨s2, k2⟩ h
  have hbasis (s : Bool) (k : Fin m) :
      (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr
        (signedMajorana m (s, k)) =
        (if s then (-1 : ℂ) else 1) • Finsupp.single {k} 1 := by
    have hb : majorana m k =
        CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m)) {k} := by
      rw [basis_singleton, Pi.basisFun_apply, majorana_def]
    cases s
    · simp only [signedMajorana, ↓reduceIte, Bool.false_eq_true, one_smul]
      rw [hb, Module.Basis.repr_self]
    · simp only [signedMajorana, ↓reduceIte, map_neg, neg_smul, one_smul]
      rw [hb, Module.Basis.repr_self]
  have hr := congrArg (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr h
  rw [hbasis, hbasis] at hr
  have hk : k1 = k2 := by
    have h1 := congrArg (fun f ↦ f {k1}) hr
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_one, ite_true] at h1
    by_contra hne
    have hne' : ({k2} : Finset (Fin m)) ≠ {k1} := by
      intro hset
      exact hne (Finset.singleton_injective hset).symm
    simp only [hne', ↓reduceIte, mul_zero] at h1
    cases s1 <;> norm_num at h1
  subst hk
  have hs := congrArg (fun f ↦ f {k1}) hr
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_one, ite_true] at hs
  cases s1 <;> cases s2 <;> norm_num at hs
  · rfl
  · rfl

private noncomputable def braidGenPerm (m : ℕ) (j : Fin (m - 1)) : Equiv.Perm (Bool × Fin m) :=
  let step : Bool × Fin m → Bool × Fin m := fun p ↦
    if p.2.val = j.val then (!p.1, ⟨j.val + 1, by omega⟩)
    else if p.2.val = j.val + 1 then (p.1, ⟨j.val, by omega⟩)
    else p
  have hinj : Function.Injective step := by
    intro p1 p2 h
    dsimp only [step] at h
    split_ifs at h
    · have hfst := congrArg Prod.fst h
      have hs : p1.1 = p2.1 := by
        rcases p1 with ⟨s1, k1⟩
        rcases p2 with ⟨s2, k2⟩
        cases s1 <;> cases s2 <;> simp_all
      exact Prod.ext hs (Fin.ext (by omega))
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · have hs := congrArg Prod.fst h
      exact Prod.ext hs (Fin.ext (by omega))
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · have hv := congrArg (fun p : Bool × Fin m ↦ p.2.val) h
      dsimp at hv
      omega
    · exact h
  Equiv.ofBijective step ((Finite.injective_iff_bijective).1 hinj)

private theorem g_conj_signedMajorana (m : ℕ) (j : Fin (m - 1)) (p : Bool × Fin m) :
    ((evenCliffordBraidUnit m j : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        signedMajorana m p *
        ((((evenCliffordBraidUnit m j)⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
          CliffordAlgebra (cliffordForm m)) =
      signedMajorana m (braidGenPerm m j p) := by
  obtain ⟨s, k⟩ := p
  have hconj := evenCliffordBraidUnit_conj_majorana m j k
  cases s
  · simp only [signedMajorana, ↓reduceIte, Bool.false_eq_true]
    rw [hconj]
    by_cases h1 : k.val = j.val
    · simp [braidGenPerm, Equiv.ofBijective_apply, h1]
    · by_cases h2 : k.val = j.val + 1 <;>
        simp [braidGenPerm, Equiv.ofBijective_apply, h1, h2]
  · simp only [signedMajorana, ↓reduceIte, mul_neg, neg_mul]
    rw [hconj]
    by_cases h1 : k.val = j.val
    · simp [braidGenPerm, Equiv.ofBijective_apply, h1]
    · by_cases h2 : k.val = j.val + 1 <;>
        simp [braidGenPerm, Equiv.ofBijective_apply, h1, h2]

private theorem coe_unit_inv_mul_left {m : ℕ} (u : (EvenClifford m)ˣ)
    (a : CliffordAlgebra (cliffordForm m)) :
    ((((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
      (((u : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * a) = a := by
  rw [← mul_assoc, ← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    OneMemClass.coe_one, one_mul]

private theorem coe_unit_inv_mul_right {m : ℕ} (u : (EvenClifford m)ˣ)
    (a : CliffordAlgebra (cliffordForm m)) :
    (a * (((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
      ((u : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = a := by
  rw [mul_assoc, ← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    OneMemClass.coe_one, mul_one]

private theorem coe_unit_mul_inv_right {m : ℕ} (u : (EvenClifford m)ˣ)
    (a : CliffordAlgebra (cliffordForm m)) :
    (a * ((u : EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
      ((((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
      a := by
  rw [mul_assoc, ← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    OneMemClass.coe_one, mul_one]

private theorem signedMajorana_inj_of_conj {m : ℕ} (u : (EvenClifford m)ˣ)
    {p1 p2 : Bool × Fin m}
    (h : ((u : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * signedMajorana m p1 *
        ((((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
      ((u : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * signedMajorana m p2 *
        ((((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)))) :
    p1 = p2 := by
  apply signedMajorana_injective m
  have h1 := congrArg (fun z ↦
    ((((u⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
      (z * ((u : EvenClifford m) : CliffordAlgebra (cliffordForm m)))) h
  rwa [coe_unit_inv_mul_right, coe_unit_inv_mul_left,
    coe_unit_inv_mul_right, coe_unit_inv_mul_left] at h1

private theorem braidSubgroup_conj_signedMajorana (m : ℕ) (h : (EvenClifford m)ˣ)
    (hh : h ∈ Subgroup.closure (Set.range (evenCliffordBraidUnit m))) (p : Bool × Fin m) :
    ∃ q : Bool × Fin m,
      ((h : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * signedMajorana m p *
        ((((h⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
        signedMajorana m q := by
  induction hh using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨braidGenPerm m j p, g_conj_signedMajorana m j p⟩
  | one => exact ⟨p, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨q, hq⟩ := ihy p
    obtain ⟨r, hr⟩ := ihx q
    refine ⟨r, ?_⟩
    simp only [Units.val_mul, Subalgebra.coe_mul, mul_inv_rev]
    calc
      ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
          ((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * signedMajorana m p *
          ((((y⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
            (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)))
          = ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
              (((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
                signedMajorana m p *
                (((y⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
                  CliffordAlgebra (cliffordForm m))) *
              (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
                CliffordAlgebra (cliffordForm m)) := by
            simp only [mul_assoc]
      _ = signedMajorana m r := by rw [hq, hr]
  | inv x _ ih =>
    have hfin : ∀ (q : Bool × Fin m), ∃ r : Bool × Fin m,
        ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * signedMajorana m q *
          (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)) =
          signedMajorana m r := ih
    choose f hf using hfin
    have hfinj : Function.Injective f := by
      intro p1 p2 hp
      have eq1 := hf p1
      have eq2 := hf p2
      rw [hp] at eq1
      exact signedMajorana_inj_of_conj x (eq1.trans eq2.symm)
    obtain ⟨p0, hp0⟩ := Finite.injective_iff_surjective.1 hfinj p
    refine ⟨p0, ?_⟩
    have hmid := hf p0
    rw [hp0] at hmid
    simp only [inv_inv]
    calc
      (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
          signedMajorana m p * ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m))
          = (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
                CliffordAlgebra (cliffordForm m)) *
              ((((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
                signedMajorana m p0 *
                (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
                  CliffordAlgebra (cliffordForm m))) *
              ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m))) := by
            rw [hmid, mul_assoc]
      _ = signedMajorana m p0 := by
            rw [coe_unit_inv_mul_right, coe_unit_inv_mul_left]

private noncomputable def braidSubgroupPerm (m : ℕ)
    (h : Subgroup.closure (Set.range (evenCliffordBraidUnit m))) :
    Equiv.Perm (Bool × Fin m) :=
  let f : Bool × Fin m → Bool × Fin m :=
    fun p ↦ Classical.choose (braidSubgroup_conj_signedMajorana m h.1 h.2 p)
  have hf : ∀ p, ((h.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
      signedMajorana m p *
      ((((h.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
      signedMajorana m (f p) :=
    fun p ↦ Classical.choose_spec (braidSubgroup_conj_signedMajorana m h.1 h.2 p)
  have hinj : Function.Injective f := by
    intro p1 p2 hp
    have eq1 := hf p1
    have eq2 := hf p2
    rw [hp] at eq1
    exact signedMajorana_inj_of_conj h.1 (eq1.trans eq2.symm)
  Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)

private noncomputable def braidSubgroupPermHom (m : ℕ) :
    Subgroup.closure (Set.range (evenCliffordBraidUnit m)) →* Equiv.Perm (Bool × Fin m) where
  toFun := braidSubgroupPerm m
  map_one' := by
    ext1 p
    apply signedMajorana_injective m
    have hspec : ((((1 : Subgroup.closure (Set.range (evenCliffordBraidUnit m))).1 :
          EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
        signedMajorana m p *
        (((((1 : Subgroup.closure (Set.range (evenCliffordBraidUnit m))).1⁻¹ :
          (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
        signedMajorana m (braidSubgroupPerm m 1 p) :=
      Classical.choose_spec (braidSubgroup_conj_signedMajorana m _
        (1 : Subgroup.closure (Set.range (evenCliffordBraidUnit m))).2 p)
    simp only [Subgroup.coe_one, Units.val_one, OneMemClass.coe_one, one_mul, inv_one,
      mul_one] at hspec
    simpa [Equiv.Perm.one_apply] using hspec.symm
  map_mul' h1 h2 := by
    ext1 p
    apply signedMajorana_injective m
    have hspec1 : ((h1.1 * h2.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        signedMajorana m p *
        ((((((h1.1 * h2.1)⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
          CliffordAlgebra (cliffordForm m)))) =
        signedMajorana m (braidSubgroupPerm m (h1 * h2) p) :=
      Classical.choose_spec (braidSubgroup_conj_signedMajorana m (h1 * h2).1 (h1 * h2).2 p)
    have hspec2 : ((h2.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        signedMajorana m p *
        ((((h2.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
        signedMajorana m (braidSubgroupPerm m h2 p) :=
      Classical.choose_spec (braidSubgroup_conj_signedMajorana m h2.1 h2.2 p)
    have hspec3 : ((h1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        signedMajorana m (braidSubgroupPerm m h2 p) *
        ((((h1.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) =
        signedMajorana m (braidSubgroupPerm m h1 (braidSubgroupPerm m h2 p)) :=
      Classical.choose_spec
        (braidSubgroup_conj_signedMajorana m h1.1 h1.2 (braidSubgroupPerm m h2 p))
    rw [Equiv.Perm.mul_apply, ← hspec1, ← hspec3, ← hspec2]
    simp only [Subalgebra.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]

private theorem mem_ker_braidSubgroupPermHom_scalar (m : ℕ)
    (h : (braidSubgroupPermHom m).ker) :
    ∃ z : ℂ,
      ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = algebraMap ℂ _ z := by
  have hcomm_majorana : ∀ k : Fin m,
      ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * majorana m k =
        majorana m k * ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
    intro k
    have hspec : ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        signedMajorana m (false, k) *
        ((((h.1.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
          CliffordAlgebra (cliffordForm m))) =
        signedMajorana m (braidSubgroupPerm m h.1 (false, k)) :=
      Classical.choose_spec (braidSubgroup_conj_signedMajorana m h.1.1 h.1.2 (false, k))
    have hfix : braidSubgroupPerm m h.1 (false, k) = (false, k) := by
      have hker : braidSubgroupPermHom m h.1 = 1 := h.2
      exact congrFun (congrArg DFunLike.coe hker) (false, k)
    rw [hfix] at hspec
    have hspec' : ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        majorana m k *
        ((((h.1.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
          CliffordAlgebra (cliffordForm m))) = majorana m k := by
      simpa [signedMajorana] using hspec
    calc
      ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * majorana m k
          = ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * majorana m k *
              ((((h.1.1⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
                CliffordAlgebra (cliffordForm m))) *
              ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
            rw [coe_unit_inv_mul_right]
      _ = majorana m k * ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
            rw [hspec']
  have hcomm_all : ∀ a : CliffordAlgebra (cliffordForm m),
      ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) * a =
        a * ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
    intro a
    induction a using CliffordAlgebra.induction with
    | algebraMap c => exact (Algebra.commutes _ _).symm
    | ι v =>
      have hv : v = ∑ k : Fin m, v k • Pi.single k 1 := by ext i; simp [Pi.single_apply]
      rw [hv, map_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      congr 1
      rw [← majorana_def]
      exact hcomm_majorana k
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | mul a b ha hb =>
      rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · have _ : Algebra.IsCentral ℂ (CliffordAlgebra (cliffordForm m)) :=
      CliffordAlgebra.isCentral_of_even_finrank (cliffordForm_nondegenerate m)
        (by simpa using hm_even)
    have hmem_center : ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) ∈
        Subalgebra.center ℂ (CliffordAlgebra (cliffordForm m)) := by
      rw [Subalgebra.mem_center_iff]
      intro a
      exact (hcomm_all a).symm
    exact (Algebra.IsCentral.mem_center_iff ℂ).mp hmem_center
  · have _ : Algebra.IsCentral ℂ (EvenClifford m) :=
      TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank (cliffordForm_nondegenerate m)
        (by simpa using hm_odd)
    have hcomm_even : (h.1.1 : EvenClifford m) ∈ Subalgebra.center ℂ (EvenClifford m) := by
      rw [Subalgebra.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm_all y).symm
    obtain ⟨z, hz⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hcomm_even
    exact ⟨z, congrArg Subtype.val hz⟩

private theorem braidSubgroup_conj_and_unitary (m : ℕ) (h : (EvenClifford m)ˣ)
    (hh : h ∈ Subgroup.closure (Set.range (evenCliffordBraidUnit m))) :
    cliffordConj m ((h : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = h ∧
      cliffordAdjoint m ((h : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
        ((h : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = 1 := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨?_, cliffordBraidGenerator_adjoint_mul_self m j⟩
    simp only [evenCliffordBraidUnit_val, cliffordBraidGenerator, cliffordConj_smul,
      map_add, map_one, map_mul, cliffordConj_majorana]
    congr 1
    simp [Complex.conj_ofReal]
  | one => simp
  | mul x y _ _ ihx ihy =>
    refine ⟨by simp [ihx.1, ihy.1], ?_⟩
    simp only [Units.val_mul, Subalgebra.coe_mul, cliffordAdjoint_mul]
    calc
      cliffordAdjoint m ((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
          cliffordAdjoint m ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
          (((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
            ((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)))
          = cliffordAdjoint m ((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
              (cliffordAdjoint m ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) *
                ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m))) *
              ((y : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
            simp only [mul_assoc]
      _ = 1 := by rw [ihx.2, mul_one, ihy.2]
  | inv x _ ih =>
    refine ⟨?_, ?_⟩
    · have heq : cliffordConj m (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
            CliffordAlgebra (cliffordForm m)) *
          ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = 1 := by
        have hx := congrArg (fun u : EvenClifford m ↦ (u : CliffordAlgebra (cliffordForm m)))
          x.inv_mul
        rw [Subalgebra.coe_mul, OneMemClass.coe_one] at hx
        have hx' := congrArg (cliffordConj m) hx
        rwa [map_mul, map_one, ih.1] at hx'
      have heq2 := congrArg (· *
        (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m))) heq
      rw [one_mul] at heq2
      rwa [coe_unit_mul_inv_right] at heq2
    · have hunit : cliffordAdjoint m ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) =
          (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
            CliffordAlgebra (cliffordForm m)) := by
        have heq := congrArg (· *
          (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) :
            CliffordAlgebra (cliffordForm m))) ih.2
        rw [one_mul, coe_unit_mul_inv_right] at heq
        exact heq
      have hunit_inv : cliffordAdjoint m
          (((x⁻¹ : (EvenClifford m)ˣ) : EvenClifford m) : CliffordAlgebra (cliffordForm m)) =
          ((x : EvenClifford m) : CliffordAlgebra (cliffordForm m)) := by
        rw [← hunit, cliffordAdjoint_cliffordAdjoint]
      rw [hunit_inv]
      have heq := congrArg (fun u : EvenClifford m ↦ (u : CliffordAlgebra (cliffordForm m)))
        x.mul_inv
      simpa only [Subalgebra.coe_mul, OneMemClass.coe_one] using heq

/-- **Finiteness of the Clifford braid group**: the subgroup of `(EvenClifford m)ˣ` generated by
the braid units `g_j = -(1 + c_j c_{j+1}) / √2` is finite. -/
theorem evenCliffordBraidSubgroup_finite (m : ℕ) :
    Finite (Subgroup.closure (Set.range (evenCliffordBraidUnit m))) := by
  let φ := braidSubgroupPermHom m
  have hker_pm (h : φ.ker) :
      Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h) = 1 ∨
        Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h) = -1 := by
    set z := Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h)
    have hz : ((h.1.1 : EvenClifford m) : CliffordAlgebra (cliffordForm m)) = algebraMap ℂ _ z :=
      Classical.choose_spec (mem_ker_braidSubgroupPermHom_scalar m h)
    have hru := braidSubgroup_conj_and_unitary m h.1.1 h.1.2
    have hconj_z : conj z = z := by
      have h1 := congrArg (cliffordScalarCoefficient m) hru.1
      rw [hz, cliffordConj_algebraMap, cliffordScalarCoefficient_algebraMap,
        cliffordScalarCoefficient_algebraMap] at h1
      exact h1
    have hnorm_z : conj z * z = 1 := by
      have h2 := congrArg (cliffordScalarCoefficient m) hru.2
      rw [hz, cliffordAdjoint_algebraMap, ← map_mul,
        cliffordScalarCoefficient_algebraMap, cliffordScalarCoefficient_one] at h2
      exact h2
    rw [hconj_z, ← sq] at hnorm_z
    exact sq_eq_one_iff.mp hnorm_z
  have hker_finite : Finite φ.ker := by
    refine Finite.of_injective (fun h : φ.ker ↦
        decide (Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h) = 1)) ?_
    intro h1 h2 hdec
    dsimp only at hdec
    have hscalar_eq : Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h1) =
        Classical.choose (mem_ker_braidSubgroupPermHom_scalar m h2) := by
      rcases hker_pm h1 with h1p | h1n <;> rcases hker_pm h2 with h2p | h2n
      · exact h1p.trans h2p.symm
      · rw [h1p, h2n] at hdec; simp at hdec; norm_num at hdec
      · rw [h1n, h2p] at hdec; simp at hdec; norm_num at hdec
      · exact h1n.trans h2n.symm
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext1
    rw [Classical.choose_spec (mem_ker_braidSubgroupPermHom_scalar m h1),
      Classical.choose_spec (mem_ker_braidSubgroupPermHom_scalar m h2), hscalar_eq]
  exact φ.finite_iff_finite_ker_range.mpr ⟨hker_finite, Subtype.finite⟩

/-- The image of `BraidGroup m` in `(EvenClifford m)ˣ` under `evenCliffordBraidRep m` is finite. -/
theorem finite_range_evenCliffordBraidRep (m : ℕ) :
    Finite (Set.range (evenCliffordBraidRep m)) := by
  let H := Subgroup.closure (Set.range (evenCliffordBraidUnit m))
  have : Finite H := evenCliffordBraidSubgroup_finite m
  have hsub : Set.range (evenCliffordBraidRep m) ⊆ (H : Set (EvenClifford m)ˣ) := by
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe]
    induction b using BraidGroup.sigma_induction_on with
    | one => rw [map_one]; exact H.one_mem
    | mul a b ha hb => rw [map_mul]; exact H.mul_mem ha hb
    | inv a ha => rw [map_inv]; exact H.inv_mem ha
    | sigma j =>
      rw [evenCliffordBraidRep_sigma]
      exact Subgroup.subset_closure ⟨j, rfl⟩
  exact Set.Finite.subset (Set.toFinite (H : Set (EvenClifford m)ˣ)) hsub

end ConjugationAction

end BraidUnits

end TauCeti.TemperleyLieb

end
