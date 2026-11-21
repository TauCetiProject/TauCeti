/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.EvenClifford.Quotient
public import TauCeti.KnotTheory.TemperleyLieb

/-!
# Braid units in the even Clifford model at `δ = √2`

In the complex Clifford algebra `Cl_m = CliffordAlgebra (cliffordForm m)` with Majorana generators
`c_j = majorana m j`, put `d_j = c_j c_{j + 1}` and `u = (1 + i) / √2 = exp (π i / 4)`. This file
studies the **Clifford braid units**

  `g_j = cliffordBraidUnit m j = -(1 + d_j) / √2 = u • ((1 + i) • p_j - 1)`,

where `p_j = cliffordProjection m j = (1 + i d_j) / 2`. The unit `g_j` is the image under the even
Clifford comparison map `F_m = evenCliffordHom m` of the Temperley–Lieb crossing
`-u • 1 + i • e j` at `δ = √2`, so the braid relations of crossings in `TemperleyLieb` transport to
the `g_j`, and they define a representation `cliffordBraidRep m` of `BraidGroup m` in the units of
`Cl_m`, taking values in the even subalgebra `Cl_m⁰`.

* **Spectrum and order**: `g_j` acts by `i u` on `p_j` and by `-u` on `1 - p_j`; `g_j² = d_j`,
  `g_j⁴ = -1` and `g_j` has order `8`.
* **Unitarity**: `g_j† = g_j⁻¹` for the analytic adjoint `cliffordAdjoint m`, hence every
  `cliffordBraidRep m b` is unitary.
* **Signed permutations**: conjugation by `g_j` sends `c_j ↦ -c_{j + 1}` and `c_{j + 1} ↦ c_j`
  and fixes the other generators, so conjugation by `cliffordBraidRep m b` sends each `c_k` to
  `± c_{π_b(k)}`, where `π_b = BraidGroup.permHom m b` is the strand permutation of `b`.
* **Kauffman bracket**: for a unit `a` with `a² = i u` (equivalently `a² = -u⁻¹`), the Jones loop
  value `jonesDelta a` is `√2`, and `F_m` sends the Kauffman crossing `a • 1 + a⁻¹ • e j`, the value
  of `TemperleyLieb.jonesUnit a j`, to `(-a / u) • g_j`.
* **Adding a strand**: the coordinate inclusion `cliffordIncl` intertwines the representations on
  `n + 1` and `n + 2` strands with `BraidGroup.strandIncl`.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordBraidUnit`: the unit `g_j = -(1 + c_j c_{j + 1}) / √2`.
* `TauCeti.TemperleyLieb.cliffordBraidRep`: the representation `BraidGroup m →* (Cl_m)ˣ` with
  `σ_j ↦ g_j`.

## Main results

* `TauCeti.TemperleyLieb.coe_evenCliffordHom_crossing_eq_cliffordBraidUnit`: `g_j` is the image of
  the crossing `-u • 1 + i • e j` under `evenCliffordHom m`.
* `TauCeti.TemperleyLieb.cliffordBraidUnit_mul_cliffordProjection` and
  `TauCeti.TemperleyLieb.cliffordBraidUnit_mul_one_sub_cliffordProjection`: the eigenvalues `i u`
  and `-u`.
* `TauCeti.TemperleyLieb.cliffordBraidUnit_mul_self`,
  `TauCeti.TemperleyLieb.cliffordBraidUnit_pow_four` and
  `TauCeti.TemperleyLieb.orderOf_cliffordBraidUnit`: `g_j² = d_j`, `g_j⁴ = -1`, order `8`.
* `TauCeti.TemperleyLieb.cliffordBraidUnit_braid` and
  `TauCeti.TemperleyLieb.cliffordBraidUnit_mul_cliffordBraidUnit_comm`: the braid relations.
* `TauCeti.TemperleyLieb.cliffordAdjoint_cliffordBraidRep` and
  `TauCeti.TemperleyLieb.cliffordBraidRep_mem_even`: unitarity and evenness of the representation.
* `TauCeti.TemperleyLieb.exists_cliffordBraidRep_mul_majorana_mul_inv`: conjugation by a braid
  permutes the Majorana generators up to sign, along the strand permutation.
* `TauCeti.TemperleyLieb.jonesDelta_eq_sqrt_two` and
  `TauCeti.TemperleyLieb.coe_evenCliffordHom_crossing_eq_smul_cliffordBraidUnit`: comparison with
  the Kauffman-bracket representation `TemperleyLieb.jones`.
* `TauCeti.TemperleyLieb.cliffordIncl_cliffordBraidRep`: compatibility with adding a strand.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111 (the specialisation `t = i`).
* K. Iohara, G. I. Lehrer and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1702.08128, §5.3.
* D. A. Ivanov, *Non-Abelian statistics of half-quantum vortices in p-wave superconductors*,
  Phys. Rev. Lett. 86 (2001), 268–271 (the braiding of Majorana generators by
  `(1 + c_{j + 1} c_j) / √2`).
-/

public section

namespace TauCeti.TemperleyLieb

open BraidGroup (strand strandSucc strand_ne_strandSucc)

private theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'

private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt zero_le_two

private theorem inv_sqrt_two_mul_self :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← sq, sqrt_two_sq]

private theorem one_add_I_ne_zero : 1 + Complex.I ≠ 0 := fun h ↦ by
  simpa using congrArg Complex.re h

/-- `cliffordProjection` written with the crossed strands of `BraidGroup.sigma j`. -/
private theorem cliffordProjection_eq_strand (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j =
      (2 : ℂ)⁻¹ • (1 + Complex.I • (majorana m (strand j) * majorana m (strandSucc j))) := by
  rw [cliffordProjection_def, show strand j = ⟨j.val, by omega⟩ from Fin.ext (by simp),
    show strandSucc j = ⟨j.val + 1, by omega⟩ from Fin.ext (by simp)]

/-- The **Clifford braid unit** `g_j = -(1 + c_j c_{j + 1}) / √2`, a unit of
`CliffordAlgebra (cliffordForm m)` with inverse `-(1 - c_j c_{j + 1}) / √2`. -/
noncomputable def cliffordBraidUnit (m : ℕ) (j : Fin (m - 1)) :
    (CliffordAlgebra (cliffordForm m))ˣ where
  val := -((Real.sqrt 2 : ℂ)⁻¹ • (1 + majorana m (strand j) * majorana m (strandSucc j)))
  inv := -((Real.sqrt 2 : ℂ)⁻¹ • (1 - majorana m (strand j) * majorana m (strandSucc j)))
  val_inv := by
    have hd := majorana_mul_majorana_mul_self_of_ne (strand_ne_strandSucc j)
    simp only [neg_mul_neg, smul_mul_smul_comm, add_mul, mul_sub, one_mul, mul_one, hd,
      inv_sqrt_two_mul_self]
    module
  inv_val := by
    have hd := majorana_mul_majorana_mul_self_of_ne (strand_ne_strandSucc j)
    simp only [neg_mul_neg, smul_mul_smul_comm, sub_mul, mul_add, one_mul, mul_one, hd,
      inv_sqrt_two_mul_self]
    module

/-- The value of the Clifford braid unit. -/
theorem cliffordBraidUnit_val (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) =
      -((Real.sqrt 2 : ℂ)⁻¹ • (1 + majorana m (strand j) * majorana m (strandSucc j))) :=
  (rfl)

/-- The value of the inverse of the Clifford braid unit. -/
theorem cliffordBraidUnit_inv_val (m : ℕ) (j : Fin (m - 1)) :
    (((cliffordBraidUnit m j)⁻¹ : (CliffordAlgebra (cliffordForm m))ˣ) :
        CliffordAlgebra (cliffordForm m)) =
      -((Real.sqrt 2 : ℂ)⁻¹ • (1 - majorana m (strand j) * majorana m (strandSucc j))) :=
  (rfl)

/-- Each Clifford braid unit lies in the even Clifford subalgebra. -/
theorem cliffordBraidUnit_mem_even (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) ∈ EvenClifford m := by
  rw [cliffordBraidUnit_val]
  exact neg_mem (Subalgebra.smul_mem _
    (add_mem (one_mem _) (majorana_mul_majorana_mem_even m _ _)) _)

/-- The Clifford braid unit is unitary for the analytic adjoint: `g_j† = g_j⁻¹`. -/
@[simp]
theorem cliffordAdjoint_cliffordBraidUnit (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordBraidUnit m j) = ↑(cliffordBraidUnit m j)⁻¹ := by
  have hne := strand_ne_strandSucc j
  simp [cliffordBraidUnit_val, cliffordBraidUnit_inv_val,
    majorana_mul_majorana_comm_of_ne hne.symm, Complex.conj_ofReal, sub_eq_add_neg]

/-! ### The braid unit as the image of a Temperley–Lieb crossing -/

/-- `evenCliffordHom` sends the Kauffman crossing `α • 1 + β • e j` to
`α • 1 + (β * √2) • p_j`. -/
theorem coe_evenCliffordHom_crossing (m : ℕ) (α β : ℂ) (j : Fin (m - 1)) :
    (evenCliffordHom m (crossing (Real.sqrt 2 : ℂ) α β j) : CliffordAlgebra (cliffordForm m)) =
      α • 1 + (β * Real.sqrt 2) • cliffordProjection m j := by
  simp [mul_smul]

/-- The Clifford braid unit is the image under `evenCliffordHom` of the crossing
`-u • 1 + i • e j` at `u = (1 + i) / √2 = exp (π i / 4)`. -/
theorem coe_evenCliffordHom_crossing_eq_cliffordBraidUnit (m : ℕ) (j : Fin (m - 1)) :
    (evenCliffordHom m
        (crossing (Real.sqrt 2 : ℂ) (-((1 + Complex.I) / Real.sqrt 2)) Complex.I j) :
        CliffordAlgebra (cliffordForm m)) = cliffordBraidUnit m j := by
  rw [coe_evenCliffordHom_crossing, cliffordProjection_eq_strand, cliffordBraidUnit_val]
  have hs := sqrt_two_ne_zero
  match_scalars <;> field_simp
  · linear_combination Complex.I * sqrt_two_sq
  · linear_combination Complex.I ^ 2 * sqrt_two_sq + 2 * Complex.I_sq

/-- The Clifford braid unit in terms of the Clifford projection:
`g_j = u • ((1 + i) • p_j - 1)` with `u = (1 + i) / √2 = exp (π i / 4)`. -/
theorem cliffordBraidUnit_val_eq_smul_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) =
      ((1 + Complex.I) / Real.sqrt 2) • ((1 + Complex.I) • cliffordProjection m j - 1) := by
  rw [cliffordProjection_eq_strand, cliffordBraidUnit_val]
  have hs := sqrt_two_ne_zero
  match_scalars <;> field_simp
  · linear_combination -Complex.I_sq
  · linear_combination (-2 - Complex.I) * Complex.I_sq

/-- `p_j` is an eigenvector of the Clifford braid unit with eigenvalue `i u`, where
`u = (1 + i) / √2`. -/
theorem cliffordBraidUnit_mul_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * cliffordProjection m j =
      (Complex.I * ((1 + Complex.I) / Real.sqrt 2)) • cliffordProjection m j := by
  rw [cliffordBraidUnit_val_eq_smul_cliffordProjection, smul_mul_assoc, sub_mul, smul_mul_assoc,
    cliffordProjection_mul_self, one_mul]
  module

/-- `1 - p_j` is an eigenvector of the Clifford braid unit with eigenvalue `-u`, where
`u = (1 + i) / √2`. -/
theorem cliffordBraidUnit_mul_one_sub_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * (1 - cliffordProjection m j) =
      (-((1 + Complex.I) / Real.sqrt 2)) • (1 - cliffordProjection m j) := by
  rw [cliffordBraidUnit_val_eq_smul_cliffordProjection, smul_mul_assoc, sub_mul, mul_sub,
    mul_sub, smul_mul_assoc, smul_mul_assoc, cliffordProjection_mul_self, one_mul, mul_one,
    one_mul]
  module

/-! ### Powers and order -/

/-- The square of the Clifford braid unit is the Majorana bivector: `g_j² = c_j c_{j + 1}`. -/
theorem cliffordBraidUnit_mul_self (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * cliffordBraidUnit m j =
      majorana m (strand j) * majorana m (strandSucc j) := by
  have hd := majorana_mul_majorana_mul_self_of_ne (strand_ne_strandSucc j)
  simp only [cliffordBraidUnit_val, neg_mul_neg, smul_mul_smul_comm, add_mul, mul_add, one_mul,
    mul_one, hd, inv_sqrt_two_mul_self]
  module

/-- The fourth power of a Clifford braid unit is `-1`. -/
theorem cliffordBraidUnit_pow_four (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidUnit m j ^ 4 = -1 := by
  ext
  rw [Units.val_pow_eq_pow_val, show 4 = 2 * 2 from rfl, pow_mul,
    sq (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)), cliffordBraidUnit_mul_self, sq,
    majorana_mul_majorana_mul_self_of_ne (strand_ne_strandSucc j), Units.val_neg, Units.val_one]

/-- The eighth power of a Clifford braid unit is `1`. -/
theorem cliffordBraidUnit_pow_eight (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidUnit m j ^ 8 = 1 := by
  rw [show 8 = 4 * 2 from rfl, pow_mul, cliffordBraidUnit_pow_four, neg_one_sq]

/-- Each Clifford braid unit has order exactly `8`. -/
theorem orderOf_cliffordBraidUnit (m : ℕ) (j : Fin (m - 1)) :
    orderOf (cliffordBraidUnit m j) = 8 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 2) ?_ (cliffordBraidUnit_pow_eight m j)
  rw [show 2 ^ 2 = 4 from rfl, cliffordBraidUnit_pow_four]
  intro h
  have := congrArg (fun x : (CliffordAlgebra (cliffordForm m))ˣ ↦
    CliffordAlgebra.scalarTrace (cliffordForm m) (x : CliffordAlgebra (cliffordForm m))) h
  norm_num [CliffordAlgebra.scalarTrace_one] at this

/-! ### Braid relations and the braid group representation -/

/-- Clifford braid units on disjoint pairs of strands commute. -/
theorem cliffordBraidUnit_mul_cliffordBraidUnit_comm (m : ℕ) {i j : Fin (m - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    cliffordBraidUnit m i * cliffordBraidUnit m j =
      cliffordBraidUnit m j * cliffordBraidUnit m i := by
  ext
  have := congrArg (fun x ↦ (evenCliffordHom m x : CliffordAlgebra (cliffordForm m)))
    (crossing_mul_crossing_comm (δ := (Real.sqrt 2 : ℂ))
      (-((1 + Complex.I) / Real.sqrt 2)) Complex.I
      (-((1 + Complex.I) / Real.sqrt 2)) Complex.I h)
  simpa only [map_mul, Subalgebra.coe_mul, coe_evenCliffordHom_crossing_eq_cliffordBraidUnit,
    Units.val_mul] using this

/-- Clifford braid units on adjacent pairs of strands satisfy the braid relation. -/
theorem cliffordBraidUnit_braid (m : ℕ) {i j : Fin (m - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cliffordBraidUnit m i * cliffordBraidUnit m j * cliffordBraidUnit m i =
      cliffordBraidUnit m j * cliffordBraidUnit m i * cliffordBraidUnit m j := by
  ext
  have hpoly : Complex.I * ((-((1 + Complex.I) / Real.sqrt 2)) ^ 2 +
      -((1 + Complex.I) / Real.sqrt 2) * Complex.I * Real.sqrt 2 + Complex.I ^ 2) = 0 := by
    have hs := sqrt_two_ne_zero
    field_simp
    linear_combination -Complex.I ^ 2 * sqrt_two_sq + Complex.I * Complex.I_sq
  have := congrArg (fun x ↦ (evenCliffordHom m x : CliffordAlgebra (cliffordForm m)))
    (crossing_braid (δ := (Real.sqrt 2 : ℂ)) hpoly h)
  simpa only [map_mul, Subalgebra.coe_mul, coe_evenCliffordHom_crossing_eq_cliffordBraidUnit,
    Units.val_mul] using this

/-- The **Clifford braid representation** `BraidGroup m →* (Cl_m)ˣ` sending the elementary braid
`σ_j` to the Clifford braid unit `g_j = -(1 + c_j c_{j + 1}) / √2`. -/
noncomputable def cliffordBraidRep (m : ℕ) : BraidGroup m →* (CliffordAlgebra (cliffordForm m))ˣ :=
  BraidGroup.lift (cliffordBraidUnit m) (cliffordBraidUnit_mul_cliffordBraidUnit_comm m)
    (cliffordBraidUnit_braid m)

/-- The Clifford braid representation sends `σ_j` to the Clifford braid unit `g_j`. -/
@[simp]
theorem cliffordBraidRep_sigma (m : ℕ) (j : Fin (m - 1)) :
    cliffordBraidRep m (BraidGroup.sigma j) = cliffordBraidUnit m j :=
  BraidGroup.lift_sigma _ _ _ j

/-- The Clifford braid representation is unitary for the analytic adjoint:
`ρ(b)† = ρ(b)⁻¹` for every braid `b`. -/
@[simp]
theorem cliffordAdjoint_cliffordBraidRep (m : ℕ) (b : BraidGroup m) :
    cliffordAdjoint m (cliffordBraidRep m b) = ↑(cliffordBraidRep m b)⁻¹ := by
  induction b using BraidGroup.sigma_induction_on with
  | sigma j => rw [cliffordBraidRep_sigma, cliffordAdjoint_cliffordBraidUnit]
  | one => simp
  | mul b b' hb hb' => simp [hb, hb']
  | inv b hb =>
    rw [map_inv, inv_inv, ← hb, cliffordAdjoint_cliffordAdjoint]

/-- The Clifford braid representation takes values in the even Clifford subalgebra. -/
theorem cliffordBraidRep_mem_even (m : ℕ) (b : BraidGroup m) :
    (cliffordBraidRep m b : CliffordAlgebra (cliffordForm m)) ∈ EvenClifford m := by
  induction b using BraidGroup.sigma_induction_on with
  | sigma j => simpa using cliffordBraidUnit_mem_even m j
  | one => simp
  | mul b b' hb hb' => simpa using mul_mem hb hb'
  | inv b hb =>
    rw [map_inv, ← cliffordAdjoint_cliffordBraidRep]
    exact cliffordAdjoint_mem_even m hb

/-! ### Conjugation of the Majorana generators -/

/-- Conjugation by `g_j` sends `c_j` to `-c_{j + 1}`. -/
theorem cliffordBraidUnit_mul_majorana_strand_mul_inv (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * majorana m (strand j) *
        ↑(cliffordBraidUnit m j)⁻¹ = -majorana m (strandSucc j) := by
  have hne := strand_ne_strandSucc j
  have haba : majorana m (strand j) * majorana m (strandSucc j) * majorana m (strand j) =
      -majorana m (strandSucc j) := by
    rw [majorana_mul_majorana_comm_of_ne hne, neg_mul, mul_assoc, majorana_mul_self, mul_one]
  have hbab : majorana m (strandSucc j) * (majorana m (strand j) * majorana m (strandSucc j)) =
      -majorana m (strand j) := by
    rw [majorana_mul_majorana_comm_of_ne hne, mul_neg, ← mul_assoc, majorana_mul_self, one_mul]
  have h : (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * majorana m (strand j) =
      -majorana m (strandSucc j) * cliffordBraidUnit m j := by
    simp only [cliffordBraidUnit_val, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, add_mul,
      mul_add, one_mul, mul_one, haba, hbab]
    module
  rw [h, Units.mul_inv_cancel_right]

/-- Conjugation by `g_j` sends `c_{j + 1}` to `c_j`. -/
theorem cliffordBraidUnit_mul_majorana_strandSucc_mul_inv (m : ℕ) (j : Fin (m - 1)) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * majorana m (strandSucc j) *
        ↑(cliffordBraidUnit m j)⁻¹ = majorana m (strand j) := by
  have habb : majorana m (strand j) * majorana m (strandSucc j) * majorana m (strandSucc j) =
      majorana m (strand j) := by
    rw [mul_assoc, majorana_mul_self, mul_one]
  have haab : majorana m (strand j) * (majorana m (strand j) * majorana m (strandSucc j)) =
      majorana m (strandSucc j) := by
    rw [← mul_assoc, majorana_mul_self, one_mul]
  have h : (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) *
      majorana m (strandSucc j) = majorana m (strand j) * cliffordBraidUnit m j := by
    simp only [cliffordBraidUnit_val, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, add_mul,
      mul_add, one_mul, mul_one, habb, haab]
    module
  rw [h, Units.mul_inv_cancel_right]

/-- Conjugation by `g_j` fixes every Majorana generator `c_k` with `k ∉ {j, j + 1}`. -/
theorem cliffordBraidUnit_mul_majorana_mul_inv_of_ne (m : ℕ) {j : Fin (m - 1)} {k : Fin m}
    (hk : k ≠ strand j) (hk' : k ≠ strandSucc j) :
    (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) * majorana m k *
        ↑(cliffordBraidUnit m j)⁻¹ = majorana m k := by
  have hc : Commute (cliffordBraidUnit m j : CliffordAlgebra (cliffordForm m)) (majorana m k) := by
    rw [cliffordBraidUnit_val]
    exact (((Commute.one_left _).add_left
      (commute_majorana_majorana_mul_majorana_of_ne hk hk').symm).smul_left _).neg_left
  rw [hc.eq, Units.mul_inv_cancel_right]

/-- Conjugation by the Clifford braid representation permutes the Majorana generators up to sign,
following the strand permutation `BraidGroup.permHom`: for every braid `b` and strand `k` there is
a sign `ε = ±1` with `ρ(b) c_k ρ(b)⁻¹ = ε c_{π_b(k)}`. -/
theorem exists_cliffordBraidRep_mul_majorana_mul_inv (m : ℕ) (b : BraidGroup m) (k : Fin m) :
    ∃ ε : ℤˣ, (cliffordBraidRep m b : CliffordAlgebra (cliffordForm m)) * majorana m k *
        ↑(cliffordBraidRep m b)⁻¹ = (ε : ℤ) • majorana m (BraidGroup.permHom m b k) := by
  induction b using BraidGroup.sigma_induction_on generalizing k with
  | sigma j =>
    rw [cliffordBraidRep_sigma, BraidGroup.permHom_sigma]
    by_cases hk : k = strand j
    · subst hk
      refine ⟨-1, ?_⟩
      rw [cliffordBraidUnit_mul_majorana_strand_mul_inv, BraidGroup.transposition_apply_strand,
        Units.val_neg, Units.val_one, neg_one_zsmul]
    by_cases hk' : k = strandSucc j
    · subst hk'
      refine ⟨1, ?_⟩
      rw [cliffordBraidUnit_mul_majorana_strandSucc_mul_inv,
        BraidGroup.transposition_apply_strandSucc, Units.val_one, one_smul]
    refine ⟨1, ?_⟩
    rw [cliffordBraidUnit_mul_majorana_mul_inv_of_ne m hk hk', BraidGroup.transposition_eq_swap,
      Equiv.swap_apply_of_ne_of_ne hk hk', Units.val_one, one_smul]
  | one => exact ⟨1, by simp⟩
  | mul b b' hb hb' =>
    obtain ⟨ε', hε'⟩ := hb' k
    obtain ⟨ε, hε⟩ := hb (BraidGroup.permHom m b' k)
    refine ⟨ε * ε', ?_⟩
    calc ((cliffordBraidRep m (b * b') : (CliffordAlgebra (cliffordForm m))ˣ) :
          CliffordAlgebra (cliffordForm m)) * majorana m k * ↑(cliffordBraidRep m (b * b'))⁻¹
        = ↑(cliffordBraidRep m b) * (↑(cliffordBraidRep m b') * majorana m k *
            ↑(cliffordBraidRep m b')⁻¹) * ↑(cliffordBraidRep m b)⁻¹ := by
          simp only [map_mul, mul_inv_rev, Units.val_mul, mul_assoc]
      _ = ((ε * ε' : ℤˣ) : ℤ) • majorana m (BraidGroup.permHom m (b * b') k) := by
          rw [hε', mul_smul_comm, smul_mul_assoc, hε, smul_smul, map_mul, Equiv.Perm.mul_apply,
            Units.val_mul, mul_comm]
  | inv b hb =>
    obtain ⟨ε, hε⟩ := hb ((BraidGroup.permHom m b)⁻¹ k)
    rw [Equiv.Perm.eq_inv_iff_eq.mp rfl] at hε
    refine ⟨ε, ?_⟩
    have hk : majorana m k = ↑(cliffordBraidRep m b) *
        ((ε : ℤ) • majorana m ((BraidGroup.permHom m b)⁻¹ k)) * ↑(cliffordBraidRep m b)⁻¹ := by
      rw [mul_smul_comm, smul_mul_assoc, hε, smul_smul, ← Units.val_mul,
        Int.units_mul_self, Units.val_one, one_smul]
    rw [map_inv, inv_inv, map_inv, hk]
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

/-! ### Comparison with the Kauffman-bracket representation -/

/-- If `a² = i u` with `u = (1 + i) / √2`, the Jones loop value `-(a² + a⁻²)` is `√2`. -/
theorem jonesDelta_eq_sqrt_two {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = Complex.I * ((1 + Complex.I) / Real.sqrt 2)) :
    jonesDelta a = Real.sqrt 2 := by
  have hs := sqrt_two_ne_zero
  have hI := one_add_I_ne_zero
  rw [jonesDelta_def, Units.val_inv_eq_inv_val, inv_pow, ha]
  field_simp
  linear_combination (-1 - Complex.I - Complex.I ^ 2) * sqrt_two_sq -
    (Complex.I ^ 2 + 2 * Complex.I + 2) * Complex.I_sq

/-- If `a² = i u` with `u = (1 + i) / √2`, then `evenCliffordHom` sends the Kauffman crossing
`a • 1 + a⁻¹ • e j` at `δ = √2` to `(-a / u) • g_j`. This is the crossing whose value at the loop
parameter `jonesDelta a`, which equals `√2` by `jonesDelta_eq_sqrt_two`, is
`TemperleyLieb.jonesUnit a j`. -/
theorem coe_evenCliffordHom_crossing_eq_smul_cliffordBraidUnit (m : ℕ) {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = Complex.I * ((1 + Complex.I) / Real.sqrt 2)) (j : Fin (m - 1)) :
    (evenCliffordHom m (crossing (Real.sqrt 2 : ℂ) a ↑a⁻¹ j) : CliffordAlgebra (cliffordForm m)) =
      (-(a : ℂ) / ((1 + Complex.I) / Real.sqrt 2)) • (cliffordBraidUnit m j :
        CliffordAlgebra (cliffordForm m)) := by
  have hs := sqrt_two_ne_zero
  have hI := one_add_I_ne_zero
  rw [← coe_evenCliffordHom_crossing_eq_cliffordBraidUnit, coe_evenCliffordHom_crossing,
    coe_evenCliffordHom_crossing, Units.val_inv_eq_inv_val]
  match_scalars <;> field_simp
  rw [ha]
  field_simp
  linear_combination Complex.I_sq

/-! ### Compatibility with adding a strand -/

/-- The coordinate inclusion `Cl_{n + 1} → Cl_{n + 2}` sends `g_j` to `g_j`. -/
@[simp]
theorem cliffordIncl_cliffordBraidUnit (n : ℕ) (j : Fin n) :
    cliffordIncl (n + 1) (cliffordBraidUnit (n + 1) j) = cliffordBraidUnit (n + 2) j.castSucc := by
  have h0 : (strand (n := n + 1) j).castSucc = strand (n := n + 2) j.castSucc := Fin.ext (by simp)
  have h1 : (strandSucc (n := n + 1) j).castSucc = strandSucc (n := n + 2) j.castSucc :=
    Fin.ext (by simp)
  simp [cliffordBraidUnit_val, h0, h1]

/-- The Clifford braid representation commutes with adding a strand: the coordinate inclusion
`Cl_{n + 1} → Cl_{n + 2}` intertwines it with `BraidGroup.strandIncl`. -/
@[simp]
theorem cliffordIncl_cliffordBraidRep (n : ℕ) (b : BraidGroup (n + 1)) :
    cliffordIncl (n + 1) (cliffordBraidRep (n + 1) b) =
      cliffordBraidRep (n + 2) (BraidGroup.strandIncl b) := by
  have hhom : (Units.map (cliffordIncl (n + 1)).toMonoidHom).comp (cliffordBraidRep (n + 1)) =
      (cliffordBraidRep (n + 2)).comp BraidGroup.strandIncl :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg (fun f : BraidGroup (n + 1) →* (CliffordAlgebra (cliffordForm (n + 2)))ˣ ↦
    ((f b : (CliffordAlgebra (cliffordForm (n + 2)))ˣ) : CliffordAlgebra (cliffordForm (n + 2))))
    hhom

end TauCeti.TemperleyLieb
