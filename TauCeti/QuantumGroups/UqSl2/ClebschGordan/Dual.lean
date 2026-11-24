/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Projection
public import TauCeti.QuantumGroups.UqSl2.Dual.LadderModule

import TauCeti.Algebra.Ring.Int.Units

/-!
# The trivial Clebsch–Gordan channel and duality

At a generic parameter `q`, the tensor square `L_m^ε ⊗ L_m^ε` of a signed ladder module contains
the trivial module exactly once, as its last Clebsch–Gordan channel `j = m`, spanned by the
highest vector `w_m = ∑_i α_i v_i ⊗ v_(m - i)` of weight `1`. This file identifies the
coevaluation and the evaluation of the right dual of `L_m^ε` with the inclusion of that channel
and the projection onto it, once the contragredient module is identified with `L_m^ε` by
`LadderModule.hopfDualEquiv` (the module form of `LadderModule.contragredientEquiv`).

Write `C : L_m^ε ≃ (L_m^ε)*` for that isomorphism. The results are:

* invariant vectors and invariant functionals of `L_m^ε ⊗ L_m^ε` only see the trivial channel:
  an invariant vector is a multiple of `w_m`, and an invariant functional `g` is
  `g(w_m)` times the coordinate of the channel projection;
* the coevaluation `1 ↦ ∑_i b_i ⊗ b^i`, followed by `C⁻¹` on the second factor, is
  `(-ε)^m q^(-m) w_m`;
* the evaluation `φ ⊗ v ↦ φ(v)`, precomposed with `C` on the first factor, is `q^m [m + 1]_q`
  times the coordinate of the projection onto the trivial channel.

The two scalars come from the corner entry `C(v_m)(v₀) = (-ε)^m q^m` and from the identity
`α_i C(v_i)(v_(m - i)) = q^(2i)`, whose sum over `i` is `q^m [m + 1]_q`.

The coevaluation `TauCeti.BialgebraModule.dualCoeval` and the evaluation
`TauCeti.BialgebraModule.dualEval` are the underlying maps of the right duality of
`TauCeti.FiniteHopfModuleCat.instRightRigidCategory`.

## Main results

* `TauCeti.UqSl2.eq_basis_repr_clebschGordanProjection_smul_of_forall_smul_eq`: an invariant
  vector of `L_m^ε ⊗ L_m^ε` is a multiple of `w_m`.
* `TauCeti.UqSl2.apply_eq_basis_repr_clebschGordanProjection_smul`: an invariant functional
  factors through the projection onto the trivial channel.
* `TauCeti.UqSl2.tensorMap_hopfDualEquiv_symm_dualCoeval`: coevaluation is the trivial
  Clebsch–Gordan vector, up to `(-ε)^m q^(-m)`.
* `TauCeti.UqSl2.trivialEquiv_dualEval_tensorMap_hopfDualEquiv`: evaluation is the trivial
  channel coordinate, up to `q^m [m + 1]_q`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XIV, for the
  Clebsch–Gordan decomposition and duality of the modules `V_(ε,n)`.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

variable {q : ℂ} [Fact (q ≠ 0)] {m : ℕ} {ε : ℤˣ}

omit [Fact (q ≠ 0)] in
/-- The weight `εδ q^(m + n - 2j)` of a Clebsch–Gordan vector of `L_m^ε ⊗ L_m^ε` is not `1`
outside the trivial channel `j = m`. -/
private theorem units_mul_self_mul_zpow_ne_one (hq : IsGenericQuantumParameter q)
    {j : Fin (min m m + 1)} (hj : j ≠ ⟨m, by simp⟩) :
    ((ε * ε : ℤˣ) : ℂ) * q ^ ((m : ℤ) + m - 2 * (j : ℕ)) ≠ 1 := by
  have hjm : (j : ℕ) < m := by
    have := j.isLt
    have : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
    omega
  rw [Int.units_mul_self, Units.val_one, Int.cast_one, one_mul,
    show (m : ℤ) + m - 2 * (j : ℕ) = ((2 * (m - j) : ℕ) : ℤ) by omega, zpow_natCast]
  exact hq.pow_ne_one (by omega)

/-- At a generic parameter, an invariant vector `x` of `L_m^ε ⊗ L_m^ε`, one on which `U_q` acts
through the counit, is a multiple of the trivial-channel Clebsch–Gordan vector `w_m`: the
multiple is the coordinate of its projection onto that channel. -/
theorem eq_basis_repr_clebschGordanProjection_smul_of_forall_smul_eq
    (hq : IsGenericQuantumParameter q)
    {x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q m ε)}
    (hx : ∀ a : UqSl2 q, a • x = Coalgebra.counit (R := ℂ) a • x) :
    x = (basis q _ _).repr (clebschGordanProjection hq ⟨m, by simp⟩ x) 0 •
      clebschGordanVector q m ε m ε m := by
  have hw : x ∈ weightSpace q _ (((1 : ℤˣ) : ℂ) * q ^ (0 : ℕ)) := by
    rw [mem_weightSpace_iff, hx, counit_k]
    simp
  have he : e q • x = 0 := by rw [hx, counit_e, zero_smul]
  have hf : f q ^ (0 + 1) • x = 0 := by rw [zero_add, pow_one, hx, counit_f, zero_smul]
  -- The invariant vector is the image of `v₀` under a module map out of `L_0^+`; its channel
  -- components are therefore Schur multiples of `v₀`, and vanish outside the trivial channel.
  set ℓ := LadderModule.lift hq hw he hf
  have hproj (j : Fin (min m m + 1)) : clebschGordanProjection hq j x =
      schurScalar ((clebschGordanProjection hq j).comp ℓ) • vec q _ _ 0 := by
    rw [← apply_vec_eq_schurScalar_smul hq, LinearMap.comp_apply, lift_vec_zero]
  conv_lhs => rw [← sum_clebschGordanInclusion_projection hq x]
  rw [Finset.sum_eq_single ⟨m, by simp⟩ (fun j _ hj => ?_) (by simp), hproj,
    LinearMap.map_smul_of_tower, clebschGordanInclusion_vec_zero]
  · simp
  · have hne : (0 : ℕ) ≠ m + m - 2 * (j : ℕ) := by
      have := j.isLt
      have : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
      omega
    rw [hproj, schurScalar_eq_zero_of_ne hq (.inl hne), zero_smul, map_zero]

/-- At a generic parameter, an invariant functional `g` on `L_m^ε ⊗ L_m^ε`, that is a module map
to the trivial module, is its value on the trivial-channel Clebsch–Gordan vector `w_m` times the
coordinate of the projection onto that channel. -/
theorem apply_eq_basis_repr_clebschGordanProjection_smul (hq : IsGenericQuantumParameter q)
    (g : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q m ε) →ₗ[UqSl2 q]
      Trivial ℂ (UqSl2 q))
    (y : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q m ε)) :
    g y = (basis q _ _).repr (clebschGordanProjection hq ⟨m, by simp⟩ y) 0 •
      g (clebschGordanVector q m ε m ε m) := by
  conv_lhs => rw [← sum_clebschGordanInclusion_projection hq y]
  rw [map_sum, Finset.sum_eq_single ⟨m, by simp⟩ (fun j _ hj => ?_) (by simp),
    ← LinearMap.comp_apply, apply_eq_basis_repr_zero_smul hq, LinearMap.comp_apply,
    clebschGordanInclusion_vec_zero]
  rw [← LinearMap.comp_apply, apply_eq_basis_repr_zero_smul hq, LinearMap.comp_apply,
    clebschGordanInclusion_vec_zero,
    apply_eq_zero_of_mem_weightSpace g (units_mul_self_mul_zpow_ne_one hq hj)
      (clebschGordanVector_mem_weightSpace _), smul_zero]

/-- The reversed-diagonal entries `κ_i = C(v_i)(v_(m - i))` of the contragredient isomorphism
satisfy `[i + 1]_q κ_(i+1) = -ε q^(2i + 2 - m) [m - i]_q κ_i`, by the action of `F`. -/
private theorem quantumInteger_mul_contragredientEquiv_vec_succ
    (hq : IsGenericQuantumParameter q) (i : ℕ) :
    quantumInteger q ((i : ℤ) + 1) *
        contragredientEquiv (m := m) (ε := ε) hq (vec q m ε ((i : ℤ) + 1))
          (vec q m ε ((m : ℤ) - (i + 1))) =
      -(ε : ℂ) * q ^ (2 * (i : ℤ) + 2 - m) * quantumInteger q ((m : ℤ) - i) *
        contragredientEquiv hq (vec q m ε i) (vec q m ε ((m : ℤ) - i)) := by
  have h := LinearMap.congr_fun
    (contragredientEquiv_intertwines (m := m) (ε := ε) hq (f q) (vec q m ε i))
    (vec q m ε ((m : ℤ) - (i + 1)))
  rw [← smul_def, f_smul_vec, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hopfDual_f_apply_vec, show (m : ℤ) - (i + 1) + 1 = m - i by ring,
    show (m : ℤ) - 2 * ((m : ℤ) - (i + 1)) = 2 * i + 2 - m by ring] at h
  exact h

/-- The products `α_i κ_i` of the trivial-channel Clebsch–Gordan coefficients with the
reversed-diagonal entries of the contragredient isomorphism are `q^(2i)`. -/
private theorem clebschGordanCoeff_mul_contragredientEquiv_vec (hq : IsGenericQuantumParameter q)
    {i : ℕ} (hi : i ≤ m) :
    clebschGordanCoeff q m m ε m i *
        contragredientEquiv (m := m) (ε := ε) hq (vec q m ε i) (vec q m ε ((m : ℤ) - i)) =
      q ^ (2 * i) := by
  have hq0 : q ≠ 0 := Fact.out
  induction i with
  | zero => simp [contragredientEquiv_vec_zero]
  | succ i ih =>
    have h1 := quantumInteger_mul_clebschGordanCoeff_succ hq (m := m) (n := m) (δ := ε) (j := m)
      (i := i) (by omega)
    rw [show (m : ℤ) - m + i + 1 = i + 1 by ring] at h1
    have h2 := quantumInteger_mul_contragredientEquiv_vec_succ (m := m) (ε := ε) hq i
    have hne : quantumInteger q ((m : ℤ) - i) * quantumInteger q ((i : ℤ) + 1) ≠ 0 :=
      mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (quantumInteger_ne_zero hq (by omega))
    have hqq : q ^ ((m : ℤ) - 2 * i) * q ^ (2 * (i : ℤ) + 2 - m) = q ^ 2 := by
      rw [← zpow_add₀ hq0, show (m : ℤ) - 2 * i + (2 * i + 2 - m) = (2 : ℕ) by ring, zpow_natCast]
    have hε : ((ε : ℤ) : ℂ) ^ 2 = 1 := Int.cast_units_sq ε
    push_cast
    apply mul_left_cancel₀ hne
    linear_combination
      (quantumInteger q ((i : ℤ) + 1) *
        contragredientEquiv hq (vec q m ε ((i : ℤ) + 1)) (vec q m ε ((m : ℤ) - (i + 1)))) * h1 +
      (-(ε : ℂ) * q ^ ((m : ℤ) - 2 * i) * quantumInteger q ((i : ℤ) + 1) *
        clebschGordanCoeff q m m ε m i) * h2 +
      ((ε : ℂ) ^ 2 * q ^ ((m : ℤ) - 2 * i) * q ^ (2 * (i : ℤ) + 2 - m) *
        quantumInteger q ((i : ℤ) + 1) * quantumInteger q ((m : ℤ) - i)) * ih (by omega) +
      (q ^ ((m : ℤ) - 2 * i) * q ^ (2 * (i : ℤ) + 2 - m) * quantumInteger q ((i : ℤ) + 1) *
        quantumInteger q ((m : ℤ) - i) * q ^ (2 * i)) * hε +
      (quantumInteger q ((i : ℤ) + 1) * quantumInteger q ((m : ℤ) - i) * q ^ (2 * i)) * hqq

/-- The functional `v ⊗ w ↦ (v₀-coordinate of v) · C(w)(v₀)` on `L_m^ε ⊗ L_m^ε`, used to read off
the scalar relating coevaluation and the trivial-channel Clebsch–Gordan vector. -/
private def coevalCoord (hq : IsGenericQuantumParameter q) :
    Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q m ε) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map ((basis q m ε).coord 0)
      (LinearMap.applyₗ (vec q m ε 0) ∘ₗ (contragredientEquiv hq).toLinearMap) ∘ₗ
    (tensorEquiv ℂ (UqSl2 q) _ _).toLinearMap

private theorem coevalCoord_tmul (hq : IsGenericQuantumParameter q) (v w : LadderModule q m ε) :
    coevalCoord hq (tmul ℂ (UqSl2 q) v w) =
      (basis q m ε).coord 0 v * contragredientEquiv hq w (vec q m ε 0) := by
  simp [coevalCoord]

/-- On the coevaluation vector, after `C⁻¹` on the second factor, the functional
`coevalCoord` is `r`, by the dual-basis expansion of `v₀`. -/
private theorem coevalCoord_tensorMap_dualCoeval (hq : IsGenericQuantumParameter q)
    (r : Trivial ℂ (UqSl2 q)) :
    coevalCoord hq (tensorMap ℂ (UqSl2 q) LinearMap.id
        (hopfDualEquiv (m := m) (ε := ε) hq).symm.toLinearMap
        (dualCoeval ℂ (UqSl2 q) (LadderModule q m ε) r)) = trivialEquiv ℂ (UqSl2 q) r := by
  let b := Module.Basis.ofVectorSpace ℂ (LadderModule q m ε)
  simp only [dualCoeval_apply_eq_sum, map_sum, tensorMap_tmul, coevalCoord_tmul,
    LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hopfDualEquiv_symm_apply,
    LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  conv_rhs => rw [← mul_one (trivialEquiv ℂ (UqSl2 q) r)]
  congr 1
  have := congrArg ((basis q m ε).coord 0) (b.sum_repr (vec q m ε 0))
  simpa [map_sum, b, mul_comm] using this

/-- On the trivial-channel Clebsch–Gordan vector the functional `coevalCoord` is the corner
entry `C(v_m)(v₀) = (-ε)^m q^m`. -/
private theorem coevalCoord_clebschGordanVector (hq : IsGenericQuantumParameter q) :
    coevalCoord hq (clebschGordanVector q m ε m ε m) = (-(ε : ℂ)) ^ m * q ^ m := by
  simp only [clebschGordanVector_def, map_sum, map_smul, coevalCoord_tmul, smul_eq_mul]
  rw [Finset.sum_eq_single 0 (fun i _ hi => ?_) (by simp)]
  · simp [contragredientEquiv_vec_apply_vec_zero hq]
  · have h0 : (0 : ℤ) ≠ i := by omega
    simp [Module.Basis.coord_apply, basis_repr_vec, h0]

/-- At a generic parameter, the coevaluation `1 ↦ ∑_i b_i ⊗ b^i` of the right dual of `L_m^ε`,
followed by the inverse contragredient isomorphism `C⁻¹` on the second factor, is
`(-ε)^m q^(-m)` times the trivial-channel Clebsch–Gordan vector `w_m` of `L_m^ε ⊗ L_m^ε`. -/
theorem tensorMap_hopfDualEquiv_symm_dualCoeval (hq : IsGenericQuantumParameter q)
    (r : Trivial ℂ (UqSl2 q)) :
    tensorMap ℂ (UqSl2 q) LinearMap.id (hopfDualEquiv (m := m) (ε := ε) hq).symm.toLinearMap
        (dualCoeval ℂ (UqSl2 q) (LadderModule q m ε) r) =
      (trivialEquiv ℂ (UqSl2 q) r * ((-(ε : ℂ)) ^ m * q ^ (-(m : ℤ)))) •
        clebschGordanVector q m ε m ε m := by
  have hq0 : q ≠ 0 := Fact.out
  set x := tensorMap ℂ (UqSl2 q) LinearMap.id (hopfDualEquiv (m := m) (ε := ε) hq).symm.toLinearMap
    (dualCoeval ℂ (UqSl2 q) (LadderModule q m ε) r) with hxdef
  -- The coevaluation vector is invariant, hence a multiple `s • w_m`.
  have hinv (a : UqSl2 q) : a • x = Coalgebra.counit (R := ℂ) a • x := by
    have har : a • r = Coalgebra.counit (R := ℂ) a • r :=
      (trivialEquiv ℂ (UqSl2 q)).injective (by rw [trivialEquiv_smul, map_smul, smul_eq_mul])
    rw [hxdef, ← LinearMap.map_smul, ← LinearMap.map_smul, har, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower]
  set s := (basis q _ _).repr (clebschGordanProjection hq ⟨m, by simp⟩ x) 0
  have hx : x = s • clebschGordanVector q m ε m ε m :=
    eq_basis_repr_clebschGordanProjection_smul_of_forall_smul_eq hq hinv
  -- Comparing the values of `coevalCoord` pins `s`.
  have hs : trivialEquiv ℂ (UqSl2 q) r = s * ((-(ε : ℂ)) ^ m * q ^ m) := by
    rw [← coevalCoord_tensorMap_dualCoeval hq r, ← hxdef, ← coevalCoord_clebschGordanVector hq,
      hx, LinearMap.map_smul_of_tower, smul_eq_mul]
  have hprod : ((-(ε : ℂ)) ^ m * q ^ m) * ((-(ε : ℂ)) ^ m * q ^ (-(m : ℤ))) = 1 := by
    rw [mul_mul_mul_comm, ← pow_add, ← two_mul, pow_mul, neg_sq, Int.cast_units_sq, one_pow,
      one_mul, ← zpow_natCast, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero]
  rw [hx, hs]
  congr 1
  linear_combination (-s) * hprod

/-- At a generic parameter, the evaluation `φ ⊗ v ↦ φ(v)` of the right dual of `L_m^ε`,
precomposed with the contragredient isomorphism `C` on the first factor, is `q^m [m + 1]_q`
times the coordinate of the projection of `L_m^ε ⊗ L_m^ε` onto its trivial Clebsch–Gordan
channel. -/
theorem trivialEquiv_dualEval_tensorMap_hopfDualEquiv (hq : IsGenericQuantumParameter q)
    (y : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q m ε)) :
    trivialEquiv ℂ (UqSl2 q) (dualEval ℂ (UqSl2 q) (LadderModule q m ε)
        (tensorMap ℂ (UqSl2 q) (hopfDualEquiv hq).toLinearMap LinearMap.id y)) =
      q ^ m * quantumInteger q ((m : ℤ) + 1) *
        (basis q _ _).repr (clebschGordanProjection hq ⟨m, by simp⟩ y) 0 := by
  have h := apply_eq_basis_repr_clebschGordanProjection_smul hq
    ((dualEval ℂ (UqSl2 q) (LadderModule q m ε)).comp
      (tensorMap ℂ (UqSl2 q) (hopfDualEquiv hq).toLinearMap LinearMap.id)) y
  rw [LinearMap.comp_apply] at h
  rw [h, map_smul, smul_eq_mul, mul_comm]
  congr 1
  simp only [clebschGordanVector_def, LinearMap.comp_apply, map_sum,
    LinearMap.map_smul_of_tower, tensorMap_tmul, LinearEquiv.coe_toLinearMap, LinearMap.id_apply,
    dualEval_tmul, map_smul, LinearEquiv.apply_symm_apply, dualEquiv_hopfDualEquiv, smul_eq_mul]
  rw [← sum_range_pow_two_mul_eq_pow_mul_quantumInteger hq.sub_inv_ne_zero m]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact clebschGordanCoeff_mul_contragredientEquiv_vec hq
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

end TauCeti.UqSl2
