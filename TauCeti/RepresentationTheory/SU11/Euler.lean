/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.RepresentationTheory.SU11.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Euler angles of `SU(1,1)`

Every element of `SU(1,1)` has the form `rotation α * boost t * rotation γ` with
`0 ≤ α < 2π`, `t ≥ 0`, and `-2π ≤ γ < 2π`. The coordinates in these ranges are unique
when the off-diagonal entry is nonzero, which is equivalent to `t > 0`.
`SU11.continuous_euler` gives the measurability needed to push forward the Euler Haar
density from the positive-boost domain to the group. `SU11.bijOn_euler` gives each element
with nonzero upper-right entry exactly one parameter triple in that domain.

The order of the factors and the half-angle convention follow Vilenkin and Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §6.1.1, (10)–(12).
-/

public section

open Real Set

namespace TauCeti.SU11

/-- The diagonal rotation with entries `exp (i α/2)` and `exp (-i α/2)`. -/
noncomputable def rotation (α : ℝ) : SU11 :=
  ofPair (Circle.exp (α / 2)) 0 (by simp only [Circle.norm_coe, norm_zero, one_pow, zero_pow
    (by decide : 2 ≠ 0), sub_zero])

@[simp]
theorem entryA_rotation (α : ℝ) : (rotation α).entryA = (Circle.exp (α / 2) : ℂ) := by
  simp [rotation]

@[simp]
theorem entryB_rotation (α : ℝ) : (rotation α).entryB = 0 := by simp [rotation]

@[simp]
theorem rotation_zero : rotation 0 = 1 := by ext <;> simp

/-- The rotation parameters add under multiplication. -/
theorem rotation_add (α γ : ℝ) : rotation (α + γ) = rotation α * rotation γ := by
  ext <;> simp only [entryA_rotation, entryB_rotation, entryA_mul, entryB_mul,
    mul_zero, zero_mul, add_zero, add_div, Circle.exp_add, Circle.coe_mul]

/-- Rotation depends continuously on its angle. -/
@[fun_prop]
theorem continuous_rotation : Continuous rotation := by
  rw [continuous_iff_entryA_entryB]
  constructor
  · simp only [entryA_rotation]
    exact continuous_subtypeVal.comp (Circle.exp.continuous.comp (continuous_id.div_const 2))
  · simp only [entryB_rotation]
    exact continuous_const

/-- A full turn in the angle parameter is represented by the matrix `-1`. -/
theorem coe_rotation_two_pi :
    ((rotation (2 * π)).val : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [coe_eq_matrix]
  conv_rhs => rw [Matrix.eta_fin_two (-1 : Matrix (Fin 2) (Fin 2) ℂ)]
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- Two full turns in the angle parameter give the identity. -/
@[simp]
theorem rotation_four_pi : rotation (4 * π) = 1 := by
  have h : 4 * π / 2 = 2 * π := by ring
  ext <;> simp only [entryA_rotation, h, Circle.exp_two_pi, Circle.coe_one, entryA_one,
    entryB_rotation, entryB_one]

/-- The real symmetric boost with diagonal `cosh (t/2)` and off-diagonal `sinh (t/2)`. -/
noncomputable def boost (t : ℝ) : SU11 :=
  ofPair (cosh (t / 2)) (sinh (t / 2)) (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using cosh_sq_sub_sinh_sq (t / 2))

@[simp]
theorem entryA_boost (t : ℝ) : (boost t).entryA = (cosh (t / 2) : ℂ) := by simp [boost]

@[simp]
theorem entryB_boost (t : ℝ) : (boost t).entryB = (sinh (t / 2) : ℂ) := by simp [boost]

@[simp]
theorem boost_zero : boost 0 = 1 := by ext <;> simp

/-- The boost parameters add under multiplication. -/
theorem boost_add (s t : ℝ) : boost (s + t) = boost s * boost t := by
  ext
  · simp only [entryA_mul, entryA_boost, entryB_boost, add_div, Real.cosh_add, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal]
  · simp only [entryB_mul, entryA_boost, entryB_boost, add_div, Real.sinh_add, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal, add_comm]

/-- A real boost depends continuously on its parameter. -/
@[fun_prop]
theorem continuous_boost : Continuous boost := by
  rw [continuous_iff_entryA_entryB]
  constructor
  · simp only [entryA_boost]
    fun_prop
  · simp only [entryB_boost]
    fun_prop

/-- The Euler product with outer rotation parameters `α`, `γ` and boost parameter `t`. -/
noncomputable def euler (α t γ : ℝ) : SU11 := rotation α * boost t * rotation γ

/-- The Euler product in terms of the rotation and boost. -/
theorem euler_def (α t γ : ℝ) : euler α t γ = rotation α * boost t * rotation γ := (rfl)

/-- The Euler map from triples of real parameters is continuous. -/
@[fun_prop]
theorem continuous_euler : Continuous (fun p : ℝ × ℝ × ℝ ↦ euler p.1 p.2.1 p.2.2) := by
  simp only [euler_def]
  fun_prop

/-- The upper-left entry in Euler coordinates has phase `(α + γ)/2`. -/
@[simp]
theorem entryA_euler (α t γ : ℝ) :
    (euler α t γ).entryA = (cosh (t / 2) : ℂ) * (Circle.exp ((α + γ) / 2) : ℂ) := by
  simp only [euler_def, entryA_mul, entryA_rotation, entryB_rotation, star_zero, mul_zero,
    zero_mul, add_zero, entryA_boost, add_div, Circle.exp_add, Circle.coe_mul]
  ring

/-- The upper-right entry is the unit complex factor at angle `(α - γ)/2`
scaled by the signed amplitude `sinh (t / 2)`. -/
theorem entryB_euler (α t γ : ℝ) :
    (euler α t γ).entryB = (sinh (t / 2) : ℂ) * (Circle.exp ((α - γ) / 2) : ℂ) := by
  have hconj : star (Circle.exp (γ / 2) : ℂ) = (↑((Circle.exp (γ / 2))⁻¹) : ℂ) :=
    (Circle.coe_inv_eq_conj _).symm
  simp only [euler_def, entryB_mul, entryB_rotation, mul_zero, zero_mul, zero_add, add_zero,
    entryA_rotation, entryB_boost]
  rw [hconj, sub_div, Circle.exp_sub, Circle.coe_div, Circle.coe_inv, div_eq_mul_inv]
  ring

/-- The absolute size of the upper-right entry is determined by the boost parameter. -/
@[simp]
theorem norm_entryB_euler (α t γ : ℝ) : ‖(euler α t γ).entryB‖ = |sinh (t / 2)| := by
  simp only [entryB_euler, norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]

/-- The off-diagonal entry vanishes exactly at boost parameter zero. -/
@[simp]
theorem entryB_euler_eq_zero_iff (α t γ : ℝ) : (euler α t γ).entryB = 0 ↔ t = 0 := by
  rw [← norm_eq_zero, norm_entryB_euler, abs_eq_zero, sinh_eq_zero, div_eq_zero_iff]
  norm_num

/-- The Euler parameters with positive boost and one fundamental range for the phases. -/
noncomputable def eulerDomain : Set (ℝ × ℝ × ℝ) :=
  Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π)

@[simp]
theorem mem_eulerDomain {α t γ : ℝ} :
    (α, t, γ) ∈ eulerDomain ↔ α ∈ Ico 0 (2 * π) ∧ 0 < t ∧ γ ∈ Ico (-(2 * π)) (2 * π) :=
  Iff.rfl

private theorem half_mem_euler_Ico {γ : ℝ} :
    γ / 2 ∈ Ico (-π) π ↔ γ ∈ Ico (-(2 * π)) (2 * π) := by
  have h := preimage_mul_const_Ico₀ (-π) π (by norm_num : 0 < (2 : ℝ)⁻¹)
  simpa only [mem_preimage, div_eq_mul_inv, inv_inv, neg_mul, mul_comm π] using
    Set.ext_iff.mp h γ

/-- Every element has Euler angles in the stated ranges, including the case `t = 0`. -/
theorem exists_euler_eq (g : SU11) :
    ∃ α t γ : ℝ, α ∈ Ico 0 (2 * π) ∧ 0 ≤ t ∧ γ ∈ Ico (-(2 * π)) (2 * π) ∧
      euler α t γ = g := by
  let t := 2 * arsinh ‖g.entryB‖
  have hsinh : sinh (t / 2) = ‖g.entryB‖ := by
    simp [t, mul_comm (2 : ℝ)]
  have hcosh : cosh (t / 2) = ‖g.entryA‖ := by
    have h := g.norm_entryA_sq_sub_norm_entryB_sq
    have hsq := cosh_sq_sub_sinh_sq (t / 2)
    rw [hsinh] at hsq
    exact (sq_eq_sq₀ (cosh_pos _).le (norm_nonneg _)).mp (by linarith)
  -- The product of the two phases determines `α` modulo `2π`. Once `α` is fixed,
  -- the first phase determines the half-angle `γ / 2` modulo `2π`.
  let u := Circle.exp (Complex.arg g.entryA)
  let v := Circle.exp (Complex.arg g.entryB)
  have hexp (l : ℝ) (z : Circle) : z ∈ Circle.exp '' Ico l (l + 2 * π) := by
    obtain ⟨x, hx, heq⟩ := Circle.periodic_exp.exists_mem_Ico two_pi_pos (Complex.arg z) l
    exact ⟨x, hx, heq.symm.trans (Circle.exp_arg z)⟩
  obtain ⟨α, hα, hαphase⟩ := hexp 0 (u * v)
  obtain ⟨δ, hδ, hδphase⟩ := hexp (-π) (u / Circle.exp (α / 2))
  have hpA : Circle.exp ((α + 2 * δ) / 2) = u := by
    rw [add_div, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Circle.exp_add,
      hδphase, mul_div_cancel]
  have hpB : Circle.exp ((α - 2 * δ) / 2) = v := by
    have hadd : (α - 2 * δ) / 2 + (α + 2 * δ) / 2 = α := by ring
    apply mul_right_cancel (b := u)
    rw [← hpA, ← Circle.exp_add, hadd, hαphase, hpA, mul_comm]
  refine ⟨α, t, 2 * δ, by simpa using hα,
    mul_nonneg (by norm_num) (arsinh_nonneg_iff.mpr (norm_nonneg _)), ?_, ?_⟩
  · apply half_mem_euler_Ico.mp
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    simpa only [two_mul π, neg_add_cancel_left] using hδ
  · ext
    · rw [entryA_euler, hcosh, hpA, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
    · rw [entryB_euler, hsinh, hpB, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]

private theorem injOn_euler : InjOn (fun p : ℝ × ℝ × ℝ ↦ euler p.1 p.2.1 p.2.2) eulerDomain := by
  rintro ⟨α, t, γ⟩ hmem ⟨α', t', γ'⟩ hmem' h
  obtain ⟨hα, ht, hγ⟩ := mem_eulerDomain.mp hmem
  obtain ⟨hα', ht', hγ'⟩ := mem_eulerDomain.mp hmem'
  have hs : sinh (t / 2) = sinh (t' / 2) := by
    simpa only [norm_entryB_euler, abs_of_pos (sinh_pos_iff.mpr (half_pos ht)),
      abs_of_pos (sinh_pos_iff.mpr (half_pos ht'))]
      using congrArg (fun g : SU11 ↦ ‖g.entryB‖) h
  have ht_eq : t = t' := by linarith [sinh_injective hs]
  subst t'
  -- The boost is positive here, so both moduli can be cancelled to compare phases.
  have hpA : Circle.exp ((α + γ) / 2) = Circle.exp ((α' + γ') / 2) :=
    Circle.coe_injective <| mul_left_cancel₀
      (Complex.ofReal_ne_zero.mpr (cosh_pos (t / 2)).ne')
      (by simpa only [entryA_euler] using congrArg entryA h)
  have hpB : Circle.exp ((α - γ) / 2) = Circle.exp ((α' - γ') / 2) :=
    Circle.coe_injective <| mul_left_cancel₀
      (Complex.ofReal_ne_zero.mpr (sinh_pos_iff.mpr (half_pos ht)).ne')
      (by simpa only [entryB_euler] using congrArg entryB h)
  have hsum (a c : ℝ) : (a + c) / 2 + (a - c) / 2 = a := by ring
  have hαeq : α = α' := Circle.exp_injOn_Ico (by simp) hα hα' (by
    rw [← hsum α γ, Circle.exp_add, hpA, hpB, ← Circle.exp_add, hsum])
  subst α'
  have hδ : γ / 2 = γ' / 2 :=
    Circle.exp_injOn_Ico (a := -π) (b := π) (by rw [sub_neg_eq_add, two_mul])
      (half_mem_euler_Ico.mpr hγ) (half_mem_euler_Ico.mpr hγ')
      (by simpa only [add_div, Circle.exp_add, mul_right_inj] using hpA)
  have hγeq : γ = γ' := by linarith
  subst γ'
  rfl

/-- The Euler parametrization bijects its positive-boost domain with the matrices whose
upper-right entry is nonzero. -/
theorem bijOn_euler :
    BijOn (fun p : ℝ × ℝ × ℝ ↦ euler p.1 p.2.1 p.2.2) eulerDomain
      {g : SU11 | g.entryB ≠ 0} := by
  refine ⟨?_, injOn_euler, ?_⟩
  · rintro ⟨α, t, γ⟩ hmem
    exact fun h ↦ (mem_eulerDomain.mp hmem).2.1.ne' ((entryB_euler_eq_zero_iff α t γ).mp h)
  · intro g hg
    obtain ⟨α, t, γ, hα, ht, hγ, rfl⟩ := exists_euler_eq g
    have ht' : 0 < t := lt_of_le_of_ne ht fun h ↦ hg ((entryB_euler_eq_zero_iff α t γ).mpr h.symm)
    exact ⟨(α, t, γ), mem_eulerDomain.mpr ⟨hα, ht', hγ⟩, rfl⟩

end TauCeti.SU11
