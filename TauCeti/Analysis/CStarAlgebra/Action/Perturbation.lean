/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bounded perturbations of C⋆-dynamics

Let `α` be a point-norm continuous real action on a unital C⋆-algebra `B`, with generator `δ`,
and let `P ∈ B`. The Dyson series, for `t ≥ 0`,
`Γ_t = 1 + ∑_{n ≥ 1} iⁿ ∫_{0 ≤ t₁ ≤ ⋯ ≤ tₙ ≤ t} α_{t₁}(P) ⋯ α_{tₙ}(P)`,
is written here, for all real `t`, through its recursive iterated integrals
`Γ⁽⁰⁾_t = 1` and `Γ⁽ⁿ⁺¹⁾_t = i ∫₀ᵗ Γ⁽ⁿ⁾_s α_s(P) ds`. These satisfy
`‖Γ⁽ⁿ⁾_t‖ ≤ (‖P‖ |t|)ⁿ / n!`, so the series converges in norm, and its sum is the unique solution
of `Γ_t' = i Γ_t α_t(P)` with `Γ_0 = 1`. It is a cocycle: `Γ_{s+t} = Γ_s α_s(Γ_t)`.

When `P` is self-adjoint every `Γ_t` is unitary, and `t ↦ Γ_t α_t(·) Γ_t⋆` is again a
point-norm continuous action, the perturbed dynamics `CStarAction.perturb`. Its generator has the
same domain as `δ` and equals `δ + i[P, ·]` there (`CStarAction.generator_perturb`).

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.4.1, for the perturbation expansion of automorphism groups and its cocycle.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Interval Nat

namespace TauCeti.CStarAction

variable {B : Type*} [CStarAlgebra B]

/-- The `n`-th Dyson term of a perturbation `P` of a real C⋆-dynamics `α`, defined by the
iterated integrals `Γ⁽⁰⁾_t = 1` and `Γ⁽ⁿ⁺¹⁾_t = i ∫₀ᵗ Γ⁽ⁿ⁾_s α_s(P) ds`. -/
def dysonTerm (α : CStarAction (Multiplicative ℝ) B) (P : B) : ℕ → ℝ → B
  | 0 => fun _ => 1
  | n + 1 => fun t => I • ∫ s in (0 : ℝ)..t, dysonTerm α P n s * α (Multiplicative.ofAdd s) P

variable (α : CStarAction (Multiplicative ℝ) B) (P : B)

@[simp]
theorem dysonTerm_zero (t : ℝ) : α.dysonTerm P 0 t = 1 :=
  (rfl)

theorem dysonTerm_succ (n : ℕ) (t : ℝ) :
    α.dysonTerm P (n + 1) t =
      I • ∫ s in (0 : ℝ)..t, α.dysonTerm P n s * α (Multiplicative.ofAdd s) P :=
  (rfl)

private theorem continuous_orbit_ofAdd :
    Continuous fun s : ℝ => α (Multiplicative.ofAdd s) P :=
  (α.continuous_orbit P).comp continuous_ofAdd

/-- Every Dyson term is continuous in time. -/
theorem continuous_dysonTerm : ∀ n, Continuous (α.dysonTerm P n)
  | 0 => continuous_const
  | n + 1 => by
    have h :=
      ((continuous_dysonTerm n).mul (α.continuous_orbit_ofAdd P)).integral_hasStrictDerivAt 0
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact ((h t).hasDerivAt.const_smul I).continuousAt

/-- The Dyson terms satisfy the recursive differential equation
`(Γ⁽ⁿ⁺¹⁾)'_t = i Γ⁽ⁿ⁾_t α_t(P)`. -/
theorem hasDerivAt_dysonTerm_succ (n : ℕ) (t : ℝ) :
    HasDerivAt (α.dysonTerm P (n + 1))
      (I • (α.dysonTerm P n t * α (Multiplicative.ofAdd t) P)) t :=
  (((α.continuous_dysonTerm P n).mul (α.continuous_orbit_ofAdd P)).integral_hasStrictDerivAt
    0 t).hasDerivAt.const_smul I

/-- The factorial bound on the Dyson terms. -/
theorem norm_dysonTerm_le (n : ℕ) (t : ℝ) :
    ‖α.dysonTerm P n t‖ ≤ (‖P‖ * |t|) ^ n / n ! := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · rw [Subsingleton.elim (α.dysonTerm P n t) 0, norm_zero]
    positivity
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hf := (α.continuous_dysonTerm P n).mul (α.continuous_orbit_ofAdd P)
    rw [dysonTerm_succ, norm_smul, norm_I, one_mul]
    calc ‖∫ s in (0 : ℝ)..t, α.dysonTerm P n s * α (Multiplicative.ofAdd s) P‖
        ≤ ∫ s in Ι (0 : ℝ) t, ‖α.dysonTerm P n s * α (Multiplicative.ofAdd s) P‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Ι (0 : ℝ) t, ‖P‖ ^ (n + 1) / n ! * |s - 0| ^ n := by
          have hg : Continuous fun s : ℝ => ‖P‖ ^ (n + 1) / n ! * |s - 0| ^ n := by fun_prop
          refine setIntegral_mono_on hf.norm.integrableOn_uIoc hg.integrableOn_uIoc
            measurableSet_uIoc fun s _ => ?_
          calc ‖α.dysonTerm P n s * α (Multiplicative.ofAdd s) P‖
              ≤ ‖α.dysonTerm P n s‖ * ‖α (Multiplicative.ofAdd s) P‖ := norm_mul_le _ _
            _ ≤ (‖P‖ * |s|) ^ n / n ! * ‖P‖ := by
                rw [StarAlgEquiv.norm_map]
                exact mul_le_mul_of_nonneg_right (ih s) (norm_nonneg P)
            _ = ‖P‖ ^ (n + 1) / n ! * |s - 0| ^ n := by
                rw [sub_zero, mul_pow, pow_succ]
                ring
      _ = (‖P‖ * |t|) ^ (n + 1) / (n + 1)! := by
          rw [integral_const_mul, integral_pow_abs_sub_uIoc, sub_zero, Nat.factorial_succ]
          push_cast
          field_simp
          ring

/-- The Dyson series converges in norm at every time. -/
theorem summable_dysonTerm (t : ℝ) : Summable fun n => α.dysonTerm P n t :=
  .of_norm_bounded (Real.summable_pow_div_factorial (‖P‖ * |t|)) fun n =>
    α.norm_dysonTerm_le P n t

/-- The Dyson cocycle `Γ_t = ∑ₙ Γ⁽ⁿ⁾_t` of a perturbation `P` of a real C⋆-dynamics `α`. -/
def dysonCocycle (t : ℝ) : B :=
  ∑' n, α.dysonTerm P n t

/-- The Dyson series sums to the Dyson cocycle. -/
theorem hasSum_dysonCocycle (t : ℝ) :
    HasSum (fun n => α.dysonTerm P n t) (α.dysonCocycle P t) :=
  (α.summable_dysonTerm P t).hasSum

/-- The Dyson cocycle is the identity plus the sum of the higher Dyson terms. -/
theorem dysonCocycle_eq_one_add (t : ℝ) :
    α.dysonCocycle P t = 1 + ∑' n, α.dysonTerm P (n + 1) t :=
  (α.summable_dysonTerm P t).tsum_eq_zero_add

/-- The Dyson cocycle is the identity at time zero. -/
@[simp]
theorem dysonCocycle_apply_zero : α.dysonCocycle P 0 = 1 := by
  simp [dysonCocycle_eq_one_add, dysonTerm_succ]

/-- The Dyson cocycle solves `Γ_t' = i Γ_t α_t(P)`. -/
theorem hasDerivAt_dysonCocycle (t : ℝ) :
    HasDerivAt (α.dysonCocycle P)
      (I • (α.dysonCocycle P t * α (Multiplicative.ofAdd t) P)) t := by
  set T := |t| + 1
  have hT : 0 < T := by positivity
  have hsum : HasDerivAt (fun y => ∑' n, α.dysonTerm P (n + 1) y)
      (∑' n, I • (α.dysonTerm P n t * α (Multiplicative.ofAdd t) P)) t := by
    refine hasDerivAt_tsum_of_isPreconnected (u := fun n => ‖P‖ * ((‖P‖ * T) ^ n / n !))
      (t := Ioo (-T) T) ((Real.summable_pow_div_factorial _).mul_left _) isOpen_Ioo
      isPreconnected_Ioo (fun n y _ => α.hasDerivAt_dysonTerm_succ P n y) (fun n y hy => ?_)
      (y₀ := 0) ⟨by linarith, hT⟩
      ((summable_nat_add_iff 1).2 (α.summable_dysonTerm P 0))
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hy : |y| ≤ T := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    rw [norm_smul, norm_I, one_mul]
    calc ‖α.dysonTerm P n y * α (Multiplicative.ofAdd y) P‖
        ≤ ‖α.dysonTerm P n y‖ * ‖P‖ := by
          simpa only [StarAlgEquiv.norm_map] using norm_mul_le (α.dysonTerm P n y)
            (α (Multiplicative.ofAdd y) P)
      _ ≤ (‖P‖ * T) ^ n / n ! * ‖P‖ := by
          refine mul_le_mul_of_nonneg_right ((α.norm_dysonTerm_le P n y).trans ?_) (norm_nonneg P)
          gcongr
      _ = ‖P‖ * ((‖P‖ * T) ^ n / n !) := mul_comm _ _
  have heq : α.dysonCocycle P = fun y => 1 + ∑' n, α.dysonTerm P (n + 1) y :=
    funext (α.dysonCocycle_eq_one_add P)
  convert (hasDerivAt_const t (1 : B)).add hsum using 1
  rw [zero_add, (((α.hasSum_dysonCocycle P t).mul_right _).const_smul I).tsum_eq]

/-- The Dyson cocycle is continuous in time. -/
theorem continuous_dysonCocycle : Continuous (α.dysonCocycle P) :=
  continuous_iff_continuousAt.2 fun t => (α.hasDerivAt_dysonCocycle P t).continuousAt

/-- The linear vector field `Y ↦ i Y α_u(P)` is Lipschitz with constant `‖P‖`. -/
private theorem lipschitzOnWith_smul_mul (u : ℝ) :
    LipschitzOnWith ‖P‖₊ (fun Y : B => I • (Y * α (Multiplicative.ofAdd u) P)) univ := by
  refine (LipschitzWith.of_dist_le_mul fun Y Z => ?_).lipschitzOnWith
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, ← sub_mul, norm_smul, norm_I, one_mul,
    coe_nnnorm, mul_comm ‖P‖]
  simpa only [StarAlgEquiv.norm_map] using norm_mul_le (Y - Z) (α (Multiplicative.ofAdd u) P)

/-- The Dyson cocycle is the unique solution of `Y_t' = i Y_t α_t(P)` with `Y_0 = 1`. -/
theorem eq_dysonCocycle_of_hasDerivAt {Y : ℝ → B}
    (hY : ∀ t, HasDerivAt Y (I • (Y t * α (Multiplicative.ofAdd t) P)) t) (h0 : Y 0 = 1) :
    Y = α.dysonCocycle P :=
  -- Uniqueness of solutions of Lipschitz differential equations, Mathlib's
  -- `ODE_solution_unique_univ`.
  ODE_solution_unique_univ (s := fun _ => univ) (α.lipschitzOnWith_smul_mul P)
    (fun t => ⟨hY t, mem_univ _⟩) (fun t => ⟨α.hasDerivAt_dysonCocycle P t, mem_univ _⟩)
    (t₀ := 0) (by simp [h0])

/-- The cocycle identity `Γ_{s+t} = Γ_s α_s(Γ_t)`. -/
theorem dysonCocycle_add (s t : ℝ) :
    α.dysonCocycle P (s + t) =
      α.dysonCocycle P s * α (Multiplicative.ofAdd s) (α.dysonCocycle P t) := by
  -- Both sides solve `Y' = i Y α_{s+t}(P)` with value `Γ_s` at `t = 0`, so they agree by
  -- Mathlib's ODE uniqueness theorem `ODE_solution_unique_univ`.
  have hv (u : ℝ) := α.lipschitzOnWith_smul_mul P (s + u)
  have hf (u : ℝ) : HasDerivAt (fun u => α.dysonCocycle P (s + u))
      (I • (α.dysonCocycle P (s + u) * α (Multiplicative.ofAdd (s + u)) P)) u :=
    (α.hasDerivAt_dysonCocycle P (s + u)).comp_const_add s u
  have hg (u : ℝ) : HasDerivAt
      (fun u => α.dysonCocycle P s * α (Multiplicative.ofAdd s) (α.dysonCocycle P u))
      (I • (α.dysonCocycle P s * α (Multiplicative.ofAdd s) (α.dysonCocycle P u) *
        α (Multiplicative.ofAdd (s + u)) P)) u := by
    have h := ((α.toStronglyContinuousGroup s).hasFDerivAt.comp_hasDerivAt u
      (α.hasDerivAt_dysonCocycle P u)).const_mul (α.dysonCocycle P s)
    simp only [Function.comp_def, toStronglyContinuousGroup_apply] at h
    convert h using 1
    simp only [map_smul, map_mul, ofAdd_add, mul_apply, mul_assoc, mul_smul_comm]
  have := ODE_solution_unique_univ (s := fun _ => univ) hv (fun u => ⟨hf u, mem_univ _⟩)
    (fun u => ⟨hg u, mem_univ _⟩) (t₀ := 0) (by simp)
  exact congrFun this t

variable {P}

/-- For self-adjoint `P`, the Dyson cocycle is a coisometry. -/
@[simp]
theorem dysonCocycle_mul_star (hP : IsSelfAdjoint P) (t : ℝ) :
    α.dysonCocycle P t * star (α.dysonCocycle P t) = 1 := by
  -- `Γ_u Γ_u⋆` has derivative zero, so it is constantly `Γ_0 Γ_0⋆ = 1`.
  have hd (u : ℝ) : HasDerivAt (fun u => α.dysonCocycle P u * star (α.dysonCocycle P u)) 0 u := by
    have h := α.hasDerivAt_dysonCocycle P u
    convert h.fun_mul h.star using 1
    rw [star_smul, star_mul, (hP.map (α (Multiplicative.ofAdd u))).star_eq, star_def, conj_I]
    simp [mul_assoc]
  have := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simpa using this

/-- For self-adjoint `P`, the Dyson cocycle is an isometry. -/
@[simp]
theorem star_dysonCocycle_mul (hP : IsSelfAdjoint P) (t : ℝ) :
    star (α.dysonCocycle P t) * α.dysonCocycle P t = 1 := by
  -- `w = α_t(Γ_{-t})` is a two-sided inverse of `Γ_t` by the cocycle identity.
  set w := α (Multiplicative.ofAdd t) (α.dysonCocycle P (-t))
  have hleft : w * α.dysonCocycle P t = 1 := by
    have h := α.dysonCocycle_add P (-t) t
    rw [neg_add_cancel, dysonCocycle_apply_zero] at h
    have h' := congrArg (α (Multiplicative.ofAdd t)) h
    rwa [map_one, map_mul, ofAdd_neg, apply_inv_apply, eq_comm] at h'
  have hstar : star (α.dysonCocycle P t) = w := by
    calc star (α.dysonCocycle P t)
        = (w * α.dysonCocycle P t) * star (α.dysonCocycle P t) := by rw [hleft, one_mul]
      _ = w := by rw [mul_assoc, α.dysonCocycle_mul_star hP, mul_one]
  rw [hstar, hleft]

/-- For self-adjoint `P`, the Dyson cocycle is unitary. -/
theorem dysonCocycle_mem_unitary (hP : IsSelfAdjoint P) (t : ℝ) :
    α.dysonCocycle P t ∈ unitary B :=
  Unitary.mem_iff.2 ⟨α.star_dysonCocycle_mul hP t, α.dysonCocycle_mul_star hP t⟩

/-- The perturbation of a real C⋆-dynamics `α` by a self-adjoint `P`, acting at time `t` by
`a ↦ Γ_t α_t(a) Γ_t⋆`, where `Γ` is the Dyson cocycle. -/
def perturb (hP : IsSelfAdjoint P) : CStarAction (Multiplicative ℝ) B where
  toMonoidHom :=
    { toFun := fun t => (α t).trans (Unitary.conjStarAlgAut ℂ B
        ⟨α.dysonCocycle P t.toAdd, α.dysonCocycle_mem_unitary hP t.toAdd⟩)
      map_one' := by
        ext a
        simp
      map_mul' := fun s t => by
        ext a
        simp [dysonCocycle_add, toAdd_mul, mul_apply, mul_assoc, map_star] }
  continuous_orbit a := by
    have hΓ := (α.continuous_dysonCocycle P).comp continuous_toAdd
    exact (hΓ.mul (α.continuous_orbit a)).mul hΓ.star

@[simp]
theorem perturb_apply (hP : IsSelfAdjoint P) (t : ℝ) (a : B) :
    α.perturb hP (Multiplicative.ofAdd t) a =
      α.dysonCocycle P t * α (Multiplicative.ofAdd t) a * star (α.dysonCocycle P t) :=
  (rfl)

/-- The perturbed orbit of a generator-domain element has derivative `δ(a) + i(Pa - aP)` at zero. -/
private theorem hasDerivAt_perturb_zero (hP : IsSelfAdjoint P) (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α.perturb hP (Multiplicative.ofAdd t) (a : B))
      (α.generator a + I • (P * a - a * P)) 0 := by
  have hΓ := α.hasDerivAt_dysonCocycle P 0
  simp only [dysonCocycle_apply_zero, one_mul, ofAdd_zero, one_apply] at hΓ
  have hs : star (I • P) = -(I • P) := by rw [star_smul, hP.star_eq, star_def, conj_I, neg_smul]
  simp only [perturb_apply]
  convert (hΓ.fun_mul (α.hasDerivAt_zero a)).fun_mul hΓ.star using 1
  simp only [dysonCocycle_apply_zero, ofAdd_zero, one_apply, star_one, mul_one, one_mul, hs,
    mul_neg, smul_sub, smul_mul_assoc, mul_smul_comm]
  abel

/-- The perturbed dynamics has the same generator domain as the original dynamics. -/
@[simp]
theorem mem_generator_perturb_domain_iff (hP : IsSelfAdjoint P) (a : B) :
    a ∈ (α.perturb hP).generator.domain ↔ a ∈ α.generator.domain := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · -- Undo the unitary conjugation: `α_t(a) = Γ_t⋆ (Γ_t α_t(a) Γ_t⋆) Γ_t`.
    rw [mem_generator_domain_iff_differentiableAt] at ha ⊢
    have hΓ := (α.hasDerivAt_dysonCocycle P 0).differentiableAt
    have h := (hΓ.star.mul ha).mul hΓ
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, perturb_apply, mul_assoc, α.star_dysonCocycle_mul hP, mul_one]
    rw [← mul_assoc, α.star_dysonCocycle_mul hP, one_mul]
  · rw [mem_generator_domain_iff_differentiableAt]
    exact (α.hasDerivAt_perturb_zero hP ⟨a, ha⟩).differentiableAt

/-- The generator of the perturbed dynamics is `δ + i[P, ·]` on the domain of `δ`. -/
theorem generator_perturb_apply (hP : IsSelfAdjoint P) (a : α.generator.domain) :
    (α.perturb hP).generator ⟨a, (α.mem_generator_perturb_domain_iff hP a).2 a.property⟩ =
      α.generator a + I • (P * a - a * P) :=
  generator_eq_of_hasDerivAt _ _ (α.hasDerivAt_perturb_zero hP a)

/-- The generator of the perturbed dynamics is the bounded perturbation `δ + i[P, ·]`, with the
same domain as `δ`. -/
theorem generator_perturb (hP : IsSelfAdjoint P) :
    (α.perturb hP).generator =
      (I • (LinearMap.mulLeft ℂ P - LinearMap.mulRight ℂ P)) +ᵥ α.generator := by
  refine LinearPMap.ext ?_ fun a _ ha => ?_
  · ext a
    rw [LinearPMap.vadd_domain]
    exact α.mem_generator_perturb_domain_iff hP a
  · rw [LinearPMap.vadd_apply]
    exact (α.generator_perturb_apply hP ⟨a, ha⟩).trans (by simp [add_comm])

/-- The Dyson cocycle of the zero perturbation is the identity. -/
@[simp]
theorem dysonCocycle_zero : α.dysonCocycle 0 = 1 := by
  funext t
  simp [dysonCocycle_eq_one_add, dysonTerm_succ]

/-- Perturbing by zero recovers the original dynamics. -/
@[simp]
theorem perturb_zero : α.perturb (IsSelfAdjoint.zero B) = α := by
  ext t a
  rw [← ofAdd_toAdd t, perturb_apply]
  simp

end TauCeti.CStarAction
