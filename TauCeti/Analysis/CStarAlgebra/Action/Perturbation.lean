/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Multiplier
public import TauCeti.Analysis.ODE.DysonSeries

/-!
# Unitary cocycles of bounded perturbations of C⋆-dynamics

Let `τ` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A` and let
`P ∈ A`. The perturbation cocycle `Γ t` is the time-ordered exponential of the path
`s ↦ i τ_s(P)` in the multiplier algebra `𝓜(ℂ, A)`, given by the norm-convergent Dyson series

`Γ t = 1 + Σ_{n ≥ 1} iⁿ ∫_{0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t} τ_{s₁}(P) ⋯ τ_{sₙ}(P) ds` for `t ≥ 0`.

For `t < 0` the `n`-th term instead integrates over `t ≤ sₙ ≤ ⋯ ≤ s₁ ≤ 0`, with an extra
factor `(-1)ⁿ`.

It is the unique solution of `Γ' t = i Γ t τ_t(P)` with `Γ 0 = 1`. When `P` is self-adjoint,
each `Γ t` is unitary, and the family satisfies the cocycle identity
`Γ (s + t) = Γ s τ_s(Γ t)` for the induced action on multipliers. These cocycles are the
input for the perturbed dynamics `a ↦ Γ t τ_t(a) Γ t⋆` with generator `δ + i[P, ·]`; that
dynamics is not constructed in this file.

A multiplier-valued cocycle is used so that `A` need not be unital; the path itself is
norm-continuous because `P` lies in `A`.

## Main declarations

* `TauCeti.CStarAction.perturbationCocycle`: the cocycle `Γ` of the perturbation `P`.
* `TauCeti.CStarAction.hasDerivAt_perturbationCocycle`: `Γ' t = Γ t * (i τ_t(P))`.
* `TauCeti.CStarAction.eq_perturbationCocycle`: uniqueness of this initial value problem.
* `TauCeti.CStarAction.perturbationCocycle_mem_unitary`: unitarity for self-adjoint `P`.
* `TauCeti.CStarAction.perturbationCocycle_add`: the cocycle identity.
* `TauCeti.CStarAction.perturbationCocycle_neg`: `Γ (-t) = τ_{-t}(Γ t⋆)`.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.4.1, for the perturbation cocycle and its Dyson expansion.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The path `s ↦ i τ_s(P)` in the multiplier algebra whose time-ordered exponential is the
perturbation cocycle. -/
private def perturbationPath (α : CStarAction (Multiplicative ℝ) A) (P : A) (s : ℝ) :
    𝓜(ℂ, A) :=
  Complex.I • ((α (Multiplicative.ofAdd s) P : A) : 𝓜(ℂ, A))

private theorem continuous_perturbationPath (α : CStarAction (Multiplicative ℝ) A) (P : A) :
    Continuous (perturbationPath α P) := by
  unfold perturbationPath
  exact (DoubleCentralizer.isometry_coe.continuous.comp
    ((α.continuous_orbit P).comp continuous_ofAdd)).const_smul Complex.I

/-- The perturbation cocycle of `P ∈ A` for a real dynamics `α`: the Dyson series of the
path `s ↦ i α_s(P)` in `𝓜(ℂ, A)`. -/
def perturbationCocycle (α : CStarAction (Multiplicative ℝ) A) (P : A) (t : ℝ) : 𝓜(ℂ, A) :=
  dysonSeries (perturbationPath α P) t

variable (α : CStarAction (Multiplicative ℝ) A) (P : A)

/-- The Dyson expansion of the perturbation cocycle, as a norm-convergent series of iterated
integrals. -/
theorem hasSum_perturbationCocycle (t : ℝ) :
    HasSum (fun n => dysonTerm (fun s => Complex.I • ((α (Multiplicative.ofAdd s) P : A) :
      𝓜(ℂ, A))) n t) (α.perturbationCocycle P t) :=
  hasSum_dysonSeries (continuous_perturbationPath α P) t

@[simp]
theorem perturbationCocycle_zero : α.perturbationCocycle P 0 = 1 :=
  dysonSeries_zero _

/-- The perturbation cocycle solves `Γ' t = Γ t * (i α_t(P))`. -/
theorem hasDerivAt_perturbationCocycle (t : ℝ) :
    HasDerivAt (α.perturbationCocycle P)
      (α.perturbationCocycle P t * Complex.I • ((α (Multiplicative.ofAdd t) P : A) : 𝓜(ℂ, A)))
      t :=
  hasDerivAt_dysonSeries (continuous_perturbationPath α P) t

/-- The perturbation cocycle is norm-continuous. -/
theorem continuous_perturbationCocycle : Continuous (α.perturbationCocycle P) :=
  continuous_dysonSeries (continuous_perturbationPath α P)

/-- The perturbation cocycle is the unique solution of `Γ' t = Γ t * (i α_t(P))` with
`Γ 0 = 1`. -/
theorem eq_perturbationCocycle {f : ℝ → 𝓜(ℂ, A)} (hf₀ : f 0 = 1)
    (hf : ∀ t, HasDerivAt f
      (f t * Complex.I • ((α (Multiplicative.ofAdd t) P : A) : 𝓜(ℂ, A))) t) :
    f = α.perturbationCocycle P :=
  funext fun t => (eq_mul_dysonSeries (continuous_perturbationPath α P) hf t).trans <| by
    rw [hf₀, one_mul]
    rfl

/-- The perturbation cocycle of a self-adjoint perturbation is unitary. -/
theorem perturbationCocycle_mem_unitary {P : A} (hP : IsSelfAdjoint P) (t : ℝ) :
    α.perturbationCocycle P t ∈ unitary 𝓜(ℂ, A) :=
  dysonSeries_mem_unitary (continuous_perturbationPath α P) (fun s => by
    have hcoe (a : A) : star (a : 𝓜(ℂ, A)) = ((star a : A) : 𝓜(ℂ, A)) :=
      (map_star (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A)) a).symm
    simp [perturbationPath, star_smul, hcoe, ← map_star, hP.star_eq]) t

/-- The cocycle identity `Γ (s + t) = Γ s * α_s(Γ t)`, for the action induced on multipliers. -/
theorem perturbationCocycle_add (s t : ℝ) :
    α.perturbationCocycle P (s + t) =
      α.perturbationCocycle P s *
        α.multiplier (Multiplicative.ofAdd s) (α.perturbationCocycle P t) := by
  -- The automorphism `α_s` of `𝓜(ℂ, A)` as a continuous real-linear map.
  let E : 𝓜(ℂ, A) →L[ℝ] 𝓜(ℂ, A) :=
    (LinearIsometry.toContinuousLinearMap
      ⟨(α.multiplier (Multiplicative.ofAdd s) : 𝓜(ℂ, A) →ₗ[ℂ] 𝓜(ℂ, A)),
        fun m => StarAlgEquiv.norm_map (α.multiplier (Multiplicative.ofAdd s)) m⟩).restrictScalars
      ℝ
  have hE (m : 𝓜(ℂ, A)) : E m = α.multiplier (Multiplicative.ofAdd s) m := rfl
  -- Both sides solve `Y' u = Y u * (i α_{s + u}(P))` and take the value `Γ s` at `u = 0`.
  have key := eq_of_hasDerivAt_mul
    ((continuous_perturbationPath α P).comp (continuous_const_add s))
    (f := fun u => α.perturbationCocycle P (s + u))
    (g := fun u => α.perturbationCocycle P s *
      α.multiplier (Multiplicative.ofAdd s) (α.perturbationCocycle P u)) (t₀ := 0)
    (fun u => (hasDerivAt_perturbationCocycle α P (s + u)).comp_const_add s u)
    (fun u => by
      refine ((E.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_perturbationCocycle α P u)).const_mul
        (α.perturbationCocycle P s)).congr_deriv ?_
      simp only [hE, map_mul, map_smul, multiplier_coe, ← mul_apply, ← ofAdd_add,
        Function.comp_apply, perturbationPath, mul_assoc])
    (by simp)
  exact congrFun key t

/-- The cocycle at negative times: `Γ (-t) = α_{-t}(Γ t⋆)` for self-adjoint `P`. -/
theorem perturbationCocycle_neg {P : A} (hP : IsSelfAdjoint P) (t : ℝ) :
    α.perturbationCocycle P (-t) =
      α.multiplier (Multiplicative.ofAdd (-t)) (star (α.perturbationCocycle P t)) := by
  have h := α.perturbationCocycle_add P t (-t)
  rw [add_neg_cancel, perturbationCocycle_zero] at h
  have hu := α.perturbationCocycle_mem_unitary hP t
  have h' : α.multiplier (Multiplicative.ofAdd t) (α.perturbationCocycle P (-t)) =
      star (α.perturbationCocycle P t) := by
    rw [← one_mul (α.multiplier _ _), ← Unitary.star_mul_self_of_mem hu, mul_assoc, ← h,
      mul_one]
  rw [ofAdd_neg, ← multiplier_symm_apply, ← h', StarAlgEquiv.symm_apply_apply]

end TauCeti.CStarAction
