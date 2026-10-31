/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Multiplier
public import TauCeti.Analysis.ODE.DysonSeries

/-!
# Bounded perturbations of C⋆-dynamics

Let `τ` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A` and let
`P ∈ A`. The perturbation cocycle `Γ t` is the time-ordered exponential of the path
`s ↦ i τ_s(P)` in the multiplier algebra `𝓜(ℂ, A)`, given by the norm-convergent Dyson series

`Γ t = 1 + Σ_{n ≥ 1} iⁿ ∫_{0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t} τ_{s₁}(P) ⋯ τ_{sₙ}(P) ds` for `t ≥ 0`.

For `t < 0` the `n`-th term instead integrates over `t ≤ sₙ ≤ ⋯ ≤ s₁ ≤ 0`, with an extra
factor `(-1)ⁿ`.

It is the unique solution of `Γ' t = i Γ t τ_t(P)` with `Γ 0 = 1`. When `P` is self-adjoint,
each `Γ t` is unitary, and the family satisfies the cocycle identity
`Γ (s + t) = Γ s τ_s(Γ t)` for the induced action on multipliers.

For self-adjoint `P`, the cocycle identity makes `τ^P_t(a) = Γ t τ_t(a) Γ t⋆` a point-norm
continuous real action on `A`, the perturbed dynamics. Its generator is `δ + i[P, ·]` on the
domain of the generator `δ` of `τ`; in particular the perturbation does not change the
domain. Perturbing `τ^P` by `-P` recovers `τ`, its cocycle being `Γ t⋆`.

A multiplier-valued cocycle is used so that `A` need not be unital; the path itself is
norm-continuous because `P` lies in `A`. Since `A` is an ideal in `𝓜(ℂ, A)`, conjugation by the
unitary `Γ t` maps `A` to itself.

## Main declarations

* `TauCeti.CStarAction.perturbationCocycle`: the cocycle `Γ` of the perturbation `P`.
* `TauCeti.CStarAction.hasDerivAt_perturbationCocycle`: `Γ' t = Γ t * (i τ_t(P))`.
* `TauCeti.CStarAction.eq_perturbationCocycle`: uniqueness of this initial value problem.
* `TauCeti.CStarAction.perturbationCocycle_mem_unitary`: unitarity for self-adjoint `P`.
* `TauCeti.CStarAction.perturbationCocycle_add`: the cocycle identity.
* `TauCeti.CStarAction.perturbationCocycle_neg`: `Γ (-t) = τ_{-t}(Γ t⋆)`.
* `TauCeti.CStarAction.perturbed`: the perturbed dynamics `τ^P`.
* `TauCeti.CStarAction.generator_perturbed`: its generator is `δ + i[P, ·]`.
* `TauCeti.CStarAction.perturbed_perturbed_neg`: perturbing `τ^P` by `-P` gives back `τ`.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.4.1, for the perturbation cocycle, its Dyson expansion, and the perturbed dynamics
  with generator `δ + i[P, ·]`.
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
    simp [perturbationPath, star_smul, ← DoubleCentralizer.coe_star, ← map_star, hP.star_eq]) t

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

section Perturbed

variable {P : A} (hP : IsSelfAdjoint P)

/-- The perturbation cocycle of a self-adjoint perturbation, as a unitary multiplier. -/
private def perturbationUnitary (t : ℝ) : unitary 𝓜(ℂ, A) :=
  ⟨α.perturbationCocycle P t, α.perturbationCocycle_mem_unitary hP t⟩

/-- The **perturbed dynamics** of `α` by a self-adjoint `P ∈ A`:
`α^P_t(a) = Γ t α_t(a) (Γ t)⋆`, where `Γ` is the perturbation cocycle of `P`. It is a group
of automorphisms by the cocycle identity, and its generator is `δ + i[P, ·]`, where `δ` is the
generator of `α` (`generator_perturbed`). -/
def perturbed : CStarAction (Multiplicative ℝ) A where
  toMonoidHom :=
    { toFun t := DoubleCentralizer.conjStarAlgAut (perturbationUnitary α hP t.toAdd) * α t
      map_one' := by
        ext a
        apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
        simp [perturbationUnitary]
      map_mul' s t := by
        ext a
        apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
        simp only [StarAlgEquiv.mul_apply, DoubleCentralizer.coe_conjStarAlgAut_apply,
          perturbationUnitary, toAdd_mul, perturbationCocycle_add, ofAdd_toAdd, α.mul_apply,
          ← multiplier_coe, map_mul, map_star, star_mul, mul_assoc] }
  continuous_orbit a := by
    have hcoe := DoubleCentralizer.isometry_coe (𝕜 := ℂ) (A := A)
    rw [hcoe.isUniformInducing.isInducing.continuous_iff]
    have hΓ := (α.continuous_perturbationCocycle P).comp continuous_toAdd
    refine ((hΓ.mul (hcoe.continuous.comp (α.continuous_orbit a))).mul hΓ.star).congr
      fun t => ?_
    simp only [Pi.mul_apply, Pi.star_apply, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      StarAlgEquiv.mul_apply, DoubleCentralizer.coe_conjStarAlgAut_apply, perturbationUnitary,
      toMonoidHom_apply]

/-- The perturbed dynamics is `α^P_t(a) = Γ t α_t(a) (Γ t)⋆`, computed in the multiplier
algebra. -/
@[simp]
theorem coe_perturbed_apply (t : Multiplicative ℝ) (a : A) :
    ((α.perturbed hP t a : A) : 𝓜(ℂ, A)) =
      α.perturbationCocycle P t.toAdd * (α t a : 𝓜(ℂ, A)) *
        star (α.perturbationCocycle P t.toAdd) :=
  DoubleCentralizer.coe_conjStarAlgAut_apply _ _

/-- The perturbation cocycle has derivative `i P` at time zero. -/
private theorem hasDerivAt_perturbationCocycle_zero :
    HasDerivAt (α.perturbationCocycle P) (Complex.I • (P : 𝓜(ℂ, A))) 0 := by
  simpa using α.hasDerivAt_perturbationCocycle P 0

/-- On the generator domain of `α`, the orbits of the perturbed dynamics have derivative
`δ a + i[P, a]` at time zero. -/
private theorem hasDerivAt_perturbed_zero (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α.perturbed hP (Multiplicative.ofAdd t) a)
      (α.generator a + Complex.I • (P * a - a * P)) 0 := by
  simpa using DoubleCentralizer.hasDerivAt_conj_zero hP (α.perturbationCocycle_zero P)
    (hasDerivAt_perturbationCocycle_zero α)
    (fun t => α.coe_perturbed_apply hP (Multiplicative.ofAdd t) a) (α.hasDerivAt_zero a)

/-- The perturbation cocycle of `-P` for the perturbed dynamics `α^P` is the adjoint of the
perturbation cocycle of `P` for `α`. -/
theorem perturbationCocycle_perturbed_neg (t : ℝ) :
    (α.perturbed hP).perturbationCocycle (-P) t = star (α.perturbationCocycle P t) := by
  refine congrFun ((α.perturbed hP).eq_perturbationCocycle (-P)
    (f := fun s => star (α.perturbationCocycle P s)) (by simp) fun s => ?_).symm t
  have hu := α.perturbationCocycle_mem_unitary hP s
  convert (α.hasDerivAt_perturbationCocycle P s).star using 1
  simp only [coe_perturbed_apply, toAdd_ofAdd, map_neg, DoubleCentralizer.coe_neg, star_mul,
    star_smul, ← DoubleCentralizer.coe_star, ← map_star, hP.star_eq, Complex.star_def,
    Complex.conj_I, mul_smul_comm, ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul, neg_smul,
    mul_neg, smul_neg]

/-- Perturbing the perturbed dynamics `α^P` by `-P` recovers `α`. -/
@[simp]
theorem perturbed_perturbed_neg : (α.perturbed hP).perturbed hP.neg = α := by
  ext t a
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  have hu := α.perturbationCocycle_mem_unitary hP t.toAdd
  rw [coe_perturbed_apply, perturbationCocycle_perturbed_neg, coe_perturbed_apply, star_star]
  simp only [← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]
  simp only [mul_assoc, Unitary.star_mul_self_of_mem hu, mul_one]

/-- A bounded perturbation does not change the domain of the generator. -/
theorem generator_perturbed_domain :
    (α.perturbed hP).generator.domain = α.generator.domain := by
  ext a
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · -- Perturbing `α^P` back by `-P` recovers `α`.
    have h := hasDerivAt_perturbed_zero (α.perturbed hP) hP.neg ⟨a, ha⟩
    rw [perturbed_perturbed_neg] at h
    exact (α.mem_generator_domain_iff_differentiableAt a).2 h.differentiableAt
  · exact ((α.perturbed hP).mem_generator_domain_iff_differentiableAt a).2
      (hasDerivAt_perturbed_zero α hP ⟨a, ha⟩).differentiableAt

/-- The generator of the perturbed dynamics is `δ + i[P, ·]`, on the domain of the generator `δ`
of `α`. -/
theorem generator_perturbed :
    (α.perturbed hP).generator =
      (Complex.I • (LinearMap.mulLeft ℂ P - LinearMap.mulRight ℂ P)) +ᵥ α.generator := by
  refine LinearPMap.ext (by rw [LinearPMap.vadd_domain, generator_perturbed_domain])
    fun a ha hb => ?_
  rw [LinearPMap.vadd_apply, (α.perturbed hP).generator_eq_of_hasDerivAt ha
    (hasDerivAt_perturbed_zero α hP ⟨a, hb⟩)]
  simp [add_comm]

end Perturbed

end TauCeti.CStarAction
