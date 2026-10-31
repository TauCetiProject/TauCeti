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
# Unitary cocycles of bounded perturbations of C⋆-dynamics

Let `τ` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A` and let
`P ∈ A`. The perturbation cocycle `Γ t` is the time-ordered exponential of the path
`s ↦ i τ_s(P)` in the multiplier algebra `𝓜(ℂ, A)`, given by the norm-convergent Dyson series

`Γ t = 1 + Σ_{n ≥ 1} iⁿ ∫_{0 ≤ s₁ ≤ ⋯ ≤ sₙ ≤ t} τ_{s₁}(P) ⋯ τ_{sₙ}(P) ds` for `t ≥ 0`.

For `t < 0` the `n`-th term instead integrates over `t ≤ sₙ ≤ ⋯ ≤ s₁ ≤ 0`, with an extra
factor `(-1)ⁿ`.

It is the unique solution of `Γ' t = i Γ t τ_t(P)` with `Γ 0 = 1`. When `P` is self-adjoint,
each `Γ t` is unitary, and the family satisfies the cocycle identity
`Γ (s + t) = Γ s τ_s(Γ t)` for the induced action on multipliers.

For self-adjoint `P`, conjugating by these cocycles gives the perturbed dynamics
`CStarAction.perturb`, acting at time `t` by `a ↦ Γ t τ_t(a) Γ t⋆` on `A`. Its generator has
the same domain as the generator `δ` of `τ` and equals `δ + i[P, ·]` there
(`CStarAction.generator_perturb`).

A multiplier-valued cocycle is used so that `A` need not be unital; the path itself is
norm-continuous because `P` lies in `A`.

## Main declarations

* `TauCeti.CStarAction.perturbationCocycle`: the cocycle `Γ` of the perturbation `P`.
* `TauCeti.CStarAction.hasDerivAt_perturbationCocycle`: `Γ' t = Γ t * (i τ_t(P))`.
* `TauCeti.CStarAction.eq_perturbationCocycle`: uniqueness of this initial value problem.
* `TauCeti.CStarAction.perturbationCocycle_mem_unitary`: unitarity for self-adjoint `P`.
* `TauCeti.CStarAction.perturbationCocycle_add`: the cocycle identity.
* `TauCeti.CStarAction.perturbationCocycle_neg`: `Γ (-t) = τ_{-t}(Γ t⋆)`.
* `TauCeti.CStarAction.perturb`: the perturbed dynamics `a ↦ Γ t τ_t(a) Γ t⋆`.
* `TauCeti.CStarAction.generator_perturb`: its generator is `δ + i[P, ·]`, with the domain of `δ`.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.4.1, for the perturbation cocycle, its Dyson expansion and the perturbed dynamics.
-/

public section

noncomputable section

open Complex
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

/-- The cocycle of the zero perturbation is the identity. -/
@[simp]
theorem perturbationCocycle_zero_left : α.perturbationCocycle 0 = 1 := by
  have h0 : ((0 : A) : 𝓜(ℂ, A)) = 0 := map_zero (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))
  exact (α.eq_perturbationCocycle 0 rfl fun t =>
    (hasDerivAt_const t (1 : 𝓜(ℂ, A))).congr_deriv (by simp [h0])).symm

/-! ### The perturbed dynamics -/

variable {P}

/-- The perturbation of a real C⋆-dynamics `α` by a self-adjoint `P`, acting at time `t` by
`a ↦ Γ t α_t(a) Γ t⋆`, where `Γ` is the perturbation cocycle. -/
def perturb (hP : IsSelfAdjoint P) : CStarAction (Multiplicative ℝ) A where
  toMonoidHom :=
    { toFun := fun t => (α t).trans (DoubleCentralizer.conjStarAlgAut
        ⟨α.perturbationCocycle P t.toAdd, α.perturbationCocycle_mem_unitary hP t.toAdd⟩)
      map_one' := by
        ext a
        apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
        simp [one_apply]
      map_mul' := fun s t => by
        ext a
        apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
        have h := α.multiplier_coe s (DoubleCentralizer.conjStarAlgAut
          ⟨α.perturbationCocycle P t.toAdd, α.perturbationCocycle_mem_unitary hP t.toAdd⟩
          (α t a))
        simp only [StarAlgEquiv.trans_apply, StarAlgEquiv.mul_apply,
          DoubleCentralizer.coe_conjStarAlgAut_apply] at h ⊢
        rw [← h, toAdd_mul, perturbationCocycle_add, ofAdd_toAdd, mul_apply,
          ← multiplier_coe, map_mul (α.multiplier s), map_mul (α.multiplier s),
          map_star (α.multiplier s), star_mul]
        simp only [mul_assoc] }
  continuous_orbit a := by
    have hc := DoubleCentralizer.isometry_coe (𝕜 := ℂ) (A := A)
    rw [hc.isEmbedding.continuous_iff]
    have hΓ := (α.continuous_perturbationCocycle P).comp continuous_toAdd
    refine ((hΓ.mul (hc.continuous.comp
      (α.continuous_orbit a))).mul hΓ.star).congr fun t => ?_
    simp

theorem perturb_apply (hP : IsSelfAdjoint P) (t : Multiplicative ℝ) (a : A) :
    α.perturb hP t a = DoubleCentralizer.conjStarAlgAut
      ⟨α.perturbationCocycle P t.toAdd, α.perturbationCocycle_mem_unitary hP t.toAdd⟩ (α t a) :=
  (rfl)

/-- The perturbed dynamics, seen in the multiplier algebra. -/
@[simp]
theorem coe_perturb_apply (hP : IsSelfAdjoint P) (t : ℝ) (a : A) :
    ((α.perturb hP (Multiplicative.ofAdd t) a : A) : 𝓜(ℂ, A)) =
      α.perturbationCocycle P t * (α (Multiplicative.ofAdd t) a : 𝓜(ℂ, A)) *
        star (α.perturbationCocycle P t) := by
  simp [perturb_apply]

/-- The derivative of the perturbation cocycle at time zero. -/
private theorem hasDerivAt_perturbationCocycle_zero :
    HasDerivAt (α.perturbationCocycle P) (I • (P : 𝓜(ℂ, A))) 0 := by
  simpa [one_apply] using α.hasDerivAt_perturbationCocycle P 0

private theorem star_I_smul_coe (hP : IsSelfAdjoint P) :
    star (I • (P : 𝓜(ℂ, A))) = -(I • (P : 𝓜(ℂ, A))) := by
  have hs : star (P : 𝓜(ℂ, A)) = P :=
    (map_star (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A)) P).symm.trans
      (congrArg _ hP.star_eq)
  rw [star_smul, hs, star_def, conj_I, neg_smul]

/-- The perturbed orbit of a generator-domain element has derivative `δ(a) + i(Pa - aP)` at zero. -/
private theorem hasDerivAt_perturb_zero (hP : IsSelfAdjoint P) (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α.perturb hP (Multiplicative.ofAdd t) (a : A))
      (α.generator a + I • (P * a - a * P)) 0 := by
  have hΓ := α.hasDerivAt_perturbationCocycle_zero (P := P)
  refine DoubleCentralizer.hasDerivAt_coe_iff.mp ?_
  simp only [coe_perturb_apply]
  convert (hΓ.mul (DoubleCentralizer.hasDerivAt_coe_iff.mpr (α.hasDerivAt_zero a))).mul hΓ.star
    using 1
  rw [star_I_smul_coe hP]
  simp only [Pi.mul_apply, perturbationCocycle_zero, ofAdd_zero, one_apply, star_one, mul_one,
    one_mul]
  simp only [← DoubleCentralizer.coeHom_apply (𝕜 := ℂ), map_add, map_sub, map_smul, map_mul,
    mul_neg, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- The perturbed dynamics has the same generator domain as the original dynamics. -/
@[simp]
theorem mem_generator_perturb_domain_iff (hP : IsSelfAdjoint P) (a : A) :
    a ∈ (α.perturb hP).generator.domain ↔ a ∈ α.generator.domain := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · -- Undo the unitary conjugation: `α_t(a) = Γ t⋆ (Γ t α_t(a) Γ t⋆) Γ t`.
    rw [mem_generator_domain_iff_differentiableAt]
    have hΓ := α.hasDerivAt_perturbationCocycle_zero (P := P)
    have hb := DoubleCentralizer.hasDerivAt_coe_iff.mpr
      ((α.perturb hP).hasDerivAt_zero ⟨a, ha⟩)
    have h := (hΓ.star.mul hb).mul hΓ
    refine (DoubleCentralizer.hasDerivAt_coe_iff (d := (α.perturb hP).generator ⟨a, ha⟩ -
      I • (P * a - a * P))).mp ?_ |>.differentiableAt
    convert h using 1
    · funext t
      have hu := α.perturbationCocycle_mem_unitary hP t
      simp only [Pi.mul_apply, coe_perturb_apply, ← mul_assoc, Unitary.star_mul_self_of_mem hu,
        one_mul]
      rw [mul_assoc, Unitary.star_mul_self_of_mem hu, mul_one]
    · rw [star_I_smul_coe hP]
      simp only [Pi.mul_apply, perturbationCocycle_zero, ofAdd_zero, one_apply, star_one,
        mul_one, one_mul, coe_perturb_apply]
      simp only [← DoubleCentralizer.coeHom_apply (𝕜 := ℂ), map_sub, map_smul,
        map_mul, neg_mul, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
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

/-- Perturbing by zero recovers the original dynamics. -/
@[simp]
theorem perturb_zero : α.perturb (IsSelfAdjoint.zero A) = α := by
  ext t a
  apply DoubleCentralizer.coe_injective (𝕜 := ℂ)
  rw [← ofAdd_toAdd t, coe_perturb_apply]
  simp

end TauCeti.CStarAction
