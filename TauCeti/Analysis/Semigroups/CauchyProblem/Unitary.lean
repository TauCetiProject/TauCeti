/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous
public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak solutions of the Cauchy problem for a unitary group

Let `U` be a unitary strongly continuous group on a complex Hilbert space `H`, with generator `A`
(`TauCeti.Semigroups.StronglyContinuousGroup.complexGenerator`), and let `F : ℝ → H` be locally
integrable on `[0, ∞)`. A continuous `u : [0, ∞) → H` is a **weak solution** of `u' = A u + F`,
`u(0) = x`, when for every test vector `ψ` in the domain of `A` and every `t ≥ 0`

`⟪ψ, u t⟫ = ⟪ψ, x⟫ - ∫_{(0,t]} ⟪A ψ, u s⟫ ds + ∫_{(0,t]} ⟪ψ, F s⟫ ds`.

This is the integrated form of `d/dt ⟪ψ, u t⟫ = ⟪A* ψ, u t⟫ + ⟪ψ, F t⟫`, since `A* = -A`. Weak
solutions are exactly the mild solutions
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isForcedMildSolution_iff_forall_inner_eq`),
so by Duhamel's formula there is exactly one, `u t = U t x + ∫_{(0,t]} U (t - s) F s ds`. For a
concrete group the test vectors are concrete functions: for the Schrödinger group they are the
`ψ ∈ L²` with `Δψ ∈ L²`, and the weak formulation becomes the Schrödinger equation tested against
them.

## The argument

Let `v = ∫_{(0,t]} u` and `w = u t - x - ∫_{(0,t]} F`. Being a mild solution means `v ∈ D(A)`
and `A v = w`. Pairing this with `ψ ∈ D(A)` and using the skew-symmetry `⟪ψ, A v⟫ = -⟪A ψ, v⟫`
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.inner_complexGenerator_eq_neg`) gives the
weak formulation, the inner products commuting with the Bochner integrals. Conversely, the weak
formulation says `⟪-w, ψ⟫ = ⟪v, A ψ⟫` for every `ψ ∈ D(A)`, which puts `v` in the domain of the
adjoint `A†` with `A† v = -w`. The generator of a unitary group is skew-adjoint, `A† = -A`
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.complexGenerator_adjoint_eq_neg`), so
`v ∈ D(A)` and `A v = w`. At `t = 0` this reads `0 = u 0 - x`, so the initial value is part of
the weak formulation.

## Main declarations

* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.inner_eq_of_isForcedMildSolution`: a
  mild solution is a weak solution.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isForcedMildSolution_of_forall_inner_eq`:
  a continuous weak solution is a mild solution.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isForcedMildSolution_iff_forall_inner_eq`:
  the two notions agree.

## References

* J. M. Ball, *Strongly continuous semigroups, weak solutions, and the variation of constants
  formula*, Proc. Amer. Math. Soc. 63 (1977), 370–373.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 4.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace LinearPMap

namespace TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : StronglyContinuousGroup H} {F : ℝ → H} {x : H} {u : ℝ → H}

/-- The weak formulation against `ψ` at time `t`, with `φ` standing for `A ψ`, says that
`⟪φ, ∫_{(0,t]} u⟫ = -⟪ψ, u t - x - ∫_{(0,t]} F⟫`: the inner products commute with the time
integrals. -/
private theorem inner_eq_iff_inner_integral_eq {t : ℝ} (hu : IntegrableOn u (Ioc 0 t))
    (hF : IntegrableOn F (Ioc 0 t)) (ψ φ : H) :
    ⟪ψ, u t⟫_ℂ = ⟪ψ, x⟫_ℂ - (∫ s in Ioc 0 t, ⟪φ, u s⟫_ℂ) + ∫ s in Ioc 0 t, ⟪ψ, F s⟫_ℂ ↔
      ⟪φ, ∫ s in Ioc 0 t, u s⟫_ℂ = -⟪ψ, u t - x - ∫ s in Ioc 0 t, F s⟫_ℂ := by
  rw [integral_inner hu, integral_inner hF, inner_sub_right, inner_sub_right]
  constructor <;> intro h <;> linear_combination h

/-- **A mild solution is a weak solution.** If `u` is a mild solution of `u' = A u + F`,
`u(0) = x`, for the generator `A` of a unitary group, then for every `ψ` in the domain of `A`
and every `t ≥ 0`, `⟪ψ, u t⟫ = ⟪ψ, x⟫ - ∫_{(0,t]} ⟪A ψ, u s⟫ ds + ∫_{(0,t]} ⟪ψ, F s⟫ ds`. -/
theorem inner_eq_of_isForcedMildSolution (hU : U.IsUnitary)
    (hu : IsForcedMildSolution U.toSemigroup.generator F x u)
    (ψ : (U.complexGenerator hU).domain) {t : ℝ} (ht : 0 ≤ t) :
    ⟪(ψ : H), u t⟫_ℂ = ⟪(ψ : H), x⟫_ℂ - (∫ s in Ioc 0 t, ⟪U.complexGenerator hU ψ, u s⟫_ℂ) +
      ∫ s in Ioc 0 t, ⟪(ψ : H), F s⟫_ℂ := by
  rw [← generator_def, ← U.complexGenerator_restrictScalars hU] at hu
  have hv := hu.integral_mem_domain ht
  have hA := hu.map_integral_eq_sub ht
  rw [LinearPMap.restrictScalars_apply] at hA
  have hskew := hU.inner_complexGenerator_eq_neg ψ
    ⟨∫ s in Ioc 0 t, u s, (LinearPMap.mem_restrictScalars_domain ℝ _).mp hv⟩
  rw [hA] at hskew
  refine (inner_eq_iff_inner_integral_eq
    ((hu.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_Ioc_of_Ici t)
    (hu.locallyIntegrableOn.integrableOn_Ioc_of_Ici t) _ _).2 ?_
  linear_combination hskew

/-- The weak formulation at a time `t ≥ 0` identifies the generator on the time integral: the
time integral `∫_{(0,t]} u` lies in the domain of `A`, where `A` takes the value
`u t - x - ∫_{(0,t]} F`. -/
private theorem exists_mem_domain_complexGenerator_eq (hU : U.IsUnitary)
    (hF : LocallyIntegrableOn F (Ici 0)) (hu : ContinuousOn u (Ici 0)) {t : ℝ}
    (h : ∀ ψ : (U.complexGenerator hU).domain,
      ⟪(ψ : H), u t⟫_ℂ = ⟪(ψ : H), x⟫_ℂ - (∫ s in Ioc 0 t, ⟪U.complexGenerator hU ψ, u s⟫_ℂ) +
        ∫ s in Ioc 0 t, ⟪(ψ : H), F s⟫_ℂ) :
    ∃ hv : (∫ s in Ioc 0 t, u s) ∈ (U.complexGenerator hU).domain,
      U.complexGenerator hU ⟨_, hv⟩ = u t - x - ∫ s in Ioc 0 t, F s := by
  set A := U.complexGenerator hU
  set w := u t - x - ∫ s in Ioc 0 t, F s
  have hdense : Dense (A.domain : Set H) := by
    rw [complexGenerator_domain]
    exact U.dense_complexDomain hU
  -- The weak formulation says that `-w` is the adjoint of `A` applied to the time integral.
  have hadj : ∀ ψ : A.domain, ⟪-w, (ψ : H)⟫_ℂ = ⟪∫ s in Ioc 0 t, u s, A ψ⟫_ℂ := by
    intro ψ
    have hval : ⟪A ψ, ∫ s in Ioc 0 t, u s⟫_ℂ = -⟪(ψ : H), w⟫_ℂ :=
      (inner_eq_iff_inner_integral_eq
        ((hu.locallyIntegrableOn measurableSet_Ici).integrableOn_Ioc_of_Ici t)
        (hF.integrableOn_Ioc_of_Ici t) _ _).1 (h ψ)
    calc ⟪-w, (ψ : H)⟫_ℂ = (starRingEnd ℂ) ⟪(ψ : H), -w⟫_ℂ := (inner_conj_symm _ _).symm
      _ = (starRingEnd ℂ) ⟪A ψ, ∫ s in Ioc 0 t, u s⟫_ℂ := by rw [inner_neg_right, hval]
      _ = ⟪∫ s in Ioc 0 t, u s, A ψ⟫_ℂ := inner_conj_symm _ _
  have hmem : (∫ s in Ioc 0 t, u s) ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨-w, hadj⟩
  have hval := LinearPMap.adjoint_apply_eq hdense ⟨_, hmem⟩ hadj
  have hA : A† = -A := hU.complexGenerator_adjoint_eq_neg
  have hmem' : (∫ s in Ioc 0 t, u s) ∈ A.domain := by
    rwa [hA, LinearPMap.neg_domain] at hmem
  refine ⟨hmem', ?_⟩
  have hneg : (-A) ⟨_, by rwa [LinearPMap.neg_domain]⟩ = -w := by
    rw [← hval]
    exact LinearPMap.congr_fun hA.symm _ _
  rw [LinearPMap.neg_apply, neg_inj] at hneg
  exact hneg

/-- **A weak solution is a mild solution.** Let `A` be the generator of a unitary group and let
`F` be locally integrable on `[0, ∞)`. If `u` is continuous on `[0, ∞)` and for every `ψ` in the
domain of `A` and every `t ≥ 0`,
`⟪ψ, u t⟫ = ⟪ψ, x⟫ - ∫_{(0,t]} ⟪A ψ, u s⟫ ds + ∫_{(0,t]} ⟪ψ, F s⟫ ds`, then `u` is the mild
solution of `u' = A u + F`, `u(0) = x`. -/
theorem isForcedMildSolution_of_forall_inner_eq (hU : U.IsUnitary)
    (hF : LocallyIntegrableOn F (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (h : ∀ ψ : (U.complexGenerator hU).domain, ∀ t : ℝ, 0 ≤ t →
      ⟪(ψ : H), u t⟫_ℂ = ⟪(ψ : H), x⟫_ℂ - (∫ s in Ioc 0 t, ⟪U.complexGenerator hU ψ, u s⟫_ℂ) +
        ∫ s in Ioc 0 t, ⟪(ψ : H), F s⟫_ℂ) :
    IsForcedMildSolution U.toSemigroup.generator F x u := by
  rw [← generator_def, ← U.complexGenerator_restrictScalars hU]
  have key (t : ℝ) (ht : 0 ≤ t) :=
    exists_mem_domain_complexGenerator_eq hU hF hu fun ψ ↦ h ψ t ht
  refine isForcedMildSolution_iff.2 ⟨inferInstance, hF, hu, ?_, fun t ht ↦ ?_⟩
  · -- At `t = 0` the time integrals vanish, so the identified value `u 0 - x` is `A 0 = 0`.
    obtain ⟨hv, hAv⟩ := key 0 le_rfl
    have hzero : (⟨_, hv⟩ : (U.complexGenerator hU).domain) = 0 := Subtype.ext (by simp)
    rw [hzero, LinearPMap.map_zero] at hAv
    simpa [sub_eq_zero] using hAv.symm
  · obtain ⟨hv, hAv⟩ := key t ht
    exact ⟨(LinearPMap.mem_restrictScalars_domain ℝ _).mpr hv, by
      rw [LinearPMap.restrictScalars_apply]
      exact hAv⟩

/-- **Weak and mild solutions agree** for the Cauchy problem `u' = A u + F`, `u(0) = x`, of the
generator `A` of a unitary group, with `F` locally integrable on `[0, ∞)`: a function continuous
on `[0, ∞)` is the mild solution if and only if for every `ψ` in the domain of `A` and every
`t ≥ 0`, `⟪ψ, u t⟫ = ⟪ψ, x⟫ - ∫_{(0,t]} ⟪A ψ, u s⟫ ds + ∫_{(0,t]} ⟪ψ, F s⟫ ds`. -/
theorem isForcedMildSolution_iff_forall_inner_eq (hU : U.IsUnitary)
    (hF : LocallyIntegrableOn F (Ici 0)) (hu : ContinuousOn u (Ici 0)) :
    IsForcedMildSolution U.toSemigroup.generator F x u ↔
      ∀ ψ : (U.complexGenerator hU).domain, ∀ t : ℝ, 0 ≤ t →
        ⟪(ψ : H), u t⟫_ℂ = ⟪(ψ : H), x⟫_ℂ - (∫ s in Ioc 0 t, ⟪U.complexGenerator hU ψ, u s⟫_ℂ) +
          ∫ s in Ioc 0 t, ⟪(ψ : H), F s⟫_ℂ :=
  ⟨fun hmild ψ _ ht ↦ inner_eq_of_isForcedMildSolution hU hmild ψ ht,
    isForcedMildSolution_of_forall_inner_eq hU hF hu⟩

end TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary
