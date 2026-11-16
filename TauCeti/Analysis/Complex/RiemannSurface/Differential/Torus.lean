/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.NowhereVanishing
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import Mathlib.Algebra.Module.ZLattice.Basic
import TauCeti.Algebra.Module.ZLattice.Quotient
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor

/-!
# The holomorphic differential of a complex torus

Let `L` be a lattice in `ℂ` and `X = ℂ / L` the complex torus, the orbit space
`AddAction.orbitRel.Quotient L ℂ` with its quotient complex structure. Translations by `L` do not
change `dz`, so `dz` descends to a `1`-form `TauCeti.RiemannSurface.torusDifferential L` on `X`:
at the class of `z` it is the inverse of the differential of the projection `ℂ → X` at `z`, and
its pullback to `ℂ` is `dz` (`TauCeti.RiemannSurface.pullback_torusDifferential`). In the
coordinate given by a local inverse of the projection it is `dz`, so it is holomorphic and it
vanishes nowhere.

On the compact torus (`IsZLattice ℝ L`) the general results for nowhere vanishing holomorphic
`1`-forms give:

* `TauCeti.RiemannSurface.divisor_torusDifferential`: `div dz = 0`, so the zero divisor is
  canonical (`TauCeti.RiemannSurface.isCanonicalDivisor_zero_torus`) and every canonical divisor
  has degree `0` (`TauCeti.RiemannSurface.degree_eq_zero_of_isCanonicalDivisor_torus`);
* `TauCeti.RiemannSurface.holomorphicOneForms_torus_eq_span_singleton`: every holomorphic
  `1`-form is a constant multiple of `dz`, and
  `TauCeti.RiemannSurface.finrank_holomorphicOneForms_torus`: `h⁰(K) = 1`.

These are the genus-one cases of `h⁰(K) = g` and `deg K = 2g - 2`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§9 and 17 (the differential `dz` on a torus).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable (L : Submodule ℤ ℂ) [DiscreteTopology L]

/-- The local diffeomorphism property of the projection `ℂ → ℂ / L`, at a point. -/
private theorem isLocalDiffeomorphAt_torusMk (z : ℂ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 (Quotient.mk (AddAction.orbitRel L ℂ)) z :=
  TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := 1) z

/-- **The differential `dz` on the complex torus `ℂ / L`.** At a class `x`, it is the inverse of
the differential at a representative of `x` of the projection `ℂ → ℂ / L`; this does not depend on
the representative (`TauCeti.RiemannSurface.torusDifferential_apply_mfderiv`). -/
def torusDifferential : OneForm (AddAction.orbitRel.Quotient L ℂ) := fun x ↦
  ((isLocalDiffeomorphAt_torusMk L x.out).mfderivToContinuousLinearEquiv
    one_ne_zero).symm.toContinuousLinearMap

variable {L}

/-- **The torus differential inverts the projection's differential**: on the differential of the
projection `ℂ → ℂ / L` at any representative `z` of `x`, the form `torusDifferential L` at `x` is
the identity. -/
theorem torusDifferential_apply_mfderiv {x : AddAction.orbitRel.Quotient L ℂ} {z : ℂ}
    (h : Quotient.mk (AddAction.orbitRel L ℂ) z = x) (v : ℂ) :
    torusDifferential L x (mfderiv 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (AddAction.orbitRel L ℂ)) z v) = v := by
  subst h
  have hz : Quotient.mk (AddAction.orbitRel L ℂ) (Quotient.mk (AddAction.orbitRel L ℂ) z).out =
      Quotient.mk (AddAction.orbitRel L ℂ) z := Quotient.out_eq _
  rw [← Submodule.mfderiv_orbitRelQuotient_mk_eq hz]
  exact ((isLocalDiffeomorphAt_torusMk L _).mfderivToContinuousLinearEquiv
    one_ne_zero).symm_apply_apply v

/-- **The pullback of the torus differential to `ℂ` is `dz`.** -/
@[simp]
theorem pullback_torusDifferential :
    (torusDifferential L).pullback (Quotient.mk (AddAction.orbitRel L ℂ)) = mvfderiv 𝓘(ℂ) id := by
  funext z
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [OneForm.pullback_apply]
  refine (torusDifferential_apply_mfderiv (L := L) rfl v).trans ?_
  rw [mvfderiv_eq_fderiv, fderiv_id]
  rfl

/-- The torus differential vanishes nowhere. -/
theorem torusDifferential_apply_ne_zero (x : AddAction.orbitRel.Quotient L ℂ) :
    torusDifferential L x ≠ 0 := by
  intro h0
  have h1 := torusDifferential_apply_mfderiv (Quotient.out_eq x) 1
  rw [h0] at h1
  exact zero_ne_one (α := ℂ) h1

/-- Near every point, the torus differential is the differential of a local inverse of the
projection `ℂ → ℂ / L`. -/
private theorem exists_eventuallyEq_mvfderiv (x : AddAction.orbitRel.Quotient L ℂ) :
    ∃ s : AddAction.orbitRel.Quotient L ℂ → ℂ,
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y) ∧
        ∀ᶠ y in 𝓝 x, mvfderiv 𝓘(ℂ) s y = torusDifferential L y := by
  set hf := isLocalDiffeomorphAt_torusMk L x.out
  have hx : x ∈ hf.localInverse.source := by
    simpa only [Quotient.out_eq] using hf.localInverse_mem_source
  have hU : ∀ᶠ y in 𝓝 x, y ∈ hf.localInverse.source :=
    hf.localInverse.open_source.mem_nhds hx
  have hmd : ∀ y ∈ hf.localInverse.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) hf.localInverse y :=
    fun y hy ↦ (hf.contMDiffOn_localInverse.contMDiffAt
      (hf.localInverse.open_source.mem_nhds hy)).mdifferentiableAt one_ne_zero
  refine ⟨hf.localInverse, hU.mono hmd, ?_⟩
  filter_upwards [hU] with y hy
  have hs := hmd y hy
  have hq : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (AddAction.orbitRel L ℂ))
      (hf.localInverse y) :=
    (isLocalDiffeomorphAt_torusMk L _).mdifferentiableAt one_ne_zero
  have hid : Quotient.mk (AddAction.orbitRel L ℂ) ∘ hf.localInverse =ᶠ[𝓝 y] id :=
    eventuallyEq_of_mem (hf.localInverse.open_source.mem_nhds hy) hf.localInverse_eqOn_right
  have hchain := mfderiv_comp y hq hs
  rw [hid.mfderiv_eq, mfderiv_id] at hchain
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : mfderiv 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (AddAction.orbitRel L ℂ)) (hf.localInverse y)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) hf.localInverse y v) = v :=
    (congrArg (fun T ↦ T v) hchain).symm
  exact (torusDifferential_apply_mfderiv (hf.localInverse_right_inv hy) _).symm.trans
    (congrArg (torusDifferential L y) hv)

/-- The torus differential is holomorphic. -/
theorem holomorphicAt_torusDifferential (x : AddAction.orbitRel.Quotient L ℂ) :
    (torusDifferential L).HolomorphicAt x := by
  obtain ⟨s, hs, hω⟩ := exists_eventuallyEq_mvfderiv x
  exact (OneForm.holomorphicAt_mvfderiv hs).congr hω

/-- The torus differential is a holomorphic `1`-form. -/
theorem torusDifferential_mem_holomorphicOneForms :
    torusDifferential L ∈ holomorphicOneForms (AddAction.orbitRel.Quotient L ℂ) :=
  mem_holomorphicOneForms.2 holomorphicAt_torusDifferential

variable [IsZLattice ℝ L]

/-- **`div dz = 0` on a complex torus.** -/
@[simp]
theorem divisor_torusDifferential : (torusDifferential L).divisor = 0 :=
  OneForm.divisor_eq_zero_of_apply_ne_zero torusDifferential_mem_holomorphicOneForms
    torusDifferential_apply_ne_zero

/-- **The zero divisor is canonical on a complex torus.** -/
theorem isCanonicalDivisor_zero_torus :
    IsCanonicalDivisor (0 : WeilDivisor (AddAction.orbitRel.Quotient L ℂ)) :=
  OneForm.isCanonicalDivisor_zero_of_apply_ne_zero torusDifferential_mem_holomorphicOneForms
    torusDifferential_apply_ne_zero

/-- **`deg K = 0` on a complex torus**: every canonical divisor of `ℂ / L` has degree zero. -/
theorem degree_eq_zero_of_isCanonicalDivisor_torus
    {K : WeilDivisor (AddAction.orbitRel.Quotient L ℂ)} (hK : IsCanonicalDivisor K) :
    WeilDivisor.degree K = 0 := by
  rw [MeromorphicFunction.degree_eq_of_linearlyEquivalent
    (hK.linearlyEquivalent isCanonicalDivisor_zero_torus), WeilDivisor.degree_zero]

/-- **Every holomorphic `1`-form on a complex torus is a constant multiple of `dz`.** -/
theorem holomorphicOneForms_torus_eq_span_singleton :
    holomorphicOneForms (AddAction.orbitRel.Quotient L ℂ) = ℂ ∙ torusDifferential L :=
  OneForm.holomorphicOneForms_eq_span_singleton_of_apply_ne_zero
    torusDifferential_mem_holomorphicOneForms torusDifferential_apply_ne_zero

/-- **`h⁰(K) = 1` on a complex torus**, the genus-one case of `h⁰(K) = g`. -/
theorem finrank_holomorphicOneForms_torus :
    Module.finrank ℂ (holomorphicOneForms (AddAction.orbitRel.Quotient L ℂ)) = 1 :=
  OneForm.finrank_holomorphicOneForms_eq_one_of_apply_ne_zero
    torusDifferential_mem_holomorphicOneForms torusDifferential_apply_ne_zero

end TauCeti.RiemannSurface
