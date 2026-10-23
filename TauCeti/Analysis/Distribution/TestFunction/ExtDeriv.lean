/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Distribution.Distribution
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The exterior derivative of test forms

For an open set `Ω` of a real normed space `E`, a *test `k`-form* on `Ω` with coefficients in
`F` is a test function `ω ∈ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)`: a smooth compactly supported `k`-form whose
support lies in `Ω`. This file packages Mathlib's exterior derivative `extDeriv` of differential
forms on normed spaces as a continuous linear map between test forms, in the style of Mathlib's
`TestFunction.fderivCLM`.

Test forms are the Euclidean chart model of the test forms acted on by currents: a `k`-current
on `Ω` is a continuous linear functional `T` on test `k`-forms, and its boundary is the transpose
`∂T = T ∘ d` of this exterior derivative. The identity `d ∘ d = 0` gives `∂ ∘ ∂ = 0`.

In degree `k + 1 ≥ dim E`, the interior product `ι_y α` of a constant form `α` times a scalar test
function `g` has exterior derivative `∂_y g • α`. Consequently, if a continuous linear functional
`T` on test `(k + 1)`-forms annihilates every exact test form, then the scalar distribution
`g ↦ T (g • α)` has vanishing distributional derivatives in every direction. This is the step that
reduces the constancy theorem for top-degree currents without boundary to the constancy of scalar
distributions whose derivatives all vanish.

## Main declarations

* `TestFunction.extDerivCLM`: the exterior derivative `𝓓(Ω, Λᵏ) →L[ℝ] 𝓓(Ω, Λᵏ⁺¹)`.
* `TestFunction.extDerivCLM_apply`: pointwise, it is Mathlib's `extDeriv`.
* `TestFunction.extDerivCLM_extDerivCLM`: `d (d ω) = 0`.
* `TestFunction.extDerivCLM_monoCLM`: the exterior derivative commutes with extending a test form
  from `Ω'` to a larger open set `Ω`.
* `TestFunction.extDerivCLM_postcompCLM_toSpanSingleton_curryLeft`: the top-degree formula
  `d (g • ι_y α) = ∂_y g • α`.
* `TestFunction.map_postcompCLM_toSpanSingleton_lineDerivOp_eq_zero`: a functional on top-degree
  test forms annihilating exact forms induces scalar distributions with vanishing derivatives.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §1.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousAlternatingMap LineDeriv
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' : Opens E} {k : ℕ}

/-- The **exterior derivative** of test `k`-forms on `Ω` with coefficients in `F`, as a
continuous linear map into the test `(k + 1)`-forms. It is the alternatization
`ContinuousAlternatingMap.alternatizeUncurryFinCLM` of the Fréchet derivative
`TestFunction.fderivCLM`, so pointwise it is Mathlib's `extDeriv`. -/
noncomputable def extDerivCLM :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  postcompCLM (alternatizeUncurryFinCLM ℝ E F) ∘L fderivCLM ℝ ⊤ ⊤

/-- The exterior derivative of a test form is pointwise its exterior derivative as a
differential form. -/
@[simp]
theorem extDerivCLM_apply (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) (x : E) :
    extDerivCLM ω x = extDeriv (ω : E → E [⋀^Fin k]→L[ℝ] F) x := by
  simp [extDerivCLM, extDeriv]

/-- The exterior derivative of a test form, as a function, is its exterior derivative as a
differential form. -/
theorem coe_extDerivCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    (extDerivCLM ω : E → E [⋀^Fin (k + 1)]→L[ℝ] F) = extDeriv (ω : E → E [⋀^Fin k]→L[ℝ] F) :=
  funext (extDerivCLM_apply ω)

/-- **`d ∘ d = 0`** on test forms. -/
@[simp]
theorem extDerivCLM_extDerivCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (extDerivCLM ω) = 0 := by
  ext x : 1
  rw [extDerivCLM_apply, coe_extDerivCLM, extDeriv_extDeriv ω.contDiff (by simp)]
  rfl

/-- **`d ∘ d = 0`** on test forms, as an identity of continuous linear maps. -/
@[simp]
theorem extDerivCLM_comp_extDerivCLM :
    (extDerivCLM ∘L extDerivCLM :
      𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] F)) = 0 := by
  ext ω : 1
  exact extDerivCLM_extDerivCLM ω

/-- The exterior derivative does not enlarge the support of a test form. -/
theorem tsupport_extDerivCLM_subset (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    tsupport (extDerivCLM ω : E → E [⋀^Fin (k + 1)]→L[ℝ] F) ⊆ tsupport ω := by
  rw [coe_extDerivCLM]
  exact (tsupport_comp_subset (map_zero (alternatizeUncurryFinCLM ℝ E F)) _).trans
    (tsupport_fderiv_subset ℝ)

/-- The exterior derivative of a test form extended from `Ω'` to a larger open set `Ω` is the
extension of its exterior derivative. -/
@[simp]
theorem extDerivCLM_monoCLM (h : Ω' ≤ Ω) (ω : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (monoCLM ℝ ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      (monoCLM ℝ (extDerivCLM ω) : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) := by
  ext x : 1
  simp [monoCLM_apply, h]

/-- In degree zero, the exterior derivative of the `0`-form with values `f` is the `1`-form
`Df`. -/
theorem extDerivCLM_postcompCLM_constOfIsEmptyLIE (f : 𝓓(Ω, F)) :
    extDerivCLM (postcompCLM (constOfIsEmptyLIE ℝ E F (Fin 0) : F →L[ℝ] E [⋀^Fin 0]→L[ℝ] F) f) =
      postcompCLM
        (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1) :
          (E →L[ℝ] F) →L[ℝ] E [⋀^Fin 1]→L[ℝ] F)
        (fderivCLM ℝ ⊤ ⊤ f) := by
  ext x : 1
  simp only [extDerivCLM_apply, postcompCLM_apply, fderivCLM_apply]
  exact extDeriv_constOfIsEmpty (f : E → F) x

/-- **The exterior derivative in top degree.** If `dim E ≤ k + 1`, then for a constant
`(k + 1)`-form `α`, a vector `y` and a scalar test function `g`, the test `k`-form `g • ι_y α`
has exterior derivative `∂_y g • α`. Here `ι_y α = α.curryLeft y` is the interior product. -/
theorem extDerivCLM_postcompCLM_toSpanSingleton_curryLeft [FiniteDimensional ℝ E]
    (hk : Module.finrank ℝ E ≤ k + 1) (α : E [⋀^Fin (k + 1)]→L[ℝ] F) (y : E) (g : 𝓓(Ω, ℝ)) :
    extDerivCLM (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (α.curryLeft y)) g) =
      postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ α) (∂_{y} g) := by
  ext x : 1
  have hg : DifferentiableAt ℝ (g : E → ℝ) x := g.contDiff.differentiable (by simp) x
  -- The derivative of `g • α` at `x` is the constant-coefficient family `L w = Dg(x) w • α`.
  set L : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] F := (fderiv ℝ (g : E → ℝ) x).smulRight α
  -- Its alternatization is a `(k + 2)`-form on a space of dimension at most `k + 1`.
  have hzero : alternatizeUncurryFin L = 0 :=
    eq_zero_of_finrank_lt _ (by simpa using Nat.lt_succ_of_le hk)
  have hcartan := alternatizeUncurryFin_curryLeft_comp_add_curryLeft L y
  rw [hzero, curryLeft_zero, zero_apply, add_zero] at hcartan
  have hcomp : (curryLeftLI (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearMap.flip y ∘L L =
      (fderiv ℝ (g : E → ℝ) x).smulRight (α.curryLeft y) := by
    ext w : 1
    simp [L]
  rw [hcomp] at hcartan
  have hd : fderiv ℝ (fun z ↦ g z • α.curryLeft y) x =
      (fderiv ℝ (g : E → ℝ) x).smulRight (α.curryLeft y) :=
    (hg.hasFDerivAt.smul_const (α.curryLeft y)).fderiv
  have hfun : (ContinuousLinearMap.toSpanSingleton ℝ (α.curryLeft y)) ∘ (g : E → ℝ) =
      fun z ↦ g z • α.curryLeft y :=
    funext fun z ↦ ContinuousLinearMap.toSpanSingleton_apply ℝ (α.curryLeft y) (g z)
  simp only [extDerivCLM_apply, postcompCLM_apply, extDeriv]
  rw [hfun, hd, hcartan]
  simp [L, lineDerivOp_eq_lineDerivCLM ℝ, hg.lineDeriv_eq_fderiv]

/-- A continuous linear functional `T` on test `(k + 1)`-forms, `dim E ≤ k + 1`, that annihilates
every exact test form (that is, a top-degree current with zero boundary `T ∘ d = 0`) annihilates
`∂_y g • α` for every constant `(k + 1)`-form `α`, vector `y` and scalar test function `g`. Thus
the scalar distribution `g ↦ T (g • α)` has vanishing distributional derivatives. -/
theorem map_postcompCLM_toSpanSingleton_lineDerivOp_eq_zero [FiniteDimensional ℝ E]
    {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G} (hT : T ∘L extDerivCLM = 0)
    (hk : Module.finrank ℝ E ≤ k + 1) (α : E [⋀^Fin (k + 1)]→L[ℝ] F) (y : E) (g : 𝓓(Ω, ℝ)) :
    T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ α) (∂_{y} g)) = 0 := by
  rw [← extDerivCLM_postcompCLM_toSpanSingleton_curryLeft hk, ← ContinuousLinearMap.comp_apply,
    hT, zero_apply]

end TestFunction
