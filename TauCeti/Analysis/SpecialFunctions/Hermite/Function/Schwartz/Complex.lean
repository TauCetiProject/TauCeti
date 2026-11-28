/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Lp
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz.Seminorm

/-!
# The Hermite functions as complex Schwartz functions

The Hermite function `ψₙ` is real valued, and Tau Ceti packages it as the real Schwartz function
`TauCeti.hermiteSchwartzMap n : 𝓢(ℝ, ℝ)`. Applications in quantum mechanics and harmonic analysis
expand complex Schwartz functions in the `ψₙ`, so they need `ψₙ` in `𝓢(ℝ, ℂ)`.
`TauCeti.complexHermiteSchwartzMap n` is its image under postcomposition with the inclusion
`ℝ → ℂ` (`SchwartzMap.postcompCLM Complex.ofRealCLM`).

Postcomposition with a linear isometry does not change the norms of the iterated derivatives,
so it preserves every Schwartz seminorm (`SchwartzMap.seminorm_postcompCLM_linearIsometry`). The
seminorms of the complex Hermite functions are therefore those of the real ones, and the
polynomial growth `TauCeti.exists_seminorm_hermiteSchwartzMap_le` carries over unchanged.

## Main statements

* `TauCeti.complexHermiteSchwartzMap`: the Hermite function `ψₙ` in `𝓢(ℝ, ℂ)`, with
  `TauCeti.complexHermiteSchwartzMap_apply` and its `L²` class
  `TauCeti.toLp_complexHermiteSchwartzMap`.
* `TauCeti.seminorm_complexHermiteSchwartzMap`: its seminorms are those of
  `TauCeti.hermiteSchwartzMap n`.
* `TauCeti.exists_seminorm_complexHermiteSchwartzMap_le`,
  `TauCeti.exists_complexHermiteSchwartzMap_le_of_continuous`: every Schwartz seminorm, and every
  continuous seminorm on `𝓢(ℝ, ℂ)`, grows at most polynomially along the `ψₙ`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, §V.3.
-/

public section

open MeasureTheory
open scoped SchwartzMap

namespace TauCeti

/-- The Hermite function `ψₙ` as a complex Schwartz function: the real Schwartz function
`TauCeti.hermiteSchwartzMap n` postcomposed with the inclusion `ℝ → ℂ`. -/
noncomputable def complexHermiteSchwartzMap (n : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (hermiteSchwartzMap n)

/-- The underlying function of `TauCeti.complexHermiteSchwartzMap n` is `ψₙ`, cast to `ℂ`. -/
@[simp]
theorem complexHermiteSchwartzMap_apply (n : ℕ) (x : ℝ) :
    complexHermiteSchwartzMap n x = (hermiteFunction n x : ℂ) := by
  rw [complexHermiteSchwartzMap, SchwartzMap.postcompCLM_apply, hermiteSchwartzMap_apply,
    Complex.ofRealCLM_apply]

/-- The coercion of `TauCeti.complexHermiteSchwartzMap n` is the complexified Hermite
function. -/
@[simp]
theorem coe_complexHermiteSchwartzMap (n : ℕ) :
    ⇑(complexHermiteSchwartzMap n) = fun x : ℝ ↦ (hermiteFunction n x : ℂ) :=
  funext (complexHermiteSchwartzMap_apply n)

/-- The `L²` class of `TauCeti.complexHermiteSchwartzMap n` is the Hermite basis vector
`TauCeti.hermiteFunctionLp ℂ n`. -/
theorem toLp_complexHermiteSchwartzMap (n : ℕ) :
    (complexHermiteSchwartzMap n).toLp 2 = hermiteFunctionLp ℂ n := by
  refine Lp.ext ?_
  filter_upwards [(complexHermiteSchwartzMap n).coeFn_toLp 2 volume,
    coeFn_hermiteFunctionLp (𝕜 := ℂ) n] with x hx hy
  rw [hx, hy, complexHermiteSchwartzMap_apply, Complex.coe_algebraMap]

/-- The Schwartz seminorms of `TauCeti.complexHermiteSchwartzMap n` are those of the real
Schwartz function `TauCeti.hermiteSchwartzMap n`. -/
@[simp]
theorem seminorm_complexHermiteSchwartzMap (k m n : ℕ) :
    SchwartzMap.seminorm ℂ k m (complexHermiteSchwartzMap n) =
      SchwartzMap.seminorm ℝ k m (hermiteSchwartzMap n) := by
  -- `Complex.ofRealCLM` is defined as the linear isometry `Complex.ofRealLI`.
  rw [SchwartzMap.seminorm_eq_seminorm ℂ ℝ, complexHermiteSchwartzMap, Complex.ofRealCLM]
  exact SchwartzMap.seminorm_postcompCLM_linearIsometry Complex.ofRealLI (hermiteSchwartzMap n) k m

/-- **Polynomial growth of the Schwartz seminorms of the complex Hermite functions.** For all
`k m` there are `C` and `N` with `p_{k,m}(ψₙ) ≤ C (1 + n)ᴺ` in `𝓢(ℝ, ℂ)` for every `n`. -/
theorem exists_seminorm_complexHermiteSchwartzMap_le (k m : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, SchwartzMap.seminorm ℂ k m (complexHermiteSchwartzMap n) ≤ C * (1 + n) ^ N := by
  simpa only [seminorm_complexHermiteSchwartzMap] using exists_seminorm_hermiteSchwartzMap_le k m

/-- **Polynomial growth of every continuous seminorm along the complex Hermite functions.** For
every continuous seminorm `p` on `𝓢(ℝ, ℂ)` there are `C` and `N` with
`p(ψₙ) ≤ C (1 + n)ᴺ` for every `n`. -/
theorem exists_complexHermiteSchwartzMap_le_of_continuous (p : Seminorm ℂ 𝓢(ℝ, ℂ))
    (hp : Continuous p) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, p (complexHermiteSchwartzMap n) ≤ C * (1 + n) ^ N := by
  -- Apply the real result to the continuous real seminorm `f ↦ p(ofReal ∘ f)` on `𝓢(ℝ, ℝ)`.
  set L := SchwartzMap.postcompCLM (E := ℝ) Complex.ofRealCLM
  obtain ⟨C, N, hC, h⟩ := exists_hermiteSchwartzMap_le_of_continuous
    ((p.restrictScalars ℝ).comp L.toLinearMap) (by
      rw [Seminorm.coe_comp, Seminorm.coe_restrictScalars, ContinuousLinearMap.coe_coe]
      exact hp.comp L.continuous)
  refine ⟨C, N, hC, fun n ↦ ?_⟩
  simpa only [Seminorm.comp_apply, Seminorm.coe_restrictScalars, ContinuousLinearMap.coe_coe,
    L, complexHermiteSchwartzMap] using h n

end TauCeti
