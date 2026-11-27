/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Lp
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz.Basic
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

* `SchwartzMap.seminorm_postcompCLM_linearIsometry`: postcomposition with a linear isometry
  preserves the Schwartz seminorms.
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

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Postcomposition with a linear isometry preserves the Schwartz seminorms.** The iterated
derivatives of `L ∘ f` are those of `f` followed by `L`, with the same norms. -/
theorem seminorm_postcompCLM_linearIsometry (L : F →ₗᵢ[ℝ] G) (f : 𝓢(E, F)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (postcompCLM L.toContinuousLinearMap f) =
      SchwartzMap.seminorm ℝ k n f := by
  have hcoe : ⇑(postcompCLM L.toContinuousLinearMap f) = L ∘ f :=
    funext fun x ↦ postcompCLM_apply _ f x
  have h (x : E) :
      ‖iteratedFDeriv ℝ n (postcompCLM L.toContinuousLinearMap f) x‖ =
        ‖iteratedFDeriv ℝ n f x‖ := by
    rw [hcoe]
    exact L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top)
  simp only [seminorm_apply, h]

end SchwartzMap

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
  rw [SchwartzMap.seminorm_apply, ← SchwartzMap.seminorm_apply (𝕜 := ℝ)]
  exact SchwartzMap.seminorm_postcompCLM_linearIsometry Complex.ofRealLI (hermiteSchwartzMap n) k m

/-- **Polynomial growth of the Schwartz seminorms of the complex Hermite functions.** For all
`k m` there are `C` and `N` with `p_{k,m}(ψₙ) ≤ C (1 + n)ᴺ` in `𝓢(ℝ, ℂ)` for every `n`. -/
theorem exists_seminorm_complexHermiteSchwartzMap_le (k m : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, SchwartzMap.seminorm ℂ k m (complexHermiteSchwartzMap n) ≤ C * (1 + n) ^ N := by
  simpa only [seminorm_complexHermiteSchwartzMap] using exists_seminorm_hermiteSchwartzMap_le k m

/-- **Polynomial growth of every continuous seminorm along the complex Hermite functions.** For
every continuous seminorm `p` on `𝓢(ℝ, ℂ)` there are `C` and `N` with
`p(ψₙ) ≤ C (1 + n)ᴺ` for every `n`. The real seminorm `f ↦ p(ofReal ∘ f)` on `𝓢(ℝ, ℝ)` is
continuous, so `TauCeti.exists_hermiteSchwartzMap_le_of_continuous` applies to it. -/
theorem exists_complexHermiteSchwartzMap_le_of_continuous (p : Seminorm ℂ 𝓢(ℝ, ℂ))
    (hp : Continuous p) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, p (complexHermiteSchwartzMap n) ≤ C * (1 + n) ^ N :=
  exists_hermiteSchwartzMap_le_of_continuous
    ((p.restrictScalars ℝ).comp (SchwartzMap.postcompCLM Complex.ofRealCLM).toLinearMap)
    (hp.comp (SchwartzMap.postcompCLM Complex.ofRealCLM).continuous)

end TauCeti
