/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SchwartzMap

/-!
# Tempered distributions are distributions

Test functions on an open set `Ω`, extended by zero, are Schwartz functions, continuously for the
inductive limit topology (`TestFunction.toSchwartzMapCLM`). Transposing this inclusion, a tempered
distribution `S` on `E` restricts to the distribution `φ ↦ S φ` on `Ω`
(`TemperedDistribution.toDistribution`). This is how statements about tempered distributions, for
instance about elements of Mathlib's Bessel-potential spaces `H^s` and the operators acting on
them, become statements about distributions on open sets, such as their wave front sets.

The complex-linear extension of the restriction to complex test functions is `S` itself
(`TemperedDistribution.complexPairing_toDistribution`).

## Main declarations

* `TemperedDistribution.toDistribution Ω S`: the restriction of `S` to `Ω`.
* `TemperedDistribution.toDistribution_apply`: its value on a real test function.
* `TemperedDistribution.complexPairing_toDistribution`: its value on a complex test function.
-/

public section

noncomputable section

open Complex TopologicalSpace TestFunction
open scoped Distributions SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

variable (Ω : Opens E) in
/-- The **restriction of a tempered distribution** `S` on `E` to an open set `Ω`: the
distribution `φ ↦ S φ` on `Ω`, where the real test function `φ` is viewed as a complex Schwartz
function on `E`. -/
def toDistribution (S : 𝓢'(E, F)) : 𝓓'(Ω, F) :=
  ((S : 𝓢(E, ℂ) →L[ℂ] F).comp (toSchwartzMapCLM ℂ)).restrictScalars ℝ ∘L
    postcompCLM (𝕜 := ℝ) ofRealCLM

variable {Ω : Opens E}

/-- The value of the restriction of `S` on a real test function `φ` is the value of `S` on the
complex Schwartz function `φ`. -/
theorem toDistribution_apply (S : 𝓢'(E, F)) (φ : 𝓓(Ω, ℝ)) :
    toDistribution Ω S φ = S (toSchwartzMapCLM ℂ (postcompCLM (𝕜 := ℝ) ofRealCLM φ)) :=
  (rfl)

@[simp]
theorem toDistribution_add (S S' : 𝓢'(E, F)) :
    toDistribution Ω (S + S') = toDistribution Ω S + toDistribution Ω S' :=
  (rfl)

@[simp]
theorem toDistribution_smul (c : ℂ) (S : 𝓢'(E, F)) :
    toDistribution Ω (c • S) = c • toDistribution Ω S :=
  (rfl)

@[simp]
theorem toDistribution_neg (S : 𝓢'(E, F)) : toDistribution Ω (-S) = -toDistribution Ω S :=
  (rfl)

@[simp]
theorem toDistribution_sub (S S' : 𝓢'(E, F)) :
    toDistribution Ω (S - S') = toDistribution Ω S - toDistribution Ω S' :=
  (rfl)

@[simp]
theorem toDistribution_zero : toDistribution Ω (0 : 𝓢'(E, F)) = 0 :=
  (rfl)

/-- **The restriction of a scalar tempered distribution on complex test functions.** The
complex-linear extension of the restriction of `S` pairs it with a complex test function `φ` as
`S` with the Schwartz function `φ`. -/
@[simp]
theorem complexPairing_toDistribution (S : 𝓢'(E, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (toDistribution Ω S).complexPairing φ = S (toSchwartzMapCLM ℂ φ) := by
  have hφ : toSchwartzMapCLM ℂ φ =
      toSchwartzMapCLM ℂ (postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) reCLM φ)) +
        I • toSchwartzMapCLM ℂ (postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) imCLM φ)) := by
    ext x
    simp [mul_comm I, re_add_im]
  rw [Distribution.complexPairing_apply, toDistribution_apply, toDistribution_apply, hφ, map_add,
    map_smul, smul_eq_mul]

end TemperedDistribution
