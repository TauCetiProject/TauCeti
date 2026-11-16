/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The coefficient of the differentiated Cauchy–Riemann system

Write `z = s + i t` on `ℂ` and `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` for coefficient fields
`J, S : ℂ → (V →L[ℝ] V)`. Differentiating `D ξ = η` shows that the pair `Ξ = (∂_s ξ, ∂_t ξ)`
solves `∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
`J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`. This file defines the coefficient `S₂`
pointwise and records its elementary algebra.

## Main declarations

* `TauCeti.differentiatedCRCoefficient`: the coefficient `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`,
  as a function of `S` and of the derivative `DJ` of `J` at a point.
* `TauCeti.differentiatedCRCoefficientL`: `S₂` as a continuous linear map of the pair `(S, DJ)`.
* `TauCeti.differentiatedCRCoefficient_ne_prodMap`: `S₂ ≠ diag(S, S)` as soon as `∂_s J ≠ 0`.

The differentiated system itself is `TauCeti.crOperator_differentiated_system` for `C²` maps and
`TauCeti.ae_differentiated_cauchyRiemann` for Sobolev data.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.4.9.
-/

public section

open Complex

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The zeroth-order coefficient `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` of the differentiated
Cauchy–Riemann system on `V × V`, built from the value `S` of the zeroth-order coefficient and the
derivative `DJ` of the complex structure at a point, with `∂_s J = DJ 1` and `∂_t J = DJ I`. -/
noncomputable def differentiatedCRCoefficient (S : V →L[ℝ] V) (DJ : ℂ →L[ℝ] V →L[ℝ] V) :
    V × V →L[ℝ] V × V :=
  (S.coprod (DJ 1)).prod ((0 : V →L[ℝ] V).coprod (S + DJ I))

/-- The two rows of `S₂`: `S₂ (a, b) = (S a + (∂_s J) b, S b + (∂_t J) b)`. -/
@[simp]
theorem differentiatedCRCoefficient_apply (S : V →L[ℝ] V) (DJ : ℂ →L[ℝ] V →L[ℝ] V) (x : V × V) :
    differentiatedCRCoefficient S DJ x = (S x.1 + DJ 1 x.2, S x.2 + DJ I x.2) := by
  simp [differentiatedCRCoefficient]

/-- The coefficient `S₂` depends continuously and linearly on the pair `(S, DJ)`. -/
noncomputable def differentiatedCRCoefficientL :
    (V →L[ℝ] V) × (ℂ →L[ℝ] V →L[ℝ] V) →L[ℝ] (V × V →L[ℝ] V × V) :=
  let coprodL := (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := V) (F := V) (G := V)
    ℝ).toContinuousLinearMap
  let fst := ContinuousLinearMap.fst ℝ (V →L[ℝ] V) (ℂ →L[ℝ] V →L[ℝ] V)
  let snd := ContinuousLinearMap.snd ℝ (V →L[ℝ] V) (ℂ →L[ℝ] V →L[ℝ] V)
  let ev (v : ℂ) := (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v).comp snd
  (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := V × V) (F := V) (G := V)
    ℝ).toContinuousLinearMap.comp
    ((coprodL.comp (fst.prod (ev 1))).prod (coprodL.comp ((0 : _ →L[ℝ] V →L[ℝ] V).prod
      (fst + ev I))))

/-- `differentiatedCRCoefficientL` evaluates to `differentiatedCRCoefficient`. -/
@[simp]
theorem differentiatedCRCoefficientL_apply (x : (V →L[ℝ] V) × (ℂ →L[ℝ] V →L[ℝ] V)) :
    differentiatedCRCoefficientL x = differentiatedCRCoefficient x.1 x.2 := by
  ext <;> simp [differentiatedCRCoefficientL]

/-- **Check: the coupling term cannot be dropped.** If `∂_s J ≠ 0` at a point, then the coefficient
`S₂` differs from the plausible wrong `diag(S, S)`: its first row contains `∂_s J`. -/
theorem differentiatedCRCoefficient_ne_prodMap (S : V →L[ℝ] V) {DJ : ℂ →L[ℝ] V →L[ℝ] V}
    (hDJ : DJ 1 ≠ 0) : differentiatedCRCoefficient S DJ ≠ S.prodMap S := by
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 hDJ
  intro h
  exact hb (by simpa using congr(($h (0, b)).1))

/-- For a constant complex structure and `S = 0` the coefficient `S₂` vanishes. -/
@[simp]
theorem differentiatedCRCoefficient_zero_zero :
    differentiatedCRCoefficient (0 : V →L[ℝ] V) 0 = 0 := by
  ext <;> simp

end TauCeti
