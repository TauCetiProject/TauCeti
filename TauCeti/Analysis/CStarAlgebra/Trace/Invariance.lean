/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.SemiconjBy

/-!
# Unitary and adjoint invariance of traces

Unitary invariance for traces `τ : B → ℝ≥0∞` (`TauCeti.IsTrace`) on a C⋆-algebra `B`:
`τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every unitary, or more generally every isometry, `u` of the
forced unitization `B^† = Unitization ℂ B`. The product `uxu⋆` lies in `B`, which is an ideal of
`B^†`; it is `z⋆z` for `z = x^{1/2}u⋆ ∈ B`, while `zz⋆ = x^{1/2}u⋆ux^{1/2} = x`, so the trace
identity gives `τ(uxu⋆) = τ(x)`.

The element `uxu⋆` of `B` is `Unitization.conjStar u x`, from
`TauCeti.Algebra.Algebra.Unitization`.

Adjoint invariance: `τ(f(x⋆x)) = τ(f(xx⋆))` for every `x ∈ B` and every real function `f`
nonnegative on the quasispectrum of `x⋆x` (Dixmier 1963, Lemme 3, p. 226). For continuous `f`
with `f(0) = 0`, write `f = h²` with `h = √f`; then `f(x⋆x) = y⋆y` and `f(xx⋆) = yy⋆` for some
`y ∈ B` (`exists_star_mul_self_eq_and_mul_star_self_eq`), and the trace identity applies.
Otherwise both sides are the trace of `0`.

## Main results

* `TauCeti.IsTrace.map_conjStar`: invariance under conjugation by isometries `u⋆u = 1` of `B^†`.
* `TauCeti.IsTrace.map_conjStar_of_mem_unitary`: unitary invariance.
* `TauCeti.IsTrace.map_cfcₙ_star_mul_self`: adjoint invariance, `τ(f(x⋆x)) = τ(f(xx⋆))`.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Lemme 3, p. 226.
-/

public section

open scoped ENNReal NNReal

variable {B : Type*} [NonUnitalCStarAlgebra B]

namespace TauCeti

variable [PartialOrder B] [StarOrderedRing B] {τ : B → ℝ≥0∞}

namespace IsTrace

/-- **Isometric invariance of traces**: `τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every isometry
`u⋆u = 1` of the forced unitization `B^†`. -/
theorem map_conjStar (hτ : IsTrace τ) {u : Unitization ℂ B} (hu : star u * u = 1) {x : B}
    (hx : 0 ≤ x) : τ (u.conjStar x) = τ x := by
  -- `z = x^{1/2} u⋆ ∈ B` has `z⋆z = uxu⋆` and `zz⋆ = x`.
  set s := CFC.sqrt x
  have hs : star s = s := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have hss : s * s = x := CFC.sqrt_mul_sqrt_self x hx
  set z : B := (star u).fst • s + s * (star u).snd
  have hz : (z : Unitization ℂ B) = (s : Unitization ℂ B) * star u :=
    (Unitization.inr_mul_eq_inr s (star u)).symm
  have hsu : star (s : Unitization ℂ B) = s := by rw [← Unitization.inr_star, hs]
  have h₁ : star z * z = u.conjStar x := Unitization.inr_injective (R := ℂ) <| by
    simp [hz, ← hss, hsu, mul_assoc]
  have h₂ : z * star z = x := Unitization.inr_injective (R := ℂ) <| by
    simp [hz, ← hss, hsu, mul_assoc, ← mul_assoc (star u), hu]
  rw [← h₁, hτ.map_star_mul_self, h₂]

/-- **Unitary invariance of traces**: `τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every unitary `u` of the
forced unitization `B^†`. -/
theorem map_conjStar_of_mem_unitary (hτ : IsTrace τ) {u : Unitization ℂ B}
    (hu : u ∈ unitary (Unitization ℂ B)) {x : B} (hx : 0 ≤ x) : τ (u.conjStar x) = τ x :=
  hτ.map_conjStar (Unitary.star_mul_self_of_mem hu) hx

/-- **Adjoint invariance of traces**: `τ(f(x⋆x)) = τ(f(xx⋆))` for every real function `f`
nonnegative on the quasispectrum of `x⋆x`; with `f(t) = t^{p/2}`, `τ(|x|^p) = τ(|x⋆|^p)`. -/
theorem map_cfcₙ_star_mul_self (hτ : IsTrace τ) (x : B) {f : ℝ → ℝ}
    (hf : ∀ t ∈ quasispectrum ℝ (star x * x), 0 ≤ f t) :
    τ (cfcₙ f (star x * x)) = τ (cfcₙ f (x * star x)) := by
  have hσ : quasispectrum ℝ (star x * x) = quasispectrum ℝ (x * star x) :=
    quasispectrum.mul_comm _ _
  by_cases hc : ContinuousOn f (quasispectrum ℝ (star x * x))
  swap
  · rw [cfcₙ_apply_of_not_continuousOn _ hc,
      cfcₙ_apply_of_not_continuousOn _ (hσ ▸ hc : ¬ ContinuousOn f _)]
  by_cases hf0 : f 0 = 0
  swap
  · rw [cfcₙ_apply_of_not_map_zero _ hf0, cfcₙ_apply_of_not_map_zero _ hf0]
  obtain ⟨y, hy₁, hy₂⟩ := exists_star_mul_self_eq_and_mul_star_self_eq x (fun t ↦ √(f t))
    (Real.continuous_sqrt.comp_continuousOn hc) (by simp [hf0])
  have h₁ : cfcₙ (fun t ↦ √(f t) * √(f t)) (star x * x) = cfcₙ f (star x * x) :=
    cfcₙ_congr fun t ht ↦ Real.mul_self_sqrt (hf t ht)
  have h₂ : cfcₙ (fun t ↦ √(f t) * √(f t)) (x * star x) = cfcₙ f (x * star x) :=
    cfcₙ_congr fun t ht ↦ Real.mul_self_sqrt (hf t (hσ ▸ ht))
  rw [← h₁, ← hy₁, hτ.map_star_mul_self, hy₂, h₂]

end IsTrace

end TauCeti
