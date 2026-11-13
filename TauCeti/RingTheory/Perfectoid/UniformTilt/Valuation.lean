/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# Continuous valuations on the tilt via the sharp map

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent. Any
continuous valuation `v` on `B` pulls back along the multiplicative sharp map `♯ : B♭ → B`
(`x ↦ x⁽⁰⁾`) to a continuous valuation `v ∘ ♯` on `B♭`. Although `♯` is not additive, the limit
formula `(a + b)♯ = lim_m (a⁽ᵐ⁾ + b⁽ᵐ⁾)^{p^m}` together with local constancy of `v` off its
support (`Valuation.IsContinuous.eventually_eq`) yields the ultrametric inequality
`v((a + b)♯) ≤ max (v(a♯)) (v(b♯))`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.sharpValuation`: pullback of a continuous valuation on `B` along
  `♯ : uniformTilt p B → B`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.sharpValuation_apply`: evaluation formula
  `sharpValuation v hv a = v (coeff p B 0 a)`.
* `TauCeti.Perfectoid.uniformTilt.sharpValuation_isContinuous`: `sharpValuation v hv` is
  continuous.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §6, proof of Theorem 6.3.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, Arizona
  Winter School 2017, Lemma 2.6.12.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- Pulling back a continuous valuation `v` on `B` along the sharp map `♯ : uniformTilt p B → B`
yields a valuation on `uniformTilt p B`. -/
noncomputable def sharpValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) : Valuation (uniformTilt p B) Γ₀ where
  toFun a := v (coeff p B 0 a)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by simp
  map_add_le_max' a b := by
    rcases eq_or_ne (v (coeff p B 0 (a + b))) 0 with hz | hne
    · simp [hz]
    · obtain ⟨m, hm⟩ := ((coeff_add a b 0).eventually (hv.eventually_eq hne)).exists
      have ha : v (coeff p B m a) ^ p ^ m = v (coeff p B 0 a) := by
        simpa only [← map_pow, zero_add] using congrArg v (coeff_pow_p_pow a 0 m)
      have hb : v (coeff p B m b) ^ p ^ m = v (coeff p B 0 b) := by
        simpa only [← map_pow, zero_add] using congrArg v (coeff_pow_p_pow b 0 m)
      calc
        v (coeff p B 0 (a + b)) = v ((coeff p B m a + coeff p B m b) ^ p ^ m) := by
          simpa only [zero_add] using hm.symm
        _ = v (coeff p B m a + coeff p B m b) ^ p ^ m := map_pow _ _ _
        _ ≤ max (v (coeff p B m a)) (v (coeff p B m b)) ^ p ^ m :=
          pow_le_pow_left' (v.map_add _ _) (p ^ m)
        _ = max (v (coeff p B 0 a)) (v (coeff p B 0 b)) := by rw [max_pow, ha, hb]

/-- Evaluating `sharpValuation v hv` at `a` applies `v` to the zeroth coordinate `a♯`. -/
@[simp]
theorem sharpValuation_apply {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) (a : uniformTilt p B) :
    sharpValuation (p := p) v hv a = v (coeff p B 0 a) :=
  (rfl)

/-- The pullback of a continuous valuation `v` on `B` along `♯ : uniformTilt p B → B` is
continuous on `uniformTilt p B`. -/
theorem sharpValuation_isContinuous {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) :
    (sharpValuation (p := p) v hv).IsContinuous := by
  rw [Valuation.isContinuous_def]
  intro b
  exact ((Valuation.isContinuous_def.mp hv) (coeff p B 0 b)).preimage (continuous_coeff 0)

end TauCeti.Perfectoid.uniformTilt
