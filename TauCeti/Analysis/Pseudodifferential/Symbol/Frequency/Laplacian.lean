/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# The shifted frequency Laplacian on symbols

For a symbol `a : Symbol n V W m` of order `m`, the frequency Laplacian `Δ_ξ = ∑ⱼ ∂²_{ξ_j}`
(`TauCeti.Symbol.frequencyLaplacian`) lowers the order to `m - 2`. Subtracting it from the identity
defines the shifted frequency Laplacian `1 - Δ_ξ` (`TauCeti.Symbol.oneSubFrequencyLaplacian`), an
order-preserving linear endomorphism of `Symbol n V W m`. Iterating `1 - Δ_ξ` trades against powers
`(1 + ‖x - y‖²) ^ (-N)` when integrating by parts in Kohn–Nirenberg quantization
(`TauCeti.Symbol.quantizeSchwartzValue_eq_iterate_oneSubFrequencyLaplacian`).

## Main declarations

* `TauCeti.Symbol.oneSubFrequencyLaplacian`: the linear operator `1 - Δ_ξ : Symbol n V W m →ₗ[ℂ]
  Symbol n V W m`.
* `TauCeti.Symbol.IsUniform.oneSubFrequencyLaplacian`,
  `TauCeti.Symbol.IsUniform.iterate_oneSubFrequencyLaplacian`,
  `TauCeti.Symbol.HasCompactSpatialSupport.oneSubFrequencyLaplacian`,
  `TauCeti.Symbol.HasCompactSpatialSupport.iterate_oneSubFrequencyLaplacian`: preservation of
  uniform symbol estimates and compact spatial support.
* `TauCeti.Symbol.spatialDeriv_iterate_oneSubFrequencyLaplacian`,
  `TauCeti.Symbol.frequencyDeriv_iterate_oneSubFrequencyLaplacian`: commutation with position and
  frequency derivatives.
* `TauCeti.Symbol.coefficient_iterate_oneSubFrequencyLaplacian_congr`: order independence of the
  iterated coefficient.
* `TauCeti.Symbol.frequencyLaplacian_const`, `TauCeti.Symbol.oneSubFrequencyLaplacian_const`,
  `TauCeti.Symbol.iterate_oneSubFrequencyLaplacian_const`: action on constant symbols.
-/

public section
noncomputable section

namespace TauCeti
namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The shifted frequency Laplacian `1 - Δ_ξ` on symbols of order `m`. -/
def oneSubFrequencyLaplacian : Symbol n V W m →ₗ[ℂ] Symbol n V W m :=
  LinearMap.id - inclusion (by linarith) ∘ₗ frequencyLaplacian (m := m)

@[simp]
theorem coefficient_oneSubFrequencyLaplacian (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (oneSubFrequencyLaplacian a).coefficient p =
      a.coefficient p - (frequencyLaplacian a).coefficient p := by
  simp [oneSubFrequencyLaplacian]

theorem IsUniform.oneSubFrequencyLaplacian {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.oneSubFrequencyLaplacian a).IsUniform :=
  ha.sub <| IsUniform.inclusion (by
    rw [frequencyLaplacian_eq_sum]
    exact IsUniform.sum fun j _ ↦ ((ha.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith))
    (by linarith)

theorem IsUniform.iterate_oneSubFrequencyLaplacian {a : Symbol n V W m} (ha : a.IsUniform) :
    ∀ N : ℕ, ((Symbol.oneSubFrequencyLaplacian (m := m))^[N] a).IsUniform
  | 0 => ha
  | N + 1 => ha.oneSubFrequencyLaplacian.iterate_oneSubFrequencyLaplacian N

theorem HasCompactSpatialSupport.oneSubFrequencyLaplacian {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) :
    (Symbol.oneSubFrequencyLaplacian a).HasCompactSpatialSupport :=
  ha.sub <| HasCompactSpatialSupport.inclusion (by
    rw [frequencyLaplacian_eq_sum]
    exact Finset.sum_induction _ HasCompactSpatialSupport (fun _ _ ↦ .add)
      hasCompactSpatialSupport_zero fun j _ ↦
        ((ha.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)) (by linarith)

theorem HasCompactSpatialSupport.iterate_oneSubFrequencyLaplacian {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) :
    ∀ N : ℕ, ((Symbol.oneSubFrequencyLaplacian (m := m))^[N] a).HasCompactSpatialSupport
  | 0 => ha
  | N + 1 => ha.oneSubFrequencyLaplacian.iterate_oneSubFrequencyLaplacian N

theorem spatialDeriv_oneSubFrequencyLaplacian (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j (oneSubFrequencyLaplacian a) = oneSubFrequencyLaplacian (spatialDeriv j a) := by
  simp [oneSubFrequencyLaplacian, frequencyLaplacian_eq_sum, spatialDeriv_frequencyDeriv_comm]

theorem spatialDeriv_iterate_oneSubFrequencyLaplacian (N : ℕ) (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j ((oneSubFrequencyLaplacian (m := m))^[N] a) =
      (oneSubFrequencyLaplacian (m := m))^[N] (spatialDeriv j a) :=
  Function.Semiconj.iterate_right (spatialDeriv_oneSubFrequencyLaplacian j) N a

theorem frequencyDeriv_oneSubFrequencyLaplacian (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j (oneSubFrequencyLaplacian a) =
      oneSubFrequencyLaplacian (frequencyDeriv j a) := by
  simp only [oneSubFrequencyLaplacian, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
    LinearMap.comp_apply, map_sub, frequencyDeriv_inclusion, frequencyLaplacian_eq_sum, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ by
    rw [frequencyDeriv_comm j l, frequencyDeriv_comm j l]
    ext1
    simp

theorem frequencyDeriv_iterate_oneSubFrequencyLaplacian (N : ℕ) (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j ((oneSubFrequencyLaplacian (m := m))^[N] a) =
      (oneSubFrequencyLaplacian (m := m - 1))^[N] (frequencyDeriv j a) :=
  Function.Semiconj.iterate_right (frequencyDeriv_oneSubFrequencyLaplacian j) N a

/-- The coefficient of `(1 - Δ_ξ) ^ N a` depends only on the coefficient of `a`, not its order. -/
theorem coefficient_iterate_oneSubFrequencyLaplacian_congr {m₁ m₂ : ℝ} {a₁ : Symbol n V W m₁}
    {a₂ : Symbol n V W m₂} (h : a₁.coefficient = a₂.coefficient) :
    ∀ N : ℕ, ((oneSubFrequencyLaplacian (m := m₁))^[N] a₁).coefficient =
      ((oneSubFrequencyLaplacian (m := m₂))^[N] a₂).coefficient
  | 0 => h
  | N + 1 => coefficient_iterate_oneSubFrequencyLaplacian_congr
      (funext fun ⟨x, ξ⟩ ↦ by simp [h]) N

@[simp]
theorem frequencyLaplacian_const (T : V →L[ℂ] W) :
    frequencyLaplacian (const T : Symbol n V W 0) = 0 := by
  ext ⟨x, ξ⟩ : 2
  rw [coefficient_frequencyLaplacian, coefficient_zero, Pi.zero_apply]
  exact Finset.sum_eq_zero fun j _ ↦ by
    simp [coordinateDeriv_const _ (by simp : ([j] : List (Fin n)) ≠ [])]

@[simp]
theorem oneSubFrequencyLaplacian_const (T : V →L[ℂ] W) :
    oneSubFrequencyLaplacian (const T : Symbol n V W 0) = const T := by
  simp [oneSubFrequencyLaplacian]

@[simp]
theorem iterate_oneSubFrequencyLaplacian_const (T : V →L[ℂ] W) (N : ℕ) :
    (oneSubFrequencyLaplacian (m := 0))^[N] (const T : Symbol n V W 0) = const T :=
  Function.IsFixedPt.iterate (oneSubFrequencyLaplacian_const T) N

end Symbol
end TauCeti
