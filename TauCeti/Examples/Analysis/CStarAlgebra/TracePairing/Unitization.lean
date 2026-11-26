/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Unitization
public import TauCeti.Examples.Analysis.CStarAlgebra.TracePairing.Basic

/-!
# Checks for the trace pairing with the nonunital `K₀`-group

Take `A = ℂ`, regarded as a nonunital C⋆-algebra, with the identity functional `τ = id`, and its
unitization `ℂ⁺`. The projection `e = inr 1` has scalar part `0`, so `[e]` lies in `K₀(A)` and
pairs to `τ(1) = 1`. The projection `1 − e` has scalar part `1`, so `[1 − e] − [1]` lies in
`K₀(A)` and pairs to `τ(−1) = −1`: the scalar part of `1 − e` is removed by the correction `−[1]`,
and omitting it would give `τ⁺(1 − e) = 0` instead.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.UnitizationTracePairingExample

open TracePairingExample

/-- The `1 × 1` matrix `inr 1` over `ℂ⁺`. -/
noncomputable abbrev e : Matrix (Fin 1) (Fin 1) (Unitization ℂ ℂ) :=
  (1 : Matrix (Fin 1) (Fin 1) ℂ).map (Unitization.inrNonUnitalStarAlgHom ℂ ℂ)

theorem isStarProjection_e : IsStarProjection e :=
  (IsStarProjection.one _).matrix_map
    (NonUnitalStarRingHom.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ ℂ))

theorem map_fst_e : e.map (fun x ↦ x.fst) = 0 :=
  Matrix.ext fun i j ↦ by simp

theorem map_fst_one_sub_e : (1 - e).map (fun x ↦ x.fst) = 1 :=
  Matrix.ext fun i j ↦ by fin_cases i; fin_cases j; simp

/-- The class `[inr 1]` of `K₀(ℂ)` pairs to `1`. -/
theorem unitizationKZeroPairing_e :
    idTrace.unitizationKZeroPairing
        ⟨_, UnitizationKZero.of_mk_sub_inl_of_mk_mem isStarProjection_e (.zero _) map_fst_e⟩ =
      1 := by
  rw [PositiveTracialFunctional.unitizationKZeroPairing_of_mk_sub_inl_of_mk]
  simp

/-- The class `[1 − inr 1] − [1]` of `K₀(ℂ)` pairs to `−1`. -/
theorem unitizationKZeroPairing_one_sub_e :
    idTrace.unitizationKZeroPairing
        ⟨_, UnitizationKZero.of_mk_sub_inl_of_mk_mem isStarProjection_e.one_sub (.one _)
          map_fst_one_sub_e⟩ =
      -1 := by
  rw [PositiveTracialFunctional.unitizationKZeroPairing_of_mk_sub_inl_of_mk]
  simp

end TauCeti.UnitizationTracePairingExample
