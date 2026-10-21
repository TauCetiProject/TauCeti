/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.QuaternionicStructure
public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticEnd

/-!
# Charge conjugation of the Seiberg–Witten quadratic map

Charge conjugation sends a Seiberg–Witten configuration `(A, ψ)` on a `Spinᶜ` structure to the
configuration `(conj A, j ψ)` on the conjugate `Spinᶜ` structure, where `j` is the quaternionic
structure of the half-spinors: a conjugate-linear isometry with `j (j ψ) = -ψ`
(`TauCeti.stdQuaternionicStructure` on `ℂ²`). Conjugation negates the imaginary curvature form
`F_A`. The curvature equation `F_A⁺ = Q₀(ψ) + η` is therefore carried to the curvature equation
with forcing `-η`, because the quadratic map changes sign:

`Q₀(j ψ) = -Q₀(ψ)`, where `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id`.

This file proves that sign change and its consequences for the polarization and derivative of
`Q₀`, pointwise on a complex inner product space `E` of complex dimension two. The proof uses the
decomposition `ψψ* + (j ψ)(j ψ)* = ‖ψ‖² Id`
(`LinearIsometry.rankOne_self_add_rankOne_map_self`).

Any conjugate-linear isometry `j : E → F` intertwines `Q₀(ψ)` with `Q₀(j ψ)`; with the sign
change, a quaternionic structure anticommutes with every `Q₀(ψ)`.

## Main results

* `TauCeti.SeibergWitten.map_quadraticEnd_apply`: `j (Q₀(ψ) v) = Q₀(j ψ) (j v)` for every
  conjugate-linear isometry `j`.
* `TauCeti.SeibergWitten.quadraticEnd_map`: `Q₀(j ψ) = -Q₀(ψ)` in complex dimension two.
* `TauCeti.SeibergWitten.quadraticEndPolar_map_map`: the polarization, which is also the
  derivative of `Q₀`, satisfies `B(j ψ, j φ) = -B(ψ, φ)`.
* `TauCeti.SeibergWitten.map_quadraticEnd_apply_eq_neg`: `j` anticommutes with `Q₀(ψ)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

/-- A conjugate-linear isometry `j` intertwines `Q₀(ψ)` with `Q₀(j ψ)`:
`j (Q₀(ψ) v) = Q₀(j ψ) (j v)`. -/
theorem map_quadraticEnd_apply (j : E →ₗᵢ⋆[ℂ] F) (ψ v : E) :
    j (quadraticEnd ψ v) = quadraticEnd (j ψ) (j v) := by
  simp only [quadraticEnd_apply, map_sub, map_smulₛₗ, j.inner_map_map_eq_conj, j.norm_map,
    map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]

/-- A conjugate-linear isometry `j` intertwines `B(ψ, φ)` with `B(j ψ, j φ)`:
`j (B(ψ, φ) v) = B(j ψ, j φ) (j v)`. -/
theorem map_quadraticEndPolar_apply (j : E →ₗᵢ⋆[ℂ] F) (ψ φ v : E) :
    j (quadraticEndPolar ψ φ v) = quadraticEndPolar (j ψ) (j φ) (j v) := by
  simp only [quadraticEndPolar_apply_apply, map_sub, map_add, map_smulₛₗ,
    j.inner_map_map_eq_conj, Complex.conj_ofReal, Complex.conj_re]

variable {j : E →ₗᵢ⋆[ℂ] E}

/-- **Charge conjugation reverses the quadratic map**: for a quaternionic structure `j` in complex
dimension two, `Q₀(j ψ) = -Q₀(ψ)`. -/
theorem quadraticEnd_map (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    quadraticEnd (j ψ) = -quadraticEnd ψ := by
  have h := j.rankOne_self_add_rankOne_map_self hj h₂ ψ
  rw [quadraticEnd_def, quadraticEnd_def, j.norm_map, eq_sub_of_add_eq' h]
  module

/-- For a quaternionic structure `j` in complex dimension two, the polarization of `Q₀` satisfies
`B(j ψ, j φ) = -B(ψ, φ)`. Since `B(ψ, ·)` is the derivative of `Q₀` at `ψ`, charge conjugation
also reverses the linearized curvature equation. -/
theorem quadraticEndPolar_map_map (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2)
    (ψ φ : E) : quadraticEndPolar (j ψ) (j φ) = -quadraticEndPolar ψ φ := by
  have h := quadraticEnd_add (j ψ) (j φ)
  rw [← map_add, quadraticEnd_map hj h₂, quadraticEnd_map hj h₂, quadraticEnd_map hj h₂,
    quadraticEnd_add] at h
  linear_combination (norm := module) -h

/-- In complex dimension two a quaternionic structure `j` anticommutes with every `Q₀(ψ)`:
`j (Q₀(ψ) v) = -Q₀(ψ) (j v)`. -/
theorem map_quadraticEnd_apply_eq_neg (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2)
    (ψ v : E) : j (quadraticEnd ψ v) = -quadraticEnd ψ (j v) := by
  rw [map_quadraticEnd_apply, quadraticEnd_map hj h₂, neg_apply]

end TauCeti.SeibergWitten
