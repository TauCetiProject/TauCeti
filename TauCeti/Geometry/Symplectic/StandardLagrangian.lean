/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Geometry.Symplectic.Lagrangian
import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# Lagrangian coordinate factors of the standard symplectic model

On the standard model `V × V` of a real inner product space `V`, equipped with the standard
symplectic form `TauCeti.stdSymplecticForm`, the two coordinate factors `V × {0}` and `{0} × V`
are Lagrangian. These are the standard-model witnesses that the generic Lagrangian vocabulary of
`TauCeti.Geometry.Symplectic.Lagrangian` is inhabited; they also pair with the maximal totally
real statements `TauCeti.Submodule.isMaximalTotallyReal_prod_top_bot_product` and
`TauCeti.Submodule.isMaximalTotallyReal_prod_bot_top_product`, exhibiting the coordinate factors as
simultaneously maximal totally real and Lagrangian.

The positive-definiteness of the inner product enters through `inner_self_eq_zero`: a vector
orthogonal to itself for `ω₀` along its own factor vanishes.

## Main declarations

* `TauCeti.SymplecticForm.stdSymplecticForm_isLagrangian_prod_top_bot`: the first coordinate factor
  `V × {0}` is Lagrangian for `stdSymplecticForm`.
* `TauCeti.SymplecticForm.stdSymplecticForm_isLagrangian_prod_bot_top`: the second coordinate factor
  `{0} × V` is Lagrangian for `stdSymplecticForm`.
-/

namespace TauCeti

namespace SymplecticForm

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The first coordinate factor `V × {0}` is Lagrangian for the standard symplectic form. -/
lemma stdSymplecticForm_isLagrangian_prod_top_bot :
    (stdSymplecticForm (V := V)).IsLagrangian ((⊤ : Submodule ℝ V).prod ⊥) := by
  refine Submodule.ext fun x => ?_
  rw [mem_orthogonal_iff, Submodule.mem_prod]
  refine ⟨fun h => ⟨trivial, ?_⟩, fun h y hy => ?_⟩
  · rw [Submodule.mem_bot]
    have hh := h (x.2, 0) (Submodule.mem_prod.2 ⟨trivial, Submodule.zero_mem _⟩)
    rw [stdSymplecticForm_apply] at hh
    have hx : ⟪x.2, x.2⟫_ℝ = 0 := by simpa using hh
    exact inner_self_eq_zero.1 hx
  · have hy2 : y.2 = 0 := (Submodule.mem_bot ℝ).1 (Submodule.mem_prod.1 hy).2
    have hx2 : x.2 = 0 := (Submodule.mem_bot ℝ).1 h.2
    simp [hy2, hx2]

/-- The second coordinate factor `{0} × V` is Lagrangian for the standard symplectic form. -/
lemma stdSymplecticForm_isLagrangian_prod_bot_top :
    (stdSymplecticForm (V := V)).IsLagrangian ((⊥ : Submodule ℝ V).prod ⊤) := by
  refine Submodule.ext fun x => ?_
  rw [mem_orthogonal_iff, Submodule.mem_prod]
  refine ⟨fun h => ⟨?_, trivial⟩, fun h y hy => ?_⟩
  · rw [Submodule.mem_bot]
    have hh := h (0, x.1) (Submodule.mem_prod.2 ⟨Submodule.zero_mem _, trivial⟩)
    rw [stdSymplecticForm_apply] at hh
    have hx : ⟪x.1, x.1⟫_ℝ = 0 := by simpa using hh
    exact inner_self_eq_zero.1 hx
  · have hy1 : y.1 = 0 := (Submodule.mem_bot ℝ).1 (Submodule.mem_prod.1 hy).1
    have hx1 : x.1 = 0 := (Submodule.mem_bot ℝ).1 h.1
    simp [hy1, hx1]

end SymplecticForm

end TauCeti
