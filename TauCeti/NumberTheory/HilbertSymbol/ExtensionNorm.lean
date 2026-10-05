/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.RingTheory.Norm.Units

import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.Algebra.QuadraticAlgebra.NormTrace

/-!
# Norms from an algebra containing a square root

Let `F` be a field in which `2` is invertible, `b ∈ Fˣ`, and `M` a commutative `F`-algebra in
which the image of `b` is a square. Then every norm `N_{M/F}(c)` of a unit `c` of `M` is a norm
from the quadratic algebra `F[√b]`, so the norm-equation Hilbert symbol `(b, N_{M/F}(c))` is `1`.
The invertibility of `2` is used only when `b` is already a square in `F`: in characteristic two
the symbol `(1, c)` is `1` only for squares `c`.

When `b` is a square in `F` the symbol is `1` outright. Otherwise `F[√b]` is the field `F(√b)`, and
a square root `s` of `b` in `M` makes `M` an algebra over it by `√b ↦ s`; transitivity of the norm
in the tower `F ⊆ F(√b) → M` writes `N_{M/F}(c)` as the norm from `F(√b)` of `N_{M/F(√b)}(c)`.
No finiteness of `M` over `F` is needed, since the norm of an algebra that is not module-finite is
`1`.

Applied to the completions `L_w ⊇ K_v` of a number field `L` in which `b ∈ Kˣ` is a square, it
shows that every factor `N_{L_w/K_v}(c_w)` of a coordinate of an idele norm from `L` is a norm from
`K_v(√b)`. This is how the norm-equation Hilbert symbol sees the idele norm group `N_{L/K}(𝕀_L)`.

## Main results

* `TauCeti.hilbertSymbol_normUnits_eq_one`: if `b` is a square in `M`, then
  `(b, N_{M/F}(c)) = 1` for every unit `c` of `M`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19a.
-/

public section

namespace TauCeti

variable {F M : Type*} [Field F] [Invertible (2 : F)] [CommRing M] [Algebra F M]

/-- **Norms from an algebra containing `√b` are norms from `F(√b)`.** If the image of `b ∈ Fˣ` in
the commutative `F`-algebra `M` is a square, then the Hilbert symbol `(b, N_{M/F}(c))` is `1` for
every unit `c` of `M`. -/
@[simp]
theorem hilbertSymbol_normUnits_eq_one {b : Fˣ} (hb : IsSquare (algebraMap F M b)) (c : Mˣ) :
    hilbertSymbol b (Algebra.normUnits F c) = 1 := by
  by_cases hbF : IsSquare b
  · exact hilbertSymbol_eq_one_of_isSquare_left hbF _
  obtain ⟨s, hs⟩ := hb
  have : Fact (¬IsSquare (b : F)) := ⟨by rwa [isSquare_units_val_iff]⟩
  -- The quadratic algebra `F[√b]` is the field `F(√b)`, and `√b ↦ s` makes `M` an algebra over it.
  let φ : QuadraticAlgebra F (b : F) 0 →ₐ[F] M :=
    QuadraticAlgebra.lift ⟨s, by rw [← hs, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  let : Algebra (QuadraticAlgebra F (b : F) 0) M := φ.toAlgebra
  have : IsScalarTower F (QuadraticAlgebra F (b : F) 0) M :=
    .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  rw [hilbertSymbol_eq_one_iff_exists_norm_eq]
  refine ⟨Algebra.norm (QuadraticAlgebra F (b : F) 0) (c : M), ?_⟩
  rw [← QuadraticAlgebra.algebraNorm_eq_norm, Algebra.norm_norm, Algebra.coe_normUnits]

end TauCeti
