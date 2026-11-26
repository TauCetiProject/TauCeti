/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.CoordinateAction.Loop
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.PoleBounded.Basic
import TauCeti.RingTheory.LaurentSeries.Substitution.Lattice

/-!
# Coordinate changes preserve pole-bounded loops

Let `H` be a Hopf algebra over a commutative semiring `k`, `R` a commutative `k`-algebra, and fix
a family `x : ι → H`. Substitution of a formal coordinate preserves every lattice
`X^(-N) R⟦X⟧` of Laurent series, so the action `ρ_φ (g) = σ_(φ⁻¹) ∘ g` of formal coordinate
changes on the convolution points `WithConv (H →ₐ[k] R⸨X⸩)` maps the set
`TauCeti.HopfAlgebra.poleBoundedLoops k x R N` of loops pole-bounded of level `N` for `x` onto
itself, for every family `x` and every `N`. When `k` is a commutative ring, `H` is a commutative
Hopf algebra and `x` is a finite generating family, these sets are the pieces `LG_(≤N)(R)` of the
ind-affine presentation of the loop group of `G = Spec H`.

As for the action on loops, `R⸨X⸩` carries its coefficientwise `k`-algebra structure
`HahnSeries.instAlgebra`, selected with `attribute [local instance 1100] HahnSeries.instAlgebra`.

## Main results

* `TauCeti.LaurentSeries.smul_mem_poleBoundedLoops_iff`: a loop is pole-bounded of level `N` for
  `x` exactly when its image under a coordinate change is.
* `TauCeti.LaurentSeries.smul_poleBoundedLoops`: each coordinate change maps the pole-bounded
  loops of level `N` for `x` onto themselves.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge University Press (2007),
  §1.3.1 for the loop group, §§3.5.3–3.5.4 for the group of coordinate changes.
-/

public section

open HahnSeries WithConv
open scoped Pointwise LaurentSeries

-- The coefficientwise `k`-algebra structure on Laurent series, as in `CommAlgCat.laurentSeries`.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.LaurentSeries

variable {k H R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]
  [Semiring H] [HopfAlgebra k H] {ι : Type*} (x : ι → H)

/-- A loop is pole-bounded of level `N` for the family `x` exactly when its image under a
coordinate change is. -/
@[simp]
theorem smul_mem_poleBoundedLoops_iff {N : ℕ} (φ : FormalCoordinate R)
    {g : WithConv (H →ₐ[k] R⸨X⸩)} :
    φ • g ∈ HopfAlgebra.poleBoundedLoops k x R N ↔ g ∈ HopfAlgebra.poleBoundedLoops k x R N := by
  simp only [HopfAlgebra.mem_poleBoundedLoops_iff_antipode, ofConv_smul_apply,
    substAlgEquiv_mem_lattice_iff]

/-- Each coordinate change maps the set of loops pole-bounded of level `N` for the family `x`
onto itself. When `k` is a commutative ring, `H` is a commutative Hopf algebra and `x` is a finite
generating family, this set is the piece `LG_(≤N)(R)` of the ind-affine presentation of the loop
group of `G = Spec H`. -/
@[simp]
theorem smul_poleBoundedLoops (N : ℕ) (φ : FormalCoordinate R) :
    φ • HopfAlgebra.poleBoundedLoops k x R N = HopfAlgebra.poleBoundedLoops k x R N := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_mem_poleBoundedLoops_iff]

end TauCeti.LaurentSeries
