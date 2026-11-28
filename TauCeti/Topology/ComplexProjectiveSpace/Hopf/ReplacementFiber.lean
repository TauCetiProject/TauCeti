/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Basic
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# The fibre of the Moore-path replacement of the Hopf fibration

Let `F'` be the fibre over `[v] ∈ CPⁿ` of the Moore-path replacement of the Hopf fibration
`S²ⁿ⁺¹ → CPⁿ` (`TauCeti.MooreReplacement.Fiber`): the pairs of a point `x` of the sphere and a
Moore path in `CPⁿ` from `[x]` to `[v]`. The Moore loops of `CPⁿ` at `[v]` act on `F'` strictly, by
concatenation, and the cubical chains on `F'` with this action are the DG local system of the
Hopf fibration (`TauCeti.fibrationLocalSystem`).

The Hopf fibration is a Hurewicz fibration
(`TauCeti.ComplexProjectiveSpace.isHurewiczFibration_mk`), so its fibre over `[v]` is homotopy
equivalent to `F'` through `x ↦ (x, const)` (`TauCeti.MooreReplacement.fiberHomotopyEquivFiber`),
and that fibre is the unit circle through the orbit map `u ↦ u • v`
(`TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`). Hence `F'` is homotopy equivalent to the
unit circle, by `u ↦ (u • v, const)`
(`TauCeti.ComplexProjectiveSpace.hopfReplacementFiberHomotopyEquiv`). Through
`ContinuousMap.HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv`, the cubical chains on
`F'`, which carry the DG local system of the Hopf fibration, are therefore homotopy equivalent to
the cubical chains of the circle.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfReplacementFiberHomotopyEquiv`: the homotopy equivalence
  from the unit circle to the fibre of the Moore-path replacement of the Hopf fibration.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  §4.2, Example 4.45.
-/

public section

noncomputable section

open Metric

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- **The fibre of the Moore-path replacement of the Hopf fibration is a circle up to homotopy**:
the map `u ↦ (u • v, const)` from the unit circle to the fibre over `[v]` of the Moore-path
replacement of `S²ⁿ⁺¹ → CPⁿ` is a homotopy equivalence. -/
def hopfReplacementFiberHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (sphere (0 : ℂ) 1)
      (MooreReplacement.Fiber ⟨mk n, continuous_mk n⟩ (mk n v)) :=
  -- The fibre `mk n ⁻¹' {mk n v}` of `hopfFiberHomeomorph` is read as the subtype
  -- `{x // mk n x = mk n v}` of `fiberHomotopyEquivFiber`.
  ((hopfFiberHomeomorph v).trans
      ((Homeomorph.refl _).subtype fun _ ↦ by simp)).toHomotopyEquiv.trans
    (MooreReplacement.fiberHomotopyEquivFiber (p := ⟨mk n, continuous_mk n⟩)
      (isHurewiczFibration_mk n) (mk n v))

/-- The homotopy equivalence sends `u` to the point `u • v` with the constant path at `[v]`. -/
@[simp]
theorem val_hopfReplacementFiberHomotopyEquiv_apply (u : sphere (0 : ℂ) 1) :
    (hopfReplacementFiberHomotopyEquiv v u).val =
      MooreReplacement.incl ⟨mk n, continuous_mk n⟩ (u • v) := by
  rw [hopfReplacementFiberHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans_apply,
    Homeomorph.coe_toHomotopyEquiv, MooreReplacement.val_fiberHomotopyEquivFiber_apply]
  simp

end TauCeti.ComplexProjectiveSpace
