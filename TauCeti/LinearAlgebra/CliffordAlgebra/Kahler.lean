/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The Clifford action of the Kähler form in dimension four

Let `J` be an orthogonal complex structure on a real inner product space `V` of dimension four,
with a unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, and Kähler two-vector
`ω = e₀ ∧ e₁ + e₂ ∧ e₃` (`TauCeti.AlmostComplexStructure.kahlerForm`). For the quadratic form
`Q v = -‖v‖²`, Clifford multiplication by two-forms `c₂ = CliffordAlgebra.bivectorExterior Q`
sends `ω` to `c(e₀) c(e₁) + c(e₂) c(e₃)`, where `c = CliffordAlgebra.ι Q`.

The commutator of `c₂(ω)` with a generator is the Clifford image of `J`:
`⁅c₂(ω), c(v)⁆ = 2 c(J v)`. On a Clifford module this is how the eigenspaces of `c₂(ω)` see `J`.
For instance, on Taubes's canonical line, the `-2i`-eigenline of `c₂(ω)` in the positive
half-spinors, `v ↦ c(v) u` turns `J` into multiplication by `i`
(`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`).

## Main results

* `TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm`:
  `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` in a unitary frame.
* `TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm_lie_ι`:
  `⁅c₂(ω), c(v)⁆ = 2 c(J v)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

omit [FiniteDimensional ℝ V] in
include h₀ h₂ in
/-- `J v` in a unitary frame: `J` rotates each of the planes `⟨e₀, e₁⟩` and `⟨e₂, e₃⟩` by a
right angle. -/
private theorem apply_eq_inner_smul (v : V) :
    J v = ⟪e 0, v⟫ • e 1 - ⟪e 1, v⟫ • e 0 + ⟪e 2, v⟫ • e 3 - ⟪e 3, v⟫ • e 2 := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have hv : J v = ∑ i, ⟪e i, v⟫ • J (e i) := by
    conv_lhs => rw [← e.sum_repr' v]
    simp [map_sum, map_smul]
  rw [hv, Fin.sum_univ_four, h₀, h₁, h₂, h₃]
  module

include hQ h₀ h₂ in
/-- **The Clifford image of the Kähler form** in a unitary frame:
`c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)`. -/
theorem bivectorExterior_kahlerForm :
    bivectorExterior Q J.kahlerForm = ι Q (e 0) * ι Q (e 1) + ι Q (e 2) * ι Q (e 3) := by
  have hortho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (e i) (e j) :=
    (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (e.orthonormal.2 hij)
  rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, bivectorExterior_apply_ιMulti,
    bivectorExterior_apply_ιMulti, bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide))]

include hQ h₀ h₂ in
/-- **The Kähler form generates `J` in the Clifford algebra**: `⁅c₂(ω), c(v)⁆ = 2 c(J v)`. -/
theorem bivectorExterior_kahlerForm_lie_ι (v : V) :
    ⁅bivectorExterior Q J.kahlerForm, ι Q v⁆ = ι Q ((2 : ℝ) • J v) := by
  have hpolar (x y : V) : QuadraticMap.polar Q x y = -2 * ⟪x, y⟫ := by
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  rw [bivectorExterior_kahlerForm hQ h₀ h₂, Ring.lie_def, add_mul, mul_add, add_sub_add_comm,
    ← Ring.lie_def, ← Ring.lie_def, ι_mul_ι_lie_ι, ι_mul_ι_lie_ι, ← map_add,
    apply_eq_inner_smul h₀ h₂ v]
  congr 1
  simp only [hpolar]
  module

end TauCeti.AlmostComplexStructure
