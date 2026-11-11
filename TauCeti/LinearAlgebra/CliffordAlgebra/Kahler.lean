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
# The Clifford action of the Kähler form

Let `J` be an orthogonal complex structure on a finite-dimensional real inner product space `V`,
with Kähler two-vector `ω` (`TauCeti.AlmostComplexStructure.kahlerForm`). For the quadratic form
`Q v = -‖v‖²`, write `c = CliffordAlgebra.ι Q` and `c₂ = CliffordAlgebra.bivectorExterior Q` for
Clifford multiplication by vectors and by two-forms.

The commutator of `c₂(ω)` with a generator is the Clifford image of `J`:
`⁅c₂(ω), c(v)⁆ = 2 c(J v)`. On a Clifford module this is how the eigenspaces of `c₂(ω)` see `J`.
For instance, on Taubes's canonical line, the `-2i`-eigenline of `c₂(ω)` in the positive
half-spinors of a four-dimensional spin module, `v ↦ c(v) u` turns `J` into multiplication by `i`
(`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`).

In dimension four, with a unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, the
Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`, and `c₂` sends it to `c(e₀) c(e₁) + c(e₂) c(e₃)`.

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
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) {J : AlmostComplexStructure V}

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

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

end Frame

include hQ in
/-- **The Kähler form generates `J` in the Clifford algebra**: for an orthogonal `J`,
`⁅c₂(ω), c(v)⁆ = 2 c(J v)`. -/
theorem bivectorExterior_kahlerForm_lie_ι (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (v : V) :
    ⁅bivectorExterior Q J.kahlerForm, ι Q v⁆ = ι Q ((2 : ℝ) • J v) := by
  have hpolar (x y : V) : QuadraticMap.polar Q x y = -2 * ⟪x, y⟫ := by
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  rw [kahlerForm_def, map_smul, map_sum, Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [← Ring.lie_def, bivectorExterior_apply_ιMulti, bivector_lie_ι, ← map_sum]
  set b := stdOrthonormalBasis ℝ V
  -- Expanding `ω = (1 / 2) ∑ᵢ bᵢ ∧ J bᵢ`, each `bᵢ ∧ J bᵢ` rotates `v` within `⟨bᵢ, J bᵢ⟩`.
  have hsum : ∑ i, (QuadraticMap.polar Q (J (b i)) v • b i - QuadraticMap.polar Q (b i) v • J (b i))
      = (4 : ℝ) • J v := by
    have hJv : ∑ i, ⟪b i, J v⟫ • b i = J v := b.sum_repr' (J v)
    have hv : ∑ i, ⟪b i, v⟫ • J (b i) = J v := by
      conv_rhs => rw [← b.sum_repr' v]
      simp [map_sum, map_smul]
    calc _ = ∑ i, ((2 : ℝ) • (⟪b i, J v⟫ • b i) + (2 : ℝ) • (⟪b i, v⟫ • J (b i))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hpolar, hpolar, inner_apply_left hJ]
          module
      _ = (4 : ℝ) • J v := by
          rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hJv, hv]
          module
  rw [hsum, ← map_smul, smul_smul]
  norm_num

end TauCeti.AlmostComplexStructure
