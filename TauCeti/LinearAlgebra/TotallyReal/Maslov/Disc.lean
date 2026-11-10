/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Map
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Prod

/-!
# The boundary Maslov index on the disc

Let `E` be a finite-dimensional complex normed space. A bundle pair `(E, F)` over the closed unit
disc `D` is a complex vector bundle over `D` together with a maximal totally real subbundle `F`
of its restriction to the boundary circle, that is, a totally real subbundle whose real rank is
the complex rank of the bundle. Every complex bundle over `D` is trivial, and in a
trivialization `D × E` the subbundle `F` is a loop `Λ` of maximal totally real subspaces of `E`
(`TauCeti.TotallyRealLoop`), parametrized by `t ↦ e^{2πit}`. The boundary Maslov index `μ(E, F)`
is the Maslov index `μ(Λ)` of that loop (McDuff--Salamon, Theorem C.3.6). This file proves the
properties that make this a well-defined invariant with the expected axioms on the disc.

* **Independence of the trivialization.** Two trivializations differ by a continuous map
  `B : D → GL(E)`, and the loop read in the second trivialization is `t ↦ B (e^{2πit}) (Λ t)`. Its
  Maslov index is `μ(Λ)` (`TauCeti.TotallyRealLoop.maslovIndex_map_of_continuousOn_closedBall`):
  by the product formula `μ(B Λ) = μ(Λ) + 2 deg (det B)` (`TauCeti.TotallyRealLoop.maslovIndex_map`)
  it suffices that the loop of normalized determinants of `B` along the boundary has degree zero,
  and it is null-homotopic through the loops `t ↦ det B (s e^{2πit})`, `s ∈ [0, 1]`. The general
  statement behind it is that the Maslov index of `B Λ` only depends on the free homotopy class of
  the loop `B` of automorphisms (`TauCeti.TotallyRealLoop.maslovIndex_map_eq_of_homotopy`).
* **Normalization.** On `E = ℂ` with the real line `ℝ ⊆ ℂ`
  (`TauCeti.isMaximalTotallyReal_span_one`), the loop `θ ↦ e^{ikθ/2} ℝ`, `θ = 2πt`, is the `k`-fold
  half-turn `TauCeti.TotallyRealLoop.rotationZPow` and has Maslov index `k`; in rank `n` the
  `k`-fold half-turn has index `k n` (`TauCeti.TotallyRealLoop.maslovIndex_rotationZPow`).
* **Orientation.** Reversing the orientation of the boundary circle reverses the loop
  (`TauCeti.TotallyRealLoop.symm`) and negates the index
  (`TauCeti.TotallyRealLoop.maslovIndex_symm`), so `e^{-ikθ/2} ℝ` has index `-k`.
* **Additivity** under direct sums is `TauCeti.TotallyRealLoop.maslovIndex_prod`, and
  **naturality** under a constant change of frame is
  `TauCeti.TotallyRealLoop.maslovIndex_map_const`.

The definition of `μ(E, F)` for bundle pairs over general compact surfaces with boundary, as the
first Chern number of the doubled bundle, and its loop formula as a sum over boundary circles are
not treated here.

## Main declarations

* `TauCeti.TotallyRealLoop.maslovIndex_map_of_continuousOn_closedBall`: moving a loop by the
  boundary values of a continuous map from the closed disc to the automorphisms preserves the
  Maslov index.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3, Theorems C.3.5 and C.3.6 (the boundary
  Maslov index of a bundle pair, its axioms, and its computation in a trivialization).
-/

public section

open Metric Module Real
open scoped unitInterval

namespace TauCeti

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (Λ : TotallyRealLoop E)

/-- **Independence of the trivialization on the disc.** Let `B` be a continuous map from the closed
unit disc to the complex-linear automorphisms of `E`, and `b t = B (e^{2πit})` its loop of
boundary values. Moving a loop of maximal totally real subspaces by `b` does not change its Maslov
index: the loop of determinants of `b` extends over the disc, so it has degree zero. -/
theorem maslovIndex_map_of_continuousOn_closedBall (B : ℂ → E ≃L[ℂ] E)
    (hB : ContinuousOn (fun z => (B z : E →L[ℂ] E)) (closedBall 0 1))
    (b : I → E ≃L[ℂ] E) (hb : Continuous fun t => (b t : E →L[ℂ] E)) (hb01 : b 0 = b 1)
    (hbB : ∀ t, b t = B (Circle.expLoop t)) :
    (Λ.map b hb hb01).maslovIndex = Λ.maslovIndex := by
  -- Contract the boundary circle to the centre through the circles of radius `s`.
  let H (p : I × I) : E ≃L[ℂ] E := B ((p.1 : ℝ) * (Circle.expLoop p.2 : ℂ))
  have hmem (p : I × I) : ((p.1 : ℝ) * (Circle.expLoop p.2 : ℂ) : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    exact p.1.2.2
  have hH : Continuous fun p => (H p : E →L[ℂ] E) :=
    hB.comp_continuous (by fun_prop) hmem
  have hH01 (s : I) : H (s, 0) = H (s, 1) := by
    simp only [H, Circle.expLoop.source, Circle.expLoop.target]
  have h₀ : Λ.map (fun t => H (0, t)) (hH.comp (Continuous.prodMk_right 0)) (hH01 0) =
      Λ.map (fun _ => B 0) continuous_const rfl :=
    ext fun t => by simp [H]
  have h₁ : Λ.map (fun t => H (1, t)) (hH.comp (Continuous.prodMk_right 1)) (hH01 1) =
      Λ.map b hb hb01 :=
    ext fun t => by simp [H, hbB]
  rw [← h₁, ← Λ.maslovIndex_map_eq_of_homotopy H hH hH01, h₀, maslovIndex_map_const]

/-! ### Checks -/

/-- The convention witness: the half-turn `θ ↦ e^{iθ/2} ℝ` of the real line in `ℂ` has Maslov
index `1`, not `1 / 2`. -/
example : (rotation isMaximalTotallyReal_span_one).maslovIndex = 1 := by
  simp

/-- The normalization `μ(ℂ, e^{ikθ/2} ℝ) = k` on the disc, for every integer `k`. -/
example (k : ℤ) : (rotationZPow isMaximalTotallyReal_span_one k).maslovIndex = k := by
  simp

/-- Orientation: traversed backwards, the loop `e^{ikθ/2} ℝ` has Maslov index `-k`. -/
example (k : ℤ) : (rotationZPow isMaximalTotallyReal_span_one k).symm.maslovIndex = -k := by
  simp

/-- Additivity: `(ℂ², ℝ ⊕ e^{iθ} ℝ)` has Maslov index `0 + 2 = 2`. -/
example :
    ((const isMaximalTotallyReal_span_one).prod
      (rotationZPow isMaximalTotallyReal_span_one 2)).maslovIndex = 2 := by
  simp

/-- The extension hypothesis of `maslovIndex_map_of_continuousOn_closedBall` cannot be dropped:
multiplication by `z` on the boundary circle, which does not extend over the disc as a family of
automorphisms since `z` vanishes at the centre, adds `2` to the Maslov index of `e^{ikθ/2} ℝ`. -/
example (k : ℤ) :
    ((rotationZPow isMaximalTotallyReal_span_one k).map
      (fun t => ContinuousLinearEquiv.smulLeft
        (Units.mk0 (Circle.expLoop t : ℂ) (Circle.coe_ne_zero _)))
      (by
        have h (t : I) : ((ContinuousLinearEquiv.smulLeft
            (Units.mk0 (Circle.expLoop t : ℂ) (Circle.coe_ne_zero _)) : ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) =
            (Circle.expLoop t : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
          ext
          simp
        simp_rw [h]
        fun_prop)
      (by simp)).maslovIndex = k + 2 := by
  rw [maslovIndex_map _ _ _ _ (Circle.expLoop) fun t => ?_, Circle.degree_expLoop]
  · simp
  · simp [Complex.norm_exp]

end TotallyRealLoop

end TauCeti
