/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Convex.Integral
import TauCeti.MeasureTheory.Integral.Average

/-!
# Averages of uniformly elliptic coefficient fields

Let `a` be a matrix-valued coefficient field, uniformly elliptic with constants `0 < λ ≤ Λ` on a
set `s` of positive finite measure. Its entrywise average `ā = ⨍_s a` is again uniformly elliptic
with the same constants (`TauCeti.PDE.UniformlyEllipticOn.setAverage`): the bilinear form of `ā`
is the average of the bilinear forms of `a`
(`TauCeti.dotProduct_mulVec_setAverage`), and both defining inequalities survive averaging.

Freezing a variable coefficient at its average over a ball, rather than at its value at a point,
is how equations with coefficients of vanishing mean oscillation are compared with
constant-coefficient equations: the frozen operator is uniformly elliptic, and the error of the
comparison is measured by the mean oscillation `⨍_s |a - ā|` of the coefficients, which makes
sense for discontinuous `a`.
-/

public section

open MeasureTheory Matrix

namespace TauCeti

namespace PDE

variable {X n : Type*} [MeasurableSpace X] [Fintype n] {μ : Measure X} {s : Set X}
  {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- **Averages of uniformly elliptic fields.** If `a` is uniformly elliptic with constants
`λ, Λ` on a measurable set `s` of positive finite measure and has integrable entries there, then
its entrywise average `⨍_s a` is a constant coefficient matrix that is uniformly elliptic with the
same constants. -/
theorem UniformlyEllipticOn.setAverage [DecidableEq n] {Y : Type*}
    (h : UniformlyEllipticOn s a lam Lam) (hs : MeasurableSet s) (hμ0 : μ s ≠ 0) (hμ : μ s ≠ ⊤)
    (ha : ∀ i j, IntegrableOn (fun x => a x i j) s μ) (t : Set Y) :
    UniformlyEllipticOn t (fun _ => Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) lam Lam := by
  have hint : ∀ η ξ : n → ℝ, IntegrableOn (fun x => η ⬝ᵥ (a x *ᵥ ξ)) s μ := fun η ξ => by
    simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (ha i j).mul_const _).const_mul _
  -- Both bounds pass to the average because they cut out closed convex sets
  -- (`Convex.set_average_mem`).
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun _ _ ξ => ?_) (fun _ _ η ξ => ?_)
  · rw [toQuadraticForm'_apply, dotProduct_mulVec_setAverage ha, ← Set.mem_Ici]
    refine (convex_Ici _).set_average_mem isClosed_Ici hμ0 hμ
      (ae_restrict_of_forall_mem hs fun x hx => ?_) (hint _ _)
    rw [Set.mem_Ici, ← toQuadraticForm'_apply]
    exact h.lower_bound hx ξ
  · rw [dotProduct_mulVec_setAverage ha, abs_le, ← Set.mem_Icc]
    exact (convex_Icc _ _).set_average_mem isClosed_Icc hμ0 hμ
      (ae_restrict_of_forall_mem hs fun x hx => abs_le.1 (h.upper_bound hx η ξ)) (hint _ _)

end PDE

end TauCeti
