/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.AlgebraicDependence
import TauCeti.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Analytic functions with semialgebraic graphs are Nash

A real-valued function with semialgebraic graph on any specified domain satisfies a single
nonzero polynomial relation on that entire domain. Neither continuity nor openness of the
domain is needed for this algebraic assertion. In particular, if the function is analytic at
a point and its graph is semialgebraic on a neighbourhood, it is a Nash germ there.

The scalar output is encoded as `Unit → ℝ` in `IsSemialgebraicOn`, in accordance with its
finite-coordinate graph convention. The resulting relation is a polynomial in the value
variable with coefficients in the coordinate polynomial ring, as used by `IsNashAt`.
The empty domain and the zero-dimensional input space are included. No nonsingularity of
the relation at a graph point is asserted or needed.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 8.1 (the semialgebraic graph criterion for Nash functions).
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

/-- A scalar function with semialgebraic graph on `s` satisfies one nonzero polynomial
relation on all of `s`, without continuity or openness assumptions. -/
theorem IsSemialgebraicOn.exists_ne_zero_polynomial_relation {σ : Type*}
    {f : (σ → ℝ) → ℝ} {s : Set (σ → ℝ)}
    (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) :
    ∃ P : Polynomial (MvPolynomial σ ℝ), P ≠ 0 ∧
      ∀ x ∈ s, (P.map (eval x)).eval (f x) = 0 := by
  have hint : interior (Equiv.sumArrowEquivProdArrow σ Unit ℝ ⁻¹'
      s.graphOn (fun x (_ : Unit) ↦ f x)) = ∅ := by
    have he : ⇑(Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ) (ι := σ) (ι' := Unit)) =
        ⇑(Equiv.sumArrowEquivProdArrow σ Unit ℝ) := by
      -- The homeomorphism's toEquiv is Equiv.sumArrowEquivProdArrow by definition.
      rfl
    rw [← he, ← Homeomorph.preimage_interior, interior_graphOn, preimage_empty]
  obtain ⟨p, hp, hrel⟩ := hf.graph.exists_ne_zero_polynomial_of_interior_eq_empty hint
  let k : σ ⊕ Unit → Option σ := Sum.elim some (fun _ ↦ none)
  have hk : Function.Injective k := by
    rintro (i | ⟨⟩) (j | ⟨⟩) h <;> simp_all [k]
  refine ⟨optionEquivLeft ℝ σ (rename k p), ?_, fun x hx ↦ ?_⟩
  · simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff,
      rename_eq_zero_iff_of_injective p hk] using hp
  · rw [← optionEquivLeft_elim_eval, eval_rename]
    have heval : (fun a ↦ Option.elim a (f x) x) ∘ k = Sum.elim x (fun _ ↦ f x) := by
      ext (i | ⟨⟩) <;> rfl
    rw [heval]
    exact hrel _ (by
      rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
      exact ⟨hx, rfl⟩)

/-- An analytic function whose graph is semialgebraic on a neighbourhood of `x` is a Nash
germ at `x`. The neighbourhood need not itself be open. -/
theorem IsSemialgebraicOn.isNashAt {σ : Type*} [Fintype σ]
    {f : (σ → ℝ) → ℝ} {s : Set (σ → ℝ)} {x : σ → ℝ}
    (hf : IsSemialgebraicOn (fun y (_ : Unit) ↦ f y) s)
    (hfa : AnalyticAt ℝ f x) (hs : s ∈ 𝓝 x) : IsNashAt f x := by
  obtain ⟨P, hP, hrel⟩ := hf.exists_ne_zero_polynomial_relation
  exact isNashAt_iff.mpr ⟨hfa, P, hP, eventually_of_mem hs hrel⟩

/-- An analytic function with semialgebraic graph on an open domain is Nash at every point
of that domain. -/
theorem IsSemialgebraicOn.isNashAt_of_isOpen {σ : Type*} [Fintype σ]
    {f : (σ → ℝ) → ℝ} {s : Set (σ → ℝ)}
    (hf : IsSemialgebraicOn (fun y (_ : Unit) ↦ f y) s)
    (hfa : AnalyticOnNhd ℝ f s) (hs : IsOpen s) : ∀ x ∈ s, IsNashAt f x :=
  fun x hx ↦ hf.isNashAt (hfa x hx) (hs.mem_nhds hx)

end TauCeti
