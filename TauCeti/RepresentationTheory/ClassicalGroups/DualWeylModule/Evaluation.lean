/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
import TauCeti.RingTheory.MvPolynomial.Evaluation.Span

/-!
# Spanning a Weyl module by evaluations

In the basis dual to the standard bideterminant basis, an evaluation vector has coordinates
obtained by evaluating each standard bideterminant on the same matrix. These vectors span even
if each entry is restricted to an infinite subset of the field and a polynomial nonvanishing
condition is imposed. In particular, complex arrays with entries that are roots of unity can
be used to test linear maps on the Weyl module.

The evaluation criterion is the field case of `New.GL.ext_weylEval` in
[lsernau/grh-lean][short-proof], using the standard bideterminant basis.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/GLn/SchurModule/WeylKernel.lean
-/

public section

open MvPolynomial Set

namespace TauCeti.DualWeylModule

/-- Evaluations of the standard bideterminants on a matrix box with infinite sides span the
Weyl module in dual basis coordinates. The matrices can be restricted to the complement of
the zero locus of a nonzero polynomial, for example a product of specified minors. -/
theorem span_range_eval_bideterminant_eq_top {K : Type*} [Field K] {N n : ℕ}
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) {s : Fin N × Fin n → Set K}
    (hs : ∀ i, (s i).Infinite) {g : MvPolynomial (Fin N × Fin n) K} (hg : g ≠ 0) :
    Submodule.span K (Set.range fun x : {x ∈ pi univ s | eval x g ≠ 0} ↦
      fun T : BoundedSSYT N μ ↦ eval x.val (bideterminant K μ hμ (ssytFilling T))) = ⊤ :=
  (span_range_eval_eq_top_iff _ hs hg).2 (linearIndependent_bideterminant_ssytFilling K N μ hμ)

end TauCeti.DualWeylModule
