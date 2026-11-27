/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Matrix.Domain
public import TauCeti.Analysis.CStarAlgebra.Trace.Projection

/-!
# Projections of `M_n(B)` under the matrix amplification of a densely defined trace

Let `τ` be a densely defined trace on a C⋆-algebra `B` and `τ_n(x) = Σᵢ τ(xᵢᵢ)` its matrix
amplification to `M_n(B) = CStarMatrix n n B` (`TauCeti.matrixTrace`). Since `τ_n` is again a
densely defined trace (`TauCeti.IsTrace.isTrace_matrixTrace`,
`TauCeti.IsTrace.isDenselyDefined_matrixTrace`), every projection `e` of `M_n(B)` has finite
amplified trace `τ_n(e) < ∞` and lies in the domain `𝔪_{τ_n} = M_n(𝔪_τ)`, so all its entries lie
in `𝔪_τ` (Thomsen [WTK], Lemma 4.11, with Lemma 3.1 (f)).

## Main results

* `TauCeti.IsTrace.matrixTrace_lt_top_of_isStarProjection`: `τ_n(e) < ∞`.
* `TauCeti.IsTrace.mem_domain_matrixTrace_of_isStarProjection`: `e ∈ 𝔪_{τ_n}`.
* `TauCeti.IsTrace.apply_mem_domain_of_isStarProjection`: `eᵢⱼ ∈ 𝔪_τ` for all `i, j`.

## References

* Klaus Thomsen, *On weights, traces and K-theory*, arXiv:2211.03172, version of 15 March 2024:
  Lemma 3.1 and Lemma 4.11.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞} {n : Type*} [Fintype n]

namespace IsTrace

/-- **Projections of `M_n(B)` have finite amplified trace.** For a densely defined trace `τ`,
every projection `e ∈ M_n(B)` satisfies `τ_n(e) < ∞` (Thomsen [WTK], Lemma 4.11). -/
theorem matrixTrace_lt_top_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ)
    {e : CStarMatrix n n B} (he : IsStarProjection e) : matrixTrace τ n e < ∞ :=
  hτ.isTrace_matrixTrace.lt_top_of_isStarProjection (hτ.isDenselyDefined_matrixTrace hd) he

/-- A projection of `M_n(B)` lies in the domain `𝔪_{τ_n}` of the amplification of a densely
defined trace. -/
theorem mem_domain_matrixTrace_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ)
    {e : CStarMatrix n n B} (he : IsStarProjection e) : e ∈ domain (matrixTrace τ n) :=
  hτ.isTrace_matrixTrace.mem_domain_of_isStarProjection (hτ.isDenselyDefined_matrixTrace hd) he

/-- **Projections of `M_n(B)` lie in `M_n(𝔪_τ)`.** For a densely defined trace `τ`, every entry
of a projection `e ∈ M_n(B)` lies in the domain `𝔪_τ` (Thomsen [WTK], Lemmas 3.1 (f) and 4.11). -/
theorem apply_mem_domain_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ)
    {e : CStarMatrix n n B} (he : IsStarProjection e) (i j : n) : e i j ∈ domain τ :=
  hτ.mem_domain_matrixTrace_iff.1 (hτ.mem_domain_matrixTrace_of_isStarProjection hd he) i j

end IsTrace

end TauCeti
