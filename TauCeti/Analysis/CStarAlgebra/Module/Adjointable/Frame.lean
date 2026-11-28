/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Compact
public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Operators

/-!
# Finite Parseval frames and module-compact identity operators

For a finite family `x : ι → E` in a Hilbert C⋆-module over a (possibly non-unital) C⋆-algebra
`A`, synthesis after analysis is the sum of the rank-one operators `∑ i, θ_{x i, x i}`. Hence
`x` is a Parseval frame iff `∑ i, θ_{x i, x i} = 1`, which in particular shows that the identity
operator of any Hilbert C⋆-module with a finite Parseval frame is module-compact.

## Main declarations

* `TauCeti.AdjointableMap.synthesis_comp_analysis`:
  `(synthesis A x).comp (analysis A x) = ∑ i, rankOne A (x i) (x i)`.
* `TauCeti.AdjointableMap.isParsevalFrame_iff_sum_rankOne_eq_one`:
  `IsParsevalFrame A x ↔ ∑ i, rankOne A (x i) (x i) = 1`.
* `CStarModule.IsParsevalFrame.sum_rankOne_eq_one` and
  `CStarModule.IsParsevalFrame.one_mem_compactOperator`: rank-one identity decomposition and
  compactness of `1` for any module with a finite Parseval frame.
-/

public section

open CStarModule

namespace TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]

/-- Synthesis after analysis is the sum of the rank-one operators `θ_{x i, x i}`. -/
theorem synthesis_comp_analysis (x : ι → E) :
    (synthesis A x).comp (analysis A x) = ∑ i, rankOne A (x i) (x i) :=
  ext fun z ↦ by simp

/-- A family is a Parseval frame exactly when its rank-one operators sum to the identity,
`∑ i, θ_{x i, x i} = 1`. -/
theorem isParsevalFrame_iff_sum_rankOne_eq_one {x : ι → E} :
    IsParsevalFrame A x ↔ ∑ i, rankOne A (x i) (x i) = 1 := by
  rw [isParsevalFrame_iff_synthesis_comp_analysis_eq_id, synthesis_comp_analysis, one_def]

end TauCeti.AdjointableMap

namespace CStarModule.IsParsevalFrame

open TauCeti TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- The rank-one operators of a Parseval frame sum to the identity, `∑ i, θ_{x i, x i} = 1`. -/
theorem sum_rankOne_eq_one (hx : IsParsevalFrame A x) : ∑ i, rankOne A (x i) (x i) = 1 :=
  isParsevalFrame_iff_sum_rankOne_eq_one.mp hx

/-- The identity operator of a Hilbert C⋆-module with a finite Parseval frame is module-compact:
it is the finite sum `∑ i, θ_{x i, x i}`. -/
theorem one_mem_compactOperator (hx : IsParsevalFrame A x) :
    (1 : AdjointableMap A E E) ∈ compactOperator A E E := by
  rw [← hx.sum_rankOne_eq_one]
  exact Submodule.sum_mem _ fun i _ ↦ rankOne_mem_compactOperator _ _

end CStarModule.IsParsevalFrame
