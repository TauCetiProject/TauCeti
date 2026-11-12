/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.JordanChevalley
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.LinearAlgebra.JordanChevalley.AdjointPair

/-!
# Jordan–Chevalley parts in Lie algebras of skew-adjoint endomorphisms

Let `B` be a bilinear form on a finite-dimensional vector space over a perfect field. The
Jordan–Chevalley parts of a skew-adjoint endomorphism are again skew-adjoint
(`LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`, `LinearMap.IsSkewAdjoint.of_isSemisimple_of_add`),
so the Lie algebra `skewAdjointLieSubalgebra B` of skew-adjoint endomorphisms, such as a symplectic
Lie algebra `sp(V, ω)` or an orthogonal Lie algebra, contains the nilpotent and semisimple parts
of each of its elements.

## Main results

* `TauCeti.mem_skewAdjointLieSubalgebra_of_isNilpotent_of_add_mem`,
  `TauCeti.mem_skewAdjointLieSubalgebra_of_isSemisimple_of_add_mem`: the Lie algebra of
  skew-adjoint endomorphisms of a bilinear form contains the Jordan–Chevalley parts of its
  elements.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §1.2 (the
  classical Lie algebras as skew-adjoint endomorphisms) and §4.2 (the Jordan–Chevalley
  decomposition).
-/

public section

open Module Module.End

namespace TauCeti

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : LinearMap.BilinForm K V}

/-- The Lie algebra of skew-adjoint endomorphisms of a bilinear form on a finite-dimensional
vector space over a perfect field contains the nilpotent part of the Jordan–Chevalley
decomposition of each of its elements. -/
theorem mem_skewAdjointLieSubalgebra_of_isNilpotent_of_add_mem {n s : Module.End K V}
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (h : n + s ∈ skewAdjointLieSubalgebra B) : n ∈ skewAdjointLieSubalgebra B :=
  (B.mem_skewAdjointLieSubalgebra n).2 <|
    LinearMap.IsSkewAdjoint.of_isNilpotent_of_add hc hn hs
      ((B.mem_skewAdjointLieSubalgebra _).1 h)

/-- The Lie algebra of skew-adjoint endomorphisms of a bilinear form on a finite-dimensional
vector space over a perfect field contains the semisimple part of the Jordan–Chevalley
decomposition of each of its elements. -/
theorem mem_skewAdjointLieSubalgebra_of_isSemisimple_of_add_mem {n s : Module.End K V}
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (h : n + s ∈ skewAdjointLieSubalgebra B) : s ∈ skewAdjointLieSubalgebra B :=
  (B.mem_skewAdjointLieSubalgebra s).2 <|
    LinearMap.IsSkewAdjoint.of_isSemisimple_of_add hc hn hs
      ((B.mem_skewAdjointLieSubalgebra _).1 h)

end TauCeti
