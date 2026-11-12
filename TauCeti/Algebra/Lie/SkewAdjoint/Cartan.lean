/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.JordanChevalley
import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Cartan
import TauCeti.Algebra.Lie.SkewAdjoint.JordanChevalley

/-!
# Cartan subalgebras of Killing Lie algebras of skew-adjoint endomorphisms

Let `B` be a bilinear form on a finite-dimensional vector space `V` over a perfect field whose Lie
algebra `skewAdjointLieSubalgebra B` of skew-adjoint endomorphisms has nondegenerate Killing form,
such as a symplectic Lie algebra `sp(V, ω)` in characteristic zero. This Lie algebra contains the
nilpotent part of the Jordan–Chevalley decomposition of each of its elements
(`TauCeti.mem_skewAdjointLieSubalgebra_of_isNilpotent_of_add_mem`), so its Cartan subalgebras are
toral: their elements are semisimple endomorphisms of `V`
(`TauCeti.isSemisimple_of_mem_isCartanSubalgebra_skewAdjointLieSubalgebra`). No splitting is
assumed, so this covers the real symplectic Lie algebras, whose Cartan subalgebras are in general
not split over `ℝ`.

## Main results

* `TauCeti.isSemisimple_of_mem_isCartanSubalgebra_skewAdjointLieSubalgebra`: the elements of a
  Cartan subalgebra of a Killing Lie algebra of skew-adjoint endomorphisms are semisimple.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.1 and §15.3
  (Cartan subalgebras of semisimple Lie algebras are toral).
-/

public section

open LieAlgebra Module Module.End

namespace TauCeti

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : LinearMap.BilinForm K V}

/-- **Cartan subalgebras of Killing Lie algebras of skew-adjoint endomorphisms are toral.** If the
Lie algebra of skew-adjoint endomorphisms of a bilinear form on a finite-dimensional vector space
over a perfect field has nondegenerate Killing form, every element of a Cartan subalgebra is a
semisimple endomorphism. -/
theorem isSemisimple_of_mem_isCartanSubalgebra_skewAdjointLieSubalgebra
    [IsKilling K (skewAdjointLieSubalgebra B)] {H : LieSubalgebra K (skewAdjointLieSubalgebra B)}
    [H.IsCartanSubalgebra] {x : skewAdjointLieSubalgebra B} (hx : x ∈ H) :
    (x : Module.End K V).IsSemisimple :=
  LieSubalgebra.isSemisimple_of_mem_isCartanSubalgebra
    (fun _ _ hc hn hs ↦ mem_skewAdjointLieSubalgebra_of_isNilpotent_of_add_mem hc hn hs) hx

end TauCeti
