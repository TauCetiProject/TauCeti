/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Freeness of relative homology along the long exact sequence of a triple

Let `B ⊆ A ⊆ X` be a triple of spaces and `V` a module over a principal ideal ring `k` without
zero divisors, such as `ℤ` (in any universe). Write `Hᵢ(-)` for relative singular homology with
coefficients in `V`. If `Hₙ₊₁(X, A)` vanishes, the long exact sequence of the triple begins

`0 ⟶ Hₙ(A, B) ⟶ Hₙ(X, B) ⟶ Hₙ(X, A)`,

and then `Hₙ(X, B)` is free as soon as `Hₙ(A, B)` is free and `Hₙ(X, A)` is projective (for
instance free) (`TauCeti.TopTriple.free_singularHomology_totalPair`). The image of `Hₙ(X, B)` in
the projective module `Hₙ(X, A)` is free because every submodule of a projective module over such a
ring is free, in any rank (`Submodule.free_of_projective_of_isPrincipalIdealRing`), so the
surjection onto the image splits
(`Function.Exact.free_of_injective_of_projective_of_isPrincipalIdealRing`).

This is the step that propagates freeness of homology in the top degree of a filtration, for
instance along the sublevels of a Morse function all of whose critical points have index at most
`n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, the long exact sequence of a triple.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w

namespace TauCeti.TopTriple

variable (T : TopTriple.{w}) {k : Type*} [Ring k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  (V : ModuleCat.{w} k)

/-- **Freeness along a triple.** Over a principal ideal ring without zero divisors (in any
universe, including `ℤ`), if `Hₙ₊₁(X, A)` vanishes, `Hₙ(A, B)` is free and `Hₙ(X, A)` is projective
(for instance free), then `Hₙ(X, B)` is free, with no finiteness assumption on any rank. -/
theorem free_singularHomology_totalPair (n : ℕ)
    [Module.Free k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [Module.Projective k ((outerPair.obj T).singularHomology V n : ModuleCat k)]
    (h : IsZero ((outerPair.obj T).singularHomology V (n + 1))) :
    Module.Free k ((totalPair.obj T).singularHomology V n : ModuleCat k) := by
  -- The connecting morphism out of `Hₙ₊₁(X, A) = 0` vanishes, so `Hₙ(A, B) ⟶ Hₙ(X, B)` is
  -- injective.
  have hmono : Mono (TopPair.singularHomologyMap (innerToTotal.app T) V n) :=
    (T.singularHomology_exact_inner V (n + 1) n).mono_g (h.eq_of_src _ _)
  have hex : Function.Exact (TopPair.singularHomologyMap (innerToTotal.app T) V n).hom
      (TopPair.singularHomologyMap (totalToOuter.app T) V n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.singularHomology_exact_total V n)
  exact hex.free_of_injective_of_projective_of_isPrincipalIdealRing
    ((ModuleCat.mono_iff_injective _).1 hmono)

end TauCeti.TopTriple
