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
# Freeness of top relative homology along the long exact sequence of a triple

Let `B ⊆ A ⊆ X` be a triple of topological spaces and `P` a module over a principal ideal ring `k`
without zero divisors (in any universe, including `ℤ`). When `H_{d+1}(X, A; P)` vanishes, the long
exact sequence of the triple gives an exact sequence of `k`-modules

`0 ⟶ H_d(A, B; P) ⟶ H_d(X, B; P) ⟶ H_d(X, A; P)`

whose right-hand map has image a submodule of `H_d(X, A; P)`. If `H_d(A, B; P)` is free and
`H_d(X, A; P)` is projective (for instance free), that image is free over the principal ideal
domain `k`, so the sequence splits onto its image and `H_d(X, B; P)` is free as well
(`TauCeti.TopTriple.free_singularHomology_totalPair`), with no finiteness assumption on any rank.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* S. Lang, *Algebra*, Chapter III, Theorem 7.1.
-/

public section

noncomputable section

open CategoryTheory

universe w u

namespace TauCeti.TopTriple

/-- **Freeness of top relative homology glues across a triple** over a principal ideal ring
without zero divisors (in any universe, including `ℤ`): if `H_{d+1}(X, A; P)` vanishes,
`H_d(A, B; P)` is free and `H_d(X, A; P)` is projective (for instance free), then `H_d(X, B; P)` is
free, with no finiteness assumption on any rank. -/
theorem free_singularHomology_totalPair (T : TopTriple.{w}) {k : Type u} [CommRing k]
    [NoZeroDivisors k] [IsPrincipalIdealRing k] (P : ModuleCat.{w} k) (d : ℕ)
    (h : Limits.IsZero ((outerPair.obj T).singularHomology P (d + 1)))
    [Module.Free k ((innerPair.obj T).singularHomology P d : ModuleCat k)]
    [Module.Projective k ((outerPair.obj T).singularHomology P d : ModuleCat k)] :
    Module.Free k ((totalPair.obj T).singularHomology P d : ModuleCat k) := by
  have hmono : Mono (TopPair.singularHomologyMap (innerToTotal.app T) P d) :=
    (T.singularHomology_exact_inner P (d + 1) d rfl).mono_g (h.eq_of_src _ 0)
  have hex : Function.Exact (TopPair.singularHomologyMap (innerToTotal.app T) P d).hom
      (TopPair.singularHomologyMap (totalToOuter.app T) P d).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.singularHomology_exact_total P d)
  exact hex.free_of_injective_of_projective_of_isPrincipalIdealRing
    ((ModuleCat.mono_iff_injective _).1 hmono)

end TauCeti.TopTriple
